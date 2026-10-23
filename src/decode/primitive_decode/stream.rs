//! One ordered input stream, not a semantic checker or verdict publisher.
use super::{Decoder, Failure as RecordFailure, Item, Scratch};
use crate::decode::export_header::{self, Header};
use crate::decode::framing::{FrameError, Framer};
use crate::resource::{Budget, ResourceError};
use std::io::Read;

pub(crate) mod diagnostic;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Failure<E> {
    Framing(FrameError),
    Header(export_header::Failure),
    MissingHeader,
    Record {
        failure: RecordFailure,
        /// An input error already observed, even if a later resource failure
        /// prevents completing this record. Never erase it in wire selection.
        repeated_metadata: bool,
    },
    Consumer(E),
}
#[derive(Debug, Eq, PartialEq)]
pub(crate) enum Next<T> {
    Header,
    Item(T),
    /// Clean structural EOF of this supported decoder path; never acceptance.
    End,
}
/// Holds the reader and decoder origins fixed for the entire input. A callback
/// may consume a validated record with the same decoder stores, but cannot retain
/// its borrowed declaration payload. No input-sized queue or record copy exists.
/// Failure is terminal, including callback failure; the caller discards semantic
/// candidates/caches and the run after panic. This owner issues no proof verdict.
pub(crate) struct Stream<'r, 'd, R: Read, E> {
    framer: Framer<'r, R>,
    decoder: &'d mut Decoder,
    header: Option<Header>,
    header_scratch: export_header::Scratch,
    body_scratch: Scratch,
    decoded_records: u64,
    ended: bool,
    failure: Option<Failure<E>>,
}
impl<'r, 'd, R: Read, E: Copy> Stream<'r, 'd, R, E> {
    #[cfg(feature = "introspection")]
    pub(crate) fn diagnostic_syntax(
        &self,
    ) -> (
        &crate::syntax::names::Names,
        &crate::syntax::levels::Levels,
        &crate::syntax::expressions::Expressions,
    ) {
        self.decoder.syntax()
    }

    /// Decoder must be newly created with this budget; syntax bootstrap failures
    /// precede this constructor and require whole-run/ledger discard.
    pub(crate) fn new(
        reader: &'r mut R,
        decoder: &'d mut Decoder,
        b: &mut Budget,
    ) -> Result<Self, FrameError> {
        b.charge_work(1)?;
        if decoder.failure.is_some()
            || decoder.names.len() != 1
            || decoder.levels.len() != 1
            || decoder.expressions.len() != 0
        {
            return Err(FrameError::Resource(ResourceError::Invariant));
        }
        Ok(Self {
            framer: Framer::new(reader, b)?,
            decoder,
            header: None,
            header_scratch: export_header::Scratch::default(),
            body_scratch: Scratch::default(),
            decoded_records: 0,
            ended: false,
            failure: None,
        })
    }
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn header(&self) -> Option<&Header> {
        self.header.as_ref()
    }
    pub(crate) fn admitted_bytes(&self) -> u64 {
        self.framer.admitted_bytes()
    }
    /// Complete supported records, including the header, before semantic work.
    /// This is neither a declaration count nor evidence of validated installation.
    pub(crate) fn decoded_records(&self) -> u64 {
        self.decoded_records
    }
    /// Established physical record of a terminal failure, never a declaration
    /// ordinal. Successful records form a contiguous prefix: decoding errors
    /// refer to its next record, consumer errors to the just-decoded record.
    /// Header retirement can fail after decoding; that remains record one.
    /// Framing/missing-input failures do not establish a record here. No error
    /// or ambiguous/overflowed location is replaced by a fabricated ordinal.
    pub(crate) fn failure_record(&self) -> Option<std::num::NonZeroU64> {
        let record = match self.failure? {
            Failure::Header(_) => 1,
            Failure::Record { .. } => self.decoded_records.checked_add(1)?,
            Failure::Consumer(_) => self.decoded_records,
            Failure::Framing(_) | Failure::MissingHeader => return None,
        };
        std::num::NonZeroU64::new(record)
    }
    /// The callback runs only after complete record grammar, field and reference
    /// validation. Declaration semantic checking/installation are its obligations.
    /// A semantic rejection may be returned as T so the owner can keep structurally
    /// scanning; Err is reserved for terminal failures, never a pending rejection.
    pub(crate) fn next<T>(
        &mut self,
        b: &mut Budget,
        consume: impl FnOnce(Item<'_>, &mut Decoder, &mut Budget) -> Result<T, E>,
    ) -> Result<Next<T>, Failure<E>> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if self.ended {
            return Ok(Next::End);
        }
        let result = (|| {
            let line = self.framer.next(b).map_err(Failure::Framing)?;
            let Some(line) = line else {
                if self.header.is_none() {
                    return Err(Failure::MissingHeader);
                }
                self.ended = true;
                return Ok(Next::End);
            };
            if self.header.is_none() {
                self.header = Some(
                    export_header::decode(line, &mut self.header_scratch, b)
                        .map_err(Failure::Header)?,
                );
                self.decoded_records = self.decoded_records.checked_add(1).ok_or(
                    Failure::Framing(FrameError::Resource(ResourceError::Counter)),
                )?;
                b.decoded_records(self.decoded_records);
                // Header parsing never recurs. Retire its scratch before body
                // decoding; retain only the required owned provenance strings.
                std::mem::take(&mut self.header_scratch)
                    .retire(b)
                    .map_err(|error| {
                        Failure::Header(export_header::Failure {
                            observed: Default::default(),
                            cause: export_header::Cause::Resource(error),
                        })
                    })?;
                return Ok(Next::Header);
            }
            // Framer owns the fixed-chunk byte charge required by item. Its
            // borrow expires before advancing the reader or reusing scratch.
            let item = self
                .decoder
                .item(line, &mut self.body_scratch, b)
                .map_err(|failure| Failure::Record {
                    failure,
                    repeated_metadata: self.decoder.metadata_seen,
                })?;
            // Complete decoding is independent of the consumer's result. One
            // checked increment per record is covered by its coarse decoding
            // charge, never by introspection. Overflow stops before the callback.
            self.decoded_records = self.decoded_records.checked_add(1).ok_or(Failure::Framing(
                FrameError::Resource(ResourceError::Counter),
            ))?;
            b.decoded_records(self.decoded_records);
            consume(item, self.decoder, b)
                .map(Next::Item)
                .map_err(Failure::Consumer)
        })();
        if let Err(error) = result {
            self.failure = Some(error);
        }
        result
    }
    /// Flat scratch/header buffers retire even under exhausted work. Decoder
    /// stores remain with their external owner and original ledger.
    pub(crate) fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let a = self.framer.retire(b);
        let c = self.header_scratch.retire(b);
        let d = self.body_scratch.retire(b);
        let e = self.header.map_or(Ok(()), |header| header.retire(b));
        a.and(c).and(d).and(e)
    }
}
