//! Mandatory lean4export metadata record. This validates one
//! header, not whole-input sequencing. Its producer strings confer no trust.
use crate::decode::record_validation::Findings;
use crate::resource::{Budget, RECORD_BYTES, ResourceError};

const _: () = assert!(RECORD_BYTES <= u32::MAX as usize);

#[derive(Clone, Copy)]
#[repr(usize)]
#[allow(
    dead_code,
    reason = "Retained for component regressions and explicit internal inspection"
)]
pub(crate) enum Field {
    ExporterName,
    ExporterVersion,
    LeanHash,
    LeanVersion,
    FormatVersion,
}
#[derive(Clone, Copy, Default)]
#[allow(
    dead_code,
    reason = "Retained for component regressions and explicit internal inspection"
)]
struct Span {
    start: u32,
    len: u32,
}
pub(crate) struct Header {
    bytes: Vec<u8>,
    spans: [Span; 5],
}
impl Header {
    /// Immutable spans were checked before copying all five decoded strings.
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn get(&self, field: Field) -> &[u8] {
        let span = self.spans[field as usize];
        &self.bytes[span.start as usize..(span.start + span.len) as usize]
    }
    pub(crate) fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let capacity = self.bytes.capacity();
        drop(self.bytes);
        b.release(capacity as u64)
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Cause {
    Framing,
    Metadata,
    UnsupportedField,
    UnsupportedFormat,
    Resource(ResourceError),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Failure {
    pub observed: Findings,
    pub cause: Cause,
}
#[derive(Default)]
pub(crate) struct Scratch {}
impl Scratch {
    pub(crate) fn retire(self, _b: &mut Budget) -> Result<(), ResourceError> {
        Ok(())
    }
}
pub(crate) fn decode(input: &[u8], _s: &mut Scratch, b: &mut Budget) -> Result<Header, Failure> {
    crate::decode::primitive_decode::decode_header(input, b)
}
impl Header {
    pub(super) fn from_values(values: [&[u8]; 5], b: &mut Budget) -> Result<Self, Cause> {
        if values[4] != b"3.1.0" {
            return Err(Cause::UnsupportedFormat);
        }
        let total = values
            .iter()
            .try_fold(0usize, |sum, v| sum.checked_add(v.len()))
            .ok_or(Cause::Resource(ResourceError::Counter))?;
        b.charge_work(total as u64 + 1).map_err(Cause::Resource)?;
        let mut header = Self {
            bytes: Vec::new(),
            spans: [Span::default(); 5],
        };
        b.grow_vec(&mut header.bytes, total)
            .map_err(Cause::Resource)?;
        // All allocations/checks precede publication; bounded input lengths
        // ensure every copied span fits u32 and belongs to this header owner.
        for (i, value) in values.into_iter().enumerate() {
            header.spans[i] = Span {
                start: header.bytes.len() as u32,
                len: value.len() as u32,
            };
            header.bytes.extend_from_slice(value);
        }
        Ok(header)
    }
}
