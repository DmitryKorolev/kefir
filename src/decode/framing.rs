//! Bounded physical-line input for the decoder. This does not validate
//! JSON, UTF-8, blank lines, metadata or record fields; the scanner must do so.
use crate::resource::{Budget, INPUT_BYTES, READER_BUFFER_BYTES, RECORD_BYTES, ResourceError};
use std::io::{ErrorKind, Read};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FrameError {
    Resource(ResourceError),
    Io(ErrorKind),
}
impl From<ResourceError> for FrameError {
    fn from(e: ResourceError) -> Self {
        Self::Resource(e)
    }
}

/// Borrows the source so retiring managed buffers cannot invoke an unbounded
/// user-defined reader destructor. Buffers stay paired with their original ledger.
/// The returned slice expires before another read; no complete input is retained.
/// On panic the caller discards the whole run, not merely the current record.
pub(crate) struct Framer<'a, R: Read> {
    reader: &'a mut R,
    chunk: Vec<u8>,
    record: Vec<u8>,
    pos: usize,
    end: usize,
    eof: bool,
    admitted: u64,
    failure: Option<FrameError>,
    input_limit: u64,
    record_limit: usize,
}

/// The logical record is either already contiguous in the fixed read chunk or
/// assembled in `record` after crossing a chunk boundary.  Indices, rather
/// than a borrowed slice, let `next` finish all accounting before borrowing
/// either backing store.
#[derive(Clone, Copy)]
enum Frame {
    Chunk { start: usize, len: usize },
    Record { len: usize },
}

impl<'a, R: Read> Framer<'a, R> {
    pub(crate) fn new(reader: &'a mut R, b: &mut Budget) -> Result<Self, FrameError> {
        // Initialize one fixed buffer and prepay its two flat cleanup actions.
        b.charge_work(READER_BUFFER_BYTES as u64 + 3)?;
        let mut chunk = Vec::new();
        b.grow_vec(&mut chunk, READER_BUFFER_BYTES)?;
        chunk.resize(READER_BUFFER_BYTES, 0);
        Ok(Self {
            reader,
            chunk,
            record: Vec::new(),
            pos: 0,
            end: 0,
            eof: false,
            admitted: 0,
            failure: None,
            input_limit: INPUT_BYTES,
            record_limit: RECORD_BYTES,
        })
    }
    /// Bytes actually admitted to framing, not bytes merely read ahead. Sentinels
    /// proving input/record excess do not enter this count.
    pub(crate) fn admitted_bytes(&self) -> u64 {
        self.admitted
    }
    /// Returns one physical line without LF/CRLF, or final unterminated bytes.
    /// Empty lines are returned, never silently discarded. None is clean IO EOF,
    /// not proof of structurally valid EOF or permission to publish acceptance.
    pub(crate) fn next<'s>(&'s mut self, b: &mut Budget) -> Result<Option<&'s [u8]>, FrameError> {
        if let Some(e) = self.failure {
            return Err(e);
        }
        match self.advance(b) {
            Ok(Some(Frame::Chunk { start, len })) => Ok(Some(&self.chunk[start..start + len])),
            Ok(Some(Frame::Record { len })) => Ok(Some(&self.record[..len])),
            Ok(None) => Ok(None),
            Err(e) => {
                self.failure = Some(e);
                Err(e)
            }
        }
    }
    fn advance(&mut self, b: &mut Budget) -> Result<Option<Frame>, FrameError> {
        self.record.clear();
        loop {
            if self.pos == self.end && !self.refill(b)? {
                return Ok((!self.record.is_empty()).then_some(Frame::Record {
                    len: self.record.len(),
                }));
            }
            let remaining = self
                .record_limit
                .checked_sub(self.record.len())
                .ok_or(ResourceError::Invariant)?;
            let scan = (self.end - self.pos).min(remaining.saturating_add(1));
            let bytes = &self.chunk[self.pos..self.pos + scan];
            // The chunk charge covers this scan and copying. No byte-loop ledger
            // or counter updates; at most one byte beyond the record cap is read.
            let newline = find_newline(bytes);
            let take = newline.map_or(scan, |i| i + 1);
            if crate::resource::traced!("framing.limit", (take, remaining), { take > remaining }) {
                self.pos += remaining;
                self.admitted = self
                    .admitted
                    .checked_add(remaining as u64)
                    .ok_or(ResourceError::Counter)?;
                b.admitted_input(self.admitted);
                return Err(ResourceError::RecordBytes.into());
            }
            let required = self
                .record
                .len()
                .checked_add(take)
                .ok_or(ResourceError::Counter)?;
            // This in-cap span was inspected by framing, unlike untouched
            // read-ahead. Account it even if allocating its retained copy fails.
            let start = self.pos;
            self.admitted = self
                .admitted
                .checked_add(take as u64)
                .ok_or(ResourceError::Counter)?;
            b.admitted_input(self.admitted);
            self.pos += take;

            if self.record.is_empty() && (newline.is_some() || self.eof) {
                // Preserve the old record-buffer reservation and allocator-failure
                // point even though this record is returned directly from `chunk`.
                // The budget therefore observes the same growth/charge sequence;
                // only the redundant byte copy is removed.
                b.grow_vec(&mut self.record, required)?;
                let mut len = take - usize::from(newline.is_some());
                if newline.is_some() && len > 0 && self.chunk[start + len - 1] == b'\r' {
                    len -= 1;
                }
                return Ok(Some(Frame::Chunk { start, len }));
            }

            b.grow_vec(&mut self.record, required)?;
            self.record.extend_from_slice(&self.chunk[start..self.pos]);
            if newline.is_some() {
                let mut len = self.record.len() - 1;
                if len > 0 && self.record[len - 1] == b'\r' {
                    len -= 1;
                }
                return Ok(Some(Frame::Record { len }));
            }
        }
    }
    fn refill(&mut self, b: &mut Budget) -> Result<bool, FrameError> {
        if self.eof {
            return Ok(false);
        }
        let remaining = self
            .input_limit
            .checked_sub(self.admitted)
            .ok_or(ResourceError::Invariant)?;
        if crate::resource::traced!("framing.limit", (remaining, 0), { remaining == 0 }) {
            // A single raw sentinel distinguishes EOF from excess. Never scan or
            // charge it as an admitted chunk, and never request arbitrary suffix.
            let mut sentinel = [0];
            loop {
                match self.reader.read(&mut sentinel) {
                    Ok(0) => {
                        self.eof = true;
                        return Ok(false);
                    }
                    Ok(1) => return Err(ResourceError::InputBytes.into()),
                    Ok(_) => return Err(ResourceError::Invariant.into()),
                    Err(e) if e.kind() == ErrorKind::Interrupted => {}
                    Err(e) => return Err(FrameError::Io(e.kind())),
                }
            }
        }
        let target = remaining.min(READER_BUFFER_BYTES as u64) as usize;
        let mut filled = 0;
        while filled < target {
            match self.reader.read(&mut self.chunk[filled..target]) {
                Ok(0) => {
                    self.eof = true;
                    break;
                }
                Ok(n) if n <= target - filled => filled += n,
                Ok(_) => return Err(ResourceError::Invariant.into()),
                Err(e) if e.kind() == ErrorKind::Interrupted => {}
                Err(e) => return Err(FrameError::Io(e.kind())),
            }
        }
        // Production input cap is an exact multiple of the chunk size, so chunks
        // are full except at EOF. Short OS reads cannot change the charge stream.
        if filled > 0 {
            b.charge_work(filled as u64 + 1)?;
        }
        self.pos = 0;
        self.end = filled;
        Ok(filled > 0)
    }
    pub(crate) fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let a = release(self.chunk, b);
        let c = release(self.record, b);
        a.and(c)
    }
}

/// Find the first LF with eight-byte zero-byte probes. Ordinary safe loads
/// ensure the input boundary never
/// reads padding or crosses the supplied record-cap scan window.
#[inline]
fn find_newline(bytes: &[u8]) -> Option<usize> {
    const ONES: u64 = 0x0101_0101_0101_0101;
    const HIGHS: u64 = 0x8080_8080_8080_8080;
    const LFS: u64 = u64::from_le_bytes([b'\n'; 8]);

    let mut start = 0;
    while start + 8 <= bytes.len() {
        let word = u64::from_le_bytes(bytes[start..start + 8].try_into().unwrap());
        let equal = word ^ LFS;
        let mask = equal.wrapping_sub(ONES) & !equal & HIGHS;
        if mask != 0 {
            // The least flagged byte is the first zero byte: subtraction's
            // borrow can flag a later 0x01 only after an earlier actual zero.
            // Little-endian load order makes trailing bits match input order.
            return Some(start + mask.trailing_zeros() as usize / 8);
        }
        start += 8;
    }
    bytes[start..]
        .iter()
        .position(|byte| *byte == b'\n')
        .map(|offset| start + offset)
}
fn release(bytes: Vec<u8>, b: &mut Budget) -> Result<(), ResourceError> {
    let n = bytes.capacity();
    drop(bytes);
    b.release(n as u64)
}
const _: () = assert!(INPUT_BYTES.is_multiple_of(READER_BUFFER_BYTES as u64));
