//! Mandatory assumption fragments; no semantic validation or reporter.
use crate::resource::{Budget, ResourceError};
use crate::syntax::levels::NameId;
use crate::syntax::names::{Component, Names};

const ALLOWANCE: usize =
    (crate::resource::profile::REPORT_BYTES - crate::resource::profile::EMERGENCY_BYTES) as usize;
const START: &[u8] = b"{\"declaration\":\"";
const MIDDLE: &[u8] = b"\",\"name\":[";
const END: &[u8] = b"]}";

/// Original decoder names must remain immutable throughout preparation. Encoded
/// fragments own their bytes and retain no syntax handle. Their ledger remains
/// the originating run's ledger, independent of introspection/detail selection.
#[derive(Default)]
pub(crate) struct Axioms {
    bytes: Vec<u8>,
    committed_len: usize,
    count: u64,
    last_declaration: u64,
}

/// Borrow prevents observing the axiom set during preparation/installation.
/// Dropping rolls back logical bytes, retaining charged capacity for reuse.
/// Commit only after ALL semantic checks and atomic environment publication.
pub(crate) struct Pending<'a> {
    owner: &'a mut Axioms,
    start: usize,
    declaration: u64,
    count: u64,
    committed: bool,
}
impl Pending<'_> {
    pub(crate) fn commit(mut self) {
        self.owner.committed_len = self.owner.bytes.len();
        self.owner.count = self.count;
        self.owner.last_declaration = self.declaration;
        self.committed = true;
    }
}
impl Drop for Pending<'_> {
    fn drop(&mut self) {
        if !self.committed {
            self.owner.bytes.truncate(self.start);
        }
    }
}
impl Axioms {
    /// Returns comma-separated fragments, not an acceptance report or proof that
    /// an axiom was checked. Only the eventual validator may commit admission.
    pub(crate) fn encoded(&self) -> &[u8] {
        &self.bytes[..self.committed_len]
    }

    pub(crate) fn prepare<'a>(
        &'a mut self,
        declaration: u64,
        name: NameId,
        names: &Names,
        b: &mut Budget,
    ) -> Result<Pending<'a>, ResourceError> {
        b.charge_work(1)?;
        if declaration == 0 || declaration <= self.last_declaration {
            return Err(ResourceError::Invariant);
        }
        let count = self.count.checked_add(1).ok_or(ResourceError::Counter)?;
        // Even a forgotten Pending cannot expose an uncommitted assumption.
        // The committed prefix is authority; Drop is cleanup, not correctness.
        self.bytes.truncate(self.committed_len);
        let mut number = [0; 20];
        let digits = decimal(declaration, &mut number);
        let comma = self.count != 0;
        let mut size = START.len() + digits.len() + MIDDLE.len() + END.len() + usize::from(comma);
        let mut current = name;
        let mut components = 0;
        while let Some((prefix, component)) = names.view(current, b)? {
            let (tag, bytes) = component_bytes(component);
            let length = match component {
                Component::Number(_) => bytes.len(),
                Component::String(_) => escaped_len(bytes)?,
            };
            size = size
                .checked_add(tag.len() + 2 + usize::from(components != 0))
                .and_then(|s| s.checked_add(length))
                .ok_or(ResourceError::Counter)?;
            components += 1;
            current = prefix;
        }
        let start = self.bytes.len();
        let end = start.checked_add(size).ok_or(ResourceError::Counter)?;
        if crate::resource::traced!("axiom_report.limit", (end, ALLOWANCE), { end > ALLOWANCE }) {
            return Err(ResourceError::Report);
        }
        // One encoded-span charge covers initialization and writing, with the
        // same constant-factor span convention as name storage. No byte-loop
        // accounting. Each name view separately charges its entire payload.
        b.charge_work(size as u64 + 1)?;
        b.grow_vec(&mut self.bytes, end)?;
        self.bytes.resize(end, 0);
        let pending = Pending {
            owner: self,
            start,
            declaration,
            count,
            committed: false,
        };
        let mut output = Backward {
            bytes: &mut pending.owner.bytes[start..end],
            cursor: size,
        };
        output.prepend(END);
        current = name;
        let mut first = true;
        while let Some((prefix, component)) = names.view(current, b)? {
            if !first {
                output.prepend(b",");
            }
            first = false;
            let (tag, bytes) = component_bytes(component);
            output.prepend(b"\"}");
            match component {
                Component::Number(_) => output.prepend(bytes),
                Component::String(_) => {
                    let mut end = bytes.len();
                    for (i, &byte) in bytes.iter().enumerate().rev() {
                        if byte == b'"' || byte == b'\\' || byte < 32 {
                            output.prepend(&bytes[i + 1..end]);
                            if byte < 32 {
                                output.prepend(&[
                                    b'\\',
                                    b'u',
                                    b'0',
                                    b'0',
                                    HEX[(byte >> 4) as usize],
                                    HEX[(byte & 15) as usize],
                                ]);
                            } else {
                                output.prepend(&[b'\\', byte]);
                            }
                            end = i;
                        }
                    }
                    output.prepend(&bytes[..end]);
                }
            }
            output.prepend(tag);
            current = prefix;
        }
        output.prepend(MIDDLE);
        output.prepend(digits);
        output.prepend(START);
        if comma {
            output.prepend(b",");
        }
        if output.cursor != 0 {
            return Err(ResourceError::Invariant);
        }
        Ok(pending)
    }
    pub(crate) fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let bytes = self.bytes.capacity() as u64;
        drop(self);
        b.release(bytes)
    }
}
const HEX: &[u8; 16] = b"0123456789abcdef";
fn component_bytes(component: Component<'_>) -> (&'static [u8], &[u8]) {
    match component {
        Component::String(s) => (b"{\"string\":\"", s.as_bytes()),
        Component::Number(n) => (b"{\"number\":\"", n),
    }
}
fn escaped_len(bytes: &[u8]) -> Result<usize, ResourceError> {
    // Every input byte emits at most six bytes. One coarse overflow check
    // establishes that every partial sum fits; no per-byte resource checks.
    bytes.len().checked_mul(6).ok_or(ResourceError::Counter)?;
    Ok(bytes
        .iter()
        .map(|byte| match byte {
            b'"' | b'\\' => 2,
            0..=31 => 6,
            _ => 1,
        })
        .sum())
}
fn decimal(mut value: u64, buffer: &mut [u8; 20]) -> &[u8] {
    let mut start = buffer.len();
    loop {
        start -= 1;
        buffer[start] = b'0' + (value % 10) as u8;
        value /= 10;
        if value == 0 {
            return &buffer[start..];
        }
    }
}
struct Backward<'a> {
    bytes: &'a mut [u8],
    cursor: usize,
}
impl Backward<'_> {
    // Construction invariant: the first walk computes exactly the bytes emitted
    // by this second walk, over the SAME immutable name. Each span fits the
    // unwritten prefix. Native slice bounds remain; there is no fallible reserve,
    // per-byte budget check or partially successful output result here.
    fn prepend(&mut self, bytes: &[u8]) {
        let start = self.cursor - bytes.len();
        self.bytes[start..self.cursor].copy_from_slice(bytes);
        self.cursor = start;
    }
}
