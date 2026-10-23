//! Owned diagnostic names; no semantic handles survive append.
use super::{NameId, Names};
use crate::resource::Diagnostics;

#[derive(Clone, Copy)]
/// Belongs to one Buffer epoch. Every span becomes invalid on explicit discard
/// or failed append; callers must remove all such spans before buffer reuse.
/// A numeric bounds check cannot distinguish spans from another buffer/epoch.
pub(crate) struct Span {
    start: u32,
    len: u32,
}
const _: () = assert!(std::mem::size_of::<Span>() == 8);

#[derive(Default)]
pub(crate) struct Buffer {
    bytes: Vec<u8>,
}

impl Buffer {
    /// Originating immutable names and one shared run diagnostic ledger required.
    /// All previously returned spans must be discarded when this returns None.
    pub(crate) fn append(
        &mut self,
        name: NameId,
        names: &Names,
        d: &mut Diagnostics,
    ) -> Option<Span> {
        let result = self.prepare(name, names, d);
        if result.is_none() {
            d.allocation_failed();
            self.discard(d);
        }
        result
    }

    fn prepare(&mut self, name: NameId, names: &Names, d: &mut Diagnostics) -> Option<Span> {
        let mut current = name;
        let mut size = 2usize; // brackets
        let mut components = 0usize;
        while let Some((prefix, tag, bytes)) = component(names, current, d)? {
            let length = if tag == 1 {
                bytes.len()
            } else {
                escaped_len(bytes)?
            };
            size = size
                .checked_add(length)?
                .checked_add(13 + usize::from(components != 0))?;
            components += 1;
            current = prefix;
        }
        let start = self.bytes.len();
        let end = start.checked_add(size)?;
        let span = Span {
            start: start.try_into().ok()?,
            len: size.try_into().ok()?,
        };
        if !d.charge_work(u64::try_from(size).ok()?.checked_add(1)?)
            || !d.grow_vec(&mut self.bytes, end)
        {
            return None;
        }
        self.bytes.resize(end, 0);
        let mut out = Backward {
            bytes: &mut self.bytes[start..end],
            cursor: size,
        };
        out.prepend(b"]")?;
        current = name;
        let mut first = true;
        while let Some((prefix, tag, bytes)) = component(names, current, d)? {
            if !first {
                out.prepend(b",")?;
            }
            first = false;
            out.prepend(b"\"}")?;
            if tag == 1 {
                out.prepend(bytes)?;
            } else {
                let mut end = bytes.len();
                for (index, &byte) in bytes.iter().enumerate().rev() {
                    if byte == b'"' || byte == b'\\' || byte < 32 {
                        out.prepend(&bytes[index + 1..end])?;
                        if byte < 32 {
                            const HEX: &[u8; 16] = b"0123456789abcdef";
                            out.prepend(&[
                                b'\\',
                                b'u',
                                b'0',
                                b'0',
                                HEX[(byte >> 4) as usize],
                                HEX[(byte & 15) as usize],
                            ])?;
                        } else {
                            out.prepend(&[b'\\', byte])?;
                        }
                        end = index;
                    }
                }
                out.prepend(&bytes[..end])?;
            }
            out.prepend(if tag == 1 {
                b"{\"number\":\""
            } else {
                b"{\"string\":\""
            })?;
            current = prefix;
        }
        out.prepend(b"[")?;
        (out.cursor == 0).then_some(span)
    }

    /// Caller supplies this epoch's span and checks whole-run detail availability
    /// before using any result. An unrelated diagnostic failure may hide all rows.
    pub(crate) fn get(&self, span: Span) -> Option<&[u8]> {
        self.bytes
            .get(span.start as usize..(span.start as usize).checked_add(span.len as usize)?)
    }

    /// Invalidates every span, even if a later append reuses the same byte offsets.
    /// The originating run ledger must survive discard; never reset its failure.
    pub(crate) fn discard(&mut self, d: &mut Diagnostics) {
        let bytes = std::mem::take(&mut self.bytes);
        let capacity = bytes.capacity() as u64;
        drop(bytes);
        d.release(capacity);
    }
}

/// No semantic lookup API or event: reads only immutable construction-validated
/// nodes/payloads. Prefix slots strictly decrease by Names::append's invariant.
fn component<'a>(
    names: &'a Names,
    id: NameId,
    d: &mut Diagnostics,
) -> Option<Option<(NameId, u32, &'a [u8])>> {
    let n = names.get(id).ok()?;
    if !d.charge_work(u64::from(n.len) + 1) {
        return None;
    }
    if n.tag == 0 {
        return (id == NameId::ANONYMOUS).then_some(None);
    }
    if !matches!(n.tag, 1 | 2) || n.prefix >= id.0 {
        return None;
    }
    let bytes = names
        .bytes
        .get(n.offset as usize..(n.offset as usize).checked_add(n.len as usize)?)?;
    Some(Some((NameId(n.prefix), n.tag, bytes)))
}

fn escaped_len(bytes: &[u8]) -> Option<usize> {
    bytes.len().checked_mul(6)?;
    Some(
        bytes
            .iter()
            .map(|b| match b {
                b'"' | b'\\' => 2,
                0..=31 => 6,
                _ => 1,
            })
            .sum(),
    )
}

struct Backward<'a> {
    bytes: &'a mut [u8],
    cursor: usize,
}
impl Backward<'_> {
    fn prepend(&mut self, bytes: &[u8]) -> Option<()> {
        let start = self.cursor.checked_sub(bytes.len())?;
        self.bytes
            .get_mut(start..self.cursor)?
            .copy_from_slice(bytes);
        self.cursor = start;
        Some(())
    }
}
