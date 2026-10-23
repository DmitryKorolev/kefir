//! Complete array fragments; never proof-completion evidence.
use super::{Counts, Detail};
use crate::resource::{Diagnostics, Event};
use std::fmt::{self, Write};

struct Output<'a> {
    bytes: &'a mut [u8],
    used: usize,
}
impl Output<'_> {
    fn copy(&mut self, bytes: &[u8]) -> fmt::Result {
        let end = self.used.checked_add(bytes.len()).ok_or(fmt::Error)?;
        self.bytes
            .get_mut(self.used..end)
            .ok_or(fmt::Error)?
            .copy_from_slice(bytes);
        self.used = end;
        Ok(())
    }
}
impl Write for Output<'_> {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        self.copy(text.as_bytes())
    }
}

impl Detail<'_> {
    /// Caller premises: this is the originating ledger and the destination is
    /// pre-reserved space within the report cap, excluding mandatory suffixes.
    /// Names are complete JSON copied by the owner, not arbitrary input fragments.
    /// None invalidates ALL detail; any destination prefix is scratch, never output.
    /// The caller must discard/retire the owner after this borrow ends on failure.
    pub(crate) fn encode<'a>(
        &self,
        destination: &'a mut [u8],
        d: &mut Diagnostics,
    ) -> Option<&'a [u8]> {
        let mut out = Output {
            bytes: destination,
            used: 0,
        };
        let result = self.write(&mut out, d);
        let used = out.used;
        if result.is_err() {
            d.allocation_failed();
            return None;
        }
        Some(&destination[..used])
    }

    fn write(&self, out: &mut Output<'_>, d: &mut Diagnostics) -> fmt::Result {
        if !d.charge_work(2) {
            return Err(fmt::Error);
        }
        out.write_char('[')?;
        for (bucket, counts) in ["input", "report", "runtime"].into_iter().zip(self.fixed) {
            if !d.charge_work(1024) {
                return Err(fmt::Error);
            }
            if bucket != "input" {
                out.write_char(',')?;
            }
            write!(out, "{{\"bucket\":\"{bucket}\"")?;
            counts.write(out)?;
        }
        for row in self.declarations {
            let name = self.names.get(row.name).ok_or(fmt::Error)?;
            let work = u64::try_from(name.len())
                .ok()
                .and_then(|n| n.checked_add(1024))
                .ok_or(fmt::Error)?;
            if !d.charge_work(work) {
                return Err(fmt::Error);
            }
            write!(
                out,
                ",{{\"bucket\":\"declaration\",\"declaration\":\"{}\",\"name\":",
                row.ordinal
            )?;
            out.copy(name)?;
            row.counts.write(out)?;
        }
        out.write_char(']')
    }
}

impl Counts {
    fn write(&self, out: &mut Output<'_>) -> fmt::Result {
        out.write_str(",\"accounting\":{")?;
        for (i, (key, value)) in [
            "input_bytes",
            "records",
            "work_charged",
            "peak_live_capacity_bytes",
        ]
        .into_iter()
        .zip(self.accounting)
        .enumerate()
        {
            if i != 0 {
                out.write_char(',')?;
            }
            write!(out, "\"{key}\":\"{value}\"")?;
        }
        out.write_str("},\"events\":{")?;
        for (i, (event, value)) in Event::ALL.into_iter().zip(self.events).enumerate() {
            if i != 0 {
                out.write_char(',')?;
            }
            write!(out, "\"{}\":\"{value}\"", event.wire_name())?;
        }
        out.write_str("}}")
    }
}
