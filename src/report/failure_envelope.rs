//! Bounded private encoding; no outcome selection or publication.
use crate::resource::{failure::FailureReport, profile};
use std::fmt::{self, Write};

pub(crate) mod acceptance;

#[derive(Clone, Copy)]
pub(crate) struct Identities(pub [[u8; 32]; 3]);
#[derive(Clone, Copy)]
pub(crate) struct Frozen {
    pub checked_declarations: u64,
    pub input_bytes: u64,
    pub records: u64,
    pub work_charged: u64,
    pub peak_live_capacity_bytes: u64,
}
pub(crate) struct Location {
    pub record: std::num::NonZeroU64,
    pub declaration: Option<std::num::NonZeroU64>,
}
#[derive(Clone, Copy)]
pub(crate) enum Detail {
    NotRequested,
    Unavailable,
}
/// Created once for terminal encoding, after semantic accounting is frozen.
/// Consuming self prevents retrying a failed encoder with the same allowance.
/// The owner handles the one fixed emergency attempt separately, never recursively.
pub(crate) struct Terminal {
    remaining: u64,
}
impl Terminal {
    pub(crate) fn new() -> Self {
        Self {
            remaining: profile::TERMINAL_WORK,
        }
    }
}
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Error {
    IdentityMissing,
    InvalidEnvelope,
    Output,
}
struct Buffer<'a> {
    bytes: &'a mut [u8],
    used: usize,
}
impl Write for Buffer<'_> {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        let end = self.used.checked_add(text.len()).ok_or(fmt::Error)?;
        let target = self.bytes.get_mut(self.used..end).ok_or(fmt::Error)?;
        target.copy_from_slice(text.as_bytes());
        self.used = end;
        Ok(())
    }
}
const KINDS: &[&str] = &[
    "axiom",
    "def",
    "thm",
    "opaque",
    "quot",
    "inductive",
    "unknown",
];
const DECLINE: &[&str] = &[
    "support.format",
    "support.record",
    "support.field",
    "support.numeric_range",
    "support.construct",
    "support.semantic",
    "support.literal_arithmetic",
    "support.policy",
    "resource.input_bytes",
    "resource.record_bytes",
    "resource.json_depth",
    "resource.structure_depth",
    "resource.context_depth",
    "resource.reduction_path",
    "resource.work",
    "resource.storage",
    "resource.report",
    "resource.counter",
];
const INPUT: &[&str] = &[
    "input.io",
    "input.arguments",
    "input.framing",
    "input.duplicate_key",
    "input.metadata",
    "input.field",
    "input.reference",
    "input.duplicate_id",
];
const INTERNAL: &[&str] = &[
    "internal.panic",
    "internal.invariant",
    "internal.identity",
    "internal.output",
    "internal.allocation",
];
pub(crate) struct Envelope<'a> {
    pub failure: FailureReport,
    /// The owner must establish exact executable/procedure/profile association.
    /// Well-formed digest bytes alone do not establish that invariant.
    pub identities: Option<Identities>,
    pub frozen: Frozen,
    pub detail: Detail,
    /// Required whenever a kind/policy decline identifies a declaration, even
    /// if its ordinal/location is unavailable. This is an owner obligation.
    pub declaration_kind: Option<&'a str>,
    pub location: Option<Location>,
}
/// Completed bytes paired with their matching exit. Acceptance construction is
/// restricted to the child encoder consuming a checked whole-input owner.
/// Only successful encoding constructs this token; it cannot be cloned.
/// This says nothing about the caller's identity/selection obligations.
pub(crate) struct Prepared<'a> {
    bytes: &'a [u8],
    exit: u8,
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    terminal_charge: u64,
}
impl Prepared<'_> {
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn terminal_charge(&self) -> u64 {
        self.terminal_charge
    }
    /// The caller supplies a fresh stream, with no previous report or concurrent
    /// writer, and never retries or appends another report on error. Consuming
    /// this token prevents reuse through this handle, not reconstruction by an
    /// incorrect owner. A custom writer must obey std::io::Write's contract.
    /// No report, panic classification or emergency retry is synthesized here.
    pub(crate) fn publish(self, output: &mut impl std::io::Write) -> std::io::Result<u8> {
        use std::io::{Error, ErrorKind};
        let mut remaining = self.bytes;
        while !remaining.is_empty() {
            match output.write(remaining) {
                Ok(0) => return Err(Error::from(ErrorKind::WriteZero)),
                Ok(n) => {
                    remaining = remaining
                        .get(n..)
                        .ok_or_else(|| Error::from(ErrorKind::InvalidData))?;
                }
                Err(e) if e.kind() == ErrorKind::Interrupted => continue,
                Err(e) => return Err(e),
            }
        }
        loop {
            match output.flush() {
                Err(e) if e.kind() == ErrorKind::Interrupted => continue,
                Err(e) => return Err(e),
                Ok(()) => return Ok(self.exit),
            }
        }
    }
}
impl Envelope<'_> {
    pub(crate) fn prepare<'a>(
        &self,
        terminal: Terminal,
        output: &'a mut [u8],
    ) -> Result<Prepared<'a>, Error> {
        let (bytes, terminal_charge) = self.encode(terminal, output)?;
        Ok(Prepared {
            bytes,
            exit: self.failure.outcome.exit_code(),
            terminal_charge,
        })
    }

    /// On error no completed bytes are returned; discard any partial buffer.
    /// Storage must already be reserved/charged before input by the owner.
    /// No allocator, semantic ledger, attacker text, or proof verdict is used.
    pub(crate) fn encode<'a>(
        &self,
        terminal: Terminal,
        output: &'a mut [u8],
    ) -> Result<(&'a [u8], u64), Error> {
        let ids = self.checked()?;
        let remaining = crate::resource::traced!(
            "terminal.emergency",
            (terminal.remaining, profile::EMERGENCY_BYTES),
            {
                terminal
                    .remaining
                    .checked_sub(profile::EMERGENCY_BYTES)
                    .ok_or(Error::Output)
            }
        )?;
        let limit = output.len().min(profile::EMERGENCY_BYTES as usize);
        let mut b = Buffer {
            bytes: &mut output[..limit],
            used: 0,
        };
        self.write(&mut b, ids).map_err(|_| Error::Output)?;
        let used = b.used;
        Ok((&output[..used], terminal.remaining - remaining))
    }
    /// Ordinary-decline attribution: requested complete rows
    /// rendered into the pre-reserved ordinary buffer after semantic counters
    /// are frozen. Optional rendering never changes the decline, its reason,
    /// the frozen counts or semantic charges; missing retained rows, diagnostic
    /// failure or insufficient ordinary space fall back to the closed
    /// unavailable form. Rows never reach the emergency envelope, and no
    /// partial encoding can escape.
    #[cfg(feature = "introspection")]
    pub(crate) fn prepare_decline<'a>(
        &self,
        terminal: Terminal,
        output: &'a mut [u8],
        budget: &mut crate::resource::Budget,
    ) -> Result<Prepared<'a>, Error> {
        let (bytes, terminal_charge) = self.encode_decline(terminal, output, budget)?;
        Ok(Prepared {
            bytes,
            exit: self.failure.outcome.exit_code(),
            terminal_charge,
        })
    }
    #[cfg(feature = "introspection")]
    fn encode_decline<'a>(
        &self,
        terminal: Terminal,
        output: &'a mut [u8],
        budget: &mut crate::resource::Budget,
    ) -> Result<(&'a [u8], u64), Error> {
        let ids = self.checked()?;
        let remaining = crate::resource::traced!(
            // Match the closed failure encoder's terminal event in all
            // introspection modes: optional detail cannot alter the ordered
            // semantic/charge trace.
            "terminal.emergency",
            (terminal.remaining, profile::EMERGENCY_BYTES),
            {
                terminal
                    .remaining
                    .checked_sub(profile::EMERGENCY_BYTES)
                    .ok_or(Error::Output)
            }
        )?;
        let limit = output.len().min(profile::REPORT_BYTES as usize);
        let mut b = Buffer {
            bytes: &mut output[..limit],
            used: 0,
        };
        self.write_prefix(&mut b, ids).map_err(|_| Error::Output)?;
        const PREFIX: &[u8] = b",\"detail\":\"complete\",\"declarations\":";
        const SUFFIX: &[u8] = b"}\n";
        let checkpoint = b.used;
        let start = checkpoint.checked_add(PREFIX.len());
        let end = b.bytes.len().checked_sub(SUFFIX.len());
        let size = match start.zip(end).filter(|(start, end)| start <= end) {
            Some((start, end)) => budget
                .encode_detail(&mut b.bytes[start..end])
                .map(|v| v.len()),
            None => {
                budget.encode_detail(&mut []);
                None
            }
        };
        if let (Some(start), Some(size)) = (start, size) {
            // Capacity for both markers was reserved before optional encoding.
            b.bytes[checkpoint..start].copy_from_slice(PREFIX);
            b.used = start + size;
            b.write_str("}\n").map_err(|_| Error::Output)?;
            let used = b.used;
            return Ok((&output[..used], terminal.remaining - remaining));
        }
        // Rows are unavailable: the prefix bytes are scratch until publication.
        b.used = checkpoint;
        writeln!(b, ",\"detail\":\"unavailable\"}}").map_err(|_| Error::Output)?;
        let used = b.used;
        Ok((&output[..used], terminal.remaining - remaining))
    }
    /// Closed-code, kind and location validation shared by every variant.
    fn checked(&self) -> Result<Identities, Error> {
        use crate::resource::failure::FailureOutcome;
        let ids = self.identities.ok_or(Error::IdentityMissing)?;
        let allowed = match self.failure.outcome {
            FailureOutcome::Decline => DECLINE,
            FailureOutcome::InputError => INPUT,
            FailureOutcome::InternalError => INTERNAL,
        };
        if !allowed.contains(&self.failure.code)
            || self.declaration_kind.is_some_and(|k| !KINDS.contains(&k))
            || (matches!(self.failure.code, "support.record" | "support.policy")
                && self
                    .location
                    .as_ref()
                    .is_some_and(|l| l.declaration.is_some())
                && self.declaration_kind.is_none())
        {
            return Err(Error::InvalidEnvelope);
        }
        Ok(ids)
    }
    fn write(&self, b: &mut Buffer<'_>, ids: Identities) -> fmt::Result {
        self.write_prefix(b, ids)?;
        let detail = match self.detail {
            Detail::NotRequested => "not_requested",
            Detail::Unavailable => "unavailable",
        };
        writeln!(b, ",\"detail\":\"{detail}\"}}")
    }
    /// Every mandatory field through the optional kind/location. Complete-detail
    /// variants append their own detail member and close the object instead.
    fn write_prefix(&self, b: &mut Buffer<'_>, ids: Identities) -> fmt::Result {
        write!(
            b,
            "{{\"protocol\":\"kefir-result-1\",\"outcome\":\"{}\",\"code\":\"{}\"",
            self.failure.outcome.wire_name(),
            self.failure.code
        )?;
        for (name, digest) in ["specification", "build", "resource_profile"]
            .into_iter()
            .zip(ids.0)
        {
            write!(b, ",\"{name}\":\"sha256:")?;
            let mut hex = [0u8; 64];
            for (i, byte) in digest.into_iter().enumerate() {
                hex[2 * i] = b"0123456789abcdef"[(byte >> 4) as usize];
                hex[2 * i + 1] = b"0123456789abcdef"[(byte & 15) as usize];
            }
            b.write_str(std::str::from_utf8(&hex).map_err(|_| fmt::Error)?)?;
            b.write_char('"')?;
        }
        let f = self.frozen;
        write!(
            b,
            ",\"checked_declarations\":\"{}\",\"accounting\":{{\"input_bytes\":\"{}\",\"records\":\"{}\",\"work_charged\":\"{}\",\"peak_live_capacity_bytes\":\"{}\"}}",
            f.checked_declarations,
            f.input_bytes,
            f.records,
            f.work_charged,
            f.peak_live_capacity_bytes
        )?;
        if let Some(kind) = self.declaration_kind {
            write!(b, ",\"declaration_kind\":\"{kind}\"")?;
        }
        if let Some(location) = &self.location {
            write!(b, ",\"location\":{{\"record\":\"{}\"", location.record)?;
            if let Some(d) = location.declaration {
                write!(b, ",\"declaration\":\"{d}\"")?;
            }
            b.write_char('}')?;
        }
        Ok(())
    }
}
