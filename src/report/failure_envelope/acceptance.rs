//! Verdict report from a consumed EOF or justified-negative checking owner.
use super::{Buffer, Detail, Error, Frozen, Identities, Prepared, Terminal};
use crate::check::environment::validation::stream::Complete;
use crate::resource::{Budget, ResourceError, profile};
use std::fmt::{self, Write};

#[derive(Debug)]
pub(crate) struct Failure {
    pub encoding: Option<Error>,
    pub retirement: Option<ResourceError>,
}
/// Originating budget and pre-input reserved output storage are caller premises.
/// Unavailable is the requested-detail fallback; introspection may supply complete
/// rows. Diagnostic rendering never changes checking or retries output.
pub(crate) fn prepare<'a>(
    complete: Complete,
    identities: Option<Identities>,
    detail: Detail,
    terminal: Terminal,
    output: &'a mut [u8],
    budget: &mut Budget,
) -> Result<Prepared<'a>, Failure> {
    let snapshot = budget.snapshot();
    let frozen = Frozen {
        checked_declarations: complete.checked(),
        input_bytes: complete.input_bytes(),
        records: complete.records(),
        work_charged: snapshot.work_charged,
        peak_live_capacity_bytes: snapshot.peak_live_capacity_bytes,
    };
    let exit = u8::from(complete.rejection().is_some());
    let encoded = encode(
        &complete, identities, frozen, detail, terminal, output, budget,
    );
    // All semantic frees occur before a token capable of publishing exit 0
    // exists. A partial encoding or cleanup failure cannot expose acceptance.
    let retirement = complete.retire(budget).err();
    match (encoded, retirement) {
        (Ok((bytes, terminal_charge)), None) => Ok(Prepared {
            bytes,
            exit,
            terminal_charge,
        }),
        (encoded, retirement) => Err(Failure {
            encoding: encoded.err(),
            retirement,
        }),
    }
}
#[allow(clippy::too_many_arguments)]
fn encode<'a>(
    complete: &Complete,
    identities: Option<Identities>,
    frozen: Frozen,
    detail: Detail,
    terminal: Terminal,
    output: &'a mut [u8],
    budget: &mut Budget,
) -> Result<(&'a [u8], u64), Error> {
    let ids = identities.ok_or(Error::IdentityMissing)?;
    let fragments = if complete.rejection().is_none() {
        complete.axioms()
    } else {
        &[]
    };
    let charge = profile::EMERGENCY_BYTES
        .checked_add(fragments.len() as u64)
        .ok_or(Error::Output)?;
    crate::resource::traced!("terminal.acceptance", (terminal.remaining, charge), {
        terminal.remaining.checked_sub(charge).ok_or(Error::Output)
    })?;
    // Construction invariant: Axioms prepares valid complete UTF-8 JSON fragments
    // and commits only validated assumptions. No input bytes are accepted here.
    let limit = output.len().min(profile::REPORT_BYTES as usize);
    let mut b = Buffer {
        bytes: &mut output[..limit],
        used: 0,
    };
    write(&mut b, ids, frozen, fragments, complete.rejection()).map_err(|_| Error::Output)?;
    #[cfg(feature = "introspection")]
    if complete.rejection().is_none() && matches!(detail, Detail::Unavailable) {
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
            return Ok((&output[..used], charge));
        }
    }
    #[cfg(not(feature = "introspection"))]
    let _ = budget;
    let detail = match detail {
        Detail::NotRequested => "not_requested",
        Detail::Unavailable => "unavailable",
    };
    writeln!(b, ",\"detail\":\"{detail}\"}}").map_err(|_| Error::Output)?;
    let used = b.used;
    Ok((&output[..used], charge))
}
fn write(
    b: &mut Buffer<'_>,
    ids: Identities,
    f: Frozen,
    axioms: &[u8],
    rejection: Option<crate::check::environment::validation::stream::Rejection>,
) -> fmt::Result {
    if rejection.is_some() {
        b.write_str(
            "{\"protocol\":\"kefir-result-1\",\"outcome\":\"reject\",\"code\":\"checking.failed\"",
        )?;
    } else {
        b.write_str(
            "{\"protocol\":\"kefir-result-1\",\"outcome\":\"accept\",\"code\":\"checked\"",
        )?;
    }
    for (name, digest) in ["specification", "build", "resource_profile"]
        .into_iter()
        .zip(ids.0)
    {
        write!(b, ",\"{name}\":\"sha256:")?;
        let mut hex = [0; 64];
        for (i, byte) in digest.into_iter().enumerate() {
            hex[2 * i] = b"0123456789abcdef"[(byte >> 4) as usize];
            hex[2 * i + 1] = b"0123456789abcdef"[(byte & 15) as usize];
        }
        b.write_str(std::str::from_utf8(&hex).map_err(|_| fmt::Error)?)?;
        b.write_char('"')?;
    }
    write!(
        b,
        ",\"checked_declarations\":\"{}\"",
        f.checked_declarations
    )?;
    if let Some(rejected) = rejection {
        let location = rejected.location();
        write!(
            b,
            ",\"declaration_kind\":\"{}\",\"location\":{{\"record\":\"{}\",\"declaration\":\"{}\"}}",
            rejected.kind(),
            location.record,
            location.declaration.ok_or(fmt::Error)?
        )?;
    } else {
        b.write_str(",\"assumed_axioms\":[")?;
        // Only a complete accepted owner supplies the encoded assumption set.
        let end = b.used.checked_add(axioms.len()).ok_or(fmt::Error)?;
        b.bytes
            .get_mut(b.used..end)
            .ok_or(fmt::Error)?
            .copy_from_slice(axioms);
        b.used = end;
        b.write_char(']')?;
    }
    write!(
        b,
        ",\"accounting\":{{\"input_bytes\":\"{}\",\"records\":\"{}\",\"work_charged\":\"{}\",\"peak_live_capacity_bytes\":\"{}\"}}",
        f.input_bytes, f.records, f.work_charged, f.peak_live_capacity_bytes
    )?;
    Ok(())
}
