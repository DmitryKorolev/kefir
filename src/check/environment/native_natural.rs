//! Exact remaining Nat operation certificates. Prepared evidence
//! is inert until successful original installation; pin masks never mix.
use super::*;
use crate::syntax::{expressions::Expressions, levels::Levels, names::Component};
use std::cmp::Ordering;
mod group;
mod manifest;
mod matching;

#[derive(Clone, Copy, Default)]
pub(super) struct Certificate {
    masks: [[u32; manifest::MASK_WORDS]; 2],
    slots: [u32; 6],
    frontiers: [u32; 6],
}
const _: () = assert!(size_of::<Certificate>() == 160);
const _: () = assert!(manifest::PIN_CLOSURE_MASKS.len() == 2);
impl Certificate {
    pub(super) fn complete(&self) -> bool {
        self.frontiers.iter().all(|&x| x != 0)
    }
    pub(super) fn any_ready(&self) -> bool {
        self.frontiers.iter().any(|&x| x != 0)
    }
    fn dependencies(
        &self,
        pin: usize,
        mask: u32,
        internal: &[u32; manifest::MASK_WORDS],
    ) -> Result<bool, ResourceError> {
        let expected = manifest::DEPENDENCY_MASKS
            .get(mask.checked_sub(1).ok_or(ResourceError::Invariant)? as usize)
            .ok_or(ResourceError::Invariant)?;
        Ok(expected
            .iter()
            .zip(self.masks[pin])
            .zip(internal)
            .all(|((&required, present), &own)| required & !(present | own) == 0))
    }
    fn insert(&mut self, pin: usize, referent: usize, slot: u32) -> Result<(), ResourceError> {
        if pin >= 2 || referent >= manifest::REFERENTS || slot == 0 {
            return Err(ResourceError::Invariant);
        }
        self.masks[pin][referent / 32] |= 1 << (referent % 32);
        if let Some(index) = manifest::ROOTS.iter().position(|&r| r == referent) {
            if self.slots[index] != 0 && self.slots[index] != slot {
                return Err(ResourceError::Invariant);
            }
            self.slots[index] = slot;
        }
        Ok(())
    }
    fn finish(&mut self, after: u32) -> Result<(), ResourceError> {
        if after == 0 {
            return Err(ResourceError::Invariant);
        }
        for i in 0..6 {
            if self.frontiers[i] != 0 {
                continue;
            }
            if (0..2).any(|pin| {
                self.masks[pin]
                    .iter()
                    .zip(manifest::OPERATION_CLOSURES[pin][i])
                    .all(|(&present, required)| present & required == required)
            }) {
                if self.slots[i] == 0 || self.slots[i] > after {
                    return Err(ResourceError::Invariant);
                }
                self.frontiers[i] = after;
            }
        }
        Ok(())
    }
    pub(super) fn operation(
        &self,
        encoded: u32,
        before: usize,
        committed: u32,
    ) -> Result<Option<crate::check::natural::Operation>, ResourceError> {
        use crate::check::natural::Operation::*;
        let Some(i) = self.slots.iter().position(|&s| s == encoded) else {
            return Ok(None);
        };
        let frontier = self.frontiers[i];
        if frontier == 0 {
            return Ok(None);
        }
        if frontier > committed || encoded == 0 || encoded > frontier {
            return Err(ResourceError::Invariant);
        }
        if before < frontier as usize {
            return Ok(None);
        }
        Ok(Some([Gcd, Land, Lor, Xor, ShiftLeft, ShiftRight][i]))
    }
}
fn bytes(start: u32, len: u32) -> Result<&'static [u8], ResourceError> {
    let end = (start as usize)
        .checked_add(len as usize)
        .ok_or(ResourceError::Counter)?;
    manifest::UTF8_BYTES
        .get(start as usize..end)
        .ok_or(ResourceError::Invariant)
}
fn last(expected: u32, actual: Component<'_>) -> Result<Ordering, ResourceError> {
    let [_, tag, a, c] = *manifest::NAMES
        .get(expected.checked_sub(1).ok_or(ResourceError::Invariant)? as usize)
        .ok_or(ResourceError::Invariant)?;
    match (tag, actual) {
        (0, Component::String(value)) => Ok(bytes(a, c)?.cmp(value.as_bytes())),
        (0, Component::Number(_)) => Ok(Ordering::Less),
        (1, Component::String(_)) => Ok(Ordering::Greater),
        (1, Component::Number(value)) => {
            let actual = std::str::from_utf8(value)
                .ok()
                .and_then(|s| s.parse::<u64>().ok());
            // Canonical decimal names outside u64 exceed every numeric name
            // in this finite manifest. They cannot match by truncation.
            Ok(actual.map_or(Ordering::Less, |value| {
                (u64::from(a) | (u64::from(c) << 32)).cmp(&value)
            }))
        }
        _ => Err(ResourceError::Invariant),
    }
}
fn candidate(actual: NameId, n: &Names, b: &mut Budget) -> Result<Option<usize>, ResourceError> {
    let Some((_, component)) = n.view(actual, b)? else {
        return Ok(None);
    };
    let length = match component {
        Component::String(s) => s.len(),
        Component::Number(s) => s.len(),
    };
    // Nine binary-search comparisons suffice for 432 entries; charge their
    // possible input-byte work together, before inspecting component contents.
    b.charge_work(
        (length as u64)
            .checked_add(1)
            .and_then(|n| n.checked_mul(10))
            .ok_or(ResourceError::Counter)?,
    )?;
    let (mut low, mut high) = (0, manifest::REFERENT_NAMES.len());
    while low < high {
        let middle = low + (high - low) / 2;
        if last(manifest::REFERENT_NAMES[middle], component)? == Ordering::Less {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    while let Some(&expected) = manifest::REFERENT_NAMES.get(low) {
        b.charge_work(length as u64 + 1)?;
        if last(expected, component)? != Ordering::Equal {
            break;
        }
        if matching::name(expected, actual, n, b)? {
            return Ok(Some(low));
        }
        low += 1;
    }
    Ok(None)
}
fn names(
    expected: u32,
    actual: &[NameId],
    n: &Names,
    b: &mut Budget,
) -> Result<bool, ResourceError> {
    let expected = matching::sequence(expected)?;
    if expected.len() != actual.len() {
        return Ok(false);
    }
    for (&expected, &actual) in expected.iter().zip(actual) {
        if !matching::name(expected, actual, n, b)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn inherited_shape(
    string: &super::string::Certificate,
    alternative: usize,
) -> Result<bool, ResourceError> {
    let witnesses = manifest::STRING_WITNESSES
        .get(alternative)
        .ok_or(ResourceError::Invariant)?;
    for (pin, &referent) in witnesses.iter().enumerate() {
        if string.exact_referent(pin, referent)? {
            return Ok(true);
        }
    }
    Ok(false)
}

impl Environment {
    /// Called after complete ordinary validation and cleanup, before installing
    /// the same original. A pending returned copy grants no execution authority.
    /// Construction invariant: string is self.string or the successful pending
    /// String preparation for exactly this request in this same Environment.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn prepare_native_natural_definition(
        &self,
        previous: Certificate,
        string: &super::string::Certificate,
        request: &Request<'_>,
        n: &Names,
        l: &Levels,
        e: &Expressions,
        b: &mut Budget,
    ) -> Result<Certificate, ResourceError> {
        if self.stage.is_some() || self.entries.len() != self.committed as usize {
            return Err(ResourceError::Invariant);
        }
        if previous.complete() || request.safety != Safety::Safe {
            return Ok(previous);
        }
        let kind = match request.kind {
            Kind::Definition => 3,
            Kind::Theorem => 4,
            Kind::Axiom => 5,
            _ => return Ok(previous),
        };
        let Some(referent) = candidate(request.name, n, b)? else {
            return Ok(previous);
        };
        let expected_name = manifest::REFERENT_NAMES[referent];
        let mut next = previous;
        // Retain the full-scan envelope: it also covers dependency-mask and
        // frontier bookkeeping when an indexed whole-shape fact is reused.
        b.charge_work(manifest::DECLARATIONS.len() as u64 + 24)?;
        for alternative in manifest::REFERENT_ALTERNATIVES[referent] {
            if alternative == 0 {
                continue;
            }
            let index = (alternative - 1) as usize;
            let row = manifest::DECLARATIONS
                .get(index)
                .ok_or(ResourceError::Invariant)?;
            if row[0] != expected_name || row[1] != kind {
                continue;
            }
            let pins = manifest::ALTERNATIVE_PIN_MASKS[index];
            let mut eligible = 0;
            for pin in 0..2 {
                if pins & (1 << pin) != 0
                    && previous.dependencies(pin, row[10], &[0; manifest::MASK_WORDS])?
                {
                    eligible |= 1 << pin;
                }
            }
            if eligible == 0 {
                continue;
            }
            if !inherited_shape(string, index)? {
                let metadata = matching::sequence(row[8])?;
                if (kind == 3 && metadata != [0, 0])
                    || (kind == 4 && !metadata.is_empty())
                    || (kind == 5 && metadata != [1, 0])
                {
                    return Err(ResourceError::Invariant);
                }
                if !names(row[2], request.parameters, n, b)?
                    || !names(row[5], request.all, n, b)?
                    || !matching::expression(row[3], request.ty, e, l, n, b)?
                {
                    continue;
                }
                match (row[4], request.value) {
                    (0, None) if kind == 5 => {}
                    (expected, Some(value)) if kind != 5 && expected != 0 => {
                        if !matching::expression(expected, value, e, l, n, b)? {
                            continue;
                        }
                    }
                    _ => continue,
                }
            }
            let slot = self
                .committed
                .checked_add(1)
                .ok_or(ResourceError::Counter)?;
            for pin in 0..2 {
                if eligible & (1 << pin) != 0 {
                    next.insert(pin, referent, slot)?;
                }
            }
        }
        next.finish(
            self.committed
                .checked_add(1)
                .ok_or(ResourceError::Counter)?,
        )?;
        Ok(next)
    }
}
