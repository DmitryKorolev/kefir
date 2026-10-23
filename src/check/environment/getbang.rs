//! Exact committed Get! closure certification. Masks are inert until one coherent pin is complete.
use super::*;
use crate::syntax::expressions::Expressions;
use crate::syntax::levels::Levels;
use crate::syntax::names::Component;
use std::cmp::Ordering;
mod group;
mod manifest;
mod matching;
#[derive(Clone, Copy, Default)]
pub(super) struct Certificate {
    masks: [[u32; manifest::MASK_WORDS]; 2],
    slots: [u32; manifest::ROOTS.len()],
    frontier: u32,
}
const _: () = assert!(size_of::<Certificate>() == 184);
impl Certificate {
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
        if let Some(index) = manifest::ROOTS.iter().position(|&root| root == referent) {
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
        if self
            .masks
            .iter()
            .zip(manifest::PIN_CLOSURE_MASKS)
            .any(|(present, required)| present.iter().zip(required).all(|(&p, r)| p & r == r))
        {
            if self.slots.iter().any(|&slot| slot == 0 || slot > after) {
                return Err(ResourceError::Invariant);
            }
            self.frontier = after;
        }
        Ok(())
    }
}
impl Environment {
    /// Original committed roots, within the full closure publication frontier. No signature-only authority.
    pub(crate) fn getbang_symbols(
        &self,
        before: usize,
        formation: Option<Formation>,
        b: &mut Budget,
    ) -> Result<Option<[NameId; manifest::ROOTS.len()]>, ResourceError> {
        self.check_visibility(before, formation)?;
        if formation.is_some()
            || self.getbang.frontier == 0
            || before < self.getbang.frontier as usize
        {
            return Ok(None);
        }
        if self.getbang.frontier > self.committed {
            return Err(ResourceError::Invariant);
        }
        b.charge_work(6)?;
        let mut out = [NameId::ANONYMOUS; manifest::ROOTS.len()];
        for (out, &slot) in out.iter_mut().zip(&self.getbang.slots) {
            if slot == 0 || slot > self.getbang.frontier || slot as usize > before {
                return Err(ResourceError::Invariant);
            }
            *out = self
                .entries
                .get(slot as usize - 1)
                .ok_or(ResourceError::Invariant)?
                .name;
        }
        Ok(Some(out))
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
    // Ten binary-search comparisons suffice for 571 entries; charge their
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

impl Environment {
    /// Called only for an original declaration after successful ordinary
    /// validation and session cleanup. The returned copy remains private until
    /// the same declaration is installed; theorem-copy never calls this path.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn prepare_getbang_definition(
        &self,
        previous: Certificate,
        request: &Request<'_>,
        n: &Names,
        l: &Levels,
        e: &Expressions,
        b: &mut Budget,
    ) -> Result<Certificate, ResourceError> {
        if self.stage.is_some() || self.entries.len() != self.committed as usize {
            return Err(ResourceError::Invariant);
        }
        if previous.frontier != 0 || request.safety != Safety::Safe {
            return Ok(previous);
        }
        let kind = match request.kind {
            Kind::Definition => 3,
            Kind::Theorem => 4,
            Kind::Axiom => 5,
            Kind::Opaque => 6,
        };
        let Some(referent) = candidate(request.name, n, b)? else {
            return Ok(previous);
        };
        let expected_name = manifest::REFERENT_NAMES[referent];
        let value = request.value;
        let mut next = previous;
        b.charge_work(manifest::DECLARATIONS.len() as u64 + 24)?;
        for (index, row) in manifest::DECLARATIONS.iter().enumerate() {
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
            let metadata = matching::sequence(row[8])?;
            if (kind == 3 && metadata != [0, 0])
                || (kind == 4 && !metadata.is_empty())
                || (matches!(kind, 5 | 6) && metadata != [1, 0])
            {
                return Err(ResourceError::Invariant);
            }
            if !names(row[2], request.parameters, n, b)?
                || !names(row[5], request.all, n, b)?
                || !matching::expression(row[3], request.ty, e, l, n, b)?
                || match value {
                    Some(value) => row[4] == 0 || !matching::expression(row[4], value, e, l, n, b)?,
                    None => row[4] != 0,
                }
            {
                continue;
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
