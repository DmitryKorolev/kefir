//! Typed literal interface and stronger exact String/Char certification.
//! Prepared matching evidence gains authority only at successful installation.
use super::*;
use crate::syntax::expressions::Expressions;
use crate::syntax::levels::Levels;
use crate::syntax::names::Component;
use std::cmp::Ordering;
mod division_mask;
mod group;
mod interface;
mod manifest;
mod matching;
mod modulus_mask;

/// One immutable Environment retains two separate authorities over the same
/// original role slots: checked public typing signatures, and exact pinned
/// closures for stronger interpretation. Partial masks/slots authorize neither.
/// Each completed frontier covers its own full witness and committed visibility.
#[derive(Clone, Copy, Default)]
pub(super) struct Certificate {
    masks: [[u32; manifest::MASK_WORDS]; 2],
    slots: [u32; 7],
    frontier: u32,
    interface_mask: u32,
    interface_frontier: u32,
    division_slot: u32,
    division_frontier: u32,
    modulus_slot: u32,
    modulus_frontier: u32,
}
const _: () = assert!(size_of::<Certificate>() == 152);
// Zero-based referent indices in the generated inventory, in retained-slot order:
// String, String.ofList, List, List.nil, List.cons, Char, Char.ofNat.
const ROOTS: [usize; 7] = [34, 288, 23, 274, 100, 6, 290];
impl Certificate {
    /// Exact whole original declaration facts only. Scope is this Environment's
    /// immutable originals, including a same-publication pending copy. This is
    /// not an interface, dependency-closure, checkedness or execution query.
    pub(super) fn exact_referent(&self, pin: usize, referent: u32) -> Result<bool, ResourceError> {
        if referent == 0 {
            return Ok(false);
        }
        let index = (referent - 1) as usize;
        if pin >= 2 || index >= manifest::REFERENTS {
            return Err(ResourceError::Invariant);
        }
        Ok(self.masks[pin][index / 32] & (1 << (index % 32)) != 0)
    }
    fn dependencies(
        &self,
        pin: usize,
        mask: u32,
        internal: &[u32; 12],
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
        if referent == division_mask::ROOT {
            if self.division_slot != 0 && self.division_slot != slot {
                return Err(ResourceError::Invariant);
            }
            self.division_slot = slot;
        }
        if referent == modulus_mask::ROOT {
            if self.modulus_slot != 0 && self.modulus_slot != slot {
                return Err(ResourceError::Invariant);
            }
            self.modulus_slot = slot;
        }
        if let Some(index) = ROOTS.iter().position(|&root| root == referent) {
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
        // A complete pin-specific Nat.div closure precedes String.ofList in
        // both pinned exports. It has its own publication frontier; partial
        // masks from either pin and a pending root alone grant no authority.
        if self.division_frontier == 0
            && self
                .masks
                .iter()
                .zip(division_mask::CLOSURES)
                .any(|(present, required)| {
                    present
                        .iter()
                        .zip(required)
                        .all(|(&present, required)| present & required == required)
                })
        {
            if self.division_slot == 0 || self.division_slot > after {
                return Err(ResourceError::Invariant);
            }
            self.division_frontier = after;
        }
        if self.modulus_frontier == 0
            && self
                .masks
                .iter()
                .zip(modulus_mask::CLOSURES)
                .any(|(present, required)| {
                    present
                        .iter()
                        .zip(required)
                        .all(|(&present, required)| present & required == required)
                })
        {
            if self.modulus_slot == 0 || self.modulus_slot > after {
                return Err(ResourceError::Invariant);
            }
            self.modulus_frontier = after;
        }
        if self
            .masks
            .iter()
            .zip(manifest::PIN_CLOSURE_MASKS)
            .any(|(present, required)| {
                present
                    .iter()
                    .zip(required)
                    .all(|(&present, required)| present & required == required)
            })
        {
            if self.slots.iter().any(|&slot| slot == 0 || slot > after) {
                return Err(ResourceError::Invariant);
            }
            // Capture the whole publication boundary, never the minimum root
            // slot: an older observation must not borrow newer dependencies.
            self.frontier = after;
        }
        Ok(())
    }
}

impl Environment {
    /// Exact original root, published only after one complete pin-specific
    /// Nat.mod closure. A partial or mixed pin cannot authorize interpretation.
    pub(super) fn certified_modulus_slot(
        &self,
        before: usize,
        formation: Option<Formation>,
    ) -> Result<Option<u32>, ResourceError> {
        self.check_visibility(before, formation)?;
        if formation.is_some()
            || self.string.modulus_frontier == 0
            || before < self.string.modulus_frontier as usize
        {
            return Ok(None);
        }
        let slot = self.string.modulus_slot;
        if self.string.modulus_frontier > self.committed
            || slot == 0
            || slot > self.string.modulus_frontier
            || slot as usize > before
        {
            return Err(ResourceError::Invariant);
        }
        Ok(Some(slot))
    }

    /// The caller checks ordinary constant use. This only exposes the original
    /// committed slot after one complete exact pin closure has been published.
    pub(super) fn certified_division_slot(
        &self,
        before: usize,
        formation: Option<Formation>,
    ) -> Result<Option<u32>, ResourceError> {
        self.check_visibility(before, formation)?;
        if formation.is_some()
            || self.string.division_frontier == 0
            || before < self.string.division_frontier as usize
        {
            return Ok(None);
        }
        let slot = self.string.division_slot;
        if self.string.division_frontier > self.committed
            || slot == 0
            || slot > self.string.division_frontier
            || slot as usize > before
        {
            return Err(ResourceError::Invariant);
        }
        Ok(Some(slot))
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
    // Nine binary-search comparisons suffice for 380 entries; charge their
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
// Each immutable whole-declaration row belongs to exactly one referent. Preserve
// manifest row order so per-pin matching sees precisely the original alternatives.
// Bounds and total coverage are checked during compilation; zero is only padding.
const fn alternative_index() -> [[u16; 2]; manifest::REFERENTS] {
    assert!(manifest::DECLARATIONS.len() < u16::MAX as usize);
    let mut result = [[0; 2]; manifest::REFERENTS];
    let mut row = 0;
    while row < manifest::DECLARATIONS.len() {
        let name = manifest::DECLARATIONS[row][0];
        let mut referent = 0;
        while referent < manifest::REFERENTS && manifest::REFERENT_NAMES[referent] != name {
            referent += 1;
        }
        assert!(referent < manifest::REFERENTS);
        let slot = if result[referent][0] == 0 { 0 } else { 1 };
        assert!(result[referent][slot] == 0);
        result[referent][slot] = (row + 1) as u16;
        row += 1;
    }
    let mut referent = 0;
    while referent < manifest::REFERENTS {
        assert!(result[referent][0] != 0);
        referent += 1;
    }
    result
}
static REFERENT_ALTERNATIVES: [[u16; 2]; manifest::REFERENTS] = alternative_index();

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
    pub(super) fn prepare_string_definition(
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
        let previous = self.prepare_string_interface_definition(previous, request, n, l, e, b)?;
        if previous.frontier != 0 || request.safety != Safety::Safe {
            return Ok(previous);
        }
        let kind = match request.kind {
            Kind::Definition => 3,
            Kind::Theorem => 4,
            _ => return Ok(previous),
        };
        let Some(referent) = candidate(request.name, n, b)? else {
            return Ok(previous);
        };
        let expected_name = manifest::REFERENT_NAMES[referent];
        let Some(value) = request.value else {
            return Err(ResourceError::Invariant);
        };
        let mut next = previous;
        b.charge_work(manifest::DECLARATIONS.len() as u64 + 24)?;
        for alternative in REFERENT_ALTERNATIVES[referent] {
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
                if pins & (1 << pin) != 0 && previous.dependencies(pin, row[10], &[0; 12])? {
                    eligible |= 1 << pin;
                }
            }
            if eligible == 0 {
                continue;
            }
            let metadata = matching::sequence(row[8])?;
            if (kind == 3 && metadata != [0, 0]) || (kind == 4 && !metadata.is_empty()) {
                return Err(ResourceError::Invariant);
            }
            if !names(row[2], request.parameters, n, b)?
                || !names(row[5], request.all, n, b)?
                || !matching::expression(row[3], request.ty, e, l, n, b)?
                || !matching::expression(row[4], value, e, l, n, b)?
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

impl Environment {
    /// Retained committed handles only. Neither a current name lookup nor a
    /// staging signature can lend authority to String literal interpretation.
    pub(crate) fn string_type(
        &self,
        before: usize,
        formation: Option<Formation>,
        expression_end: usize,
        expressions: &Expressions,
        levels: &Levels,
        b: &mut Budget,
    ) -> Result<Option<ExprId>, ResourceError> {
        self.check_visibility(before, formation)?;
        b.charge_work(8)?;
        let certificate = self.string;
        let frontier = if certificate.interface_frontier != 0 {
            certificate.interface_frontier
        } else {
            certificate.frontier
        };
        if frontier > self.committed {
            return Err(ResourceError::Invariant);
        }
        if frontier == 0 || before < frontier as usize {
            return Ok(None);
        }
        if formation.is_some() {
            let stage = self.stage.ok_or(ResourceError::Invariant)?;
            if stage.expression_end as usize != expression_end {
                return Err(ResourceError::Invariant);
            }
            // Construction invariant: only an inductive signature-only phase
            // starts its private prefix with an inductive signature. Reuse is
            // confined to the already committed certificate and original
            // syntax watermark; staged entries cannot supply literal authority.
            // Admission and generated-name collision checks also ensure these
            // phases cannot shadow any committed certified symbol name.
            if !self
                .entries
                .get(self.committed as usize)
                .is_some_and(|entry| entry.kind == StoredKind::Signature(SignatureKind::Inductive))
            {
                return Ok(None);
            }
        }
        for slot in certificate.slots {
            if slot == 0 || slot > frontier || slot as usize > before {
                return Err(ResourceError::Invariant);
            }
        }
        let definition = self
            .entries
            .get(certificate.slots[1] as usize - 1)
            .ok_or(ResourceError::Invariant)?;
        if definition.type_slot as usize >= expression_end
            || definition.kind != StoredKind::Ordinary(Kind::Definition)
        {
            return Err(ResourceError::Invariant);
        }
        let root = expressions.resolve_slot(definition.type_slot, b)?;
        let crate::syntax::expressions::ExprKind::Pi(_, _, body, _) =
            expressions.get(root, b)?.kind(expressions, levels, b)?
        else {
            return Err(ResourceError::Invariant);
        };
        if body.slot() as usize >= expression_end {
            return Err(ResourceError::Invariant);
        }
        let node = expressions.get(body, b)?;
        if node.has_free() || node.loose_range() != 0 {
            return Err(ResourceError::Invariant);
        }
        // Either completed authority has the original closed String type here.
        // Returning this original child needs no fresh type or binder opening.
        Ok(Some(body))
    }
}

impl Environment {
    /// Same certificate scope as String typing. These are retained committed
    /// identities, never names discovered in an unvalidated current group.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn string_symbols(
        &self,
        before: usize,
        formation: Option<Formation>,
        expression_end: usize,
        expressions: &Expressions,
        levels: &Levels,
        b: &mut Budget,
    ) -> Result<Option<[NameId; 5]>, ResourceError> {
        if self
            .string_type(before, formation, expression_end, expressions, levels, b)?
            .is_none()
        {
            return Ok(None);
        }
        b.charge_work(5)?;
        let mut names = [NameId::ANONYMOUS; 5];
        // Char, Char.ofNat, List.nil, List.cons, String.ofList.
        for (out, index) in names.iter_mut().zip([5, 6, 3, 4, 1]) {
            let slot = self.string.slots[index];
            *out = self
                .entries
                .get(slot as usize - 1)
                .ok_or(ResourceError::Invariant)?
                .name;
        }
        Ok(Some(names))
    }
}
