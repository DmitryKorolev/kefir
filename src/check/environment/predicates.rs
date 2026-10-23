//! Exact dependency manifests. No matching result is proof conversion.
//! Callers prepare only after complete ordinary validation and publish the copied
//! certificate only after infallible installation of the same original referents.
use super::constant_use::{ConstantUse, UseError};
use super::*;
use crate::decode::primitive_decode::inductives::{Request as Group, Span as GroupSpan};
use crate::syntax::expressions::ExprKind;
use crate::syntax::{expressions::Expressions, levels::Levels, names::Component};
mod manifest;
mod matching;

#[derive(Clone, Copy)]
struct Expression([u32; 4]);
#[derive(Clone, Copy)]
struct Level([u32; 3]);
#[derive(Clone, Copy)]
struct Declaration([u32; 8]);
#[derive(Clone, Copy)]
struct Rule([u32; 3]);
// Adopted narrow letE matcher: payload row for the tag-8 let main
// row — [name_ref, type_ref, value_ref, body_ref, nondep_flag].
#[derive(Clone, Copy)]
struct LetPayload([u32; 5]);
struct Name {
    parent: u32,
    component: &'static str,
}
const _: () = assert!(size_of::<Expression>() == 16 && size_of::<Level>() == 12);
const _: () = assert!(size_of::<Declaration>() == 32 && size_of::<Rule>() == 12);
const _: () = assert!(size_of::<LetPayload>() == 20);
const _: () = assert!(size_of::<Name>() == 24);

#[derive(Clone, Copy, Default)]
pub(super) struct Certificate([u32; 10]);
const _: () = assert!(size_of::<Certificate>() == 40);
// Slots are original committed declaration identities, not canonical name IDs.
// The mask belongs to one growing immutable Environment. No theorem transport,
// staging signature or auxiliary-template phase can publish a certificate.
fn words(low: u32, high: u32) -> u64 {
    u64::from(low) | (u64::from(high) << 32)
}
impl Certificate {
    fn insert(&mut self, mask: u64) {
        self.0[0] |= mask as u32;
        self.0[5] |= (mask >> 32) as u32;
    }
    fn has(self, dependencies: u64) -> bool {
        words(self.0[0], self.0[5]) & dependencies == dependencies
    }
}
fn classify(actual: NameId, n: &Names, b: &mut Budget) -> Result<Option<u32>, ResourceError> {
    if n.summary(actual, b)?.depth > 3 {
        return Ok(None);
    }
    let Some((_, Component::String(component))) = n.view(actual, b)? else {
        return Ok(None);
    };
    b.charge_work(manifest::REFERENTS as u64)?;
    for (i, item) in manifest::NAMES.iter().take(manifest::REFERENTS).enumerate() {
        if item.component == component && matching::name(i as u32 + 1, actual, n, b)? {
            return Ok(Some(i as u32 + 1));
        }
    }
    Ok(None)
}
fn scope(word: u32, actual: &[NameId], n: &Names, b: &mut Budget) -> Result<bool, ResourceError> {
    if actual.len() != (word >> 24) as usize {
        return Ok(false);
    }
    for (i, value) in actual.iter().enumerate() {
        if !matching::name(word >> (8 * i) & 255, *value, n, b)? {
            return Ok(false);
        }
    }
    Ok(true)
}
fn slice<T>(values: &[T], span: GroupSpan) -> Result<&[T], ResourceError> {
    values
        .get(
            span.start as usize
                ..(span.start as usize)
                    .checked_add(span.len as usize)
                    .ok_or(ResourceError::Counter)?,
        )
        .ok_or(ResourceError::Invariant)
}
impl Environment {
    pub(super) fn prepare_predicate_definition(
        &self,
        request: &Request<'_>,
        n: &Names,
        l: &Levels,
        e: &Expressions,
        b: &mut Budget,
    ) -> Result<Certificate, ResourceError> {
        if self.stage.is_some() || self.entries.len() != self.committed as usize {
            return Err(ResourceError::Invariant);
        }
        let mut next = self.predicates;
        if request.kind != Kind::Definition || request.safety != Safety::Safe {
            return Ok(next);
        }
        let Some(code) = classify(request.name, n, b)? else {
            return Ok(next);
        };
        if request.all != [request.name] {
            return Ok(next);
        }
        let Some(value) = request.value else {
            return Ok(next);
        };
        // Each row is a whole alternative. In particular the reference root's
        // dependency mask includes its exact _f; no body-fragment union occurs.
        for &Declaration(
            [
                header,
                scopes,
                ty,
                body,
                dependencies,
                _,
                _,
                dependencies_hi,
            ],
        ) in &manifest::DECLARATIONS
        {
            if header & 255 != code
                || (header >> 8) & 255 != 4
                || !next.has(words(dependencies, dependencies_hi))
            {
                continue;
            }
            if scope(scopes, request.parameters, n, b)?
                && matching::expression(ty, request.ty, e, l, n, b)?
                && matching::expression(body, value, e, l, n, b)?
            {
                next.insert(1u64 << (code - 1));
                // The two operation codes are fixed by the retained name table.
                if code == 7 {
                    next.0[1] = self
                        .committed
                        .checked_add(1)
                        .ok_or(ResourceError::Counter)?
                }
                if code == 10 {
                    next.0[2] = self
                        .committed
                        .checked_add(1)
                        .ok_or(ResourceError::Counter)?
                }
                if let Some(index) = manifest::ARITHMETIC.iter().position(|&x| x == code) {
                    next.0[6 + index] = self
                        .committed
                        .checked_add(1)
                        .ok_or(ResourceError::Counter)?;
                }
                break;
            }
        }
        Ok(next)
    }
    pub(super) fn commit_predicates(&mut self, pending: Certificate) {
        self.predicates = pending
    }

    pub(super) fn prepare_predicate_group(
        &self,
        request: &Group<'_>,
        n: &Names,
        l: &Levels,
        e: &Expressions,
        b: &mut Budget,
    ) -> Result<Certificate, ResourceError> {
        self.require_public_stage()?;
        let mut next = self.predicates;
        let [family] = request.types else {
            return Ok(next);
        };
        let Some(code) = classify(family.name, n, b)? else {
            return Ok(next);
        };
        let Some(&Declaration(
            [
                header,
                scopes,
                ty,
                ctor_lo,
                family_deps,
                meta,
                ctor_hi,
                family_deps_hi,
            ],
        )) = manifest::DECLARATIONS
            .iter()
            .find(|Declaration(row)| row[0] & 255 == code && row[0] >> 8 & 255 == 1)
        else {
            return Ok(next);
        };
        let ctor_mask = words(ctor_lo, ctor_hi);
        if family.is_unsafe
            || family.is_reflexive
            || family.is_recursive != (header >> 17 & 1 != 0)
            || family.num_params != meta & 255
            || family.num_indices != meta >> 8 & 255
            || family.num_nested != meta >> 16 & 255
            || !scope(scopes, slice(request.names, family.parameters)?, n, b)?
            || !matching::expression(ty, family.ty, e, l, n, b)?
        {
            return Ok(next);
        }
        let [all] = slice(request.names, family.all)? else {
            return Ok(next);
        };
        if !matching::name(code, *all, n, b)? {
            return Ok(next);
        }
        let declared_ctors = slice(request.names, family.constructors)?;
        if declared_ctors.len() != request.constructors.len()
            || request.constructors.len() != ctor_mask.count_ones() as usize
            || request.recursors.len() != 1
        {
            return Ok(next);
        }
        // The fixed complete group's internal edges are permitted only after all
        // descriptors below match; all external referents must already be certified.
        let rec = request.recursors[0];
        let Some(rec_code) = classify(rec.name, n, b)? else {
            return Ok(next);
        };
        let group_mask = (1 << (code - 1)) | ctor_mask | (1 << (rec_code - 1));
        if !next.has(words(family_deps, family_deps_hi) & !group_mask) {
            return Ok(next);
        }
        let mut found = 0u64;
        for (i, ctor) in request.constructors.iter().enumerate() {
            let Some(ctor_code) = classify(ctor.name, n, b)? else {
                return Ok(next);
            };
            if ctor_mask & (1 << (ctor_code - 1)) == 0 || found & (1 << (ctor_code - 1)) != 0 {
                return Ok(next);
            }
            found |= 1 << (ctor_code - 1);
            let Some(&Declaration([head, scope_word, expected_ty, _, deps, data, _, deps_hi])) =
                manifest::DECLARATIONS
                    .iter()
                    .find(|Declaration(row)| row[0] & 255 == ctor_code && row[0] >> 8 & 255 == 2)
            else {
                return Ok(next);
            };
            if head >> 24 != code
                || !next.has(words(deps, deps_hi) & !group_mask)
                || ctor.is_unsafe
                || ctor.index != data & 255
                || ctor.index as usize != i
                || ctor.num_params != data >> 8 & 255
                || ctor.num_fields != data >> 16 & 255
                || !matching::name(ctor_code, declared_ctors[i], n, b)?
                || !matching::name(code, ctor.inductive, n, b)?
                || !scope(scope_word, slice(request.names, ctor.parameters)?, n, b)?
                || !matching::expression(expected_ty, ctor.ty, e, l, n, b)?
            {
                return Ok(next);
            }
        }
        let Some(&Declaration(
            [
                head,
                scope_word,
                expected_ty,
                rule_span,
                deps,
                data,
                _,
                deps_hi,
            ],
        )) = manifest::DECLARATIONS
            .iter()
            .find(|Declaration(row)| row[0] & 255 == rec_code && row[0] >> 8 & 255 == 3)
        else {
            return Ok(next);
        };
        if head >> 24 != code
            || !next.has(words(deps, deps_hi) & !group_mask)
            || rec.is_unsafe
            || rec.k != (head >> 17 & 1 != 0)
            || rec.num_params != data & 255
            || rec.num_indices != data >> 8 & 255
            || rec.num_motives != data >> 16 & 255
            || rec.num_minors != data >> 24
            || !scope(scope_word, slice(request.names, rec.parameters)?, n, b)?
            || !matching::expression(expected_ty, rec.ty, e, l, n, b)?
        {
            return Ok(next);
        }
        let [all] = slice(request.names, rec.all)? else {
            return Ok(next);
        };
        if !matching::name(code, *all, n, b)? {
            return Ok(next);
        }
        let actual_rules = slice(request.rules, rec.rules)?;
        let start = (rule_span & 65535) as usize;
        let count = (rule_span >> 16) as usize;
        let expected_rules = manifest::RULES
            .get(start..start + count)
            .ok_or(ResourceError::Invariant)?;
        if actual_rules.len() != count || request.rules.len() != count {
            return Ok(next);
        }
        for (rule, &Rule([ctor_code, fields, rhs])) in actual_rules.iter().zip(expected_rules) {
            if rule.num_fields != fields
                || !matching::name(ctor_code, rule.constructor, n, b)?
                || !matching::expression(rhs, rule.rhs, e, l, n, b)?
            {
                return Ok(next);
            }
        }
        next.insert(group_mask);
        if code == 1 {
            // Bool's order and exact zero-field constructors were checked above.
            next.0[3] = request.constructors[0].name.0;
            next.0[4] = request.constructors[1].name.0;
        }
        Ok(next)
    }
}

impl Environment {
    /// Identify a certified operation before deciding how to expose operands.
    /// The result belongs to this exact committed environment and use scope;
    /// it is not a transferable certificate or permission to skip operand typing.
    /// `true` denotes equality and `false` denotes less-than-or-equal.
    pub(crate) fn natural_predicate_kind(
        &self,
        site: &ConstantUse<'_>,
        levels: &Levels,
        names: &Names,
        budget: &mut Budget,
    ) -> Result<Option<bool>, UseError> {
        if site.formation.is_some() || (self.predicates.0[1] == 0 && self.predicates.0[2] == 0) {
            return Ok(None);
        }
        self.check_visibility(site.before, None)?;
        let canonical = names.summary(site.name, budget)?.canonical as usize;
        let encoded = self.by_name.get(canonical).copied().unwrap_or(0);
        let equality = if encoded != 0 && encoded == self.predicates.0[1] {
            true
        } else if encoded != 0 && encoded == self.predicates.0[2] {
            false
        } else {
            return Ok(None);
        };
        if encoded as usize > site.before || encoded > self.committed {
            return Ok(None);
        }
        let entry = self.check_use(site, levels, names, budget)?;
        if entry.slot != Some(encoded - 1)
            || entry.kind != StoredKind::Ordinary(Kind::Definition)
            || entry.safety != Safety::Safe
        {
            return Err(ResourceError::Invariant.into());
        }
        if !site.arguments.is_empty() {
            return Err(UseError::Arity);
        }
        Ok(Some(equality))
    }

    /// Same-owner committed arithmetic authority. No signature/auxiliary phase
    /// or generated declaration can query or mint these original referents.
    pub(crate) fn natural_arithmetic_kind(
        &self,
        site: &ConstantUse<'_>,
        levels: &Levels,
        names: &Names,
        budget: &mut Budget,
    ) -> Result<Option<crate::check::natural::Operation>, UseError> {
        use crate::check::natural::Operation;
        if site.formation.is_some() {
            return Ok(None);
        }
        self.check_visibility(site.before, None)?;
        let division = self.certified_division_slot(site.before, None)?;
        let modulus = self.certified_modulus_slot(site.before, None)?;
        if self.predicates.0[6..10] == [0; 4]
            && division.is_none()
            && modulus.is_none()
            && !self.native_natural.any_ready()
        {
            return Ok(None);
        }
        let canonical = names.summary(site.name, budget)?.canonical as usize;
        let encoded = self.by_name.get(canonical).copied().unwrap_or(0);
        if encoded == 0 || encoded as usize > site.before || encoded > self.committed {
            return Ok(None);
        }
        let old = self.predicates.0[6..10]
            .iter()
            .position(|&slot| slot == encoded);
        let operation = old
            .map(|index| {
                [
                    Operation::Add,
                    Operation::Mul,
                    Operation::Pow,
                    Operation::Sub,
                ][index]
            })
            .or_else(|| (division == Some(encoded)).then_some(Operation::Div))
            .or_else(|| (modulus == Some(encoded)).then_some(Operation::Mod));
        let operation = match operation {
            Some(op) => Some(op),
            None => self
                .native_natural
                .operation(encoded, site.before, self.committed)?,
        };
        let Some(operation) = operation else {
            return Ok(None);
        };
        let entry = self.check_use(site, levels, names, budget)?;
        if entry.slot != Some(encoded - 1)
            || entry.kind != StoredKind::Ordinary(Kind::Definition)
            || entry.safety != Safety::Safe
        {
            return Err(ResourceError::Invariant.into());
        }
        if !site.arguments.is_empty() {
            return Err(UseError::Arity);
        }
        Ok(Some(operation))
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn natural_arithmetic_result(
        &self,
        site: &ConstantUse<'_>,
        left: ExprKind<'_>,
        right: ExprKind<'_>,
        levels: &Levels,
        names: &Names,
        budget: &mut Budget,
    ) -> Result<Option<crate::check::natural::Digits>, UseError> {
        let Some(operation) = self.natural_arithmetic_kind(site, levels, names, budget)? else {
            return Ok(None);
        };
        let number = |kind, budget: &mut Budget| -> Result<Option<&[u8]>, ResourceError> {
            match kind {
                ExprKind::Natural(bytes) => Ok(Some(bytes)),
                ExprKind::Constant(name, []) if matching::name(18, name, names, budget)? => {
                    Ok(Some(b"0"))
                }
                _ => Ok(None),
            }
        };
        let Some(left) = number(left, budget)? else {
            return Ok(None);
        };
        let Some(right) = number(right, budget)? else {
            return Ok(None);
        };
        match crate::check::natural::arithmetic(operation, left, right, budget) {
            Ok(digits) => Ok(Some(digits)),
            Err(crate::check::natural::Error::Unsupported) => Err(UseError::LiteralArithmetic),
            Err(crate::check::natural::Error::Resource(error)) => Err(error.into()),
        }
    }

    /// Full-exposure primitive over two already checked canonical Nat literals.
    /// Authority is the retained committed slot, never this name by itself.
    /// No staging, theorem-copy or cross-environment authority is introduced.
    #[allow(clippy::too_many_arguments)]
    /// The committed Bool constructor for a completed predicate answer.
    pub(crate) fn natural_predicate_constructor(&self, answer: bool) -> Option<NameId> {
        let name = self.predicates.0[if answer { 4 } else { 3 }];
        (name != 0).then_some(NameId(name))
    }
    pub(crate) fn natural_predicate_result(
        &self,
        site: &ConstantUse<'_>,
        left: ExprKind<'_>,
        right: ExprKind<'_>,
        levels: &Levels,
        names: &Names,
        budget: &mut Budget,
    ) -> Result<Option<NameId>, UseError> {
        let Some(equality) = self.natural_predicate_kind(site, levels, names, budget)? else {
            return Ok(None);
        };
        // The completed dependency closure includes exact Nat/zero. Constant
        // spelling alone is never enough: this is after the committed predicate
        // slot and all of its dependency bits have been established.
        let number = |kind, budget: &mut Budget| -> Result<Option<&[u8]>, ResourceError> {
            match kind {
                ExprKind::Natural(bytes) => Ok(Some(bytes)),
                ExprKind::Constant(name, []) if matching::name(18, name, names, budget)? => {
                    Ok(Some(b"0"))
                }
                _ => Ok(None),
            }
        };
        let Some(left) = number(left, budget)? else {
            return Ok(None);
        };
        let Some(right) = number(right, budget)? else {
            return Ok(None);
        };
        let work = left
            .len()
            .checked_add(right.len())
            .and_then(|x| x.checked_add(4))
            .ok_or(ResourceError::Counter)?;
        budget.charge_work(u64::try_from(work).map_err(|_| ResourceError::Counter)?)?;
        // Store invariant: ASCII decimal digits, no leading zero except zero.
        // Same-length lexical order is numeric order; no parser or allocation.
        let order = left.len().cmp(&right.len()).then_with(|| left.cmp(right));
        let answer = if equality {
            order.is_eq()
        } else {
            !order.is_gt()
        };
        let name = self.predicates.0[if answer { 4 } else { 3 }];
        if name == 0 {
            return Err(ResourceError::Invariant.into());
        }
        Ok(Some(NameId(name)))
    }
}
