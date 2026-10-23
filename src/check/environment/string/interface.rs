//! Checked public typing witness for the existing literal expansion.
//! This never certifies function behavior, byte injectivity, or native arithmetic.
use super::*;
use crate::decode::primitive_decode::inductives::{Request as Group, Span};
use crate::syntax::expressions::ExprKind;
use crate::syntax::levels::{LevelId, LevelKind};

const COMPLETE: u32 = (1 << 7) - 1;

fn role(name: NameId, names: &Names, b: &mut Budget) -> Result<Option<usize>, ResourceError> {
    let candidate = candidate(name, names, b)?;
    b.charge_work(7)?;
    Ok(candidate.and_then(|candidate| ROOTS.iter().position(|&root| root == candidate)))
}

struct Shape<'a, 'b> {
    e: &'a Expressions,
    l: &'a Levels,
    n: &'a Names,
    b: &'b mut Budget,
}
impl<'a> Shape<'a, '_> {
    fn kind(&mut self, root: ExprId) -> Result<ExprKind<'a>, ResourceError> {
        self.e.get(root, self.b)?.kind(self.e, self.l, self.b)
    }
    fn same_name(&mut self, a: NameId, c: NameId) -> Result<bool, ResourceError> {
        Ok(self.n.summary(a, self.b)?.canonical == self.n.summary(c, self.b)?.canonical)
    }
    fn named(&mut self, name: NameId, index: usize) -> Result<bool, ResourceError> {
        matching::name(manifest::REFERENT_NAMES[ROOTS[index]], name, self.n, self.b)
    }
    fn parameter(&mut self, level: LevelId, parameter: NameId) -> Result<bool, ResourceError> {
        let LevelKind::Param(name) = self.l.get(level, self.b)?.kind() else {
            return Ok(false);
        };
        self.same_name(name, parameter)
    }
    fn universe(
        &mut self,
        level: LevelId,
        parameter: Option<NameId>,
    ) -> Result<bool, ResourceError> {
        let LevelKind::Succ(inner) = self.l.get(level, self.b)?.kind() else {
            return Ok(false);
        };
        match parameter {
            Some(parameter) => self.parameter(inner, parameter),
            None => Ok(matches!(self.l.get(inner, self.b)?.kind(), LevelKind::Zero)),
        }
    }
    fn sort(&mut self, root: ExprId, parameter: Option<NameId>) -> Result<bool, ResourceError> {
        let ExprKind::Sort(level) = self.kind(root)? else {
            return Ok(false);
        };
        self.universe(level, parameter)
    }
    fn constant(&mut self, root: ExprId, index: usize) -> Result<bool, ResourceError> {
        let ExprKind::Constant(name, []) = self.kind(root)? else {
            return Ok(false);
        };
        self.named(name, index)
    }
    fn bound(&mut self, root: ExprId, index: u32) -> Result<bool, ResourceError> {
        Ok(matches!(self.kind(root)?, ExprKind::Bound(actual) if actual == index))
    }
    fn list(
        &mut self,
        root: ExprId,
        parameter: Option<NameId>,
        argument: Option<u32>,
    ) -> Result<bool, ResourceError> {
        let ExprKind::App(head, arg) = self.kind(root)? else {
            return Ok(false);
        };
        let ExprKind::Constant(name, [level]) = self.kind(head)? else {
            return Ok(false);
        };
        if !self.named(name, 2)? {
            return Ok(false);
        }
        let instance = match parameter {
            Some(parameter) => self.parameter(*level, parameter)?,
            None => matches!(self.l.get(*level, self.b)?.kind(), LevelKind::Zero),
        };
        if !instance {
            return Ok(false);
        }
        match argument {
            Some(index) => self.bound(arg, index),
            None => self.constant(arg, 5),
        }
    }
    fn signature(
        &mut self,
        index: usize,
        root: ExprId,
        parameters: &[NameId],
        natural: Option<NameId>,
    ) -> Result<bool, ResourceError> {
        // The expansion supplies [] to monomorphic roles and [0] to List
        // constructors. Unused declaration universe parameters matter too.
        match index {
            0 | 5 if parameters.is_empty() => self.sort(root, None),
            2..=4 if parameters.len() == 1 => {
                let parameter = parameters[0];
                let ExprKind::Pi(_, domain, body, _) = self.kind(root)? else {
                    return Ok(false);
                };
                if !self.sort(domain, Some(parameter))? {
                    return Ok(false);
                }
                match index {
                    2 => self.sort(body, Some(parameter)),
                    3 => self.list(body, Some(parameter), Some(0)),
                    4 => {
                        let ExprKind::Pi(_, domain, body, _) = self.kind(body)? else {
                            return Ok(false);
                        };
                        if !self.bound(domain, 0)? {
                            return Ok(false);
                        }
                        let ExprKind::Pi(_, domain, body, _) = self.kind(body)? else {
                            return Ok(false);
                        };
                        Ok(self.list(domain, Some(parameter), Some(1))?
                            && self.list(body, Some(parameter), Some(2))?)
                    }
                    _ => Err(ResourceError::Invariant),
                }
            }
            1 | 6 if parameters.is_empty() => {
                let ExprKind::Pi(_, domain, body, _) = self.kind(root)? else {
                    return Ok(false);
                };
                if index == 1 {
                    Ok(self.list(domain, None, None)? && self.constant(body, 0)?)
                } else {
                    let Some(natural) = natural else {
                        return Ok(false);
                    };
                    let ExprKind::Constant(name, []) = self.kind(domain)? else {
                        return Ok(false);
                    };
                    Ok(self.same_name(name, natural)? && self.constant(body, 5)?)
                }
            }
            _ => Ok(false),
        }
    }
}

impl Certificate {
    fn interface_insert(&mut self, index: usize, slot: u32) -> Result<(), ResourceError> {
        if index >= self.slots.len() || slot == 0 {
            return Err(ResourceError::Invariant);
        }
        if self.slots[index] != 0 && self.slots[index] != slot {
            return Err(ResourceError::Invariant);
        }
        self.slots[index] = slot;
        self.interface_mask |= 1 << index;
        Ok(())
    }
    fn interface_finish(
        &mut self,
        after: u32,
        natural: natural::Certificate,
        committed: u32,
    ) -> Result<(), ResourceError> {
        if self.interface_mask != COMPLETE || natural.0[0] == 0 {
            return Ok(());
        }
        if after == 0
            || natural.0[0] > committed
            || natural.0[0] > after
            || self.slots.iter().any(|&slot| slot == 0 || slot > after)
        {
            return Err(ResourceError::Invariant);
        }
        // All seven role bits came from successful ORIGINAL declaration/group
        // validation. This copy is inert until the same infallible commit.
        // Nat is from an earlier committed group, so this boundary covers it.
        self.interface_frontier = after;
        Ok(())
    }
}

fn parameters(names: &[NameId], span: Span) -> Result<&[NameId], ResourceError> {
    let end = (span.start as usize)
        .checked_add(span.len as usize)
        .ok_or(ResourceError::Counter)?;
    names
        .get(span.start as usize..end)
        .ok_or(ResourceError::Invariant)
}

impl Environment {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn prepare_string_interface_definition(
        &self,
        previous: Certificate,
        request: &Request<'_>,
        n: &Names,
        l: &Levels,
        e: &Expressions,
        b: &mut Budget,
    ) -> Result<Certificate, ResourceError> {
        if previous.interface_frontier != 0
            || request.kind != Kind::Definition
            || request.safety != Safety::Safe
        {
            return Ok(previous);
        }
        let Some(index @ (1 | 6)) = role(request.name, n, b)? else {
            return Ok(previous);
        };
        b.charge_work(64)?; // fixed, bounded public type inspection, no allocation
        let natural = (self.natural.0[0] != 0).then_some(NameId(self.natural.0[1]));
        let mut shape = Shape { e, l, n, b };
        if !shape.signature(index, request.ty, request.parameters, natural)? {
            return Ok(previous);
        }
        if request.value.is_none() {
            return Err(ResourceError::Invariant);
        }
        let after = self
            .committed
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        let mut next = previous;
        next.interface_insert(index, after)?;
        next.interface_finish(after, self.natural, self.committed)?;
        Ok(next)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn prepare_string_interface_group(
        &self,
        previous: Certificate,
        request: &Group<'_>,
        n: &Names,
        l: &Levels,
        e: &Expressions,
        b: &mut Budget,
    ) -> Result<Certificate, ResourceError> {
        if previous.interface_frontier != 0 {
            return Ok(previous);
        }
        let phase = self.stage.ok_or(ResourceError::Invariant)?.phase;
        let mut next = previous;
        for family in request.types {
            let Some(index @ (0 | 2 | 5)) = role(family.name, n, b)? else {
                continue;
            };
            if family.is_unsafe {
                continue;
            }
            b.charge_work(64)?;
            let mut shape = Shape { e, l, n, b };
            if !shape.signature(
                index,
                family.ty,
                parameters(request.names, family.parameters)?,
                None,
            )? {
                continue;
            }
            let signature = self
                .lookup_visible(family.name, phase.before(), Some(phase), n, b)?
                .ok_or(ResourceError::Invariant)?;
            if signature.kind != StoredKind::Signature(SignatureKind::Inductive)
                || signature.ty != TypeSource::Original(family.ty)
            {
                return Err(ResourceError::Invariant);
            }
            let original_slot = signature.slot.ok_or(ResourceError::Invariant)?;
            if original_slot < self.committed {
                return Err(ResourceError::Invariant);
            }
            let slot = original_slot.checked_add(1).ok_or(ResourceError::Counter)?;
            next.interface_insert(index, slot)?;
        }
        for constructor in request.constructors {
            let Some(index @ (3 | 4)) = role(constructor.name, n, b)? else {
                continue;
            };
            if constructor.is_unsafe {
                continue;
            }
            b.charge_work(64)?;
            let mut shape = Shape { e, l, n, b };
            if !shape.named(constructor.inductive, 2)?
                || !shape.signature(
                    index,
                    constructor.ty,
                    parameters(request.names, constructor.parameters)?,
                    None,
                )?
            {
                continue;
            }
            // Group validation already rederived ownership and metadata. Check
            // the retained original staged signature, never a generated copy.
            let signature = self
                .lookup_visible(constructor.name, phase.before(), Some(phase), n, b)?
                .ok_or(ResourceError::Invariant)?;
            if signature.kind != StoredKind::Signature(SignatureKind::Constructor)
                || signature.ty != TypeSource::Original(constructor.ty)
            {
                return Err(ResourceError::Invariant);
            }
            let original_slot = signature.slot.ok_or(ResourceError::Invariant)?;
            if original_slot < self.committed {
                return Err(ResourceError::Invariant);
            }
            let slot = original_slot.checked_add(1).ok_or(ResourceError::Counter)?;
            next.interface_insert(index, slot)?;
        }
        let after = u32::try_from(self.entries.len()).map_err(|_| ResourceError::Counter)?;
        next.interface_finish(after, self.natural, self.committed)?;
        Ok(next)
    }
}
