//! Base Nat interpretation. Only a fully checked original group can
//! prepare this certificate; the existing infallible block commit publishes it.
use super::*;
use crate::decode::primitive_decode::inductives::Request as Group;
use crate::syntax::expressions::{ExprKind, Expressions};
use crate::syntax::levels::{LevelKind, Levels};
use crate::syntax::names::Component;

#[derive(Clone, Copy, Default)]
// Minimum committed frontier, original Nat/zero/succ names, original zero type.
pub(super) struct Certificate(pub(super) [u32; 5]);
const _: () = assert!(size_of::<Certificate>() == 20);
fn named(
    name: NameId,
    prefix: NameId,
    text: &str,
    names: &Names,
    b: &mut Budget,
) -> Result<bool, ResourceError> {
    let Some((actual, Component::String(component))) = names.view(name, b)? else {
        return Ok(false);
    };
    Ok(component == text
        && names.summary(actual, b)?.canonical == names.summary(prefix, b)?.canonical)
}
fn family_type(
    root: ExprId,
    family: NameId,
    e: &Expressions,
    l: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<bool, ResourceError> {
    match e.get(root, b)?.kind(e, l, b)? {
        ExprKind::Constant(name, []) => {
            Ok(names.summary(name, b)?.canonical == names.summary(family, b)?.canonical)
        }
        _ => Ok(false),
    }
}
impl Environment {
    /// Caller has finished all group derivation, exact export matching
    /// and generated rule checks. This fixed manifest inspection adds no semantic
    /// authority to a shape that has merely decoded or reached a private phase.
    pub(super) fn prepare_natural(
        &self,
        request: &Group<'_>,
        names: &Names,
        levels: &Levels,
        expressions: &Expressions,
        b: &mut Budget,
    ) -> Result<Certificate, ResourceError> {
        let absent = Certificate::default();
        if request.types.len() != 1
            || request.constructors.len() != 2
            || request.recursors.len() != 1
        {
            return Ok(absent);
        }
        let family = request.types[0];
        if !named(family.name, NameId::ANONYMOUS, "Nat", names, b)? {
            return Ok(absent);
        }
        b.charge_work(12)?; // fixed bounded shape inspection; no allocation
        if family.is_unsafe
            || family.parameters.len != 0
            || family.num_params != 0
            || family.num_indices != 0
            || family.num_nested != 0
            || family.all.len != 1
            || family.constructors.len != 2
        {
            return Ok(absent);
        }
        let ExprKind::Sort(level) = expressions
            .get(family.ty, b)?
            .kind(expressions, levels, b)?
        else {
            return Ok(absent);
        };
        let LevelKind::Succ(zero) = levels.get(level, b)?.kind() else {
            return Ok(absent);
        };
        if !matches!(levels.get(zero, b)?.kind(), LevelKind::Zero) {
            return Ok(absent);
        }
        let start = family.constructors.start as usize;
        let order = request
            .names
            .get(start..start + 2)
            .ok_or(ResourceError::Invariant)?;
        if !named(order[0], family.name, "zero", names, b)?
            || !named(order[1], family.name, "succ", names, b)?
        {
            return Ok(absent);
        }
        let recursor = request.recursors[0];
        if !named(recursor.name, family.name, "rec", names, b)?
            || recursor.k
            || recursor.num_params != 0
            || recursor.num_indices != 0
            || recursor.num_motives != 1
            || recursor.num_minors != 2
        {
            return Ok(absent);
        }
        let mut constructors = [None, None];
        for constructor in request.constructors {
            for (index, &name) in order.iter().enumerate() {
                if names.summary(constructor.name, b)?.canonical
                    == names.summary(name, b)?.canonical
                {
                    constructors[index] = Some(constructor);
                }
            }
        }
        let zero = constructors[0].ok_or(ResourceError::Invariant)?;
        let succ = constructors[1].ok_or(ResourceError::Invariant)?;
        if !family_type(zero.ty, family.name, expressions, levels, names, b)? {
            return Ok(absent);
        }
        let ExprKind::Pi(_, domain, body, _) =
            expressions.get(succ.ty, b)?.kind(expressions, levels, b)?
        else {
            return Ok(absent);
        };
        if !family_type(domain, family.name, expressions, levels, names, b)?
            || !family_type(body, family.name, expressions, levels, names, b)?
        {
            return Ok(absent);
        }
        Ok(Certificate([
            u32::try_from(self.entries.len()).map_err(|_| ResourceError::Counter)?,
            family.name.0,
            order[0].0,
            order[1].0,
            zero.ty.slot(),
        ]))
    }
    /// Existing committed authority is usable during ordinary checking after a
    /// theorem copy completes. Copying itself neither queries nor mints it.
    /// A later inductive signature phase may read this prior certificate, never
    /// mint or shadow it. All handles have this owner's original store provenance;
    /// the current declaration retains those roots.
    pub(crate) fn natural_type(
        &self,
        before: usize,
        formation: Option<Formation>,
        expression_end: usize,
        expressions: &Expressions,
        b: &mut Budget,
    ) -> Result<Option<ExprId>, ResourceError> {
        self.check_visibility(before, formation)?;
        b.charge_work(1)?;
        let certificate = self.natural;
        if certificate.0[0] == 0 || before < certificate.0[0] as usize {
            return Ok(None);
        }
        if certificate.0[4] as usize >= expression_end || certificate.0[0] > self.committed {
            return Err(ResourceError::Invariant);
        }
        if formation.is_some() {
            let stage = self.stage.ok_or(ResourceError::Invariant)?;
            if stage.expression_end as usize != expression_end {
                return Err(ResourceError::Invariant);
            }
            // Construction invariant: an inductive group's private prefix starts
            // with its family signature; quotient and unsafe-candidate phases
            // cannot append an inductive signature. This classifies the phase,
            // not the new group's validity. All its derivation/rechecking remains
            // required before publication. Empty stages have no such authority.
            if !self
                .entries
                .get(self.committed as usize)
                .is_some_and(|entry| entry.kind == StoredKind::Signature(SignatureKind::Inductive))
            {
                return Ok(None);
            }
        }
        // Resolve only the retained original slot. In particular, neither the
        // current name index nor any staged declaration supplies this authority.
        Ok(Some(expressions.resolve_slot(certificate.0[4], b)?))
    }
}

impl Environment {
    /// Same committed manifest and original-store premises as literal typing.
    /// This is only identity recognition; exact application arity and universes
    /// remain the consuming head rule's responsibility.
    pub(crate) fn natural_constructors(
        &self,
        before: usize,
        formation: Option<Formation>,
        expression_end: usize,
        expressions: &Expressions,
        b: &mut Budget,
    ) -> Result<Option<(NameId, NameId, NameId)>, ResourceError> {
        if self
            .natural_type(before, formation, expression_end, expressions, b)?
            .is_none()
        {
            return Ok(None);
        }
        Ok(Some((
            NameId(self.natural.0[1]),
            NameId(self.natural.0[2]),
            NameId(self.natural.0[3]),
        )))
    }
}
