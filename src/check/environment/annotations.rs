//! The narrow generated-binder exception. Certificates grant no delta authority.
use super::*;
use crate::syntax::expressions::{ExprKind, Expressions};
use crate::syntax::levels::Levels;
use crate::syntax::names::Component;

pub(super) fn annotation(
    name: NameId,
    names: &Names,
    budget: &mut Budget,
) -> Result<Option<(usize, usize)>, ResourceError> {
    let Some((prefix, Component::String(text))) = names.view(name, budget)? else {
        return Ok(None);
    };
    if names.summary(prefix, budget)?.canonical
        != names.summary(NameId::ANONYMOUS, budget)?.canonical
    {
        return Ok(None);
    }
    Ok(match text {
        "outParam" => Some((0, 1)),
        "semiOutParam" => Some((1, 1)),
        "optParam" => Some((2, 2)),
        "autoParam" => Some((3, 2)),
        _ => None,
    })
}
impl Environment {
    /// Called only after the ordinary declaration's full checking and cleanup.
    /// Inspect at most three original nodes; no reduction or cache publication.
    pub(super) fn prepare_annotation(
        request: &Request<'_>,
        names: &Names,
        levels: &Levels,
        expressions: &Expressions,
        budget: &mut Budget,
    ) -> Result<Option<usize>, ResourceError> {
        if request.kind != Kind::Definition || request.safety != Safety::Safe {
            return Ok(None);
        }
        let Some((slot, arity)) = annotation(request.name, names, budget)? else {
            return Ok(None);
        };
        budget.charge_work((arity + 1) as u64)?;
        let Some(mut body) = request.value else {
            return Err(ResourceError::Invariant);
        };
        for _ in 0..arity {
            let ExprKind::Lambda(_, _, next, _) =
                expressions
                    .get(body, budget)?
                    .kind(expressions, levels, budget)?
            else {
                return Ok(None);
            };
            body = next;
        }
        Ok(matches!(expressions.get(body, budget)?.kind(expressions, levels, budget)?, ExprKind::Bound(index) if index as usize == arity - 1).then_some(slot))
    }
    /// Infallible and immediately after successful ordinary publication. No caller
    /// may retain a prepared certificate across another publication or environment.
    pub(super) fn commit_annotation(&mut self, certificate: Option<usize>) {
        if let Some(slot) = certificate {
            self.annotation_identity[slot] = self.committed;
        }
    }
    pub(super) fn certified_annotation(
        &self,
        name: NameId,
        slot: usize,
        before: usize,
        names: &Names,
        budget: &mut Budget,
    ) -> Result<bool, ResourceError> {
        budget.charge_work(1)?;
        self.check_visibility(before, None)?;
        let key = names.summary(name, budget)?.canonical as usize;
        let encoded = self.by_name.get(key).copied().unwrap_or(0);
        Ok(encoded != 0 && encoded as usize <= before && self.annotation_identity[slot] == encoded)
    }
}
