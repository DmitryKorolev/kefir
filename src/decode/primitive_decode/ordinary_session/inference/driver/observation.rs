//! Allocation-free cases of the existing checked-operand observation rule.
//! The request's owner retains the typing derivation and exact active context.
//! This helper grants neither checking authority nor permission to cache a type.
use super::*;
use crate::check::environment::normalization::TypeObservation;

pub(super) fn complete(
    request: TypeObservation,
    work: &mut Working<'_>,
) -> Result<Option<Inferred>, Stop> {
    complete_root(request.root(), request.incoming(), work)
}

// Kept private: raw roots alone do not carry observation permission. Tests of
// shape/error boundaries may call this core without manufacturing a capability.
fn complete_root(
    root: ExprId,
    incoming: ReductionPath,
    work: &mut Working<'_>,
) -> Result<Option<Inferred>, Stop> {
    work.budget.charge_work(1)?;
    let ty = match work.expressions.get(root, work.budget)?.kind(
        work.expressions,
        work.levels,
        work.budget,
    )? {
        ExprKind::Free(id) => work.context.get(id, work.budget)?.ty(),
        ExprKind::App(function, _) => {
            let ExprKind::Free(id) = work.expressions.get(function, work.budget)?.kind(
                work.expressions,
                work.levels,
                work.budget,
            )?
            else {
                return Ok(None);
            };
            let ty = work.context.get(id, work.budget)?.ty();
            let ExprKind::Pi(_, _, codomain, _) = work.expressions.get(ty, work.budget)?.kind(
                work.expressions,
                work.levels,
                work.budget,
            )?
            else {
                return Ok(None);
            };
            // Exactly the existing instantiate_application_result identity case:
            // no substitution/index lowering, including underneath binders. The
            // checked observation request already supplies the argument premise.
            if work.expressions.get(codomain, work.budget)?.loose_range() != 0 {
                return Ok(None);
            }
            codomain
        }
        _ => return Ok(None),
    };
    // Reading a local type and exposing an already raw Pi take no reductions.
    // Local values (including let bindings) are irrelevant to this typing rule.
    Ok(Some(Inferred { ty, path: incoming }))
}
