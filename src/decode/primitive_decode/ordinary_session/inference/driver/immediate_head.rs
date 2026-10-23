//! Zero-rewrite cases of the existing head exposure procedure. This returns
//! neither a normal form nor a typing/conversion certificate. The caller holds
//! the same scope and active locals as the ordinary head owner would retain.
use super::*;

pub(super) fn complete(
    root: ExprId,
    incoming: ReductionPath,
    work: &mut Working<'_>,
) -> Result<Option<Head>, Stop> {
    work.budget.charge_work(1)?;
    let exposed = match work.expressions.get(root, work.budget)?.kind(
        work.expressions,
        work.levels,
        work.budget,
    )? {
        ExprKind::Sort(_) | ExprKind::Pi(..) | ExprKind::Lambda(..) => true,
        ExprKind::Free(id) => work.context.get(id, work.budget)?.value().is_none(),
        ExprKind::App(function, _) => {
            match work.expressions.get(function, work.budget)?.kind(
                work.expressions,
                work.levels,
                work.budget,
            )? {
                ExprKind::Free(id) => work.context.get(id, work.budget)?.value().is_none(),
                _ => false,
            }
        }
        _ => false,
    };
    // An active assumption has no zeta step; application arguments do not
    // participate in head exposure. No beta/iota/delta/projection is skipped.
    Ok(exposed.then_some(Head {
        expression: root,
        path: incoming,
    }))
}
