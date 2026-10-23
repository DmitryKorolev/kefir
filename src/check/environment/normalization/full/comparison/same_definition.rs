//! Optional same-regular-definition shortcut.
use super::*;

/// Caller has validated two application heads as the same installed regular
/// definition in the fixed comparison scope. These immutable source handles
/// retain that classification; no body is inspected or installed here.
/// None means a completed universe mismatch, not an enclosing negative.
/// Some(false) requires the common last-to-first arguments before arity fails.
#[allow(clippy::too_many_arguments)]
pub(super) fn prepare(
    left: ExprId,
    right: ExprId,
    pairs: &mut Vec<(ExprId, ExprId)>,
    expressions: &Expressions,
    levels: &mut Levels,
    names: &Names,
    ledger: &mut SessionCacheBudget,
    universes: &mut SharedMemo,
    budget: &mut Budget,
) -> Result<Option<bool>, HeadError> {
    if !pairs.is_empty() {
        return Err(ResourceError::Invariant.into());
    }
    let head = |mut root, budget: &mut Budget| -> Result<ExprId, HeadError> {
        loop {
            budget.charge_work(1)?;
            match expressions
                .get(root, budget)?
                .kind(expressions, levels, budget)?
            {
                ExprKind::App(function, _) => root = function,
                ExprKind::Constant(..) => return Ok(root),
                _ => return Err(ResourceError::Invariant.into()),
            }
        }
    };
    let a = head(left, budget)?;
    let b = head(right, budget)?;
    let ExprKind::Constant(_, xs) =
        expressions
            .get(a, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Err(ResourceError::Invariant.into());
    };
    let ExprKind::Constant(_, ys) =
        expressions
            .get(b, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Err(ResourceError::Invariant.into());
    };
    // Both validated uses have the declaration's exact universe arity.
    if xs.len() != ys.len() {
        return Err(ResourceError::Invariant.into());
    }
    for (&x, &y) in xs.iter().zip(ys) {
        if matches!(
            levels.with_helpers(names, budget, |h| {
                h.compare_universes_with(
                    x,
                    y,
                    Some(SharedTable {
                        memo: &mut *universes,
                        ledger: &mut *ledger,
                    }),
                )
            })?,
            UniverseComparison::NotEqual
        ) {
            return Ok(None);
        }
    }
    let (mut a, mut b) = (left, right);
    let equal_arity = loop {
        budget.charge_work(1)?;
        match (
            expressions
                .get(a, budget)?
                .kind(expressions, levels, budget)?,
            expressions
                .get(b, budget)?
                .kind(expressions, levels, budget)?,
        ) {
            (ExprKind::App(f, x), ExprKind::App(g, y)) => {
                let required = pairs.len().checked_add(1).ok_or(ResourceError::Counter)?;
                budget.reserve_frames(1)?;
                if let Err(error) = budget.grow_vec(pairs, required) {
                    budget.release_frames(1)?;
                    return Err(error.into());
                }
                pairs.push((x, y));
                (a, b) = (f, g);
            }
            (ExprKind::Constant(..), ExprKind::Constant(..)) => break true,
            (ExprKind::App(..), ExprKind::Constant(..))
            | (ExprKind::Constant(..), ExprKind::App(..)) => break false,
            _ => return Err(ResourceError::Invariant.into()),
        }
    };
    // Outer application arguments were gathered first. The owner pops the vector,
    // so reverse once to demand the specified last argument first.
    budget.charge_work(pairs.len() as u64)?;
    pairs.reverse();
    Ok(Some(equal_arity))
}
