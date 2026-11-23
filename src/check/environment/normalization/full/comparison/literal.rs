//! Literal/constructor admission before paired delta loses the explicit head.
use super::*;

pub(super) enum Pair {
    Zero,
    Successors(ExprId, ExprId),
    StringLiteral { left: bool, function: ExprId },
    Unavailable,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn paired(
    left: ExprId,
    right: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &mut Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Pair, HeadError> {
    let a = expressions
        .get(left, budget)?
        .kind(expressions, levels, budget)?;
    let b = expressions
        .get(right, budget)?
        .kind(expressions, levels, budget)?;
    match (a, b) {
        (ExprKind::String(_), ExprKind::App(function, _)) => {
            return Ok(Pair::StringLiteral {
                left: true,
                function,
            });
        }
        (ExprKind::App(function, _), ExprKind::String(_)) => {
            return Ok(Pair::StringLiteral {
                left: false,
                function,
            });
        }
        _ => {}
    }
    match natural::classify_paired(a, b, scope, environment, expressions, levels, names, budget)? {
        Pair::Unavailable => natural::paired_predecessors(
            left,
            right,
            scope,
            environment,
            expressions,
            levels,
            names,
            budget,
        ),
        other => Ok(other),
    }
}
