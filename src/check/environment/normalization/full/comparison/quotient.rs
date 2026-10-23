//! Bounded Lift/local shape. Raw classification carries no exposure
//! certificate: only the parent owner's ordered continuation can use a hit.
use super::*;
use crate::check::environment::constant_use::{ConstantUse, UseError};
use crate::decode::primitive_decode::quotients::Role;
use crate::syntax::levels::LevelKind;

fn spine(
    mut root: ExprId,
    expressions: &Expressions,
    levels: &Levels,
    budget: &mut Budget,
) -> Result<(ExprId, usize, Option<ExprId>), HeadError> {
    let mut arity = 0usize;
    let mut last = None;
    loop {
        budget.charge_work(1)?;
        match expressions
            .get(root, budget)?
            .kind(expressions, levels, budget)?
        {
            ExprKind::App(function, argument) => {
                arity = arity.checked_add(1).ok_or(ResourceError::Counter)?;
                if last.is_none() {
                    last = Some(argument);
                }
                root = function;
            }
            _ => return Ok((root, arity, last)),
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn candidate(
    left: ExprId,
    right: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    locals: &LocalContext,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    if scope.formation.is_some() {
        return Ok(false);
    }
    // No allocation or syntax construction. Both operands must be applications;
    // bare locals, partial/extra Lift and function-valued cases grant nothing.
    for root in [left, right] {
        if !matches!(
            expressions
                .get(root, budget)?
                .kind(expressions, levels, budget)?,
            ExprKind::App(..)
        ) {
            return Ok(false);
        }
    }
    for (primitive, other) in [(left, right), (right, left)] {
        let mut head = primitive;
        let mut major = None;
        let mut arity = 0;
        for _ in 0..6 {
            budget.charge_work(1)?;
            let ExprKind::App(function, argument) =
                expressions
                    .get(head, budget)?
                    .kind(expressions, levels, budget)?
            else {
                break;
            };
            if major.is_none() {
                major = Some(argument);
            }
            head = function;
            arity += 1;
        }
        if arity != 6 {
            continue;
        }
        let ExprKind::Constant(name, arguments) =
            expressions
                .get(head, budget)?
                .kind(expressions, levels, budget)?
        else {
            continue;
        };
        let role = environment.quotient_role_use(
            ConstantUse {
                name,
                arguments,
                parameters: scope.parameters,
                before: scope.before,
                formation: scope.formation,
                mode: scope.mode,
                expression_end: scope.expression_end,
                level_end: scope.level_end,
            },
            levels,
            names,
            budget,
        );
        match role {
            Ok(Some(Role::Lift)) => {}
            Ok(_) | Err(UseError::Unavailable | UseError::UnsafeUse) => {}
            Err(error) => return Err(error.into()),
        }
        if !matches!(role, Ok(Some(Role::Lift))) {
            continue;
        }
        let ExprKind::Free(major) = expressions
            .get(major.ok_or(ResourceError::Invariant)?, budget)?
            .kind(expressions, levels, budget)?
        else {
            continue;
        };
        if locals.get(major, budget)?.value().is_some() {
            continue;
        }
        // Arbitrary counterpart traversal is gated by committed Lift authority.
        let local = spine(other, expressions, levels, budget)?;
        let ExprKind::Free(id) =
            expressions
                .get(local.0, budget)?
                .kind(expressions, levels, budget)?
        else {
            continue;
        };
        if local.1 != 0 && locals.get(id, budget)?.value().is_none() {
            return Ok(true);
        }
    }
    Ok(false)
}

pub(super) fn data_type(
    root: ExprId,
    expressions: &Expressions,
    levels: &Levels,
    locals: &LocalContext,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    let ExprKind::Free(id) = expressions
        .get(root, budget)?
        .kind(expressions, levels, budget)?
    else {
        return Ok(false);
    };
    let local = locals.get(id, budget)?;
    if local.value().is_some() {
        return Ok(false);
    }
    let ExprKind::Sort(u) =
        expressions
            .get(local.ty(), budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(false);
    };
    let LevelKind::Succ(inner) = levels.get(u, budget)?.kind() else {
        return Ok(false);
    };
    // One-sided admission uses the exact normalized-zero decision.
    // Other level-one representations conservatively miss, never prove Different.
    Ok(levels.get(inner, budget)?.zero() == LevelZero::Zero)
}
