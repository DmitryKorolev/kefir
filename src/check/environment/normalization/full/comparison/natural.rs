//! Paired Nat constructor tests authority.
use super::*;
use crate::syntax::levels::LevelNames;
pub(super) mod primitive;

pub(super) enum Pair {
    Zero,
    Successors(ExprId, ExprId),
    Unavailable,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn classify(
    left: ExprId,
    right: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
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
    enum Shape {
        Zero(crate::syntax::levels::NameId),
        Successors(
            crate::syntax::levels::NameId,
            ExprId,
            crate::syntax::levels::NameId,
            ExprId,
        ),
    }
    let shape = match (a, b) {
        (ExprKind::Natural(b"0"), ExprKind::Constant(name, []))
        | (ExprKind::Constant(name, []), ExprKind::Natural(b"0")) => Shape::Zero(name),
        (ExprKind::App(af, ax), ExprKind::App(bf, bx)) => {
            match (
                expressions
                    .get(af, budget)?
                    .kind(expressions, levels, budget)?,
                expressions
                    .get(bf, budget)?
                    .kind(expressions, levels, budget)?,
            ) {
                (ExprKind::Constant(an, []), ExprKind::Constant(bn, [])) => {
                    Shape::Successors(an, ax, bn, bx)
                }
                _ => return Ok(Pair::Unavailable),
            }
        }
        _ => return Ok(Pair::Unavailable),
    };
    // Both operands have checked derivations in this exact session. Only the
    // committed original Nat group can justify literal/constructor identity;
    // neither a same-named impostor nor private inductive staging supplies it.
    let Some((_, zero, successor)) = environment.natural_constructors(
        scope.before,
        scope.formation,
        scope.expression_end,
        expressions,
        budget,
    )?
    else {
        return Ok(Pair::Unavailable);
    };
    Ok(match shape {
        Shape::Zero(name)
            if names.summary(name, budget)?.canonical == names.summary(zero, budget)?.canonical =>
        {
            Pair::Zero
        }
        Shape::Successors(an, ax, bn, bx) => {
            let successor = names.summary(successor, budget)?.canonical;
            if names.summary(an, budget)?.canonical == successor
                && names.summary(bn, budget)?.canonical == successor
            {
                Pair::Successors(ax, bx)
            } else {
                Pair::Unavailable
            }
        }
        _ => Pair::Unavailable,
    })
}

/// Paired-loop predecessor rule on checked operands in this exact session.
/// Only one literal layer is materialized, after committed Nat authority is found.
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
    let classified = classify(
        left,
        right,
        scope,
        environment,
        expressions,
        levels,
        names,
        budget,
    )?;
    if !matches!(classified, Pair::Unavailable) {
        return Ok(classified);
    }
    let a = expressions
        .get(left, budget)?
        .kind(expressions, levels, budget)?;
    let b = expressions
        .get(right, budget)?
        .kind(expressions, levels, budget)?;
    let (bytes, function, argument, literal_left) = match (a, b) {
        (ExprKind::Natural(bytes), ExprKind::App(function, argument)) if bytes != b"0" => {
            (bytes, function, argument, true)
        }
        (ExprKind::App(function, argument), ExprKind::Natural(bytes)) if bytes != b"0" => {
            (bytes, function, argument, false)
        }
        _ => return Ok(Pair::Unavailable),
    };
    let ExprKind::Constant(name, []) =
        expressions
            .get(function, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(Pair::Unavailable);
    };
    let Some((_, _, successor)) = environment.natural_constructors(
        scope.before,
        scope.formation,
        scope.expression_end,
        expressions,
        budget,
    )?
    else {
        return Ok(Pair::Unavailable);
    };
    if names.summary(name, budget)?.canonical != names.summary(successor, budget)?.canonical {
        return Ok(Pair::Unavailable);
    }
    let digits =
        crate::check::natural::predecessor(bytes, budget).map_err(|error| match error {
            crate::check::natural::Error::Resource(error) => HeadError::from(error),
            crate::check::natural::Error::Unsupported => HeadError::Unsupported,
        })?;
    let appended = expressions.append(ExprKind::Natural(digits.as_bytes()), levels, names, budget);
    let retired = digits.retire(budget);
    if let Some(error) = select_failure([
        appended.as_ref().err().copied().map(HeadError::from),
        retired.err().map(HeadError::from),
        None,
        None,
    ]) {
        return Err(error);
    }
    let predecessor = appended?;
    Ok(if literal_left {
        Pair::Successors(predecessor, argument)
    } else {
        Pair::Successors(argument, predecessor)
    })
}

/// Positive fallback only: both roots are completed normalizations of checked
/// terms in this session. No successor recursion or negative authority is supplied.
#[allow(clippy::too_many_arguments)]
pub(super) fn zero_identity(
    left: ExprId,
    right: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    let a = expressions
        .get(left, budget)?
        .kind(expressions, levels, budget)?;
    let b = expressions
        .get(right, budget)?
        .kind(expressions, levels, budget)?;
    if !matches!(
        (a, b),
        (ExprKind::Natural(b"0"), ExprKind::Constant(_, []))
            | (ExprKind::Constant(_, []), ExprKind::Natural(b"0"))
    ) {
        return Ok(false);
    }
    Ok(matches!(
        classify(
            left,
            right,
            scope,
            environment,
            expressions,
            levels,
            names,
            budget
        )?,
        Pair::Zero
    ))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Distinct {
    Proven,
    Unavailable,
}

/// Shape certificate for C13 only. The owner has completed C4 and head/paired
/// work on checked operands, and must still discharge C12 after this returns.
/// Scope is this comparison's environment and phase; no result is retained.
#[allow(clippy::too_many_arguments)]
pub(super) fn distinct_constructors(
    left: ExprKind<'_>,
    right: ExprKind<'_>,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Distinct, HeadError> {
    let (zero_shape, head) = match (left, right) {
        (z @ (ExprKind::Constant(_, []) | ExprKind::Natural(b"0")), ExprKind::App(f, _))
        | (ExprKind::App(f, _), z @ (ExprKind::Constant(_, []) | ExprKind::Natural(b"0"))) => {
            (z, f)
        }
        _ => return Ok(Distinct::Unavailable),
    };
    let ExprKind::Constant(name, []) =
        expressions
            .get(head, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(Distinct::Unavailable);
    };
    let Some((_, zero, successor)) = environment.natural_constructors(
        scope.before,
        scope.formation,
        scope.expression_end,
        expressions,
        budget,
    )?
    else {
        return Ok(Distinct::Unavailable);
    };
    if names.summary(name, budget)?.canonical != names.summary(successor, budget)?.canonical {
        return Ok(Distinct::Unavailable);
    }
    match zero_shape {
        ExprKind::Natural(b"0") => Ok(Distinct::Proven),
        ExprKind::Constant(name, []) => Ok(
            if names.summary(name, budget)?.canonical == names.summary(zero, budget)?.canonical {
                Distinct::Proven
            } else {
                Distinct::Unavailable
            },
        ),
        _ => Err(ResourceError::Invariant.into()),
    }
}

/// C9's certified closed predicate step only. Ordinary unfolding is deliberately
/// absent: a failed fallback can never manufacture a restarted negative route.
#[allow(clippy::too_many_arguments)]
pub(super) fn predicate_step(
    root: ExprId,
    incoming: ReductionPath,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &mut Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Option<Head>, HeadError> {
    use crate::check::environment::constant_use::ConstantUse;
    if expressions.get(root, budget)?.has_free() {
        return Ok(None);
    }
    let ExprKind::App(function, right) =
        expressions
            .get(root, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(None);
    };
    let ExprKind::App(head, left) =
        expressions
            .get(function, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(None);
    };
    let ExprKind::Constant(name, arguments) =
        expressions
            .get(head, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(None);
    };
    let site = ConstantUse {
        name,
        arguments,
        parameters: scope.parameters,
        before: scope.before,
        formation: scope.formation,
        mode: scope.mode,
        expression_end: scope.expression_end,
        level_end: scope.level_end,
    };
    let Some(result) = environment.natural_predicate_result(
        &site,
        expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?,
        expressions
            .get(right, budget)?
            .kind(expressions, levels, budget)?,
        levels,
        names,
        budget,
    )?
    else {
        return Ok(None);
    };
    let path = incoming.after_reduction()?;
    let expression = expressions.append(ExprKind::Constant(result, &[]), levels, names, budget)?;
    budget.observe(crate::resource::Event::Reductions, 1);
    Ok(Some(Head { expression, path }))
}
