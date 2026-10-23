//! Exact committed predicate operands, within one full-head owner and scope.
//! Exposure never checks or installs a declaration. A miss unfolds the already
//! validated body once; it cannot assert inequality or re-arm this same attempt.
use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn resume(
    frame: Iota,
    observed: Head,
    scratch: &mut Scratch,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &mut Expressions,
    levels: &mut Levels,
    names: &Names,
    cache: Option<(
        &mut super::super::super::instantiation::Cache,
        &mut crate::resource::SessionCacheBudget,
    )>,
    b: &mut Budget,
) -> Result<Head, HeadError> {
    let SuspensionPayload::Predicate {
        incoming,
        left_height,
    } = frame.payload
    else {
        return Err(ResourceError::Invariant.into());
    };
    let height = observed.path.height_since(incoming)?;
    let end = scratch.applications.len();
    if end != frame.end as usize || end < 2 || end - 2 < scratch.base() {
        return Err(ResourceError::Invariant.into());
    }
    let left = frame.kind == Suspension::PredicateLeft;
    let position = end - if left { 1 } else { 2 };
    let saved = &mut scratch.applications[position];
    if saved.argument != observed.expression {
        saved.argument = observed.expression;
        // A changed argument invalidates the original application. Equal
        // original/function handles are the established pending-spine marker;
        // readback must build an application instead of returning old syntax.
        saved.original = saved.function;
    }
    if left
        && numeric(
            observed.expression,
            scope,
            environment,
            expressions,
            levels,
            names,
            b,
        )?
    {
        let mut next = frame;
        next.kind = Suspension::PredicateRight;
        next.payload = SuspensionPayload::Predicate {
            incoming,
            left_height: height,
        };
        scratch.suspend(next, b)?;
        return Ok(Head {
            expression: scratch.applications[end - 2].argument,
            path: incoming,
        });
    }
    let path = if left {
        observed.path
    } else {
        incoming.after_height(left_height)?.maximum(observed.path)
    };
    let ExprKind::Constant(name, []) =
        expressions
            .get(frame.recursor, b)?
            .kind(expressions, levels, b)?
    else {
        return Err(ResourceError::Invariant.into());
    };
    let site = ConstantUse {
        name,
        arguments: &[],
        parameters: scope.parameters,
        before: scope.before,
        formation: scope.formation,
        mode: scope.mode,
        expression_end: scope.expression_end,
        level_end: scope.level_end,
    };
    if !left
        && let Some(answer) = literal_step(
            &site,
            scratch.applications[end - 1].argument,
            scratch.applications[end - 2].argument,
            path,
            environment,
            expressions,
            levels,
            names,
            b,
        )?
    {
        scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
        scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
        return Ok(answer);
    }
    // Ordinary delta is required on a completed nonnumeric operand. Continuing
    // at the body (not the certified head) prevents re-entering this attempt.
    match environment.delta_step_with_cache(site, path, expressions, levels, names, cache, b)? {
        DeltaStep::Unfolded { expression, path } => Ok(Head { expression, path }),
        _ => Err(ResourceError::Invariant.into()),
    }
}

#[allow(clippy::too_many_arguments)]
fn numeric(
    root: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<bool, HeadError> {
    match expressions.get(root, b)?.kind(expressions, levels, b)? {
        ExprKind::Natural(_) => Ok(true),
        ExprKind::Constant(name, []) => {
            let (_, zero, _) = environment
                .natural_constructors(
                    scope.before,
                    scope.formation,
                    scope.expression_end,
                    expressions,
                    b,
                )?
                .ok_or(ResourceError::Invariant)?;
            Ok(names.summary(name, b)?.canonical == names.summary(zero, b)?.canonical)
        }
        _ => Ok(false),
    }
}

/// Completed certified binary arithmetic/predicate rewrite only. The returned
/// digit owner's reservation is retired even if route checking or append fails.
#[allow(clippy::too_many_arguments)]
pub(super) fn literal_step(
    site: &ConstantUse<'_>,
    left: ExprId,
    right: ExprId,
    incoming: ReductionPath,
    environment: &Environment,
    expressions: &mut Expressions,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<Option<Head>, HeadError> {
    if let Some(answer) = environment.natural_predicate_result(
        site,
        expressions.get(left, b)?.kind(expressions, levels, b)?,
        expressions.get(right, b)?.kind(expressions, levels, b)?,
        levels,
        names,
        b,
    )? {
        let path = incoming.after_reduction()?;
        let expression = expressions.append(ExprKind::Constant(answer, &[]), levels, names, b)?;
        b.observe(Event::Reductions, 1);
        return Ok(Some(Head { expression, path }));
    }
    let Some(digits) = environment.natural_arithmetic_result(
        site,
        expressions.get(left, b)?.kind(expressions, levels, b)?,
        expressions.get(right, b)?.kind(expressions, levels, b)?,
        levels,
        names,
        b,
    )?
    else {
        return Ok(None);
    };
    publish_arithmetic(digits, incoming, expressions, levels, names, b).map(Some)
}

fn publish_arithmetic(
    digits: crate::check::natural::Digits,
    incoming: ReductionPath,
    expressions: &mut Expressions,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<Head, HeadError> {
    let result = (|| -> Result<Head, HeadError> {
        let path = incoming.after_reduction()?;
        let expression =
            expressions.append(ExprKind::Natural(digits.as_bytes()), levels, names, b)?;
        b.observe(Event::Reductions, 1);
        Ok(Head { expression, path })
    })();
    digits.retire(b)?;
    result
}
