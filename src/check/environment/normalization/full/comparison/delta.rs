//! Paired delta selection. A classification never computes a body.
use super::*;
use crate::check::environment::constant_use::{ConstantUse, DeltaStep};
use crate::syntax::levels::LevelNames;

fn site<'a>(
    name: crate::syntax::levels::NameId,
    arguments: &'a [crate::syntax::levels::LevelId],
    scope: &'a Scope<'_>,
) -> ConstantUse<'a> {
    ConstantUse {
        name,
        arguments,
        parameters: scope.parameters,
        before: scope.before,
        formation: scope.formation,
        mode: scope.mode,
        expression_end: scope.expression_end,
        level_end: scope.level_end,
    }
}

struct Candidate {
    priority: Option<(u8, u32)>,
    projection: u8,
    intrinsic: bool,
    native: bool,
    regular_head: Option<(crate::syntax::levels::NameId, ExprId, usize)>,
}

#[allow(clippy::too_many_arguments)]
fn inspect(
    mut root: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Candidate, HeadError> {
    let mut arity = 0usize;
    loop {
        budget.charge_work(1)?;
        match expressions
            .get(root, budget)?
            .kind(expressions, levels, budget)?
        {
            ExprKind::App(f, _) => {
                arity = arity.checked_add(1).ok_or(ResourceError::Counter)?;
                root = f;
            }
            ExprKind::Constant(name, arguments) => {
                let kind = spine::intrinsic_kind(name, names, budget)?;
                let mut intrinsic = kind == 1;
                if intrinsic
                    && arguments.is_empty()
                    && let Some((_, zero, succ)) = environment.natural_constructors(
                        scope.before,
                        scope.formation,
                        scope.expression_end,
                        expressions,
                        budget,
                    )?
                {
                    let identity = names.summary(name, budget)?.canonical;
                    // Only certified, exactly saturated representations are
                    // exempt from arithmetic applicability checks. Names alone
                    // never make an ordinary definition a Nat constructor.
                    intrinsic = !((arity == 0
                        && identity == names.summary(zero, budget)?.canonical)
                        || (arity == 1 && identity == names.summary(succ, budget)?.canonical));
                }
                let candidate = environment
                    .delta_candidate(site(name, arguments, scope), levels, names, budget)
                    .map_err(|error| match error {
                        crate::check::environment::constant_use::UseError::Unavailable => {
                            HeadError::Unsupported
                        }
                        other => other.into(),
                    })?;
                let priority = candidate.map(|candidate| candidate.priority);
                return Ok(Candidate {
                    priority,
                    projection: 0,
                    intrinsic,
                    native: kind == 2,
                    regular_head: candidate.and_then(|candidate| {
                        (arity != 0 && candidate.priority.0 == 1).then_some((
                            name,
                            candidate.body,
                            arity,
                        ))
                    }),
                });
            }
            ExprKind::Projection(..) => {
                return Ok(Candidate {
                    priority: None,
                    projection: if arity == 0 { 1 } else { 2 },
                    intrinsic: false,
                    native: false,
                    regular_head: None,
                });
            }
            _ => {
                return Ok(Candidate {
                    priority: None,
                    projection: 0,
                    intrinsic: false,
                    native: false,
                    regular_head: None,
                });
            }
        }
    }
}

/// Bits zero/one select left/right delta; bits two/three first demand Hfull
/// on the left/right projection. Unimplemented primitive guards decline before
/// either body changes unless ordinary positive-only fallback is available.
/// Bit four requests C8 for an applied projection head after delta is unavailable.
/// Bit five requests terminal positive-only ordinary normalization for a closed
/// intrinsic with a checked transparent body. No primitive or negative
/// exhaustion certificate follows from this fallback.
/// Bit six permits the same-regular-definition shortcut before paired delta.
/// Zero means only no ordinary delta; downstream primitive guards are still
/// required. It is never a certificate of completed C5 or negative exhaustion.
#[allow(clippy::too_many_arguments)]
pub(super) fn select(
    left: ExprId,
    right: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<u8, HeadError> {
    select_inner(
        left,
        right,
        scope,
        environment,
        expressions,
        levels,
        names,
        budget,
        false,
    )
}

/// C7 uses paired delta steps, not the outer Nat-offset/acceleration loop.
/// Native exclusion and checked constant-use validation remain mandatory.
#[allow(clippy::too_many_arguments)]
pub(super) fn select_sources(
    left: ExprId,
    right: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<u8, HeadError> {
    select_inner(
        left,
        right,
        scope,
        environment,
        expressions,
        levels,
        names,
        budget,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn select_inner(
    left: ExprId,
    right: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
    source_delta: bool,
) -> Result<u8, HeadError> {
    let a = inspect(left, scope, environment, expressions, levels, names, budget)?;
    let b = inspect(
        right,
        scope,
        environment,
        expressions,
        levels,
        names,
        budget,
    )?;
    if a.native || b.native {
        return Err(HeadError::Unsupported);
    }
    // The accepted paired Nat acceleration requires both current operands
    // to contain no locals. Ordinary delta on checked open definitions does
    // not need an arithmetic certificate. Native exclusions are unconditional.
    if !source_delta
        && (a.intrinsic || b.intrinsic)
        && !expressions.get(left, budget)?.has_free()
        && !expressions.get(right, budget)?.has_free()
    {
        // No operation certificate is granted here. The owner must not return
        // to a negative-producing phase after taking this ordinary fallback.
        return if (a.intrinsic && a.priority.is_some()) || (b.intrinsic && b.priority.is_some()) {
            Ok(32)
        } else {
            Err(HeadError::Unsupported)
        };
    }
    if a.priority.is_none() && b.priority.is_none() {
        return Ok(
            if !source_delta && (a.projection == 2 || b.projection == 2) {
                16
            } else {
                0
            },
        );
    }
    let (a_regular, b_regular) = (a.regular_head, b.regular_head);
    Ok(match (a.priority, b.priority) {
        (Some(_), None) if b.projection != 0 => 9,
        (None, Some(_)) if a.projection != 0 => 6,
        (Some(_), None) => 1,
        (None, Some(_)) => 2,
        (Some(a), Some(b)) => match a.cmp(&b) {
            std::cmp::Ordering::Greater => 1,
            std::cmp::Ordering::Less => 2,
            std::cmp::Ordering::Equal => {
                // The base selector evaluated eligible_prefix only after the
                // canonical-name comparison short-circuited different heads,
                // so a different-head pair charged no body walk and could not
                // trip eligible_prefix's resource errors. Preserve that
                // boundary exactly; pre-exposure same-definition argument congruence only ever applies to
                // same-name pairs, so no route behavior needs the body prefix
                // of a different-head pair.
                let (eligible_body, a_body, left_arity, right_arity) = match (a_regular, b_regular)
                {
                    (Some((a, a_body, left_arity)), Some((b, _, right_arity))) => {
                        if names.summary(a, budget)?.canonical
                            != names.summary(b, budget)?.canonical
                        {
                            return Ok(3);
                        }
                        let eligible_body = eligible_prefix(
                            a_body,
                            left_arity.max(right_arity),
                            expressions,
                            levels,
                            budget,
                        )?;
                        (eligible_body, a_body, left_arity, right_arity)
                    }
                    // The base's non-both-regular case computed no shortcut and
                    // no route: paired unfolding decides.
                    _ => return Ok(3),
                };
                // The existing same-definition shortcut keeps its scheduling
                // hints: an eligible lambda-prefix body, no bounded-recursor
                // conflict, and first arguments that do not already differ.
                // Reaching this point the canonical names are already equal.
                let existing_shortcut = eligible_body
                    && !prefer_unfolding(
                        left,
                        right,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        budget,
                    )?;
                // Pre-exposure same-definition argument congruence (agreed design subdecision): equal
                // applied arity with both spines finishing together admits the
                // pre-exposure same-definition argument congruence route on the
                // original operands. The SameDefinition dispatch bit six drives
                // finishes Equal only from completed-equal ordinary child
                // comparisons; a different or inconclusive child keeps the
                // paired-unfold fallback with the sticky unresolved-equality
                // discipline. On exposed forms this admission is the existing
                // shortcut; the recorded added admission is the lift-wrapper
                // shape: a body that is not a lambda stack at all (an
                // under-applied primitive constant). A body with even one
                // lambda binder keeps the base schedule — paired unfolding may
                // discard arguments such bodies never read, which the
                // congruence route must not be forced to compare. Universes
                // are compared completed-equal by the same preparation the
                // dispatch runs.
                let body_has_lambda_head = matches!(
                    expressions
                        .get(a_body, budget)?
                        .kind(expressions, levels, budget)?,
                    ExprKind::Lambda(..)
                );
                let route_a = !body_has_lambda_head && left_arity == right_arity;
                if (existing_shortcut
                    && !spine::closed_first_arguments_have_different_syntax(
                        left,
                        right,
                        expressions,
                        levels,
                        names,
                        budget,
                    )?)
                    || route_a
                {
                    67
                } else {
                    3
                }
            }
        },
        (None, None) => return Err(ResourceError::Invariant.into()),
    })
}

/// Rebuild only the chosen application spine, preserving each exact argument.
/// The comparison owner retains this charged scratch on failure and retires it;
/// success releases live frames, leaving reusable capacity owned by that owner.
#[allow(clippy::too_many_arguments)]
pub(super) fn unfold(
    mut root: ExprId,
    incoming: ReductionPath,
    pairs: &mut Vec<(ExprId, ExprId)>,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &mut Expressions,
    levels: &mut Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<ExprId, HeadError> {
    if !pairs.is_empty() {
        return Err(ResourceError::Invariant.into());
    }
    loop {
        budget.charge_work(1)?;
        match expressions
            .get(root, budget)?
            .kind(expressions, levels, budget)?
        {
            ExprKind::App(f, argument) => {
                let needed = pairs.len().checked_add(1).ok_or(ResourceError::Counter)?;
                budget.reserve_frames(1)?;
                if let Err(e) = budget.grow_vec(pairs, needed) {
                    budget.release_frames(1)?;
                    return Err(e.into());
                }
                pairs.push((argument, argument));
                root = f;
            }
            ExprKind::Constant(name, arguments) => {
                let mut instances = Vec::new();
                budget.grow_vec(&mut instances, arguments.len())?;
                instances.extend_from_slice(arguments);
                let result = environment
                    .delta_step(
                        site(name, &instances, scope),
                        incoming,
                        expressions,
                        levels,
                        names,
                        budget,
                    )
                    .map_err(HeadError::from);
                let cleanup = super::super::release(instances, budget).map_err(HeadError::from);
                if let Some(error) =
                    select_failure([result.as_ref().err().copied(), cleanup.err(), None, None])
                {
                    return Err(error);
                }
                let DeltaStep::Unfolded { expression, path } = result? else {
                    return Err(ResourceError::Invariant.into());
                };
                if path != incoming.after_reduction()? {
                    return Err(ResourceError::Invariant.into());
                }
                root = expression;
                break;
            }
            _ => return Err(ResourceError::Invariant.into()),
        }
    }
    while let Some((argument, _)) = pairs.pop() {
        budget.release_frames(1)?;
        root = expressions.append(ExprKind::App(root, argument), levels, names, budget)?;
    }
    Ok(root)
}

/// Scheduling only. Actual arguments of both checked applications retain their
/// own typing derivations even when the stored domains are dependent. Child C
/// observes each original type; it never borrows an unproved earlier equality.
/// Missing syntactic exposure prefers delta; unsupported children recover only
/// through the existing positive-only continuation.
fn eligible_prefix(
    mut body: ExprId,
    arity: usize,
    expressions: &Expressions,
    levels: &Levels,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    for index in 0..arity {
        budget.charge_work(1)?;
        let ExprKind::Lambda(_, _, residual, _) =
            expressions
                .get(body, budget)?
                .kind(expressions, levels, budget)?
        else {
            return Ok(false);
        };
        if index == 0 && expressions.get(residual, budget)?.loose_range() == 0 {
            return Ok(false);
        }
        body = residual;
    }
    Ok(true)
}

/// A bounded scheduling hint, never a comparison or reduction certificate.
#[allow(clippy::too_many_arguments)]
fn prefer_unfolding(
    mut left: ExprId,
    mut right: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    loop {
        budget.charge_work(1)?;
        let (ExprKind::App(f, x), ExprKind::App(g, y)) = (
            expressions
                .get(left, budget)?
                .kind(expressions, levels, budget)?,
            expressions
                .get(right, budget)?
                .kind(expressions, levels, budget)?,
        ) else {
            return Ok(false);
        };
        if x != y
            && expressions.get(x, budget)?.syntax_fingerprint()
                != expressions.get(y, budget)?.syntax_fingerprint()
            && let Some(a) =
                bounded_recursor_head(x, scope, environment, expressions, levels, names, budget)?
            && let Some(b) =
                bounded_recursor_head(y, scope, environment, expressions, levels, names, budget)?
            && a == b
        {
            return Ok(true);
        }
        (left, right) = (f, g);
    }
}

#[allow(clippy::too_many_arguments)]
fn bounded_recursor_head(
    mut root: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Option<u32>, HeadError> {
    for depth in 0..=8 {
        budget.charge_work(1)?;
        match expressions
            .get(root, budget)?
            .kind(expressions, levels, budget)?
        {
            ExprKind::App(f, _) if depth < 8 => root = f,
            ExprKind::Constant(name, _) => {
                // Metadata is only a scheduling hint. Actual head computation
                // still validates its own use, universes and permissions.
                return if environment
                    .recursor(name, scope.before.min(environment.len()), names, budget)?
                    .is_some()
                {
                    Ok(Some(names.summary(name, budget)?.canonical))
                } else {
                    Ok(None)
                };
            }
            _ => return Ok(None),
        }
    }
    Ok(None)
}
