//! C9 head classification: rigid or completed neutral recursors.
//! Classification alone grants no negative; the owner completes all alternatives.
use super::*;
use crate::check::environment::constant_use::{ConstantUse, UseError};
use crate::syntax::levels::{LevelNames, LevelPositive};
use crate::syntax::names::Component;

pub(super) enum Prepared {
    Equal,
    Arguments,
    PositiveArguments,
    ConstructorArguments,
    UnequalArguments,
    RigidArity,
    UnitLocals,
    EtaLeft,
    EtaRight,
    StructureLeft,
    StructureRight,
    StructureIneligible,
    LocalApplication,
    RecursorLocal,
    RecursorZero,
    RecursorProjection,
    LocalProjection,
    DistinctConstructors,
    RigidConstants,
    NoRule,
    Unavailable,
}

pub(super) fn intrinsic_candidate(
    name: crate::syntax::levels::NameId,
    names: &Names,
    b: &mut Budget,
) -> Result<bool, ResourceError> {
    Ok(intrinsic_kind(name, names, b)? != 0)
}

pub(super) fn intrinsic_kind(
    name: crate::syntax::levels::NameId,
    names: &Names,
    b: &mut Budget,
) -> Result<u8, ResourceError> {
    let Some((prefix, Component::String(part))) = names.view(name, b)? else {
        return Ok(0);
    };
    let Some((root, Component::String(namespace))) = names.view(prefix, b)? else {
        return Ok(0);
    };
    if root != crate::syntax::levels::NameId::ANONYMOUS {
        return Ok(0);
    }
    Ok(match namespace {
        "Nat" => u8::from(matches!(
            part,
            "zero"
                | "succ"
                | "add"
                | "mul"
                | "sub"
                | "div"
                | "mod"
                | "pow"
                | "gcd"
                | "beq"
                | "ble"
                | "land"
                | "lor"
                | "xor"
                | "shiftLeft"
                | "shiftRight"
        )),
        "Lean" => 2 * u8::from(matches!(part, "reduceNat" | "reduceBool")),
        _ => 0,
    })
}

/// `rigid`, except that an unsupported, unavailable or unsafe use is no certificate
/// rather than an abort: the pair keeps its other routes. Resource and invariant
/// failures still propagate.
#[allow(clippy::too_many_arguments)]
fn rigid_certificate(
    root: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    locals: &LocalContext,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    match rigid(
        root,
        scope,
        environment,
        expressions,
        levels,
        names,
        locals,
        budget,
    ) {
        Err(HeadError::Unsupported) => Ok(false),
        Err(HeadError::Use(UseError::Unavailable | UseError::UnsafeUse)) => Ok(false),
        other => other,
    }
}

#[allow(clippy::too_many_arguments)]
fn rigid(
    root: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    locals: &LocalContext,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    Ok(
        match expressions
            .get(root, budget)?
            .kind(expressions, levels, budget)?
        {
            ExprKind::Free(id) => locals.get(id, budget)?.value().is_none(),
            ExprKind::Constant(name, arguments) => {
                if intrinsic_candidate(name, names, budget)? {
                    return Err(HeadError::Unsupported);
                }
                environment
                    .rigid_constant_use(
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
                    )
                    .map_err(|error| match error {
                        UseError::Unavailable => HeadError::Unsupported,
                        other => other.into(),
                    })?
            }
            _ => false,
        },
    )
}

fn push(
    pairs: &mut Vec<(ExprId, ExprId)>,
    pair: (ExprId, ExprId),
    b: &mut Budget,
) -> Result<(), ResourceError> {
    let needed = pairs.len().checked_add(1).ok_or(ResourceError::Counter)?;
    b.reserve_frames(1)?;
    if let Err(error) = b.grow_vec(pairs, needed) {
        b.release_frames(1)?;
        return Err(error);
    }
    pairs.push(pair);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn prepare(
    mut left: ExprId,
    mut right: ExprId,
    pairs: &mut Vec<(ExprId, ExprId)>,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &mut Levels,
    names: &Names,
    locals: &LocalContext,
    ledger: &mut SessionCacheBudget,
    universes: &mut SharedMemo,
    budget: &mut Budget,
) -> Result<Prepared, HeadError> {
    if !pairs.is_empty() {
        return Err(ResourceError::Invariant.into());
    }
    if same_local_application(left, right, pairs, expressions, levels, locals, budget)? {
        return Ok(Prepared::Arguments);
    }
    if matches!(
        recursor_projection_heads(
            left,
            right,
            scope,
            environment,
            expressions,
            levels,
            names,
            budget
        )?,
        MixedHeads::Proven
    ) {
        return Ok(Prepared::RecursorProjection);
    }
    if recursor_zero(
        left,
        right,
        scope,
        environment,
        expressions,
        levels,
        names,
        locals,
        budget,
    )? {
        return Ok(Prepared::RecursorZero);
    }
    if distinct_saturated_constructors(
        left,
        right,
        scope,
        environment,
        expressions,
        levels,
        names,
        budget,
    )? {
        return Ok(Prepared::DistinctConstructors);
    }
    if distinct_stuck_recursors(
        left,
        right,
        scope,
        environment,
        expressions,
        levels,
        names,
        locals,
        budget,
    )? {
        return Ok(Prepared::NoRule);
    }
    match (
        expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?,
        expressions
            .get(right, budget)?
            .kind(expressions, levels, budget)?,
    ) {
        (ExprKind::Sort(_) | ExprKind::Pi(..), ExprKind::Constant(..) | ExprKind::Free(_))
        | (ExprKind::Constant(..) | ExprKind::Free(_), ExprKind::Sort(_) | ExprKind::Pi(..)) => {
            let other = if matches!(
                expressions
                    .get(left, budget)?
                    .kind(expressions, levels, budget)?,
                ExprKind::Sort(_) | ExprKind::Pi(..)
            ) {
                right
            } else {
                left
            };
            if let ExprKind::Constant(name, _) =
                expressions
                    .get(other, budget)?
                    .kind(expressions, levels, budget)?
                && intrinsic_candidate(name, names, budget)?
            {
                return Ok(Prepared::Unavailable);
            }
            return Ok(
                if rigid_certificate(
                    other,
                    scope,
                    environment,
                    expressions,
                    levels,
                    names,
                    locals,
                    budget,
                )? {
                    Prepared::NoRule
                } else {
                    Prepared::Unavailable
                },
            );
        }
        (ExprKind::Projection(family, field, source), ExprKind::Constant(..)) => {
            return stuck_projection_rigid(
                (family, field, source),
                right,
                scope,
                environment,
                expressions,
                levels,
                names,
                locals,
                budget,
            );
        }
        (ExprKind::Constant(..), ExprKind::Projection(family, field, source)) => {
            return stuck_projection_rigid(
                (family, field, source),
                left,
                scope,
                environment,
                expressions,
                levels,
                names,
                locals,
                budget,
            );
        }
        (ExprKind::Lambda(..), other) if !matches!(other, ExprKind::Lambda(..)) => {
            return Ok(Prepared::EtaLeft);
        }
        (other, ExprKind::Lambda(..)) if !matches!(other, ExprKind::Lambda(..)) => {
            return Ok(Prepared::EtaRight);
        }
        (ExprKind::Free(id), ExprKind::Natural(_)) | (ExprKind::Natural(_), ExprKind::Free(id))
            if locals.get(id, budget)?.value().is_none() =>
        {
            // Checked literals represent zero or successor only under the scoped
            // committed Nat certificate. Its two-constructor family excludes
            // structure eta; the owner must still complete original-type C12.
            // This is not neutrality inferred from a failed reduction route.
            return Ok(
                if environment
                    .natural_constructors(
                        scope.before,
                        scope.formation,
                        scope.expression_end,
                        expressions,
                        budget,
                    )?
                    .is_some()
                {
                    Prepared::StructureIneligible
                } else {
                    Prepared::Unavailable
                },
            );
        }
        (
            ExprKind::Free(id),
            ExprKind::App(..) | ExprKind::Constant(..) | ExprKind::Projection(..),
        ) if locals.get(id, budget)?.value().is_none() => {
            return local_pair_prepare(
                right,
                left,
                false,
                pairs,
                scope,
                environment,
                expressions,
                levels,
                names,
                locals,
                budget,
            );
        }
        (
            ExprKind::App(..) | ExprKind::Constant(..) | ExprKind::Projection(..),
            ExprKind::Free(id),
        ) if locals.get(id, budget)?.value().is_none() => {
            return local_pair_prepare(
                left,
                right,
                true,
                pairs,
                scope,
                environment,
                expressions,
                levels,
                names,
                locals,
                budget,
            );
        }
        _ => (),
    }
    let mut unequal = false;
    loop {
        budget.charge_work(1)?;
        let a = expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?;
        let b = expressions
            .get(right, budget)?
            .kind(expressions, levels, budget)?;
        match (a, b) {
            (ExprKind::App(f, x), ExprKind::App(g, y)) => {
                push(pairs, (x, y), budget)?;
                left = f;
                right = g;
            }
            (ExprKind::App(..), _) | (_, ExprKind::App(..)) => {
                unequal = true;
                break;
            }
            _ => break,
        }
    }
    let both_applications = !pairs.is_empty();
    if unequal {
        for root in [&mut left, &mut right] {
            while let ExprKind::App(function, _) =
                expressions
                    .get(*root, budget)?
                    .kind(expressions, levels, budget)?
            {
                budget.charge_work(1)?;
                *root = function;
            }
        }
        let count = pairs.len();
        pairs.clear();
        budget.release_frames(count)?;
        // This newly exposed unequal spine is outside this bounded C9 implementation when either head is
        // an intrinsic. Preserve the existing fallback so literal reduction
        // can run; an excluded head is not an unequal-arity premise.
        for root in [left, right] {
            if let ExprKind::Constant(name, _) =
                expressions
                    .get(root, budget)?
                    .kind(expressions, levels, budget)?
                && intrinsic_candidate(name, names, budget)?
            {
                return Ok(Prepared::Unavailable);
            }
        }
    }
    if !unequal
        && let ProjectionSources::Matched(a, b) = same_projection_sources(
            left,
            right,
            scope,
            environment,
            expressions,
            levels,
            names,
            budget,
        )?
    {
        if both_applications {
            // The head child owns C7 and its exposure. This parent merely
            // schedules positive-only C9, then the existing argument pairs.
            push(pairs, (left, right), budget)?;
            return Ok(Prepared::PositiveArguments);
        }
        if matches!(
            neutral_projection_source(
                a,
                scope,
                environment,
                expressions,
                levels,
                names,
                locals,
                budget
            )?,
            NeutralSource::Proven
        ) && matches!(
            neutral_projection_source(
                b,
                scope,
                environment,
                expressions,
                levels,
                names,
                locals,
                budget
            )?,
            NeutralSource::Proven
        ) && delta::select(a, b, scope, environment, expressions, levels, names, budget)
            .map_err(optional_head_error)?
            == 0
        {
            // Completed Hcheap exposed these actual projection occurrences and
            // attempted field selection. The restricted source shapes have no
            // remaining field reduction; delta has explicitly finished. Thus C7
            // now compares the current sources, not their normal forms.
            push(pairs, (a, b), budget)?;
            return Ok(Prepared::PositiveArguments);
        }
        return Ok(Prepared::Unavailable);
    }
    if both_applications
        && matches!(
            recursor_projection_heads(
                left,
                right,
                scope,
                environment,
                expressions,
                levels,
                names,
                budget
            )?,
            MixedHeads::Proven
        )
    {
        push(pairs, (left, right), budget)?;
        return Ok(if unequal {
            Prepared::UnequalArguments
        } else {
            Prepared::Arguments
        });
    }
    if pairs.is_empty()
        && !unequal
        && committed_heads_equal(
            left,
            right,
            scope,
            environment,
            expressions,
            levels,
            names,
            ledger,
            universes,
            budget,
        )?
    {
        return Ok(Prepared::Equal);
    }
    if !rigid(
        left,
        scope,
        environment,
        expressions,
        levels,
        names,
        locals,
        budget,
    )? || !rigid(
        right,
        scope,
        environment,
        expressions,
        levels,
        names,
        locals,
        budget,
    )? {
        if !unequal && both_applications {
            let prepared = same_committed_application(
                left,
                right,
                pairs.len(),
                scope,
                environment,
                expressions,
                levels,
                names,
                budget,
            )?;
            if matches!(
                prepared,
                Prepared::Arguments | Prepared::ConstructorArguments | Prepared::PositiveArguments
            ) {
                if matches!(prepared, Prepared::ConstructorArguments) {
                    schedule_fields(
                        left,
                        pairs,
                        None,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        budget,
                    )?;
                }
                push(pairs, (left, right), budget)?;
                return Ok(prepared);
            }
        }
        return Ok(Prepared::Unavailable);
    }
    if unequal {
        if both_applications {
            push(pairs, (left, right), budget)?;
            return Ok(Prepared::UnequalArguments);
        }
        return Ok(Prepared::RigidArity);
    }
    if !pairs.is_empty() {
        // Collected last argument first; popping the head then the remaining
        // pairs observes precisely head, first argument, ..., last argument.
        push(pairs, (left, right), budget)?;
        return Ok(Prepared::Arguments);
    }
    if matches!(
        expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?,
        ExprKind::Free(_)
    ) && matches!(
        expressions
            .get(right, budget)?
            .kind(expressions, levels, budget)?,
        ExprKind::Free(_)
    ) {
        // Both rigid checks above established active locals with no let value.
        // No intervening application, projection, literal or constructor-eta
        // route applies to this pair of bare local operands.
        return Ok(Prepared::UnitLocals);
    }
    if let (ExprKind::Constant(a, us), ExprKind::Constant(b, vs)) = (
        expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?,
        expressions
            .get(right, budget)?
            .kind(expressions, levels, budget)?,
    ) {
        // Both uses above completed rigid-kind, scope, safety and arity checks.
        // This is residual evidence only; the owner still discharges C12.
        if names.summary(a, budget)?.canonical != names.summary(b, budget)?.canonical {
            return Ok(Prepared::RigidConstants);
        }
        if us.len() != vs.len() {
            return Err(ResourceError::Invariant.into());
        }
        for (&u, &v) in us.iter().zip(vs) {
            if levels.with_helpers(names, budget, |h| h.compare_universes(u, v))?
                != UniverseComparison::Equal
            {
                return Ok(Prepared::RigidConstants);
            }
        }
        return Ok(Prepared::Equal);
    }
    Ok(Prepared::Unavailable)
}

/// Two validated bare uses of the same committed `Quot`, `Quot.mk` or recursor with
/// completed-equal universe instances are equal (, committed head equality):
/// same name and equivalent levels is the same term. This is the head child of the
/// positive quotient-type, rigid constructor, or recursor spine route (bare constants only).
/// Unequal instances, other heads, or any
/// unvalidated use answer false: no negative and no equality follow from a false here.
#[allow(clippy::too_many_arguments)]
fn committed_heads_equal(
    left: ExprId,
    right: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &mut Levels,
    names: &Names,
    ledger: &mut SessionCacheBudget,
    universes: &mut SharedMemo,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    let (ExprKind::Constant(a, us), ExprKind::Constant(b, vs)) = (
        expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?,
        expressions
            .get(right, budget)?
            .kind(expressions, levels, budget)?,
    ) else {
        return Ok(false);
    };
    if names.summary(a, budget)?.canonical != names.summary(b, budget)?.canonical {
        return Ok(false);
    }
    for (name, arguments) in [(a, us), (b, vs)] {
        match environment.opaque_head_use(
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
        ) {
            Ok(true) => {}
            // Not this rule. Resource, scope and internal failures stay terminal.
            Ok(false) | Err(UseError::Unavailable) => return Ok(false),
            Err(error) => return Err(error.into()),
        }
    }
    if us.len() != vs.len() {
        return Err(ResourceError::Invariant.into());
    }
    for (&u, &v) in us.iter().zip(vs) {
        if levels.with_helpers(names, budget, |h| {
            h.compare_universes_with(
                u,
                v,
                Some(SharedTable {
                    memo: &mut *universes,
                    ledger: &mut *ledger,
                }),
            )
        })? != UniverseComparison::Equal
        {
            return Ok(false);
        }
    }
    Ok(true)
}

/// The caller retains completed Hcheap/paired operands, including every demanded
/// major/K/structure judgment. Syntax alone does not establish that completion.
/// For the zero/local-major shape Hfull has no further applicable action.
/// extends the certified Nat side to a successor application, the major to a neutral
/// spine, and the stuck operand to a projection of a neutral source; the extended
/// shapes additionally require every recursor involved to be non-K with at least two
/// constructors, so neither structure eta nor K can expand its major.
#[allow(clippy::too_many_arguments)]
fn recursor_zero(
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
    let a = expressions
        .get(left, budget)?
        .kind(expressions, levels, budget)?;
    let b = expressions
        .get(right, budget)?
        .kind(expressions, levels, budget)?;
    // Cheap syntactic screens first: this runs for every comparison pair, so nothing below
    // (recursor lookup, Nat certificate, neutral walk) happens for other shapes.
    let unary_constant = |kind: ExprKind<'_>, budget: &mut Budget| -> Result<bool, HeadError> {
        Ok(match kind {
            ExprKind::App(f, _) => matches!(
                expressions
                    .get(f, budget)?
                    .kind(expressions, levels, budget)?,
                ExprKind::Constant(_, [])
            ),
            _ => false,
        })
    };
    let zero_like =
        |kind: ExprKind<'_>| matches!(kind, ExprKind::Natural(b"0") | ExprKind::Constant(_, []));
    let stuck_like =
        |kind: ExprKind<'_>| matches!(kind, ExprKind::App(..) | ExprKind::Projection(..));
    let zero_shape = (zero_like(a) && stuck_like(b)) || (stuck_like(a) && zero_like(b));
    let application_pair = stuck_like(a) && stuck_like(b);
    if !zero_shape
        && !(application_pair && (unary_constant(a, budget)? || unary_constant(b, budget)?))
    {
        return Ok(false);
    }
    // The stuck operand: a saturated committed recursor application or a projection. Its
    // shape is checked before the Nat-certificate lookup and the neutral walk so other
    // shapes stop here.
    let candidate = |e: ExprId, budget: &mut Budget| {
        stuck_candidate(e, scope, environment, expressions, levels, names, budget)
    };
    let (recursor_side, other_side) = if zero_shape {
        if stuck_like(a) {
            (left, right)
        } else {
            (right, left)
        }
    } else {
        match (candidate(left, budget)?, candidate(right, budget)?) {
            (Some(_), None) => (left, right),
            (None, Some(_)) => (right, left),
            _ => return Ok(false),
        }
    };
    let Some(stuck) = candidate(recursor_side, budget)? else {
        return Ok(false);
    };
    let Some((_, zero_name, succ_name)) = environment.natural_constructors(
        scope.before,
        scope.formation,
        scope.expression_end,
        expressions,
        budget,
    )?
    else {
        return Ok(false);
    };
    // The other side must be certified zero, or (in the application pair) a certified
    // successor application.
    let extended_side = if zero_shape {
        match expressions
            .get(other_side, budget)?
            .kind(expressions, levels, budget)?
        {
            ExprKind::Natural(b"0") => false,
            ExprKind::Constant(name, []) => {
                if names.summary(name, budget)?.canonical
                    != names.summary(zero_name, budget)?.canonical
                {
                    return Ok(false);
                }
                false
            }
            _ => return Ok(false),
        }
    } else {
        match expressions
            .get(other_side, budget)?
            .kind(expressions, levels, budget)?
        {
            ExprKind::App(f, _) => {
                match expressions
                    .get(f, budget)?
                    .kind(expressions, levels, budget)?
                {
                    ExprKind::Constant(name, [])
                        if names.summary(name, budget)?.canonical
                            == names.summary(succ_name, budget)?.canonical => {}
                    _ => return Ok(false),
                }
            }
            _ => return Ok(false),
        }
        true
    };
    let walked = match stuck {
        // A projection is always an extended shape; its source must be neutral.
        Stuck::Projection => recursor_side,
        Stuck::Recursor { k, constructors } => {
            let ExprKind::App(_, major) =
                expressions
                    .get(recursor_side, budget)?
                    .kind(expressions, levels, budget)?
            else {
                return Ok(false);
            };
            // The original shape needs a non-let local major; any other major is extended.
            let local_major = matches!(
                expressions.get(major, budget)?.kind(expressions, levels, budget)?,
                ExprKind::Free(local) if locals.get(local, budget)?.value().is_none()
            );
            if (extended_side || !local_major) && (k || constructors < 2) {
                // Structure eta could expand a neutral major of a structure-like family,
                // and K could apply: extended shapes need a non-K family with at least two
                // constructors.
                return Ok(false);
            }
            major
        }
    };
    neutral_major(
        walked,
        scope,
        environment,
        expressions,
        levels,
        names,
        locals,
        budget,
        0,
        false,
    )
}

/// The stuck operand of a recursor-versus-Nat comparison.
enum Stuck {
    /// A saturated committed recursor application: its K flag and constructor count.
    Recursor { k: bool, constructors: usize },
    /// A projection; the caller walks its source for neutrality.
    Projection,
}

/// Classify an operand as a saturated committed recursor application or a projection.
#[allow(clippy::too_many_arguments)]
fn stuck_candidate(
    e: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Option<Stuck>, HeadError> {
    if let ExprKind::Projection(..) =
        expressions
            .get(e, budget)?
            .kind(expressions, levels, budget)?
    {
        return Ok(Some(Stuck::Projection));
    }
    Ok(
        saturated_recursor(e, scope, environment, expressions, levels, names, budget)?
            .map(|(k, constructors)| Stuck::Recursor { k, constructors }),
    )
}

/// A saturated application of a committed recursor: its `k` flag and constructor count.
#[allow(clippy::too_many_arguments)]
fn saturated_recursor(
    e: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Option<(bool, usize)>, HeadError> {
    Ok(
        recursor_application(e, scope, environment, expressions, levels, names, budget)?
            .map(|application| (application.k, application.constructors)),
    )
}

struct RecursorApplication {
    name: crate::syntax::levels::NameId,
    k: bool,
    constructors: usize,
    major: ExprId,
}

/// A saturated application of a committed recursor, with its name and major.
#[allow(clippy::too_many_arguments)]
fn recursor_application(
    e: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Option<RecursorApplication>, HeadError> {
    let mut head = e;
    let mut arity = 0usize;
    let mut major = e;
    while let ExprKind::App(function, argument) =
        expressions
            .get(head, budget)?
            .kind(expressions, levels, budget)?
    {
        budget.charge_work(1)?;
        if arity == 0 {
            major = argument;
        }
        arity = arity.checked_add(1).ok_or(ResourceError::Counter)?;
        head = function;
    }
    let ExprKind::Constant(name, arguments) =
        expressions
            .get(head, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(None);
    };
    if intrinsic_candidate(name, names, budget)? {
        return Ok(None);
    }
    let step = environment.restricted_head_step(
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
    )?;
    if !matches!(
        step,
        crate::check::environment::constant_use::DeltaStep::Recursor
    ) {
        return Ok(None);
    }
    let Some(recursor) =
        environment.recursor(name, scope.before.min(environment.len()), names, budget)?
    else {
        return Ok(None);
    };
    let required = (recursor.common_prefix as usize)
        .checked_add(recursor.num_indices as usize)
        .and_then(|n| n.checked_add(1))
        .ok_or(ResourceError::Counter)?;
    Ok((arity == required).then_some(RecursorApplication {
        name,
        k: recursor.k,
        constructors: recursor.rules.len(),
        major,
    }))
}

/// Two saturated applications of different committed recursors, each non-K with at
/// least two constructors (so neither K nor structure eta can act) and each with a
/// neutral major. The operands come from completed head exposure, so no iota step
/// remains for either; the recursors have no delta and different names, so no
/// congruence, eta or unfolding equates them. Classification only: C4 has completed
/// and the owner still completes C12 on the original left type.
#[allow(clippy::too_many_arguments)]
fn distinct_stuck_recursors(
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
    let stuck_like = |kind: ExprKind<'_>| matches!(kind, ExprKind::App(..));
    if !stuck_like(
        expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?,
    ) || !stuck_like(
        expressions
            .get(right, budget)?
            .kind(expressions, levels, budget)?,
    ) {
        return Ok(false);
    }
    let Some(a) =
        recursor_application(left, scope, environment, expressions, levels, names, budget)?
    else {
        return Ok(false);
    };
    let Some(b) = recursor_application(
        right,
        scope,
        environment,
        expressions,
        levels,
        names,
        budget,
    )?
    else {
        return Ok(false);
    };
    if a.k
        || b.k
        || a.constructors < 2
        || b.constructors < 2
        || names.summary(a.name, budget)?.canonical == names.summary(b.name, budget)?.canonical
    {
        return Ok(false);
    }
    for major in [a.major, b.major] {
        if !neutral_major(
            major,
            scope,
            environment,
            expressions,
            levels,
            names,
            locals,
            budget,
            0,
            true,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// A projection of a neutral source paired with an ordinary rigid head. Both
/// operands come from completed head exposure and paired unfolding, so the source
/// is the actual exposed source: it has no constructor to select a field from
/// (neutral), and a rigid head has no delta. The layout must be a committed
/// nonrecursive, non-indexed structure with the field in range. This classifies
/// only; C4 has completed and the owner still completes C12 on the original left
/// type before any negative.
#[allow(clippy::too_many_arguments)]
fn stuck_projection_rigid(
    projection: (crate::syntax::levels::NameId, u32, ExprId),
    other: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    locals: &LocalContext,
    budget: &mut Budget,
) -> Result<Prepared, HeadError> {
    let (family, field, source) = projection;
    if let ExprKind::Constant(name, _) =
        expressions
            .get(other, budget)?
            .kind(expressions, levels, budget)?
        && intrinsic_candidate(name, names, budget)?
    {
        return Ok(Prepared::Unavailable);
    }
    if !matches!(
        projection_layout(family, field, scope, environment, names, budget)?,
        MixedHeads::Proven
    ) || !rigid_certificate(
        other,
        scope,
        environment,
        expressions,
        levels,
        names,
        locals,
        budget,
    )? || !neutral_major(
        source,
        scope,
        environment,
        expressions,
        levels,
        names,
        locals,
        budget,
        0,
        true,
    )? {
        return Ok(Prepared::Unavailable);
    }
    Ok(Prepared::NoRule)
}

/// Neutral-spine judgment: a non-let local, an application of a neutral term, a
/// projection of a neutral term, or a saturated non-K recursor of a family with at least
/// two constructors whose major is neutral.
#[allow(clippy::too_many_arguments)]
fn neutral_major(
    e: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    locals: &LocalContext,
    budget: &mut Budget,
    depth: u32,
    stuck_values: bool,
) -> Result<bool, HeadError> {
    if depth > 32 {
        return Ok(false);
    }
    budget.charge_work(1)?;
    match expressions
        .get(e, budget)?
        .kind(expressions, levels, budget)?
    {
        ExprKind::Free(local) => Ok(locals.get(local, budget)?.value().is_none()),
        ExprKind::Projection(_, _, source) => neutral_major(
            source,
            scope,
            environment,
            expressions,
            levels,
            names,
            locals,
            budget,
            depth + 1,
            stuck_values,
        ),
        ExprKind::App(f, _) => {
            // Application of a neutral function, or a saturated Nat recursor whose
            // major is neutral (the head is a committed recursor constant).
            let mut head = e;
            let mut arity = 0usize;
            while let ExprKind::App(function, _) =
                expressions
                    .get(head, budget)?
                    .kind(expressions, levels, budget)?
            {
                budget.charge_work(1)?;
                arity += 1;
                head = function;
            }
            match expressions
                .get(head, budget)?
                .kind(expressions, levels, budget)?
            {
                ExprKind::Constant(name, arguments) => {
                    if intrinsic_candidate(name, names, budget)? {
                        return Ok(false);
                    }
                    if stuck_values
                        && stuck_value(name, arguments, scope, environment, levels, names, budget)?
                    {
                        return Ok(true);
                    }
                    let step = environment.restricted_head_step(
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
                    )?;
                    if !matches!(
                        step,
                        crate::check::environment::constant_use::DeltaStep::Recursor
                    ) {
                        return Ok(false);
                    }
                    let Some(recursor) = environment.recursor(
                        name,
                        scope.before.min(environment.len()),
                        names,
                        budget,
                    )?
                    else {
                        return Ok(false);
                    };
                    let required = (recursor.common_prefix as usize)
                        .checked_add(recursor.num_indices as usize)
                        .and_then(|n| n.checked_add(1))
                        .ok_or(ResourceError::Counter)?;
                    if recursor.k || arity != required {
                        return Ok(false);
                    }
                    // At least two constructors: not structure-like, so no eta expands its
                    // major; K was excluded above.
                    if recursor.rules.len() < 2 {
                        return Ok(false);
                    }
                    let major =
                        match expressions
                            .get(e, budget)?
                            .kind(expressions, levels, budget)?
                        {
                            ExprKind::App(_, major) => major,
                            _ => return Ok(false),
                        };
                    neutral_major(
                        major,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        locals,
                        budget,
                        depth + 1,
                        stuck_values,
                    )
                }
                _ => neutral_major(
                    f,
                    scope,
                    environment,
                    expressions,
                    levels,
                    names,
                    locals,
                    budget,
                    depth + 1,
                    stuck_values,
                ),
            }
        }
        ExprKind::Constant(name, arguments) => {
            if intrinsic_candidate(name, names, budget)? {
                return Ok(false);
            }
            if !stuck_values {
                return Ok(false);
            }
            stuck_value(name, arguments, scope, environment, levels, names, budget)
        }
        _ => Ok(false),
    }
}

/// A validated axiom or opaque constant use: it has no delta body, so it and every
/// application of it stay stuck values under any exposure. Callers exclude
/// intrinsic names first. A missing or unavailable use is not neutrality.
fn stuck_value(
    name: crate::syntax::levels::NameId,
    arguments: &[crate::syntax::levels::LevelId],
    scope: &Scope<'_>,
    environment: &Environment,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    environment
        .stuck_value_use(
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
        )
        .map_err(mixed_use_error)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn unit_eligible(
    mut ty: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    let mut parameters = 0u32;
    loop {
        budget.charge_work(1)?;
        match expressions
            .get(ty, budget)?
            .kind(expressions, levels, budget)?
        {
            ExprKind::App(function, _) => {
                parameters = parameters.checked_add(1).ok_or(ResourceError::Counter)?;
                ty = function;
            }
            ExprKind::Constant(name, arguments) => {
                let valid = environment
                    .inductive_type_use(
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
                    )
                    .map_err(|error| match error {
                        UseError::Unavailable => HeadError::Unsupported,
                        other => other.into(),
                    })?;
                if !valid {
                    return Ok(false);
                }
                let family = environment
                    .inductive(name, scope.before.min(environment.len()), names, budget)?
                    .ok_or(HeadError::Unsupported)?;
                // Field counts come from the checked constructor telescopes.
                // With no fields, there cannot be a recursive field. Indices
                // still forbid unit eta, independently of the field count.
                return Ok(family.nonrecursive
                    && family.num_indices == 0
                    && family.num_params == parameters
                    && matches!(family.constructors, [constructor] if constructor.num_fields == 0));
            }
            _ => return Ok(false),
        }
    }
}

/// Only committed, single-constructor, nonrecursive, non-indexed families grant
/// structure eta. The original checked operand supplies its application typing.
#[allow(clippy::too_many_arguments)]
pub(super) fn local_pair_prepare(
    mut constructor: ExprId,
    neutral: ExprId,
    constructor_left: bool,
    pairs: &mut Vec<(ExprId, ExprId)>,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    locals: &LocalContext,
    budget: &mut Budget,
) -> Result<Prepared, HeadError> {
    loop {
        budget.charge_work(1)?;
        match expressions
            .get(constructor, budget)?
            .kind(expressions, levels, budget)?
        {
            ExprKind::App(f, x) => {
                push(pairs, (x, neutral), budget)?;
                constructor = f;
            }
            ExprKind::Projection(family, field, _) => {
                return Ok(
                    match projection_layout(family, field, scope, environment, names, budget)? {
                        MixedHeads::Proven => Prepared::LocalProjection,
                        MixedHeads::Unavailable => Prepared::Unavailable,
                    },
                );
            }
            ExprKind::Free(id)
                if !pairs.is_empty() && locals.get(id, budget)?.value().is_none() =>
            {
                // The other operand was established a bare non-let local by
                // prepare. This certificate never covers two applications.
                return Ok(Prepared::LocalApplication);
            }
            ExprKind::Constant(name, arguments) => {
                // Completed head/paired work discharges certified Nat constructor
                // computation, but no other intrinsic candidate or impostor gains
                // a residual classification from its constructor role alone.
                if intrinsic_candidate(name, names, budget)? {
                    let Some((_, zero, successor)) = environment.natural_constructors(
                        scope.before,
                        scope.formation,
                        scope.expression_end,
                        expressions,
                        budget,
                    )?
                    else {
                        return Err(HeadError::Unsupported);
                    };
                    let canonical = names.summary(name, budget)?.canonical;
                    if !arguments.is_empty()
                        || !((pairs.is_empty()
                            && canonical == names.summary(zero, budget)?.canonical)
                            || (pairs.len() == 1
                                && canonical == names.summary(successor, budget)?.canonical))
                    {
                        return Err(HeadError::Unsupported);
                    }
                }
                environment
                    .restricted_head_step(
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
                    )
                    .map_err(|e| match e {
                        UseError::Unavailable => HeadError::Unsupported,
                        other => other.into(),
                    })?;
                let Some(ctor) = environment.constructor(
                    name,
                    scope.before.min(environment.len()),
                    names,
                    budget,
                )?
                else {
                    if environment
                        .recursor(name, scope.before.min(environment.len()), names, budget)?
                        .is_none()
                    {
                        return Ok(Prepared::Unavailable);
                    }
                    // Construction premise: Phase::Rigid receives the exact
                    // completed exposed operands after paired unfolding. For a
                    // saturated recursor this includes major/K/structure guards.
                    // Private signatures and incomplete exposure cannot reach here.
                    // C4 and the later C12 guard still own type-directed equality.
                    return Ok(Prepared::RecursorLocal);
                };
                let family = environment
                    .inductive(
                        ctor.family,
                        scope.before.min(environment.len()),
                        names,
                        budget,
                    )?
                    .ok_or(HeadError::Unsupported)?;
                let [rule] = family.constructors else {
                    return Ok(Prepared::StructureIneligible);
                };
                if ctor.index != 0 {
                    return Err(ResourceError::Invariant.into());
                }
                if !family.nonrecursive
                    || family.num_indices != 0
                    || pairs.len() as u64
                        != u64::from(family.num_params) + u64::from(rule.num_fields)
                {
                    return Ok(Prepared::StructureIneligible);
                }
                // Reverse application order puts parameters at the end. Only
                // fields survive; their original order is restored by popping.
                for _ in 0..family.num_params {
                    pairs.pop().ok_or(ResourceError::Invariant)?;
                    budget.release_frames(1)?;
                }
                return Ok(if constructor_left {
                    Prepared::StructureLeft
                } else {
                    Prepared::StructureRight
                });
            }
            _ => return Ok(Prepared::Unavailable),
        }
    }
}

/// Check the observed local type really exposes the constructor's family before
/// constructing projections. This is in addition to the completed type comparison.
#[allow(clippy::too_many_arguments)]
pub(super) fn structure_family(
    mut constructor: ExprId,
    mut neutral_type: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Option<crate::syntax::levels::NameId>, HeadError> {
    loop {
        budget.charge_work(1)?;
        match expressions
            .get(constructor, budget)?
            .kind(expressions, levels, budget)?
        {
            ExprKind::App(f, _) => constructor = f,
            ExprKind::Constant(name, _) => {
                let ctor = environment
                    .constructor(name, scope.before.min(environment.len()), names, budget)?
                    .ok_or(HeadError::Unsupported)?;
                let family = environment
                    .inductive(
                        ctor.family,
                        scope.before.min(environment.len()),
                        names,
                        budget,
                    )?
                    .ok_or(HeadError::Unsupported)?;
                let mut count = 0u32;
                loop {
                    budget.charge_work(1)?;
                    match expressions.get(neutral_type, budget)?.kind(
                        expressions,
                        levels,
                        budget,
                    )? {
                        ExprKind::App(f, _) => {
                            count = count.checked_add(1).ok_or(ResourceError::Counter)?;
                            neutral_type = f;
                        }
                        ExprKind::Constant(name, _) => {
                            return Ok((count == family.num_params
                                && names.summary(name, budget)?.canonical
                                    == names.summary(ctor.family, budget)?.canonical)
                                .then_some(ctor.family));
                        }
                        _ => return Ok(None),
                    }
                }
            }
            _ => return Err(ResourceError::Invariant.into()),
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn distinct_saturated_constructors(
    left: ExprId,
    right: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<bool, HeadError> {
    let mut a = expressions.get(left, b)?.kind(expressions, levels, b)?;
    if !matches!(
        a,
        ExprKind::Constant(..) | ExprKind::App(..) | ExprKind::Natural(b"0")
    ) {
        return Ok(false);
    }
    let mut z = expressions.get(right, b)?.kind(expressions, levels, b)?;
    // An application spine is compared to its saturated arity below.
    let applied = matches!(a, ExprKind::App(..)) || matches!(z, ExprKind::App(..));
    let mut arities = [0usize; 2];
    if !matches!((a, z), (ExprKind::Constant(..), ExprKind::Constant(..))) {
        if matches!(
            natural::distinct_constructors(
                a,
                z,
                scope,
                environment,
                expressions,
                levels,
                names,
                b
            )?,
            natural::Distinct::Proven
        ) {
            return Ok(true);
        }
        for (kind, arity) in [&mut a, &mut z].into_iter().zip(arities.iter_mut()) {
            while let ExprKind::App(function, _) = *kind {
                b.charge_work(1)?;
                *arity = arity.checked_add(1).ok_or(ResourceError::Counter)?;
                *kind = expressions.get(function, b)?.kind(expressions, levels, b)?;
            }
        }
    }
    let (ExprKind::Constant(a, aa), ExprKind::Constant(z, za)) = (a, z) else {
        return Ok(false);
    };
    let before = scope.before.min(environment.len());
    let (Some(a_ctor), Some(z_ctor)) = (
        environment.constructor(a, before, names, b)?,
        environment.constructor(z, before, names, b)?,
    ) else {
        return Ok(false);
    };
    if a_ctor.index == z_ctor.index
        || names.summary(a_ctor.family, b)?.canonical != names.summary(z_ctor.family, b)?.canonical
    {
        return Ok(false);
    }
    if intrinsic_candidate(a, names, b)? || intrinsic_candidate(z, names, b)? {
        return Err(HeadError::Unsupported);
    }
    for (name, arguments) in [(a, aa), (z, za)] {
        environment.restricted_head_step(
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
            b,
        )?;
    }
    let family = environment
        .inductive(a_ctor.family, before, names, b)?
        .ok_or(HeadError::Unsupported)?;
    let a_rule = family
        .constructors
        .get(a_ctor.index as usize)
        .ok_or(ResourceError::Invariant)?;
    let z_rule = family
        .constructors
        .get(z_ctor.index as usize)
        .ok_or(ResourceError::Invariant)?;
    if applied && family.num_indices != 0 {
        return Ok(false);
    }
    let params = family.num_params as usize;
    Ok(params
        .checked_add(a_rule.num_fields as usize)
        .ok_or(ResourceError::Counter)?
        == arities[0]
        && params
            .checked_add(z_rule.num_fields as usize)
            .ok_or(ResourceError::Counter)?
            == arities[1])
}

/// Only completed Hcheap/paired operands qualify. The exact same committed
/// recursor is neutral here, not globally rigid. A committed constructor grants
/// positive congruence at this classification; a different argument only fails
/// this optional route. A negative for the pair comes later, from the
/// constructor-argument route after its eta attempts and C12.
/// Exact saturated committed `Quot.lift`/`Quot.ind` likewise grant only positive
/// congruence after both constant uses and earlier major exposure complete.
/// Exact two-argument `Quot` type applications grant only positive congruence.
/// Exact three-argument `Quot.mk` applications are rigid C9 heads: a
/// different argument fails the congruence route and C4/C12 precede any C13.
#[allow(clippy::too_many_arguments)]
pub(super) fn same_committed_application(
    left: ExprId,
    right: ExprId,
    arguments: usize,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Prepared, HeadError> {
    let (ExprKind::Constant(a, _), ExprKind::Constant(b, _)) = (
        expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?,
        expressions
            .get(right, budget)?
            .kind(expressions, levels, budget)?,
    ) else {
        return Ok(Prepared::Unavailable);
    };
    if names.summary(a, budget)?.canonical != names.summary(b, budget)?.canonical {
        return Ok(Prepared::Unavailable);
    }
    let before = scope.before.min(environment.len());
    if let Some(recursor) = environment.recursor(a, before, names, budget)? {
        let arity = (recursor.common_prefix as usize)
            .checked_add(recursor.num_indices as usize)
            .and_then(|n| n.checked_add(1)) // the major follows the complete block prefix and indices
            .ok_or(ResourceError::Counter)?;
        return Ok(if arguments == arity {
            Prepared::Arguments
        } else {
            // Partial and extra applications admit positive congruence only.
            // The head child still checks universe instances, and failed
            // arguments grant no recursor neutrality or negative certificate.
            Prepared::PositiveArguments
        });
    }
    let Some(constructor) = environment.constructor(a, before, names, budget)? else {
        // C5/C8 already completed on the checked whole operands. Quotient roles
        // come only from a committed entry; a staged signature or same spelling
        // grants no equations. Lift/Ind congruence is positive-only, never injectivity.
        if let Some(entry) = environment.lookup(a, before, names, budget)?
            && let crate::check::environment::StoredKind::Quotient(role) = entry.kind
        {
            use crate::decode::primitive_decode::quotients::Role;
            let arity = match role {
                Role::Lift => 6,
                Role::Induction => 5,
                Role::Constructor => 3,
                Role::Type => 2,
            };
            if arguments != arity {
                return Ok(Prepared::Unavailable);
            }
            if matches!(role, Role::Constructor | Role::Type) {
                // Both roles require validated committed uses. Quot Type
                // grants only positive congruence. For Constructor, Quot.mk has
                // no delta and no rule of its own, so validated same-head uses are
                // rigid C9 heads. A different argument only fails this congruence
                // route; C4 and C12 still run before C13 (never injectivity).
                for head in [left, right] {
                    let ExprKind::Constant(name, arguments) =
                        expressions
                            .get(head, budget)?
                            .kind(expressions, levels, budget)?
                    else {
                        return Err(ResourceError::Invariant.into());
                    };
                    let found = environment
                        .quotient_role_use(
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
                        )
                        .map_err(|error| match error {
                            UseError::Unavailable => HeadError::Unsupported,
                            other => other.into(),
                        })?;
                    if found != Some(role) {
                        return Err(HeadError::Unsupported);
                    }
                }
                // Type applications grant positive congruence only. A different
                // carrier/relation restores the mandatory route; it supplies no
                // quotient injectivity or residual negative certificate.
                return Ok(if role == Role::Type {
                    Prepared::PositiveArguments
                } else {
                    Prepared::Arguments
                });
            }
            for head in [left, right] {
                let ExprKind::Constant(name, arguments) =
                    expressions
                        .get(head, budget)?
                        .kind(expressions, levels, budget)?
                else {
                    return Err(ResourceError::Invariant.into());
                };
                if !matches!(environment.restricted_head_step(ConstantUse {
                    name, arguments, parameters: scope.parameters, before: scope.before,
                    formation: scope.formation, mode: scope.mode,
                    expression_end: scope.expression_end, level_end: scope.level_end,
                }, levels, names, budget)?,
                    crate::check::environment::constant_use::DeltaStep::Quotient(found) if found == role)
                {
                    return Err(HeadError::Unsupported);
                }
            }
            return Ok(Prepared::PositiveArguments);
        }
        return Ok(Prepared::Unavailable);
    };
    let family = environment
        .inductive(constructor.family, before, names, budget)?
        .ok_or(ResourceError::Invariant)?;
    let rule = family
        .constructors
        .get(constructor.index as usize)
        .ok_or(ResourceError::Invariant)?;
    let arity = (family.num_params as usize)
        .checked_add(rule.num_fields as usize)
        .ok_or(ResourceError::Counter)?;
    Ok(if arguments == arity {
        Prepared::ConstructorArguments
    } else {
        Prepared::Unavailable
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum MixedHeads {
    Proven,
    Unavailable,
}

/// One-sided role certificate, never a result of conversion. Each owner must
/// complete C4/C8 on checked inputs itself; peeling a parent's spine cannot
/// transfer neutrality to the child comparing these heads. C12 remains required.
#[allow(clippy::too_many_arguments)]
pub(super) fn recursor_projection_heads(
    left: ExprId,
    right: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<MixedHeads, HeadError> {
    let a = expressions
        .get(left, budget)?
        .kind(expressions, levels, budget)?;
    if !matches!(a, ExprKind::Constant(..) | ExprKind::Projection(..)) {
        return Ok(MixedHeads::Unavailable);
    }
    let b = expressions
        .get(right, budget)?
        .kind(expressions, levels, budget)?;
    let (name, arguments, family, field) = match (a, b) {
        (ExprKind::Constant(n, u), ExprKind::Projection(f, i, _))
        | (ExprKind::Projection(f, i, _), ExprKind::Constant(n, u)) => (n, u, f, i),
        _ => return Ok(MixedHeads::Unavailable),
    };
    if intrinsic_candidate(name, names, budget)? {
        return Ok(MixedHeads::Unavailable);
    }
    let before = scope.before.min(environment.len());
    if environment.recursor(name, before, names, budget)?.is_none() {
        return Ok(MixedHeads::Unavailable);
    }
    let step = environment
        .restricted_head_step(
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
        )
        .map_err(mixed_use_error)?;
    if !matches!(
        step,
        crate::check::environment::constant_use::DeltaStep::Recursor
    ) {
        return Ok(MixedHeads::Unavailable);
    }
    projection_layout(family, field, scope, environment, names, budget)
}

/// Layout only, not a neutrality or conversion certificate. The checked owner
/// has already completed full exposure of the actual source and field.
fn projection_layout(
    family: crate::syntax::levels::NameId,
    field: u32,
    scope: &Scope<'_>,
    environment: &Environment,
    names: &Names,
    budget: &mut Budget,
) -> Result<MixedHeads, HeadError> {
    let before = scope.before.min(environment.len());
    let Some(metadata) = environment.inductive(family, before, names, budget)? else {
        return Ok(MixedHeads::Unavailable);
    };
    let [rule] = metadata.constructors else {
        return Ok(MixedHeads::Unavailable);
    };
    Ok(
        if metadata.nonrecursive && metadata.num_indices == 0 && field < rule.num_fields {
            MixedHeads::Proven
        } else {
            MixedHeads::Unavailable
        },
    )
}

// An unavailable optional role observation is not declaration-level negative
// evidence. Whole-run exhaustion and internal failures keep their own class.
pub(super) fn mixed_use_error(error: UseError) -> HeadError {
    match error {
        UseError::Unavailable | UseError::UnsafeUse => HeadError::Unsupported,
        other => other.into(),
    }
}

pub(super) enum ProjectionSources {
    NotPair,
    Unmatched,
    Matched(ExprId, ExprId),
}

fn shared_argument_constant_head(
    mut left: ExprId,
    mut right: ExprId,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    let mut applied = false;
    for _ in 0..8 {
        budget.charge_work(1)?;
        match (
            expressions
                .get(left, budget)?
                .kind(expressions, levels, budget)?,
            expressions
                .get(right, budget)?
                .kind(expressions, levels, budget)?,
        ) {
            (ExprKind::App(f, _), ExprKind::App(g, _)) => {
                applied = true;
                (left, right) = (f, g);
            }
            (ExprKind::Constant(a, _), ExprKind::Constant(b, _)) => {
                return Ok(applied
                    && names.summary(a, budget)?.canonical == names.summary(b, budget)?.canonical);
            }
            _ => return Ok(false),
        }
    }
    Ok(false)
}

/// Route-order hint only. A different fingerprint does not prove that the
/// checked arguments differ: the caller must still run a complete existing
/// conversion route and retain its ordinary positive-only fallback.
#[allow(clippy::too_many_arguments)]
pub(super) fn closed_first_arguments_have_different_syntax(
    mut left: ExprId,
    mut right: ExprId,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    let mut first = None;
    for _ in 0..8 {
        budget.charge_work(1)?;
        match (
            expressions
                .get(left, budget)?
                .kind(expressions, levels, budget)?,
            expressions
                .get(right, budget)?
                .kind(expressions, levels, budget)?,
        ) {
            (ExprKind::App(f, x), ExprKind::App(g, y)) => {
                first = Some((x, y));
                (left, right) = (f, g);
            }
            (ExprKind::Constant(a, _), ExprKind::Constant(b, _)) => {
                let Some((x, y)) = first else {
                    return Ok(false);
                };
                return Ok(names.summary(a, budget)?.canonical
                    == names.summary(b, budget)?.canonical
                    && x != y
                    && !expressions.get(x, budget)?.has_free()
                    && !expressions.get(y, budget)?.has_free()
                    && expressions.get(x, budget)?.loose_range() == 0
                    && expressions.get(y, budget)?.loose_range() == 0
                    && expressions.get(x, budget)?.syntax_fingerprint()
                        != expressions.get(y, budget)?.syntax_fingerprint()
                    && shared_argument_constant_head(x, y, expressions, levels, names, budget)?);
            }
            _ => return Ok(false),
        }
    }
    Ok(false)
}

/// Checked occurrences only: same written identity/index and committed layout.
/// This is no certificate of source equality, neutrality or projection typing.
#[allow(clippy::too_many_arguments)]
pub(super) fn same_projection_sources(
    left: ExprId,
    right: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<ProjectionSources, HeadError> {
    let ExprKind::Projection(a, i, x) =
        expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(ProjectionSources::NotPair);
    };
    let ExprKind::Projection(b, j, y) =
        expressions
            .get(right, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(ProjectionSources::NotPair);
    };
    if i != j || names.summary(a, budget)?.canonical != names.summary(b, budget)?.canonical {
        return Ok(ProjectionSources::Unmatched);
    }
    Ok(
        if matches!(
            projection_layout(a, i, scope, environment, names, budget)?,
            MixedHeads::Proven
        ) {
            ProjectionSources::Matched(x, y)
        } else {
            ProjectionSources::Unmatched
        },
    )
}

/// One-sided applicability only, scoped to the owner's completed checked head
/// exposure. A saturated recursor includes completed major/K/structure guards;
/// metadata or raw syntax alone never authorizes skipping those computations.
#[allow(clippy::too_many_arguments)]
fn neutral_projection_source(
    root: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    locals: &LocalContext,
    budget: &mut Budget,
) -> Result<NeutralSource, HeadError> {
    let mut head = root;
    let mut arity = 0usize;
    match expressions
        .get(root, budget)?
        .kind(expressions, levels, budget)?
    {
        ExprKind::Free(id) => {
            return Ok(if locals.get(id, budget)?.value().is_none() {
                NeutralSource::Proven
            } else {
                NeutralSource::Unavailable
            });
        }
        ExprKind::App(_, major) => {
            let ExprKind::Free(id) =
                expressions
                    .get(major, budget)?
                    .kind(expressions, levels, budget)?
            else {
                return Ok(NeutralSource::Unavailable);
            };
            if locals.get(id, budget)?.value().is_some() {
                return Ok(NeutralSource::Unavailable);
            }
        }
        _ => return Ok(NeutralSource::Unavailable),
    }
    loop {
        budget.charge_work(1)?;
        match expressions
            .get(head, budget)?
            .kind(expressions, levels, budget)?
        {
            ExprKind::App(f, _) => {
                arity = arity.checked_add(1).ok_or(ResourceError::Counter)?;
                head = f;
            }
            ExprKind::Constant(name, _) => {
                let Some(recursor) = environment.recursor(
                    name,
                    scope.before.min(environment.len()),
                    names,
                    budget,
                )?
                else {
                    return Ok(NeutralSource::Unavailable);
                };
                let expected = (recursor.common_prefix as usize)
                    .checked_add(recursor.num_indices as usize)
                    .and_then(|n| n.checked_add(1))
                    .ok_or(ResourceError::Counter)?;
                return Ok(if arity == expected {
                    NeutralSource::Proven
                } else {
                    NeutralSource::Unavailable
                });
            }
            _ => return Ok(NeutralSource::Unavailable),
        }
    }
}

enum NeutralSource {
    Proven,
    Unavailable,
}

pub(super) fn optional_head_error(error: HeadError) -> HeadError {
    match error {
        HeadError::Use(error) => mixed_use_error(error),
        other => other,
    }
}

/// At C9 both cheap heads and earlier comparison phases have completed. This
/// exact shape excludes every nonlocal head classifier, without skipping either
/// ordered child comparison. A local definition must retain ordinary exposure.
fn same_local_application(
    left: ExprId,
    right: ExprId,
    pairs: &mut Vec<(ExprId, ExprId)>,
    expressions: &Expressions,
    levels: &Levels,
    locals: &LocalContext,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    budget.charge_work(1)?;
    let ExprKind::App(function, argument) =
        expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(false);
    };
    let ExprKind::App(other_function, other_argument) =
        expressions
            .get(right, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(false);
    };
    if function != other_function {
        return Ok(false);
    }
    let ExprKind::Free(id) =
        expressions
            .get(function, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(false);
    };
    if locals.get(id, budget)?.value().is_some() {
        return Ok(false);
    }
    push(pairs, (argument, other_argument), budget)?;
    push(pairs, (function, other_function), budget)?;
    Ok(true)
}

/// Classification only: a positive attempt is available, never an equality or
/// negative premise. Scope remains the same checked comparison throughout.
#[allow(clippy::too_many_arguments)]
pub(super) fn general_structure(
    left: ExprId,
    right: ExprId,
    pairs: &mut Vec<(ExprId, ExprId)>,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    locals: &LocalContext,
    budget: &mut Budget,
) -> Result<bool, HeadError> {
    for (constructor, other, constructor_left) in [(right, left, false), (left, right, true)] {
        let count = pairs.len();
        pairs.clear();
        budget.release_frames(count)?;
        match local_pair_prepare(
            constructor,
            other,
            constructor_left,
            pairs,
            scope,
            environment,
            expressions,
            levels,
            names,
            locals,
            budget,
        )? {
            Prepared::StructureLeft | Prepared::StructureRight => return Ok(true),
            _ => {}
        }
    }
    Ok(false)
}

pub(super) enum GeneralArguments {
    Inapplicable,
    EqualArity,
    UnequalArity,
}

/// C9 is entered only for two actual applications after full C8. The head is
/// popped first, then arguments in their original order. Unequal arity still
/// compares the peeled heads; its result cannot authorize equality of the pair.
pub(super) fn general_arguments(
    mut left: ExprId,
    mut right: ExprId,
    pairs: &mut Vec<(ExprId, ExprId)>,
    expressions: &Expressions,
    levels: &Levels,
    budget: &mut Budget,
) -> Result<GeneralArguments, HeadError> {
    if !pairs.is_empty() {
        return Err(ResourceError::Invariant.into());
    }
    if !matches!(
        expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?,
        ExprKind::App(..)
    ) || !matches!(
        expressions
            .get(right, budget)?
            .kind(expressions, levels, budget)?,
        ExprKind::App(..)
    ) {
        return Ok(GeneralArguments::Inapplicable);
    }
    loop {
        budget.charge_work(1)?;
        match (
            expressions
                .get(left, budget)?
                .kind(expressions, levels, budget)?,
            expressions
                .get(right, budget)?
                .kind(expressions, levels, budget)?,
        ) {
            (ExprKind::App(f, x), ExprKind::App(g, y)) => {
                push(pairs, (x, y), budget)?;
                left = f;
                right = g;
            }
            (a, b) => {
                let unequal = matches!(a, ExprKind::App(..)) || matches!(b, ExprKind::App(..));
                if unequal {
                    let count = pairs.len();
                    pairs.clear();
                    budget.release_frames(count)?;
                    for root in [&mut left, &mut right] {
                        while let ExprKind::App(f, _) =
                            expressions
                                .get(*root, budget)?
                                .kind(expressions, levels, budget)?
                        {
                            budget.charge_work(1)?;
                            *root = f;
                        }
                    }
                }
                push(pairs, (left, right), budget)?;
                return Ok(if unequal {
                    GeneralArguments::UnequalArity
                } else {
                    GeneralArguments::EqualArity
                });
            }
        }
    }
}

/// Guarded catalogue batching under checked operands in this immutable context.
/// Exact opaque non-Prop A prevents skipped intermediate proof/eta/unit routes.
pub(super) fn local_prefix(
    mut left: ExprId,
    mut right: ExprId,
    expressions: &Expressions,
    levels: &Levels,
    locals: &LocalContext,
    budget: &mut Budget,
) -> Result<Option<(ExprId, ExprId)>, HeadError> {
    let ExprKind::App(function, _) =
        expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(None);
    };
    let ExprKind::Free(id) =
        expressions
            .get(function, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(None);
    };
    let f = locals.get(id, budget)?;
    if f.value().is_some() {
        return Ok(None);
    }
    let ExprKind::Pi(_, domain, codomain, _) =
        expressions
            .get(f.ty(), budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(None);
    };
    if domain != codomain || expressions.get(codomain, budget)?.loose_range() != 0 {
        return Ok(None);
    }
    let ExprKind::Free(alpha) =
        expressions
            .get(domain, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(None);
    };
    let alpha = locals.get(alpha, budget)?;
    if alpha.value().is_some() {
        return Ok(None);
    }
    let ExprKind::Sort(level) =
        expressions
            .get(alpha.ty(), budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(None);
    };
    // One-sided probe: NotProven grants no positivity and
    // ends this classification without a negative conclusion (Ok(None)).
    if levels.get(level, budget)?.positive() != LevelPositive::Proven {
        return Ok(None);
    }
    let mut count = 0usize;
    while left != right {
        budget.charge_work(1)?;
        let a = expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?;
        let b = expressions
            .get(right, budget)?
            .kind(expressions, levels, budget)?;
        let (ExprKind::App(f, a), ExprKind::App(g, b)) = (a, b) else {
            break;
        };
        if f != function || g != function {
            break;
        }
        count = count.checked_add(1).ok_or(ResourceError::Counter)?;
        left = a;
        right = b;
    }
    Ok((count >= 2).then_some((left, right)))
}

/// Schedules one independent field; it produces no comparison result.
/// None marks C9 (both raw fields); Some marks the constructor side of C10,
/// after exact type/family checking and source-indexed projection construction.
#[allow(clippy::too_many_arguments)]
pub(super) fn schedule_fields(
    mut constructor: ExprId,
    pairs: &mut [(ExprId, ExprId)],
    constructor_left: Option<bool>,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<(), HeadError> {
    budget.charge_work(1)?;
    const FIELD_CAP: usize = 8;
    const BINDER_CAP: usize = 16;
    if scope.formation.is_some() || pairs.len() < 2 {
        return Ok(());
    }
    let mut applied = 0;
    let name = loop {
        budget.charge_work(1)?;
        match expressions
            .get(constructor, budget)?
            .kind(expressions, levels, budget)?
        {
            ExprKind::App(f, _) if applied < BINDER_CAP => {
                applied += 1;
                constructor = f;
            }
            ExprKind::Constant(name, _) => break name,
            _ => return Ok(()),
        }
    };
    let before = scope.before.min(environment.len());
    let Some(ctor) = environment.constructor(name, before, names, budget)? else {
        return Ok(());
    };
    let family = environment
        .inductive(ctor.family, before, names, budget)?
        .ok_or(ResourceError::Invariant)?;
    let rule = family
        .constructors
        .get(ctor.index as usize)
        .ok_or(ResourceError::Invariant)?;
    let fields = rule.num_fields as usize;
    // Committed family metadata describes this target constructor's actual
    // term parameters, including restored helpers; never use a recursor's
    // common parameter/motive/minor prefix for this binder-index proof.
    let parameters = family.num_params as usize;
    let Some(arity) = parameters.checked_add(fields) else {
        return Err(ResourceError::Counter.into());
    };
    // Refuse the whole layout before scanning its telescope or moving any pair.
    if !(2..=FIELD_CAP).contains(&fields) || arity > BINDER_CAP {
        return Ok(());
    }
    if constructor_left.is_some() {
        if applied != arity || pairs.len() != fields {
            return Ok(());
        }
    } else if applied != 0 || pairs.len() != arity {
        return Ok(());
    }
    let signature = environment
        .lookup_visible(name, before, None, names, budget)?
        .ok_or(ResourceError::Invariant)?;
    let crate::check::environment::TypeSource::Original(mut ty) = signature.ty else {
        return Ok(());
    };
    if scope.expression_end > expressions.len()
        || scope.level_end > levels.len()
        || ty.slot() as usize >= scope.expression_end
    {
        return Err(ResourceError::Invariant.into());
    }
    // Known bounded spans cover telescope/domain classification and both raw
    // field roots (only one root per field in C10); no per-node telemetry.
    let rank_reads = if constructor_left.is_some() {
        fields
    } else {
        2 * fields
    };
    budget.charge_work((arity + 2 * fields + rank_reads) as u64)?;
    for binder in 0..arity {
        let ExprKind::Pi(_, domain, body, _) =
            expressions
                .get(ty, budget)?
                .kind(expressions, levels, budget)?
        else {
            return Ok(());
        };
        if binder >= parameters {
            let preceding = binder - parameters;
            let domain_node = expressions.get(domain, budget)?;
            if domain_node.loose_range() != 0 {
                let ExprKind::Bound(index) = domain_node.kind(expressions, levels, budget)? else {
                    return Ok(());
                };
                // Exact original indices [i,i+p) refer only to term parameters.
                // Universe substitution never introduces term bound indices.
                if (index as usize) < preceding || index as usize >= preceding + parameters {
                    return Ok(());
                }
            }
        }
        ty = body;
    }
    // Reverse storage keeps C9 parameters (and the subsequently pushed head)
    // above this field segment. C10 pairs already contain the legal projection
    // for their ORIGINAL source index, so rotating never changes projection IDs.
    for index in (0..fields).rev() {
        let (a, z) = pairs[index];
        let mut constant = |root| -> Result<bool, HeadError> {
            Ok(matches!(
                expressions
                    .get(root, budget)?
                    .kind(expressions, levels, budget)?,
                ExprKind::Constant(..)
            ))
        };
        let cheap = match constructor_left {
            None => constant(a)? && constant(z)?,
            Some(true) => constant(a)?,
            Some(false) => constant(z)?,
        };
        if cheap {
            if index + 1 != fields {
                budget.charge_work((fields - index) as u64)?;
                pairs[index..fields].rotate_left(1);
            }
            return Ok(());
        }
    }
    Ok(())
}
