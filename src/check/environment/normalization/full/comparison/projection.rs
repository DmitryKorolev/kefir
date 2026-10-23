//! C7 observations live only in one checked comparison and its fixed scope.
//! Original projections stay in the owner; this attempt never owns a verdict.
use super::*;
use crate::syntax::levels::LevelNames;
mod paired;
pub(super) use paired::Step;

pub(super) struct Attempt {
    pub left: Head,
    pub right: Head,
    paired: paired::State,
}
const _: () = assert!(std::mem::size_of::<Attempt>() == 28);

pub(super) enum Preparation {
    NotPair,
    Expose,
    ExposeUnresolved,
    Compare(Attempt),
}

#[allow(clippy::too_many_arguments)]
pub(super) fn prepare(
    left: ExprId,
    right: ExprId,
    incoming: ReductionPath,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Preparation, HeadError> {
    let sources = spine::same_projection_sources(
        left,
        right,
        scope,
        environment,
        expressions,
        levels,
        names,
        budget,
    )?;
    Ok(match sources {
        spine::ProjectionSources::NotPair => Preparation::NotPair,
        spine::ProjectionSources::Unmatched => Preparation::Expose,
        spine::ProjectionSources::Matched(left, right)
            if spine::closed_first_arguments_have_different_syntax(
                left,
                right,
                expressions,
                levels,
                names,
                budget,
            )? =>
        {
            Preparation::ExposeUnresolved
        }
        spine::ProjectionSources::Matched(left, right) => {
            Preparation::Compare(Attempt::new(left, right, incoming))
        }
    })
}

/// Called only after the driver's full observation of this checked source.
/// One linear spine scan, no allocation or per-node retained state.
#[allow(clippy::too_many_arguments)]
pub(super) fn field(
    projection: ExprId,
    source: Head,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Option<Head>, HeadError> {
    let ExprKind::Projection(family, field, _) =
        expressions
            .get(projection, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Err(ResourceError::Invariant.into());
    };
    let metadata = environment
        .inductive(family, scope.before.min(environment.len()), names, budget)?
        .ok_or(HeadError::Unsupported)?;
    let [constructor] = metadata.constructors else {
        return Err(HeadError::Unsupported);
    };
    if field >= constructor.num_fields {
        return Err(HeadError::Unsupported);
    }
    let arity = metadata
        .num_params
        .checked_add(constructor.num_fields)
        .ok_or(ResourceError::Counter)?;
    let position = constructor.num_fields - field - 1;
    let mut root = source.expression;
    let mut count = 0u32;
    let mut selected = None;
    while let ExprKind::App(function, argument) =
        expressions
            .get(root, budget)?
            .kind(expressions, levels, budget)?
    {
        budget.charge_work(1)?;
        if count == position {
            selected = Some(argument);
        }
        count = count.checked_add(1).ok_or(ResourceError::Counter)?;
        root = function;
    }
    let ExprKind::Constant(name, _) =
        expressions
            .get(root, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Ok(None);
    };
    if names.summary(name, budget)?.canonical
        != names.summary(constructor.constructor, budget)?.canonical
    {
        return Ok(None);
    }
    if count != arity {
        return Err(HeadError::Unsupported);
    }
    let expression = selected.ok_or(ResourceError::Invariant)?;
    let path = source.path.after_reduction()?;
    budget.observe(crate::resource::Event::Reductions, 1);
    Ok(Some(Head { expression, path }))
}
