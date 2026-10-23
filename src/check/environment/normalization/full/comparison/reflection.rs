//! Canonical Bool shape validation for the optional closed-left reflection route.
use super::*;
use crate::check::environment::TypeSource;
use crate::syntax::levels::{LevelKind, LevelNames, NameId};
use crate::syntax::names::Component;

fn component(
    name: NameId,
    prefix: NameId,
    text: &str,
    names: &Names,
    b: &mut Budget,
) -> Result<bool, ResourceError> {
    Ok(
        matches!(names.view(name, b)?, Some((parent, Component::String(s)))
        if s == text && names.summary(parent, b)?.canonical == names.summary(prefix, b)?.canonical),
    )
}

/// A matching spelling with an uncertified referent is unavailable, not false.
/// The metadata consulted here can only come from committed validated safe groups.
#[allow(clippy::too_many_arguments)]
pub(super) fn candidate(
    root: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<bool, HeadError> {
    let ExprKind::Constant(name, args) = expressions.get(root, b)?.kind(expressions, levels, b)?
    else {
        return Ok(false);
    };
    let Some((family_name, Component::String("true"))) = names.view(name, b)? else {
        return Ok(false);
    };
    if !component(family_name, NameId::ANONYMOUS, "Bool", names, b)? {
        return Ok(false);
    }
    let before = scope.before.min(environment.len());
    let Some(ctor) = environment.constructor(name, before, names, b)? else {
        return Err(HeadError::Unsupported);
    };
    if !args.is_empty()
        || ctor.index != 1
        || names.summary(ctor.family, b)?.canonical != names.summary(family_name, b)?.canonical
    {
        return Err(HeadError::Unsupported);
    }
    let family = environment
        .inductive(ctor.family, before, names, b)?
        .ok_or(HeadError::Unsupported)?;
    if !family.nonrecursive
        || family.num_params != 0
        || family.num_indices != 0
        || family.constructors.len() != 2
    {
        return Err(HeadError::Unsupported);
    }
    let signature = environment
        .lookup(ctor.family, before, names, b)?
        .ok_or(HeadError::Unsupported)?;
    let TypeSource::Original(ty) = signature.ty else {
        return Err(HeadError::Unsupported);
    };
    if !signature.parameters.is_empty() {
        return Err(HeadError::Unsupported);
    }
    let ExprKind::Sort(level) = expressions.get(ty, b)?.kind(expressions, levels, b)? else {
        return Err(HeadError::Unsupported);
    };
    let LevelKind::Succ(zero) = levels.get(level, b)?.kind() else {
        return Err(HeadError::Unsupported);
    };
    if levels.get(zero, b)?.kind() != LevelKind::Zero {
        return Err(HeadError::Unsupported);
    }
    for (rule, label) in family.constructors.iter().zip(["false", "true"]) {
        if rule.num_fields != 0 || !component(rule.constructor, ctor.family, label, names, b)? {
            return Err(HeadError::Unsupported);
        }
        let signature = environment
            .lookup(rule.constructor, before, names, b)?
            .ok_or(HeadError::Unsupported)?;
        let TypeSource::Original(ty) = signature.ty else {
            return Err(HeadError::Unsupported);
        };
        if !signature.parameters.is_empty() {
            return Err(HeadError::Unsupported);
        }
        let ExprKind::Constant(result, universes) =
            expressions.get(ty, b)?.kind(expressions, levels, b)?
        else {
            return Err(HeadError::Unsupported);
        };
        if !universes.is_empty()
            || names.summary(result, b)?.canonical != names.summary(ctor.family, b)?.canonical
        {
            return Err(HeadError::Unsupported);
        }
    }
    Ok(true)
}

pub(super) fn result_is_true(
    result: ExprId,
    right: ExprId,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<bool, HeadError> {
    let ExprKind::Constant(a, args) = expressions.get(result, b)?.kind(expressions, levels, b)?
    else {
        return Ok(false);
    };
    let ExprKind::Constant(z, _) = expressions.get(right, b)?.kind(expressions, levels, b)? else {
        return Err(ResourceError::Invariant.into());
    };
    Ok(args.is_empty() && names.summary(a, b)?.canonical == names.summary(z, b)?.canonical)
}
