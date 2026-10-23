//! Positive structure expansion for a previously checked recursor major.
use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn eligible(
    mut major: ExprId,
    recursor: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<bool, HeadError> {
    let family = family(recursor, scope, environment, expressions, levels, names, b)?;
    let metadata = environment
        .inductive(family, scope.before.min(environment.len()), names, b)?
        .ok_or(ResourceError::Invariant)?;
    if !metadata.nonrecursive || metadata.num_indices != 0 || metadata.constructors.len() != 1 {
        return Ok(false);
    }
    loop {
        b.charge_work(1)?;
        match expressions.get(major, b)?.kind(expressions, levels, b)? {
            ExprKind::App(function, _) => major = function,
            ExprKind::Constant(name, arguments) => {
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
                if environment
                    .constructor(name, scope.before.min(environment.len()), names, b)?
                    .is_some()
                {
                    return Ok(false);
                }
                break;
            }
            // Literal conversion precedes this structure alternative; these
            // representations must retain their dedicated reduction rules.
            ExprKind::Natural(_) | ExprKind::String(_) => return Ok(false),
            _ => break,
        }
    }
    // The owner validated this scope's live phase and original frontiers.
    // Formation may supply the checked major's type, but all recursor/family
    // metadata above is bounded by the committed frontier. The following
    // type/Sort observations and projection checks grant no staged computation
    // authority.
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn family(
    recursor: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<NameId, HeadError> {
    let ExprKind::Constant(name, _) = expressions.get(recursor, b)?.kind(expressions, levels, b)?
    else {
        return Err(ResourceError::Invariant.into());
    };
    Ok(environment
        .recursor(name, scope.before.min(environment.len()), names, b)?
        .ok_or(ResourceError::Invariant)?
        .family)
}

/// Exact major-family identity and arity, without treating unavailable typing as
/// a mismatch. The caller retains the original exposed type across Sort checking.
#[allow(clippy::too_many_arguments)]
pub(super) fn matches_type(
    mut ty: ExprId,
    recursor: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<bool, HeadError> {
    let expected = family(recursor, scope, environment, expressions, levels, names, b)?;
    let mut parameters = 0usize;
    loop {
        b.charge_work(1)?;
        match expressions.get(ty, b)?.kind(expressions, levels, b)? {
            ExprKind::App(f, _) => {
                parameters = parameters.checked_add(1).ok_or(ResourceError::Counter)?;
                ty = f;
            }
            ExprKind::Constant(name, arguments) => {
                let valid = environment.inductive_type_use(
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
                if !valid
                    || names.summary(name, b)?.canonical != names.summary(expected, b)?.canonical
                {
                    return Ok(false);
                }
                let metadata = environment
                    .inductive(name, scope.before.min(environment.len()), names, b)?
                    .ok_or(ResourceError::Invariant)?;
                return Ok(metadata.num_indices == 0 && metadata.num_params as usize == parameters);
            }
            _ => return Ok(false),
        }
    }
}

/// The caller established exact family, non-Prop actual type, and a checked
/// original major. Re-derived constructor telescopes and dependent projection
/// typing justify these arguments. Scratch is not retained across a demand.
#[allow(clippy::too_many_arguments)]
pub(super) fn expand(
    mut ty: ExprId,
    major: ExprId,
    scratch: &mut Scratch,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &mut Expressions,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<ExprId, HeadError> {
    scratch.constructor_arguments.clear();
    loop {
        b.charge_work(1)?;
        match expressions.get(ty, b)?.kind(expressions, levels, b)? {
            ExprKind::App(f, argument) => {
                let needed = scratch
                    .constructor_arguments
                    .len()
                    .checked_add(1)
                    .ok_or(ResourceError::Counter)?;
                b.grow_vec(&mut scratch.constructor_arguments, needed)?;
                scratch.constructor_arguments.push(argument);
                ty = f;
            }
            ExprKind::Constant(family, universes) => {
                let metadata = environment
                    .inductive(family, scope.before.min(environment.len()), names, b)?
                    .ok_or(ResourceError::Invariant)?;
                let [constructor] = metadata.constructors else {
                    return Err(ResourceError::Invariant.into());
                };
                if !metadata.nonrecursive
                    || metadata.num_indices != 0
                    || metadata.num_params as usize != scratch.constructor_arguments.len()
                {
                    return Err(ResourceError::Invariant.into());
                }
                b.charge_work(universes.len() as u64 + 1)?;
                b.grow_vec(&mut scratch.arguments, universes.len())?;
                scratch.arguments.clear();
                scratch.arguments.extend_from_slice(universes);
                let mut result = expressions.append(
                    ExprKind::Constant(constructor.constructor, &scratch.arguments),
                    levels,
                    names,
                    b,
                )?;
                for &argument in scratch.constructor_arguments.iter().rev() {
                    result =
                        expressions.append(ExprKind::App(result, argument), levels, names, b)?;
                }
                for index in 0..constructor.num_fields {
                    let projection = expressions.append(
                        ExprKind::Projection(family, index, major),
                        levels,
                        names,
                        b,
                    )?;
                    result =
                        expressions.append(ExprKind::App(result, projection), levels, names, b)?;
                }
                scratch.constructor_arguments.clear();
                scratch.arguments.clear();
                return Ok(result);
            }
            _ => return Err(ResourceError::Invariant.into()),
        }
    }
}
