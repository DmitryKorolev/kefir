//! First slice: exact committed public root, ordinary index exposure,
//! and a raw demanded prefix. No generated default or shared-helper authority.
use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn root(
    site: &ConstantUse<'_>,
    environment: &Environment,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<bool, HeadError> {
    if site.mode != Mode::Safe || site.formation.is_some() || site.arguments.len() != 1 {
        return Ok(false);
    }
    let Some(symbols) = environment.getbang_symbols(site.before, site.formation, b)? else {
        return Ok(false);
    };
    if names.summary(site.name, b)?.canonical != names.summary(symbols[0], b)?.canonical {
        return Ok(false);
    }
    environment.check_use(site, levels, names, b)?;
    Ok(true)
}

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
    let end = scratch.applications.len();
    if end != frame.end as usize || end < 4 || end - 4 < scratch.base() {
        return Err(ResourceError::Invariant.into());
    }
    let alpha = scratch.applications[end - 1].argument;
    let list = scratch.applications[end - 3].argument;
    let ExprKind::Constant(name, universes) =
        expressions
            .get(frame.recursor, b)?
            .kind(expressions, levels, b)?
    else {
        return Err(ResourceError::Invariant.into());
    };
    if universes.len() != 1 {
        return Err(ResourceError::Invariant.into());
    }
    let universe = universes[0];
    let symbols = environment
        .getbang_symbols(scope.before, scope.formation, b)?
        .ok_or(ResourceError::Invariant)?;
    // Construction premise: Full head exposure receives a checked occurrence
    // in this exact scope. The certified root fixes its motive/handlers, and
    // the checked application fixes List alpha and its Inhabited instance.
    // The suspended index stays in this same owner, with sticky K state intact.
    let index = bounded_index(
        observed.expression,
        scope,
        environment,
        expressions,
        levels,
        names,
        b,
    )?;
    let mut path = observed.path;
    if let Some(index) = index {
        let walked = walk(
            list,
            alpha,
            universe,
            index,
            path,
            symbols,
            expressions,
            levels,
            names,
            b,
        )?;
        path = walked.path;
        if let Some(selected) = walked.selected {
            for _ in 0..4 {
                scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
            }
            return Ok(Head {
                expression: selected,
                path,
            });
        }
    }
    // Preserve the completed index for ordinary fallback. This marks changed
    // application syntax exactly as the arithmetic owner does. No syntax is
    // discarded, no provisional result/cache escapes and this root cannot retry:
    // delta starts at the original validated body rather than its root constant.
    let saved = &mut scratch.applications[end - 4];
    if saved.argument != observed.expression {
        saved.argument = observed.expression;
        saved.original = saved.function;
    }
    let site = ConstantUse {
        name,
        arguments: &[universe],
        parameters: scope.parameters,
        before: scope.before,
        formation: scope.formation,
        mode: scope.mode,
        expression_end: scope.expression_end,
        level_end: scope.level_end,
    };
    match environment.delta_step_with_cache(site, path, expressions, levels, names, cache, b)? {
        DeltaStep::Unfolded { expression, path } => Ok(Head { expression, path }),
        _ => Err(ResourceError::Invariant.into()),
    }
}

#[allow(clippy::too_many_arguments)]
fn bounded_index(
    root: ExprId,
    scope: &Scope<'_>,
    environment: &Environment,
    e: &Expressions,
    l: &Levels,
    n: &Names,
    b: &mut Budget,
) -> Result<Option<u16>, HeadError> {
    match e.get(root, b)?.kind(e, l, b)? {
        ExprKind::Natural(bytes) => {
            if bytes.len() > 4 {
                return Ok(None);
            }
            b.charge_work(bytes.len() as u64 + 1)?;
            let mut index = 0u16;
            for &digit in bytes {
                if !digit.is_ascii_digit() {
                    return Err(ResourceError::Invariant.into());
                }
                index = index * 10 + u16::from(digit - b'0');
            }
            Ok((index < 4096).then_some(index))
        }
        ExprKind::Constant(name, []) => {
            let Some((_, zero, _)) = environment.natural_constructors(
                scope.before,
                scope.formation,
                scope.expression_end,
                e,
                b,
            )?
            else {
                return Ok(None);
            };
            Ok((n.summary(name, b)?.canonical == n.summary(zero, b)?.canonical).then_some(0))
        }
        _ => Ok(None),
    }
}

fn same_alpha(
    a: ExprId,
    z: ExprId,
    e: &Expressions,
    l: &Levels,
    n: &Names,
    b: &mut Budget,
) -> Result<bool, ResourceError> {
    if a == z {
        return Ok(true);
    }
    match (e.get(a, b)?.kind(e, l, b)?, e.get(z, b)?.kind(e, l, b)?) {
        (ExprKind::Constant(an, au), ExprKind::Constant(zn, zu)) => {
            Ok(au == zu && n.summary(an, b)?.canonical == n.summary(zn, b)?.canonical)
        }
        _ => Ok(false),
    }
}

struct Walk {
    selected: Option<ExprId>,
    path: ReductionPath,
}

#[allow(clippy::too_many_arguments)]
fn walk(
    mut list: ExprId,
    alpha: ExprId,
    universe: LevelId,
    mut remaining: u16,
    mut path: ReductionPath,
    symbols: [NameId; 7],
    e: &Expressions,
    l: &Levels,
    n: &Names,
    b: &mut Budget,
) -> Result<Walk, HeadError> {
    // Coarse control/branch prepayment. Syntax/name reads retain their ordinary
    // charges; sequential branch height is never a sibling maximum or reset.
    b.charge_work(2 * (u64::from(remaining) + 1))?;
    loop {
        if e.get(list, b)?.loose_range() != 0 {
            return Ok(Walk {
                selected: None,
                path,
            });
        }
        let mut head = list;
        let mut args = [list; 3];
        let mut len = 0;
        loop {
            match e.get(head, b)?.kind(e, l, b)? {
                ExprKind::App(function, argument) if len < 3 => {
                    args[len] = argument;
                    len += 1;
                    head = function;
                }
                ExprKind::App(..) => {
                    return Ok(Walk {
                        selected: None,
                        path,
                    });
                }
                _ => break,
            }
        }
        let ExprKind::Constant(name, us) = e.get(head, b)?.kind(e, l, b)? else {
            return Ok(Walk {
                selected: None,
                path,
            });
        };
        if us != [universe] {
            return Ok(Walk {
                selected: None,
                path,
            });
        }
        let cons = n.summary(name, b)?.canonical == n.summary(symbols[5], b)?.canonical;
        // Nil/default and nonraw demanded tails use the justified ordinary route.
        if !cons || len != 3 || !same_alpha(args[2], alpha, e, l, n, b)? {
            return Ok(Walk {
                selected: None,
                path,
            });
        }
        path = path.after_reduction()?;
        b.observe(Event::Reductions, 1);
        if remaining == 0 {
            let selected = args[1];
            if e.get(selected, b)?.loose_range() != 0 {
                return Ok(Walk {
                    selected: None,
                    path,
                });
            }
            return Ok(Walk {
                selected: Some(selected),
                path,
            });
        }
        remaining -= 1;
        list = args[0];
    }
}
