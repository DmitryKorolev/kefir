//! Consecutive checked head substitutions. The flat environment is
//! oldest first; entries have no loose bound variables and retain the request's
//! active free locals. No cache, typing permission or partial head escapes.
use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn reduce_with_cache(
    mut body: ExprId,
    argument: ExprId,
    mut path: ReductionPath,
    pending: &mut Scratch,
    expressions: &mut Expressions,
    levels: &Levels,
    names: &Names,
    mut cache: Option<(
        &mut crate::syntax::expressions::binding::plan::Cache,
        &mut crate::resource::SessionCacheBudget,
    )>,
    b: &mut Budget,
) -> Result<Head, HeadError> {
    let node = expressions.get(body, b)?;
    if node.loose_range() == 0 {
        if expressions.get(argument, b)?.loose_range() != 0 {
            return Err(ResourceError::Invariant.into());
        }
        return Ok(Head {
            expression: body,
            path,
        });
    }
    let kind = node.kind(expressions, levels, b)?;
    if matches!(kind, ExprKind::Bound(0)) {
        if expressions.get(argument, b)?.loose_range() != 0 {
            return Err(ResourceError::Invariant.into());
        }
        return Ok(Head {
            expression: argument,
            path,
        });
    }
    let mut next = redex_kind(kind, pending, expressions, levels, b)?;
    if next.is_none() {
        return Ok(Head {
            expression: bind_terminal(
                expressions,
                &mut cache,
                pending,
                body,
                Binding::Instantiate(&[argument]),
                levels,
                names,
                b,
            )?,
            path,
        });
    }
    // Preserve Instantiate's closed-argument invariant even when the delayed
    // argument is unused and final readback would never demand its slot.
    if expressions.get(argument, b)?.loose_range() != 0 {
        return Err(ResourceError::Invariant.into());
    }
    b.charge_work(1)?; // Flat environment retirement.
    let mut bindings = Vec::new();
    let result = (|| {
        b.grow_vec(&mut bindings, 1)?;
        bindings.push(argument);
        loop {
            let Some((next_body, next_argument, from_pending)) = next else {
                let expression = readback(
                    body,
                    &bindings,
                    expressions,
                    levels,
                    names,
                    &mut cache,
                    Some(pending),
                    b,
                )?;
                return Ok(Head { expression, path });
            };
            if from_pending {
                // Only this active head's innermost argument; never consume a
                // suspended eliminator's saved application prefix.
                pending.pop(b)?.ok_or(ResourceError::Invariant)?;
                b.charge_work(1)?;
                b.observe(Event::MachineSteps, 1);
            }
            let advanced = path.after_reduction()?;
            // The next argument is outside its binder. Resolve all preceding
            // binders before appending it, including dependent delayed arguments.
            let value = if from_pending {
                // This argument is outside every binder collected in bindings.
                next_argument
            } else {
                readback(
                    next_argument,
                    &bindings,
                    expressions,
                    levels,
                    names,
                    &mut cache,
                    None,
                    b,
                )?
            };
            if expressions.get(value, b)?.loose_range() != 0 {
                return Err(ResourceError::Invariant.into());
            }
            let needed = bindings
                .len()
                .checked_add(1)
                .ok_or(ResourceError::Counter)?;
            b.grow_vec(&mut bindings, needed)?;
            bindings.push(value);
            body = next_body;
            path = advanced;
            b.observe(Event::Reductions, 1);
            b.observe(Event::MachineSteps, 1);
            next = redex(body, pending, expressions, levels, b)?;
        }
    })();
    let cleanup = release(bindings, b).err().map(HeadError::from);
    match full::select_failure([result.as_ref().err().copied(), cleanup, None, None]) {
        Some(error) => Err(error),
        None => result,
    }
}

fn redex(
    root: ExprId,
    pending: &Scratch,
    expressions: &Expressions,
    levels: &Levels,
    b: &mut Budget,
) -> Result<Option<(ExprId, ExprId, bool)>, HeadError> {
    redex_kind(
        expressions.get(root, b)?.kind(expressions, levels, b)?,
        pending,
        expressions,
        levels,
        b,
    )
}

fn redex_kind(
    kind: ExprKind<'_>,
    pending: &Scratch,
    expressions: &Expressions,
    levels: &Levels,
    b: &mut Budget,
) -> Result<Option<(ExprId, ExprId, bool)>, HeadError> {
    b.charge_work(1)?;
    Ok(match kind {
        ExprKind::App(function, argument) => {
            match expressions.get(function, b)?.kind(expressions, levels, b)? {
                ExprKind::Lambda(_, _, body, _) => Some((body, argument, false)),
                _ => None,
            }
        }
        ExprKind::Let(_, _, value, body, _) => Some((body, value, false)),
        ExprKind::Lambda(_, _, body, _) if pending.applications.len() > pending.base() => {
            let argument = pending
                .applications
                .last()
                .ok_or(ResourceError::Invariant)?
                .argument;
            Some((body, argument, true))
        }
        _ => None,
    })
}

#[allow(clippy::too_many_arguments)]
fn readback(
    root: ExprId,
    bindings: &[ExprId],
    expressions: &mut Expressions,
    levels: &Levels,
    names: &Names,
    cache: &mut Option<(
        &mut crate::syntax::expressions::binding::plan::Cache,
        &mut crate::resource::SessionCacheBudget,
    )>,
    pending: Option<&mut Scratch>,
    b: &mut Budget,
) -> Result<ExprId, HeadError> {
    if expressions.get(root, b)?.loose_range() == 0 {
        return Ok(root);
    }
    let len = u32::try_from(bindings.len()).map_err(|_| ResourceError::Counter)?;
    let lookup = |index, _: &mut Budget| {
        let position = len
            .checked_sub(index)
            .and_then(|n| n.checked_sub(1))
            .ok_or(ResourceError::Invariant)?;
        Ok(bindings[position as usize].slot())
    };
    let operation = Binding::Environment {
        len,
        lookup: &lookup,
    };
    Ok(if let Some(pending) = pending {
        bind_terminal(
            expressions,
            cache,
            pending,
            root,
            operation,
            levels,
            names,
            b,
        )?
    } else {
        bind(expressions, cache, root, 0, operation, levels, names, b)?
    })
}

#[allow(clippy::too_many_arguments)]
fn bind(
    expressions: &mut Expressions,
    cache: &mut Option<(
        &mut crate::syntax::expressions::binding::plan::Cache,
        &mut crate::resource::SessionCacheBudget,
    )>,
    root: ExprId,
    cutoff: u32,
    operation: Binding<'_>,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<ExprId, crate::syntax::expressions::ExpressionError> {
    if let Some((plans, session)) = cache.as_mut() {
        plans.bind(
            expressions,
            root,
            cutoff,
            operation,
            levels,
            names,
            session,
            b,
        )
    } else {
        expressions.bind(root, cutoff, operation, levels, names, b)
    }
}

#[allow(clippy::too_many_arguments)]
fn bind_terminal(
    expressions: &mut Expressions,
    cache: &mut Option<(
        &mut crate::syntax::expressions::binding::plan::Cache,
        &mut crate::resource::SessionCacheBudget,
    )>,
    pending: &mut Scratch,
    root: ExprId,
    operation: Binding<'_>,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<ExprId, crate::syntax::expressions::ExpressionError> {
    let Some((plans, session)) = cache.as_mut() else {
        return expressions.bind(root, 0, operation, levels, names, b);
    };
    let (expression, spine) =
        plans.bind_head(expressions, root, operation, levels, names, session, b)?;
    if let Some(spine) = spine {
        b.charge_work(spine.arguments().len() as u64 + 1)?;
        // Append above the current suspension boundary. All values completed
        // under this request's environment; no delayed binder escapes.
        for &argument in spine.arguments().iter().rev() {
            pending.push(
                Application {
                    original: spine.head,
                    function: spine.head,
                    argument,
                },
                b,
            )?;
        }
        Ok(spine.head)
    } else {
        Ok(expression)
    }
}
