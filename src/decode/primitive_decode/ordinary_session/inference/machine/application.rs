//! Carry checked substitutions through syntactic Pi results of adjacent applications.
use super::*;

pub(super) fn finish(
    work: &mut Working<'_>,
    environments: &mut EvaluationEnvironments,
    frames: &mut Vec<Frame>,
    codomain: ExprId,
    argument: View,
    path: ReductionPath,
    #[cfg(feature = "introspection")] failure_view: &mut Option<View>,
) -> Result<Option<Inferred>, Stop> {
    let parent = match frames.last().copied() {
        Some(Frame::AppSubstitution(env)) => {
            frames.pop();
            work.budget.release_frames(1)?;
            env
        }
        _ => EnvId::EMPTY,
    };
    let source = work.expressions.get(codomain, work.budget)?;
    if source.loose_range() == 0 {
        return Ok(Some(Inferred { ty: codomain, path }));
    }
    // A substitution cannot change a Pi's outer constructor. This replaces
    // only a zero-rewrite head request. The argument's type has already been
    // compared at this exact application; every following argument is checked.
    let next = match frames.last().copied() {
        Some(Frame::AppFunction(root, incoming)) => {
            match source.kind(work.expressions, work.levels, work.budget)? {
                ExprKind::Pi(_, domain, body, _) => Some((root, incoming, domain, body)),
                _ => None,
            }
        }
        _ => None,
    };
    if parent == EnvId::EMPTY && next.is_none() {
        let ty = work.instantiate_application_result(codomain, argument, environments)?;
        return Ok(Some(Inferred { ty, path }));
    }
    let value = work.materialize_view(argument, environments)?;
    if work.expressions.get(value, work.budget)?.loose_range() != 0 {
        return Err(ResourceError::Invariant.into());
    }
    let env = environments.extend(parent, BindingId::new(value.slot()), work.budget)?;
    let materialized = |work: &mut Working<'_>, expression| {
        work.materialize_view(
            View {
                expression,
                environment: env,
            },
            environments,
        )
    };
    let Some((root, incoming, domain, body)) = next else {
        let ty = materialized(work, codomain)?;
        return Ok(Some(Inferred { ty, path }));
    };
    #[cfg(feature = "introspection")]
    {
        *failure_view = Some(root);
    }
    work.budget.charge_work(1)?;
    work.budget.observe(Event::MachineSteps, 1);
    frames.pop();
    work.budget.release_frames(1)?;
    let domain = materialized(work, domain)?;
    let ExprKind::App(_, arg) = work.expressions.get(root.expression, work.budget)?.kind(
        work.expressions,
        work.levels,
        work.budget,
    )?
    else {
        return Err(ResourceError::Invariant.into());
    };
    push(frames, Frame::AppSubstitution(env), work.budget)?;
    push(
        frames,
        Frame::AppArgument {
            root,
            domain,
            codomain: body,
            function_path: path,
        },
        work.budget,
    )?;
    push(frames, Frame::Visit(root.child(arg), incoming), work.budget)?;
    Ok(None)
}
