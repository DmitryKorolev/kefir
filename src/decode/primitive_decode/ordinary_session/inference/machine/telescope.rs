//! Close a consecutive run of already-returning lambda types.
use super::*;
use crate::syntax::expressions::binding::Abstraction;

pub(super) fn close(
    work: &mut Working<'_>,
    first: Frame,
    frames: &mut Vec<Frame>,
    mut body: Inferred,
    #[cfg(feature = "introspection")] failure_view: &mut Option<View>,
) -> Result<Inferred, Stop> {
    let mut ids = Vec::new();
    let result = (|| {
        // A LambdaBody has no outstanding demand. A memo frame or any other
        // continuation must observe its own complete intermediate judgment.
        for frame in std::iter::once(&first).chain(frames.iter().rev()) {
            let Frame::LambdaBody { local, .. } = frame else {
                break;
            };
            work.budget.charge_work(1)?;
            let required = ids.len() + 1;
            work.budget.grow_vec(&mut ids, required)?;
            ids.push(local.slot());
        }
        // The first ID is the innermost local. Each domain is outside its
        // own binder and every inner binder, hence it uses only the suffix.
        let positions = Abstraction::new(&ids, work.budget)?;
        body.ty = abstract_over(work, body.ty, positions.suffix(0)?)?;
        let mut frame = first;
        for index in 0..ids.len() {
            if index != 0 {
                #[cfg(feature = "introspection")]
                {
                    *failure_view = frames.last().and_then(|next| next.diagnostic_view());
                }
                work.budget.charge_work(1)?;
                work.budget.observe(Event::MachineSteps, 1);
                frame = frames.pop().ok_or(ResourceError::Invariant)?;
                work.budget.release_frames(1)?;
            }
            let Frame::LambdaBody {
                root,
                local,
                domain_path,
                ..
            } = frame
            else {
                return Err(ResourceError::Invariant.into());
            };
            let (pi, name, _, _, annotation) = work.binder_fields(root.expression)?;
            if pi {
                return Err(ResourceError::Invariant.into());
            }
            let domain = work.context.get(local.slot(), work.budget)?.ty();
            let closed = if index + 1 == ids.len() {
                domain
            } else {
                abstract_over(work, domain, positions.suffix(index + 1)?)?
            };
            body.ty = work.expressions.append(
                ExprKind::Pi(name, closed, body.ty, annotation),
                work.levels,
                work.names,
                work.budget,
            )?;
            body.path = body.path.maximum(domain_path);
            work.context.leave(local, work.budget)?;
        }
        Ok(body)
    })();
    let bytes = ids.capacity() * crate::resource::charged::bytes::<u32>();
    drop(ids);
    work.budget.release(bytes as u64)?;
    result
}

fn abstract_over(work: &mut Working<'_>, ty: ExprId, binding: Binding<'_>) -> Result<ExprId, Stop> {
    if !work.expressions.get(ty, work.budget)?.has_free() {
        return Ok(ty);
    }
    Ok(work
        .expressions
        .bind(ty, 0, binding, work.levels, work.names, work.budget)?)
}
