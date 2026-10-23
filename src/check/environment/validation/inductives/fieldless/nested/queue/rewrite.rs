//! Saved-key replacement only. These roots remain unvalidated owner-local syntax.
//! A replacement keeps every original index handle and is never traversed again.
//! No result memo is shared between occurrences, constructors, or declarations.
use super::*;
use crate::syntax::levels::LevelKind;

enum Frame {
    Visit(ExprId),
    Finish(ExprId),
}
impl Queue {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn rewrite_constructors(
        &mut self,
        request: &Request<'_>,
        order: &Order,
        parameters: &parameters::Parameters,
        work: &mut Working<'_>,
        env: &Environment,
        before: usize,
    ) -> Result<(), Stop> {
        let mut levels = Vec::new();
        let result = (|| {
            let first = request.types.first().ok_or(ResourceError::Invariant)?;
            for &name in list(request.names, first.parameters)? {
                let level = work
                    .levels
                    .append(LevelKind::Param(name), work.names, work.budget)?;
                push(&mut levels, level, work.budget)?;
            }
            for &index in &order.constructors {
                let ctor = &request.constructors[index as usize];
                let root = parameters.rewrite(ctor.ty, work, |root, work| {
                    self.rewrite(root, &levels, parameters, work, env, before)
                })?;
                push(&mut self.original_constructors, root, work.budget)?;
            }
            for index in 0..self.constructors.len() {
                let root = self.constructors[index].ty;
                self.constructors[index].ty = parameters.rewrite(root, work, |root, work| {
                    self.rewrite(root, &levels, parameters, work, env, before)
                })?;
            }
            Ok(())
        })();
        release(levels, work.budget)?;
        result
    }
    fn rewrite(
        &self,
        root: ExprId,
        levels: &[LevelId],
        parameters: &parameters::Parameters,
        work: &mut Working<'_>,
        env: &Environment,
        before: usize,
    ) -> Result<ExprId, Stop> {
        walk(
            root,
            work,
            |root, work| self.replace(root, levels, parameters, work, env, before),
            |root, _| Ok(root),
        )
    }
    fn replace(
        &self,
        root: ExprId,
        levels: &[LevelId],
        parameters: &parameters::Parameters,
        work: &mut Working<'_>,
        env: &Environment,
        before: usize,
    ) -> Result<Option<ExprId>, Stop> {
        let mut args = Vec::new();
        let result = (|| {
            let mut head = root;
            while let ExprKind::App(f, a) = work.expressions.get(head, work.budget)?.kind(
                work.expressions,
                work.levels,
                work.budget,
            )? {
                push(&mut args, a, work.budget)?;
                head = f;
            }
            let ExprKind::Constant(name, _) = work.expressions.get(head, work.budget)?.kind(
                work.expressions,
                work.levels,
                work.budget,
            )?
            else {
                return Ok(None);
            };
            let Some(metadata) = env.inductive(name, before, work.names, work.budget)? else {
                return Ok(None);
            };
            let count = metadata.num_params as usize;
            if count == 0 || args.len() < count {
                return Ok(None);
            }
            // Use the original prefix handle, not a reconstructed or normalized key.
            let indices = args.len() - count;
            let mut prefix = root;
            for _ in 0..indices {
                let ExprKind::App(f, _) = work.expressions.get(prefix, work.budget)?.kind(
                    work.expressions,
                    work.levels,
                    work.budget,
                )?
                else {
                    return Err(ResourceError::Invariant.into());
                };
                prefix = f;
            }
            self.replace_saved(prefix, &args[..indices], levels, parameters, work)
        })();
        release(args, work.budget)?;
        result
    }
    /// `reverse_indices` are the unchanged outer arguments, outermost first.
    /// Key and helper belong to this same queue; generated helpers have no authority.
    fn replace_saved(
        &self,
        prefix: ExprId,
        reverse_indices: &[ExprId],
        levels: &[LevelId],
        parameters: &parameters::Parameters,
        work: &mut Working<'_>,
    ) -> Result<Option<ExprId>, Stop> {
        let Some(key) = self.find(prefix, work)? else {
            return Ok(None);
        };
        let mut helper = None;
        for family in &self.families {
            work.budget.charge_work(1)?;
            if family.key as usize == key && helper.replace(family.helper).is_some() {
                return Err(ResourceError::Invariant.into());
            }
        }
        let helper = helper.ok_or(ResourceError::Invariant)?;
        let root = application(helper, levels, &[], work)?;
        let mut root = parameters.apply(root, work)?;
        for &index in reverse_indices.iter().rev() {
            root = work.expressions.append(
                ExprKind::App(root, index),
                work.levels,
                work.names,
                work.budget,
            )?;
        }
        Ok(Some(root))
    }
}
/// Iterative occurrence walk. Completed pre-replacements are not revisited;
/// unchanged composites keep exact handles. No expression/result memo exists.
pub(super) fn walk(
    root: ExprId,
    work: &mut Working<'_>,
    mut before: impl FnMut(ExprId, &mut Working<'_>) -> Result<Option<ExprId>, Stop>,
    mut after: impl FnMut(ExprId, &mut Working<'_>) -> Result<ExprId, Stop>,
) -> Result<ExprId, Stop> {
    let mut stack = Vec::new();
    let mut values = Vec::new();
    let result = (|| {
        push_frame(&mut stack, Frame::Visit(root), work.budget)?;
        while let Some(frame) = pop_frame(&mut stack, work.budget)? {
            work.budget.charge_work(1)?;
            match frame {
                Frame::Visit(root) => {
                    if let Some(replacement) = before(root, work)? {
                        push_frame(&mut values, replacement, work.budget)?;
                        continue;
                    }
                    let children = children(root, work)?;
                    if children[0].is_none() {
                        let root = after(root, work)?;
                        push_frame(&mut values, root, work.budget)?;
                    } else {
                        push_frame(&mut stack, Frame::Finish(root), work.budget)?;
                        for child in children.into_iter().rev().flatten() {
                            push_frame(&mut stack, Frame::Visit(child), work.budget)?;
                        }
                    }
                }
                Frame::Finish(root) => {
                    let mut changed = children(root, work)?;
                    for item in changed.iter_mut().rev().filter(|c| c.is_some()) {
                        *item = Some(
                            pop_frame(&mut values, work.budget)?.ok_or(ResourceError::Invariant)?,
                        );
                    }
                    let root = rebuild(root, changed, work)?;
                    let root = after(root, work)?;
                    push_frame(&mut values, root, work.budget)?;
                }
            }
        }
        let result = pop_frame(&mut values, work.budget)?.ok_or(ResourceError::Invariant)?;
        if !values.is_empty() {
            return Err(ResourceError::Invariant.into());
        }
        Ok(result)
    })();
    let a = release_stack(stack, work.budget);
    let b = release_stack(values, work.budget);
    a?;
    b?;
    result
}
pub(super) fn rebuild(
    root: ExprId,
    changed: [Option<ExprId>; 3],
    work: &mut Working<'_>,
) -> Result<ExprId, Stop> {
    if children(root, work)? == changed {
        return Ok(root);
    }
    let a = changed[0].ok_or(ResourceError::Invariant)?;
    let node = work.expressions.get(root, work.budget)?.kind(
        work.expressions,
        work.levels,
        work.budget,
    )?;
    let kind = match node {
        ExprKind::Projection(name, index, _) => ExprKind::Projection(name, index, a),
        ExprKind::App(..) => ExprKind::App(a, changed[1].ok_or(ResourceError::Invariant)?),
        ExprKind::Pi(name, _, _, info) => {
            ExprKind::Pi(name, a, changed[1].ok_or(ResourceError::Invariant)?, info)
        }
        ExprKind::Lambda(name, _, _, info) => {
            ExprKind::Lambda(name, a, changed[1].ok_or(ResourceError::Invariant)?, info)
        }
        ExprKind::Let(name, _, _, _, non_dep) => ExprKind::Let(
            name,
            a,
            changed[1].ok_or(ResourceError::Invariant)?,
            changed[2].ok_or(ResourceError::Invariant)?,
            non_dep,
        ),
        _ => return Err(ResourceError::Invariant.into()),
    };
    Ok(work
        .expressions
        .append(kind, work.levels, work.names, work.budget)?)
}
