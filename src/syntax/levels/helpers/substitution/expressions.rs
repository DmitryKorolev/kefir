//! Universe transport through an original expression frontier.
//! One fixed instance shares its level and expression memos across all roots.
use super::*;
use crate::syntax::expressions::{ExprId, ExprKind, ExpressionError, Expressions};

pub(crate) struct Instance<'a> {
    pub expression_end: usize,
    pub level_end: usize,
    pub parameters: &'a [NameId],
    pub replacements: &'a [LevelId],
}
#[derive(Clone, Copy)]
enum Frame {
    Visit(ExprId),
    Finish(ExprId),
}
const _: () = assert!(size_of::<Frame>() == 8);
pub(crate) struct ExpressionSubstitution<'e, 's, 'h, 'a, N, const CACHED: bool = true> {
    expressions: &'e mut Expressions,
    levels: &'s mut Substitution<'h, 'a, N, CACHED>,
    end: usize,
    // Original expression handle -> completed expression result, separate from
    // level/name maps. Valid only for this fixed instance and original frontier.
    // No binder, context, declaration, thread or table-origin change is admitted.
    memo: Map,
    frames: Vec<Frame>,
    results: Vec<ExprId>,
    universe_list: Vec<LevelId>,
    failure: Option<ExpressionError>,
}
impl Expressions {
    /// Caller validates universe scope and the original-template frontier. No
    /// generated source, environment change, binder/context/declaration change or
    /// replacement-vector change is admitted during this operation. Loose/free
    /// term variables are transported unchanged, never granted scope validity.
    pub(crate) fn with_universe_substitution<N: LevelNames, T>(
        &mut self,
        levels: &mut Levels,
        names: &N,
        instance: Instance<'_>,
        b: &mut Budget,
        body: impl FnOnce(&mut ExpressionSubstitution<'_, '_, '_, '_, N>) -> Result<T, ExpressionError>,
    ) -> Result<T, ExpressionError> {
        if instance.expression_end > self.len() {
            return Err(ResourceError::Invariant.into());
        }
        levels.with_substitution(
            names,
            instance.level_end,
            instance.parameters,
            instance.replacements,
            b,
            |levels| self.with_expression_substitution(levels, instance.expression_end, body),
        )?
    }

    /// Template construction: reconstruct each parameter-dependent
    /// occurrence independently in both stores; preserve exact replacement leaves.
    /// The caller validates an immutable owned template frontier, including any
    /// generated pool's phase and lifetime. This operation does not grant typing
    /// authority or permit relabeling generated roots as imported templates.
    pub(crate) fn with_uncached_universe_substitution<N: LevelNames, T>(
        &mut self,
        levels: &mut Levels,
        names: &N,
        instance: Instance<'_>,
        b: &mut Budget,
        body: impl FnOnce(
            &mut ExpressionSubstitution<'_, '_, '_, '_, N, false>,
        ) -> Result<T, ExpressionError>,
    ) -> Result<T, ExpressionError> {
        self.with_universe_substitution_mode::<N, T, false>(levels, names, instance, b, body)
    }

    fn with_universe_substitution_mode<N: LevelNames, T, const CACHED: bool>(
        &mut self,
        levels: &mut Levels,
        names: &N,
        instance: Instance<'_>,
        b: &mut Budget,
        body: impl FnOnce(
            &mut ExpressionSubstitution<'_, '_, '_, '_, N, CACHED>,
        ) -> Result<T, ExpressionError>,
    ) -> Result<T, ExpressionError> {
        if instance.expression_end > self.len() {
            return Err(ResourceError::Invariant.into());
        }
        levels.with_substitution_mode::<N, _, CACHED>(
            names,
            instance.level_end,
            instance.parameters,
            instance.replacements,
            b,
            |levels| self.with_expression_substitution(levels, instance.expression_end, body),
        )?
    }

    fn with_expression_substitution<N: LevelNames, T, const CACHED: bool>(
        &mut self,
        levels: &mut Substitution<'_, '_, N, CACHED>,
        end: usize,
        body: impl FnOnce(
            &mut ExpressionSubstitution<'_, '_, '_, '_, N, CACHED>,
        ) -> Result<T, ExpressionError>,
    ) -> Result<Result<T, ExpressionError>, ResourceError> {
        levels.h.budget.charge_work(5)?;
        let mut s = ExpressionSubstitution {
            expressions: self,
            levels,
            end,
            memo: Map::default(),
            frames: Vec::new(),
            results: Vec::new(),
            universe_list: Vec::new(),
            failure: None,
        };
        let result = body(&mut s);
        let result = match s.failure {
            Some(error) => Err(error),
            None => result,
        };
        let count = s.frames.len() + s.results.len();
        let a = release_vec(take(&mut s.memo.entries), s.levels.h.budget);
        let c = release_vec(take(&mut s.frames), s.levels.h.budget);
        let d = release_vec(take(&mut s.results), s.levels.h.budget);
        let e = release_vec(take(&mut s.universe_list), s.levels.h.budget);
        let f = s.levels.h.budget.release_frames(count);
        a.and(c).and(d).and(e).and(f)?;
        Ok(result)
    }
}
impl<N: LevelNames, const CACHED: bool> ExpressionSubstitution<'_, '_, '_, '_, N, CACHED> {
    fn cached(&self) -> bool {
        CACHED
    }
    fn remember(&mut self, source: ExprId, result: ExprId) -> Result<(), ResourceError> {
        if self.cached() {
            self.memo
                .insert(source.slot(), result.slot(), self.levels.h.budget)?;
        }
        Ok(())
    }
    fn push(&mut self, frame: Frame) -> Result<(), ResourceError> {
        let required = self.frames.len() + 1;
        self.levels.h.budget.reserve_frames(1)?;
        if let Err(e) = self.levels.h.budget.grow_vec(&mut self.frames, required) {
            self.levels.h.budget.release_frames(1)?;
            return Err(e);
        }
        self.frames.push(frame);
        Ok(())
    }
    fn result(&mut self, id: ExprId) -> Result<(), ResourceError> {
        let required = self.results.len() + 1;
        self.levels.h.budget.reserve_frames(1)?;
        if let Err(e) = self.levels.h.budget.grow_vec(&mut self.results, required) {
            self.levels.h.budget.release_frames(1)?;
            return Err(e);
        }
        self.results.push(id);
        Ok(())
    }
    fn pop(&mut self) -> Result<ExprId, ResourceError> {
        let id = self.results.pop().ok_or(ResourceError::Invariant)?;
        self.levels.h.budget.release_frames(1)?;
        Ok(id)
    }
    fn append(&mut self, kind: ExprKind<'_>) -> Result<ExprId, ExpressionError> {
        self.expressions.append(
            kind,
            self.levels.h.levels,
            self.levels.h.names,
            self.levels.h.budget,
        )
    }
    pub(crate) fn apply(&mut self, root: ExprId) -> Result<ExprId, ExpressionError> {
        if let Some(e) = self.failure {
            return Err(e);
        }
        let result = self.inner(root);
        if let Err(e) = result {
            self.failure = Some(e);
        }
        result
    }
    fn inner(&mut self, root: ExprId) -> Result<ExprId, ExpressionError> {
        self.push(Frame::Visit(root))?;
        while let Some(frame) = self.frames.pop() {
            self.levels.h.budget.release_frames(1)?;
            self.levels.h.budget.charge_work(1)?;
            self.levels
                .h
                .budget
                .observe(crate::resource::Event::MachineSteps, 1);
            let id = match frame {
                Frame::Visit(id) | Frame::Finish(id) => id,
            };
            if id.slot() as usize >= self.end {
                return Err(ResourceError::Invariant.into());
            }
            match frame {
                Frame::Visit(_) => {
                    let node = self.expressions.get(id, self.levels.h.budget)?;
                    if !node.has_param() {
                        self.result(id)?;
                        continue;
                    }
                    if let Some(e) = if self.cached() {
                        self.memo.get(id.slot(), self.levels.h.budget)?
                    } else {
                        None
                    } {
                        let result = self
                            .expressions
                            .resolve_slot(e.value, self.levels.h.budget)?;
                        self.result(result)?;
                        continue;
                    }
                    let leaf = match node.kind(
                        self.expressions,
                        self.levels.h.levels,
                        self.levels.h.budget,
                    )? {
                        ExprKind::Sort(original) => {
                            let level = self.levels.apply(original)?;
                            Some(if level == original {
                                id
                            } else {
                                self.append(ExprKind::Sort(level))?
                            })
                        }
                        ExprKind::Constant(name, levels) => {
                            self.universe_list.clear();
                            let mut changed = false;
                            for &original in levels {
                                let level = self.levels.apply(original)?;
                                changed |= level != original;
                                let required = self.universe_list.len() + 1;
                                self.levels
                                    .h
                                    .budget
                                    .grow_vec(&mut self.universe_list, required)?;
                                self.universe_list.push(level);
                            }
                            Some(if !changed {
                                id
                            } else {
                                self.expressions.append(
                                    ExprKind::Constant(name, &self.universe_list),
                                    self.levels.h.levels,
                                    self.levels.h.names,
                                    self.levels.h.budget,
                                )?
                            })
                        }
                        ExprKind::Bound(_)
                        | ExprKind::Free(_)
                        | ExprKind::Natural(_)
                        | ExprKind::String(_) => return Err(ResourceError::Invariant.into()),
                        // Decode once, then retain only owned child handles
                        // before mutating the frame/row owners. Each push and
                        // work charge stays in the original order; a second
                        // descriptor query here would only repeat this work.
                        ExprKind::App(a, b)
                        | ExprKind::Lambda(_, a, b, _)
                        | ExprKind::Pi(_, a, b, _) => {
                            self.push(Frame::Finish(id))?;
                            self.push(Frame::Visit(b))?;
                            self.push(Frame::Visit(a))?;
                            None
                        }
                        ExprKind::Let(_, a, b, c, _) => {
                            self.push(Frame::Finish(id))?;
                            self.push(Frame::Visit(c))?;
                            self.push(Frame::Visit(b))?;
                            self.push(Frame::Visit(a))?;
                            None
                        }
                        ExprKind::Projection(_, _, a) => {
                            self.push(Frame::Finish(id))?;
                            self.push(Frame::Visit(a))?;
                            None
                        }
                        _ => {
                            // Preserve the original unsupported-branch frame
                            // charge before declining this local operation.
                            self.push(Frame::Finish(id))?;
                            return Err(ResourceError::Invariant.into());
                        }
                    };
                    if let Some(result) = leaf {
                        self.remember(id, result)?;
                        self.result(result)?;
                    }
                }
                Frame::Finish(_) => {
                    let last = self.pop()?;
                    let node = self.expressions.get(id, self.levels.h.budget)?;
                    // Only scalar fields and child handles are borrowed here;
                    // literals/constants finish in the leaf branch above.
                    let result = match node.kind(
                        self.expressions,
                        self.levels.h.levels,
                        self.levels.h.budget,
                    )? {
                        ExprKind::App(a, b) => {
                            let first = self.pop()?;
                            if (first, last) == (a, b) {
                                id
                            } else {
                                self.append(ExprKind::App(first, last))?
                            }
                        }
                        ExprKind::Lambda(name, a, b, info) => {
                            let first = self.pop()?;
                            if (first, last) == (a, b) {
                                id
                            } else {
                                self.append(ExprKind::Lambda(name, first, last, info))?
                            }
                        }
                        ExprKind::Pi(name, a, b, info) => {
                            let first = self.pop()?;
                            if (first, last) == (a, b) {
                                id
                            } else {
                                self.append(ExprKind::Pi(name, first, last, info))?
                            }
                        }
                        ExprKind::Let(name, a, b, c, nondep) => {
                            let value = self.pop()?;
                            let ty = self.pop()?;
                            if (ty, value, last) == (a, b, c) {
                                id
                            } else {
                                self.append(ExprKind::Let(name, ty, value, last, nondep))?
                            }
                        }
                        ExprKind::Projection(name, index, a) => {
                            if last == a {
                                id
                            } else {
                                self.append(ExprKind::Projection(name, index, last))?
                            }
                        }
                        _ => return Err(ResourceError::Invariant.into()),
                    };
                    self.remember(id, result)?;
                    self.result(result)?;
                }
            }
        }
        let result = self.pop()?;
        if !self.results.is_empty() {
            return Err(ResourceError::Invariant.into());
        }
        Ok(result)
    }
}
