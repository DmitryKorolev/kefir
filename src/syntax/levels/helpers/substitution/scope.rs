//! Universe-scope boundary, separate from U and proof judgments.
use super::*;
use crate::syntax::expressions::{ExprId, ExprKind, Expressions};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ScopeError {
    Resource(ResourceError),
    DuplicateParameter(NameId),
    UnknownParameter(NameId),
    OpenExpression(ExprId),
}
impl From<ResourceError> for ScopeError {
    fn from(error: ResourceError) -> Self {
        Self::Resource(error)
    }
}

impl Levels {
    /// Check exact-name uniqueness and coverage of all supplied level roots.
    /// Names/levels belong to the same immutable run; no binder/local context is
    /// involved. Unused declared parameters are permitted. This does not check
    /// expression closedness, infer types, compare universes or publish a verdict.
    ///
    /// The parameter map and discovered-source set last only this call. A set
    /// entry means a node's obligations are scheduled, NOT that its scope passed.
    /// Every scheduled node must finish before success; failures return no scope
    /// fact. No result crosses parameter scopes, declarations, threads or stores.
    /// Duplicate/unknown findings must follow the caller's verdict policy (the
    /// positive-only first slice declines); exhaustion is never a scope negative.
    pub(crate) fn check_scope(
        &self,
        names: &impl LevelNames,
        parameters: &[NameId],
        roots: &[LevelId],
        b: &mut Budget,
    ) -> Result<(), ScopeError> {
        run_scope(self, names, parameters, b, |scope| {
            for &root in roots {
                scope.root(root)?;
            }
            Ok(())
        })
    }
}

// Internal callbacks must propagate every failed root immediately. Scope is
// never exposed to semantic callers and is destroyed before returning a result.
struct Scope<'a, N> {
    levels: &'a Levels,
    names: &'a N,
    b: &'a mut Budget,
    declared: Map,
    discovered: Map,
    pending: Vec<LevelId>,
}
fn run_scope<N: LevelNames>(
    levels: &Levels,
    names: &N,
    parameters: &[NameId],
    b: &mut Budget,
    body: impl FnOnce(&mut Scope<'_, N>) -> Result<(), ScopeError>,
) -> Result<(), ScopeError> {
    b.charge_work(4)?;
    let mut scope = Scope {
        levels,
        names,
        b,
        declared: Map::default(),
        discovered: Map::default(),
        pending: Vec::new(),
    };
    let result = (|| {
        for &name in parameters {
            scope.b.charge_work(1)?;
            let canonical = names.summary(name, scope.b)?.canonical;
            if scope.declared.get(canonical, scope.b)?.is_some() {
                return Err(ScopeError::DuplicateParameter(name));
            }
            scope.declared.insert(canonical, 0, scope.b)?;
        }
        body(&mut scope)
    })();
    let frames = scope.b.release_frames(scope.pending.len());
    let worklist = release_vec(scope.pending, scope.b);
    let params = release_vec(scope.declared.entries, scope.b);
    let seen = release_vec(scope.discovered.entries, scope.b);
    frames?;
    worklist?;
    params?;
    seen?;
    result
}
impl<N: LevelNames> Scope<'_, N> {
    fn root(&mut self, root: LevelId) -> Result<(), ScopeError> {
        schedule(
            self.levels,
            root,
            &mut self.discovered,
            &mut self.pending,
            self.b,
        )?;
        while let Some(id) = self.pending.pop() {
            self.b.release_frames(1)?;
            self.b.charge_work(1)?;
            self.b.observe(crate::resource::Event::MachineSteps, 1);
            match self.levels.get(id, self.b)?.kind() {
                LevelKind::Param(name) => {
                    if self
                        .declared
                        .get(self.names.summary(name, self.b)?.canonical, self.b)?
                        .is_none()
                    {
                        return Err(ScopeError::UnknownParameter(name));
                    }
                }
                LevelKind::Succ(child) => schedule(
                    self.levels,
                    child,
                    &mut self.discovered,
                    &mut self.pending,
                    self.b,
                )?,
                LevelKind::Max(a, c) | LevelKind::IMax(a, c) => {
                    schedule(
                        self.levels,
                        a,
                        &mut self.discovered,
                        &mut self.pending,
                        self.b,
                    )?;
                    schedule(
                        self.levels,
                        c,
                        &mut self.discovered,
                        &mut self.pending,
                        self.b,
                    )?;
                }
                LevelKind::Zero => {}
            }
        }
        Ok(())
    }
}

impl Expressions {
    /// Declaration-root coverage and closedness only, not inference. Immutable
    /// construction-derived loose/free summaries justify the O(1) root checks:
    /// loose_range == 0 iff no bound index escapes the root's binders; has_free
    /// is false iff no free local occurs. nonDep never suppresses these summaries.
    /// Every name/level/expression originates in this run. No metadata node exists
    /// yet; future metadata constructors must preserve these summary invariants.
    /// A declaration can install nothing until its other semantic checks finish.
    pub(crate) fn check_scope(
        &self,
        levels: &Levels,
        names: &impl LevelNames,
        parameters: &[NameId],
        roots: &[ExprId],
        b: &mut Budget,
    ) -> Result<(), ScopeError> {
        run_scope(levels, names, parameters, b, |scope| {
            scope.b.charge_work(3)?; // entry and two allocation releases
            let mut discovered = Map::default();
            let mut pending = Vec::new();
            let result = (|| {
                for &root in roots {
                    scope.b.charge_work(1)?;
                    let node = self.get(root, scope.b)?;
                    if node.loose_range() != 0 || node.has_free() {
                        return Err(ScopeError::OpenExpression(root));
                    }
                    schedule_expression(self, root, &mut discovered, &mut pending, scope.b)?;
                    while let Some(id) = pending.pop() {
                        scope.b.release_frames(1)?;
                        scope.b.charge_work(1)?;
                        scope.b.observe(crate::resource::Event::MachineSteps, 1);
                        match self.get(id, scope.b)?.kind(self, levels, scope.b)? {
                            ExprKind::Sort(level) => scope.root(level)?,
                            ExprKind::Constant(_, args) => {
                                // Stream borrowed arguments; never copy a declaration's
                                // level lists into a second temporary root vector.
                                for &arg in args {
                                    scope.root(arg)?;
                                }
                            }
                            ExprKind::App(a, c)
                            | ExprKind::Lambda(_, a, c, _)
                            | ExprKind::Pi(_, a, c, _) => {
                                schedule_expression(
                                    self,
                                    a,
                                    &mut discovered,
                                    &mut pending,
                                    scope.b,
                                )?;
                                schedule_expression(
                                    self,
                                    c,
                                    &mut discovered,
                                    &mut pending,
                                    scope.b,
                                )?;
                            }
                            ExprKind::Let(_, ty, value, body, _) => {
                                for child in [ty, value, body] {
                                    schedule_expression(
                                        self,
                                        child,
                                        &mut discovered,
                                        &mut pending,
                                        scope.b,
                                    )?;
                                }
                            }
                            ExprKind::Projection(_, _, target) => schedule_expression(
                                self,
                                target,
                                &mut discovered,
                                &mut pending,
                                scope.b,
                            )?,
                            ExprKind::MData(_, wrapped) => schedule_expression(
                                self,
                                wrapped,
                                &mut discovered,
                                &mut pending,
                                scope.b,
                            )?,
                            ExprKind::Bound(_)
                            | ExprKind::Free(_)
                            | ExprKind::Natural(_)
                            | ExprKind::String(_) => {}
                        }
                    }
                }
                Ok(())
            })();
            let frames = scope.b.release_frames(pending.len());
            let worklist = release_vec(pending, scope.b);
            let seen = release_vec(discovered.entries, scope.b);
            frames?;
            worklist?;
            seen?;
            result
        })
    }
}
fn schedule_expression(
    e: &Expressions,
    id: ExprId,
    discovered: &mut Map,
    pending: &mut Vec<ExprId>,
    b: &mut Budget,
) -> Result<(), ResourceError> {
    b.charge_work(1)?;
    // Discovery has the same scheduled-only meaning as the level set. Coverage
    // depends only on parameters, not binder depth; closedness is checked at each
    // root even if that expression was discovered earlier under a binder.
    if !e.get(id, b)?.has_param() || discovered.get(id.slot(), b)?.is_some() {
        return Ok(());
    }
    discovered.insert(id.slot(), 0, b)?;
    b.reserve_frames(1)?;
    if let Err(error) = b.grow_vec(pending, pending.len() + 1) {
        b.release_frames(1)?;
        return Err(error);
    }
    pending.push(id);
    Ok(())
}

fn schedule(
    levels: &Levels,
    id: LevelId,
    discovered: &mut Map,
    pending: &mut Vec<LevelId>,
    b: &mut Budget,
) -> Result<(), ResourceError> {
    b.charge_work(1)?;
    if !levels.get(id, b)?.has_param() || discovered.get(id.slot(), b)?.is_some() {
        return Ok(());
    }
    // A failed insertion/reservation aborts the entire call; it cannot be reused
    // as a completed query. Flat handles avoid occurrence-tree expansion.
    discovered.insert(id.slot(), 0, b)?;
    b.reserve_frames(1)?;
    if let Err(error) = b.grow_vec(pending, pending.len() + 1) {
        b.release_frames(1)?;
        return Err(error);
    }
    pending.push(id);
    Ok(())
}
