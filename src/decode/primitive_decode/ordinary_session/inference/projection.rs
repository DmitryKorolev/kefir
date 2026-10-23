//! Projection typing. Original constructor telescopes, no field-plan cache.
use super::*;
mod absence;
use crate::syntax::levels::LevelNames;
use absence::Absence;

fn invalid() -> Stop {
    Stop::Judgment(Negative::InvalidProjection)
}
impl Working<'_> {
    fn projection_fields(&mut self, root: ExprId) -> Result<(NameId, u32, ExprId), Stop> {
        match self.expressions.get(root, self.budget)?.kind(
            self.expressions,
            self.levels,
            self.budget,
        )? {
            ExprKind::Projection(name, index, source) => Ok((name, index, source)),
            _ => Err(ResourceError::Invariant.into()),
        }
    }
    pub(super) fn projection_telescope(
        &mut self,
        root: ExprId,
        source_type: ExprId,
        mut path: ReductionPath,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<(ExprId, ReductionPath), Stop> {
        let (written, index, _) = self.projection_fields(root)?;
        self.budget.charge_work(2)?; // prepay the two flat scratch releases
        let mut arguments = Vec::new();
        let mut universes = Vec::new();
        let result = (|| {
            let mut head = source_type;
            let (constructor, params) = loop {
                match self.expressions.get(head, self.budget)?.kind(
                    self.expressions,
                    self.levels,
                    self.budget,
                )? {
                    ExprKind::App(f, a) => {
                        self.budget.charge_work(1)?;
                        let needed = arguments
                            .len()
                            .checked_add(1)
                            .ok_or(ResourceError::Counter)?;
                        self.budget.grow_vec(&mut arguments, needed)?;
                        arguments.push(a);
                        head = f;
                    }
                    ExprKind::Constant(name, levels) => {
                        if self.names.summary(name, self.budget)?.canonical
                            != self.names.summary(written, self.budget)?.canonical
                        {
                            return Err(invalid());
                        }
                        if scope.formation.is_some()
                            && environment
                                .lookup(name, environment.len(), self.names, self.budget)?
                                .is_none()
                        {
                            return Err(Stop::Unsupported);
                        }
                        let view = environment
                            .inductive(
                                name,
                                scope.before.min(environment.len()),
                                self.names,
                                self.budget,
                            )?
                            .ok_or_else(invalid)?;
                        let [constructor] = view.constructors else {
                            return Err(invalid());
                        };
                        let count = view
                            .num_params
                            .checked_add(view.num_indices)
                            .ok_or(ResourceError::Counter)?;
                        if arguments.len() != count as usize || index >= constructor.num_fields {
                            return Err(invalid());
                        }
                        // Source-type inference checked exact universe arity/scope. The
                        // validated block establishes identical constructor parameters.
                        self.budget.charge_work(levels.len() as u64 + 1)?;
                        self.budget.grow_vec(&mut universes, levels.len())?;
                        universes.extend_from_slice(levels);
                        let constructor = self.expressions.append(
                            ExprKind::Constant(constructor.constructor, &universes),
                            self.levels,
                            self.names,
                            self.budget,
                        )?;
                        break (constructor, view.num_params);
                    }
                    _ => return Err(invalid()),
                }
            };
            let mut telescope = scope.constant_type(
                constructor,
                environment,
                self.expressions,
                self.levels,
                self.names,
                self.budget,
            )?;
            for parameter in 0..params as usize {
                let exposed = self.expose_type_auxiliary(
                    Inferred {
                        ty: telescope,
                        path,
                    },
                    scope,
                    environment,
                )?;
                path = exposed.path;
                let ExprKind::Pi(_, _, body, _) = self
                    .expressions
                    .get(exposed.expression, self.budget)?
                    .kind(self.expressions, self.levels, self.budget)?
                else {
                    return Err(invalid());
                };
                let argument = arguments[arguments.len() - 1 - parameter];
                telescope = self.expressions.bind(
                    body,
                    0,
                    Binding::Instantiate(&[argument]),
                    self.levels,
                    self.names,
                    self.budget,
                )?;
            }
            Ok((telescope, path))
        })();
        let bytes = arguments
            .capacity()
            .checked_mul(size_of::<ExprId>())
            .ok_or(ResourceError::Counter)?;
        let universe_bytes = universes
            .capacity()
            .checked_mul(size_of::<LevelId>())
            .ok_or(ResourceError::Counter)?;
        drop(arguments);
        drop(universes);
        let a = self.budget.release(bytes as u64);
        let b = self.budget.release(universe_bytes as u64);
        a?;
        b?;
        result
    }
    pub(super) fn projection_substitute(
        &mut self,
        root: ExprId,
        body: ExprId,
        index: u32,
    ) -> Result<ExprId, Stop> {
        let (name, _, source) = self.projection_fields(root)?;
        let projection = self.expressions.append(
            ExprKind::Projection(name, index, source),
            self.levels,
            self.names,
            self.budget,
        )?;
        Ok(self.expressions.bind(
            body,
            0,
            Binding::Instantiate(&[projection]),
            self.levels,
            self.names,
            self.budget,
        )?)
    }
    #[allow(clippy::too_many_arguments)]
    pub(super) fn projection_scan(
        &mut self,
        root: ExprId,
        telescope: ExprId,
        next: u32,
        path: ReductionPath,
        prop: ScanMode,
        scope: &Scope<'_>,
        environment: &Environment,
        frames: &mut Vec<Frame>,
        pending: &mut Option<Inferred>,
    ) -> Result<(), Stop> {
        let (_, selected, _) = self.projection_fields(root)?;
        let exposed = self.expose_type_auxiliary(
            Inferred {
                ty: telescope,
                path,
            },
            scope,
            environment,
        )?;
        let path = exposed.path;
        let ExprKind::Pi(_, domain, body, _) = self
            .expressions
            .get(exposed.expression, self.budget)?
            .kind(self.expressions, self.levels, self.budget)?
        else {
            return Err(invalid());
        };
        let needed = next != selected && self.projection_occurs(body)?;
        if prop == ScanMode::Restricted && (next == selected || needed) {
            push(
                frames,
                Frame::ProjectionGuard {
                    root,
                    body,
                    domain,
                    next: if next == selected { u32::MAX } else { next },
                    path,
                },
                self.budget,
            )?;
            push(
                frames,
                Frame::Visit(
                    View {
                        expression: domain,
                        environment: EnvId::EMPTY,
                    },
                    path,
                ),
                self.budget,
            )?;
        } else if next == selected {
            *pending = Some(Inferred { ty: domain, path });
        } else {
            let telescope = if needed {
                self.projection_substitute(root, body, next)?
            } else {
                // Raw absence was proved above; Lower adjusts outer indices and
                // cannot erase a demanded field occurrence through normalization.
                self.expressions.bind(
                    body,
                    0,
                    Binding::Lower(1),
                    self.levels,
                    self.names,
                    self.budget,
                )?
            };
            push(
                frames,
                Frame::ProjectionScan {
                    root,
                    telescope,
                    next: next.checked_add(1).ok_or(ResourceError::Counter)?,
                    path,
                    prop,
                },
                self.budget,
            )?;
        }
        Ok(())
    }
    /// Syntactic occurrence of the just-opened field in the raw remaining body.
    /// Exact (node, depth) stack entries; shared syntax at different depths is not merged.
    fn projection_occurs(&mut self, body: ExprId) -> Result<bool, Stop> {
        #[derive(Clone, Copy)]
        enum Occurrence {
            Visit(ExprId, u32),
            Finish(ExprId, u32),
        }
        const _: () = assert!(size_of::<Occurrence>() == 12);

        fn add(
            work: &mut Working<'_>,
            stack: &mut Vec<Occurrence>,
            id: ExprId,
            depth: u32,
        ) -> Result<(), Stop> {
            let needed = stack.len().checked_add(1).ok_or(ResourceError::Counter)?;
            work.budget.reserve_frames(1)?;
            if let Err(e) = work.budget.grow_vec(stack, needed) {
                work.budget.release_frames(1)?;
                return Err(e.into());
            }
            stack.push(Occurrence::Visit(id, depth));
            Ok(())
        }
        self.budget.charge_work(3)?; // prepay stack, memo and frame retirement
        let mut stack = Vec::new();
        let mut absence = Absence::default();
        let result = (|| {
            add(self, &mut stack, body, 0)?;
            while let Some(frame) = stack.pop() {
                self.budget.release_frames(1)?;
                self.budget.charge_work(1)?;
                let (id, depth) = match frame {
                    Occurrence::Finish(id, depth) => {
                        // Reached only after every child completed false. An error
                        // or positive child exits before this parent can be inserted.
                        absence.insert(id, depth, self.budget)?;
                        continue;
                    }
                    Occurrence::Visit(id, depth) => (id, depth),
                };
                if self.expressions.get(id, self.budget)?.loose_range() <= depth
                    || absence.contains(id, depth, self.budget)?
                {
                    continue;
                }
                add(self, &mut stack, id, depth)?;
                *stack.last_mut().ok_or(ResourceError::Invariant)? = Occurrence::Finish(id, depth);
                match self.expressions.get(id, self.budget)?.kind(
                    self.expressions,
                    self.levels,
                    self.budget,
                )? {
                    ExprKind::Bound(index) if index == depth => return Ok(true),
                    ExprKind::App(a, b) => {
                        add(self, &mut stack, b, depth)?;
                        add(self, &mut stack, a, depth)?;
                    }
                    ExprKind::Pi(_, a, b, _) | ExprKind::Lambda(_, a, b, _) => {
                        add(
                            self,
                            &mut stack,
                            b,
                            depth.checked_add(1).ok_or(ResourceError::Counter)?,
                        )?;
                        add(self, &mut stack, a, depth)?;
                    }
                    ExprKind::Let(_, a, b, c, _) => {
                        add(
                            self,
                            &mut stack,
                            c,
                            depth.checked_add(1).ok_or(ResourceError::Counter)?,
                        )?;
                        add(self, &mut stack, b, depth)?;
                        add(self, &mut stack, a, depth)?;
                    }
                    ExprKind::Projection(_, _, source) => add(self, &mut stack, source, depth)?,
                    _ => (),
                }
            }
            Ok(false)
        })();
        let remaining = stack.len();
        let bytes = stack
            .capacity()
            .checked_mul(size_of::<Occurrence>())
            .ok_or(ResourceError::Counter)?;
        drop(stack);
        let frames = self.budget.release_frames(remaining);
        let storage = self.budget.release(bytes as u64);
        let memo = absence.retire(self.budget);
        frames?;
        storage?;
        memo?;
        result
    }
}
