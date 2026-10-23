//! Resumable checked inference for ordinary head/comparison demands. One outer
//! Working failure owner drives the machine; it never recursively calls infer_at.
use super::*;
mod memo;
use crate::check::environment::normalization::Head;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Demand {
    Head(Inferred),
    Comparison {
        left: ExprId,
        right: ExprId,
        incoming: ReductionPath,
    },
    Complete(Inferred),
}
#[derive(Clone, Copy)]
enum Response {
    Head(Head),
    Comparison(ExprId, ReductionPath),
}

pub(super) struct Machine {
    environments: EvaluationEnvironments,
    memo: memo::Memo,
    frames: Vec<Frame>,
    pending: Option<Inferred>,
    current: Option<Frame>,
    request: Option<Demand>,
    response: Option<Response>,
    initial_depth: u32,
    request_depth: u32,
    complete: bool,
    observation: bool,
    failure: Option<Stop>,
    #[cfg(feature = "introspection")]
    failure_view: Option<View>,
}
#[cfg(not(feature = "introspection"))]
const _: () = assert!(size_of::<Machine>() == 192);
#[cfg(feature = "introspection")]
const _: () = assert!(size_of::<Machine>() == 208);

impl Machine {
    pub(super) fn new(
        root: ExprId,
        incoming: ReductionPath,
        depth: usize,
        b: &mut Budget,
    ) -> Result<Self, Stop> {
        b.charge_work(1)?;
        // Active context depth is capped at 65,536. Compact checkpoints keep
        // both build modes within the same charged driver-job layout.
        let depth = u32::try_from(depth).map_err(|_| ResourceError::Invariant)?;
        let mut machine = Self {
            environments: EvaluationEnvironments::new(),
            memo: memo::Memo::default(),
            frames: Vec::new(),
            pending: None,
            current: None,
            request: None,
            response: None,
            initial_depth: depth,
            request_depth: depth,
            complete: false,
            observation: false,
            failure: None,
            #[cfg(feature = "introspection")]
            failure_view: None,
        };
        if let Err(error) = push(
            &mut machine.frames,
            Frame::Root(
                View {
                    expression: root,
                    environment: EnvId::EMPTY,
                },
                incoming,
            ),
            b,
        ) {
            machine.failure = Some(error);
            return Err(machine
                .retire(b, &mut SessionCacheBudget::default())
                .err()
                .ok_or(ResourceError::Invariant)?);
        }
        Ok(machine)
    }

    /// Only a head/comparison-issued request carries the already-checked source premise.
    /// Parents retain its exact context/frontiers until this owner retires. This
    /// mode yields type information, never new checking or cache authority.
    pub(super) fn new_observation(
        request: crate::check::environment::normalization::TypeObservation,
        work: &mut Working<'_>,
    ) -> Result<Self, Stop> {
        let mut machine = Self::new(
            request.root(),
            request.incoming(),
            work.context.depth(),
            work.budget,
        )?;
        machine.observation = true;
        Ok(machine)
    }

    /// The driver holds exact original frontiers, ordinary scope and immutable
    /// environment fixed. A demanded operation restores its incoming context
    /// depth; outer locals and these delayed environments remain alive throughout.
    /// Auxiliary projection helper internals still use their existing synchronous
    /// routes and decline demands outside those routes' implemented permission.
    pub(super) fn advance(
        &mut self,
        work: &mut Working<'_>,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<Demand, Stop> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if self.complete || self.request.is_some() {
            self.failure = Some(ResourceError::Invariant.into());
            return Err(ResourceError::Invariant.into());
        }
        self.failure = Some(ResourceError::Invariant.into());
        let result = (|| loop {
            if self.current.is_none() {
                self.current = self.frames.pop();
                if let Some(frame) = self.current {
                    if matches!(frame, Frame::Visit(..)) {
                        work.budget.observe(Event::Inferences, 1);
                    }
                    work.budget.charge_work(1)?;
                    work.budget.observe(Event::MachineSteps, 1);
                }
            }
            let Some(frame) = self.current else {
                if work.context.depth() != self.initial_depth as usize || self.response.is_some() {
                    return Err(ResourceError::Invariant.into());
                }
                return Ok(Demand::Complete(
                    self.pending.take().ok_or(ResourceError::Invariant)?,
                ));
            };
            #[cfg(feature = "introspection")]
            {
                self.failure_view = frame.diagnostic_view();
            }
            if self.response.is_none() {
                if let Some(request) = self.demand(frame, work)? {
                    self.request = Some(request);
                    self.request_depth = u32::try_from(work.context.depth())
                        .map_err(|_| ResourceError::Invariant)?;
                    return Ok(request);
                }
            } else if work.context.depth() != self.request_depth as usize {
                return Err(ResourceError::Invariant.into());
            }
            self.current = None;
            work.budget.release_frames(1)?;
            let environments = &mut self.environments;
            let frames = &mut self.frames;
            let pending = &mut self.pending;
            let response = &mut self.response;
            match frame {
                Frame::Root(root, incoming) | Frame::Visit(root, incoming) => {
                    if pending.is_some() {
                        return Err(ResourceError::Invariant.into());
                    }
                    let mut kind = work.expressions.get(root.expression, work.budget)?.kind(
                        work.expressions,
                        work.levels,
                        work.budget,
                    )?;
                    if !self.observation
                        && scope.formation.is_none()
                        && scope.mode == crate::check::environment::normalization::Mode::Safe
                        && matches!(
                            kind,
                            ExprKind::App(..)
                                | ExprKind::Constant(..)
                                | ExprKind::Pi(..)
                                | ExprKind::Lambda(..)
                                | ExprKind::Let(..)
                        )
                        && let Some(context) = work.context.cache_identity()
                    {
                        if let Some(result) =
                            self.memo.get(root, context, incoming, environments, work)?
                        {
                            *pending = Some(result);
                            continue;
                        }
                        push(
                            frames,
                            Frame::MemoResult(root, incoming, context),
                            work.budget,
                        )?;
                        kind = work.expressions.get(root.expression, work.budget)?.kind(
                            work.expressions,
                            work.levels,
                            work.budget,
                        )?;
                    }
                    match kind {
                        ExprKind::Sort(_) | ExprKind::Free(_) | ExprKind::Bound(_) => {
                            let atom = work.materialize_view(root, environments)?;
                            *pending = Some(Inferred {
                                ty: work.infer_atom_rule(atom)?,
                                path: incoming,
                            });
                        }
                        ExprKind::Natural(bytes) => {
                            // This typing slice covers imported payloads and their
                            // copies. Test/generated nodes must satisfy the same
                            // actual bound; later arithmetic needs its own exact
                            // pinned numeral-size applicability certificate.
                            if bytes.len() > crate::resource::profile::RECORD_BYTES {
                                crate::decode::primitive_decode::ordinary_session::inference::machine::probe("natural-oversize");
                                return Err(Stop::Unsupported);
                            }
                            let ty = match environment.natural_type(
                                scope.before,
                                scope.formation,
                                scope.expression_end,
                                work.expressions,
                                work.budget,
                            )? {
                                Some(ty) => ty,
                                None => {
                                    // Probe only on actual unavailability: an
                                    // ok_or argument evaluates on Some too.
                                    crate::decode::primitive_decode::ordinary_session::inference::machine::probe(
                                        "natural-type-missing",
                                    );
                                    return Err(Stop::Unsupported);
                                }
                            };
                            *pending = Some(Inferred { ty, path: incoming });
                        }
                        ExprKind::String(bytes) => {
                            if bytes.len() > crate::resource::profile::RECORD_BYTES {
                                crate::decode::primitive_decode::ordinary_session::inference::machine::probe("string-oversize");
                                return Err(Stop::Unsupported);
                            }
                            let ty = match environment.string_type(
                                scope.before,
                                scope.formation,
                                scope.expression_end,
                                work.expressions,
                                work.levels,
                                work.budget,
                            )? {
                                Some(ty) => ty,
                                None => {
                                    // Probe only on actual unavailability: an
                                    // ok_or argument evaluates on Some too.
                                    crate::decode::primitive_decode::ordinary_session::inference::machine::probe(
                                        "string-type-missing",
                                    );
                                    return Err(Stop::Unsupported);
                                }
                            };
                            *pending = Some(Inferred { ty, path: incoming });
                        }
                        ExprKind::Constant(..) => {
                            *pending = Some(Inferred {
                                ty: scope.constant_type(
                                    root.expression,
                                    environment,
                                    work.expressions,
                                    work.levels,
                                    work.names,
                                    work.budget,
                                )?,
                                path: incoming,
                            });
                        }
                        ExprKind::Lambda(name, domain, body, annotation) if self.observation => {
                            let domain = work.materialize_view(root.child(domain), environments)?;
                            let local = work.context.enter_checked(
                                // Certificate authority: the enclosing checked
                                // syntax carries the
                                // domain's checkedness; the
                                // entry binds a fresh machine-local identity.
                                CheckedTy::checked_decode_session(domain, CheckednessMint::mint()),
                                None,
                                name,
                                annotation,
                                work.expressions,
                                work.names,
                                work.budget,
                            )?;
                            let opened =
                                work.open_view(body, root.environment, local, environments)?;
                            push(
                                frames,
                                Frame::LambdaBody {
                                    root,
                                    local,
                                    // Unused by LambdaBody result construction;
                                    // only PiBody consumes a domain sort. This is
                                    // not an observed claim that the domain is Prop.
                                    domain_level: LevelId::ZERO,
                                    domain_path: incoming,
                                },
                                work.budget,
                            )?;
                            push(frames, Frame::Visit(opened, incoming), work.budget)?;
                        }
                        ExprKind::Pi(_, domain, _, _) | ExprKind::Lambda(_, domain, _, _) => {
                            push(frames, Frame::Domain(root, incoming), work.budget)?;
                            push(
                                frames,
                                Frame::Visit(root.child(domain), incoming),
                                work.budget,
                            )?;
                        }
                        ExprKind::App(function, _) => {
                            push(frames, Frame::AppFunction(root, incoming), work.budget)?;
                            push(
                                frames,
                                Frame::Visit(root.child(function), incoming),
                                work.budget,
                            )?;
                        }
                        ExprKind::Projection(_, _, source) => {
                            push(frames, Frame::ProjectionSource(root, incoming), work.budget)?;
                            push(
                                frames,
                                Frame::Visit(root.child(source), incoming),
                                work.budget,
                            )?;
                        }
                        ExprKind::Let(name, ty, value, body, _) if self.observation => {
                            let ty = work.materialize_view(root.child(ty), environments)?;
                            let value = work.materialize_view(root.child(value), environments)?;
                            let local = work.context.enter_checked(
                                // Certificate authority: the enclosing checked
                                // syntax carries the
                                // let type's and value's checkedness
                                // the entry binds fresh identities.
                                CheckedTy::checked_decode_session(ty, CheckednessMint::mint()),
                                Some(CheckedVal::checked_decode_session(
                                    value,
                                    CheckednessMint::mint(),
                                )),
                                name,
                                BinderInfo::Default,
                                work.expressions,
                                work.names,
                                work.budget,
                            )?;
                            let opened =
                                work.open_view(body, root.environment, local, environments)?;
                            push(
                                frames,
                                Frame::LetBody {
                                    local,
                                    value,
                                    premises_path: incoming,
                                },
                                work.budget,
                            )?;
                            push(frames, Frame::Visit(opened, incoming), work.budget)?;
                        }
                        ExprKind::Let(_, ty, _, _, _) => {
                            push(frames, Frame::LetType(root, incoming), work.budget)?;
                            push(frames, Frame::Visit(root.child(ty), incoming), work.budget)?;
                        }
                        // Preserved metadata has no implemented
                        // interpretation; typing a wrapped expression declines
                        // instead of inventing a rule.
                        ExprKind::MData(..) => return Err(Stop::Unsupported),
                    }
                }
                Frame::Domain(root, incoming) => {
                    let _inferred = pending.take().ok_or(ResourceError::Invariant)?;
                    let (domain_level, domain_path) = observed_sort(
                        work,
                        take_head(response)?,
                        self.observation,
                        scope,
                        environment,
                    )?;
                    let (pi, name, domain, body, annotation) =
                        work.binder_fields(root.expression)?;
                    let domain = work.materialize_view(root.child(domain), environments)?;
                    let local = work.context.enter_checked(
                        // Certificate authority: the machine's completed
                        // observation of this domain (pending consumption
                        // above) plus the enclosing checked syntax (
                        // expose_checked) establish the certificate
                        CheckedTy::checked_decode_session(domain, CheckednessMint::mint()),
                        None,
                        name,
                        annotation,
                        work.expressions,
                        work.names,
                        work.budget,
                    )?;
                    let opened = work.open_view(body, root.environment, local, environments)?;
                    push(
                        frames,
                        if pi {
                            Frame::PiBody {
                                root,
                                local,
                                domain_level,
                                domain_path,
                            }
                        } else {
                            Frame::LambdaBody {
                                root,
                                local,
                                domain_level,
                                domain_path,
                            }
                        },
                        work.budget,
                    )?;
                    push(frames, Frame::Visit(opened, incoming), work.budget)?;
                }
                Frame::PiBody {
                    root,
                    local,
                    domain_level,
                    domain_path,
                }
                | Frame::LambdaBody {
                    root,
                    local,
                    domain_level,
                    domain_path,
                } => {
                    let body_type = pending.take().ok_or(ResourceError::Invariant)?;
                    let (pi, name, _, _, annotation) = work.binder_fields(root.expression)?;
                    let (ty, body_path) = if pi {
                        let (codomain_level, path) = observed_sort(
                            work,
                            take_head(response)?,
                            self.observation,
                            scope,
                            environment,
                        )?;
                        let level =
                            work.levels
                                .with_helpers(work.names, work.budget, |helpers| {
                                    helpers.imax(domain_level, codomain_level)
                                })?;
                        (
                            work.expressions.append(
                                ExprKind::Sort(level),
                                work.levels,
                                work.names,
                                work.budget,
                            )?,
                            path,
                        )
                    } else {
                        // Domain already materialized and checked this exact type
                        // before entering local. It is immutable and still active;
                        // rebuilding it here would duplicate syntax and work.
                        let domain = work.context.get(local.slot(), work.budget)?.ty();
                        let closed = if work.expressions.get(body_type.ty, work.budget)?.has_free()
                        {
                            work.expressions.bind(
                                body_type.ty,
                                0,
                                Binding::Abstract(&[local.slot()]),
                                work.levels,
                                work.names,
                                work.budget,
                            )?
                        } else {
                            // No Free can be this active local: abstraction is
                            // exactly identity, with no required replacement check.
                            body_type.ty
                        };
                        (
                            work.expressions.append(
                                ExprKind::Pi(name, domain, closed, annotation),
                                work.levels,
                                work.names,
                                work.budget,
                            )?,
                            body_type.path,
                        )
                    };
                    work.context.leave(local, work.budget)?;
                    *pending = Some(Inferred {
                        ty,
                        path: domain_path.maximum(body_path),
                    });
                }
                Frame::ProjectionSource(root, _incoming) => {
                    let _source = pending.take().ok_or(ResourceError::Invariant)?;
                    let head = take_head(response)?;
                    let root = work.materialize_view(root, environments)?;
                    if self.observation {
                        // The originating checked projection establishes field
                        // legality, including Prop elimination. Observe its type
                        // without repeating those checking premises. The original
                        // telescope and committed metadata still determine the
                        // selected domain and all dependent substitutions.
                        let (telescope, path) = work.projection_telescope(
                            root,
                            head.expression,
                            head.path,
                            scope,
                            environment,
                        )?;
                        // The originating checked projection establishes field
                        // legality, including Prop elimination: this scan is
                        // unrestricted by premise, without claiming the type is
                        // not a proposition.
                        push(
                            frames,
                            Frame::ProjectionScan {
                                root,
                                telescope,
                                next: 0,
                                path,
                                prop: ScanMode::Unrestricted,
                            },
                            work.budget,
                        )?;
                        continue;
                    }
                    push(
                        frames,
                        Frame::ProjectionSort(root, head.expression, head.path),
                        work.budget,
                    )?;
                    // Inferring the exposed source type is a demanded continuation.
                    push(
                        frames,
                        Frame::Visit(
                            View {
                                expression: head.expression,
                                environment: EnvId::EMPTY,
                            },
                            head.path,
                        ),
                        work.budget,
                    )?;
                }
                Frame::ProjectionSort(root, source_type, path) => {
                    let _inferred = pending.take().ok_or(ResourceError::Invariant)?;
                    let (level, sort_path) = observed_sort(
                        work,
                        take_head(response)?,
                        self.observation,
                        scope,
                        environment,
                    )?;
                    let (telescope, path) = work.projection_telescope(
                        root,
                        source_type,
                        path.maximum(sort_path),
                        scope,
                        environment,
                    )?;
                    let prop = match work.levels.get(level, work.budget)?.zero() {
                        // Total decision: a proven
                        // identically-zero sort restricts the scan; a proven
                        // NonZero sort means no proof-field restriction applies.
                        LevelZero::Zero => ScanMode::Restricted,
                        LevelZero::NonZero => ScanMode::Unrestricted,
                    };
                    push(
                        frames,
                        Frame::ProjectionScan {
                            root,
                            telescope,
                            next: 0,
                            path,
                            prop,
                        },
                        work.budget,
                    )?;
                }
                Frame::ProjectionScan {
                    root,
                    telescope,
                    next,
                    path,
                    prop,
                } => {
                    work.projection_scan(
                        root,
                        telescope,
                        next,
                        path,
                        prop,
                        scope,
                        environment,
                        frames,
                        pending,
                    )?;
                }
                Frame::ProjectionGuard {
                    root,
                    body,
                    domain,
                    next,
                    path,
                } => {
                    let _inferred = pending.take().ok_or(ResourceError::Invariant)?;
                    let (level, checked_path) = observed_sort(
                        work,
                        take_head(response)?,
                        self.observation,
                        scope,
                        environment,
                    )?;
                    if work.levels.get(level, work.budget)?.zero() != LevelZero::Zero {
                        return Err(Stop::Judgment(Negative::InvalidProjection));
                    }
                    let path = path.maximum(checked_path);
                    // Selected/earlier indices are strictly below the validated
                    // num_fields (at most u32::MAX), so MAX is not a field index.
                    if next == u32::MAX {
                        *pending = Some(Inferred { ty: domain, path });
                    } else {
                        let telescope = work.projection_substitute(root, body, next)?;
                        push(
                            frames,
                            Frame::ProjectionScan {
                                root,
                                telescope,
                                next: next.checked_add(1).ok_or(ResourceError::Counter)?,
                                path,
                                // The sort decision above proved the source is
                                // identically zero; the continuation scan stays
                                // restricted.
                                prop: ScanMode::Restricted,
                            },
                            work.budget,
                        )?;
                    }
                }
                Frame::AppFunction(root, incoming) => {
                    let _function = pending.take().ok_or(ResourceError::Invariant)?;
                    let head = take_head(response)?;
                    let (domain, codomain) = match work
                        .expressions
                        .get(head.expression, work.budget)?
                        .kind(work.expressions, work.levels, work.budget)?
                    {
                        ExprKind::Pi(_, domain, codomain, _) => (domain, codomain),
                        ExprKind::Sort(_) | ExprKind::Lambda(..) | ExprKind::Free(_) => {
                            return Err(if self.observation {
                                Stop::Unsupported
                            } else {
                                Stop::Judgment(Negative::ExpectedPi)
                            });
                        }
                        _ => return Err(Stop::Unsupported),
                    };
                    let ExprKind::App(_, argument) = work
                        .expressions
                        .get(root.expression, work.budget)?
                        .kind(work.expressions, work.levels, work.budget)?
                    else {
                        return Err(ResourceError::Invariant.into());
                    };
                    if self.observation {
                        let ty = work.instantiate_application_result(
                            codomain,
                            root.child(argument),
                            environments,
                        )?;
                        *pending = Some(Inferred {
                            ty,
                            path: head.path,
                        });
                        continue;
                    }
                    push(
                        frames,
                        Frame::AppArgument {
                            root,
                            domain,
                            codomain,
                            function_path: head.path,
                        },
                        work.budget,
                    )?;
                    push(
                        frames,
                        Frame::Visit(root.child(argument), incoming),
                        work.budget,
                    )?;
                }
                Frame::AppArgument {
                    root,
                    domain: _,
                    codomain,
                    function_path: _,
                } => {
                    let _argument_type = pending.take().ok_or(ResourceError::Invariant)?;
                    let (_, path) = take_comparison(response)?;
                    let ExprKind::App(_, argument) = work
                        .expressions
                        .get(root.expression, work.budget)?
                        .kind(work.expressions, work.levels, work.budget)?
                    else {
                        return Err(ResourceError::Invariant.into());
                    };
                    let ty = work.instantiate_application_result(
                        codomain,
                        root.child(argument),
                        environments,
                    )?;
                    *pending = Some(Inferred { ty, path });
                }
                Frame::LetType(root, incoming) => {
                    let _inferred = pending.take().ok_or(ResourceError::Invariant)?;
                    let (_, type_path) = observed_sort(
                        work,
                        take_head(response)?,
                        self.observation,
                        scope,
                        environment,
                    )?;
                    let (_, _, value, _) = work.let_fields(root.expression)?;
                    push(
                        frames,
                        Frame::LetValue {
                            root,
                            incoming,
                            type_path,
                        },
                        work.budget,
                    )?;
                    push(
                        frames,
                        Frame::Visit(root.child(value), incoming),
                        work.budget,
                    )?;
                }
                Frame::LetValue {
                    root,
                    incoming,
                    type_path: _,
                } => {
                    let _value_type = pending.take().ok_or(ResourceError::Invariant)?;
                    let (name, _, value, body) = work.let_fields(root.expression)?;
                    let (ty, premises_path) = take_comparison(response)?;
                    let value = work.materialize_view(root.child(value), environments)?;

                    let local = work.context.enter_checked(
                        // Certificate authority: the completed let-type
                        // comparison and value-type inference (pending
                        // consumption above) plus the enclosing checked syntax
                        //  establish the certificates
                        CheckedTy::checked_decode_session(ty, CheckednessMint::mint()),
                        Some(CheckedVal::checked_decode_session(
                            value,
                            CheckednessMint::mint(),
                        )),
                        name,
                        BinderInfo::Default,
                        work.expressions,
                        work.names,
                        work.budget,
                    )?;
                    let opened = work.open_view(body, root.environment, local, environments)?;
                    push(
                        frames,
                        Frame::LetBody {
                            local,
                            value,
                            premises_path,
                        },
                        work.budget,
                    )?;
                    push(frames, Frame::Visit(opened, incoming), work.budget)?;
                }
                Frame::MemoResult(view, incoming, context) => {
                    if self.observation
                        || scope.formation.is_some()
                        || work.context.cache_identity() != Some(context)
                    {
                        return Err(ResourceError::Invariant.into());
                    }
                    let result = pending.as_ref().copied().ok_or(ResourceError::Invariant)?;
                    self.memo
                        .insert(view, context, result, incoming, environments, work)?;
                }
                Frame::LetBody {
                    local,
                    value,
                    premises_path,
                } => {
                    let body_type = pending.take().ok_or(ResourceError::Invariant)?;
                    // Two existing charged binding traversals close only this
                    // local and substitute its already checked outer-context
                    // value. No departed local can escape in the result type.
                    let closed = work.expressions.bind(
                        body_type.ty,
                        0,
                        Binding::Abstract(&[local.slot()]),
                        work.levels,
                        work.names,
                        work.budget,
                    )?;
                    let ty = work.expressions.bind(
                        closed,
                        0,
                        Binding::Instantiate(&[value]),
                        work.levels,
                        work.names,
                        work.budget,
                    )?;
                    work.context.leave(local, work.budget)?;
                    *pending = Some(Inferred {
                        ty,
                        path: premises_path.maximum(body_type.path),
                    });
                }
            }
            if response.is_some() {
                return Err(ResourceError::Invariant.into());
            }
        })();
        self.failure = result.as_ref().err().copied();
        self.complete = matches!(result, Ok(Demand::Complete(_)));
        result
    }

    #[cfg(feature = "introspection")]
    pub(super) fn diagnostic_snapshot(
        &self,
        work: &Working<'_>,
    ) -> Option<crate::report::failure_snapshot::Snapshot> {
        use crate::check::diagnostic::Sources;
        use crate::report::failure_snapshot::{Capture, Delayed, Identity, Role, Snapshot};
        let view = self
            .current
            .and_then(Frame::diagnostic_view)
            .or(self.failure_view)?;
        Some(Snapshot::capture(Capture {
            declaration: None,
            rules: &[],
            identities: &[Identity::expression(Role::Root, view.expression)],
            invariant: None,
            delayed: Some(Delayed {
                expression: view.expression,
                environment: view.environment,
                environments: &self.environments,
                locals: work.context,
            }),
            mismatch: None,
            sources: Sources {
                expressions: work.expressions,
                levels: work.levels,
                names: work.names,
                locals: Some(work.context),
            },
        }))
    }

    fn demand(&self, frame: Frame, work: &mut Working<'_>) -> Result<Option<Demand>, Stop> {
        if self.observation
            && matches!(
                frame,
                Frame::AppArgument { .. }
                    | Frame::LetType(..)
                    | Frame::LetValue { .. }
                    | Frame::ProjectionSort(..)
                    | Frame::ProjectionScan {
                        prop: ScanMode::Restricted,
                        ..
                    }
                    | Frame::ProjectionGuard { .. }
            )
        {
            return Err(ResourceError::Invariant.into());
        }
        let head = matches!(
            frame,
            Frame::Domain(..)
                | Frame::AppFunction(..)
                | Frame::LetType(..)
                | Frame::ProjectionSource(..)
                | Frame::ProjectionSort(..)
                | Frame::ProjectionGuard { .. }
        ) || matches!(frame, Frame::PiBody { .. });
        if head {
            return Ok(Some(Demand::Head(
                self.pending.ok_or(ResourceError::Invariant)?,
            )));
        }
        Ok(match frame {
            Frame::AppArgument {
                domain,
                function_path,
                ..
            } => {
                let argument = self.pending.ok_or(ResourceError::Invariant)?;
                Some(Demand::Comparison {
                    left: argument.ty,
                    right: domain,
                    incoming: function_path.maximum(argument.path),
                })
            }
            Frame::LetValue {
                root, type_path, ..
            } => {
                let value = self.pending.ok_or(ResourceError::Invariant)?;
                let (_, ty, _, _) = work.let_fields(root.expression)?;
                let ty = work.materialize_view(root.child(ty), &self.environments)?;
                Some(Demand::Comparison {
                    left: value.ty,
                    right: ty,
                    incoming: type_path.maximum(value.path),
                })
            }
            _ => None,
        })
    }

    pub(super) fn resume_head(&mut self, head: Head) -> Result<(), Stop> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if !matches!(self.request, Some(Demand::Head(_))) || self.response.is_some() {
            self.failure = Some(ResourceError::Invariant.into());
            return Err(ResourceError::Invariant.into());
        }
        self.request = None;
        self.response = Some(Response::Head(head));
        Ok(())
    }
    pub(super) fn resume_comparison(&mut self, path: ReductionPath) -> Result<(), Stop> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        let Some(Demand::Comparison { right, .. }) = self.request else {
            self.failure = Some(ResourceError::Invariant.into());
            return Err(ResourceError::Invariant.into());
        };
        if self.response.is_some() {
            self.failure = Some(ResourceError::Invariant.into());
            return Err(ResourceError::Invariant.into());
        }
        self.request = None;
        self.response = Some(Response::Comparison(right, path));
        Ok(())
    }

    pub(super) fn abandon(
        mut self,
        b: &mut Budget,
        caches: &mut SessionCacheBudget,
    ) -> Result<(), Stop> {
        if self.failure.is_some_and(super::driver::locally_unsupported) {
            self.failure = None;
        }
        self.retire(b, caches)
    }

    pub(super) fn retire(
        self,
        b: &mut Budget,
        caches: &mut SessionCacheBudget,
    ) -> Result<(), Stop> {
        let remaining = self.frames.len() + usize::from(self.current.is_some());
        let bytes = self
            .frames
            .capacity()
            .checked_mul(size_of::<Frame>())
            .ok_or(ResourceError::Counter);
        drop(self.frames);
        let cache_error = self.memo.retire(caches, b).err().map(Stop::Resource);
        let releases = [
            bytes
                .and_then(|bytes| b.release(bytes as u64))
                .err()
                .map(Stop::Resource),
            b.release_frames(remaining).err().map(Stop::Resource),
            self.environments.retire(b).err().map(Stop::Resource),
        ];
        let operation = select_failure([self.failure, cache_error, None, None]);
        match select_failure([operation, releases[0], releases[1], releases[2]]) {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
}

fn take_head(response: &mut Option<Response>) -> Result<Head, Stop> {
    match response.take() {
        Some(Response::Head(head)) => Ok(head),
        _ => Err(ResourceError::Invariant.into()),
    }
}
fn take_comparison(response: &mut Option<Response>) -> Result<(ExprId, ReductionPath), Stop> {
    match response.take() {
        Some(Response::Comparison(ty, path)) => Ok((ty, path)),
        _ => Err(ResourceError::Invariant.into()),
    }
}
pub(super) fn select_failure<const N: usize>(errors: [Option<Stop>; N]) -> Option<Stop> {
    errors
        .into_iter()
        .flatten()
        .find(|error| error.report().outcome == FailureOutcome::InternalError)
        .or_else(|| {
            errors
                .into_iter()
                .flatten()
                .find(|error| !matches!(error, Stop::Judgment(_)))
        })
        .or_else(|| errors.into_iter().flatten().next())
}

/// Observation extracts required type information but cannot create a fresh
/// formation rejection. Missing head support remains an inconclusive failure.
fn observed_sort(
    work: &mut Working<'_>,
    head: Head,
    observation: bool,
    scope: &Scope<'_>,
    environment: &Environment,
) -> Result<(LevelId, ReductionPath), Stop> {
    if !observation {
        return work.sort_level_head(head, scope, environment);
    }
    match work.expressions.get(head.expression, work.budget)?.kind(
        work.expressions,
        work.levels,
        work.budget,
    )? {
        ExprKind::Sort(level) => Ok((level, head.path)),
        _ => {
            crate::decode::primitive_decode::ordinary_session::inference::machine::probe(
                "sort-level-head",
            );
            Err(Stop::Unsupported)
        }
    }
}

/// Ephemeral site-attribution probe (introspection builds only).
#[cfg(feature = "introspection")]
pub(crate) fn probe(site: &'static str) {
    if std::env::var_os("KEFIR_COLIMIT_PROBE").is_some() {
        eprintln!("INFERENCE_UNSUPPORTED site={site}");
    }
}

#[cfg(not(feature = "introspection"))]
pub(crate) fn probe(site: &'static str) {
    let _ = site;
}
