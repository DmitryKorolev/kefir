//! Resumable ordinary normalization: demanded head exposure is a continuation,
//! never a recursive inference callback or a provisional normal result.
use super::*;
use crate::check::environment::CheckednessMint;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Demand {
    Head {
        root: ExprId,
        incoming: ReductionPath,
    },
    Complete(Normal),
}

pub(crate) struct Machine {
    scratch: Scratch,
    pending: Option<Normal>,
    head: Option<Head>,
    incoming: ReductionPath,
    depth: usize,
    waiting: bool,
    complete: bool,
    failure: Option<HeadError>,
}
const _: () = assert!(size_of::<Machine>() == 72);

impl Machine {
    pub(crate) fn new(
        root: ExprId,
        path: ReductionPath,
        depth: usize,
        b: &mut Budget,
    ) -> Result<Self, HeadError> {
        b.charge_work(2)?;
        let mut machine = Self {
            scratch: Scratch::default(),
            pending: None,
            head: None,
            incoming: path,
            depth,
            waiting: false,
            complete: false,
            failure: None,
        };
        if let Err(error) = machine.scratch.push(Frame::Visit(root, path), b) {
            let cleanup = machine.retire(b).err();
            return Err(select_failure([Some(error.into()), cleanup, None, None])
                .ok_or(ResourceError::Invariant)?);
        }
        Ok(machine)
    }

    /// Caller keeps the exact scope, store origins, cache owner and active locals
    /// fixed while a head is demanded. The child operation may append syntax and
    /// temporarily open locals, but must restore its incoming context on success.
    /// The suspended parent keeps its own opened binders and cache continuations.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn advance<const HEAD_READY: bool>(
        &mut self,
        _scope: &Scope<'_>,
        _environment: &Environment,
        e: &mut Expressions,
        l: &mut Levels,
        n: &Names,
        locals: &mut LocalContext,
        b: &mut Budget,
        mut cache: Option<(&mut cache::Cache, &mut SessionCacheBudget)>,
    ) -> Result<Demand, HeadError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if self.complete || self.waiting {
            self.failure = Some(ResourceError::Invariant.into());
            return Err(ResourceError::Invariant.into());
        }
        self.failure = Some(ResourceError::Invariant.into());
        let scratch = &mut self.scratch;
        let pending = &mut self.pending;
        let result = (|| {
            if let Some(head) = self.head.take() {
                Self::children::<HEAD_READY>(head, self.incoming, scratch, pending, e, l, b)?;
            }
            while let Some(frame) = scratch.pop(b)? {
                b.charge_work(1)?;
                b.observe(crate::resource::Event::MachineSteps, 1);
                match frame {
                    Frame::Visit(root, incoming) | Frame::HeadReady(root, incoming) => {
                        if pending.is_some() {
                            return Err(ResourceError::Invariant.into());
                        }
                        if let Some((table, _)) = cache.as_mut() {
                            #[cfg(debug_assertions)]
                            debug_assert!(
                                e.debug_free_scope(root, l, |id| locals.debug_is_active(id))?,
                                "normalization query contains an inactive free local"
                            );
                            if let Some(normal) = table.get(root.slot(), incoming, e, b)? {
                                *pending = Some(normal);
                                continue;
                            }
                            scratch.push(Frame::CacheFinish(root), b)?;
                        }
                        // HeadReady is derived only from a successfully exposed
                        // neutral application's function edge or a neutral
                        // projection's already exposed source. It runs immediately
                        // in unchanged scope/active locals; never derive it for an
                        // unexposed argument, domain, body, or separate request.
                        if !matches!(frame, Frame::HeadReady(..)) {
                            self.incoming = incoming;
                            self.waiting = true;
                            return Ok(Demand::Head { root, incoming });
                        }
                        let head = Head {
                            expression: root,
                            path: incoming,
                        };
                        Self::children::<HEAD_READY>(head, incoming, scratch, pending, e, l, b)?;
                    }
                    Frame::CacheFinish(source) => {
                        let normal = (*pending).ok_or(ResourceError::Invariant)?;
                        let (table, session) = cache.as_mut().ok_or(ResourceError::Invariant)?;
                        table.insert(source.slot(), normal, session, b)?;
                    }
                    Frame::AppArgument { head, path, height } => {
                        let function = take(pending)?;
                        let ExprKind::App(_, argument) = e.get(head, b)?.kind(e, l, b)? else {
                            return Err(ResourceError::Invariant.into());
                        };
                        scratch.push(
                            Frame::AppFinish {
                                head,
                                height,
                                function,
                            },
                            b,
                        )?;
                        scratch.push(Frame::Visit(argument, path), b)?;
                    }
                    Frame::AppFinish {
                        head,
                        height: head_height,
                        function,
                    } => {
                        let argument = take(pending)?;
                        let ExprKind::App(old_function, old_argument) =
                            e.get(head, b)?.kind(e, l, b)?
                        else {
                            return Err(ResourceError::Invariant.into());
                        };
                        // Normalizing children of a neutral application cannot
                        // expose a new head lambda in the beta/delta/zeta fragment.
                        // If that preservation premise breaks, report an invariant
                        // failure rather than publish a reducible normal form.
                        if matches!(
                            e.get(function.expression, b)?.kind(e, l, b)?,
                            ExprKind::Lambda(..)
                        ) {
                            return Err(ResourceError::Invariant.into());
                        }
                        let expression = if (function.expression, argument.expression)
                            == (old_function, old_argument)
                        {
                            head
                        } else {
                            e.append(
                                ExprKind::App(function.expression, argument.expression),
                                l,
                                n,
                                b,
                            )?
                        };
                        *pending = Some(Normal {
                            expression,
                            height: height(head_height, function.height, argument.height)?,
                        });
                    }
                    Frame::BinderOpen { head, path, height } => {
                        let domain = take(pending)?;
                        let (_, name, original_domain, body, annotation) = binder(head, e, l, b)?;
                        let local = locals.enter_checked(
                            // Certificate authority: the completed pending
                            // inference of the domain establishes the checked
                            // form; the local records the original syntax.
                            CheckedTy::checked(original_domain, CheckednessMint::mint()),
                            None,
                            name,
                            annotation,
                            e,
                            n,
                            b,
                        )?;
                        let free = e.append(ExprKind::Free(local.slot()), l, n, b)?;
                        let opened = e.bind(body, 0, Binding::Instantiate(&[free]), l, n, b)?;
                        scratch.push(
                            Frame::BinderFinish {
                                head,
                                height,
                                domain,
                                local,
                            },
                            b,
                        )?;
                        scratch.push(Frame::Visit(opened, path), b)?;
                    }
                    Frame::ProjectionFinish {
                        head,
                        height: head_height,
                    } => {
                        let source = take(pending)?;
                        let ExprKind::Projection(name, index, old_source) =
                            e.get(head, b)?.kind(e, l, b)?
                        else {
                            return Err(ResourceError::Invariant.into());
                        };
                        // Head exposure has already established a neutral source.
                        // Child normalization preserves that neutral head; this
                        // rebuild introduces no new typing or inequality claim.
                        let expression = if source.expression == old_source {
                            head
                        } else {
                            e.append(
                                ExprKind::Projection(name, index, source.expression),
                                l,
                                n,
                                b,
                            )?
                        };
                        *pending = Some(Normal {
                            expression,
                            height: head_height
                                .checked_add(source.height)
                                .ok_or(ResourceError::Counter)?,
                        });
                    }
                    Frame::BinderFinish {
                        head,
                        height: head_height,
                        domain,
                        local,
                    } => {
                        let body = take(pending)?;
                        let closed = e.bind(
                            body.expression,
                            0,
                            Binding::Abstract(&[local.slot()]),
                            l,
                            n,
                            b,
                        )?;
                        let (lambda, name, old_domain, old_body, annotation) =
                            binder(head, e, l, b)?;
                        let expression = if (domain.expression, closed) == (old_domain, old_body) {
                            head
                        } else {
                            let kind = if lambda {
                                ExprKind::Lambda(name, domain.expression, closed, annotation)
                            } else {
                                ExprKind::Pi(name, domain.expression, closed, annotation)
                            };
                            e.append(kind, l, n, b)?
                        };
                        locals.leave(local, b)?;
                        *pending = Some(Normal {
                            expression,
                            height: height(head_height, domain.height, body.height)?,
                        });
                    }
                }
            }
            if locals.depth() != self.depth {
                return Err(ResourceError::Invariant.into());
            }
            Ok(Demand::Complete(take(pending)?))
        })();
        self.failure = result.as_ref().err().copied();
        self.complete = matches!(result, Ok(Demand::Complete(_)));
        result
    }

    pub(crate) fn resume_head(&mut self, head: Head) -> Result<(), HeadError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if !self.waiting || self.complete || self.head.is_some() {
            self.failure = Some(ResourceError::Invariant.into());
            return Err(ResourceError::Invariant.into());
        }
        self.head = Some(head);
        self.waiting = false;
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn children<const HEAD_READY: bool>(
        head: Head,
        incoming: ReductionPath,
        scratch: &mut Scratch,
        pending: &mut Option<Normal>,
        e: &Expressions,
        l: &Levels,
        b: &mut Budget,
    ) -> Result<(), HeadError> {
        let height = head.path.height_since(incoming)?;
        match e.get(head.expression, b)?.kind(e, l, b)? {
            ExprKind::App(function, _) => {
                scratch.push(
                    Frame::AppArgument {
                        head: head.expression,
                        path: head.path,
                        height,
                    },
                    b,
                )?;
                scratch.push(
                    if HEAD_READY {
                        Frame::HeadReady(function, head.path)
                    } else {
                        Frame::Visit(function, head.path)
                    },
                    b,
                )?;
            }
            ExprKind::Lambda(_, domain, _, _) | ExprKind::Pi(_, domain, _, _) => {
                scratch.push(
                    Frame::BinderOpen {
                        head: head.expression,
                        path: head.path,
                        height,
                    },
                    b,
                )?;
                scratch.push(Frame::Visit(domain, head.path), b)?;
            }
            ExprKind::Projection(_, _, source) => {
                scratch.push(
                    Frame::ProjectionFinish {
                        head: head.expression,
                        height,
                    },
                    b,
                )?;
                scratch.push(
                    if HEAD_READY {
                        Frame::HeadReady(source, head.path)
                    } else {
                        Frame::Visit(source, head.path)
                    },
                    b,
                )?;
            }
            ExprKind::Free(_)
            | ExprKind::Sort(_)
            | ExprKind::Constant(..)
            | ExprKind::Natural(_)
            | ExprKind::String(_) => {
                *pending = Some(Normal {
                    expression: head.expression,
                    height,
                });
            }
            // Head exposure must not return these. In particular
            // an unimplemented reduction cannot certify normality.
            ExprKind::Bound(_) | ExprKind::Let(..) => {
                return Err(ResourceError::Invariant.into());
            }
            // Preserved metadata has no implemented
            // interpretation; its normality is unknown, so exposure
            // declines instead of certifying a normal form.
            ExprKind::MData(..) => return Err(HeadError::Unsupported),
        }

        Ok(())
    }

    /// Abandon only locally unsupported optional work. All cleanup and other
    /// operation failures remain terminal; no completed result is returned.
    pub(crate) fn abandon(mut self, b: &mut Budget) -> Result<(), HeadError> {
        if self.failure == Some(HeadError::Unsupported) {
            self.failure = None;
        }
        self.retire(b)
    }

    pub(crate) fn retire(self, b: &mut Budget) -> Result<(), HeadError> {
        let cleanup = self.scratch.retire(b).err().map(HeadError::from);
        match select_failure([self.failure, cleanup, None, None]) {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
}
