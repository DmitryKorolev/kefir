//! Full traversal/cache and private positive comparison; no declaration checking.
pub(crate) mod cache;
pub(crate) mod comparison;
pub(crate) mod machine;
mod positive;

use super::{Environment, Head, HeadError, Scope, release};
use crate::resource::{Budget, ReductionPath, ResourceError, SessionCacheBudget};
use crate::syntax::expressions::{BinderInfo, ExprId, ExprKind, Expressions, binding::Binding};
use crate::syntax::levels::{Levels, NameId};
use crate::syntax::local_context::{CheckedTy, FreeId, LocalContext};
use crate::syntax::names::Names;
use std::mem::size_of;

/// Completed beta/delta/zeta normal syntax under the checked-input premises.
/// Height is the longest demanded route below the incoming counter, not total
/// rewrites or semantic work. This carries no new typing or conversion judgment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Normal {
    pub expression: ExprId,
    pub height: u32,
}
const _: () = assert!(size_of::<Normal>() == 8);

#[derive(Clone, Copy)]
enum Frame {
    Visit(ExprId, ReductionPath),
    HeadReady(ExprId, ReductionPath),
    CacheFinish(ExprId),
    ProjectionFinish {
        head: ExprId,
        height: u32,
    },
    AppArgument {
        head: ExprId,
        path: ReductionPath,
        height: u32,
    },
    AppFinish {
        head: ExprId,
        height: u32,
        function: Normal,
    },
    BinderOpen {
        head: ExprId,
        path: ReductionPath,
        height: u32,
    },
    BinderFinish {
        head: ExprId,
        height: u32,
        domain: Normal,
        local: FreeId,
    },
}
const _: () = assert!(size_of::<Frame>() <= 24);
#[derive(Default)]
struct Scratch {
    frames: Vec<Frame>,
}
impl Scratch {
    fn push(&mut self, frame: Frame, b: &mut Budget) -> Result<(), ResourceError> {
        let count = self
            .frames
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        b.reserve_frames(1)?;
        if let Err(error) = b.grow_vec(&mut self.frames, count) {
            b.release_frames(1)?;
            return Err(error);
        }
        self.frames.push(frame);
        Ok(())
    }
    fn pop(&mut self, b: &mut Budget) -> Result<Option<Frame>, ResourceError> {
        let frame = self.frames.pop();
        if frame.is_some() {
            b.release_frames(1)?;
        }
        Ok(frame)
    }
    fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let count = self.frames.len();
        let a = release(self.frames, b);
        let c = b.release_frames(count);
        a.and(c)
    }
}
fn take(pending: &mut Option<Normal>) -> Result<Normal, ResourceError> {
    pending.take().ok_or(ResourceError::Invariant)
}
fn height(head: u32, left: u32, right: u32) -> Result<u32, ResourceError> {
    head.checked_add(left.max(right))
        .ok_or(ResourceError::Counter)
}
/// Only copies constant-size binder fields; no borrowed payload outlives syntax
/// mutation and no temporary heap copy is needed to reconstruct a binder.
fn binder(
    head: ExprId,
    e: &Expressions,
    l: &Levels,
    b: &mut Budget,
) -> Result<(bool, NameId, ExprId, ExprId, BinderInfo), ResourceError> {
    match e.get(head, b)?.kind(e, l, b)? {
        ExprKind::Lambda(name, domain, body, annotation) => {
            Ok((true, name, domain, body, annotation))
        }
        ExprKind::Pi(name, domain, body, annotation) => Ok((false, name, domain, body, annotation)),
        _ => Err(ResourceError::Invariant),
    }
}

impl Scope<'_> {
    /// Baseline for the eventual cached differential. Caller supplies checked
    /// syntax, validated locals and fixed original-template environment/scope.
    /// Do not use this as a substitute for checking let annotations or values.
    /// Every requested child inherits the completed head's path. Successful
    /// sibling paths combine by maximum; neither traversal nor binding resets it.
    /// Fresh locals use original checked domains, never their normalized forms.
    ///
    /// Failure leaves any opened locals/generated syntax for whole-declaration
    /// retirement; caller MUST abort that declaration and its caches, not resume.
    /// A panic requires run/ledger discard. Only successful abstraction AND local
    /// leave may publish a completed binder. No partial result survives cleanup.
    #[allow(clippy::too_many_arguments)]
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn normalize_uncached(
        &self,
        root: ExprId,
        path: ReductionPath,
        environment: &Environment,
        e: &mut Expressions,
        l: &mut Levels,
        n: &Names,
        locals: &mut LocalContext,
        b: &mut Budget,
    ) -> Result<Normal, HeadError> {
        self.normalize_traversal::<true>(root, path, environment, e, l, n, locals, b, None)
    }

    #[allow(clippy::too_many_arguments)]
    fn normalize_traversal<const HEAD_READY: bool>(
        &self,
        root: ExprId,
        path: ReductionPath,
        environment: &Environment,
        e: &mut Expressions,
        l: &mut Levels,
        n: &Names,
        locals: &mut LocalContext,
        b: &mut Budget,
        mut cache: Option<(&mut cache::Cache, &mut SessionCacheBudget)>,
    ) -> Result<Normal, HeadError> {
        let mut machine = machine::Machine::new(root, path, locals.depth(), b)?;
        let result = (|| loop {
            let demand = machine.advance::<HEAD_READY>(
                self,
                environment,
                e,
                l,
                n,
                locals,
                b,
                cache
                    .as_mut()
                    .map(|(table, ledger)| (&mut **table, &mut **ledger)),
            )?;
            match demand {
                machine::Demand::Head { root, incoming } => {
                    let head = self.expose(root, incoming, environment, e, l, n, locals, b)?;
                    machine.resume_head(head)?;
                }
                machine::Demand::Complete(normal) => return Ok(normal),
            }
        })();
        let cleanup = machine.retire(b).err();
        match select_failure([result.as_ref().err().copied(), cleanup, None, None]) {
            Some(error) => Err(error),
            None => result,
        }
    }
}

/// Borrowed fixed-origin cache owner. Fields stay private: callers cannot change
/// permissions, replace stores or retire locals while a cache is live. Raw IDs
/// remain unbranded; checkedness and no-origin-forgery remain caller invariants.
pub(crate) struct Session<'a> {
    scope: Scope<'a>,
    environment: &'a Environment,
    expressions: &'a mut Expressions,
    levels: &'a mut Levels,
    names: &'a Names,
    locals: &'a mut LocalContext,
    ledger: &'a mut SessionCacheBudget,
    budget: &'a mut Budget,
    cache: cache::Cache,
    failure: Option<HeadError>,
    poisoned: bool,
}
impl Session<'_> {
    pub(crate) fn normalize(
        &mut self,
        root: ExprId,
        path: ReductionPath,
    ) -> Result<Normal, HeadError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if self.poisoned {
            return Err(ResourceError::Invariant.into());
        }
        // Poison precedes debug assertions and all fallible work; an ignored
        // error or caught panic cannot make the enclosing callback successful.
        self.poisoned = true;
        let result = self.scope.normalize_traversal::<true>(
            root,
            path,
            self.environment,
            self.expressions,
            self.levels,
            self.names,
            self.locals,
            self.budget,
            Some((&mut self.cache, self.ledger)),
        );
        self.poisoned = false;
        if let Err(error) = result {
            self.failure = Some(error);
        }
        result
    }
}
pub(crate) fn select_failure<const N: usize>(errors: [Option<HeadError>; N]) -> Option<HeadError> {
    use super::UseError;
    use crate::resource::failure::FailureOutcome;
    use crate::syntax::expressions::ExpressionError;
    use crate::syntax::levels::ScopeError;
    let internal = |error: &HeadError| match error {
        HeadError::Use(
            UseError::Resource(error)
            | UseError::Scope(ScopeError::Resource(error))
            | UseError::Expression(ExpressionError::Resource(error)),
        ) => error.failure_report().outcome == FailureOutcome::InternalError,
        // Checked stored literal bytes cannot become invalid during rebuilding.
        // Keep this invariant classification even before the outer report adapter.
        HeadError::Use(UseError::Expression(
            ExpressionError::InvalidNatural | ExpressionError::InvalidString,
        )) => true,
        _ => false,
    };
    errors
        .into_iter()
        .flatten()
        .find(internal)
        .or_else(|| errors.into_iter().flatten().next())
}

impl Scope<'_> {
    /// One ordinary declaration/permission class, with a ledger shared by all
    /// its optional tables. The callback may normalize checked roots only. It
    /// must not export generated handles beyond the declaration's working region
    /// or install generated templates. This method retires the table before
    /// releasing syntax/context borrows, on success or ordinary failure. Panic
    /// unwinding requires whole-run/ledger discard; no session may be resumed.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn with_cache<T>(
        self,
        environment: &Environment,
        expressions: &mut Expressions,
        levels: &mut Levels,
        names: &Names,
        locals: &mut LocalContext,
        ledger: &mut SessionCacheBudget,
        budget: &mut Budget,
        work: impl FnOnce(&mut Session<'_>) -> Result<T, HeadError>,
    ) -> Result<T, HeadError> {
        self.validate_formation(environment)?;
        budget.charge_work(1)?;
        let mut session = Session {
            scope: self,
            environment,
            expressions,
            levels,
            names,
            locals,
            ledger,
            budget,
            cache: cache::Cache::default(),
            failure: None,
            poisoned: false,
        };
        let result = work(&mut session);
        let cleanup = session.cache.retire(session.ledger, session.budget);
        // Retain every observed cause until selection. An internal failure must
        // never be downgraded by an earlier decline. Equal-severity ties use
        // callback, operation, panic poison, cleanup order, not claimed chronology.
        let errors = [
            result.as_ref().err().copied(),
            session.failure,
            session.poisoned.then(|| ResourceError::Invariant.into()),
            cleanup.err().map(HeadError::from),
        ];
        match select_failure(errors) {
            Some(error) => Err(error),
            None => result,
        }
    }
}
