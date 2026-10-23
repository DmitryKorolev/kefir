//! Checked inference: atoms, constants, Pi, lambda, application and let.
//! Scope and validated environment/context are premises; no proof verdict exists.
use super::*;
use crate::check::delayed::environment::{BindingId, EnvId, Environment as EvaluationEnvironments};
use crate::resource::{Event, ReductionPath};
use crate::syntax::expressions::{BinderInfo, binding::Binding};
use crate::syntax::levels::LevelZero;
use crate::syntax::local_context::{CheckedTy, CheckedVal, FreeId};
use std::mem::size_of;

/// Zero-sized trusted-construction authority for checkedness
/// certificates minted by the ordinary-session inference machine: the
/// enclosing checked syntax carries the binder
/// type's and value's checkedness. The field is private and
/// the mint is module-private, so only code inside
/// `crate::decode::primitive_decode::ordinary_session::inference` — including
/// its descendant modules — can construct it; out-of-region minting is a
/// compile error. The exhaustive production mint list is
/// `scripts/check_checked_mint_sites.py`.
pub(crate) struct CheckednessMint(());
impl CheckednessMint {
    fn mint() -> Self {
        Self(())
    }
}

mod driver;
mod machine;
mod projection;
mod sort;

/// Whether a projection-scan step must apply the no-data-out-of-proof
/// restriction. `Restricted` is established either by a completed
/// identically-zero decision on the scanned type's sort or by the originating
/// checked projection's own field-legality premise; `Unrestricted` never
/// claims the type is not a proposition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ScanMode {
    Restricted,
    Unrestricted,
}

/// Original syntax with a session-owned lexical substitution. No generated
/// handle or local outlives its ordinary-session owner. Inferred types are
/// materialized at the existing closing boundary in this first slice.
#[derive(Clone, Copy)]
struct View {
    expression: ExprId,
    environment: EnvId,
}
impl View {
    fn child(self, expression: ExprId) -> Self {
        Self { expression, ..self }
    }
}
const _: () = assert!(size_of::<View>() == 8);

impl From<ResourceError> for Stop {
    fn from(error: ResourceError) -> Self {
        Self::Resource(error)
    }
}
impl From<ExpressionError> for Stop {
    fn from(error: ExpressionError) -> Self {
        Self::Expression(error)
    }
}
impl From<HeadError> for Stop {
    fn from(error: HeadError) -> Self {
        Self::Inference(error)
    }
}

/// Type and maximum completed route of one checked judgment. Valid only in the
/// originating declaration/context; never install this generated handle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Inferred {
    pub ty: ExprId,
    pub path: ReductionPath,
}
const _: () = assert!(size_of::<Inferred>() == 8);

#[derive(Clone, Copy)]
enum Frame {
    Root(View, ReductionPath),
    Visit(View, ReductionPath),
    MemoResult(View, ReductionPath, u32),
    Domain(View, ReductionPath),
    PiBody {
        root: View,
        local: FreeId,
        domain_level: LevelId,
        domain_path: ReductionPath,
    },
    LambdaBody {
        root: View,
        local: FreeId,
        domain_level: LevelId,
        domain_path: ReductionPath,
    },
    AppFunction(View, ReductionPath),
    AppArgument {
        root: View,
        domain: ExprId,
        codomain: ExprId,
        function_path: ReductionPath,
    },
    ProjectionSource(View, ReductionPath),
    ProjectionSort(ExprId, ExprId, ReductionPath),
    ProjectionScan {
        root: ExprId,
        telescope: ExprId,
        next: u32,
        path: ReductionPath,
        prop: ScanMode,
    },
    ProjectionGuard {
        root: ExprId,
        body: ExprId,
        domain: ExprId,
        next: u32,
        path: ReductionPath,
    },
    LetType(View, ReductionPath),
    LetValue {
        root: View,
        incoming: ReductionPath,
        type_path: ReductionPath,
    },
    LetBody {
        local: FreeId,
        value: ExprId,
        premises_path: ReductionPath,
    },
}
const _: () = assert!(size_of::<Frame>() == 24);

#[cfg(feature = "introspection")]
impl Frame {
    fn diagnostic_view(self) -> Option<View> {
        match self {
            Self::Root(view, _)
            | Self::Visit(view, _)
            | Self::MemoResult(view, _, _)
            | Self::Domain(view, _)
            | Self::AppFunction(view, _)
            | Self::ProjectionSource(view, _)
            | Self::LetType(view, _)
            | Self::PiBody { root: view, .. }
            | Self::LambdaBody { root: view, .. }
            | Self::AppArgument { root: view, .. }
            | Self::LetValue { root: view, .. } => Some(view),
            Self::ProjectionSort(root, _, _)
            | Self::ProjectionScan { root, .. }
            | Self::ProjectionGuard { root, .. } => Some(View {
                expression: root,
                environment: EnvId::EMPTY,
            }),
            Self::LetBody { .. } => None,
        }
    }
}

#[inline(always)] // Preserve frame-payload specialization at the inference continuation.
fn push(frames: &mut Vec<Frame>, frame: Frame, budget: &mut Budget) -> Result<(), Stop> {
    let count = frames.len().checked_add(1).ok_or(ResourceError::Counter)?;
    budget.reserve_frames(1)?;
    if let Err(error) = budget.grow_vec(frames, count) {
        budget.release_frames(1)?;
        return Err(error.into());
    }
    frames.push(frame);
    Ok(())
}

impl Working<'_> {
    /// Caller established universe scope and absence of loose variables. Active
    /// locals and installed templates are checked premises. Completed scoped checked-inference entries may replay their
    /// derivation; observation and incomplete routes supply no checking evidence.
    pub(crate) fn infer_at(
        &mut self,
        root: ExprId,
        incoming: ReductionPath,
        scope: Scope<'_>,
        environment: &Environment,
    ) -> Result<Inferred, Stop> {
        self.budget.observe(Event::Inferences, 1);
        if let Some(error) = self.owned_failure {
            return Err(error);
        }
        self.owned_failure = Some(Stop::Resource(ResourceError::Invariant));
        let result = self.infer_machine(root, incoming, &scope, environment);
        self.owned_failure = result.as_ref().err().copied();
        result
    }

    /// Existing checked-substitution callers establish root universe/loose-variable
    /// scope before entering this consumer. A completed formation query owns no
    /// syntax certificate: only its Sort level escapes until session retirement.
    /// Its independent engine bound does not reset the incoming ordinary path.
    fn checked_sort(
        &mut self,
        root: ExprId,
        incoming: ReductionPath,
        scope: Scope<'_>,
        environment: &Environment,
    ) -> Result<(LevelId, ReductionPath, ExprId), Stop> {
        if let Some(error) = self.owned_cleanup {
            return Err(error.into());
        }
        if let Some(error) = self.owned_failure {
            return Err(error);
        }
        if let Some(level) = self.try_formation_sort(root, scope, environment)? {
            // No materialized inferred type exists on this positive route.
            return Ok((level, incoming, root));
        }
        let inferred = self.infer_at(root, incoming, scope, environment)?;
        self.owned_failure = Some(Stop::Resource(ResourceError::Invariant));
        let result = self
            .sort_level(inferred, &scope, environment)
            .map(|(level, path)| (level, path, inferred.ty));
        self.owned_failure = result.as_ref().err().copied();
        result
    }

    /// Positive query only: each caller retains its own exact ordinary fallback,
    /// including its existing negative classification and reduction-path rules.
    pub(crate) fn try_formation_sort(
        &mut self,
        root: ExprId,
        scope: Scope<'_>,
        environment: &Environment,
    ) -> Result<Option<LevelId>, Stop> {
        if let Some(error) = self.owned_cleanup {
            return Err(error.into());
        }
        if let Some(error) = self.owned_failure {
            return Err(error);
        }
        // Staged formation, or the inductive pre-staging pass's
        // explicit authority against the committed environment. Every other
        // formation-free consumer keeps the ordinary route.
        let pre_staging = scope.formation.is_none() && self.pre_staging_sorts();
        if scope.formation.is_none() && !pre_staging {
            return Ok(None);
        }
        self.owned_failure = Some(Stop::Resource(ResourceError::Invariant));
        let result = (|| {
            self.check_formation_origin(scope)?;
            crate::check::environment::kernel::formation_sort(
                environment,
                root,
                &scope,
                pre_staging,
                self.context,
                self.names,
                self.expressions,
                self.levels,
                self.budget,
            )
            .map_err(Stop::Inference)
        })();
        self.owned_failure = result.as_ref().err().copied();
        if result.as_ref().is_ok_and(Option::is_some) {
            self.budget.observe(Event::Inferences, 1);
        }
        result
    }

    fn check_formation_origin(&self, scope: Scope<'_>) -> Result<(), Stop> {
        if scope.expression_end != self.original_expressions
            || scope.level_end != self.original_levels
        {
            return Err(ResourceError::Invariant.into());
        }
        Ok(())
    }

    /// Independent checked expected type and typed rule judgment. A refusal
    /// supplies no verdict; the caller must run its unchanged ordinary check.
    /// Context/source/phase are immutable until this query and all cleanup end.
    pub(crate) fn check_formation_rule(
        &mut self,
        root: ExprId,
        expected: ExprId,
        scope: Scope<'_>,
        environment: &Environment,
    ) -> Result<bool, Stop> {
        if let Some(error) = self.owned_cleanup {
            return Err(error.into());
        }
        if let Some(error) = self.owned_failure {
            return Err(error);
        }
        self.owned_failure = Some(Stop::Resource(ResourceError::Invariant));
        let result = (|| {
            self.check_formation_origin(scope)?;
            crate::check::environment::kernel::formation_check(
                environment,
                root,
                expected,
                &scope,
                self.context,
                self.names,
                self.expressions,
                self.levels,
                self.budget,
            )
            .map_err(Stop::Inference)
        })();
        self.owned_failure = result.as_ref().err().copied();
        result
    }

    /// Establish type formation, including the demanded inferred-type exposure.
    /// Used at declaration roots; errors remain owned even if a caller ignores one.
    pub(crate) fn check_type(
        &mut self,
        root: ExprId,
        require_proposition: bool,
        incoming: ReductionPath,
        scope: Scope<'_>,
        environment: &Environment,
    ) -> Result<ReductionPath, Stop> {
        if let Some(error) = self.owned_cleanup {
            return Err(error.into());
        }
        // This consumer returns only a scalar path. Its input root and every
        // caller-owned local/source predate these marks; the inferred type and
        // Sort level below must not escape them.
        let expression_mark = self.expressions.watermark();
        let level_end = self.levels.len();
        let name_end = self.names.len();
        let local_entries = self.context.entry_count();
        let local_depth = self.context.depth();
        let (level, path, _retirement_witness) =
            self.checked_sort(root, incoming, scope, environment)?;
        self.owned_failure = Some(Stop::Resource(ResourceError::Invariant));
        let result = (|| {
            // Test the sort of the declared type, not the type
            // expression itself. The summary is valid for this immutable
            // level store, including nonliteral identically-zero levels.
            // Total decision: NonZero rejects the
            // declaration as not a proposition.
            if require_proposition && self.levels.get(level, self.budget)?.zero() != LevelZero::Zero
            {
                return Err(Stop::Judgment(Negative::ExpectedProposition));
            }
            Ok(path)
        })()
        .and_then(|path| {
            // Both inference/exposure drivers and their semantic tables
            // have retired. Preserve terminal cleanup independently from
            // operation poison, including an unwind or partial name removal.
            self.owned_cleanup.get_or_insert(ResourceError::Invariant);
            let cleanup = (|| {
                // Equal depth alone is insufficient: the primitive also
                // checks the active suffix. Scrub its payloads before slots
                // can be reused, while keeping FreeIds/bitmap monotone.
                self.context.retire_inactive_since(
                    local_entries,
                    local_depth,
                    root,
                    self.budget,
                )?;
                self.expressions
                    .discard_since(expression_mark, self.budget)?;
                self.levels.discard_since(level_end, self.budget)?;
                self.names.discard_since(name_end, self.budget)
            })();
            self.owned_cleanup = cleanup.as_ref().err().copied();
            cleanup.map(|()| path).map_err(Stop::Resource)
        });
        self.owned_failure = result.as_ref().err().copied();
        result
    }

    /// Caller supplies an already checked expression (including checked active
    /// locals) in this exact session and scope. This exposes it, never infers
    /// unchecked syntax or authorizes a new negative. Demanded observations and
    /// comparisons retain the driver's restricted staging policy.
    pub(crate) fn expose_checked(
        &mut self,
        root: ExprId,
        path: ReductionPath,
        scope: Scope<'_>,
        environment: &Environment,
    ) -> Result<crate::check::environment::normalization::Head, Stop> {
        if let Some(error) = self.owned_failure {
            return Err(error);
        }
        self.owned_failure = Some(Stop::Resource(ResourceError::Invariant));
        let result = driver::run(driver::Seed::Head(root, path), self, &scope, environment)
            .and_then(|completed| match completed {
                driver::Completed::Head(head) => Ok(head),
                _ => Err(ResourceError::Invariant.into()),
            });
        self.owned_failure = result.as_ref().err().copied();
        result
    }

    fn expose_type(
        &mut self,
        inferred: Inferred,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<crate::check::environment::normalization::Head, Stop> {
        match driver::run(
            driver::Seed::Head(inferred.ty, inferred.path),
            self,
            scope,
            environment,
        )? {
            driver::Completed::Head(head) => Ok(head),
            _ => Err(ResourceError::Invariant.into()),
        }
    }

    fn expose_type_auxiliary(
        &mut self,
        inferred: Inferred,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<crate::check::environment::normalization::Head, Stop> {
        Ok(scope.expose(
            inferred.ty,
            inferred.path,
            environment,
            self.expressions,
            self.levels,
            self.names,
            self.context,
            self.budget,
        )?)
    }

    fn sort_level(
        &mut self,
        inferred: Inferred,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<(LevelId, ReductionPath), Stop> {
        let head = self.expose_type(inferred, scope, environment)?;
        self.sort_level_head(head, scope, environment)
    }

    fn sort_level_head(
        &mut self,
        head: crate::check::environment::normalization::Head,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<(LevelId, ReductionPath), Stop> {
        match self.expressions.get(head.expression, self.budget)?.kind(
            self.expressions,
            self.levels,
            self.budget,
        )? {
            ExprKind::Sort(level) => Ok((level, head.path)),
            ExprKind::Pi(..) | ExprKind::Lambda(..) | ExprKind::Free(_) => {
                // Completed bare heads have no remaining weak-head rule here.
                Err(Stop::Judgment(Negative::ExpectedSort))
            }
            _ => match sort::completed_neutral_recursor(head, self, scope, environment)? {
                sort::NonSort::Proven => Err(Stop::Judgment(Negative::ExpectedSort)),
                sort::NonSort::NotProven => Err(Stop::Unsupported),
            },
        }
    }

    /// Both operands have completed checking in this exact ordinary scope.
    /// No failed comparison or abandoned child supplies negative evidence.
    pub(crate) fn compare_checked_types(
        &mut self,
        left: ExprId,
        right: ExprId,
        incoming: ReductionPath,
        scope: Scope<'_>,
        environment: &Environment,
    ) -> Result<ReductionPath, Stop> {
        if let Some(error) = self.owned_failure {
            return Err(error);
        }
        self.owned_failure = Some(ResourceError::Invariant.into());
        let result = self.compare_types(left, right, incoming, &scope, environment);
        self.owned_failure = result.as_ref().err().copied();
        result
    }

    // Called under an ordinary failure owner. Both operands are checked types
    // in the same active context. The cache retires before that context changes.
    fn compare_types(
        &mut self,
        left: ExprId,
        right: ExprId,
        incoming: ReductionPath,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<ReductionPath, Stop> {
        if let Some(path) = crate::check::environment::normalization::value::try_equal(
            left,
            right,
            incoming,
            *scope,
            environment,
            self.expressions,
            self.levels,
            self.names,
            self.budget,
            &mut self.value_force_calls,
        )
        .map_err(Stop::Normalization)?
        {
            return Ok(path);
        }
        match driver::run(
            driver::Seed::Comparison(left, right, incoming),
            self,
            scope,
            environment,
        )? {
            driver::Completed::Comparison(
                crate::check::environment::normalization::full::comparison::Decision::Equal(path),
            ) => Ok(path),
            driver::Completed::Comparison(
                crate::check::environment::normalization::full::comparison::Decision::Different(_),
            ) => Err(Stop::Judgment(Negative::TypeMismatch)),
            _ => Err(ResourceError::Invariant.into()),
        }
    }

    fn binder_fields(
        &mut self,
        root: ExprId,
    ) -> Result<(bool, NameId, ExprId, ExprId, BinderInfo), Stop> {
        match self.expressions.get(root, self.budget)?.kind(
            self.expressions,
            self.levels,
            self.budget,
        )? {
            ExprKind::Pi(name, domain, body, annotation) => {
                Ok((true, name, domain, body, annotation))
            }
            ExprKind::Lambda(name, domain, body, annotation) => {
                Ok((false, name, domain, body, annotation))
            }
            _ => Err(ResourceError::Invariant.into()),
        }
    }

    fn let_fields(&mut self, root: ExprId) -> Result<(NameId, ExprId, ExprId, ExprId), Stop> {
        match self.expressions.get(root, self.budget)?.kind(
            self.expressions,
            self.levels,
            self.budget,
        )? {
            ExprKind::Let(name, ty, value, body, _) => Ok((name, ty, value, body)),
            _ => Err(ResourceError::Invariant.into()),
        }
    }

    // The codomain belongs to the exposed Pi in this checked session. An exact
    // zero loose range means substitution and index lowering are both identities,
    // including below binders; free locals keep their original active identities.
    // Callers still check the argument (or hold checked-observation permission).
    fn instantiate_application_result(
        &mut self,
        codomain: ExprId,
        argument: View,
        environments: &EvaluationEnvironments,
    ) -> Result<ExprId, Stop> {
        if self.expressions.get(codomain, self.budget)?.loose_range() == 0 {
            return Ok(codomain);
        }
        let argument = self.materialize_view(argument, environments)?;
        Ok(self.expressions.bind(
            codomain,
            0,
            Binding::Instantiate(&[argument]),
            self.levels,
            self.names,
            self.budget,
        )?)
    }

    fn materialize_view(
        &mut self,
        view: View,
        environments: &EvaluationEnvironments,
    ) -> Result<ExprId, Stop> {
        let source = self.expressions.get(view.expression, self.budget)?;
        if source.loose_range() == 0 {
            return Ok(view.expression);
        }
        if let ExprKind::Bound(index) = source.kind(self.expressions, self.levels, self.budget)?
            && index < environments.len(view.environment)?
        {
            // Exact leaf of Binding::Environment: preserve the replacement's
            // handle and required closedness check, without allocating a worklist.
            let binding = environments.lookup(view.environment, index, self.budget)?;
            let result = self.expressions.resolve_slot(binding.slot(), self.budget)?;
            if self.expressions.get(result, self.budget)?.loose_range() != 0 {
                return Err(ResourceError::Invariant.into());
            }
            return Ok(result);
        }
        let lookup = |index, budget: &mut Budget| {
            environments
                .lookup(view.environment, index, budget)
                .map(|binding| binding.slot())
        };
        Ok(self.expressions.bind(
            view.expression,
            0,
            Binding::Environment {
                len: environments.len(view.environment)?,
                lookup: &lookup,
            },
            self.levels,
            self.names,
            self.budget,
        )?)
    }

    fn open_view(
        &mut self,
        body: ExprId,
        parent: EnvId,
        local: FreeId,
        environments: &mut EvaluationEnvironments,
    ) -> Result<View, Stop> {
        let free = self.expressions.append(
            ExprKind::Free(local.slot()),
            self.levels,
            self.names,
            self.budget,
        )?;
        let environment = environments.extend(parent, BindingId::new(free.slot()), self.budget)?;
        Ok(View {
            expression: body,
            environment,
        })
    }

    fn infer_machine(
        &mut self,
        root: ExprId,
        incoming: ReductionPath,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<Inferred, Stop> {
        match driver::run(
            driver::Seed::Inference(root, incoming),
            self,
            scope,
            environment,
        )? {
            driver::Completed::Inference(inferred) => Ok(inferred),
            _ => Err(ResourceError::Invariant.into()),
        }
    }
}
