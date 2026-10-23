//! Ordinary original-template lifetime owner, not validation.
use super::{Cause, Decoder, Failure};
mod inference;
// The inference region's checkedness-mint authority is re-exported so the
// certificate constructors in crate::syntax::local_context can name the
// token type without widening the private module itself.
pub(crate) use self::inference::CheckednessMint;
use crate::check::environment::{
    Environment,
    normalization::{HeadError, Scope, full::Session},
};
use crate::resource::failure::{FailureOutcome, FailureReport};
use crate::resource::{Budget, ResourceError, SessionCacheBudget};
use crate::syntax::expressions::{ExprId, ExprKind, ExpressionError, Expressions};
use crate::syntax::levels::{LevelId, Levels, NameId, ScopeError};
use crate::syntax::local_context::LocalContext;
use crate::syntax::names::Names;

/// A completed rule failure, never a resource/unsupported sentinel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Negative {
    ExpectedSort,
    ExpectedPi,
    ExpectedProposition,
    DuplicateUniverseParameter,
    MissingConstant,
    UnsafeReference,
    InvalidProjection,
    TypeMismatch,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Stop {
    Judgment(Negative),
    Resource(ResourceError),
    Copy(crate::check::theorem_copy::Error),
    Unsupported,
    Normalization(HeadError),
    Scope(ScopeError),
    Expression(ExpressionError),
    Inference(HeadError),
    Observation(HeadError),
}
impl Stop {
    /// Classification only, not permission to reject. Generated checking and
    /// positive-only owners must intercept every category before retirement.
    fn completed_negative(self) -> Option<Negative> {
        Some(match self {
            Stop::Judgment(kind) => kind,
            Stop::Scope(ScopeError::DuplicateParameter(_)) => Negative::DuplicateUniverseParameter,
            Stop::Inference(HeadError::Use(
                crate::check::environment::normalization::UseError::Unavailable,
            )) => Negative::MissingConstant,
            Stop::Inference(HeadError::Use(
                crate::check::environment::normalization::UseError::UnsafeUse,
            )) => Negative::UnsafeReference,
            _ => return None,
        })
    }

    fn report(self) -> FailureReport {
        match self {
            Self::Resource(error)
            | Self::Copy(crate::check::theorem_copy::Error::Resource(error)) => {
                error.failure_report()
            }
            Self::Copy(crate::check::theorem_copy::Error::NumericRange) => FailureReport {
                outcome: FailureOutcome::Decline,
                code: "support.numeric_range",
            },
            Self::Normalization(error) | Self::Inference(error) | Self::Observation(error) => {
                normalization_report(error)
            }
            Self::Expression(error) => normalization_report(HeadError::Use(
                crate::check::environment::normalization::UseError::Expression(error),
            )),
            Self::Scope(ScopeError::Resource(error)) => error.failure_report(),
            Self::Scope(
                ScopeError::DuplicateParameter(_)
                | ScopeError::UnknownParameter(_)
                | ScopeError::OpenExpression(_),
            ) => Self::Unsupported.report(),
            // Positive-only clients cannot publish a negative. Declaration
            // completion consumes this separately after successful retirement.
            Self::Judgment(_) => Self::Unsupported.report(),
            Self::Unsupported => FailureReport {
                outcome: FailureOutcome::Decline,
                code: "support.semantic",
            },
        }
    }
}
// This adapter is only for checked-input normalization in the positive slice.
// Failed premises remain inconclusive. Invalid literal reconstruction from
// already validated stored bytes is a broken invariant, not an input verdict.
fn normalization_report(error: HeadError) -> FailureReport {
    use crate::check::environment::normalization::UseError;
    use crate::syntax::expressions::ExpressionError;
    use crate::syntax::levels::ScopeError;
    match error {
        HeadError::Use(UseError::LiteralArithmetic) => FailureReport {
            outcome: FailureOutcome::Decline,
            code: "support.literal_arithmetic",
        },
        HeadError::Use(
            UseError::Resource(error)
            | UseError::Scope(ScopeError::Resource(error))
            | UseError::Expression(ExpressionError::Resource(error)),
        ) => error.failure_report(),
        HeadError::Use(UseError::Expression(ExpressionError::NumericRange)) => FailureReport {
            outcome: FailureOutcome::Decline,
            code: "support.numeric_range",
        },
        HeadError::Use(UseError::Expression(
            ExpressionError::InvalidNatural | ExpressionError::InvalidString,
        )) => ResourceError::Invariant.failure_report(),
        HeadError::Unsupported
        | HeadError::Use(
            UseError::Unavailable
            | UseError::UnsafeUse
            | UseError::Arity
            | UseError::Scope(
                ScopeError::DuplicateParameter(_)
                | ScopeError::UnknownParameter(_)
                | ScopeError::OpenExpression(_),
            ),
        ) => Stop::Unsupported.report(),
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Interrupted {
    /// Preserve the operation cause even if reclamation subsequently fails.
    pub operation: Option<Stop>,
    pub owned_work: Option<Stop>,
    pub cleanup: Option<ResourceError>,
}

#[cfg(feature = "introspection")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SelectedSource {
    Operation,
    OwnedWork,
    Cleanup,
    Synthesized,
}

impl Interrupted {
    fn completed_negative(&self) -> Option<Negative> {
        if self.cleanup.is_some() {
            return None;
        }
        let mut negative = None;
        for cause in [self.operation, self.owned_work].into_iter().flatten() {
            let kind = cause.completed_negative()?;
            if negative.is_some_and(|previous| previous != kind) {
                return None;
            }
            negative = Some(kind);
        }
        negative
    }

    /// Select only among retained ordinary-session failures, never the decoder's
    /// retry poison. Internal failures dominate declines. Diagnostic ties use
    /// callback, owned-work, cleanup order; this is not claimed chronology.
    /// No facts are consumed and no budget, allocation or verdict is involved.
    pub(crate) fn failure_report(&self) -> FailureReport {
        let reports = [
            self.operation
                .filter(|cause| !matches!(cause, Stop::Judgment(_)))
                .map(Stop::report),
            self.owned_work
                .filter(|cause| !matches!(cause, Stop::Judgment(_)))
                .map(Stop::report),
            self.cleanup.map(ResourceError::failure_report),
        ];
        reports
            .iter()
            .flatten()
            .copied()
            .find(|report| report.outcome == FailureOutcome::InternalError)
            .or_else(|| reports.into_iter().flatten().next())
            .unwrap_or_else(|| {
                if self.completed_negative().is_some() {
                    Stop::Unsupported.report()
                } else {
                    ResourceError::Invariant.failure_report()
                }
            })
    }

    #[cfg(feature = "introspection")]
    fn selected_source(&self) -> SelectedSource {
        let reports = [
            self.operation
                .filter(|cause| !matches!(cause, Stop::Judgment(_)))
                .map(Stop::report),
            self.owned_work
                .filter(|cause| !matches!(cause, Stop::Judgment(_)))
                .map(Stop::report),
            self.cleanup.map(ResourceError::failure_report),
        ];
        reports
            .iter()
            .position(|report| {
                report.is_some_and(|report| report.outcome == FailureOutcome::InternalError)
            })
            .or_else(|| reports.iter().position(Option::is_some))
            .map(|index| match index {
                0 => SelectedSource::Operation,
                1 => SelectedSource::OwnedWork,
                2 => SelectedSource::Cleanup,
                _ => unreachable!(),
            })
            .unwrap_or(SelectedSource::Synthesized)
    }
}
/// Internal checking work must not export generated handles through captured
/// state, install generated roots, replace stores/ledger, or retain any context,
/// memo or frame after returning. Original templates alone may outlive this
/// scope. These are construction invariants, not Rust lifetime branding of IDs.
/// Propagate every raw-operation resource/internal/unsupported failure. The
/// owner cannot detect an ignored error from a raw store exposed below.
/// This type supplies no checkedness and no environment installer.
pub(crate) struct Working<'a> {
    pub names: &'a mut Names,
    pub levels: &'a mut Levels,
    pub expressions: &'a mut Expressions,
    pub context: &'a mut LocalContext,
    pub budget: &'a mut Budget,
    original_expressions: usize,
    original_levels: usize,
    caches: SessionCacheBudget,
    // One declaration-wide admission limit for the optional closed-value
    // comparison route. Exhaustion falls through to the established driver.
    value_force_calls: u32,
    // Pre-staging authority: set only by `with_pre_staging_sorts`,
    // which the inductive validators call around their pre-staging family
    // typing. While set, a formation-free positive Sort query may use the
    // value engine against the committed environment (`Environment::
    // check_scope` requires `before == len()` for `formation = None`).
    pre_staging_sorts: bool,
    owned_failure: Option<Stop>,
    // Nested/consumed-check terminal retirement precedes enclosing rollback.
    // An active cleanup sentinel also survives unwind. It must not erase an
    // operation/owned-work cause or allow a completed negative through cleanup.
    owned_cleanup: Option<ResourceError>,
}
const _: () = assert!(std::mem::size_of::<Working<'_>>() <= 96);
impl Working<'_> {
    /// Runs `f` with the pre-staging Sort authority. Only the
    /// inductive validators' pre-staging family typing calls this; its scope
    /// is the committed environment with no staged signature. The flag is
    /// restored whatever `f` returns.
    pub(crate) fn with_pre_staging_sorts<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let previous = std::mem::replace(&mut self.pre_staging_sorts, true);
        let result = f(self);
        self.pre_staging_sorts = previous;
        result
    }
    pub(crate) fn pre_staging_sorts(&self) -> bool {
        self.pre_staging_sorts
    }
    /// Only the nested validator records its owned cleanup at callback exit.
    /// After this call it may retire further owners, but must perform no checking
    /// or publication. The Environment retires before callback exit in all cases.
    /// Keep the first cleanup failure separately from every semantic cause.
    pub(crate) fn record_nested_retirement(&mut self, result: Result<(), ResourceError>) {
        if self.owned_cleanup.is_none() {
            self.owned_cleanup = result.err();
        }
    }
    // The inference machine uses this complete atom rule under its own failure
    // owner. It does not skip a checking premise or install a scope fact.
    fn infer_atom_rule(&mut self, root: ExprId) -> Result<ExprId, Stop> {
        self.budget.charge_work(1).map_err(Stop::Resource)?;
        let kind = self
            .expressions
            .get(root, self.budget)
            .map_err(Stop::Resource)?
            .kind(self.expressions, self.levels, self.budget)
            .map_err(Stop::Resource)?;
        match kind {
            ExprKind::Sort(level) => {
                let successor = self
                    .levels
                    .append(
                        crate::syntax::levels::LevelKind::Succ(level),
                        self.names,
                        self.budget,
                    )
                    .map_err(Stop::Resource)?;
                self.expressions
                    .append(
                        ExprKind::Sort(successor),
                        self.levels,
                        self.names,
                        self.budget,
                    )
                    .map_err(Stop::Expression)
            }
            ExprKind::Free(id) => self
                .context
                .get(id, self.budget)
                .map(|local| local.ty())
                .map_err(Stop::Resource),
            ExprKind::Bound(_) => Err(Stop::Resource(ResourceError::Invariant)),
            _ => Err(Stop::Unsupported),
        }
    }
    /// Establish declaration-root closedness and exact universe coverage only.
    /// Call once over the complete type/value root set before their semantic
    /// checking, after theorem-local copying when applicable. This is neither
    /// inference nor permission to install an entry or normalize unchecked terms.
    /// All roots and parameters belong to this run. Scope scratch is call-local;
    /// no checkedness marker or cached scope fact survives the operation.
    pub(crate) fn check_root_scope(
        &mut self,
        parameters: &[NameId],
        roots: &[ExprId],
    ) -> Result<(), Stop> {
        if let Some(error) = self.owned_failure {
            return Err(error);
        }
        self.owned_failure = Some(Stop::Resource(ResourceError::Invariant));
        let result = self
            .expressions
            .check_scope(self.levels, self.names, parameters, roots, self.budget)
            .map_err(Stop::Scope);
        self.owned_failure = result.as_ref().err().copied();
        result
    }
    /// Own one fixed-permission normalization region inside this declaration.
    /// The caller still supplies checked roots and validated environment entries;
    /// scope frontiers must equal this owner's original decoded frontiers.
    /// Generated results may be used only before the enclosing ordinary session
    /// retires. Every optional table must share `caches`; never reset its ledger.
    pub(crate) fn with_normalization<T>(
        &mut self,
        scope: Scope<'_>,
        environment: &Environment,
        work: impl FnOnce(&mut Session<'_>) -> Result<T, HeadError>,
    ) -> Result<T, Stop> {
        if let Some(error) = self.owned_failure {
            return Err(error);
        }
        // Poison before callback entry: even an externally caught unwind cannot
        // make this declaration complete or resume another owned operation.
        self.owned_failure = Some(Stop::Resource(ResourceError::Invariant));
        let result = if scope.expression_end != self.original_expressions
            || scope.level_end != self.original_levels
            || environment
                .check_scope(
                    scope.before,
                    scope.formation,
                    scope.expression_end,
                    scope.level_end,
                )
                .is_err()
        {
            Err(Stop::Resource(ResourceError::Invariant))
        } else {
            scope
                .with_cache(
                    environment,
                    self.expressions,
                    self.levels,
                    self.names,
                    self.context,
                    &mut self.caches,
                    self.budget,
                    work,
                )
                .map_err(Stop::Normalization)
        };
        self.owned_failure = result.as_ref().err().copied();
        result
    }
    /// Both roots must belong to the original decoded prefix. The copy helper
    /// completes value then type and retires all of its own transient scratch.
    pub(crate) fn copy_theorem(
        &mut self,
        value: ExprId,
        ty: ExprId,
    ) -> Result<(ExprId, ExprId), Stop> {
        if let Some(error) = self.owned_failure {
            return Err(error);
        }
        let result = self.copy_theorem_inner(value, ty);
        if let Err(error) = result {
            self.owned_failure = Some(error);
        }
        result
    }
    fn copy_theorem_inner(&mut self, value: ExprId, ty: ExprId) -> Result<(ExprId, ExprId), Stop> {
        if value.slot() as usize >= self.original_expressions
            || ty.slot() as usize >= self.original_expressions
        {
            return Err(Stop::Resource(ResourceError::Invariant));
        }
        crate::check::theorem_copy::copy(
            self.names,
            self.levels,
            self.expressions,
            value,
            ty,
            self.budget,
        )
        .map_err(Stop::Copy)
    }
}
impl Decoder {
    /// Only declaration admission may consume a completed negative. On success,
    /// all session storage has retired; no generated handle is returned.
    pub(crate) fn declaration_session(
        &mut self,
        budget: &mut Budget,
        work: impl FnOnce(&mut Working<'_>) -> Result<(), Stop>,
    ) -> Result<Option<Negative>, Interrupted> {
        self.ordinary_session_inner(budget, work, true)
    }
    fn ordinary_session_inner(
        &mut self,
        budget: &mut Budget,
        work: impl FnOnce(&mut Working<'_>) -> Result<(), Stop>,
        allow_negative: bool,
    ) -> Result<Option<Negative>, Interrupted> {
        if self.failure.is_some() {
            return Err(Interrupted {
                operation: Some(Stop::Resource(ResourceError::Invariant)),
                owned_work: None,
                cleanup: None,
            });
        }
        self.failure = Some(Failure {
            observed: crate::decode::record_references::CheckedShape {
                shape: Default::default(),
                missing_reference: false,
            },
            cause: Cause::Resource(ResourceError::Invariant),
        });
        let name_end = self.names.len();
        let level_end = self.levels.len();
        let expression_end = self.expressions.len();
        let expression_mark = self.expressions.watermark();
        let mut context = LocalContext::new(budget).map_err(|error| Interrupted {
            operation: Some(Stop::Resource(error)),
            owned_work: None,
            cleanup: None,
        })?;
        let mut working = Working {
            names: &mut self.names,
            levels: &mut self.levels,
            expressions: &mut self.expressions,
            context: &mut context,
            budget,
            original_expressions: expression_end,
            original_levels: level_end,
            caches: SessionCacheBudget::default(),
            value_force_calls: 0,
            pre_staging_sorts: false,
            owned_failure: None,
            owned_cleanup: None,
        };
        let operation = work(&mut working).err();
        let owned_work = working.owned_failure;
        let owned_cleanup = working.owned_cleanup;
        // Callback locals/memos are gone before context retirement. Stop at the
        // first failed rollback: no later store may erase a still-referenced node.
        let cleanup = owned_cleanup
            .map_or(Ok(()), Err)
            .and_then(|()| context.retire(budget))
            .and_then(|()| self.expressions.discard_since(expression_mark, budget))
            .and_then(|()| self.levels.discard_since(level_end, budget))
            .and_then(|()| self.names.discard_since(name_end, budget))
            .err();
        let interrupted = Interrupted {
            operation,
            owned_work,
            cleanup,
        };
        #[cfg(feature = "introspection")]
        {
            use crate::report::failure_snapshot::{Invariant, Rule, Snapshot};
            if interrupted.selected_source() == SelectedSource::Cleanup {
                budget.replace_failure(Snapshot::rule_invariant(
                    Rule::Cleanup,
                    Some(Invariant::Cleanup),
                ));
            } else if interrupted.failure_report().code == "internal.invariant" {
                budget.ensure_failure_invariant(Invariant::Unavailable);
            }
        }
        if allow_negative && let Some(negative) = interrupted.completed_negative() {
            self.failure = None; // The declaration owner must terminate; no generated handles escape.
            return Ok(Some(negative));
        }
        if operation.is_some() || owned_work.is_some() || cleanup.is_some() {
            return Err(interrupted);
        }
        self.failure = None;
        Ok(None)
    }
}
