//! Initial /15 ordinary validation. No whole-input verdict or public API.
use super::Environment;
use crate::check::environment::normalization::{Mode, Scope};
use crate::decode::primitive_decode::{
    Decoder,
    declarations::{Kind, Request, Safety, policy::Marker},
    ordinary_session::Stop,
};
use crate::report::axiom_report::Axioms;
use crate::resource::{
    Budget, Event, ReductionPath, ResourceError,
    failure::{FailureOutcome, FailureReport},
};
use std::mem::size_of;

mod inductives;
mod quotients;
mod schema_match;
pub(crate) mod stream;
mod theorem_judgments;
mod unsafe_candidate;

pub(crate) struct State {
    environment: Environment,
    retention: super::kernel::Retention,
    theorem_judgments: theorem_judgments::Judgments,
    axioms: Axioms,
    checked: u64,
    failure: Option<FailureReport>,
}
// Includes the exact Get! certificate; declaration entries remain unchanged.
const _: () = assert!(size_of::<State>() == 1016 + size_of::<theorem_judgments::Judgments>());
fn unsupported() -> FailureReport {
    FailureReport {
        outcome: FailureOutcome::Decline,
        code: "support.semantic",
    }
}

#[cfg(feature = "introspection")]
fn capture_ordinary(
    work: &mut crate::decode::primitive_decode::ordinary_session::Working<'_>,
    request: &Request<'_>,
    error: Stop,
    ty: crate::syntax::expressions::ExprId,
    value: Option<crate::syntax::expressions::ExprId>,
    mismatch: Option<crate::report::failure_snapshot::Mismatch>,
) {
    use crate::check::diagnostic::Sources;
    use crate::check::environment::normalization::HeadError;
    use crate::decode::primitive_decode::ordinary_session::Negative;
    use crate::report::failure_snapshot::{Capture, Identity, Role, Rule, Snapshot};
    if work
        .budget
        .failure_snapshot()
        .is_some_and(crate::report::failure_snapshot::Snapshot::has_rules)
    {
        return;
    }
    let rules: &[Rule] = match error {
        Stop::Judgment(
            Negative::ExpectedSort | Negative::ExpectedPi | Negative::ExpectedProposition,
        ) => &[Rule::Formation, Rule::Inference],
        Stop::Judgment(Negative::TypeMismatch) => &[Rule::Inference, Rule::Conversion],
        Stop::Judgment(Negative::DuplicateUniverseParameter) | Stop::Scope(_) => {
            &[Rule::DeclarationPolicy]
        }
        Stop::Judgment(
            Negative::MissingConstant | Negative::UnsafeReference | Negative::InvalidProjection,
        )
        | Stop::Inference(_) => &[Rule::Inference],
        Stop::Normalization(HeadError::Unsupported) | Stop::Observation(HeadError::Unsupported) => {
            &[Rule::Inference, Rule::UnsupportedReduction]
        }
        Stop::Normalization(_) | Stop::Observation(_) | Stop::Expression(_) => &[Rule::Inference],
        Stop::Copy(_) => &[Rule::Formation],
        Stop::Unsupported => &[Rule::Inference],
        Stop::Resource(_) => &[Rule::Inference],
    };
    let identities = [
        Identity::name(Role::Declaration, request.name),
        Identity::expression(Role::Type, ty),
        value
            .map(|value| Identity::expression(Role::Value, value))
            .unwrap_or_else(|| Identity::expression(Role::Type, ty)),
    ];
    let identities = if value.is_some() {
        &identities[..]
    } else {
        &identities[..2]
    };
    let snapshot = Snapshot::capture(Capture {
        declaration: Some(request.name),
        rules,
        identities,
        invariant: None,
        delayed: None,
        mismatch,
        sources: Sources {
            expressions: work.expressions,
            levels: work.levels,
            names: work.names,
            locals: Some(work.context),
        },
    });
    work.budget.capture_failure(snapshot);
}

#[cfg(feature = "introspection")]
fn capture_ordinary_result(
    result: &Result<Admission, FailureReport>,
    request: &Request<'_>,
    ordinal: u64,
    expected_ordinal: Option<u64>,
    decoder: &Decoder,
    budget: &mut Budget,
) {
    use crate::check::diagnostic::Sources;
    use crate::report::failure_snapshot::{
        Capture, Identity, Invariant, InvariantEvidence, Role, Rule, Snapshot, Value, ValueRole,
    };
    if budget.failure_snapshot().is_some() || matches!(result, Ok(Admission::Installed)) {
        return;
    }
    let rule = match result {
        Ok(Admission::Duplicate) => Rule::Publication,
        Err(failure) if failure.code == "support.policy" => Rule::DeclarationPolicy,
        Err(failure) if failure.code == "support.semantic" => Rule::DeclarationPolicy,
        _ => Rule::Inference,
    };
    let values = [
        Value {
            role: ValueRole::Expected,
            value: expected_ordinal.unwrap_or(0),
        },
        Value {
            role: ValueRole::Actual,
            value: ordinal,
        },
    ];
    let invariant = matches!(result, Err(failure) if failure.code == "internal.invariant")
        .then_some(expected_ordinal)
        .flatten()
        .filter(|&expected| expected != ordinal)
        .map(|_| InvariantEvidence {
            invariant: Invariant::DeclarationSequence,
            values: &values,
        })
        .or_else(|| {
            matches!(result, Err(failure) if failure.code == "internal.invariant").then_some(
                InvariantEvidence {
                    invariant: Invariant::Unavailable,
                    values: &[],
                },
            )
        });
    let (names, levels, expressions) = decoder.syntax();
    let identities = [
        Identity::name(Role::Declaration, request.name),
        Identity::expression(Role::Type, request.ty),
    ];
    budget.capture_failure(Snapshot::capture(Capture {
        declaration: Some(request.name),
        rules: &[rule],
        identities: &identities,
        invariant,
        delayed: None,
        mismatch: None,
        sources: Sources {
            expressions,
            levels,
            names,
            locals: None,
        },
    }));
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Admission {
    Installed,
    Duplicate,
    TypeMismatch,
}
impl State {
    pub(crate) fn new(budget: &mut Budget) -> Result<Self, ResourceError> {
        budget.charge_work(1)?; // prepay flat final owner retirement
        Ok(Self {
            environment: Environment::default(),
            retention: super::kernel::Retention::default(),
            theorem_judgments: theorem_judgments::Judgments::new(),
            axioms: Axioms::default(),
            checked: 0,
            failure: None,
        })
    }
    pub(crate) fn check_with_axiom_policy(
        &mut self,
        request: &Request<'_>,
        ordinal: u64,
        decoder: &mut Decoder,
        budget: &mut Budget,
        axiom_policy: crate::AxiomPolicy,
    ) -> Result<Admission, FailureReport> {
        if let Some(failure) = self.failure {
            return Err(failure);
        }
        self.failure = Some(ResourceError::Invariant.failure_report());
        budget.begin_declaration(ordinal, request.name, decoder.syntax().0);
        #[cfg(feature = "introspection")]
        let expected_ordinal = self.checked.checked_add(1);
        let mut result = self.check_inner(request, ordinal, decoder, budget, axiom_policy);
        if matches!(result, Ok(Admission::Installed)) {
            // All fallible checks, session rollback, publication and checked-count
            // updates completed. This phase flip cannot allocate or fail.
            self.retention.publish();
        } else if let Err(cleanup) = self.retention.retire(budget) {
            let cleanup = cleanup.failure_report();
            result = match result {
                Err(operation)
                    if operation.outcome == FailureOutcome::InternalError
                        || cleanup.outcome != FailureOutcome::InternalError =>
                {
                    Err(operation)
                }
                _ => Err(cleanup),
            };
        }
        self.theorem_judgments
            .finish(matches!(result, Ok(Admission::Installed)));
        #[cfg(feature = "introspection")]
        capture_ordinary_result(&result, request, ordinal, expected_ordinal, decoder, budget);
        budget.switch_bucket(crate::resource::Bucket::Input);
        self.failure = match result {
            Ok(Admission::Duplicate | Admission::TypeMismatch) => {
                Some(ResourceError::Invariant.failure_report())
            }
            _ => result.as_ref().err().copied(),
        };
        result
    }
    fn check_inner(
        &mut self,
        request: &Request<'_>,
        ordinal: u64,
        decoder: &mut Decoder,
        budget: &mut Budget,
        axiom_policy: crate::AxiomPolicy,
    ) -> Result<Admission, FailureReport> {
        budget
            .charge_work(1)
            .map_err(ResourceError::failure_report)?;
        let next = self
            .checked
            .checked_add(1)
            .ok_or_else(|| ResourceError::Counter.failure_report())?;
        if ordinal != next {
            return Err(ResourceError::Invariant.failure_report());
        }
        if (request.kind == Kind::Axiom) != request.value.is_none() {
            return Err(unsupported());
        }
        let (names, levels, expressions) = decoder.syntax();
        // Policy permits an attempt only. Checkedness still comes from all
        // ordinary validation below; no policy state is installed or cached.
        if axiom_policy == crate::AxiomPolicy::ExcludeNativeMarked
            && request
                .axiom_marker(names, budget)
                .map_err(ResourceError::failure_report)?
                == Marker::Excluded
        {
            return Err(FailureReport {
                outcome: FailureOutcome::Decline,
                code: "support.policy",
            });
        }
        if self
            .environment
            .lookup(request.name, self.environment.len(), names, budget)
            .map_err(ResourceError::failure_report)?
            .is_some()
        {
            // Exact lookup found an earlier validated declaration. This is the
            // Freshness negative, not a failed typing/conversion route.
            // The owner remains poisoned; only retirement and reporting may follow.
            return Ok(Admission::Duplicate);
        }
        if request.kind == Kind::Definition && request.safety == Safety::Unsafe {
            return self.check_unsafe_candidate(request, next, decoder, budget);
        }
        let expression_end = expressions.len();
        let level_end = levels.len();
        let before = self.environment.len();
        let mode = if request.kind == Kind::Axiom && request.safety == Safety::Unsafe {
            Mode::Unsafe
        } else {
            Mode::Safe
        };
        let scope = || Scope {
            formation: None,
            parameters: request.parameters,
            before,
            mode,
            expression_end,
            level_end,
        };
        // Original decoded roots only. This State is paired with the stream's
        // single Decoder throughout; generated/staged requests never enter here.
        let theorem_key = self.theorem_judgments.key(request, axiom_policy);
        let theorem_work_before = budget.snapshot().work_charged;
        let formation_negative = decoder
            .declaration_session(budget, |work| {
                #[cfg(feature = "introspection")]
                let mut captured_roots = (request.ty, request.value);
                #[cfg(feature = "introspection")]
                let mut compared = None;
                let result = (|| {
                    // Isolated value-kernel trial: a completed positive check
                    // replaces the ordinary route; anything else falls through
                    // to it unchanged. Mandatory resource errors stay terminal.
                    let kernel_scope = scope();
                    if super::kernel::eligible(request, &kernel_scope) {
                        let originals = [request.ty, request.value.unwrap_or(request.ty)];
                        work.check_root_scope(request.parameters, &originals)?;
                        if self
                            .theorem_judgments
                            .lookup(theorem_key, work.budget)
                            .map_err(Stop::Resource)?
                        {
                            // Only repeated T : Prop and p : T are discharged.
                            // Session cleanup and all publication checks below
                            // remain mandatory. Admitted axioms are monotonic
                            // in this State, collected at every axiom install.
                            return Ok(());
                        }
                        if super::kernel::check(
                            &self.environment,
                            request,
                            &kernel_scope,
                            work.names,
                            work.expressions,
                            work.levels,
                            work.budget,
                            Some(&mut self.retention),
                        )
                        .map_err(Stop::Normalization)?
                        {
                            return Ok(());
                        }
                    }
                    let (value, ty) = if request.kind == Kind::Theorem {
                        let (value, ty) =
                            work.copy_theorem(request.value.ok_or(Stop::Unsupported)?, request.ty)?;
                        (Some(value), ty)
                    } else {
                        (request.value, request.ty)
                    };
                    #[cfg(feature = "introspection")]
                    {
                        captured_roots = (ty, value);
                    }
                    if let Some(value) = value {
                        work.check_root_scope(request.parameters, &[ty, value])?;
                    } else {
                        work.check_root_scope(request.parameters, &[ty])?;
                    }
                    let type_path = work.check_type(
                        ty,
                        request.kind == Kind::Theorem,
                        ReductionPath::start(),
                        scope(),
                        &self.environment,
                    )?;
                    if let Some(value) = value {
                        let body_type = work.infer_at(
                            value,
                            ReductionPath::start(),
                            scope(),
                            &self.environment,
                        )?;
                        let incoming = type_path.maximum(body_type.path);
                        #[cfg(feature = "introspection")]
                        {
                            compared = Some(crate::report::failure_snapshot::Mismatch {
                                expected: ty,
                                actual: body_type.ty,
                            });
                        }
                        work.compare_checked_types(
                            body_type.ty,
                            ty,
                            incoming,
                            scope(),
                            &self.environment,
                        )?;
                    }
                    Ok(())
                })();
                #[cfg(feature = "introspection")]
                if let Err(error) = result {
                    capture_ordinary(
                        work,
                        request,
                        error,
                        captured_roots.0,
                        captured_roots.1,
                        compared,
                    );
                }
                result
            })
            .map_err(|error| error.failure_report())?;
        // A captured negative is usable only after all session cleanup succeeds.
        // It never installs this declaration or enables further semantic checking.
        if formation_negative.is_some() {
            return Ok(Admission::TypeMismatch);
        }
        let theorem_work = budget
            .snapshot()
            .work_charged
            .saturating_sub(theorem_work_before);
        self.theorem_judgments
            .prepare(theorem_key, theorem_work, budget)
            .map_err(ResourceError::failure_report)?;
        // Original fields only. All generated syntax/locals/cache retirement
        // succeeded before publication; no fallible check follows insertion.
        let (names, levels, expressions) = decoder.syntax();
        let certificate =
            Environment::prepare_annotation(request, names, levels, expressions, budget)
                .map_err(ResourceError::failure_report)?;
        let predicates = self
            .environment
            .prepare_predicate_definition(request, names, levels, expressions, budget)
            .map_err(ResourceError::failure_report)?;
        let string = self
            .environment
            .prepare_string_definition(
                self.environment.string,
                request,
                names,
                levels,
                expressions,
                budget,
            )
            .map_err(ResourceError::failure_report)?;
        let native_natural = self
            .environment
            .prepare_native_natural_definition(
                self.environment.native_natural,
                &string,
                request,
                names,
                levels,
                expressions,
                budget,
            )
            .map_err(ResourceError::failure_report)?;
        let getbang = self
            .environment
            .prepare_getbang_definition(
                self.environment.getbang,
                request,
                names,
                levels,
                expressions,
                budget,
            )
            .map_err(ResourceError::failure_report)?;
        let finite = self
            .environment
            .prepare_finite_definition(
                self.environment.finite,
                request,
                names,
                levels,
                expressions,
                budget,
            )
            .map_err(ResourceError::failure_report)?;
        let pending = if request.kind == Kind::Axiom {
            budget.switch_bucket(crate::resource::Bucket::Report);
            let pending = self.axioms.prepare(ordinal, request.name, names, budget);
            budget.switch_bucket(crate::resource::Bucket::Declaration);
            Some(pending.map_err(ResourceError::failure_report)?)
        } else {
            None
        };
        self.environment
            .publish_validated(request, names, budget)
            .map_err(ResourceError::failure_report)?;
        self.environment.commit_annotation(certificate);
        self.environment.commit_predicates(predicates);
        self.environment.native_natural = native_natural;
        self.environment.string = string;
        self.environment.getbang = getbang;
        self.environment.finite = finite;
        if let Some(pending) = pending {
            pending.commit();
        }
        self.checked = next;
        budget.checked_declarations(next);
        budget.observe(Event::DeclarationsInstalled, 1);
        Ok(Admission::Installed)
    }
    /// Usable prefix only: this is not evidence of clean EOF or whole-file
    /// acceptance. An interrupted owner cannot expose a success-shaped summary.
    pub(crate) fn prefix(&self) -> Result<(u64, &[u8]), FailureReport> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        Ok((self.checked, self.axioms.encoded()))
    }
    // Stream completion calls this on EOF and early justified rejection; the
    // later State retirement is idempotent. No semantic cache enters Complete.
    pub(super) fn retire_retention(&mut self, budget: &mut Budget) -> Result<(), ResourceError> {
        let retained = self.retention.retire(budget);
        let judgments = self.theorem_judgments.retire(budget);
        super::kernel::select_cleanup([retained, judgments])
    }
    pub(crate) fn retire(self, budget: &mut Budget) -> Result<(), ResourceError> {
        let Self {
            environment,
            mut retention,
            theorem_judgments: mut judgments,
            axioms,
            ..
        } = self;
        let retained_release = retention.retire(budget);
        let judgment_release = judgments.retire(budget);
        let env_release = environment.retire(budget);
        let axiom_release = axioms.retire(budget);
        super::kernel::select_cleanup([
            retained_release,
            judgment_release,
            env_release,
            axiom_release,
        ])
    }
}
