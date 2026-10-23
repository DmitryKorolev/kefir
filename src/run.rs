//! Single-use public reader/report owner. Unwinding is caught only by the CLI.
use crate::{
    Outcome, candidate_identity,
    check::environment::validation::stream,
    decode::primitive_decode::Decoder,
    report::failure_envelope::{Detail, Envelope, Frozen, Identities, Location},
    report::report_storage::{self, Storage},
    resource::{
        Budget,
        failure::{FailureOutcome, FailureReport},
    },
};
use std::io::{Read, Write};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Ready,
    Checking,
    Finished,
}
/// Input configuration errors identified by the thin CLI or in-process caller.
#[derive(Clone, Copy)]
pub enum InputError {
    Arguments,
    Io,
}
/// Which declared assumptions a single-use run may attempt to admit.
/// This never authorizes native execution or bypasses declaration validation.
/// Record the selected policy alongside the run; reports contain the complete
/// admitted assumption set, but do not attest the configuration.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum AxiomPolicy {
    /// Decline exact `_native` string components. This is a name convention,
    /// not a provenance guarantee or a restriction on `sorryAx`.
    #[default]
    ExcludeNativeMarked,
    /// Check every declared axiom ordinarily and report it as an assumption.
    AllowAllDeclaredAxioms,
}
/// One input, one immutable resource profile and at most one report attempt.
/// A panic propagates to the caller; discard semantic state and call report_panic
/// only from the caller's unwind boundary. Never resume checking after a panic.
pub struct Run {
    budget: Budget,
    buffers: Result<Storage, report_storage::Failure>,
    phase: Phase,
    requested: bool,
    axiom_policy: AxiomPolicy,
}
impl Run {
    fn identities() -> Identities {
        let identities = candidate_identity::CANDIDATE_IDENTITIES;
        Identities(identities)
    }
    /// Reserve report buffers before opening/reading input. A failed bootstrap is
    /// retained for reporting; bootstrap_error must be checked before CLI file IO.
    pub fn new(declarations: bool) -> Self {
        Self::new_with_axiom_policy(declarations, AxiomPolicy::ExcludeNativeMarked)
    }
    /// Construct a run with an explicit, immutable assumption-admission policy.
    /// Validation and complete assumption reporting are mandatory in both modes.
    pub fn new_with_axiom_policy(declarations: bool, axiom_policy: AxiomPolicy) -> Self {
        let mut budget = Budget::new();
        let buffers = Storage::bootstrap(&mut budget);
        Self {
            budget,
            buffers,
            phase: Phase::Ready,
            requested: declarations,
            axiom_policy,
        }
    }
    fn detail(&self) -> Detail {
        if cfg!(feature = "introspection") && self.requested {
            Detail::Unavailable
        } else {
            Detail::NotRequested
        }
    }
    fn frozen(&self) -> Frozen {
        let p = self.budget.progress();
        let b = self.budget.snapshot();
        Frozen {
            checked_declarations: p.checked_declarations,
            input_bytes: p.input_bytes,
            records: p.records,
            work_charged: b.work_charged,
            peak_live_capacity_bytes: b.peak_live_capacity_bytes,
        }
    }
    fn emit(
        &mut self,
        failure: FailureReport,
        location: Option<Location>,
        kind: Option<&str>,
        output: &mut impl Write,
    ) -> Outcome {
        self.phase = Phase::Finished;
        let envelope = Envelope {
            failure,
            identities: Some(Self::identities()),
            frozen: self.frozen(),
            detail: self.detail(),
            declaration_kind: kind,
            location,
        };
        let result = match &mut self.buffers {
            Ok(storage) => storage.publish_failure(&envelope, Some(&mut self.budget), output),
            Err(bootstrap) => {
                report_storage::attempt(bootstrap.emergency.as_mut(), &envelope, output)
                    .map(|_| failure.outcome)
            }
        };
        match result {
            Ok(FailureOutcome::Decline) => Outcome::Decline,
            Ok(FailureOutcome::InputError) => Outcome::InputError,
            _ => Outcome::InternalError,
        }
    }
    /// Report a retained bootstrap failure without touching input.
    pub fn bootstrap_error(&mut self, output: &mut impl Write) -> Option<Outcome> {
        if self.phase != Phase::Ready {
            return Some(Outcome::InternalError);
        }
        let error = self.buffers.as_ref().err()?.cause;
        Some(self.emit(error.failure_report(), None, None, output))
    }
    /// Terminal configuration error; an observed internal bootstrap failure wins.
    pub fn input_error(&mut self, error: InputError, output: &mut impl Write) -> Outcome {
        if self.phase != Phase::Ready {
            return Outcome::InternalError;
        }
        let mut failure = FailureReport {
            outcome: FailureOutcome::InputError,
            code: match error {
                InputError::Arguments => "input.arguments",
                InputError::Io => "input.io",
            },
        };
        if let Err(bootstrap) = &self.buffers {
            let report = bootstrap.cause.failure_report();
            if report.outcome == FailureOutcome::InternalError {
                failure = report;
            }
        }
        self.emit(failure, None, None, output)
    }
    /// Read and check the supplied lean4export stream, then publish one report.
    /// Missing support declines. Duplicate-name rejection requires supported EOF.
    ///
    /// Checking runs on one scoped thread with a large reserved stack (pages
    /// are committed only on use): the value kernel recurses
    /// natively and declines before it reaches that thread's stack limit. A
    /// panic on the checking thread resumes on the caller's; a thread that
    /// cannot be created is an internal allocation failure.
    pub fn check(
        &mut self,
        reader: &mut (impl Read + Send),
        output: &mut (impl Write + Send),
    ) -> Outcome {
        // Unit tests check inline: they drive the run through thread-local
        // switches and counters, and their harness threads already have large
        // stacks. Integration tests and production take the thread.
        let checked = std::thread::scope(|scope| {
            let this = &mut *self;
            let output = &mut *output;
            let thread = std::thread::Builder::new()
                .stack_size(crate::check::environment::kernel::CHECK_STACK)
                .spawn_scoped(scope, move || {
                    crate::check::environment::kernel::mark_stack_base();
                    this.check_here(reader, output)
                });
            thread
                .ok()
                .map(|t| t.join().unwrap_or_else(|p| std::panic::resume_unwind(p)))
        });
        match checked {
            Some(outcome) => outcome,
            None => self.emit(
                FailureReport {
                    outcome: FailureOutcome::InternalError,
                    code: "internal.allocation",
                },
                None,
                None,
                output,
            ),
        }
    }
    fn check_here(&mut self, reader: &mut impl Read, output: &mut impl Write) -> Outcome {
        if self.phase != Phase::Ready {
            return Outcome::InternalError;
        }
        if let Some(outcome) = self.bootstrap_error(output) {
            return outcome;
        }
        if self.requested && !cfg!(feature = "introspection") {
            return self.input_error(InputError::Arguments, output);
        }
        self.phase = Phase::Checking;
        let mut decoder = match Decoder::new(&mut self.budget) {
            Ok(decoder) => decoder,
            Err(error) => return self.emit(error.failure_report(), None, None, output),
        };
        let result = stream::check_with_axiom_policy(
            reader,
            &mut decoder,
            &mut self.budget,
            self.axiom_policy,
        );
        drop(decoder); // remaining completion owns only report bytes and flat retirement
        match result {
            Ok(complete) => {
                self.phase = Phase::Finished;
                let detail = self.detail();
                let Ok(storage) = &mut self.buffers else {
                    return Outcome::InternalError;
                };
                match storage.publish_acceptance(
                    complete,
                    Some(Self::identities()),
                    detail,
                    &mut self.budget,
                    output,
                ) {
                    Ok(0) => Outcome::Accept,
                    Ok(1) => Outcome::Reject,
                    Ok(2) => Outcome::Decline,
                    _ => Outcome::InternalError,
                }
            }
            Err(stopped) => {
                let location = stopped.record.map(|record| Location {
                    record,
                    declaration: stopped.declaration,
                });
                self.emit(
                    stopped.selected(),
                    location,
                    stopped.kind.map(|kind| kind.wire()),
                    output,
                )
            }
        }
    }
    /// CLI unwind boundary only. A begun report attempt can never be retried.
    pub fn report_panic(&mut self, output: &mut impl Write) -> Outcome {
        if self.phase == Phase::Finished {
            return Outcome::InternalError;
        }
        self.emit(
            FailureReport {
                outcome: FailureOutcome::InternalError,
                code: "internal.panic",
            },
            None,
            None,
            output,
        )
    }
}
