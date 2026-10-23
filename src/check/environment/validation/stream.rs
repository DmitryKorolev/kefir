//! Acceptance at EOF and first justified rejection.
use super::{Admission, State};
use crate::decode::primitive_decode::{
    DeclarationKind, Decoder, Item,
    declarations::Kind,
    stream::{Failure, Next, Stream, diagnostic::Mapped},
};
use crate::resource::{
    Budget, ResourceError,
    failure::{FailureOutcome, FailureReport},
};
use std::io::Read;

fn priority(report: FailureReport) -> u8 {
    match report.outcome {
        FailureOutcome::InternalError => 3,
        FailureOutcome::InputError => 2,
        FailureOutcome::Decline => 1,
    }
}

fn mapped_report(cause: &Mapped<FailureReport>) -> FailureReport {
    match cause {
        Mapped::Decoder(facts) => facts.selected().report,
        Mapped::Consumer(report) => *report,
    }
}

#[cfg(feature = "introspection")]
fn stream_cleanup_selected(
    result: Option<&Mapped<FailureReport>>,
    cleanup: Option<ResourceError>,
) -> bool {
    cleanup.is_some_and(|error| {
        result.is_none_or(|cause| priority(error.failure_report()) > priority(mapped_report(cause)))
    })
}

#[cfg(feature = "introspection")]
fn capture(
    budget: &mut Budget,
    syntax: (
        &crate::syntax::names::Names,
        &crate::syntax::levels::Levels,
        &crate::syntax::expressions::Expressions,
    ),
    rules: &[crate::report::failure_snapshot::Rule],
    invariant: Option<crate::report::failure_snapshot::InvariantEvidence<'_>>,
) {
    use crate::check::diagnostic::Sources;
    use crate::report::failure_snapshot::{Capture, Snapshot};
    if budget.failure_snapshot().is_some() {
        return;
    }
    let (names, levels, expressions) = syntax;
    budget.capture_failure(Snapshot::capture(Capture {
        declaration: None,
        rules,
        identities: &[],
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

/// Reporting-only ownership. All template handles are inaccessible; this token
/// may outlive the decoder because its report data are owned bytes and counts.
/// Retire with the originating budget, or discard the entire run and ledger.
pub(crate) struct Complete {
    state: State,
    records: u64,
    input_bytes: u64,
    rejection: Option<Rejection>,
}
/// A justified supported declaration failure observed at the earliest failing declaration.
/// Only this stream owner constructs it, and successful record validation and cleanup expose it.
#[derive(Clone, Copy)]
pub(crate) struct Rejection {
    record: std::num::NonZeroU64,
    declaration: std::num::NonZeroU64,
    kind: DeclarationKind,
}
impl Rejection {
    pub(crate) fn location(self) -> crate::report::failure_envelope::Location {
        crate::report::failure_envelope::Location {
            record: self.record,
            declaration: Some(self.declaration),
        }
    }
    pub(crate) fn kind(self) -> &'static str {
        self.kind.wire()
    }
}
// Includes the exact Nat.div/Nat.mod frontiers and the Get! certificate.
const _: () = assert!(
    std::mem::size_of::<Complete>()
        == 1056 + std::mem::size_of::<super::theorem_judgments::Judgments>()
);
impl Complete {
    pub(crate) fn rejection(&self) -> Option<Rejection> {
        self.rejection
    }
    pub(crate) fn records(&self) -> u64 {
        self.records
    }
    pub(crate) fn input_bytes(&self) -> u64 {
        self.input_bytes
    }
    pub(crate) fn checked(&self) -> u64 {
        self.state.checked
    }
    pub(crate) fn axioms(&self) -> &[u8] {
        self.state.axioms.encoded()
    }
    pub(crate) fn retire(self, budget: &mut Budget) -> Result<(), ResourceError> {
        self.state.retire(budget)
    }
}
/// Original observations survive cleanup selection. Counts are a diagnostic
/// prefix, never evidence that an unread suffix was valid or supported.
#[derive(Debug)]
pub(crate) struct Stopped {
    pub cause: Mapped<FailureReport>,
    pub stream_cleanup: Option<ResourceError>,
    pub state_cleanup: Option<ResourceError>,
    pub checked: u64,
    pub records: u64,
    pub input_bytes: u64,
    pub record: Option<std::num::NonZeroU64>,
    pub declaration: Option<std::num::NonZeroU64>,
    pub kind: Option<DeclarationKind>,
}
const _: () = assert!(std::mem::size_of::<Stopped>() <= 128);
impl Stopped {
    fn new(cause: Mapped<FailureReport>) -> Self {
        Self {
            cause,
            stream_cleanup: None,
            state_cleanup: None,
            checked: 0,
            records: 0,
            input_bytes: 0,
            record: None,
            declaration: None,
            kind: None,
        }
    }
    pub(crate) fn selected(&self) -> FailureReport {
        let mut selected = mapped_report(&self.cause);
        for error in [self.stream_cleanup, self.state_cleanup]
            .into_iter()
            .flatten()
        {
            let report = error.failure_report();
            if priority(report) > priority(selected) {
                selected = report;
            }
        }
        selected
    }
}
pub(crate) fn check_with_axiom_policy<R: Read>(
    reader: &mut R,
    decoder: &mut Decoder,
    budget: &mut Budget,
    axiom_policy: crate::AxiomPolicy,
) -> Result<Complete, Stopped> {
    let mut state = match State::new(budget) {
        Ok(state) => state,
        Err(error) => {
            #[cfg(feature = "introspection")]
            budget.capture_failure(crate::report::failure_snapshot::Snapshot::rule_invariant(
                crate::report::failure_snapshot::Rule::Setup,
                (error == ResourceError::Invariant)
                    .then_some(crate::report::failure_snapshot::Invariant::Unavailable),
            ));
            return Err(Stopped::new(Mapped::Consumer(error.failure_report())));
        }
    };
    let mut stream = match Stream::<_, FailureReport>::new(reader, decoder, budget) {
        Ok(stream) => stream,
        Err(error) => {
            #[cfg(feature = "introspection")]
            capture(
                budget,
                decoder.syntax(),
                &[crate::report::failure_snapshot::Rule::Setup],
                matches!(
                    error,
                    crate::decode::framing::FrameError::Resource(ResourceError::Invariant)
                )
                .then_some(crate::report::failure_snapshot::InvariantEvidence {
                    invariant: crate::report::failure_snapshot::Invariant::Unavailable,
                    values: &[],
                }),
            );
            let mut stopped = Stopped::new(Failure::<FailureReport>::Framing(error).facts());
            #[cfg(feature = "introspection")]
            let selected_before_cleanup = stopped.selected();
            stopped.state_cleanup = state.retire(budget).err();
            #[cfg(feature = "introspection")]
            if stopped.selected() != selected_before_cleanup {
                budget.replace_failure(crate::report::failure_snapshot::Snapshot::rule_invariant(
                    crate::report::failure_snapshot::Rule::Cleanup,
                    Some(crate::report::failure_snapshot::Invariant::Cleanup),
                ));
            }
            return Err(stopped);
        }
    };
    let mut attempted = 0u64;
    let mut rejection = None;
    let mut kind;
    budget.switch_bucket(crate::resource::Bucket::Input);
    let result = loop {
        // This is evidence for this callback only, never the preceding record.
        kind = None;
        let next = stream.next(budget, |item, decoder, budget| {
            let declaration_kind = match &item {
                Item::Declaration(request) => Some(match request.kind {
                    Kind::Axiom => DeclarationKind::Axiom,
                    Kind::Definition => DeclarationKind::Definition,
                    Kind::Theorem => DeclarationKind::Theorem,
                    Kind::Opaque => DeclarationKind::Opaque,
                }),
                Item::Inductive(_) => Some(DeclarationKind::Inductive),
                Item::Quotient(_) => Some(DeclarationKind::Quotient),
                Item::Syntax(_) => None,
            };
            if let Some(declaration_kind) = declaration_kind {
                attempted = attempted
                    .checked_add(1)
                    .ok_or_else(|| ResourceError::Counter.failure_report())?;
                kind = Some(declaration_kind);
                let admission = match item {
                    Item::Declaration(request) => state.check_with_axiom_policy(
                        &request,
                        attempted,
                        decoder,
                        budget,
                        axiom_policy,
                    )?,
                    Item::Inductive(request) => {
                        state.check_inductive(&request, attempted, decoder, budget)?
                    }
                    Item::Quotient(request) => {
                        state.check_quotient(&request, attempted, decoder, budget)?
                    }
                    Item::Syntax(_) => return Err(ResourceError::Invariant.failure_report()),
                };
                if admission != Admission::Installed {
                    rejection = Some(Rejection {
                        record: std::num::NonZeroU64::new(budget.progress().records)
                            .ok_or_else(|| ResourceError::Invariant.failure_report())?,
                        declaration: std::num::NonZeroU64::new(attempted)
                            .ok_or_else(|| ResourceError::Counter.failure_report())?,
                        kind: declaration_kind,
                    });
                }
            }
            Ok(())
        });
        match next {
            Ok(Next::End) => break Ok(()),
            Ok(Next::Item(())) if rejection.is_some() => break Ok(()),
            Ok(Next::Header | Next::Item(())) => (),
            Err(error) => {
                #[cfg(feature = "introspection")]
                if !matches!(error, Failure::Consumer(_)) {
                    capture(
                        budget,
                        stream.diagnostic_syntax(),
                        &[crate::report::failure_snapshot::Rule::Decode],
                        None,
                    );
                }
                break Err(error.facts());
            }
        }
    };
    let records = stream.decoded_records();
    let input_bytes = stream.admitted_bytes();
    let record = stream.failure_record();
    // Retire on every terminal path, including an early justified negative.
    // Evaluate both cleanups before choosing their error; neither can be skipped.
    let retained_cleanup = state.retire_retention(budget);
    let stream_cleanup = stream.retire(budget);
    let cleanup = super::super::kernel::select_cleanup([retained_cleanup, stream_cleanup]).err();
    let result_cause = result.err();
    #[cfg(feature = "introspection")]
    let cleanup_supplies_selected = stream_cleanup_selected(result_cause.as_ref(), cleanup);
    let cause = result_cause
        .or_else(|| cleanup.map(|e| Mapped::Consumer(e.failure_report())))
        .or_else(|| {
            if rejection.is_none() {
                state.prefix().err().map(Mapped::Consumer)
            } else {
                None
            }
        });
    if let Some(cause) = cause {
        let mut stopped = Stopped::new(cause);
        #[cfg(feature = "introspection")]
        let selected_before_cleanup = stopped.selected();
        stopped.checked = state.checked;
        stopped.records = records;
        stopped.input_bytes = input_bytes;
        stopped.record = record;
        stopped.declaration = kind.and_then(|_| std::num::NonZeroU64::new(attempted));
        stopped.kind = kind.or_else(|| match cause {
            Mapped::Decoder(facts) => facts.selected().declaration_kind,
            Mapped::Consumer(_) => None,
        });
        stopped.stream_cleanup = cleanup;
        stopped.state_cleanup = state.retire(budget).err();
        #[cfg(feature = "introspection")]
        if cleanup_supplies_selected || stopped.selected() != selected_before_cleanup {
            budget.replace_failure(crate::report::failure_snapshot::Snapshot::rule_invariant(
                crate::report::failure_snapshot::Rule::Cleanup,
                Some(crate::report::failure_snapshot::Invariant::Cleanup),
            ));
        }
        return Err(stopped);
    }
    // Only EOF or a fully validated record with a justified negative reaches here; stream storage
    // retired. A negative owner remains poisoned and can only report that negative;
    // otherwise the state passed prefix validation. No semantic handles escape.
    Ok(Complete {
        state,
        records,
        input_bytes,
        rejection,
    })
}
