//! Fixed pre-input report storage and single-attempt output; no public run owner.
use crate::resource::{Budget, Event, ResourceError, profile};

pub(crate) struct Emergency {
    bytes: Vec<u8>,
    attempted: bool,
}
#[derive(Debug)]
pub(crate) enum AttemptError {
    MissingBuffer,
    AlreadyAttempted,
    #[allow(
        dead_code,
        reason = "Preserve the concrete reporting failure for diagnostics and regression inspection"
    )]
    Encoding(crate::report::failure_envelope::Error),
    #[allow(
        dead_code,
        reason = "Preserve the concrete reporting failure for diagnostics and regression inspection"
    )]
    Acceptance(crate::report::failure_envelope::acceptance::Failure),
    #[allow(
        dead_code,
        reason = "Preserve the concrete reporting failure for diagnostics and regression inspection"
    )]
    Transport(std::io::Error),
}
impl AttemptError {
    /// No failure of reporting is a proof verdict, even after complete bytes
    /// escaped but the final flush failed. The consumer must preserve mismatch.
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn exit_code(&self) -> u8 {
        3
    }
}
/// Terminal emergency attempt only: the owner must have selected the cause and
/// established identities, and no bytes may previously have escaped on output.
/// Failure returns execution error; never call again or publish another report.
pub(crate) fn attempt(
    emergency: Option<&mut Emergency>,
    envelope: &crate::report::failure_envelope::Envelope<'_>,
    output: &mut impl std::io::Write,
) -> Result<u8, AttemptError> {
    let emergency = emergency.ok_or(AttemptError::MissingBuffer)?;
    if std::mem::replace(&mut emergency.attempted, true) {
        return Err(AttemptError::AlreadyAttempted);
    }
    let prepared = envelope
        .prepare(
            crate::report::failure_envelope::Terminal::new(),
            &mut emergency.bytes,
        )
        .map_err(AttemptError::Encoding)?;
    prepared.publish(output).map_err(AttemptError::Transport)
}
impl Emergency {
    #[allow(
        dead_code,
        reason = "Component retirement witness; terminal run teardown drops the owner"
    )]
    pub(crate) fn retire(self, budget: &mut Budget) -> Result<(), ResourceError> {
        drop(self);
        budget.release(profile::EMERGENCY_BYTES)
    }
}
pub(crate) struct Storage {
    ordinary: Vec<u8>,
    emergency: Emergency,
}
pub(crate) struct Failure {
    pub cause: ResourceError,
    pub emergency: Option<Emergency>,
}
impl Storage {
    /// Originating budget/identity and fresh output stream are caller premises.
    /// The shared attempt is consumed before any encoding or external callback.
    pub(crate) fn publish_acceptance(
        &mut self,
        complete: crate::check::environment::validation::stream::Complete,
        identities: Option<crate::report::failure_envelope::Identities>,
        detail: crate::report::failure_envelope::Detail,
        budget: &mut Budget,
        output: &mut impl std::io::Write,
    ) -> Result<u8, AttemptError> {
        use crate::report::failure_envelope::{Envelope, Frozen, Terminal, acceptance};
        use crate::resource::failure::{FailureOutcome, FailureReport};
        if std::mem::replace(&mut self.emergency.attempted, true) {
            if let Err(error) = complete.retire(budget) {
                return Err(AttemptError::Acceptance(acceptance::Failure {
                    encoding: None,
                    retirement: Some(error),
                }));
            }
            return Err(AttemptError::AlreadyAttempted);
        }
        let snapshot = budget.snapshot();
        let frozen = Frozen {
            checked_declarations: complete.checked(),
            input_bytes: complete.input_bytes(),
            records: complete.records(),
            work_charged: snapshot.work_charged,
            peak_live_capacity_bytes: snapshot.peak_live_capacity_bytes,
        };
        match acceptance::prepare(
            complete,
            identities,
            detail,
            Terminal::new(),
            &mut self.ordinary,
            budget,
        ) {
            Ok(prepared) => prepared.publish(output).map_err(AttemptError::Transport),
            Err(error) => {
                if identities.is_none() {
                    return Err(AttemptError::Acceptance(error));
                }
                let mut failure = FailureReport {
                    outcome: FailureOutcome::InternalError,
                    code: "internal.output",
                };
                if let Some(retirement) = error.retirement {
                    let report = retirement.failure_report();
                    if error.encoding.is_none() || report.outcome == FailureOutcome::InternalError {
                        failure = report;
                    }
                }
                // No ordinary bytes escaped. The held attempt authorizes this
                // one emergency encoding, without recursively entering an owner.
                let fallback = Envelope {
                    failure,
                    identities,
                    frozen,
                    detail,
                    declaration_kind: None,
                    location: None,
                };
                let prepared = fallback
                    .prepare(Terminal::new(), &mut self.emergency.bytes)
                    .map_err(AttemptError::Encoding)?;
                prepared.publish(output).map_err(AttemptError::Transport)
            }
        }
    }
    /// Call once before input, against the session's semantic ledger. A failure
    /// terminates bootstrap; even a retained emergency buffer cannot admit input.
    /// Both allocations are fixed and fully initialized, with no later growth.
    pub(crate) fn bootstrap(budget: &mut Budget) -> Result<Self, Failure> {
        let emergency = Emergency {
            bytes: allocate(profile::EMERGENCY_BYTES, budget).map_err(|cause| Failure {
                cause,
                emergency: None,
            })?,
            attempted: false,
        };
        match allocate(profile::REPORT_BYTES, budget) {
            Ok(ordinary) => Ok(Self {
                ordinary,
                emergency,
            }),
            Err(cause) => Err(Failure {
                cause,
                emergency: Some(emergency),
            }),
        }
    }
    /// Terminal owner for an already selected failure, never accept/reject.
    /// No previous output may exist. The shared attempt flag covers both paths,
    /// including a panic: neither this method nor direct emergency reporting can
    /// subsequently publish another report from this storage.
    pub(crate) fn publish_failure(
        &mut self,
        envelope: &crate::report::failure_envelope::Envelope<'_>,
        budget: Option<&mut Budget>,
        output: &mut impl std::io::Write,
    ) -> Result<crate::resource::failure::FailureOutcome, AttemptError> {
        use crate::report::failure_envelope::{Envelope, Error, Terminal};
        use crate::resource::failure::{FailureOutcome, FailureReport};
        if std::mem::replace(&mut self.emergency.attempted, true) {
            return Err(AttemptError::AlreadyAttempted);
        }
        // An ordinary decline with requested detail first attempts
        // complete retained rows in the ordinary buffer. Any mandatory encoding
        // failure or row unavailability falls through below; rows never reach
        // the emergency envelope and never change the decline.
        #[cfg(feature = "introspection")]
        if let Some(budget) = budget
            && matches!(envelope.failure.outcome, FailureOutcome::Decline)
            && matches!(
                envelope.detail,
                crate::report::failure_envelope::Detail::Unavailable
            )
            && let Ok(prepared) =
                envelope.prepare_decline(Terminal::new(), &mut self.ordinary, budget)
        {
            return prepared
                .publish(output)
                .map(|_| FailureOutcome::Decline)
                .map_err(AttemptError::Transport);
        }
        #[cfg(not(feature = "introspection"))]
        let _ = budget;
        match envelope.prepare(Terminal::new(), &mut self.ordinary) {
            Ok(prepared) => prepared
                .publish(output)
                .map(|_| envelope.failure.outcome)
                .map_err(AttemptError::Transport),
            Err(Error::IdentityMissing) => Err(AttemptError::Encoding(Error::IdentityMissing)),
            Err(Error::InvalidEnvelope | Error::Output) => {
                // No bytes escaped: only the completed emergency envelope may
                // now be published. It cannot inherit invalid optional fields.
                // The enclosing consumed flag authorizes exactly this fallback;
                // do not recursively call attempt or reset that flag.
                let fallback = Envelope {
                    failure: FailureReport {
                        outcome: FailureOutcome::InternalError,
                        code: "internal.output",
                    },
                    identities: envelope.identities,
                    frozen: envelope.frozen,
                    detail: envelope.detail,
                    declaration_kind: None,
                    location: None,
                };
                let prepared = fallback
                    .prepare(Terminal::new(), &mut self.emergency.bytes)
                    .map_err(AttemptError::Encoding)?;
                prepared
                    .publish(output)
                    .map(|_| FailureOutcome::InternalError)
                    .map_err(AttemptError::Transport)
            }
        }
    }
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn emergency(&mut self) -> &mut Emergency {
        &mut self.emergency
    }
    /// The ledger must be the same one used at bootstrap. Call only after all
    /// borrowed encoded/prepared reports have been consumed or abandoned.
    /// Dropping without retirement leaves a conservative charge, never more fuel.
    #[allow(
        dead_code,
        reason = "Component retirement witness; terminal run teardown drops the owner"
    )]
    pub(crate) fn retire(self, budget: &mut Budget) -> Result<(), ResourceError> {
        drop(self);
        budget.release(profile::REPORT_BYTES + profile::EMERGENCY_BYTES)
    }
}
fn allocate(bytes: u64, budget: &mut Budget) -> Result<Vec<u8>, ResourceError> {
    // Fixed profile lengths fit usize on supported targets. Do not truncate if
    // a future target cannot represent them. Charge the whole zero-fill span.
    let len = usize::try_from(bytes).map_err(|_| ResourceError::Counter)?;
    budget.charge_work(bytes.checked_add(1).ok_or(ResourceError::Counter)?)?;
    budget.reserve(bytes)?;
    let mut result = Vec::new();
    if result.try_reserve_exact(len).is_err() {
        budget.release(bytes)?;
        return Err(ResourceError::Allocation);
    }
    // Both fixed bootstrap buffers are nonempty semantic allocations. The
    // event follows allocator success, never budget denial or allocation failure.
    budget.observe(Event::Allocations, 1);
    // Capacity equality establishes that resize cannot allocate, and that the
    // eventual release matches the owned requested layout. An unusual allocator
    // exposing excess capacity cannot continue under an understated ledger.
    if result.capacity() != len {
        drop(result);
        budget.release(bytes)?;
        return Err(ResourceError::Invariant);
    }
    result.resize(len, 0);
    Ok(result)
}
