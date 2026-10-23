//! Typed resource-cause mapping, not an integrated reporter.
use super::ResourceError;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FailureOutcome {
    Decline,
    InputError,
    InternalError,
}
impl FailureOutcome {
    pub(crate) fn wire_name(self) -> &'static str {
        match self {
            Self::Decline => "decline",
            Self::InputError => "input_error",
            Self::InternalError => "internal_error",
        }
    }
    pub(crate) fn exit_code(self) -> u8 {
        match self {
            Self::Decline => 2,
            Self::InputError | Self::InternalError => 3,
        }
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct FailureReport {
    pub outcome: FailureOutcome,
    pub code: &'static str,
}
impl ResourceError {
    /// Map only the typed semantic cause, without allocation, budget mutation,
    /// diagnostic mode or message parsing. Accept/reject are unrepresentable.
    /// This neither serializes a report nor resolves competing input findings;
    /// the owning reporter must apply the recorded rules and preserve those findings.
    /// Optional diagnostic allocations use their separate ledger, never this map.
    pub(crate) fn failure_report(self) -> FailureReport {
        use FailureOutcome::{Decline, InternalError};
        let (outcome, code) = match self {
            Self::Allocation => (InternalError, "internal.allocation"),
            Self::Invariant => (InternalError, "internal.invariant"),
            Self::InputBytes => (Decline, "resource.input_bytes"),
            Self::RecordBytes => (Decline, "resource.record_bytes"),
            Self::StructureDepth => (Decline, "resource.structure_depth"),
            Self::ContextDepth => (Decline, "resource.context_depth"),
            Self::ReductionPath => (Decline, "resource.reduction_path"),
            Self::Work => (Decline, "resource.work"),
            Self::Storage => (Decline, "resource.storage"),
            Self::Report => (Decline, "resource.report"),
            Self::Counter => (Decline, "resource.counter"),
        };
        FailureReport { outcome, code }
    }
}
