//! Preserved input findings and stopping causes for reporting. No verdict or
//! semantic verdict selection: the owner must still govern whole-input publication.
use super::Failure;
use crate::decode::export_header;
use crate::decode::framing::FrameError;
use crate::decode::primitive_decode::{Cause, DeclarationKind, Unsupported};
use crate::resource::ResourceError;
use crate::resource::failure::{FailureOutcome, FailureReport};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub(crate) enum InputFinding {
    Io,
    Framing,
    Metadata,
    DuplicateKey,
    Field,
    Reference,
    DuplicateId,
}
impl InputFinding {
    pub(crate) fn report(self) -> FailureReport {
        FailureReport {
            outcome: FailureOutcome::InputError,
            code: match self {
                Self::Io => "input.io",
                Self::Framing => "input.framing",
                Self::Metadata => "input.metadata",
                Self::DuplicateKey => "input.duplicate_key",
                Self::Field => "input.field",
                Self::Reference => "input.reference",
                Self::DuplicateId => "input.duplicate_id",
            },
        }
    }
}
/// Fixed set, not a sequence or a primary-code priority. It retains all facts
/// already observed; absence says nothing about an unread/uninterpreted suffix.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct InputFindings(u8);
impl InputFindings {
    fn insert(&mut self, finding: InputFinding) {
        self.0 |= 1 << finding as u8;
    }
    pub(crate) fn contains(self, finding: InputFinding) -> bool {
        self.0 & (1 << finding as u8) != 0
    }
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn is_empty(self) -> bool {
        self.0 == 0
    }
}
const _: () = assert!(std::mem::size_of::<InputFindings>() == 1);
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct StopReason {
    pub report: FailureReport,
    pub declaration_kind: Option<DeclarationKind>,
}
impl StopReason {
    fn resource(error: ResourceError) -> Self {
        Self {
            report: error.failure_report(),
            declaration_kind: None,
        }
    }
    fn support(code: &'static str, declaration_kind: Option<DeclarationKind>) -> Self {
        Self {
            report: FailureReport {
                outcome: FailureOutcome::Decline,
                code,
            },
            declaration_kind,
        }
    }
}
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Facts {
    pub input: InputFindings,
    /// A stopping support/resource/internal cause may coexist with input facts.
    /// It cannot be serialized as the final result without precedence selection.
    pub stop: Option<StopReason>,
}
const _: () = assert!(std::mem::size_of::<Facts>() <= 48);
impl Facts {
    /// Select only among recorded terminal decoder causes. The fixed input order
    /// is a diagnostic tie rule, not observation chronology or evidence about any
    /// unread suffix. This method neither mutates/discards facts nor installs data.
    /// A mapped consumer failure never enters this selector.
    pub(crate) fn selected(&self) -> StopReason {
        if let Some(stop) = self.stop {
            match stop.report.outcome {
                FailureOutcome::InternalError => return stop,
                FailureOutcome::Decline => {}
                // Construction stores input errors only in the input bitset.
                FailureOutcome::InputError => {
                    return StopReason::resource(ResourceError::Invariant);
                }
            }
        }
        for finding in [
            InputFinding::Io,
            InputFinding::Framing,
            InputFinding::DuplicateKey,
            InputFinding::Metadata,
            InputFinding::Field,
            InputFinding::Reference,
            InputFinding::DuplicateId,
        ] {
            if self.input.contains(finding) {
                return StopReason {
                    report: finding.report(),
                    declaration_kind: None,
                };
            }
        }
        self.stop
            .unwrap_or_else(|| StopReason::resource(ResourceError::Invariant))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Mapped<E> {
    Decoder(Facts),
    /// Consumer semantic/internal causes keep their typed classification; this
    /// decoder adapter cannot reinterpret them as input errors or proof verdicts.
    Consumer(E),
}
impl<E> Failure<E> {
    /// Constant work on the terminal failure path; no allocation, byte scans,
    /// budget mutation, input-derived text or introspection-dependent behavior.
    pub(crate) fn facts(self) -> Mapped<E> {
        let mut facts = Facts::default();
        match self {
            Self::Consumer(error) => return Mapped::Consumer(error),
            Self::MissingHeader => facts.input.insert(InputFinding::Metadata),
            Self::Framing(FrameError::Io(_)) => facts.input.insert(InputFinding::Io),
            Self::Framing(FrameError::Resource(error)) => {
                facts.stop = Some(StopReason::resource(error))
            }
            Self::Header(failure) => {
                if failure.observed.duplicate {
                    facts.input.insert(InputFinding::DuplicateKey);
                }
                // Required header fields are metadata obligations, not ordinary
                // syntax-field errors. Malformed JSON still contributes framing.
                if failure.observed.field {
                    facts.input.insert(InputFinding::Metadata);
                }
                match failure.cause {
                    export_header::Cause::Framing => facts.input.insert(InputFinding::Framing),
                    export_header::Cause::Metadata => facts.input.insert(InputFinding::Metadata),
                    export_header::Cause::UnsupportedField => {
                        facts.stop = Some(StopReason::support("support.field", None))
                    }
                    export_header::Cause::UnsupportedFormat => {
                        facts.stop = Some(StopReason::support("support.format", None))
                    }
                    export_header::Cause::Resource(error) => {
                        facts.stop = Some(StopReason::resource(error))
                    }
                }
            }
            Self::Record {
                failure,
                repeated_metadata,
            } => {
                if repeated_metadata {
                    facts.input.insert(InputFinding::Metadata);
                }
                if failure.observed.shape.duplicate {
                    facts.input.insert(InputFinding::DuplicateKey);
                }
                if failure.observed.shape.field {
                    facts.input.insert(InputFinding::Field);
                }
                if failure.observed.missing_reference {
                    facts.input.insert(InputFinding::Reference);
                }
                match failure.cause {
                    Cause::Framing => facts.input.insert(InputFinding::Framing),
                    Cause::Metadata => facts.input.insert(InputFinding::Metadata),
                    Cause::DuplicateId => facts.input.insert(InputFinding::DuplicateId),
                    Cause::InvalidRecord => {
                        // Decoder construction guarantees one of the three
                        // underlying validation facts for this aggregate cause.
                        if !failure.observed.shape.duplicate
                            && !failure.observed.shape.field
                            && !failure.observed.missing_reference
                        {
                            facts.stop = Some(StopReason::resource(ResourceError::Invariant));
                        }
                    }
                    Cause::NumericRange => {
                        facts.stop = Some(StopReason::support("support.numeric_range", None))
                    }
                    Cause::Resource(error) => facts.stop = Some(StopReason::resource(error)),
                    Cause::Unsupported(unsupported) => {
                        facts.stop = Some(match unsupported {
                            Unsupported::Field => StopReason::support("support.field", None),
                            Unsupported::Record(kind) => {
                                StopReason::support("support.record", Some(kind))
                            }
                        })
                    }
                }
            }
        }
        Mapped::Decoder(facts)
    }
}
