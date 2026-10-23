//! Typed-store integration for real 3.1.0 names, levels and an expression subset.
//! No header/session policy or proof verdict. The declaration child module
//! constructs temporary requests without semantic validation or installation.
//! Other shapes receive grammar/schema/prior-reference checks before this slice
//! declines them; no semantic checking is implied.
use crate::decode::identifiers::{IdIndex, IndexError};
use crate::decode::record_references::{CheckedShape, Resolved};
use crate::decode::record_validation::Findings;
use crate::resource::{Budget, ResourceError};
use crate::syntax::expressions::{BinderInfo, ExprId, ExprKind, ExpressionError, Expressions};
use crate::syntax::levels::{LevelId, LevelKind, Levels, NameId};
use crate::syntax::names::{Component, NameError, Names};

pub(crate) mod ordinary_session;
mod typed;

// Group transport conveys schema/reference validity only, never admission.
pub(crate) mod inductives;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Published {
    Name(NameId),
    Level(LevelId),
    Expr(ExprId),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Cause {
    Resource(ResourceError),
    Framing,
    InvalidRecord,
    Metadata,
    DuplicateId,
    Unsupported(Unsupported),
    NumericRange,
}
/// Bounded support classification; input-derived tag text is never retained.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Unsupported {
    Field,
    Record(DeclarationKind),
}
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) enum DeclarationKind {
    Axiom,
    Definition,
    Theorem,
    Opaque,
    Quotient,
    Inductive,
    #[default]
    Unknown,
}
impl DeclarationKind {
    pub(crate) fn wire(self) -> &'static str {
        match self {
            Self::Axiom => "axiom",
            Self::Definition => "def",
            Self::Theorem => "thm",
            Self::Opaque => "opaque",
            Self::Quotient => "quot",
            Self::Inductive => "inductive",
            Self::Unknown => "unknown",
        }
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Failure {
    /// Observed input errors must not be lost when cause is a later decline.
    pub observed: CheckedShape,
    pub cause: Cause,
}
fn empty() -> CheckedShape {
    CheckedShape {
        shape: Findings::default(),
        missing_reference: false,
    }
}
fn resource(error: ResourceError) -> Failure {
    Failure {
        observed: empty(),
        cause: Cause::Resource(error),
    }
}
fn index_error(error: IndexError) -> Cause {
    match error {
        IndexError::Resource(e) => Cause::Resource(e),
        IndexError::Duplicate => Cause::DuplicateId,
        _ => Cause::Resource(ResourceError::Invariant),
    }
}
#[derive(Clone, Copy)]
enum Kind {
    Str,
    Num,
    Succ,
    Max,
    IMax,
    Param,
    Bvar,
    Sort,
    App,
    NatVal,
    StrVal,
    Lambda,
    Pi,
    Let,
    Projection,
    Constant,
    MData,
}
// Four fixed child slots cost 32 bytes per active record, not per stored node.
const _: () = assert!(std::mem::size_of::<Option<Resolved>>() == 8);
#[derive(Clone, Copy)]
enum PendingComponent<'a> {
    // All constructors borrow an already validated Rust string. UTF-8 only;
    // this grants no JSON/schema validity or semantic authority.
    Text(&'a str),
    Number(&'a [u8]),
    Boolean(bool),
}
#[derive(Default)]
struct Pending<'a> {
    kind: Option<Kind>,
    unsupported_kind: DeclarationKind,
    id: Option<&'a [u8]>,
    // Record-local lexical fact only; never a slot or a checkedness certificate.
    id_number: Option<u32>,
    component: Option<PendingComponent<'a>>,
    refs: [Option<Resolved>; 4],
}
#[derive(Default)]
pub(crate) struct Scratch {
    universes: Vec<LevelId>,
    declaration: declarations::Payload,
    inductive: inductives::Payload,
}
impl Scratch {
    pub(crate) fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let bytes = self.universes.capacity() * std::mem::size_of::<LevelId>();
        drop(self.universes);
        let e = self.declaration.retire(b);
        let e = e.and(self.inductive.retire(b));
        e.and(b.release(bytes as u64))
    }
}
/// Tables and indices have one owner/origin. Intrinsic zeros are constructed
/// together; expression zero is not intrinsic and is published only by a record.
/// Any failure is terminal: an append followed by failed ID insertion may leave
/// an unreachable raw node, never a published mapping or reusable session.
pub(crate) struct Decoder {
    names: Names,
    levels: Levels,
    expressions: Expressions,
    name_ids: IdIndex,
    // Serialized name ordinals exclude the one persistent quotient-name gap.
    name_gap: [u32; 2],
    level_ids: IdIndex,
    expression_ids: IdIndex,
    failure: Option<Failure>,
    // Current-record observation retained even if later parsing exhausts a budget.
    metadata_seen: bool,
}
pub(crate) enum Item<'a> {
    #[allow(
        dead_code,
        reason = "Published syntax identity is retained for decoder consumers and regressions"
    )]
    Syntax(Published),
    Declaration(declarations::Request<'a>),
    Inductive(inductives::Request<'a>),
    Quotient(quotients::Request<'a>),
}
enum Parsed {
    Syntax(Published),
    Declaration(declarations::Fields),
    Inductive,
    Quotient(quotients::Fields),
}
impl Decoder {
    /// Read-only original syntax access for the owning semantic validator.
    /// Handles retain this decoder's origin; availability is not checkedness.
    pub(crate) fn syntax(&self) -> (&Names, &Levels, &Expressions) {
        (&self.names, &self.levels, &self.expressions)
    }

    pub(crate) fn new(b: &mut Budget) -> Result<Self, ResourceError> {
        Ok(Self {
            names: Names::new(b)?,
            levels: Levels::new(b)?,
            expressions: Expressions::default(),
            name_ids: IdIndex::new(true),
            name_gap: [0, 0],
            level_ids: IdIndex::new(true),
            expression_ids: IdIndex::new(false),
            failure: None,
            metadata_seen: false,
        })
    }
    /// One grammar/reference pass selects syntax or a temporary declaration.
    /// The fixed-chunk framer must precharge all record bytes before this call;
    /// lexical scans rely on that invariant. Input spans cannot survive scratch
    /// reuse: syntax owns copied payloads and requests borrow owned scratch.
    /// No declaration request conveys checkedness or grants installation.
    pub(crate) fn item<'a>(
        &mut self,
        input: &[u8],
        scratch: &'a mut Scratch,
        b: &mut Budget,
    ) -> Result<Item<'a>, Failure> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        self.metadata_seen = false;
        match self.decode(input, scratch, b) {
            Ok(Parsed::Syntax(published)) => Ok(Item::Syntax(published)),
            Ok(Parsed::Quotient(fields)) => Ok(Item::Quotient(quotients::Request {
                role: fields.role,
                name: fields.name,
                ty: fields.ty,
                parameters: &scratch.declaration.parameters,
            })),
            Ok(Parsed::Inductive) => Ok(Item::Inductive(scratch.inductive.request())),
            Ok(Parsed::Declaration(fields)) => {
                Ok(Item::Declaration(scratch.declaration.request(fields)))
            }
            Err(error) => {
                self.failure = Some(error);
                Err(error)
            }
        }
    }
    fn decode(
        &mut self,
        input: &[u8],
        scratch: &mut Scratch,
        b: &mut Budget,
    ) -> Result<Parsed, Failure> {
        self.typed_decode(input, scratch, b)
    }
    fn publish(
        &mut self,
        pending: Pending<'_>,
        observed: CheckedShape,
        universes: &[LevelId],
        b: &mut Budget,
    ) -> Result<Published, Failure> {
        let fail = |cause| Failure { observed, cause };
        if observed.shape.duplicate || observed.shape.field || observed.missing_reference {
            return Err(fail(Cause::InvalidRecord));
        }
        let kind = pending.kind.ok_or_else(|| {
            fail(Cause::Unsupported(if observed.shape.unknown_record {
                Unsupported::Record(DeclarationKind::Unknown)
            } else if observed.shape.extension {
                Unsupported::Field
            } else {
                Unsupported::Record(pending.unsupported_kind)
            }))
        })?;
        let id = pending
            .id
            .ok_or_else(|| fail(Cause::Resource(ResourceError::Invariant)))?;
        let index = match kind {
            Kind::Str | Kind::Num => &self.name_ids,
            Kind::Succ | Kind::Max | Kind::IMax | Kind::Param => &self.level_ids,
            _ => &self.expression_ids,
        };
        let duplicate = match pending.id_number {
            Some(number) => index.resolve_canonical_u32(id, number, b),
            None => index.resolve(id, b),
        };
        if duplicate.map_err(|e| fail(index_error(e)))?.is_some() {
            return Err(fail(Cause::DuplicateId));
        }
        let insert_id = |index: &mut IdIndex, slot: u32, b: &mut Budget| match pending.id_number {
            Some(number) => index.insert_canonical_u32(id, number, slot, b),
            None => index.insert(id, slot, b),
        };
        if observed.shape.extension || observed.shape.unknown_record {
            return Err(fail(Cause::Unsupported(Unsupported::Field)));
        }
        // Complete, duplicate-free schema validation guarantees these captured
        // positions are exactly the constructor's required component/references.
        // Names/param have one Name reference; succ and ordered max/imax children
        // have Level references. No extension or conflicting tag reaches append.
        let first = || {
            pending.refs[0]
                .map(|r| r.slot)
                .ok_or_else(|| fail(Cause::Resource(ResourceError::Invariant)))
        };
        let result = match kind {
            Kind::Str | Kind::Num => {
                let prefix = self
                    .names
                    .resolve_slot(first()?, b)
                    .map_err(|e| fail(Cause::Resource(e)))?;
                let component = pending
                    .component
                    .ok_or_else(|| fail(Cause::Resource(ResourceError::Invariant)))?;
                let component = match (kind, component) {
                    (Kind::Str, PendingComponent::Text(text)) => Component::String(text),
                    (Kind::Num, PendingComponent::Number(number)) => Component::Number(number),
                    _ => return Err(fail(Cause::Resource(ResourceError::Invariant))),
                };
                let name = self.names.append(prefix, component, b).map_err(|e| {
                    fail(match e {
                        NameError::Resource(e) => Cause::Resource(e),
                        NameError::NumericRange => Cause::NumericRange,
                        NameError::InvalidNumber => Cause::Resource(ResourceError::Invariant),
                    })
                })?;
                let ordinal = self
                    .imported_name_ordinal(name.0)
                    .map_err(|e| fail(Cause::Resource(e)))?;
                insert_id(&mut self.name_ids, ordinal, b).map_err(|e| fail(index_error(e)))?;
                Published::Name(name)
            }
            Kind::Succ | Kind::Max | Kind::IMax | Kind::Param => {
                let value = match kind {
                    Kind::Param => LevelKind::Param(
                        self.names
                            .resolve_slot(first()?, b)
                            .map_err(|e| fail(Cause::Resource(e)))?,
                    ),
                    Kind::Succ => LevelKind::Succ(
                        self.levels
                            .resolve_slot(first()?, b)
                            .map_err(|e| fail(Cause::Resource(e)))?,
                    ),
                    Kind::Max | Kind::IMax => {
                        let second = pending.refs[1]
                            .ok_or_else(|| fail(Cause::Resource(ResourceError::Invariant)))?
                            .slot;
                        let a = self
                            .levels
                            .resolve_slot(first()?, b)
                            .map_err(|e| fail(Cause::Resource(e)))?;
                        let c = self
                            .levels
                            .resolve_slot(second, b)
                            .map_err(|e| fail(Cause::Resource(e)))?;
                        if matches!(kind, Kind::Max) {
                            LevelKind::Max(a, c)
                        } else {
                            LevelKind::IMax(a, c)
                        }
                    }
                    _ => unreachable!(),
                };
                let level = self
                    .levels
                    .append(value, &self.names, b)
                    .map_err(|e| fail(Cause::Resource(e)))?;
                insert_id(&mut self.level_ids, level.slot(), b)
                    .map_err(|e| fail(index_error(e)))?;
                Published::Level(level)
            }
            Kind::Bvar
            | Kind::Sort
            | Kind::App
            | Kind::NatVal
            | Kind::StrVal
            | Kind::Lambda
            | Kind::Pi
            | Kind::Let
            | Kind::Projection
            | Kind::Constant
            | Kind::MData => {
                // Valid schemas fix the named slots: name/type/body/value for
                // binders and lets, typeName/struct for projections. Their order
                // in JSON is irrelevant. These handles remain syntax only.
                let expr = |position: usize, b: &mut Budget| {
                    let slot = pending.refs[position]
                        .ok_or_else(|| fail(Cause::Resource(ResourceError::Invariant)))?
                        .slot;
                    self.expressions
                        .resolve_slot(slot, b)
                        .map_err(|e| fail(Cause::Resource(e)))
                };
                let appended = if matches!(kind, Kind::App) {
                    // Preserve Pending presence checks and fn-then-arg resolution
                    // before the construction charge and common ID insertion.
                    let second = pending.refs[1]
                        .ok_or_else(|| fail(Cause::Resource(ResourceError::Invariant)))?
                        .slot;
                    let function = self
                        .expressions
                        .resolve_slot(first()?, b)
                        .map_err(|e| fail(Cause::Resource(e)))?;
                    let argument = self
                        .expressions
                        .resolve_slot(second, b)
                        .map_err(|e| fail(Cause::Resource(e)))?;
                    self.expressions.append_application(function, argument, b)
                } else {
                    let value = match kind {
                        Kind::Bvar => {
                            let digits = match pending
                                .component
                                .ok_or_else(|| fail(Cause::Resource(ResourceError::Invariant)))?
                            {
                                PendingComponent::Number(digits) => digits,
                                _ => return Err(fail(Cause::Resource(ResourceError::Invariant))),
                            };
                            let index = digits
                                .iter()
                                .try_fold(0u32, |n, digit| {
                                    n.checked_mul(10)?.checked_add(u32::from(digit - b'0'))
                                })
                                .ok_or_else(|| fail(Cause::NumericRange))?;
                            ExprKind::Bound(index)
                        }
                        Kind::Sort => ExprKind::Sort(
                            self.levels
                                .resolve_slot(first()?, b)
                                .map_err(|e| fail(Cause::Resource(e)))?,
                        ),
                        Kind::App => {
                            // Named fields determine fn/arg positions; JSON member
                            // order must not reverse the application graph.
                            let second = pending.refs[1]
                                .ok_or_else(|| fail(Cause::Resource(ResourceError::Invariant)))?
                                .slot;
                            ExprKind::App(
                                self.expressions
                                    .resolve_slot(first()?, b)
                                    .map_err(|e| fail(Cause::Resource(e)))?,
                                self.expressions
                                    .resolve_slot(second, b)
                                    .map_err(|e| fail(Cause::Resource(e)))?,
                            )
                        }
                        Kind::Constant => ExprKind::Constant(
                            self.names
                                .resolve_slot(first()?, b)
                                .map_err(|e| fail(Cause::Resource(e)))?,
                            universes,
                        ),
                        Kind::Lambda | Kind::Pi => {
                            let Some(PendingComponent::Text(text)) = pending.component else {
                                return Err(fail(Cause::Resource(ResourceError::Invariant)));
                            };
                            let binder = match text {
                                "default" => BinderInfo::Default,
                                "implicit" => BinderInfo::Implicit,
                                "strictImplicit" => BinderInfo::StrictImplicit,
                                "instImplicit" => BinderInfo::InstanceImplicit,
                                _ => return Err(fail(Cause::Resource(ResourceError::Invariant))),
                            };
                            let name = self
                                .names
                                .resolve_slot(first()?, b)
                                .map_err(|e| fail(Cause::Resource(e)))?;
                            if matches!(kind, Kind::Lambda) {
                                ExprKind::Lambda(name, expr(1, b)?, expr(2, b)?, binder)
                            } else {
                                ExprKind::Pi(name, expr(1, b)?, expr(2, b)?, binder)
                            }
                        }
                        Kind::Let => {
                            let Some(PendingComponent::Boolean(nondep)) = pending.component else {
                                return Err(fail(Cause::Resource(ResourceError::Invariant)));
                            };
                            ExprKind::Let(
                                self.names
                                    .resolve_slot(first()?, b)
                                    .map_err(|e| fail(Cause::Resource(e)))?,
                                expr(1, b)?,
                                expr(3, b)?,
                                expr(2, b)?,
                                nondep,
                            )
                        }
                        Kind::Projection => {
                            let digits = match pending
                                .component
                                .ok_or_else(|| fail(Cause::Resource(ResourceError::Invariant)))?
                            {
                                PendingComponent::Number(digits) => digits,
                                _ => return Err(fail(Cause::Resource(ResourceError::Invariant))),
                            };
                            let index = digits
                                .iter()
                                .try_fold(0u32, |n, digit| {
                                    n.checked_mul(10)?.checked_add(u32::from(digit - b'0'))
                                })
                                .ok_or_else(|| fail(Cause::NumericRange))?;
                            ExprKind::Projection(
                                self.names
                                    .resolve_slot(first()?, b)
                                    .map_err(|e| fail(Cause::Resource(e)))?,
                                index,
                                expr(1, b)?,
                            )
                        }
                        Kind::NatVal | Kind::StrVal => {
                            let Some(PendingComponent::Text(bytes)) = pending.component else {
                                return Err(fail(Cause::Resource(ResourceError::Invariant)));
                            };
                            if matches!(kind, Kind::NatVal) {
                                ExprKind::Natural(bytes.as_bytes())
                            } else {
                                ExprKind::String(bytes.as_bytes())
                            }
                        }
                        Kind::MData => {
                            // The payload was validated as a JSON object
                            // before any node exists; append copies it verbatim.
                            let Some(PendingComponent::Text(payload)) = pending.component else {
                                return Err(fail(Cause::Resource(ResourceError::Invariant)));
                            };
                            ExprKind::MData(payload.as_bytes(), expr(0, b)?)
                        }
                        _ => unreachable!("expression kind matched above"),
                    };
                    self.expressions.append(value, &self.levels, &self.names, b)
                };
                let expression = appended.map_err(|error| {
                    fail(match error {
                        ExpressionError::Resource(error) => Cause::Resource(error),
                        ExpressionError::NumericRange => Cause::NumericRange,
                        ExpressionError::InvalidNatural | ExpressionError::InvalidString => {
                            Cause::Resource(ResourceError::Invariant)
                        }
                    })
                })?;
                insert_id(&mut self.expression_ids, expression.slot(), b)
                    .map_err(|e| fail(index_error(e)))?;
                Published::Expr(expression)
            }
        };
        Ok(result)
    }
}

pub(crate) mod declarations;
pub(crate) mod quotients;

pub(crate) mod stream;

pub(super) fn decode_header(
    input: &[u8],
    b: &mut Budget,
) -> Result<crate::decode::export_header::Header, crate::decode::export_header::Failure> {
    typed::header(input, b)
}

#[cfg(target_pointer_width = "64")]
const _: () = assert!(std::mem::size_of::<PendingComponent>() == 24);
#[cfg(target_pointer_width = "64")]
const _: () = assert!(std::mem::size_of::<Pending>() == 88);
