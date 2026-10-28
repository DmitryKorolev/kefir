//! Uncached head phase and full traversal. Session caching is separate.
pub(crate) mod full;
pub(crate) mod machine;
mod string;
pub(crate) mod value;
use super::constant_use::{ConstantUse, DeltaStep};
pub(crate) use super::constant_use::{Mode, UseError};
use super::{Environment, Formation};
use crate::resource::{Budget, Event, ReductionPath, ResourceError};
use crate::syntax::expressions::{
    ExprId, ExprKind, Expressions, binding::Binding, reduction::Step,
};
use crate::syntax::levels::{LevelId, LevelNames, Levels, NameId};
use crate::syntax::local_context::LocalContext;
use crate::syntax::names::Names;
use std::mem::size_of;

/// Fixed validated environment or private checked-signature phase, with original
/// template frontiers. A larger numeric frontier alone grants no staging access.
/// The borrowed normalization owner cannot outlive or mutate this phase.
/// Parameters belong to the same immutable name origin.
#[derive(Clone, Copy)]
pub(crate) struct Scope<'a> {
    pub parameters: &'a [NameId],
    pub before: usize,
    pub formation: Option<Formation>,
    pub mode: Mode,
    pub expression_end: usize,
    pub level_end: usize,
}

const _: () = assert!(size_of::<Scope<'_>>() == 56);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum HeadError {
    Use(UseError),
    Unsupported,
}
impl From<UseError> for HeadError {
    fn from(error: UseError) -> Self {
        Self::Use(error)
    }
}
impl From<ResourceError> for HeadError {
    fn from(error: ResourceError) -> Self {
        Self::Use(error.into())
    }
}
impl From<crate::syntax::expressions::ExpressionError> for HeadError {
    fn from(error: crate::syntax::expressions::ExpressionError) -> Self {
        Self::Use(error.into())
    }
}

/// Only the head route completed. Children beneath binders and neutral
/// applications may still reduce. This is neither a full normal form nor a
/// conversion/typing judgment, even when the returned handle equals the input.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Head {
    pub expression: ExprId,
    pub path: ReductionPath,
}

/// A live head/comparison owner may demand a type only for an operand whose
/// typing derivation is already established in this ordinary session. Driver
/// parents retain that derivation's scope and transported context until resume.
/// This request carries no authority to install a declaration or cache checkedness.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TypeObservation {
    root: ExprId,
    incoming: ReductionPath,
}
impl TypeObservation {
    pub(crate) fn root(&self) -> ExprId {
        self.root
    }
    pub(crate) fn incoming(&self) -> ReductionPath {
        self.incoming
    }
}
const _: () = assert!(size_of::<TypeObservation>() == 8);

/// Evaluation permission belongs to the live head judgment. It is restored when
/// a nested major finishes; it is never inferred from the returned expression.
#[derive(Clone, Copy, Eq, PartialEq)]
pub(crate) enum Exposure {
    /// Hfull: no root delta, but full exposure of projection scrutinees.
    NonDelta,
    Full,
    Cheap,
}

#[derive(Clone, Copy)]
struct Application {
    original: ExprId,
    function: ExprId,
    argument: ExprId,
}
const _: () = assert!(size_of::<Application>() == 12);
impl Application {
    /// Ordinary immutable application edges precede their parent. Equal handles
    /// therefore mark a pending application with no materialized original.
    /// Structure-observation sentinels never pass through ordinary reassembly.
    fn has_original(self) -> bool {
        self.original != self.function
    }
}

/// Suspends an eliminator, projection or exact successor while its operand is exposed.
/// The saved end is a boundary in the same scratch stack, never an expression
/// frontier. Natural frames have exactly one saved argument and do not use the
/// prefix/indices fields. Quotient frames also leave those fields zero; their
/// tag fixes the major position. Projection frames store the original projection
/// root, selected argument position and total constructor arity in these slots.
/// All variants share the same nesting.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Suspension {
    Iota,
    IotaNoStructure,
    StructureType,
    StructureSort,
    K,
    Natural,
    PredicateLeft,
    PredicateRight,
    QuotientLift,
    QuotientInduction,
    Projection,
}
#[derive(Clone, Copy)]
enum SuspensionPayload {
    Layout {
        prefix: u32,
        indices: u32,
    },
    // Only predicate phases own these route values. The saved incoming is an
    // actual parent counter; left_height is measured from it, never a reset.
    Predicate {
        incoming: ReductionPath,
        left_height: u32,
    },
}
#[derive(Clone, Copy)]
struct Iota {
    recursor: ExprId,
    end: u32,
    payload: SuspensionPayload,
    kind: Suspension,
    exposure: Exposure,
}
const _: () = assert!(size_of::<Iota>() == 24);

impl Iota {
    fn layout(self) -> Result<(u32, u32), ResourceError> {
        match self.payload {
            SuspensionPayload::Layout { prefix, indices } => Ok((prefix, indices)),
            SuspensionPayload::Predicate { .. } => Err(ResourceError::Invariant),
        }
    }
}

#[derive(Default)]
struct Scratch {
    applications: Vec<Application>,
    arguments: Vec<LevelId>,
    iota: Vec<Iota>,
    constructor_arguments: Vec<ExprId>,
}
impl Scratch {
    fn suspend_iota(
        &mut self,
        recursor: ExprId,
        prefix: usize,
        indices: u32,
        k: bool,
        exposure: Exposure,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        let frame = Iota {
            recursor,
            end: u32::try_from(self.applications.len()).map_err(|_| ResourceError::Counter)?,
            payload: SuspensionPayload::Layout {
                prefix: u32::try_from(prefix).map_err(|_| ResourceError::Counter)?,
                indices,
            },
            kind: if k { Suspension::K } else { Suspension::Iota },
            exposure,
        };
        self.suspend(frame, b)
    }
    fn suspend_natural(&mut self, head: ExprId, b: &mut Budget) -> Result<(), ResourceError> {
        self.suspend(
            Iota {
                recursor: head,
                end: u32::try_from(self.applications.len()).map_err(|_| ResourceError::Counter)?,
                payload: SuspensionPayload::Layout {
                    prefix: 0,
                    indices: 0,
                },
                kind: Suspension::Natural,
                exposure: Exposure::Full,
            },
            b,
        )
    }
    fn suspend_quotient(
        &mut self,
        head: ExprId,
        lift: bool,
        exposure: Exposure,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        self.suspend(
            Iota {
                recursor: head,
                end: u32::try_from(self.applications.len()).map_err(|_| ResourceError::Counter)?,
                payload: SuspensionPayload::Layout {
                    prefix: 0,
                    indices: 0,
                },
                exposure,
                kind: if lift {
                    Suspension::QuotientLift
                } else {
                    Suspension::QuotientInduction
                },
            },
            b,
        )
    }
    fn suspend_projection(
        &mut self,
        root: ExprId,
        selected: u32,
        arity: u32,
        exposure: Exposure,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        self.suspend(
            Iota {
                recursor: root,
                end: u32::try_from(self.applications.len()).map_err(|_| ResourceError::Counter)?,
                payload: SuspensionPayload::Layout {
                    prefix: selected,
                    indices: arity,
                },
                kind: Suspension::Projection,
                exposure,
            },
            b,
        )
    }
    fn suspend(&mut self, frame: Iota, b: &mut Budget) -> Result<(), ResourceError> {
        b.reserve_frames(1)?;
        let needed = self
            .iota
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        if let Err(error) = b.grow_vec(&mut self.iota, needed) {
            b.release_frames(1)?;
            return Err(error);
        }
        self.iota.push(frame);
        Ok(())
    }
    fn base(&self) -> usize {
        self.iota.last().map_or(0, |frame| frame.end as usize)
    }
    fn push(&mut self, frame: Application, b: &mut Budget) -> Result<(), ResourceError> {
        let count = self
            .applications
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        b.reserve_frames(1)?;
        if let Err(error) = b.grow_vec(&mut self.applications, count) {
            b.release_frames(1)?;
            return Err(error);
        }
        self.applications.push(frame);
        Ok(())
    }
    fn pop(&mut self, b: &mut Budget) -> Result<Option<Application>, ResourceError> {
        let frame = self.applications.pop();
        if frame.is_some() {
            b.release_frames(1)?;
        }
        Ok(frame)
    }
    fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let count = self.applications.len() + self.iota.len();
        let a = release(self.applications, b);
        let c = release(self.arguments, b);
        let e = release(self.iota, b);
        let f = release(self.constructor_arguments, b);
        let d = b.release_frames(count);
        a.and(c).and(e).and(f).and(d)
    }
}
fn release<T: Copy>(values: Vec<T>, b: &mut Budget) -> Result<(), ResourceError> {
    let bytes = values
        .capacity()
        .checked_mul(size_of::<T>())
        .ok_or(ResourceError::Counter)?;
    drop(values);
    b.release(bytes as u64)
}

impl Scope<'_> {
    fn validate_formation(&self, environment: &Environment) -> Result<(), ResourceError> {
        if self.formation.is_some() {
            environment.check_scope(
                self.before,
                self.formation,
                self.expression_end,
                self.level_end,
            )?;
        }
        Ok(())
    }
    /// Transport a constant's original validated type, never its value. The
    /// immutable environment invariant and same-origin frontiers are required.
    /// Copy argument handles before mutable transport can grow expression lists.
    pub(crate) fn constant_type(
        &self,
        root: ExprId,
        environment: &Environment,
        expressions: &mut Expressions,
        levels: &mut Levels,
        names: &Names,
        budget: &mut Budget,
    ) -> Result<ExprId, HeadError> {
        self.validate_formation(environment)?;
        budget.charge_work(1)?; // prepay the one flat argument-vector release
        let mut arguments = Vec::new();
        let result = (|| {
            let ExprKind::Constant(name, raw) =
                expressions
                    .get(root, budget)?
                    .kind(expressions, levels, budget)?
            else {
                return Err(HeadError::Unsupported);
            };
            budget.charge_work(raw.len() as u64 + 1)?;
            budget.grow_vec(&mut arguments, raw.len())?;
            arguments.extend_from_slice(raw);
            environment
                .instantiate_type(
                    ConstantUse {
                        name,
                        arguments: &arguments,
                        parameters: self.parameters,
                        before: self.before,
                        formation: self.formation,
                        mode: self.mode,
                        expression_end: self.expression_end,
                        level_end: self.level_end,
                    },
                    expressions,
                    levels,
                    names,
                    budget,
                )
                .map_err(HeadError::from)
        })();
        let cleanup = release(arguments, budget).err().map(HeadError::from);
        match full::select_failure([result.as_ref().err().copied(), cleanup, None, None]) {
            Some(error) => Err(error),
            None => result,
        }
    }
    /// Caller supplies checked syntax with no loose variables, validated active
    /// locals, and the environment's validated-entry invariant. In particular,
    /// let types/values were checked BEFORE calling: zeta cannot validate them.
    /// Local types/values are immutable and depend only on prior active locals.
    /// No caller may reuse generated syntax after declaration watermark retirement.
    /// Any error requires declaration abort; a panic requires run/ledger discard.
    /// No cache is consulted or populated, and no partial result escapes failure.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn expose(
        &self,
        root: ExprId,
        path: ReductionPath,
        environment: &Environment,
        expressions: &mut Expressions,
        levels: &mut Levels,
        names: &Names,
        locals: &LocalContext,
        b: &mut Budget,
    ) -> Result<Head, HeadError> {
        self.validate_formation(environment)?;
        let mut machine = machine::Machine::new(root, path, Exposure::Full, b)?;
        let result = (|| loop {
            if let Some(head) =
                machine.advance(self, environment, expressions, levels, names, locals, b)?
            {
                return Ok(head);
            }
            if machine.major_request().is_some() || machine.comparison_request().is_some() {
                return Err(HeadError::Unsupported);
            }
        })();
        // No result survives a failed machine retirement.
        machine.retire(b)?;
        result
    }
}
