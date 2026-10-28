//! Checked-type comparison that retains its completed-normalization cache while
//! an ordinary head or major-type judgment is demanded. The outer driver fixes
//! scope, store origins, permissions and the incoming active local context for
//! this owner's lifetime. Child judgments must restore that context on success;
//! no handle or completed cache entry escapes declaration retirement.
mod constructor;
mod delta;
mod natural;
mod projection;
mod quotient;
mod reflection;
mod same_definition;
mod spine;
use super::{Normal, Scope, cache, machine, positive, select_failure};
use crate::check::environment::CheckednessMint;
use crate::check::environment::Environment;
use crate::check::environment::normalization::{Head, HeadError, TypeObservation};
use crate::resource::{Budget, ReductionPath, ResourceError, SessionCacheBudget};
use crate::syntax::expressions::{ExprId, ExprKind, Expressions, binding::Binding};
use crate::syntax::levels::{LevelZero, Levels, SharedMemo, SharedTable, UniverseComparison};
use crate::syntax::local_context::{CheckedTy, FreeId, LocalContext};
use crate::syntax::names::Names;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Evidence {
    Sort,
    SortPi,
    Natural,
    DistinctLocals,
    RigidArguments,
    ConstructorArguments,
    LocalConstructor,
    LocalApplication,
    FunctionEta,
    RecursorLocal,
    RecursorZero,
    RecursorProjection,
    LocalProjection,
    DistinctConstructors,
    RigidConstants,
    NoRule,
    QuotientLocal,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Decision {
    Equal(ReductionPath),
    Different(Evidence),
}
const _: () = assert!(std::mem::size_of::<Decision>() == 8);
struct Binders {
    locals: Vec<FreeId>,
    result: Decision,
}
const _: () = assert!(std::mem::size_of::<Binders>() == 32);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Demand {
    Head {
        root: ExprId,
        incoming: ReductionPath,
    },
    NonDeltaHead {
        root: ExprId,
        incoming: ReductionPath,
    },
    CheapHead {
        root: ExprId,
        incoming: ReductionPath,
    },
    Comparison {
        left: ExprId,
        right: ExprId,
        incoming: ReductionPath,
    },
    Observation(TypeObservation),
    Complete(Decision),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Phase {
    Initial,
    Prefix,
    Reflection,
    ReflectionDone,
    CheapLeft,
    CheapRight,
    ObserveLeft,
    ObserveType,
    ExposeSort,
    Classify,
    ObserveRight,
    ProofCompare,
    ProofDone,
    NaturalPredecessors,
    Paired,
    Arithmetic,
    PairedUnfold,
    SameDefinition,
    InconclusiveFallback,
    InconclusiveLeft,
    InconclusiveRight,
    PairedProjectionLeft,
    PairedProjectionRight,
    FullProjectionLeft,
    FullProjectionRight,
    FullProjectionRightUnchanged,
    PairedLeft,
    PairedRight,
    PairedPrefix,
    Rigid,
    QuotientLeft,
    QuotientRight,
    QuotientRightUnchanged,
    QuotientTypeExpose,
    QuotientTypeClassify,
    ProjectionDelta,
    ProjectionSourceLeft,
    ProjectionSourceRight,
    ProjectionSelect,
    ProjectionCompare,
    ProjectionRetryLeft,
    ProjectionRetryRight,
    ProjectionRetryRightUnchanged,
    EtaFullLeft,
    EtaFullRight,
    EtaFullRightUnchanged,
    EtaReady,
    LocalPrefix,
    LocalPrefixSuccess,
    LocalPrefixDifferent,
    LocalPrefixFailed,
    Arguments,
    PositiveArguments,
    ConstructorArguments,
    GeneralStructureArguments,
    GeneralStructureUnequalArguments,
    GeneralStructurePrepare,
    GeneralStructureClassify,
    ConstructorRightPrepare,
    ConstructorLeftPrepare,
    ConstructorFailedExpose,
    ConstructorFailedClassify,
    UnequalArguments,
    UnitExpose,
    UnitClassify,
    UnitRight,
    UnitCompare,
    GeneralUnitRight,
    GeneralUnitCompare,
    ArgumentTypeExpose,
    ArgumentTypeClassify,
    EtaLeftObserve,
    EtaRightObserve,
    EtaLeftExpose,
    EtaRightExpose,
    EtaLeftBuild,
    EtaRightBuild,
    EtaCompare,
    EtaApplicationCompare,
    StructureLeftObserve,
    StructureRightObserve,
    StructureLeftCompare,
    StructureRightCompare,
    StructureLeftExpose,
    StructureRightExpose,
    StructureLeftBuild,
    StructureRightBuild,
    StructureFields,
    LocalConstructorExpose,
    LocalConstructorClassify,
    LocalApplicationExpose,
    LocalApplicationClassify,
    FunctionEtaFailedExpose,
    FunctionEtaFailedClassify,
    DistinctConstructorsExpose,
    RigidConstantsExpose,
    NoRuleExpose,
    DistinctConstructorsClassify,
    RigidConstantsClassify,
    NoRuleClassify,
    RecursorLocalExpose,
    RecursorZeroExpose,
    RecursorProjectionExpose,
    LocalProjectionExpose,
    RecursorLocalClassify,
    RecursorZeroClassify,
    RecursorProjectionClassify,
    LocalProjectionClassify,
    Fallback,
    Domain,
    Open,
    Left,
    Right,
    Complete,
}

const _: () = assert!(std::mem::size_of::<Phase>() == 1);

#[derive(Clone, Copy, Eq, PartialEq)]
enum QuotientHistory {
    Unclassified,
    Inapplicable,
    Admitted,
}

#[derive(Clone, Copy)]
struct OptionalRoute {
    incoming: ReductionPath,
    required: ReductionPath,
}

enum Auxiliary {
    Empty,
    Arithmetic(natural::primitive::Primitive),
    Normal(machine::Machine),
    Constructor(constructor::Attempt),
    GeneralStructure(constructor::Attempt),
    Projection(projection::Attempt),
}
impl Auxiliary {
    fn as_mut(&mut self) -> Option<&mut machine::Machine> {
        match self {
            Self::Normal(normal) => Some(normal),
            _ => None,
        }
    }
    fn take(&mut self) -> Option<machine::Machine> {
        match std::mem::replace(self, Self::Empty) {
            Self::Normal(normal) => Some(normal),
            _ => None,
        }
    }
    fn is_constructor(&self) -> bool {
        matches!(self, Self::Constructor(_) | Self::GeneralStructure(_))
    }
    fn constructor(&mut self) -> Result<&mut constructor::Attempt, HeadError> {
        match self {
            Self::Constructor(attempt) | Self::GeneralStructure(attempt) => Ok(attempt),
            _ => Err(ResourceError::Invariant.into()),
        }
    }
}

/// Scoped to one ordinary driver, never a semantic result or a cache.
#[derive(Clone, Copy, Eq, PartialEq)]
pub(crate) enum PrefixTrial {
    Enabled,
    Disabled,
}

pub(crate) struct Machine {
    cache: cache::Cache,
    auxiliary: Auxiliary,
    left_normal: Option<Normal>,
    observed: Option<Head>,
    arguments: Vec<(ExprId, ExprId)>,
    left: ExprId,
    right: ExprId,
    incoming: ReductionPath,
    phase: Phase,
    failure: Option<HeadError>,
    waiting: bool,
    exposed: bool,
    delta_sides: u8,
    /// Set when an optional same-definition argument shortcut was locally
    /// unsupported and this comparison continued by lazy unfolding, or when a
    /// head this owner demanded resumed after an unestablished K premise.
    /// The unresolved equality possibility is retained for the whole
    /// comparison, so this owner may finish only Equal (or fail Unsupported),
    /// never Different.
    inconclusive: bool,
    // Scoped pre-C8 pre-exposure same-definition argument congruence history, independent of sticky uncertainty. Any
    // earlier admitted same-definition candidate permanently bars this narrow
    // negative attempt, even after changed heads or completed failed children.
    quotient_history: QuotientHistory,
    binders: Binders,
    optional_route: Option<OptionalRoute>,
}
// No new imported-node field or per-entry storage. The driver charges this
// constant-sized owner only when storing a live suspended comparison job.
const _: () = assert!(std::mem::size_of::<Machine>() == 232);

/// Same setup for a stored comparison and an immediately completed C1 demand.
pub(crate) fn prepare_checked(
    scope: &Scope<'_>,
    environment: &Environment,
    budget: &mut Budget,
) -> Result<(), HeadError> {
    scope.validate_formation(environment)?;
    budget.charge_work(1)?;
    Ok(())
}

/// Caller has checked both operands in this scope and completed prepare_checked.
/// No owner, cache or local exists; both reads still pass through ordinary C1.
pub(crate) fn checked_identity(
    root: ExprId,
    incoming: ReductionPath,
    expressions: &Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Decision, HeadError> {
    positive::compare_structure(
        root,
        root,
        positive::LevelRule::Identity(levels),
        expressions,
        names,
        budget,
    )?;
    Ok(Decision::Equal(incoming))
}

impl Machine {
    pub(crate) fn new(
        left: ExprId,
        right: ExprId,
        incoming: ReductionPath,
        scope: &Scope<'_>,
        environment: &Environment,
        budget: &mut Budget,
    ) -> Result<Self, HeadError> {
        prepare_checked(scope, environment, budget)?;
        Ok(Self {
            cache: cache::Cache::default(),
            auxiliary: Auxiliary::Empty,
            left_normal: None,
            observed: None,
            arguments: Vec::new(),
            left,
            right,
            incoming,
            phase: Phase::Initial,
            failure: None,
            waiting: false,
            exposed: false,
            delta_sides: 0,
            inconclusive: false,
            quotient_history: QuotientHistory::Unclassified,
            optional_route: None,
            binders: Binders {
                locals: Vec::new(),
                result: Decision::Equal(incoming),
            },
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn advance_with_prefix(
        &mut self,
        scope: &Scope<'_>,
        environment: &Environment,
        expressions: &mut Expressions,
        levels: &mut Levels,
        names: &Names,
        locals: &mut LocalContext,
        ledger: &mut SessionCacheBudget,
        budget: &mut Budget,
        universes: &mut SharedMemo,
        prefix_trial: &mut PrefixTrial,
    ) -> Result<Demand, HeadError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if self.waiting || self.phase == Phase::Complete {
            let error = ResourceError::Invariant.into();
            self.failure = Some(error);
            return Err(error);
        }
        // A caught unwind cannot make this owner reusable. Only a successful
        // completed result or an explicit demand clears this operation poison.
        self.failure = Some(ResourceError::Invariant.into());
        let result = (|| loop {
            if self.phase == Phase::ReflectionDone {
                let head = self.observed.take().ok_or(ResourceError::Invariant)?;
                if reflection::result_is_true(
                    head.expression,
                    self.right,
                    expressions,
                    levels,
                    names,
                    budget,
                )? {
                    return self.finish(Decision::Equal(head.path), locals, ledger, budget);
                }
                self.incoming = head.path;
                self.phase = Phase::CheapLeft;
                self.waiting = true;
                return Ok(Demand::CheapHead {
                    root: self.left,
                    incoming: self.incoming,
                });
            }

            if self.phase == Phase::Initial {
                match positive::compare_structure(
                    self.left,
                    self.right,
                    positive::LevelRule::Identity(levels),
                    expressions,
                    names,
                    budget,
                ) {
                    Ok(()) => {
                        return self.finish(Decision::Equal(self.incoming), locals, ledger, budget);
                    }
                    // No C1 evidence; the existing normalization route remains.
                    Err(HeadError::Unsupported) => {}
                    Err(error) => return Err(error),
                }
                self.phase = Phase::Prefix;
            }
            if self.phase == Phase::Open {
                if let Decision::Different(evidence) = self.binders.result {
                    return self.finish(Decision::Different(evidence), locals, ledger, budget);
                }
                let (right_name, right_domain, right_body, annotation) = match expressions
                    .get(self.right, budget)?
                    .kind(expressions, levels, budget)?
                {
                    ExprKind::Pi(name, domain, body, annotation)
                    | ExprKind::Lambda(name, domain, body, annotation) => {
                        (name, domain, body, annotation)
                    }
                    _ => return Err(ResourceError::Invariant.into()),
                };
                let left_body =
                    match expressions
                        .get(self.left, budget)?
                        .kind(expressions, levels, budget)?
                    {
                        ExprKind::Pi(_, _, body, _) | ExprKind::Lambda(_, _, body, _) => body,
                        _ => return Err(ResourceError::Invariant.into()),
                    };
                // Both original binder derivations and the completed oriented
                // domain comparison justify this particular right-domain context.
                // No algorithmic rechecking or general context replacement is
                // assumed. Fresh identities and these handles stay owner-local.
                let needed = self
                    .binders
                    .locals
                    .len()
                    .checked_add(1)
                    .ok_or(ResourceError::Counter)?;
                budget.reserve_frames(1)?;
                if let Err(error) = budget.grow_vec(&mut self.binders.locals, needed) {
                    budget.release_frames(1)?;
                    return Err(error.into());
                }
                let local = match locals.enter_checked(
                    // Certificate authority: the completed oriented domain
                    // comparison above establishes this right-domain context.
                    CheckedTy::checked(right_domain, CheckednessMint::mint()),
                    None,
                    right_name,
                    annotation,
                    expressions,
                    names,
                    budget,
                ) {
                    Ok(local) => local,
                    Err(error) => {
                        budget.release_frames(1)?;
                        return Err(error.into());
                    }
                };
                self.binders.locals.push(local);
                let free =
                    expressions.append(ExprKind::Free(local.slot()), levels, names, budget)?;
                self.left = expressions.bind(
                    left_body,
                    0,
                    Binding::Instantiate(&[free]),
                    levels,
                    names,
                    budget,
                )?;
                self.right = expressions.bind(
                    right_body,
                    0,
                    Binding::Instantiate(&[free]),
                    levels,
                    names,
                    budget,
                )?;
                self.exposed = false;
                self.delta_sides = 0;
                self.left_normal = None;
                self.phase = Phase::Prefix;
            }
            if self.phase == Phase::Paired {
                match natural::paired(
                    self.left,
                    self.right,
                    scope,
                    environment,
                    expressions,
                    levels,
                    names,
                    budget,
                )? {
                    natural::Pair::Zero => {
                        return self.finish(Decision::Equal(self.incoming), locals, ledger, budget);
                    }
                    natural::Pair::Successors(left, right) => {
                        self.phase = Phase::NaturalPredecessors;
                        self.waiting = true;
                        return Ok(Demand::Comparison {
                            left,
                            right,
                            incoming: self.incoming,
                        });
                    }
                    natural::Pair::Unavailable => (),
                }
                self.delta_sides = delta::select(
                    self.left,
                    self.right,
                    scope,
                    environment,
                    expressions,
                    levels,
                    names,
                    budget,
                )?;
                if self.delta_sides & 64 != 0 {
                    self.quotient_history = QuotientHistory::Admitted;
                } else if self.delta_sides == 0
                    && self.quotient_history != QuotientHistory::Admitted
                {
                    self.quotient_history = QuotientHistory::Inapplicable;
                }
                if self.delta_sides == 32 {
                    let left = natural::predicate_step(
                        self.left,
                        self.incoming,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        budget,
                    )?;
                    let right = natural::predicate_step(
                        self.right,
                        self.incoming,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        budget,
                    )?;
                    if left.is_some() || right.is_some() {
                        // Only certified primitive computation can renew C here.
                        // Both independent operands start at the same route; no
                        // ordinary fallback result or failed route is promoted.
                        let a = left.unwrap_or(Head {
                            expression: self.left,
                            path: self.incoming,
                        });
                        let b = right.unwrap_or(Head {
                            expression: self.right,
                            path: self.incoming,
                        });
                        self.left = a.expression;
                        self.right = b.expression;
                        self.incoming = a.path.maximum(b.path);
                        self.left_normal = None;
                        self.observed = None;
                        self.exposed = false;
                        self.delta_sides = 0;
                        self.phase = Phase::Initial;
                        continue;
                    }
                    self.auxiliary = Auxiliary::Arithmetic(natural::primitive::Primitive::new(
                        self.left,
                        self.right,
                        self.incoming,
                    ));
                    self.phase = Phase::Arithmetic;
                    continue;
                }
                if self.delta_sides == 16 {
                    self.phase = Phase::FullProjectionLeft;
                    continue;
                }
                if self.delta_sides == 0 {
                    let left_projection = matches!(
                        expressions
                            .get(self.left, budget)?
                            .kind(expressions, levels, budget)?,
                        ExprKind::Projection(..)
                    );
                    let right_projection = matches!(
                        expressions
                            .get(self.right, budget)?
                            .kind(expressions, levels, budget)?,
                        ExprKind::Projection(..)
                    );
                    // C6 cannot match unlike heads; C7 needs two projections.
                    // C8 must finish before any residual conclusion is available.
                    self.phase = if left_projection != right_projection {
                        Phase::FullProjectionLeft
                    } else {
                        Phase::Rigid
                    };
                    continue;
                }
                if self.delta_sides & 64 != 0
                    && let Some(equal_arity) = same_definition::prepare(
                        self.left,
                        self.right,
                        &mut self.arguments,
                        expressions,
                        levels,
                        names,
                        ledger,
                        universes,
                        budget,
                    )?
                {
                    // C4's original type remains in left_normal. This
                    // consumed observation slot owns only the optional max.
                    self.observed = Some(Head {
                        expression: self.left,
                        path: self.incoming,
                    });
                    if !equal_arity {
                        self.delta_sides |= 128;
                    }
                    self.phase = Phase::SameDefinition;
                    continue;
                }
                self.phase = match self.delta_sides & 12 {
                    4 => Phase::PairedProjectionLeft,
                    8 => Phase::PairedProjectionRight,
                    _ => Phase::PairedUnfold,
                };
            }
            if self.phase == Phase::ProjectionDelta {
                let Auxiliary::Projection(attempt) = &mut self.auxiliary else {
                    return Err(ResourceError::Invariant.into());
                };
                match attempt.advance(
                    &mut self.arguments,
                    scope,
                    environment,
                    expressions,
                    levels,
                    names,
                    ledger,
                    universes,
                    budget,
                )? {
                    projection::Step::Head {
                        root,
                        incoming,
                        exposure,
                    } => {
                        self.waiting = true;
                        return Ok(match exposure {
                            super::super::Exposure::Cheap => Demand::CheapHead { root, incoming },
                            super::super::Exposure::NonDelta => {
                                Demand::NonDeltaHead { root, incoming }
                            }
                            super::super::Exposure::Full => Demand::Head { root, incoming },
                        });
                    }
                    projection::Step::Comparison {
                        left,
                        right,
                        incoming,
                    } => {
                        self.waiting = true;
                        return Ok(Demand::Comparison {
                            left,
                            right,
                            incoming,
                        });
                    }
                    projection::Step::Equal(path) => {
                        self.optional_route.take().ok_or(ResourceError::Invariant)?;
                        self.auxiliary = Auxiliary::Empty;
                        return self.finish(Decision::Equal(path), locals, ledger, budget);
                    }
                    projection::Step::Stopped => {
                        self.incoming = attempt.incoming();
                        self.phase = Phase::ProjectionSourceLeft;
                    }
                }
                continue;
            }
            if matches!(
                self.phase,
                Phase::ProjectionSourceLeft | Phase::ProjectionSourceRight
            ) {
                let Auxiliary::Projection(attempt) = &self.auxiliary else {
                    return Err(ResourceError::Invariant.into());
                };
                self.waiting = true;
                return Ok(Demand::Head {
                    root: if self.phase == Phase::ProjectionSourceLeft {
                        attempt.left.expression
                    } else {
                        attempt.right.expression
                    },
                    incoming: self.incoming,
                });
            }
            if self.phase == Phase::ProjectionSelect {
                let Auxiliary::Projection(attempt) = &self.auxiliary else {
                    return Err(ResourceError::Invariant.into());
                };
                let left = projection::field(
                    self.left,
                    attempt.left,
                    scope,
                    environment,
                    expressions,
                    levels,
                    names,
                    budget,
                )?;
                let right = projection::field(
                    self.right,
                    attempt.right,
                    scope,
                    environment,
                    expressions,
                    levels,
                    names,
                    budget,
                )?;
                let path = left
                    .unwrap_or(attempt.left)
                    .path
                    .maximum(right.unwrap_or(attempt.right).path);
                let (left, right) = match (left, right) {
                    (Some(left), Some(right)) => (left.expression, right.expression),
                    _ => (attempt.left.expression, attempt.right.expression),
                };
                self.incoming = path;
                self.phase = Phase::ProjectionCompare;
                self.waiting = true;
                return Ok(Demand::Comparison {
                    left,
                    right,
                    incoming: path,
                });
            }
            if matches!(
                self.phase,
                Phase::FullProjectionLeft
                    | Phase::FullProjectionRight
                    | Phase::FullProjectionRightUnchanged
                    | Phase::ProjectionRetryLeft
                    | Phase::ProjectionRetryRight
                    | Phase::ProjectionRetryRightUnchanged
            ) {
                self.waiting = true;
                return Ok(Demand::NonDeltaHead {
                    root: if matches!(
                        self.phase,
                        Phase::FullProjectionLeft | Phase::ProjectionRetryLeft
                    ) {
                        self.left
                    } else {
                        self.right
                    },
                    incoming: self.incoming,
                });
            }
            if matches!(
                self.phase,
                Phase::PairedProjectionLeft | Phase::PairedProjectionRight
            ) {
                self.waiting = true;
                return Ok(Demand::NonDeltaHead {
                    root: if self.phase == Phase::PairedProjectionLeft {
                        self.left
                    } else {
                        self.right
                    },
                    incoming: self.incoming,
                });
            }
            if self.phase == Phase::SameDefinition {
                if let Some((left, right)) = self.arguments.pop() {
                    budget.release_frames(1)?;
                    self.waiting = true;
                    return Ok(Demand::Comparison {
                        left,
                        right,
                        incoming: self.incoming,
                    });
                }
                if self.delta_sides & 128 == 0 {
                    let path = self.observed.ok_or(ResourceError::Invariant)?.path;
                    return self.finish(Decision::Equal(path), locals, ledger, budget);
                }
                // Completed arity failure closes only the optional shortcut.
                self.observed = None;
                self.phase = Phase::PairedUnfold;
            }
            if self.phase == Phase::PairedUnfold {
                if !self.arguments.is_empty() {
                    let count = self.arguments.len();
                    self.arguments.clear();
                    budget.release_frames(count)?;
                }
                if self.delta_sides & 1 != 0 {
                    self.left = delta::unfold(
                        self.left,
                        self.incoming,
                        &mut self.arguments,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        budget,
                    )?;
                }
                if self.delta_sides & 2 != 0 {
                    self.right = delta::unfold(
                        self.right,
                        self.incoming,
                        &mut self.arguments,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        budget,
                    )?;
                }
                self.observed = None;
                self.phase = if self.delta_sides & 1 != 0 {
                    Phase::PairedLeft
                } else {
                    Phase::PairedRight
                };
            }
            if matches!(self.phase, Phase::PairedLeft | Phase::PairedRight) {
                self.waiting = true;
                return Ok(Demand::CheapHead {
                    root: if self.phase == Phase::PairedLeft {
                        self.left
                    } else {
                        self.right
                    },
                    incoming: self.incoming.after_reduction()?,
                });
            }
            if self.phase == Phase::GeneralStructureClassify {
                let eligible = spine::general_structure(
                    self.left,
                    self.right,
                    &mut self.arguments,
                    scope,
                    environment,
                    expressions,
                    levels,
                    names,
                    locals,
                    budget,
                )?;
                let count = self.arguments.len();
                self.arguments.clear();
                budget.release_frames(count)?;
                self.phase = if eligible {
                    Phase::EtaFullLeft
                } else {
                    Phase::Fallback
                };
                continue;
            }
            if matches!(
                self.phase,
                Phase::EtaFullLeft | Phase::EtaFullRight | Phase::EtaFullRightUnchanged
            ) {
                self.waiting = true;
                return Ok(Demand::Head {
                    root: if self.phase == Phase::EtaFullLeft {
                        self.left
                    } else {
                        self.right
                    },
                    incoming: self.incoming,
                });
            }
            if self.phase == Phase::EtaReady {
                // Only unchanged completed C8 enters this phase. It never calls
                // prepare again, so the unchanged pair cannot cycle through C8.
                let left = expressions
                    .get(self.left, budget)?
                    .kind(expressions, levels, budget)?;
                let right =
                    expressions
                        .get(self.right, budget)?
                        .kind(expressions, levels, budget)?;
                let lambda_left = matches!(left, ExprKind::Lambda(..));
                if !lambda_left && !matches!(right, ExprKind::Lambda(..)) {
                    // The post-C5 classifier admitted a checked structure pair.
                    // This owner never acquires the old constructor C13 authority.
                    if !matches!(self.binders.result, Decision::Equal(_)) {
                        return Err(ResourceError::Invariant.into());
                    }
                    self.auxiliary = Auxiliary::GeneralStructure(constructor::Attempt {
                        incoming: self.incoming,
                        prior: self.binders.result,
                        maximum: self.incoming,
                        left_constructor: false,
                    });
                    self.phase = match spine::general_arguments(
                        self.left,
                        self.right,
                        &mut self.arguments,
                        expressions,
                        levels,
                        budget,
                    )? {
                        spine::GeneralArguments::Inapplicable => Phase::ConstructorRightPrepare,
                        spine::GeneralArguments::EqualArity => Phase::GeneralStructureArguments,
                        spine::GeneralArguments::UnequalArity => {
                            Phase::GeneralStructureUnequalArguments
                        }
                    };
                    continue;
                }
                if lambda_left == matches!(right, ExprKind::Lambda(..)) {
                    return Err(ResourceError::Invariant.into());
                }
                let (neutral, kind) = if lambda_left {
                    (self.right, right)
                } else {
                    (self.left, left)
                };
                if expressions.get(neutral, budget)?.loose_range() != 0 {
                    return Err(HeadError::Unsupported);
                }
                if let ExprKind::Free(id) = kind {
                    // Preserve only the pre-existing local-specific C13 route.
                    if locals.get(id, budget)?.value().is_some() {
                        return Err(HeadError::Unsupported);
                    }
                } else {
                    self.begin_optional_route()?;
                }
                self.phase = if lambda_left {
                    Phase::EtaLeftObserve
                } else {
                    Phase::EtaRightObserve
                };
                continue;
            }
            if matches!(
                self.phase,
                Phase::LocalPrefixSuccess | Phase::LocalPrefixDifferent | Phase::LocalPrefixFailed
            ) {
                if self.phase == Phase::LocalPrefixSuccess {
                    return self.finish(self.binders.result, locals, ledger, budget);
                }
                if self.phase == Phase::LocalPrefixDifferent {
                    // Each intermediate C13 is discharged by the checked opaque
                    // endomorphism guards. The original owner's
                    // retained type must still complete its ordinary C12 route.
                    self.phase = Phase::ArgumentTypeExpose;
                } else {
                    *prefix_trial = PrefixTrial::Disabled;
                    self.phase = Phase::Rigid;
                }
            }
            if self.phase == Phase::Rigid {
                if !self.inconclusive
                    && self.quotient_history == QuotientHistory::Inapplicable
                    && quotient::candidate(
                        self.left,
                        self.right,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        locals,
                        budget,
                    )?
                {
                    // Whole operands, before detached C9. Syntax supplies only
                    // a candidate; both ordinary full exposures must complete.
                    self.phase = Phase::QuotientLeft;
                    continue;
                }
                match projection::prepare(
                    self.left,
                    self.right,
                    self.incoming,
                    scope,
                    environment,
                    expressions,
                    levels,
                    names,
                    budget,
                )? {
                    projection::Preparation::Compare(attempt) => {
                        self.begin_optional_route()?;
                        self.auxiliary = Auxiliary::Projection(attempt);
                        self.phase = Phase::ProjectionDelta;
                        continue;
                    }
                    projection::Preparation::Expose => {
                        // C7 inapplicability does not discharge C8. This existing
                        // continuation advances beyond C7 when both heads stay
                        // unchanged, so a neutral pair cannot loop here.
                        self.phase = Phase::ProjectionRetryLeft;
                        continue;
                    }
                    projection::Preparation::ExposeUnresolved => {
                        // The skipped matched C7 source comparison might have
                        // proved equality. C8 may still prove equality, but
                        // no later route may publish Different from this owner.
                        self.inconclusive = true;
                        self.phase = Phase::ProjectionRetryLeft;
                        continue;
                    }
                    projection::Preparation::NotPair => {}
                }
                if *prefix_trial == PrefixTrial::Enabled
                    && let Some((left, right)) = spine::local_prefix(
                        self.left,
                        self.right,
                        expressions,
                        levels,
                        locals,
                        budget,
                    )?
                {
                    self.begin_optional_route()?;
                    self.phase = Phase::LocalPrefix;
                    self.waiting = true;
                    return Ok(Demand::Comparison {
                        left,
                        right,
                        incoming: self.incoming,
                    });
                }
                match spine::prepare(
                    self.left,
                    self.right,
                    &mut self.arguments,
                    scope,
                    environment,
                    expressions,
                    levels,
                    names,
                    locals,
                    ledger,
                    universes,
                    budget,
                )? {
                    spine::Prepared::Equal => {
                        return self.finish(Decision::Equal(self.incoming), locals, ledger, budget);
                    }
                    spine::Prepared::Arguments => {
                        self.begin_optional_route()?;
                        self.phase = Phase::Arguments;
                    }
                    spine::Prepared::PositiveArguments => {
                        let Decision::Equal(baseline) = self.binders.result else {
                            return Err(ResourceError::Invariant.into());
                        };
                        // This phase owns observed only as the pre-attempt binder
                        // route. Child owners cannot overwrite it. A failed optional
                        // congruence restores it before independent fallback work.
                        self.observed = Some(Head {
                            expression: self.left,
                            path: baseline,
                        });
                        self.phase = Phase::PositiveArguments;
                    }
                    spine::Prepared::ConstructorArguments => {
                        let Decision::Equal(baseline) = self.binders.result else {
                            return Err(ResourceError::Invariant.into());
                        };
                        self.observed = Some(Head {
                            expression: self.left,
                            path: baseline,
                        });
                        self.phase = Phase::ConstructorArguments;
                    }
                    spine::Prepared::UnequalArguments => self.phase = Phase::UnequalArguments,
                    spine::Prepared::RigidArity => self.phase = Phase::ArgumentTypeExpose,
                    spine::Prepared::UnitLocals => self.phase = Phase::UnitExpose,
                    spine::Prepared::EtaLeft | spine::Prepared::EtaRight => {
                        self.phase = Phase::EtaFullLeft;
                        continue;
                    }
                    spine::Prepared::StructureLeft => {
                        self.begin_optional_route()?;
                        self.phase = Phase::StructureLeftObserve;
                    }
                    spine::Prepared::StructureRight => {
                        self.begin_optional_route()?;
                        self.phase = Phase::StructureRightObserve;
                    }
                    spine::Prepared::StructureIneligible => {
                        // This is completed C10 ineligibility, not an unavailable
                        // classification or a failed optional child comparison.
                        let count = self.arguments.len();
                        self.arguments.clear();
                        budget.release_frames(count)?;
                        self.phase = Phase::LocalConstructorExpose;
                    }
                    spine::Prepared::LocalApplication => self.phase = Phase::LocalApplicationExpose,
                    spine::Prepared::RecursorLocal => self.phase = Phase::RecursorLocalExpose,
                    spine::Prepared::RecursorZero => self.phase = Phase::RecursorZeroExpose,
                    spine::Prepared::RecursorProjection => {
                        self.phase = Phase::RecursorProjectionExpose
                    }
                    spine::Prepared::LocalProjection => {
                        let count = self.arguments.len();
                        self.arguments.clear();
                        budget.release_frames(count)?;
                        self.phase = Phase::LocalProjectionExpose;
                    }
                    spine::Prepared::DistinctConstructors => {
                        self.phase = Phase::DistinctConstructorsExpose
                    }
                    spine::Prepared::RigidConstants => self.phase = Phase::RigidConstantsExpose,
                    spine::Prepared::NoRule => self.phase = Phase::NoRuleExpose,
                    spine::Prepared::Unavailable => {
                        let count = self.arguments.len();
                        self.arguments.clear();
                        budget.release_frames(count)?;
                        self.phase = Phase::GeneralStructureClassify;
                        continue;
                    }
                }
            }
            if self.phase == Phase::GeneralStructurePrepare {
                self.next_general_structure_attempt()?;
                continue;
            }
            if matches!(
                self.phase,
                Phase::GeneralStructureArguments | Phase::GeneralStructureUnequalArguments
            ) {
                if let Some((left, right)) = self.arguments.pop() {
                    budget.release_frames(1)?;
                    self.waiting = true;
                    return Ok(Demand::Comparison {
                        left,
                        right,
                        incoming: self.incoming,
                    });
                }
                if self.phase == Phase::GeneralStructureUnequalArguments {
                    self.next_general_structure_attempt()?;
                    continue;
                }
                let path = self.auxiliary.constructor()?.maximum;
                return self.finish(Decision::Equal(path), locals, ledger, budget);
            }
            if matches!(
                self.phase,
                Phase::ConstructorRightPrepare | Phase::ConstructorLeftPrepare
            ) {
                let count = self.arguments.len();
                self.arguments.clear();
                budget.release_frames(count)?;
                let left_constructor = self.phase == Phase::ConstructorLeftPrepare;
                let (constructor, other) = if left_constructor {
                    (self.left, self.right)
                } else {
                    (self.right, self.left)
                };
                self.auxiliary.constructor()?.left_constructor = left_constructor;
                match spine::local_pair_prepare(
                    constructor,
                    other,
                    left_constructor,
                    &mut self.arguments,
                    scope,
                    environment,
                    expressions,
                    levels,
                    names,
                    locals,
                    budget,
                )? {
                    spine::Prepared::StructureLeft => self.phase = Phase::StructureLeftObserve,
                    spine::Prepared::StructureRight => self.phase = Phase::StructureRightObserve,
                    spine::Prepared::StructureIneligible => self.next_constructor_attempt()?,
                    _ if matches!(self.auxiliary, Auxiliary::GeneralStructure(_)) => {
                        self.next_constructor_attempt()?
                    }
                    _ => return Err(HeadError::Unsupported),
                }
                continue;
            }
            // Unequal arity owns exactly one pending head premise. It cannot
            // conclude equality by exhausting an argument list.
            if self.phase == Phase::UnequalArguments && self.arguments.len() != 1 {
                return Err(ResourceError::Invariant.into());
            }
            if matches!(
                self.phase,
                Phase::Arguments
                    | Phase::PositiveArguments
                    | Phase::ConstructorArguments
                    | Phase::UnequalArguments
                    | Phase::StructureFields
            ) {
                if let Some((left, right)) = self.arguments.pop() {
                    budget.release_frames(1)?;
                    self.waiting = true;
                    return Ok(Demand::Comparison {
                        left,
                        right,
                        incoming: self.incoming,
                    });
                }
                let path =
                    if self.phase == Phase::StructureFields && self.auxiliary.is_constructor() {
                        self.auxiliary.constructor()?.maximum
                    } else {
                        self.incoming
                    };
                return self.finish(Decision::Equal(path), locals, ledger, budget);
            }
            if matches!(
                self.phase,
                Phase::ArgumentTypeExpose
                    | Phase::LocalApplicationExpose
                    | Phase::DistinctConstructorsExpose
                    | Phase::RigidConstantsExpose
                    | Phase::NoRuleExpose
                    | Phase::RecursorLocalExpose
                    | Phase::RecursorZeroExpose
                    | Phase::RecursorProjectionExpose
                    | Phase::LocalProjectionExpose
                    | Phase::FunctionEtaFailedExpose
                    | Phase::ConstructorFailedExpose
            ) && !self.arguments.is_empty()
            {
                let count = self.arguments.len();
                self.arguments.clear();
                budget.release_frames(count)?;
            }
            match self.phase {
                Phase::StructureLeftExpose | Phase::StructureRightExpose => {
                    let root = if self.phase == Phase::StructureLeftExpose {
                        self.observed.ok_or(ResourceError::Invariant)?.expression
                    } else {
                        self.left_normal.ok_or(ResourceError::Invariant)?.expression
                    };
                    self.waiting = true;
                    return Ok(Demand::Head {
                        root,
                        incoming: self.incoming,
                    });
                }
                Phase::StructureLeftBuild | Phase::StructureRightBuild => {
                    let constructor_left = self.phase == Phase::StructureLeftBuild;
                    let constructor = if constructor_left {
                        self.left
                    } else {
                        self.right
                    };
                    let neutral = if constructor_left {
                        self.right
                    } else {
                        self.left
                    };
                    let head = self.observed.ok_or(ResourceError::Invariant)?;
                    let Some(family) = spine::structure_family(
                        constructor,
                        head.expression,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        budget,
                    )?
                    else {
                        self.ineligible_structure(head.path)?;
                        continue;
                    };
                    // C4 already established that the left operand is not a proof.
                    // Completed type comparison and exact family exposure give
                    // the local that same instantiated non-Prop family. Thus these
                    // projections are legal; generating syntax grants no new trust.
                    let count = self.arguments.len();
                    budget.charge_work(count as u64 + 1)?;
                    for (reverse, pair) in self.arguments.iter_mut().enumerate() {
                        let index = u32::try_from(count - 1 - reverse)
                            .map_err(|_| ResourceError::Counter)?;
                        let projection = expressions.append(
                            ExprKind::Projection(family, index, neutral),
                            levels,
                            names,
                            budget,
                        )?;
                        *pair = if constructor_left {
                            (pair.0, projection)
                        } else {
                            (projection, pair.0)
                        };
                    }
                    spine::schedule_fields(
                        constructor,
                        &mut self.arguments,
                        Some(constructor_left),
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        budget,
                    )?;
                    self.incoming = head.path;
                    if self.auxiliary.is_constructor() {
                        let attempt = self.auxiliary.constructor()?;
                        attempt.maximum = attempt.maximum.maximum(head.path);
                    }
                    self.phase = Phase::StructureFields;
                    continue;
                }
                Phase::EtaLeftBuild | Phase::EtaRightBuild => {
                    let head = self.observed.ok_or(ResourceError::Invariant)?;
                    let ExprKind::Pi(name, domain, _, annotation) = expressions
                        .get(head.expression, budget)?
                        .kind(expressions, levels, budget)?
                    else {
                        if self.optional_route.is_some() {
                            self.abandon_optional_route()?;
                        } else {
                            self.incoming = head.path;
                        }
                        self.phase = Phase::Fallback;
                        continue;
                    };
                    let lambda_left = self.phase == Phase::EtaLeftBuild;
                    let neutral = if lambda_left { self.right } else { self.left };
                    // The guard established a checked non-let local or a supported
                    // neutral application with no loose bound variables. Its Pi domain gives
                    // the generated application/lambda their typing derivation.
                    let variable = expressions.append(ExprKind::Bound(0), levels, names, budget)?;
                    let body = expressions.append(
                        ExprKind::App(neutral, variable),
                        levels,
                        names,
                        budget,
                    )?;
                    let expanded = expressions.append(
                        ExprKind::Lambda(name, domain, body, annotation),
                        levels,
                        names,
                        budget,
                    )?;
                    self.phase = if self.optional_route.is_some() {
                        Phase::EtaApplicationCompare
                    } else {
                        Phase::EtaCompare
                    };
                    self.waiting = true;
                    return Ok(Demand::Comparison {
                        left: if lambda_left { self.left } else { expanded },
                        right: if lambda_left { expanded } else { self.right },
                        incoming: head.path,
                    });
                }
                Phase::EtaLeftExpose | Phase::EtaRightExpose => {
                    let head = self.observed.ok_or(ResourceError::Invariant)?;
                    self.waiting = true;
                    return Ok(Demand::Head {
                        root: head.expression,
                        incoming: head.path,
                    });
                }
                Phase::UnitExpose
                | Phase::QuotientTypeExpose
                | Phase::ArgumentTypeExpose
                | Phase::LocalConstructorExpose
                | Phase::LocalApplicationExpose
                | Phase::DistinctConstructorsExpose
                | Phase::RigidConstantsExpose
                | Phase::NoRuleExpose
                | Phase::RecursorLocalExpose
                | Phase::RecursorZeroExpose
                | Phase::RecursorProjectionExpose
                | Phase::LocalProjectionExpose
                | Phase::FunctionEtaFailedExpose
                | Phase::ConstructorFailedExpose => {
                    let left = self.left_normal.ok_or(ResourceError::Invariant)?;
                    self.waiting = true;
                    return Ok(Demand::Head {
                        root: left.expression,
                        incoming: self.incoming,
                    });
                }
                Phase::LocalConstructorClassify
                | Phase::LocalApplicationClassify
                | Phase::DistinctConstructorsClassify
                | Phase::RigidConstantsClassify
                | Phase::NoRuleClassify
                | Phase::RecursorLocalClassify
                | Phase::RecursorZeroClassify
                | Phase::RecursorProjectionClassify
                | Phase::LocalProjectionClassify
                | Phase::FunctionEtaFailedClassify
                | Phase::ConstructorFailedClassify => {
                    let left = self.observed.take().ok_or(ResourceError::Invariant)?;
                    if spine::unit_eligible(
                        left.expression,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        budget,
                    )? {
                        self.begin_general_unit(left)?;
                        continue;
                    }
                    let evidence = match self.phase {
                        Phase::LocalConstructorClassify => Evidence::LocalConstructor,
                        Phase::LocalApplicationClassify => Evidence::LocalApplication,
                        Phase::FunctionEtaFailedClassify => Evidence::FunctionEta,
                        Phase::ConstructorFailedClassify => Evidence::ConstructorArguments,
                        Phase::RecursorLocalClassify => Evidence::RecursorLocal,
                        Phase::RecursorZeroClassify => Evidence::RecursorZero,
                        Phase::RecursorProjectionClassify => Evidence::RecursorProjection,
                        Phase::LocalProjectionClassify => Evidence::LocalProjection,
                        Phase::DistinctConstructorsClassify => Evidence::DistinctConstructors,
                        Phase::RigidConstantsClassify => Evidence::RigidConstants,
                        Phase::NoRuleClassify => Evidence::NoRule,
                        _ => return Err(ResourceError::Invariant.into()),
                    };
                    return self.finish(Decision::Different(evidence), locals, ledger, budget);
                }
                Phase::QuotientTypeClassify => {
                    let ty = self.observed.take().ok_or(ResourceError::Invariant)?;
                    if self.inconclusive
                        || self.quotient_history != QuotientHistory::Inapplicable
                        || !quotient::data_type(ty.expression, expressions, levels, locals, budget)?
                        || !quotient::candidate(
                            self.left,
                            self.right,
                            scope,
                            environment,
                            expressions,
                            levels,
                            names,
                            locals,
                            budget,
                        )?
                    {
                        self.phase = Phase::GeneralStructureClassify;
                        continue;
                    }
                    let structure = spine::general_structure(
                        self.left,
                        self.right,
                        &mut self.arguments,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        locals,
                        budget,
                    )?;
                    let count = self.arguments.len();
                    self.arguments.clear();
                    budget.release_frames(count)?;
                    if structure {
                        // A miss never establishes inequality; retain the ordinary route.
                        self.phase = Phase::GeneralStructureClassify;
                        continue;
                    }
                    if spine::unit_eligible(
                        ty.expression,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        budget,
                    )? {
                        self.begin_general_unit(ty)?;
                        continue;
                    }
                    // Checked ORIGINAL LEFT function-prefix types, after actual
                    // argument instantiation, are Pis ending in this unreducible
                    // Sort-1 local A. Its function terms cannot take
                    // proof irrelevance, structure/unit eta or lambda eta;
                    // unequal local/committed-Lift heads cannot take C9. Both
                    // whole operands completed C8 in this owner, and the actual
                    // retained original left type completed C10/C12 eligibility.
                    return self.finish(
                        Decision::Different(Evidence::QuotientLocal),
                        locals,
                        ledger,
                        budget,
                    );
                }
                Phase::UnitClassify => {
                    let left = self.observed.take().ok_or(ResourceError::Invariant)?;
                    if spine::unit_eligible(
                        left.expression,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        budget,
                    )? {
                        self.left_normal = Some(Normal {
                            expression: left.expression,
                            height: left.path.height_since(self.incoming)?,
                        });
                        self.phase = Phase::UnitRight;
                    } else {
                        // Distinct non-let local heads discharged C5-C11;
                        // completed C12 ineligibility closes this C13 case.
                        return self.finish(
                            Decision::Different(Evidence::DistinctLocals),
                            locals,
                            ledger,
                            budget,
                        );
                    }
                    continue;
                }
                Phase::ArgumentTypeClassify => {
                    let left = self.observed.take().ok_or(ResourceError::Invariant)?;
                    if !spine::unit_eligible(
                        left.expression,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        budget,
                    )? {
                        // A completed C9 different child is only a failed optional
                        // route. Validated rigid heads or completed same-recursor
                        // neutral heads rule out C10/C11; this completed C12
                        // ineligibility closes the final alternative.
                        return self.finish(
                            Decision::Different(Evidence::RigidArguments),
                            locals,
                            ledger,
                            budget,
                        );
                    }
                    self.begin_general_unit(left)?;
                    continue;
                }
                Phase::ObserveLeft
                | Phase::ObserveType
                | Phase::ObserveRight
                | Phase::UnitRight
                | Phase::GeneralUnitRight
                | Phase::EtaLeftObserve
                | Phase::EtaRightObserve
                | Phase::StructureLeftObserve
                | Phase::StructureRightObserve => {
                    let (root, incoming) = match self.phase {
                        Phase::ObserveLeft => (self.left, self.incoming),
                        Phase::ObserveRight
                        | Phase::UnitRight
                        | Phase::GeneralUnitRight
                        | Phase::StructureLeftObserve
                        | Phase::StructureRightObserve => (self.right, self.incoming),
                        Phase::EtaLeftObserve => (self.right, self.incoming),
                        Phase::EtaRightObserve => (self.left, self.incoming),
                        _ => {
                            let a = self.left_normal.ok_or(ResourceError::Invariant)?;
                            (a.expression, self.incoming.after_height(a.height)?)
                        }
                    };
                    self.waiting = true;
                    return Ok(Demand::Observation(TypeObservation { root, incoming }));
                }
                Phase::ExposeSort => {
                    let head = self.observed.ok_or(ResourceError::Invariant)?;
                    self.waiting = true;
                    return Ok(Demand::Head {
                        root: head.expression,
                        incoming: head.path,
                    });
                }
                Phase::Classify => {
                    let head = self.observed.take().ok_or(ResourceError::Invariant)?;
                    let ExprKind::Sort(level) = expressions.get(head.expression, budget)?.kind(
                        expressions,
                        levels,
                        budget,
                    )?
                    else {
                        return Err(HeadError::Unsupported);
                    };
                    // Proves this summary is the exact normalized-zero
                    // predicate, including imax; no syntactic-zero shortcut.
                    // Total decision: both outcomes are exact.
                    match levels.get(level, budget)?.zero() {
                        LevelZero::Zero => {
                            self.left_normal
                                .as_mut()
                                .ok_or(ResourceError::Invariant)?
                                .height = head.path.height_since(self.incoming)?;
                            self.phase = Phase::ObserveRight;
                        }
                        LevelZero::NonZero => {
                            self.incoming = head.path;
                            // C12 may reuse A in this exact scope; its exposure is
                            // a continuation after the completed C4 classification.
                            self.left_normal
                                .as_mut()
                                .ok_or(ResourceError::Invariant)?
                                .height = 0;
                            self.phase = Phase::Paired;
                        }
                    }
                    continue;
                }
                Phase::ProofCompare
                | Phase::UnitCompare
                | Phase::GeneralUnitCompare
                | Phase::StructureLeftCompare
                | Phase::StructureRightCompare => {
                    let left = self.left_normal.ok_or(ResourceError::Invariant)?;
                    let right = self.observed.ok_or(ResourceError::Invariant)?;
                    self.waiting = true;
                    return Ok(Demand::Comparison {
                        left: left.expression,
                        right: right.expression,
                        incoming: self.incoming.after_height(left.height)?.maximum(right.path),
                    });
                }
                Phase::ProofDone => {
                    return self.finish(self.binders.result, locals, ledger, budget);
                }
                _ => {}
            }
            if self.phase == Phase::CheapRight {
                self.waiting = true;
                return Ok(Demand::CheapHead {
                    root: self.right,
                    incoming: self.incoming,
                });
            }
            if matches!(
                self.phase,
                Phase::QuotientLeft | Phase::QuotientRight | Phase::QuotientRightUnchanged
            ) {
                self.waiting = true;
                return Ok(Demand::Head {
                    root: if self.phase == Phase::QuotientLeft {
                        self.left
                    } else {
                        self.right
                    },
                    incoming: self.incoming,
                });
            }
            if matches!(self.phase, Phase::Prefix | Phase::PairedPrefix) {
                let paired = self.phase == Phase::PairedPrefix;
                if self.left == self.right {
                    return self.finish(Decision::Equal(self.incoming), locals, ledger, budget);
                }
                if self.exposed {
                    // Renewed Q retains structural identity before its terminal
                    // binder and Sort rules, just like the original Q.
                    match positive::compare_structure(
                        self.left,
                        self.right,
                        positive::LevelRule::Identity(levels),
                        expressions,
                        names,
                        budget,
                    ) {
                        Ok(()) => {
                            return self.finish(
                                Decision::Equal(self.incoming),
                                locals,
                                ledger,
                                budget,
                            );
                        }
                        Err(HeadError::Unsupported) => {}
                        Err(error) => return Err(error),
                    }
                }
                // Explicitly iterates matching prefixes. Do not rerun
                // a whole-tail identity scan at every binder: exact domains still
                // take child C1, and exact residual bodies take C1 below. This
                // changes no equality rule and introduces no new negative.
                let a = expressions
                    .get(self.left, budget)?
                    .kind(expressions, levels, budget)?;
                let b = expressions
                    .get(self.right, budget)?
                    .kind(expressions, levels, budget)?;
                match (a, b) {
                    (ExprKind::Pi(_, left, _, _), ExprKind::Pi(_, right, _, _))
                    | (ExprKind::Lambda(_, left, _, _), ExprKind::Lambda(_, right, _, _)) => {
                        self.phase = Phase::Domain;
                        self.waiting = true;
                        return Ok(Demand::Comparison {
                            left,
                            right,
                            incoming: self.incoming,
                        });
                    }
                    (ExprKind::Natural(left), ExprKind::Natural(right)) => {
                        if environment
                            .natural_constructors(
                                scope.before,
                                scope.formation,
                                scope.expression_end,
                                expressions,
                                budget,
                            )?
                            .is_none()
                        {
                            return Err(HeadError::Unsupported);
                        }
                        // Expressions::append canonicalizes decimal digits.
                        // Checked typing plus committed Nat authority permits
                        // Q's direct literal decision, not a fallback mismatch.
                        budget.charge_work(left.len().min(right.len()) as u64)?;
                        let decision = if left == right {
                            Decision::Equal(self.incoming)
                        } else {
                            Decision::Different(Evidence::Natural)
                        };
                        return self.finish(decision, locals, ledger, budget);
                    }
                    (ExprKind::Sort(left), ExprKind::Sort(right)) => {
                        let decision = match levels.with_helpers(names, budget, |helpers| {
                            helpers.compare_universes_with(
                                left,
                                right,
                                Some(SharedTable {
                                    memo: &mut *universes,
                                    ledger: &mut *ledger,
                                }),
                            )
                        })? {
                            UniverseComparison::Equal => Decision::Equal(self.incoming),
                            UniverseComparison::NotEqual => Decision::Different(Evidence::Sort),
                        };
                        return self.finish(decision, locals, ledger, budget);
                    }
                    // Sort/Pi pair: both forms are weak-head normal,
                    // neither is a proof (each one's type is a Sort whose own
                    // type is a successor Sort) and no eta, unit, literal or
                    // elimination alternative has a head to act on.
                    (ExprKind::Sort(_), ExprKind::Pi(..))
                    | (ExprKind::Pi(..), ExprKind::Sort(_)) => {
                        return self.finish(
                            Decision::Different(Evidence::SortPi),
                            locals,
                            ledger,
                            budget,
                        );
                    }
                    _ => {}
                }
                // Prefix exhaustion is not a negative. Apply C1 identity to the
                // actual opened residual operands before the existing fallback.
                if !self.exposed && !self.binders.locals.is_empty() {
                    match positive::compare_structure(
                        self.left,
                        self.right,
                        positive::LevelRule::Identity(levels),
                        expressions,
                        names,
                        budget,
                    ) {
                        Ok(()) => {
                            return self.finish(
                                Decision::Equal(self.incoming),
                                locals,
                                ledger,
                                budget,
                            );
                        }
                        Err(HeadError::Unsupported) => {}
                        Err(error) => return Err(error),
                    }
                }
                if !self.exposed {
                    if !expressions.get(self.left, budget)?.has_free()
                        && reflection::candidate(
                            self.right,
                            scope,
                            environment,
                            expressions,
                            levels,
                            names,
                            budget,
                        )?
                    {
                        self.phase = Phase::Reflection;
                        self.waiting = true;
                        return Ok(Demand::Head {
                            root: self.left,
                            incoming: self.incoming,
                        });
                    }
                    self.phase = Phase::CheapLeft;
                    self.waiting = true;
                    return Ok(Demand::CheapHead {
                        root: self.left,
                        incoming: self.incoming,
                    });
                }
                self.phase = if paired {
                    Phase::Paired
                } else {
                    Phase::ObserveLeft
                };
                continue;
            }
            if self.phase == Phase::Arithmetic {
                let Auxiliary::Arithmetic(attempt) = &mut self.auxiliary else {
                    return Err(ResourceError::Invariant.into());
                };
                match attempt.advance(scope, environment, expressions, levels, names, budget)? {
                    natural::primitive::Step::Head { root, incoming } => {
                        self.waiting = true;
                        return Ok(Demand::Head { root, incoming });
                    }
                    natural::primitive::Step::Complete(result) => {
                        self.auxiliary = Auxiliary::Empty;
                        if let Some((left, right)) = result {
                            // Only this completed certified primitive, never an
                            // arbitrary observed/fallback head, renews comparison.
                            self.left = left.expression;
                            self.right = right.expression;
                            self.incoming = left.path.maximum(right.path);
                            self.left_normal = None;
                            self.observed = None;
                            self.exposed = false;
                            self.delta_sides = 0;
                            self.phase = Phase::Initial;
                        } else {
                            self.phase = Phase::Fallback;
                        }
                        continue;
                    }
                }
            }
            if matches!(self.phase, Phase::Fallback | Phase::InconclusiveFallback) {
                self.release_arguments(budget)?;
                self.auxiliary = Auxiliary::Normal(machine::Machine::new(
                    self.left,
                    self.incoming,
                    locals.depth(),
                    budget,
                )?);
                self.phase = if self.phase == Phase::InconclusiveFallback {
                    Phase::InconclusiveLeft
                } else {
                    Phase::Left
                };
            }
            let demand = self
                .auxiliary
                .as_mut()
                .ok_or(ResourceError::Invariant)?
                .advance::<true>(
                    scope,
                    environment,
                    expressions,
                    levels,
                    names,
                    locals,
                    budget,
                    Some((&mut self.cache, ledger)),
                )?;
            match demand {
                machine::Demand::Head { root, incoming } => {
                    self.waiting = true;
                    return Ok(Demand::Head { root, incoming });
                }
                machine::Demand::Complete(normal) => {
                    self.auxiliary
                        .take()
                        .ok_or(ResourceError::Invariant)?
                        .retire(budget)?;
                    match self.phase {
                        Phase::Left | Phase::InconclusiveLeft => {
                            self.left_normal = Some(normal);
                            self.auxiliary = Auxiliary::Normal(machine::Machine::new(
                                self.right,
                                self.incoming,
                                locals.depth(),
                                budget,
                            )?);
                            self.phase = if self.phase == Phase::InconclusiveLeft {
                                Phase::InconclusiveRight
                            } else {
                                Phase::Right
                            };
                        }
                        Phase::Right | Phase::InconclusiveRight => {
                            let left = self.left_normal.ok_or(ResourceError::Invariant)?;
                            if !natural::zero_identity(
                                left.expression,
                                normal.expression,
                                scope,
                                environment,
                                expressions,
                                levels,
                                names,
                                budget,
                            )? {
                                positive::compare_structure(
                                    left.expression,
                                    normal.expression,
                                    positive::LevelRule::Universe(
                                        levels,
                                        Some(SharedTable {
                                            memo: &mut *universes,
                                            ledger: &mut *ledger,
                                        }),
                                    ),
                                    expressions,
                                    names,
                                    budget,
                                )?;
                            }
                            let path =
                                self.incoming.after_height(left.height.max(normal.height))?;
                            return self.finish(Decision::Equal(path), locals, ledger, budget);
                        }
                        _ => return Err(ResourceError::Invariant.into()),
                    }
                }
            }
        })();
        self.failure = result.as_ref().err().copied();
        result
    }

    fn finish(
        &mut self,
        decision: Decision,
        locals: &mut LocalContext,
        ledger: &mut SessionCacheBudget,
        budget: &mut Budget,
    ) -> Result<Demand, HeadError> {
        let merged = match (decision, self.binders.result) {
            (Decision::Equal(a), Decision::Equal(b)) => Decision::Equal(a.maximum(b)),
            (Decision::Different(e), _) | (_, Decision::Different(e)) => Decision::Different(e),
        };
        if self.inconclusive && matches!(merged, Decision::Different(_)) {
            // Locally unsupported, not different: the driver retires this owner.
            // The check is on the merged result, so a Different mandatory-binder
            // result cannot leave through an Equal call either.
            return Err(HeadError::Unsupported);
        }
        self.release_arguments(budget)?;
        // Cached terms mentioning opened locals die before those locals leave.
        std::mem::take(&mut self.cache).retire(ledger, budget)?;
        while let Some(&local) = self.binders.locals.last() {
            locals.leave(local, budget)?;
            self.binders.locals.pop();
            budget.release_frames(1)?;
        }
        self.phase = Phase::Complete;
        Ok(Demand::Complete(merged))
    }

    pub(crate) fn optional_same_definition(&self) -> bool {
        (self.phase == Phase::SameDefinition
            || (self.phase == Phase::ProjectionDelta
                && matches!(&self.auxiliary, Auxiliary::Projection(attempt) if attempt.comparing())))
            && self.waiting
            && self.failure.is_none()
    }

    pub(crate) fn optional_projection_comparison(&self) -> bool {
        self.phase == Phase::ProjectionCompare && self.waiting && self.failure.is_none()
    }

    pub(crate) fn optional_general_structure(&self) -> bool {
        matches!(
            self.phase,
            Phase::GeneralStructureArguments | Phase::GeneralStructureUnequalArguments
        ) && self.waiting
            && self.failure.is_none()
    }

    pub(crate) fn optional_positive_child(&self) -> bool {
        matches!(
            self.phase,
            Phase::SameDefinition
                | Phase::ProjectionCompare
                | Phase::GeneralStructureArguments
                | Phase::GeneralStructureUnequalArguments
        ) && self.waiting
            && self.failure.is_none()
    }

    pub(crate) fn optional_prefix(&self) -> bool {
        self.phase == Phase::LocalPrefix && self.waiting && self.failure.is_none()
    }

    /// Unestablished K premise. The driver calls this on the live
    /// owner waiting for the demanded head, before that head resumes without
    /// its K premise decided. The head may be a valid reduct that K would
    /// reduce further, so from here this owner finishes only Equal; a
    /// Different, from any later route or a binder result, is withheld as
    /// locally unsupported by `finish`. Owner-local by construction: the head
    /// reaches no other consumer, and this owner's completed-normal-form table
    /// is used and retired only by this owner.
    pub(crate) fn retain_unestablished_head(&mut self) -> Result<(), HeadError> {
        if !self.waiting || self.failure.is_some() || self.phase == Phase::Complete {
            self.failure = Some(ResourceError::Invariant.into());
            return Err(ResourceError::Invariant.into());
        }
        self.inconclusive = true;
        Ok(())
    }

    /// Whether this owner can publish only Equal.
    pub(crate) fn positive_only(&self) -> bool {
        self.inconclusive
    }

    /// Descendants and their context additions have already retired. Prefix
    /// resumes its baseline replay; same-definition resumes positive fallback;
    /// general C9 restores its whole checkpoint before positive structure eta.
    pub(crate) fn resume_inconclusive_shortcut(&mut self) -> Result<(), HeadError> {
        if self.phase == Phase::ProjectionDelta && self.optional_same_definition() {
            self.failure = Some(ResourceError::Invariant.into());
            let Auxiliary::Projection(attempt) = &mut self.auxiliary else {
                return Err(ResourceError::Invariant.into());
            };
            if attempt.resume_inconclusive_argument()? {
                // Keep the actual paired-source prefix and outer checkpoint.
                // Existing Unfold retires remaining pairs and charges ordinary
                // reductions. Every later negative is withheld by finish,
                // including merged mandatory-binder results.
                self.inconclusive = true;
                self.waiting = false;
                self.failure = None;
                return Ok(());
            }
            // Required matching-binder recovery retains its original
            // positive-only full-normalization fallback.
            self.abandon_optional_route()?;
            self.auxiliary = Auxiliary::Empty;
            self.waiting = false;
            self.phase = Phase::InconclusiveFallback;
            self.failure = None;
            return Ok(());
        }
        if self.optional_projection_comparison() {
            self.failure = Some(ResourceError::Invariant.into());
            self.abandon_optional_route()?;
            self.auxiliary = Auxiliary::Empty;
            // An unavailable source/field comparison leaves equality unresolved.
            // C8 may prove the projections equal but cannot revive a negative.
            self.inconclusive = true;
            self.phase = Phase::ProjectionRetryLeft;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.optional_prefix() {
            self.failure = Some(ResourceError::Invariant.into());
            self.abandon_optional_route()?;
            self.phase = Phase::LocalPrefixFailed;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if !self.optional_positive_child() || !matches!(self.binders.result, Decision::Equal(_)) {
            self.failure = Some(ResourceError::Invariant.into());
            return Err(ResourceError::Invariant.into());
        }
        self.observed = None;
        self.waiting = false;
        self.phase = if self.phase == Phase::SameDefinition {
            // Lazy delta: unfold both same-definition heads and compare again,
            // positive-only. Full normalization of the whole pair is not built.
            self.inconclusive = true;
            Phase::PairedUnfold
        } else {
            Phase::GeneralStructurePrepare
        };
        Ok(())
    }

    // Only optional C9/C10 contributions are retired. Matching binder domains
    // completed before the attempt remain required evidence for this judgment.
    // A missing exact family match is not a completed negative C10 premise.
    // Preserve the constructor owner's positive fallback, never advance to C13.
    fn ineligible_structure(&mut self, path: ReductionPath) -> Result<(), HeadError> {
        if self.auxiliary.is_constructor() {
            self.incoming = path;
        } else {
            self.abandon_optional_route()?;
        }
        self.phase = if matches!(self.auxiliary, Auxiliary::GeneralStructure(_)) {
            Phase::InconclusiveFallback
        } else {
            Phase::Fallback
        };
        Ok(())
    }

    // C12 type observation is justified by these checked operands. Its source
    // routes are independent at incoming; only the ensuing comparison inherits
    // their maximum. No failed optional contribution survives positive fallback.
    fn begin_general_unit(&mut self, left: Head) -> Result<(), HeadError> {
        let height = left.path.height_since(self.incoming)?;
        self.begin_optional_route()?;
        self.left_normal = Some(Normal {
            expression: left.expression,
            height,
        });
        self.phase = Phase::GeneralUnitRight;
        Ok(())
    }

    fn begin_optional_route(&mut self) -> Result<(), HeadError> {
        let Decision::Equal(required) = self.binders.result else {
            return Err(ResourceError::Invariant.into());
        };
        if self.optional_route.is_some() {
            return Err(ResourceError::Invariant.into());
        }
        self.optional_route = Some(OptionalRoute {
            incoming: self.incoming,
            required,
        });
        Ok(())
    }

    fn abandon_optional_route(&mut self) -> Result<(), HeadError> {
        let saved = self.optional_route.take().ok_or(ResourceError::Invariant)?;
        self.incoming = saved.incoming;
        self.binders.result = Decision::Equal(saved.required);
        self.observed = None;
        Ok(())
    }

    pub(crate) fn resume_comparison(&mut self, decision: Decision) -> Result<(), HeadError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if !self.waiting
            || !matches!(
                self.phase,
                Phase::Domain
                    | Phase::ProjectionDelta
                    | Phase::ProjectionCompare
                    | Phase::LocalPrefix
                    | Phase::SameDefinition
                    | Phase::NaturalPredecessors
                    | Phase::ProofCompare
                    | Phase::Arguments
                    | Phase::PositiveArguments
                    | Phase::ConstructorArguments
                    | Phase::GeneralStructureArguments
                    | Phase::GeneralStructureUnequalArguments
                    | Phase::UnequalArguments
                    | Phase::UnitCompare
                    | Phase::GeneralUnitCompare
                    | Phase::EtaCompare
                    | Phase::EtaApplicationCompare
                    | Phase::StructureLeftCompare
                    | Phase::StructureRightCompare
                    | Phase::StructureFields
            )
        {
            self.failure = Some(ResourceError::Invariant.into());
            return Err(ResourceError::Invariant.into());
        }
        self.failure = Some(ResourceError::Invariant.into());
        if self.phase == Phase::ProjectionDelta {
            let Auxiliary::Projection(attempt) = &mut self.auxiliary else {
                return Err(ResourceError::Invariant.into());
            };
            attempt.resume_comparison(decision)?;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.phase == Phase::ProjectionCompare {
            match decision {
                Decision::Equal(path) => {
                    path.height_since(self.incoming)?;
                    let Decision::Equal(required) = self.binders.result else {
                        return Err(ResourceError::Invariant.into());
                    };
                    self.binders.result = Decision::Equal(required.maximum(path));
                    self.optional_route.take().ok_or(ResourceError::Invariant)?;
                    self.phase = Phase::ProofDone;
                }
                Decision::Different(_) => {
                    self.abandon_optional_route()?;
                    self.phase = Phase::ProjectionRetryLeft;
                }
            }
            self.auxiliary = Auxiliary::Empty;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if matches!(
            self.phase,
            Phase::GeneralStructureArguments | Phase::GeneralStructureUnequalArguments
        ) {
            if let Decision::Equal(path) = decision {
                path.height_since(self.incoming)?;
                let attempt = self.auxiliary.constructor()?;
                attempt.maximum = attempt.maximum.maximum(path);
            }
            if matches!(decision, Decision::Different(_))
                || self.phase == Phase::GeneralStructureUnequalArguments
            {
                self.phase = Phase::GeneralStructurePrepare;
            }
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.phase == Phase::GeneralUnitCompare && matches!(decision, Decision::Different(_)) {
            self.abandon_optional_route()?;
            self.phase = Phase::Fallback;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.phase == Phase::LocalPrefix {
            match decision {
                Decision::Equal(path) => {
                    path.height_since(self.incoming)?;
                    let Decision::Equal(required) = self.binders.result else {
                        return Err(ResourceError::Invariant.into());
                    };
                    self.binders.result = Decision::Equal(required.maximum(path));
                    self.phase = Phase::LocalPrefixSuccess;
                }
                Decision::Different(_) => {
                    self.abandon_optional_route()?;
                    self.phase = Phase::LocalPrefixDifferent;
                }
            }
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.phase == Phase::SameDefinition {
            match decision {
                Decision::Equal(path) => {
                    path.height_since(self.incoming)?;
                    let accumulated = self.observed.as_mut().ok_or(ResourceError::Invariant)?;
                    accumulated.path = accumulated.path.maximum(path);
                }
                Decision::Different(_) => {
                    // Definitions need not be injective. A failed optional
                    // argument supplies no enclosing negative or route height.
                    self.observed = None;
                    self.phase = Phase::PairedUnfold;
                }
            }
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.phase == Phase::UnequalArguments {
            // C9 head-first premise completes before unequal arity. Either
            // completed answer fails congruence; neither waives C12.
            if let Decision::Equal(path) = decision {
                path.height_since(self.incoming)?;
                self.incoming = path;
            }
            self.phase = Phase::ArgumentTypeExpose;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.phase == Phase::EtaApplicationCompare && matches!(decision, Decision::Different(_))
        {
            // Only the bare-local route has the old completed C13 certificate.
            // An unsuccessful general eta comparison grants positive fallback only.
            self.abandon_optional_route()?;
            self.phase = Phase::Fallback;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.phase == Phase::EtaCompare && matches!(decision, Decision::Different(_)) {
            // Only the exact guarded function-eta attempt grants this pending
            // case. C12 is independent at the preserved post-C4 incoming route;
            // a negative child provides no returned height to reuse.
            self.phase = Phase::FunctionEtaFailedExpose;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.phase == Phase::ConstructorArguments && matches!(decision, Decision::Different(_)) {
            let prior = Decision::Equal(self.observed.take().ok_or(ResourceError::Invariant)?.path);
            self.binders.result = prior;
            self.auxiliary = Auxiliary::Constructor(constructor::Attempt {
                incoming: self.incoming,
                prior,
                maximum: self.incoming,
                left_constructor: false,
            });
            self.phase = Phase::ConstructorRightPrepare;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.auxiliary.is_constructor()
            && matches!(
                self.phase,
                Phase::StructureLeftCompare | Phase::StructureRightCompare | Phase::StructureFields
            )
        {
            match decision {
                Decision::Different(_) => self.next_constructor_attempt()?,
                Decision::Equal(path) => {
                    let expected = if self.phase == Phase::StructureFields {
                        self.incoming
                    } else {
                        self.incoming
                            .after_height(self.left_normal.ok_or(ResourceError::Invariant)?.height)?
                            .maximum(self.observed.ok_or(ResourceError::Invariant)?.path)
                    };
                    path.height_since(expected)?;
                    let attempt = self.auxiliary.constructor()?;
                    attempt.maximum = attempt.maximum.maximum(path);
                    if self.phase != Phase::StructureFields {
                        self.incoming = self.incoming.maximum(path);
                        self.phase = if self.phase == Phase::StructureLeftCompare {
                            Phase::StructureLeftExpose
                        } else {
                            Phase::StructureRightExpose
                        };
                    }
                }
            }
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.phase == Phase::PositiveArguments && matches!(decision, Decision::Different(_)) {
            self.binders.result =
                Decision::Equal(self.observed.take().ok_or(ResourceError::Invariant)?.path);
        }
        if matches!(
            self.phase,
            Phase::StructureLeftCompare | Phase::StructureRightCompare | Phase::StructureFields
        ) && matches!(decision, Decision::Different(_))
        {
            self.abandon_optional_route()?;
        }
        if matches!(
            self.phase,
            Phase::StructureLeftCompare
                | Phase::StructureRightCompare
                | Phase::StructureFields
                | Phase::PositiveArguments
        ) && matches!(decision, Decision::Different(_))
        {
            self.phase = Phase::Fallback;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.phase == Phase::Arguments && matches!(decision, Decision::Different(_)) {
            self.abandon_optional_route()?;
            // C9 is optional congruence, not injectivity. Later unimplemented
            // alternatives cannot be discharged by this failed child.
            self.phase = Phase::ArgumentTypeExpose;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        let expected = if matches!(
            self.phase,
            Phase::ProofCompare
                | Phase::UnitCompare
                | Phase::GeneralUnitCompare
                | Phase::StructureLeftCompare
                | Phase::StructureRightCompare
        ) {
            let left = self.left_normal.ok_or(ResourceError::Invariant)?;
            let right = self.observed.ok_or(ResourceError::Invariant)?;
            self.incoming.after_height(left.height)?.maximum(right.path)
        } else if matches!(self.phase, Phase::EtaCompare | Phase::EtaApplicationCompare) {
            self.observed.ok_or(ResourceError::Invariant)?.path
        } else {
            self.incoming
        };
        let decision =
            if self.phase == Phase::UnitCompare && matches!(decision, Decision::Different(_)) {
                // The type comparison only fails C12. Distinct checked local heads
                // plus that completed last alternative justify C13, not injectivity.
                Decision::Different(Evidence::DistinctLocals)
            } else {
                decision
            };
        self.binders.result = match (self.binders.result, decision) {
            (Decision::Equal(a), Decision::Equal(b)) => {
                b.height_since(expected)?;
                Decision::Equal(a.maximum(b))
            }
            (_, Decision::Different(e)) => Decision::Different(e),
            _ => return Err(ResourceError::Invariant.into()),
        };
        self.waiting = false;
        self.phase = if matches!(
            self.phase,
            Phase::StructureLeftCompare | Phase::StructureRightCompare
        ) {
            let Decision::Equal(path) = decision else {
                return Err(ResourceError::Invariant.into());
            };
            self.incoming = self.incoming.maximum(path);
            if self.phase == Phase::StructureLeftCompare {
                Phase::StructureLeftExpose
            } else {
                Phase::StructureRightExpose
            }
        } else if self.phase == Phase::StructureFields {
            Phase::StructureFields
        } else if self.phase == Phase::Domain {
            Phase::Open
        } else if matches!(
            self.phase,
            Phase::Arguments | Phase::PositiveArguments | Phase::ConstructorArguments
        ) {
            self.phase
        } else {
            Phase::ProofDone
        };
        self.failure = None;
        Ok(())
    }

    pub(crate) fn arithmetic_fallback_pending(&self) -> bool {
        self.delta_sides == 32
            && matches!(
                self.phase,
                Phase::Arithmetic | Phase::Fallback | Phase::Left | Phase::Right
            )
    }

    /// Classification head exposure remains part of observation after its
    /// inference child retires; a lookup failure cannot become a fresh negative.
    pub(crate) fn observing_type(&self) -> bool {
        self.arithmetic_fallback_pending()
            || self.auxiliary.is_constructor()
            || matches!(
                self.phase,
                Phase::LocalPrefix
                    | Phase::Arguments
                    | Phase::StructureLeftObserve
                    | Phase::StructureRightObserve
                    | Phase::StructureLeftCompare
                    | Phase::StructureRightCompare
                    | Phase::StructureFields
                    | Phase::PositiveArguments
                    | Phase::ConstructorArguments
                    | Phase::SameDefinition
                    | Phase::InconclusiveFallback
                    | Phase::InconclusiveLeft
                    | Phase::InconclusiveRight
                    | Phase::Reflection
                    | Phase::ReflectionDone
                    | Phase::Paired
                    | Phase::PairedUnfold
                    | Phase::PairedProjectionLeft
                    | Phase::PairedProjectionRight
                    | Phase::FullProjectionLeft
                    | Phase::FullProjectionRight
                    | Phase::FullProjectionRightUnchanged
                    | Phase::QuotientLeft
                    | Phase::QuotientRight
                    | Phase::QuotientRightUnchanged
                    | Phase::QuotientTypeExpose
                    | Phase::QuotientTypeClassify
                    | Phase::ProjectionDelta
                    | Phase::ProjectionSourceLeft
                    | Phase::ProjectionSourceRight
                    | Phase::ProjectionSelect
                    | Phase::ProjectionCompare
                    | Phase::ProjectionRetryLeft
                    | Phase::ProjectionRetryRight
                    | Phase::ProjectionRetryRightUnchanged
                    | Phase::EtaFullLeft
                    | Phase::EtaFullRight
                    | Phase::EtaFullRightUnchanged
                    | Phase::EtaReady
                    | Phase::GeneralStructureArguments
                    | Phase::GeneralStructureUnequalArguments
                    | Phase::GeneralStructurePrepare
                    | Phase::GeneralStructureClassify
                    | Phase::PairedLeft
                    | Phase::PairedRight
                    | Phase::PairedPrefix
                    | Phase::ExposeSort
                    | Phase::Classify
                    | Phase::UnitExpose
                    | Phase::UnitClassify
                    | Phase::GeneralUnitRight
                    | Phase::GeneralUnitCompare
                    | Phase::LocalConstructorExpose
                    | Phase::LocalConstructorClassify
                    | Phase::LocalApplicationExpose
                    | Phase::LocalApplicationClassify
                    | Phase::DistinctConstructorsExpose
                    | Phase::RigidConstantsExpose
                    | Phase::NoRuleExpose
                    | Phase::RecursorLocalExpose
                    | Phase::RecursorZeroExpose
                    | Phase::RecursorProjectionExpose
                    | Phase::LocalProjectionExpose
                    | Phase::FunctionEtaFailedExpose
                    | Phase::ConstructorFailedExpose
                    | Phase::DistinctConstructorsClassify
                    | Phase::RigidConstantsClassify
                    | Phase::NoRuleClassify
                    | Phase::RecursorLocalClassify
                    | Phase::RecursorZeroClassify
                    | Phase::RecursorProjectionClassify
                    | Phase::LocalProjectionClassify
                    | Phase::FunctionEtaFailedClassify
                    | Phase::ConstructorFailedClassify
                    | Phase::ArgumentTypeExpose
                    | Phase::ArgumentTypeClassify
                    | Phase::EtaApplicationCompare
                    | Phase::EtaLeftObserve
                    | Phase::EtaRightObserve
                    | Phase::EtaLeftExpose
                    | Phase::EtaRightExpose
                    | Phase::EtaLeftBuild
                    | Phase::EtaRightBuild
                    | Phase::StructureLeftExpose
                    | Phase::StructureRightExpose
                    | Phase::StructureLeftBuild
                    | Phase::StructureRightBuild
            )
    }

    pub(crate) fn resume_observation(&mut self, head: Head) -> Result<(), HeadError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        self.failure = Some(ResourceError::Invariant.into());
        let result = (|| {
            if !self.waiting {
                return Err(ResourceError::Invariant.into());
            }
            let expected = if self.phase == Phase::ObserveType {
                self.incoming
                    .after_height(self.left_normal.ok_or(ResourceError::Invariant)?.height)?
            } else {
                self.incoming
            };
            head.path.height_since(expected)?;
            let height = head.path.height_since(self.incoming)?;
            match self.phase {
                Phase::ObserveLeft => {
                    self.left_normal = Some(Normal {
                        expression: head.expression,
                        height,
                    });
                    self.phase = Phase::ObserveType;
                }
                Phase::ObserveType => {
                    self.observed = Some(head);
                    self.phase = Phase::ExposeSort;
                }
                Phase::ObserveRight => {
                    self.observed = Some(head);
                    self.phase = Phase::ProofCompare;
                }
                Phase::UnitRight => {
                    self.observed = Some(head);
                    self.phase = Phase::UnitCompare;
                }
                Phase::GeneralUnitRight => {
                    self.observed = Some(head);
                    self.phase = Phase::GeneralUnitCompare;
                }
                Phase::StructureLeftObserve | Phase::StructureRightObserve => {
                    self.observed = Some(head);
                    self.phase = if self.phase == Phase::StructureLeftObserve {
                        Phase::StructureLeftCompare
                    } else {
                        Phase::StructureRightCompare
                    };
                }
                Phase::EtaLeftObserve | Phase::EtaRightObserve => {
                    self.observed = Some(head);
                    self.phase = if self.phase == Phase::EtaLeftObserve {
                        Phase::EtaLeftExpose
                    } else {
                        Phase::EtaRightExpose
                    };
                }
                _ => return Err(ResourceError::Invariant.into()),
            }
            self.waiting = false;
            Ok(())
        })();
        self.failure = result.as_ref().err().copied();
        result
    }

    pub(crate) fn resume_head(&mut self, head: Head) -> Result<(), HeadError> {
        self.resume_head_reply(head, false)
    }

    /// Driver-only unchanged completed-hit status. No equality or inequality
    /// follows from it: it only suppresses handle-based progress at audited sinks.
    pub(crate) fn resume_unchanged_head(&mut self, head: Head) -> Result<(), HeadError> {
        self.resume_head_reply(head, true)
    }

    fn resume_head_reply(&mut self, head: Head, unchanged: bool) -> Result<(), HeadError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if !self.waiting || self.phase == Phase::Complete {
            let error = ResourceError::Invariant.into();
            self.failure = Some(error);
            return Err(error);
        }
        if matches!(
            self.phase,
            Phase::QuotientLeft | Phase::QuotientRight | Phase::QuotientRightUnchanged
        ) {
            self.failure = Some(ResourceError::Invariant.into());
            head.path.height_since(self.incoming)?;
            if self.phase == Phase::QuotientLeft {
                self.observed = Some(head);
                self.phase = if unchanged {
                    Phase::QuotientRightUnchanged
                } else {
                    Phase::QuotientRight
                };
            } else {
                let left = self.observed.take().ok_or(ResourceError::Invariant)?;
                let progressed = (self.phase != Phase::QuotientRightUnchanged
                    && left.expression != self.left)
                    || (!unchanged && head.expression != self.right);
                self.left = left.expression;
                self.right = head.expression;
                self.incoming = left.path.maximum(head.path);
                if progressed {
                    self.left_normal = None;
                    self.exposed = false;
                    self.delta_sides = 0;
                    self.phase = Phase::Initial;
                } else {
                    self.phase = Phase::QuotientTypeExpose;
                }
            }
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.phase == Phase::ProjectionDelta {
            self.failure = Some(ResourceError::Invariant.into());
            let Auxiliary::Projection(attempt) = &mut self.auxiliary else {
                return Err(ResourceError::Invariant.into());
            };
            attempt.resume_head_reply(head, unchanged)?;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.phase == Phase::Arithmetic {
            self.failure = Some(ResourceError::Invariant.into());
            let Auxiliary::Arithmetic(attempt) = &mut self.auxiliary else {
                return Err(ResourceError::Invariant.into());
            };
            attempt.resume(head)?;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if matches!(
            self.phase,
            Phase::ProjectionSourceLeft | Phase::ProjectionSourceRight
        ) {
            self.failure = Some(ResourceError::Invariant.into());
            head.path.height_since(self.incoming)?;
            let Auxiliary::Projection(attempt) = &mut self.auxiliary else {
                return Err(ResourceError::Invariant.into());
            };
            if self.phase == Phase::ProjectionSourceLeft {
                attempt.left = head;
                self.phase = Phase::ProjectionSourceRight;
            } else {
                attempt.right = head;
                self.phase = Phase::ProjectionSelect;
            }
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if matches!(
            self.phase,
            Phase::FullProjectionLeft
                | Phase::FullProjectionRight
                | Phase::FullProjectionRightUnchanged
                | Phase::ProjectionRetryLeft
                | Phase::ProjectionRetryRight
                | Phase::ProjectionRetryRightUnchanged
                | Phase::EtaFullLeft
                | Phase::EtaFullRight
                | Phase::EtaFullRightUnchanged
        ) {
            self.failure = Some(ResourceError::Invariant.into());
            head.path.height_since(self.incoming)?;
            let eta = matches!(
                self.phase,
                Phase::EtaFullLeft | Phase::EtaFullRight | Phase::EtaFullRightUnchanged
            );
            let projection_retry = matches!(
                self.phase,
                Phase::ProjectionRetryLeft
                    | Phase::ProjectionRetryRight
                    | Phase::ProjectionRetryRightUnchanged
            );
            if matches!(
                self.phase,
                Phase::FullProjectionLeft | Phase::EtaFullLeft | Phase::ProjectionRetryLeft
            ) {
                self.observed = Some(head);
                self.phase = if projection_retry {
                    if unchanged {
                        Phase::ProjectionRetryRightUnchanged
                    } else {
                        Phase::ProjectionRetryRight
                    }
                } else if eta {
                    if unchanged {
                        Phase::EtaFullRightUnchanged
                    } else {
                        Phase::EtaFullRight
                    }
                } else {
                    if unchanged {
                        Phase::FullProjectionRightUnchanged
                    } else {
                        Phase::FullProjectionRight
                    }
                };
            } else {
                let left = self.observed.take().ok_or(ResourceError::Invariant)?;
                self.incoming = left.path.maximum(head.path);
                // The left status belongs only to this pending sibling pair.
                // Three phase variants retain it without growing suspended state.
                let left_unchanged = matches!(
                    self.phase,
                    Phase::FullProjectionRightUnchanged
                        | Phase::ProjectionRetryRightUnchanged
                        | Phase::EtaFullRightUnchanged
                );
                let progressed = (!left_unchanged && left.expression != self.left)
                    || (!unchanged && head.expression != self.right);
                self.left = left.expression;
                self.right = head.expression;
                if progressed {
                    self.left_normal = None;
                    self.exposed = false;
                    self.delta_sides = 0;
                    self.phase = Phase::Initial;
                } else {
                    self.phase = if projection_retry {
                        Phase::GeneralStructureClassify
                    } else if eta {
                        Phase::EtaReady
                    } else {
                        Phase::Rigid
                    };
                }
            }
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if self.phase == Phase::Reflection {
            self.failure = Some(ResourceError::Invariant.into());
            head.path.height_since(self.incoming)?;
            self.observed = Some(head);
            self.phase = Phase::ReflectionDone;
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if matches!(
            self.phase,
            Phase::ExposeSort | Phase::EtaLeftExpose | Phase::EtaRightExpose
        ) {
            self.failure = Some(ResourceError::Invariant.into());
            head.path
                .height_since(self.observed.ok_or(ResourceError::Invariant)?.path)?;
            self.observed = Some(head);
            self.phase = match self.phase {
                Phase::EtaLeftExpose => Phase::EtaLeftBuild,
                Phase::EtaRightExpose => Phase::EtaRightBuild,
                _ => Phase::Classify,
            };
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if matches!(
            self.phase,
            Phase::StructureLeftExpose | Phase::StructureRightExpose
        ) {
            self.failure = Some(ResourceError::Invariant.into());
            head.path.height_since(self.incoming)?;
            self.observed = Some(head);
            self.phase = if self.phase == Phase::StructureLeftExpose {
                Phase::StructureLeftBuild
            } else {
                Phase::StructureRightBuild
            };
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if matches!(
            self.phase,
            Phase::UnitExpose
                | Phase::QuotientTypeExpose
                | Phase::ArgumentTypeExpose
                | Phase::LocalConstructorExpose
                | Phase::LocalApplicationExpose
                | Phase::DistinctConstructorsExpose
                | Phase::RigidConstantsExpose
                | Phase::NoRuleExpose
                | Phase::RecursorLocalExpose
                | Phase::RecursorZeroExpose
                | Phase::RecursorProjectionExpose
                | Phase::LocalProjectionExpose
                | Phase::FunctionEtaFailedExpose
                | Phase::ConstructorFailedExpose
        ) {
            self.failure = Some(ResourceError::Invariant.into());
            head.path.height_since(self.incoming)?;
            self.observed = Some(head);
            self.phase = match self.phase {
                Phase::UnitExpose => Phase::UnitClassify,
                Phase::QuotientTypeExpose => Phase::QuotientTypeClassify,
                Phase::LocalConstructorExpose => Phase::LocalConstructorClassify,
                Phase::LocalApplicationExpose => Phase::LocalApplicationClassify,
                Phase::FunctionEtaFailedExpose => Phase::FunctionEtaFailedClassify,
                Phase::ConstructorFailedExpose => Phase::ConstructorFailedClassify,
                Phase::RecursorLocalExpose => Phase::RecursorLocalClassify,
                Phase::RecursorZeroExpose => Phase::RecursorZeroClassify,
                Phase::RecursorProjectionExpose => Phase::RecursorProjectionClassify,
                Phase::LocalProjectionExpose => Phase::LocalProjectionClassify,
                Phase::DistinctConstructorsExpose => Phase::DistinctConstructorsClassify,
                Phase::RigidConstantsExpose => Phase::RigidConstantsClassify,
                Phase::NoRuleExpose => Phase::NoRuleClassify,
                _ => Phase::ArgumentTypeClassify,
            };
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if matches!(
            self.phase,
            Phase::PairedProjectionLeft | Phase::PairedProjectionRight
        ) {
            self.failure = Some(ResourceError::Invariant.into());
            head.path.height_since(self.incoming)?;
            let root = if self.phase == Phase::PairedProjectionLeft {
                &mut self.left
            } else {
                &mut self.right
            };
            let changed = !unchanged && *root != head.expression;
            *root = head.expression;
            self.incoming = head.path;
            self.delta_sides &= 3;
            self.phase = if changed {
                Phase::PairedPrefix
            } else {
                Phase::PairedUnfold
            };
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if matches!(self.phase, Phase::PairedLeft | Phase::PairedRight) {
            self.failure = Some(ResourceError::Invariant.into());
            head.path.height_since(self.incoming.after_reduction()?)?;
            if self.phase == Phase::PairedLeft {
                self.left = head.expression;
                if self.delta_sides & 2 != 0 {
                    self.observed = Some(head);
                    self.phase = Phase::PairedRight;
                } else {
                    self.incoming = head.path;
                    self.phase = Phase::PairedPrefix;
                }
            } else {
                self.right = head.expression;
                self.incoming = self
                    .observed
                    .take()
                    .map_or(head.path, |left| left.path.maximum(head.path));
                self.phase = Phase::PairedPrefix;
            }
            self.waiting = false;
            self.failure = None;
            return Ok(());
        }
        if matches!(self.phase, Phase::CheapLeft | Phase::CheapRight) {
            self.failure = Some(ResourceError::Invariant.into());
            let result = (|| {
                head.path.height_since(self.incoming)?;
                if self.phase == Phase::CheapLeft {
                    self.left = head.expression;
                    self.left_normal = Some(Normal {
                        expression: head.expression,
                        height: head.path.height_since(self.incoming)?,
                    });
                    self.phase = Phase::CheapRight;
                } else {
                    self.right = head.expression;
                    let left = self.left_normal.take().ok_or(ResourceError::Invariant)?;
                    self.incoming = self
                        .incoming
                        .after_height(left.height.max(head.path.height_since(self.incoming)?))?;
                    self.exposed = true;
                    self.phase = Phase::Prefix;
                }
                self.waiting = false;
                Ok(())
            })();
            self.failure = result.as_ref().err().copied();
            return result;
        }
        self.failure = Some(ResourceError::Invariant.into());
        let result = self
            .auxiliary
            .as_mut()
            .ok_or(ResourceError::Invariant)
            .map_err(HeadError::from)?
            .resume_head(head);
        self.failure = result.as_ref().err().copied();
        if result.is_ok() {
            self.waiting = false;
        }
        result
    }

    fn next_general_structure_attempt(&mut self) -> Result<(), HeadError> {
        if !matches!(self.auxiliary, Auxiliary::GeneralStructure(_)) {
            return Err(ResourceError::Invariant.into());
        }
        let attempt = self.auxiliary.constructor()?;
        self.incoming = attempt.incoming;
        self.binders.result = attempt.prior;
        attempt.maximum = attempt.incoming;
        attempt.left_constructor = false;
        self.observed = None;
        self.phase = Phase::ConstructorRightPrepare;
        Ok(())
    }

    fn next_constructor_attempt(&mut self) -> Result<(), HeadError> {
        let positive_only = matches!(self.auxiliary, Auxiliary::GeneralStructure(_));
        let attempt = self.auxiliary.constructor()?;
        self.incoming = attempt.incoming;
        self.binders.result = attempt.prior;
        attempt.maximum = attempt.incoming;
        self.observed = None;
        self.phase = if attempt.left_constructor {
            if positive_only {
                Phase::InconclusiveFallback
            } else {
                Phase::ConstructorFailedExpose
            }
        } else {
            Phase::ConstructorLeftPrepare
        };
        Ok(())
    }

    fn release_arguments(&mut self, budget: &mut Budget) -> Result<(), HeadError> {
        let arguments = std::mem::take(&mut self.arguments);
        let count = arguments.len();
        let storage = super::super::release(arguments, budget)
            .err()
            .map(HeadError::from);
        let frames = budget.release_frames(count).err().map(HeadError::from);
        match select_failure([storage, frames, None, None]) {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }

    pub(crate) fn abandon(
        mut self,
        ledger: &mut SessionCacheBudget,
        budget: &mut Budget,
    ) -> Result<(), HeadError> {
        if self.failure == Some(HeadError::Unsupported) {
            self.failure = None;
        }
        let normal = self
            .auxiliary
            .take()
            .and_then(|normal| normal.abandon(budget).err());
        let cleanup = self.retire(ledger, budget).err();
        match select_failure([cleanup, normal, None, None]) {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }

    pub(crate) fn retire(
        mut self,
        ledger: &mut SessionCacheBudget,
        budget: &mut Budget,
    ) -> Result<(), HeadError> {
        let arguments = self.release_arguments(budget).err();
        let normal = self
            .auxiliary
            .take()
            .and_then(|normal| normal.retire(budget).err());
        let cache = self.cache.retire(ledger, budget).err().map(HeadError::from);
        // On interruption, the declaration owner discards the entire context;
        // do not pop through locals owned by an abandoned child normalization.
        let count = self.binders.locals.len();
        let storage = super::super::release(self.binders.locals, budget)
            .err()
            .map(HeadError::from);
        let frames = budget.release_frames(count).err().map(HeadError::from);
        let error = select_failure([self.failure, normal, cache, storage]);
        match select_failure([error, frames, arguments, None]) {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
}

// Classification-only test access: this asserts route eligibility, never a verdict.

// Test-only syntax classifier: no checking judgment is asserted for these inputs.

// Protocol regression with a real validated constructor. The deliberately wrong
// exposed type tests abandonment, not a well-typed structure-eta judgment.

// Storage-authority test boundary only: a positive classification is not a
// checkedness or conversion certificate and is never returned as a verdict.

#[cfg(feature = "introspection")]
impl Machine {
    pub(crate) fn colimit_probe(&self, sources: crate::check::diagnostic::Sources<'_>) {
        use crate::check::diagnostic::{Limits, term};
        eprintln!(
            "COLIMIT C {:?} restricted={} left={} right={}\nLEFT {}\nRIGHT {}",
            self.phase,
            self.inconclusive,
            self.left.slot(),
            self.right.slot(),
            term(self.left, sources, Limits::DEFAULT).as_str(),
            term(self.right, sources, Limits::DEFAULT).as_str()
        );
    }
}
