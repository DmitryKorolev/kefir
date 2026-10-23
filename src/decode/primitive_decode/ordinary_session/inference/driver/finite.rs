//! Attempt: same-owner Bool replies, ordinary checked case children,
//! quarantined caches, and complete local/syntax retirement before restoration.
use super::*;
use crate::check::environment::{FiniteReferent, FiniteRequest};
use crate::syntax::expressions::Watermark;
use crate::syntax::levels::LevelNames;
use std::ops::{Deref, DerefMut};

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) struct Boundary {
    pub source: ExprId,
    pub consumer: u32,
    pub saved_end: u32,
    pub saved_depth: u32,
}
enum Permission {
    Typed,
    Observation,
    Waiting(Boundary),
}
pub(super) struct GuardedHead {
    machine: head::Machine,
    missed: Option<Boundary>,
    permission: Permission,
}
impl GuardedHead {
    pub(super) fn new(machine: head::Machine) -> Self {
        // Minted only by the private checked Head-seed gateway; descendants of
        // an actual type-observation owner are revoked at creation below.
        Self {
            machine,
            missed: None,
            permission: Permission::Typed,
        }
    }
    pub(super) fn observe(&mut self) {
        self.permission = Permission::Observation;
    }
    pub(super) fn candidate(
        &self,
        work: &mut Working<'_>,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<Option<FiniteRequest>, Stop> {
        if !matches!(self.permission, Permission::Typed) {
            return Ok(None);
        }
        let request = self.machine.finite_candidate(
            scope,
            environment,
            work.expressions,
            work.levels,
            work.names,
            work.budget,
        )?;
        Ok(request.filter(|r| {
            self.missed
                != Some(Boundary {
                    source: r.source,
                    consumer: r.consumer,
                    saved_end: r.saved_end,
                    saved_depth: r.saved_depth,
                })
        }))
    }
    pub(super) fn retire(self, b: &mut Budget) -> Result<(), HeadError> {
        self.machine.retire(b)
    }
    pub(super) fn abandon(self, b: &mut Budget) -> Result<(), HeadError> {
        self.machine.abandon(b)
    }
}
impl Deref for GuardedHead {
    type Target = head::Machine;
    fn deref(&self) -> &Self::Target {
        &self.machine
    }
}
impl DerefMut for GuardedHead {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.machine
    }
}
const _: () = assert!(size_of::<GuardedHead>() == 176);

struct Caches {
    templates: crate::check::environment::instantiation::Cache,
    heads: head_cache::Cache,
    plans: crate::syntax::expressions::binding::plan::Cache,
    universes: SharedMemo,
}
impl Caches {
    fn take(
        templates: &mut crate::check::environment::instantiation::Cache,
        heads: &mut head_cache::Cache,
        plans: &mut crate::syntax::expressions::binding::plan::Cache,
        universes: &mut SharedMemo,
    ) -> Self {
        Self {
            templates: std::mem::take(templates),
            heads: std::mem::take(heads),
            plans: std::mem::take(plans),
            universes: std::mem::take(universes),
        }
    }
    fn retire(self, work: &mut Working<'_>) -> Result<(), Stop> {
        let failure = machine::select_failure([
            self.templates
                .retire(&mut work.caches, work.budget)
                .err()
                .map(Stop::Resource),
            self.heads.retire(work).err().map(Stop::Resource),
            self.plans
                .retire(&mut work.caches, work.budget)
                .err()
                .map(Stop::Resource),
            self.universes
                .retire(&mut work.caches, work.budget)
                .err()
                .map(Stop::Resource),
        ]);
        failure.map_or(Ok(()), Err)
    }
}
struct Marks {
    expressions: Watermark,
    levels: usize,
    names: usize,
    local_entries: usize,
    local_depth: usize,
}
impl Marks {
    fn capture(work: &Working<'_>) -> Self {
        Self {
            expressions: work.expressions.watermark(),
            levels: work.levels.len(),
            names: work.names.len(),
            local_entries: work.context.entry_count(),
            local_depth: work.context.depth(),
        }
    }
    fn rollback(&self, inert: ExprId, work: &mut Working<'_>) -> Result<(), Stop> {
        work.context.unwind_to(self.local_depth, work.budget)?;
        work.context.retire_inactive_since(
            self.local_entries,
            self.local_depth,
            inert,
            work.budget,
        )?;
        work.expressions
            .discard_since(self.expressions, work.budget)?;
        work.levels.discard_since(self.levels, work.budget)?;
        work.names.discard_since(self.names, work.budget)?;
        Ok(())
    }
}
#[derive(Clone, Copy)]
pub(in crate::decode::primitive_decode::ordinary_session::inference) struct Reply {
    boundary: Boundary,
    height: u32,
    tag: bool,
}
const _: () = assert!(size_of::<Reply>() == 24);
/// Valid only within this flat driver's fixed declaration/environment and while
/// the ancestor controller remains suspended. Values/types are checked closed
/// terms. Consecutive identities are established by bind_bank's child-free loop.
#[derive(Clone, Copy)]
pub(super) struct BankView {
    bound: ExprId,
    first: u32,
    height: u32,
    count: u16,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Phase {
    Bound,
    BindPType,
    InferPType,
    BindHType,
    InferHType,
    BankType,
    InferBankType,
    BankGenerate,
    InferBankValue,
    CompareBankValue,
    Start,
    InferObserver,
    Expose,
    RetireTrue,
    RetireFalse,
    Miss,
}
pub(super) struct State {
    original_head: GuardedHead,
    original_origin: head_cache::Origin,
    suspended: Caches,
    attempt: Marks,
    case: Marks,
    operands: [ExprId; 4],
    bank: Option<BankView>,
    bank_values: Vec<ExprId>,
    bank_type: Option<ExprId>,
    bank_height: u32,
    // A zero sentinel is valid only in retired phases. Every temporary root is
    // freshly appended above the nonempty imported store and thus nonzero.
    temporary: [ExprId; 3], // generated H case, expected Decidable type, inferred type
    failure: Option<Stop>,
    incoming: ReductionPath,
    maximum_height: u32,
    case_height: u32,
    boundary: Boundary,
    bound: u16,
    case_index: u16,
    phase: Phase,
    finite: bool,
}
const _: () = assert!(size_of::<State>() <= 896);

pub(super) fn ancestor_bank<'a>(
    ancestors: impl DoubleEndedIterator<Item = &'a Job>,
    bound: ExprId,
) -> Option<BankView> {
    ancestors.rev().find_map(|job| match &job.owner {
        Owner::Finite(owned) => owned
            .first()
            .and_then(|state| state.bank)
            .filter(|bank| bank.bound == bound),
        _ => None,
    })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn begin(
    job: &mut Job,
    request: FiniteRequest,
    bank: Option<BankView>,
    work: &mut Working<'_>,
    templates: &mut crate::check::environment::instantiation::Cache,
    heads: &mut head_cache::Cache,
    plans: &mut crate::syntax::expressions::binding::plan::Cache,
    universes: &mut SharedMemo,
) -> Result<(), Stop> {
    if !matches!(&job.owner, Owner::Head(head,_) if matches!(head.permission,Permission::Typed)) {
        return Err(ResourceError::Invariant.into());
    }
    // The nine fixed schema/destruction units were paid during mapping.
    // The case precharge waits for ordinary completed bound exposure.
    let bytes = size_of::<State>() as u64;
    work.budget.charge_work(1)?;
    work.budget.reserve(bytes)?;
    let mut owned = Vec::new();
    if owned.try_reserve_exact(1).is_err() {
        work.budget.release(bytes)?;
        return Err(ResourceError::Allocation.into());
    }
    work.budget.observe(Event::Allocations, 1);
    if owned.capacity() != 1 {
        drop(owned);
        work.budget.release(bytes)?;
        return Err(ResourceError::Invariant.into());
    }
    let boundary = Boundary {
        source: request.source,
        consumer: request.consumer,
        saved_end: request.saved_end,
        saved_depth: request.saved_depth,
    };
    let old = std::mem::replace(&mut job.owner, Owner::Vacant);
    let (mut original_head, original_origin) = match old {
        Owner::Head(head, origin) => (head, origin),
        other => {
            job.owner = other;
            drop(owned);
            work.budget.release(bytes)?;
            return Err(ResourceError::Invariant.into());
        }
    };
    original_head.permission = Permission::Waiting(boundary);
    let incoming = original_head.finite_incoming();
    owned.push(State {
        original_head,
        original_origin,
        suspended: Caches::take(templates, heads, plans, universes),
        attempt: Marks::capture(work),
        case: Marks::capture(work),
        operands: request.operands,
        bank,
        bank_values: Vec::new(),
        bank_type: None,
        bank_height: 0,
        temporary: [ExprId::from_stored_original(0); 3],
        failure: None,
        incoming,
        maximum_height: 0,
        case_height: 0,
        boundary,
        bound: 0,
        case_index: 0,
        phase: Phase::Bound,
        finite: request.finite,
    });
    job.owner = Owner::Finite(owned);
    Ok(())
}

impl State {
    #[allow(clippy::too_many_arguments)]
    #[allow(
        clippy::let_and_return,
        reason = "test-only observer omitted from public source"
    )]
    pub(super) fn advance(
        &mut self,
        work: &mut Working<'_>,
        scope: &Scope<'_>,
        environment: &Environment,
        templates: &mut crate::check::environment::instantiation::Cache,
        heads: &mut head_cache::Cache,
        plans: &mut crate::syntax::expressions::binding::plan::Cache,
        universes: &mut SharedMemo,
    ) -> Result<Step, Stop> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        work.budget.charge_work(1)?;
        let result = match self.phase {
            Phase::Bound => Ok(Step::Need(Seed::Head(self.operands[1], self.incoming))),
            Phase::BindPType | Phase::BindHType => {
                let predicate = self.phase == Phase::BindPType;
                self.temporary[0] = self.alias_type(predicate, work, scope, environment)?;
                self.phase = if predicate {
                    Phase::InferPType
                } else {
                    Phase::InferHType
                };
                Ok(Step::Need(Seed::Inference(
                    self.temporary[0],
                    self.incoming,
                )))
            }
            Phase::BankType => {
                let fin = Self::constant(FiniteReferent::FinType, work, scope, environment)?;
                let ty = Self::app(fin, self.operands[1], work)?;
                self.bank_type = Some(ty);
                self.phase = Phase::InferBankType;
                Ok(Step::Need(Seed::Inference(ty, self.incoming)))
            }
            Phase::BankGenerate if self.case_index == self.bound => {
                self.bind_bank(work)?;
                self.phase = Phase::Start;
                Ok(Step::More)
            }
            Phase::BankGenerate => {
                self.temporary[0] = self.witness(work, scope, environment)?;
                self.phase = Phase::InferBankValue;
                Ok(Step::Need(Seed::Inference(
                    self.temporary[0],
                    self.incoming,
                )))
            }
            Phase::CompareBankValue => Ok(Step::Need(Seed::Comparison(
                self.temporary[2],
                self.bank_type.ok_or(ResourceError::Invariant)?,
                self.incoming.after_height(self.case_height)?,
            ))),
            Phase::Start if self.case_index == self.bound => {
                Ok(Step::Complete(Completed::Finite(Reply {
                    boundary: self.boundary,
                    height: self.maximum_height,
                    tag: true,
                })))
            }
            Phase::Start => {
                self.generate(work, scope, environment)?;
                self.phase = Phase::InferObserver;
                Ok(Step::Need(Seed::Inference(
                    self.temporary[0],
                    self.incoming,
                )))
            }
            Phase::Expose => Ok(Step::Need(Seed::Head(
                self.temporary[0],
                self.incoming.after_height(self.case_height)?,
            ))),
            Phase::RetireTrue | Phase::RetireFalse => {
                let tag = self.phase == Phase::RetireTrue;
                self.maximum_height = self.maximum_height.max(self.case_height);
                self.retire_case(work, templates, heads, plans, universes, false)?;
                if tag {
                    self.case_index = self
                        .case_index
                        .checked_add(1)
                        .ok_or(ResourceError::Counter)?;
                    self.phase = Phase::Start;
                    Ok(Step::More)
                } else {
                    Ok(Step::Complete(Completed::Finite(Reply {
                        boundary: self.boundary,
                        height: self.maximum_height,
                        tag: false,
                    })))
                }
            }
            Phase::Miss => Ok(Step::FiniteMiss),
            // A waiting phase cannot advance without its completed child reply.
            Phase::InferPType
            | Phase::InferHType
            | Phase::InferObserver
            | Phase::InferBankType
            | Phase::InferBankValue => Err(ResourceError::Invariant.into()),
        };
        result
    }
    pub(super) fn resume(
        &mut self,
        result: Completed,
        work: &mut Working<'_>,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<(), Stop> {
        match (self.phase, result) {
            (Phase::Bound, Completed::Head(head) | Completed::UnchangedHead(head)) => {
                let ExprKind::Natural(text) = work
                    .expressions
                    .get(head.expression, work.budget)?
                    .kind(work.expressions, work.levels, work.budget)?
                else {
                    self.phase = Phase::Miss;
                    return Ok(());
                };
                let bound = if text.len() <= 3 {
                    text.iter().try_fold(0u16, |v, &digit| {
                        v.checked_mul(10)?
                            .checked_add(u16::from(digit.checked_sub(b'0')?))
                    })
                } else {
                    None
                };
                let Some(bound) = bound.filter(|&n| n <= 256) else {
                    self.phase = Phase::Miss;
                    return Ok(());
                };
                work.budget.charge_work(
                    u64::from(bound)
                        .checked_mul(2)
                        .ok_or(ResourceError::Counter)?,
                )?;
                self.maximum_height = head.path.height_since(self.incoming)?;
                self.bound = bound;
                self.phase = if bound == 0 {
                    Phase::Start
                } else {
                    Phase::BindPType
                };
            }
            (Phase::InferBankType, Completed::Inference(inferred)) => {
                if !matches!(
                    work.expressions.get(inferred.ty, work.budget)?.kind(
                        work.expressions,
                        work.levels,
                        work.budget
                    )?,
                    ExprKind::Sort(_)
                ) {
                    return Err(ResourceError::Invariant.into());
                }
                self.bank_height = inferred.path.height_since(self.incoming)?;
                self.phase = Phase::BankGenerate;
            }
            (Phase::InferBankValue, Completed::Inference(inferred)) => {
                self.temporary[2] = inferred.ty;
                self.case_height = inferred.path.height_since(self.incoming)?;
                self.phase = Phase::CompareBankValue;
            }
            (Phase::CompareBankValue, Completed::Comparison(comparison::Decision::Equal(path))) => {
                let value = self.temporary[0];
                let node = work.expressions.get(value, work.budget)?;
                if node.loose_range() != 0 || node.has_free() {
                    return Err(ResourceError::Invariant.into());
                }
                self.bank_height = self.bank_height.max(path.height_since(self.incoming)?);
                let count = self
                    .bank_values
                    .len()
                    .checked_add(1)
                    .ok_or(ResourceError::Counter)?;
                work.budget.grow_vec(&mut self.bank_values, count)?;
                self.bank_values.push(value);
                self.temporary = [ExprId::from_stored_original(0); 3];
                self.case_index = self
                    .case_index
                    .checked_add(1)
                    .ok_or(ResourceError::Counter)?;
                self.phase = Phase::BankGenerate;
            }
            (Phase::InferPType | Phase::InferHType, Completed::Inference(inferred)) => {
                if !matches!(
                    work.expressions.get(inferred.ty, work.budget)?.kind(
                        work.expressions,
                        work.levels,
                        work.budget
                    )?,
                    ExprKind::Sort(_)
                ) {
                    return Err(ResourceError::Invariant.into());
                }
                self.maximum_height = self
                    .maximum_height
                    .max(inferred.path.height_since(self.incoming)?);
                let predicate = self.phase == Phase::InferPType;
                let index = if predicate { 2 } else { 3 };
                // Formation of this independently constructed schema completed.
                // Value typing is a separate premise: invert the exact originally
                // checked family application. For H, the live P alias denotes
                // its checked original value by the ordinary let rule. Nothing
                // here certifies an unchecked/generated decision or witness.
                let local = work.context.enter_checked(
                    CheckedTy::checked_decode_session(self.temporary[0], CheckednessMint::mint()),
                    Some(CheckedVal::checked_decode_session(
                        self.operands[index],
                        CheckednessMint::mint(),
                    )),
                    NameId::ANONYMOUS,
                    BinderInfo::Default,
                    work.expressions,
                    work.names,
                    work.budget,
                )?;
                self.operands[index] = work.expressions.append(
                    ExprKind::Free(local.slot()),
                    work.levels,
                    work.names,
                    work.budget,
                )?;
                self.temporary = [ExprId::from_stored_original(0); 3];
                if predicate {
                    self.phase = Phase::BindHType;
                } else {
                    // Cross-case aliases and schemas predate every case mark.
                    self.case = Marks::capture(work);
                    let bound = work.expressions.get(self.operands[1], work.budget)?;
                    let closed = bound.loose_range() == 0 && !bound.has_free();
                    self.bank = self.bank.filter(|bank| {
                        self.finite
                            && closed
                            && bank.bound == self.operands[1]
                            && bank.count == self.bound
                    });
                    self.phase = if let Some(bank) = self.bank {
                        self.maximum_height = self.maximum_height.max(bank.height);
                        Phase::Start
                    } else if self.finite && closed {
                        Phase::BankType
                    } else {
                        Phase::Start
                    };
                }
            }
            (Phase::InferObserver, Completed::Inference(inferred)) => {
                // Ordinary checking of this saturated certified decide application
                // established its Bool result type; no untyped observer is exposed.
                self.case_height = self
                    .case_height
                    .max(inferred.path.height_since(self.incoming)?);
                self.phase = Phase::Expose;
            }
            (Phase::Expose, Completed::Head(head) | Completed::UnchangedHead(head)) => {
                let Some(tag) = self.completed_tag(head.expression, work, scope, environment)?
                else {
                    self.phase = Phase::Miss;
                    return Ok(());
                };
                self.case_height = self.case_height.max(head.path.height_since(self.incoming)?);
                self.phase = if tag {
                    Phase::RetireTrue
                } else {
                    Phase::RetireFalse
                };
            }
            // A generated type disagreement is an implementation failure,
            // never an original proof rejection or a candidate miss.
            _ => return Err(ResourceError::Invariant.into()),
        }
        Ok(())
    }
    pub(super) fn miss(&mut self) {
        self.phase = Phase::Miss;
    }
    fn constant(
        referent: FiniteReferent,
        work: &mut Working<'_>,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<ExprId, Stop> {
        let name = environment
            .finite_name(referent, scope, work.names, work.budget)?
            .ok_or(ResourceError::Invariant)?;
        Ok(work.expressions.append(
            ExprKind::Constant(name, &[]),
            work.levels,
            work.names,
            work.budget,
        )?)
    }
    fn app(function: ExprId, argument: ExprId, work: &mut Working<'_>) -> Result<ExprId, Stop> {
        Ok(work.expressions.append(
            ExprKind::App(function, argument),
            work.levels,
            work.names,
            work.budget,
        )?)
    }
    fn natural(value: u16, work: &mut Working<'_>) -> Result<ExprId, Stop> {
        let mut digits = [0u8; 3];
        let mut n = value;
        let mut at = digits.len();
        loop {
            at -= 1;
            digits[at] = b'0' + (n % 10) as u8;
            n /= 10;
            if n == 0 {
                break;
            }
        }
        Ok(work.expressions.append(
            ExprKind::Natural(&digits[at..]),
            work.levels,
            work.names,
            work.budget,
        )?)
    }
    fn alias_type(
        &self,
        predicate: bool,
        work: &mut Working<'_>,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<ExprId, Stop> {
        let prop = work.expressions.append(
            ExprKind::Sort(crate::syntax::levels::LevelId::ZERO),
            work.levels,
            work.names,
            work.budget,
        )?;
        let argument =
            work.expressions
                .append(ExprKind::Bound(0), work.levels, work.names, work.budget)?;
        let domain = if self.finite {
            let fin = Self::constant(FiniteReferent::FinType, work, scope, environment)?;
            Self::app(fin, self.operands[1], work)?
        } else {
            Self::constant(FiniteReferent::NaturalType, work, scope, environment)?
        };
        let mut result = if predicate {
            prop
        } else {
            let applied = if self.finite {
                Self::app(self.operands[2], argument, work)?
            } else {
                let k = work.expressions.append(
                    ExprKind::Bound(1),
                    work.levels,
                    work.names,
                    work.budget,
                )?;
                let p = Self::app(self.operands[2], k, work)?;
                Self::app(p, argument, work)?
            };
            let decidable = Self::constant(FiniteReferent::Decidable, work, scope, environment)?;
            Self::app(decidable, applied, work)?
        };
        if !self.finite {
            let less = Self::constant(FiniteReferent::NaturalLt, work, scope, environment)?;
            let proof_domain = Self::app(less, argument, work)?;
            let proof_domain = Self::app(proof_domain, self.operands[1], work)?;
            result = work.expressions.append(
                ExprKind::Pi(NameId::ANONYMOUS, proof_domain, result, BinderInfo::Default),
                work.levels,
                work.names,
                work.budget,
            )?;
        }
        Ok(work.expressions.append(
            ExprKind::Pi(NameId::ANONYMOUS, domain, result, BinderInfo::Default),
            work.levels,
            work.names,
            work.budget,
        )?)
    }
    fn witness(
        &self,
        work: &mut Working<'_>,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<ExprId, Stop> {
        let k = Self::natural(self.case_index, work)?;
        let start = Self::natural(self.case_index + 1, work)?;
        let refl = Self::constant(FiniteReferent::Refl, work, scope, environment)?;
        let mut proof = Self::app(refl, start, work)?;
        let step = Self::constant(FiniteReferent::SuccLt, work, scope, environment)?;
        for next in self.case_index + 1..self.bound {
            let m = Self::natural(next, work)?;
            let f = Self::app(step, k, work)?;
            let f = Self::app(f, m, work)?;
            proof = Self::app(f, proof, work)?;
        }
        let constructor = Self::constant(FiniteReferent::FinMk, work, scope, environment)?;
        let fin = Self::app(constructor, self.operands[1], work)?;
        let fin = Self::app(fin, k, work)?;
        Self::app(fin, proof, work)
    }

    fn bind_bank(&mut self, work: &mut Working<'_>) -> Result<(), Stop> {
        let ty = self.bank_type.ok_or(ResourceError::Invariant)?;
        if self.bank_values.len() != self.bound as usize || self.bound == 0 {
            return Err(ResourceError::Invariant.into());
        }
        let node = work.expressions.get(ty, work.budget)?;
        if node.loose_range() != 0 || node.has_free() {
            return Err(ResourceError::Invariant.into());
        }
        let mut first = None;
        work.budget.charge_work(u64::from(self.bound))?;
        // Every value's ordinary inference and comparison already completed.
        // No child runs in this loop, so enter_checked allocates consecutive IDs.
        for (index, &value) in self.bank_values.iter().enumerate() {
            let local = work.context.enter_checked(
                CheckedTy::checked_decode_session(ty, CheckednessMint::mint()),
                Some(CheckedVal::checked_decode_session(
                    value,
                    CheckednessMint::mint(),
                )),
                NameId::ANONYMOUS,
                BinderInfo::Default,
                work.expressions,
                work.names,
                work.budget,
            )?;
            let start = *first.get_or_insert(local.slot());
            if start.checked_add(index as u32) != Some(local.slot()) {
                return Err(ResourceError::Invariant.into());
            }
        }
        self.bank = Some(BankView {
            bound: self.operands[1],
            first: first.ok_or(ResourceError::Invariant)?,
            count: self.bound,
            height: self.bank_height,
        });
        self.maximum_height = self.maximum_height.max(self.bank_height);
        self.bank_values.clear();
        self.case_index = 0;
        self.case = Marks::capture(work);
        Ok(())
    }

    fn retire_bank(&mut self, work: &mut Working<'_>) -> Result<(), Stop> {
        self.bank = None;
        self.bank_type = None;
        let values = std::mem::take(&mut self.bank_values);
        let bytes = values
            .capacity()
            .checked_mul(size_of::<ExprId>())
            .ok_or(ResourceError::Counter)?;
        drop(values);
        work.budget.release(bytes as u64)?;
        Ok(())
    }

    fn generate(
        &mut self,
        work: &mut Working<'_>,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<(), Stop> {
        if self.case_index >= self.bound || self.bound > 256 {
            return Err(ResourceError::Invariant.into());
        }
        let (predicate, case) = if self.finite {
            let fin = if let Some(bank) = self.bank {
                let id = bank
                    .first
                    .checked_add(u32::from(self.case_index))
                    .ok_or(ResourceError::Counter)?;
                // The ancestor bank is live in the unchanged driver context.
                // Ordinary case inference consumes this checked local argument.
                work.expressions
                    .append(ExprKind::Free(id), work.levels, work.names, work.budget)?
            } else {
                self.witness(work, scope, environment)?
            };
            (
                Self::app(self.operands[2], fin, work)?,
                Self::app(self.operands[3], fin, work)?,
            )
        } else {
            let k = Self::natural(self.case_index, work)?;
            let start = Self::natural(self.case_index + 1, work)?;
            let refl = Self::constant(FiniteReferent::Refl, work, scope, environment)?;
            let mut proof = Self::app(refl, start, work)?;
            let step = Self::constant(FiniteReferent::SuccLt, work, scope, environment)?;
            for next in self.case_index + 1..self.bound {
                let m = Self::natural(next, work)?;
                let f = Self::app(step, k, work)?;
                let f = Self::app(f, m, work)?;
                proof = Self::app(f, proof, work)?;
            }
            let p = Self::app(self.operands[2], k, work)?;
            let h = Self::app(self.operands[3], k, work)?;
            (Self::app(p, proof, work)?, Self::app(h, proof, work)?)
        };
        // Ordinary inference of this complete application checks P case,
        // H case and its Decidable instance type exactly once. It is exposed
        // only after that child judgment completes; no case alias is minted.
        let decide = Self::constant(FiniteReferent::Decide, work, scope, environment)?;
        let observer = Self::app(decide, predicate, work)?;
        let observer = Self::app(observer, case, work)?;
        self.temporary = [
            observer,
            ExprId::from_stored_original(0),
            ExprId::from_stored_original(0),
        ];
        self.case_height = 0;
        Ok(())
    }
    fn completed_tag(
        &self,
        root: ExprId,
        work: &mut Working<'_>,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<Option<bool>, Stop> {
        let ExprKind::Constant(name, []) = work.expressions.get(root, work.budget)?.kind(
            work.expressions,
            work.levels,
            work.budget,
        )?
        else {
            return Ok(None);
        };
        for (referent, tag) in [(FiniteReferent::False, false), (FiniteReferent::True, true)] {
            let expected = environment
                .finite_name(referent, scope, work.names, work.budget)?
                .ok_or(ResourceError::Invariant)?;
            if work.names.summary(name, work.budget)?.canonical
                == work.names.summary(expected, work.budget)?.canonical
            {
                return Ok(Some(tag));
            }
        }
        Ok(None)
    }
    fn retire_case(
        &mut self,
        work: &mut Working<'_>,
        templates: &mut crate::check::environment::instantiation::Cache,
        heads: &mut head_cache::Cache,
        plans: &mut crate::syntax::expressions::binding::plan::Cache,
        universes: &mut SharedMemo,
        force: bool,
    ) -> Result<(), Stop> {
        self.temporary = [ExprId::from_stored_original(0); 3];
        if force || self.phase == Phase::RetireFalse || self.case_index & 7 == 7 {
            // Every cache may retain handles from the whole immutable block.
            // Retire all of them before rolling any backing store back.
            Caches::take(templates, heads, plans, universes).retire(work)?;
            self.case.rollback(self.operands[0], work)?;
            self.case = Marks::capture(work);
        } else {
            // Existing cache admission is context-independent. Historical Free
            // IDs stay unique; discard departed locals' payloads before advancing
            // this mark, while preserving the block's syntax/level/name marks.
            work.context.unwind_to(self.case.local_depth, work.budget)?;
            work.context.retire_inactive_since(
                self.case.local_entries,
                self.case.local_depth,
                self.operands[0],
                work.budget,
            )?;
            self.case.local_entries = work.context.entry_count();
        }
        Ok(())
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn restore(
    job: &mut Job,
    reply: Option<Reply>,
    work: &mut Working<'_>,
    scope: &Scope<'_>,
    environment: &Environment,
    templates: &mut crate::check::environment::instantiation::Cache,
    heads: &mut head_cache::Cache,
    plans: &mut crate::syntax::expressions::binding::plan::Cache,
    universes: &mut SharedMemo,
) -> Result<(), Stop> {
    let Owner::Finite(owned) = &mut job.owner else {
        return Err(ResourceError::Invariant.into());
    };
    let state = owned.first_mut().ok_or(ResourceError::Invariant)?;
    if let Some(reply) = reply {
        if reply.boundary != state.boundary || reply.height != state.maximum_height {
            return Err(ResourceError::Invariant.into());
        }
    } else if state.phase != Phase::Miss {
        return Err(ResourceError::Invariant.into());
    }
    state.retire_bank(work)?;
    state.retire_case(work, templates, heads, plans, universes, true)?;
    // Retire every retained generated alias handle before its syntax suffix.
    state.operands[2] = state.operands[0];
    state.operands[3] = state.operands[0];
    // Charge the complete attempt suffix, including already-cleared case locals.
    state.attempt.rollback(state.operands[0], work)?;
    let old = std::mem::replace(&mut job.owner, Owner::Vacant);
    let Owner::Finite(mut owned) = old else {
        return Err(ResourceError::Invariant.into());
    };
    let state = owned.pop().ok_or(ResourceError::Invariant)?;
    let bytes = owned
        .capacity()
        .checked_mul(size_of::<State>())
        .ok_or(ResourceError::Counter)?;
    drop(owned);
    work.budget.release(bytes as u64)?;
    let State {
        mut original_head,
        original_origin,
        suspended,
        incoming,
        boundary,
        ..
    } = state;
    if !matches!(original_head.permission,Permission::Waiting(b) if b==boundary) {
        return Err(ResourceError::Invariant.into());
    }
    original_head.permission = Permission::Typed;
    if reply.is_none() {
        original_head.missed = Some(boundary);
    }
    *templates = suspended.templates;
    *heads = suspended.heads;
    *plans = suspended.plans;
    *universes = suspended.universes;
    job.owner = Owner::Head(original_head, original_origin);
    if let Some(reply) = reply {
        let expression = State::constant(
            if reply.tag {
                FiniteReferent::True
            } else {
                FiniteReferent::False
            },
            work,
            scope,
            environment,
        )?;
        let result = Head {
            expression,
            path: incoming.after_reduction()?.after_height(reply.height)?,
        };
        let Owner::Head(head, _) = &mut job.owner else {
            return Err(ResourceError::Invariant.into());
        };
        head.resume_finite_bool(
            boundary.source,
            boundary.saved_end,
            boundary.saved_depth,
            result,
            work.budget,
        )?;
    }
    Ok(())
}

/// Terminal destruction performs no speculative syntax rollback or fallback.
/// The ordinary outer poison discards the entire declaration. Retire suspended
/// original owners/caches and release the fixed allocation even on interruption.
pub(super) fn retire(mut owned: Vec<State>, work: &mut Working<'_>) -> Result<(), Stop> {
    let mut failure = None;
    for mut state in owned.drain(..) {
        failure = machine::select_failure([failure, state.retire_bank(work).err(), None, None]);
        failure = machine::select_failure([
            failure,
            state.failure,
            state
                .original_head
                .retire(work.budget)
                .err()
                .map(Stop::Normalization),
            state.suspended.retire(work).err(),
        ]);
    }
    let bytes = owned
        .capacity()
        .checked_mul(size_of::<State>())
        .ok_or(ResourceError::Counter)?;
    drop(owned);
    failure = machine::select_failure([
        failure,
        work.budget.release(bytes as u64).err().map(Stop::Resource),
        None,
        None,
    ]);
    failure.map_or(Ok(()), Err)
}
