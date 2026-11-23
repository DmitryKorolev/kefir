//! A concrete instance of a checked theorem type mismatch.
use super::*;

const CONSTRUCTOR_DEPTH: u8 = 4;
const STRING_CONSTRUCTOR_DEPTH: u8 = 12;
const STRING_WITNESS_MAX_BYTES: usize = 64;

const NATURAL_OBSERVATION_STEPS: u64 = 1 << 16;

/// Leave headroom for both a dispatcher-bounded ordinary trial and the full
/// value witness. Actual work and storage are always charged by their owners.
pub(in crate::check::environment) fn witness_probe_fits(budget: &Budget) -> bool {
    budget.has_work_headroom(2 * MAX_STEPS)
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(in crate::check::environment) enum Witness {
    Different,
    Inconclusive,
    Deferred,
}

const SYMBOLIC_STEPS: u64 = 1 << 23;

struct Schedule {
    // None denotes the ordinary concrete schedule. NONE is replaced by the
    // exact local handle only when the second checked Nat binder is opened.
    symbolic: Option<u32>,
    bound_naturals: bool,
    deferred: bool,
}

#[derive(Clone, Copy)]
struct Application {
    ci: u32,
    li: u32,
    len: usize,
    args: [u32; 8],
}

impl Kernel<'_, '_> {
    fn witness_application(&mut self, v: u32) -> R<Application> {
        let Val::Const { ci, li, mut spine } = self.vals[v as usize] else {
            return no();
        };
        let len = self.cells[spine as usize].len as usize;
        let mut args = [0; 8];
        if len > args.len() {
            return no();
        }
        self.steps_by(1 + len as u64)?;
        for slot in args[..len].iter_mut().rev() {
            let c = self.cells[spine as usize];
            if c.tag != 0 {
                return no();
            }
            *slot = c.item;
            spine = c.prev;
        }
        Ok(Application { ci, li, len, args })
    }

    fn witness_arguments(
        &mut self,
        a: Application,
        b: Application,
        skip: usize,
        depth: u8,
        expand_literals: bool,
        schedule: &mut Schedule,
    ) -> R<bool> {
        if a.ci != b.ci || a.len != b.len || !self.same_levels(a.li, b.li)? {
            return Ok(false);
        }
        let mut ty_a = self.const_type(a.ci, a.li)?;
        let mut ty_b = self.const_type(b.ci, b.li)?;
        // Instantiate both telescopes in order. Give already visible differences
        // the first chance to supply a typed witness before unfolding other fields.
        // The scheduling hint alone carries no evidence.
        let mut deferred = [None; 8];
        for (i, slot) in deferred[..a.len].iter_mut().enumerate() {
            let pa = self.pi_like(ty_a)?;
            let pb = self.pi_like(ty_b)?;
            if i >= skip && a.args[i] != b.args[i] {
                let (da, db) = (self.binder_dom(pa)?, self.binder_dom(pb)?);
                if self.visibly_distinct(a.args[i], b.args[i])? {
                    if self.defeq(da, db)?
                        && self.witness_data(
                            a.args[i],
                            b.args[i],
                            da,
                            depth,
                            expand_literals,
                            schedule,
                        )?
                    {
                        return Ok(true);
                    }
                } else {
                    *slot = Some((da, db));
                }
            }
            ty_a = self.instantiate(pa, a.args[i])?;
            ty_b = self.instantiate(pb, b.args[i])?;
        }
        for (i, domains) in deferred[..a.len].iter().enumerate() {
            if let Some((da, db)) = *domains
                && self.defeq(da, db)?
                && self.witness_data(a.args[i], b.args[i], da, depth, expand_literals, schedule)?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn witness_data(
        &mut self,
        a: u32,
        b: u32,
        ty: u32,
        depth: u8,
        expand_literals: bool,
        schedule: &mut Schedule,
    ) -> R<bool> {
        if depth == 0 || a == b {
            return Ok(false);
        }
        let Some(sort) = self.infer_value(ty)? else {
            return Ok(false);
        };
        let level = self.sort_of(sort)?;
        if self.levels.get(level, self.b)?.positive()
            != crate::syntax::levels::LevelPositive::Proven
        {
            return Ok(false);
        }
        let ty = self.whnf(ty)?;
        let Val::Const { ci: family, .. } = self.vals[ty as usize] else {
            return Ok(false);
        };
        let info = *self.const_view(family)?;
        let Some(ind) = info.ind else {
            return Ok(false);
        };
        if let Some(fresh) = schedule.symbolic {
            return if fresh == NONE {
                Ok(false)
            } else {
                self.symbolic_bool_difference(a, b, info.canon, fresh)
            };
        }
        let observe = |k: &mut Self| Ok((k.whnf(a)?, k.whnf(b)?));
        let (mut a, mut b) = if schedule.bound_naturals
            && self.nat_ctors()?.is_some_and(|(nat, _, _)| nat == family)
        {
            let saved = self.bounds;
            self.limit_total(self.steps.saturating_add(NATURAL_OBSERVATION_STEPS));
            let result = observe(self);
            self.restore_bounds(saved);
            if matches!(result, Err(KErr::Abort)) && self.steps <= self.limit {
                schedule.deferred = true;
            }
            result?
        } else {
            observe(self)?
        };
        let mut expanded = false;
        if expand_literals {
            for value in [&mut a, &mut b] {
                if let Val::Str(literal) = self.vals[*value as usize] {
                    let ExprKind::String(bytes) =
                        self.exprs
                            .get(literal, self.b)?
                            .kind(self.exprs, self.levels, self.b)?
                    else {
                        return Err(ResourceError::Invariant.into());
                    };
                    if bytes.len() > STRING_WITNESS_MAX_BYTES {
                        return Ok(false);
                    }
                    // The operands were independently checked at the common
                    // data type. Expansion computes the same String via the
                    // committed interpretation. It supplies no negative by
                    // itself, even when only the typed interface is available.
                    let v = self.expand_str(literal)?;
                    *value = self.whnf(v)?;
                    expanded = true;
                }
            }
        }
        if let (Val::Nat(x), Val::Nat(y)) = (self.vals[a as usize], self.vals[b as usize]) {
            let nat = self.nat_type()?;
            if !self.defeq(ty, nat)? {
                return Ok(false);
            }
            self.observe_pair(x, y)?;
            return Ok(!nat_eq(
                &self.nats[x as usize],
                &self.nats[y as usize],
                self.b,
            )?);
        }
        if !matches!(
            (self.vals[a as usize], self.vals[b as usize]),
            (Val::Const { .. }, Val::Const { .. })
        ) {
            return Ok(false);
        }
        let (a, b) = (self.witness_application(a)?, self.witness_application(b)?);
        for side in [a, b] {
            let c = *self.const_view(side.ci)?;
            let Some((fam, index)) = c.ctor else {
                return Ok(false);
            };
            if fam != info.canon {
                return Ok(false);
            }
            let rule = ind
                .ctors
                .get(index as usize)
                .ok_or(ResourceError::Invariant)?;
            if side.len != ind.nparams as usize + rule.num_fields as usize {
                return Ok(false);
            }
        }
        if a.ci != b.ci {
            return Ok(true);
        }
        // Spend the additional depth only once along each path. Ordinary
        // constructor and proof-field guards still decide every child.
        let depth = if expanded {
            STRING_CONSTRUCTOR_DEPTH
        } else {
            depth
        };
        self.witness_arguments(
            a,
            b,
            ind.nparams as usize,
            depth - 1,
            expand_literals && !expanded,
            schedule,
        )
    }

    fn witness_argument(&mut self, ty: u32, index: usize, schedule: &mut Schedule) -> R<u32> {
        let nat = self.nat_type()?;
        if self.defeq(ty, nat)? {
            if schedule.symbolic.is_some() {
                if index == 0 {
                    return self.nat(NatLit::Small(0));
                }
                let (_, _, succ) = self.nat_ctors()?.ok_or(KErr::Unsupported)?;
                // This is a new arbitrary Nat in the extended context, not a
                // reusable binder position from the earlier inference pass.
                let local = self.fresh_local(nat)?;
                schedule.symbolic = Some(local);
                let f = self.push(Val::Const {
                    ci: succ,
                    li: 0,
                    spine: 0,
                })?;
                return self.apply(f, local);
            }
            if index == 0 {
                return self.nat(NatLit::Small(1));
            }
            // Two naturals agreeing on low bits, but distinct as unbounded naturals.
            let high = computed_nat(
                Operation::ShiftLeft,
                &NatLit::Small(1),
                &NatLit::Small(16384),
                self.b,
                &mut self.reserved,
            )?;
            let value = computed_nat(
                Operation::Add,
                &high,
                &NatLit::Small(1),
                self.b,
                &mut self.reserved,
            )?;
            return self.nat(value);
        }
        if schedule.symbolic.is_some() {
            return no();
        }
        let Some(name) = self.env.checked_le_name() else {
            return no();
        };
        let ci = self.const_info(name)?;
        if !self.const_view(ci)?.params.is_empty() {
            return no();
        }
        let actual = self.const_type(ci, 0)?;
        if !self.defeq(actual, ty)? {
            return no();
        }
        self.push(Val::Const {
            ci,
            li: 0,
            spine: 0,
        })
    }

    fn theorem_witness(&mut self, request: &Request<'_>, schedule: &mut Schedule) -> R<bool> {
        let sort = self.infer(request.ty, 0, 0, true)?;
        let level = self.sort_of(sort)?;
        if !self.is_zero(level)? {
            return Ok(false);
        }
        let mut actual = self.infer(request.value.ok_or(KErr::Unsupported)?, 0, 0, true)?;
        let mut expected = self.eval(request.ty, 0, 0)?;
        for index in 0..=2 {
            let (a, b) = (self.whnf(actual)?, self.whnf(expected)?);
            if matches!(
                (self.vals[a as usize], self.vals[b as usize]),
                (Val::Const { .. }, Val::Const { .. })
            ) {
                let (a, b) = (self.witness_application(a)?, self.witness_application(b)?);
                let Some(ind) = self.const_view(a.ci)?.ind else {
                    return Ok(false);
                };
                if a.len != ind.nparams as usize + ind.nidx as usize {
                    return Ok(false);
                }
                return self.witness_arguments(a, b, 0, CONSTRUCTOR_DEPTH, true, schedule);
            }
            if index == 2 {
                return Ok(false);
            }
            let (a, b) = (self.pi_like(a)?, self.pi_like(b)?);
            let (da, db) = (self.binder_dom(a)?, self.binder_dom(b)?);
            if !self.defeq(da, db)? {
                return Ok(false);
            }
            let arg = self.witness_argument(da, index, schedule)?;
            actual = self.instantiate(a, arg)?;
            expected = self.instantiate(b, arg)?;
        }
        Ok(false)
    }
}

#[allow(clippy::too_many_arguments)]
pub(in crate::check::environment) fn different(
    environment: &Environment,
    request: &Request<'_>,
    scope: &Scope<'_>,
    names: &Names,
    exprs: &Expressions,
    levels: &mut Levels,
    budget: &mut Budget,
    bound_naturals: bool,
) -> Result<Witness, super::super::normalization::HeadError> {
    if request.kind != Kind::Theorem || !request.parameters.is_empty() || !eligible(request, scope)
    {
        return Ok(Witness::Inconclusive);
    }
    environment.check_scope(
        scope.before,
        scope.formation,
        scope.expression_end,
        scope.level_end,
    )?;
    // The fast positive checker has already tried these roots. Double Pi
    // syntax is only an admission hint. Both domains are checked again.
    if bound_naturals
        && budget.has_work_headroom(2 * MAX_STEPS + SYMBOLIC_STEPS)
        && let ExprKind::Pi(_, _, body, _) =
            exprs.get(request.ty, budget)?.kind(exprs, levels, budget)?
        && matches!(
            exprs.get(body, budget)?.kind(exprs, levels, budget)?,
            ExprKind::Pi(..)
        )
        && attempt(
            environment,
            request,
            scope,
            names,
            exprs,
            levels,
            budget,
            false,
            true,
        )? == Witness::Different
    {
        return Ok(Witness::Different);
    }
    attempt(
        environment,
        request,
        scope,
        names,
        exprs,
        levels,
        budget,
        bound_naturals,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
fn attempt(
    environment: &Environment,
    request: &Request<'_>,
    scope: &Scope<'_>,
    names: &Names,
    exprs: &Expressions,
    levels: &mut Levels,
    budget: &mut Budget,
    bound_naturals: bool,
    symbolic: bool,
) -> Result<Witness, super::super::normalization::HeadError> {
    let mut k = Kernel::new(environment, names, exprs, levels, budget, scope);
    let mut schedule = Schedule {
        symbolic: symbolic.then_some(NONE),
        bound_naturals,
        deferred: false,
    };
    let result = k.init().and_then(|()| {
        if symbolic {
            k.limit_total(SYMBOLIC_STEPS);
        }
        k.theorem_witness(request, &mut schedule)
    });
    let steps = k.steps - k.charged;
    let reserved = k.reserved;
    k.retire_arena();
    drop(k);
    let charge = budget.charge_work(steps);
    let release = budget.release(reserved);
    let complete = finish_witness_attempt(symbolic, result, charge, release)?;
    let different = complete && matches!(result, Ok(true));
    Ok(if different {
        Witness::Different
    } else if schedule.deferred {
        Witness::Deferred
    } else {
        Witness::Inconclusive
    })
}

/// Arithmetic unsupported only on the optional substitution is a local miss.
/// Mandatory work, storage and retirement failures still veto any result.
fn finish_witness_attempt(
    symbolic: bool,
    result: R<bool>,
    charge: Result<(), ResourceError>,
    release: Result<(), ResourceError>,
) -> Result<bool, super::super::normalization::HeadError> {
    let status = match (symbolic, result) {
        (true, Err(KErr::LiteralArithmetic)) => Err(KErr::Unsupported),
        (_, result) => result.map(|_| ()),
    };
    finish_attempt(status, charge, release, false).map(|(complete, _)| complete)
}
