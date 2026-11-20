//! A concrete instance of a checked theorem type mismatch.
use super::*;

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
                    if self.defeq(da, db)? && self.witness_data(a.args[i], b.args[i], da, depth)? {
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
                && self.witness_data(a.args[i], b.args[i], da, depth)?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn witness_data(&mut self, a: u32, b: u32, ty: u32, depth: u8) -> R<bool> {
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
        let (a, b) = (self.whnf(a)?, self.whnf(b)?);
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
        self.witness_arguments(a, b, ind.nparams as usize, depth - 1)
    }

    fn concrete_argument(&mut self, ty: u32, index: usize) -> R<u32> {
        let nat = self.nat_type()?;
        if self.defeq(ty, nat)? {
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

    fn theorem_witness(&mut self, request: &Request<'_>) -> R<bool> {
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
                return self.witness_arguments(a, b, 0, 4);
            }
            if index == 2 {
                return Ok(false);
            }
            let (a, b) = (self.pi_like(a)?, self.pi_like(b)?);
            let (da, db) = (self.binder_dom(a)?, self.binder_dom(b)?);
            if !self.defeq(da, db)? {
                return Ok(false);
            }
            let arg = self.concrete_argument(da, index)?;
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
) -> Result<bool, super::super::normalization::HeadError> {
    if request.kind != Kind::Theorem || !request.parameters.is_empty() || !eligible(request, scope)
    {
        return Ok(false);
    }
    environment.check_scope(
        scope.before,
        scope.formation,
        scope.expression_end,
        scope.level_end,
    )?;
    let mut k = Kernel::new(environment, names, exprs, levels, budget, scope);
    let result = k.init().and_then(|()| k.theorem_witness(request));
    let steps = k.steps - k.charged;
    let reserved = k.reserved;
    k.retire_arena();
    drop(k);
    let charge = budget.charge_work(steps);
    let release = budget.release(reserved);
    let (complete, _) = finish_attempt(
        result.as_ref().map(|_| ()).map_err(|e| *e),
        charge,
        release,
        false,
    )?;
    let different = complete && matches!(result, Ok(true));
    Ok(different)
}
