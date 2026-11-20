//! Restricted witnesses used solely by an ordinary checked comparison.
use super::super::normalization::full::comparison::Evidence;
use super::*;

impl Kernel<'_, '_> {
    fn data_family(&mut self, value: u32, family: u32, bare: bool) -> R<bool> {
        let Some(ty) = self.infer_value(value)? else {
            return Ok(false);
        };
        let ty = self.whnf(ty)?;
        let Val::Const { ci, spine, .. } = self.vals[ty as usize] else {
            return Ok(false);
        };
        if (bare && spine != 0) || self.const_view(ci)?.canon != family {
            return Ok(false);
        }
        let Some(sort) = self.infer_value(ty)? else {
            return Ok(false);
        };
        let level = self.sort_of(sort)?;
        Ok(self.levels.get(level, self.b)?.positive()
            == crate::syntax::levels::LevelPositive::Proven)
    }
    /// Select the earliest checked context entry denoting this value. A let can
    /// only refer back to an earlier declaration. The minimum is independent
    /// of hash-table iteration order.
    fn context_neutral(&mut self, value: u32) -> R<bool> {
        let Some(context) = self.checked_context else {
            return Ok(false);
        };
        if self.free_values.capacity() > 128 {
            return Ok(false);
        }
        self.steps_by(129)?;
        let first = self
            .free_values
            .iter()
            .filter_map(|(&id, &v)| (v == value).then_some(id))
            .min();
        match first {
            Some(id) => Ok(context.get(id, self.b)?.value().is_none()),
            None => Ok(false),
        }
    }
    /// Only a checked Nat/Bool recursor chain ending in a value-free local can
    /// certify a stuck major. Extra applications never change the major slot.
    fn check_blocker(&mut self, mut n: u32, mut trim: u8) -> R<bool> {
        let Some((nat, _, _)) = self.nat_ctors()? else {
            return Ok(false);
        };
        let nat = self.const_view(nat)?.canon;
        let Some(boolean) = self.env.natural_predicate_constructor(false) else {
            return Ok(false);
        };
        let bci = self.const_info(boolean)?;
        let Some((boolean, _)) = self.const_view(bci)?.ctor else {
            return Ok(false);
        };
        for _ in 0..10 {
            self.step()?;
            let wh = self.whnf(n)?;
            if let Val::Local { spine: 0, .. } = self.vals[wh as usize] {
                return Ok(trim == 0 && self.context_neutral(wh)?);
            }
            let Val::Const { ci, mut spine, .. } = self.vals[wh as usize] else {
                return Ok(false);
            };
            let Some(rec) = self.const_view(ci)?.rec else {
                return Ok(false);
            };
            if rec.k
                || rec.eta
                || rec.rules.len() != 2
                || (rec.family != nat && rec.family != boolean)
                || self.const_view(ci)?.delta.is_some()
                || self.const_view(ci)?.quot.is_some()
            {
                return Ok(false);
            }
            for _ in 0..trim {
                self.step()?;
                spine = self.cells[spine as usize].prev;
            }
            trim = 0;
            let k = rec
                .common
                .checked_add(rec.nidx)
                .and_then(|n| n.checked_add(1))
                .ok_or(ResourceError::Invariant)?;
            if self.cells[spine as usize].len < k {
                return Ok(false);
            }
            while self.cells[spine as usize].len > k {
                self.step()?;
                let p = self.cells[spine as usize];
                if p.tag != 0 {
                    return Ok(false);
                }
                spine = p.prev;
            }
            // A checked recursor prefix before its major has Pi type, so it
            // cannot be a projection target. Validate the cell representation
            // before using the major: a projection's item is a constant-info
            // ID, while an application's item is a value ID.
            let major = self.cells[spine as usize];
            while spine != 0 {
                self.step()?;
                let p = self.cells[spine as usize];
                if p.tag != 0 {
                    return Ok(false);
                }
                spine = p.prev;
            }
            // Only an application cell carries a value id in its item.
            n = major.item;
            if !self.data_family(n, rec.family, true)? {
                return Ok(false);
            }
        }
        Ok(false)
    }
    fn rigid_applied_field(&mut self, e: ExprId) -> R<Option<(u32, u32, u32)>> {
        let v = self.eval(e, 0, 0)?;
        let w = self.whnf(v)?;
        let Val::Const { ci, li, spine } = self.vals[w as usize] else {
            return Ok(None);
        };
        let a = self.cells[spine as usize];
        if a.tag != 0 || a.prev == 0 {
            return Ok(None);
        }
        let p = self.cells[a.prev as usize];
        if p.tag == 0 {
            return Ok(None);
        }
        let Some(ind) = self.const_view(p.item)?.ind else {
            return Ok(None);
        };
        if !ind.nonrecursive
            || ind.nidx != 0
            || ind.ctors.len() != 1
            || p.tag > ind.ctors[0].num_fields
        {
            return Ok(None);
        }
        let src = self.push(Val::Const {
            ci,
            li,
            spine: p.prev,
        })?;
        let fam = self.const_view(p.item)?.canon;
        if !self.data_family(src, fam, false)? {
            return Ok(None);
        }
        if !self.check_blocker(w, 2)? {
            return Ok(None);
        }
        Ok(Some((self.const_view(p.item)?.canon, p.tag, a.item)))
    }

    fn unequal_applied_fields(&mut self, left: ExprId, right: ExprId) -> R<bool> {
        let Some((a, i, x)) = self.rigid_applied_field(left)? else {
            return Ok(false);
        };
        let Some((c, j, y)) = self.rigid_applied_field(right)? else {
            return Ok(false);
        };
        let Some((nat, _, succ)) = self.nat_ctors()? else {
            return Ok(false);
        };
        for e in [left, right] {
            let ty = self.infer(e, 0, 0, true)?;
            let wh = self.whnf(ty)?;
            if !matches!(self.vals[wh as usize],Val::Const{ci,spine:0,li:0} if ci==nat) {
                return Ok(false);
            }
        }
        let nat_fam = self.const_view(nat)?.canon;
        if !self.data_family(x, nat_fam, true)? || !self.data_family(y, nat_fam, true)? {
            return Ok(false);
        }
        if a != c || i != j {
            return Ok(true);
        }
        let (x, y) = (self.whnf(x)?, self.whnf(y)?);
        for (u, v) in [(x, y), (y, x)] {
            let Val::Local { id, spine: 0 } = self.vals[u as usize] else {
                continue;
            };
            let Val::Const { ci, li: 0, spine } = self.vals[v as usize] else {
                continue;
            };
            if ci != succ || spine == 0 {
                continue;
            }
            let arg = self.cells[spine as usize];
            if arg.tag != 0 || arg.prev != 0 {
                continue;
            }
            let t = self.whnf(arg.item)?;
            if matches!(self.vals[t as usize],Val::Local{id:other,spine:0} if id==other)
                && self.context_neutral(u)?
                && self.context_neutral(t)?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }
    fn unequal_offsets(&mut self, left: ExprId, right: ExprId) -> R<bool> {
        let a = self.eval(left, 0, 0)?;
        let c = self.eval(right, 0, 0)?;
        let (a, m) = self.expose_natural_successors(a, true)?;
        let (c, n) = self.expose_natural_successors(c, true)?;
        if m == 0 || n == 0 || m == n {
            return Ok(false);
        }
        let (a, c) = (self.whnf_core(a)?, self.whnf_core(c)?);
        let (
            Val::Const {
                ci: x,
                li: lx,
                spine: 0,
            },
            Val::Const {
                ci: y,
                li: ly,
                spine: 0,
            },
        ) = (self.vals[a as usize], self.vals[c as usize])
        else {
            return Ok(false);
        };
        Ok(x == y && self.same_levels(lx, ly)?)
    }
}

/// Both operands are checked in the supplied context. Unfinished exposures and
/// failures in an inner comparison cannot certify inequality. Retire the local
/// graph and settle its ledger before returning a completed witness.
#[allow(clippy::too_many_arguments)]
pub(in crate::check::environment) fn different(
    environment: &Environment,
    left: ExprId,
    right: ExprId,
    scope: &Scope<'_>,
    locals: &LocalContext,
    incoming: crate::resource::ReductionPath,
    names: &Names,
    exprs: &Expressions,
    levels: &mut Levels,
    budget: &mut Budget,
) -> Result<Option<Evidence>, super::super::normalization::HeadError> {
    if scope.mode != Mode::Safe || scope.formation.is_some() || !scope.parameters.is_empty() {
        return Ok(None);
    }
    let first = exprs.get(left, budget)?;
    let open = first.has_free();
    if !matches!(first.kind(exprs, levels, budget)?, ExprKind::App(..)) {
        return Ok(None);
    }
    let second = exprs.get(right, budget)?;
    if second.has_free() != open
        || !matches!(second.kind(exprs, levels, budget)?, ExprKind::App(..))
    {
        return Ok(None);
    }
    // Reserve room on the ordinary prefix for the whole independent witness.
    // The new graph meters its own operations, including lookup on reuse.
    let allowance = if open { 32768 } else { 4096 };
    match incoming.after_height(allowance) {
        Ok(_) => {}
        Err(ResourceError::ReductionPath) => return Ok(None),
        Err(error) => return Err(error.into()),
    }
    environment.check_scope(
        scope.before,
        scope.formation,
        scope.expression_end,
        scope.level_end,
    )?;
    let mut k = Kernel::new(environment, names, exprs, levels, budget, scope);
    k.checked_context = open.then_some(locals);
    k.neutral_head_only = open;
    let result = (|| {
        k.init()?;
        k.limit_total(k.steps.saturating_add(u64::from(allowance)));
        if open {
            k.unequal_applied_fields(left, right)
        } else {
            k.unequal_offsets(left, right)
        }
    })();
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
    Ok((complete && matches!(result, Ok(true))).then_some(if open {
        Evidence::RigidArguments
    } else {
        Evidence::Natural
    }))
}
