//! Bounded structural comparison and closure congruence.

use super::*;

impl<'e, 'w> Kernel<'e, 'w> {
    pub(super) fn quick(&mut self, a: u32, c: u32) -> R<Option<bool>> {
        Ok(Some(match (self.vals[a as usize], self.vals[c as usize]) {
            (Val::Sort(x), Val::Sort(y)) => self.level_eq(x, y)?,
            (Val::Nat(x), Val::Nat(y)) => {
                self.observe_pair(x, y)?;
                nat_eq(&self.nats[x as usize], &self.nats[y as usize], self.b)?
            }
            (Val::Str(x), Val::Str(y)) => {
                let bx = match self
                    .exprs
                    .get(x, self.b)?
                    .kind(self.exprs, self.levels, self.b)?
                {
                    ExprKind::String(b) => b,
                    _ => return no(),
                };
                let by = match self
                    .exprs
                    .get(y, self.b)?
                    .kind(self.exprs, self.levels, self.b)?
                {
                    ExprKind::String(b) => b,
                    _ => return no(),
                };
                if bx == by {
                    true
                } else {
                    return Ok(None);
                }
            }
            // Equal closures of the same form denote the same value. A Pi and
            // a lambda type built from the same syntax do not: `Π x, b` is not
            // `Π x, typeof(b)`, so mixed forms always compare by binders.
            (Val::Pi(x), Val::Pi(y))
            | (Val::Lam(x), Val::Lam(y))
            | (Val::LamTy(x), Val::LamTy(y)) => {
                if x == y {
                    true
                } else {
                    self.binders(a, c)?
                }
            }
            (Val::Pi(_), Val::LamTy(_)) | (Val::LamTy(_), Val::Pi(_)) => self.binders(a, c)?,
            (Val::Arrow { .. }, Val::Pi(_) | Val::LamTy(_) | Val::Arrow { .. })
            | (Val::Pi(_) | Val::LamTy(_), Val::Arrow { .. }) => self.binders(a, c)?,
            _ => return Ok(None),
        }))
    }
    pub(in super::super) fn binders(&mut self, a: u32, c: u32) -> R<bool> {
        if let (Val::Pi(x), Val::Pi(y))
        | (Val::Lam(x), Val::Lam(y))
        | (Val::LamTy(x), Val::LamTy(y)) = (self.vals[a as usize], self.vals[c as usize])
            && (self.closure_congruent(x, y)? || self.syn_clo(x, y)?)
        {
            return Ok(true);
        }
        let da = self.binder_dom(a)?;
        let dc = self.binder_dom(c)?;
        if !self.defeq(da, dc)? {
            return Ok(false);
        }
        let x = self.open_local(da)?;
        let r = (|| {
            let ba = self.instantiate(a, x)?;
            let bc = self.instantiate(c, x)?;
            self.defeq(ba, bc)
        })();
        self.close_local();
        r
    }
    /// Same syntax needs agreement only at its referenced slots. Unknown
    /// support retains the old full-prefix sufficient condition. Environments
    /// come from valid typing/evaluation: entry types are compatible with their
    /// values; fabricated annotations would not justify LamTy congruence.
    /// Computing source support is separately charged before this local probe
    /// allowance. This helper is bounded and proves only positive congruence.
    pub(in super::super) fn env_congruent(
        &mut self,
        e1: u32,
        e2: u32,
        r: u32,
        mask: u64,
    ) -> R<bool> {
        if e1 == e2 {
            return Ok(true);
        }
        let saved = self.bounds;
        let depth = self.binders.len();
        let start = self.argument_steps();
        let allowance = if start < self.full_capture_after {
            SYN_BUDGET
        } else {
            ARGS_BUDGET
        };
        self.limit_arguments(start.saturating_add(allowance));
        let res = (|| {
            let (mut x, mut y) = (e1, e2);
            for i in 0..r {
                if x == y {
                    return Ok(true);
                }
                if x == 0 || y == 0 {
                    return Ok(false);
                }
                let (nx, ny) = (self.envs[x as usize], self.envs[y as usize]);
                if (mask == u64::MAX || (i < 64 && mask & (1u64 << i) != 0)) && nx.val != ny.val {
                    // A missed optional capture proof can only send the caller
                    // back to ordinary comparison. Full allowances may retry.
                    let key = (u64::from(nx.val) << 32) | u64::from(ny.val);
                    let hash = nx.val.wrapping_mul(0x9e3779b1) ^ ny.val.wrapping_mul(0x85ebca6b);
                    let slot = (hash >> 29) as usize;
                    if allowance == SYN_BUDGET
                        && self.markers == 0
                        && self.capture_misses[slot] == key
                    {
                        return Ok(false);
                    }
                    if !self.defeq(nx.val, ny.val)? {
                        if self.markers == 0 {
                            self.capture_misses[slot] = key;
                        }
                        return Ok(false);
                    }
                }
                x = nx.parent;
                y = ny.parent;
            }
            Ok(true)
        })();
        self.restore_bounds(saved);
        self.binders.truncate(depth);
        match res {
            Ok(false) if allowance == ARGS_BUDGET && self.full_capture_after <= start => {
                let end = self.argument_steps();
                if end > start.saturating_add(SYN_BUDGET) {
                    self.full_capture_after = end.saturating_add(ARGS_BUDGET);
                }
                Ok(false)
            }
            Ok(r) => Ok(r),
            Err(KErr::Abort) if self.steps <= self.limit => {
                let end = self.argument_steps();
                if allowance == ARGS_BUDGET && end > start.saturating_add(allowance) {
                    self.full_capture_after = end.saturating_add(ARGS_BUDGET);
                }
                Ok(false)
            }
            Err(e) => Err(e),
        }
    }
    /// Syntactic equality modulo environments for two closures of the same
    /// form: equal structure with equal variable values denotes equal terms,
    /// decided without instantiating or unfolding (bounded, positive-only).
    pub(in super::super) fn syn_clo(&mut self, x: Clo, y: Clo) -> R<bool> {
        if x.dom == y.dom && x.body == y.body {
            return Ok(false);
        }
        let saved = self.bounds;
        self.limit_total(self.steps.saturating_add(SYN_BUDGET));
        let r = (|| {
            if !self.syn_eq(x.dom, x.env, x.li, y.dom, y.env, y.li)? {
                return Ok(false);
            }
            let m = self.marker()?;
            let (e1, e2) = (
                self.env_push(x.env, m, NONE)?,
                self.env_push(y.env, m, NONE)?,
            );
            let r = self.syn_eq(x.body, e1, x.li, y.body, e2, y.li);
            self.markers -= 1;
            r
        })();
        self.restore_bounds(saved);
        match r {
            Ok(r) => Ok(r),
            Err(KErr::Abort) if self.steps <= self.limit => Ok(false),
            Err(e) => Err(e),
        }
    }
    pub(in super::super) fn syn_bounded(
        &mut self,
        e1: ExprId,
        v1: u32,
        l1: u32,
        e2: ExprId,
        v2: u32,
        l2: u32,
    ) -> R<bool> {
        let saved = self.bounds;
        self.limit_total(self.steps.saturating_add(SYN_BUDGET));
        let r = self.syn_eq(e1, v1, l1, e2, v2, l2);
        self.restore_bounds(saved);
        match r {
            Ok(r) => Ok(r),
            Err(KErr::Abort) if self.steps <= self.limit => Ok(false),
            Err(e) => Err(e),
        }
    }
    /// A placeholder bound to the same binder on both sides of `syn_eq`; it
    /// is compared by identity only and never evaluated or typed.
    pub(in super::super) fn marker(&mut self) -> R<u32> {
        let id = MARKER_BASE + self.markers;
        self.markers += 1;
        if let Some(&v) = self.marker_vals.get(&id) {
            return Ok(v);
        }
        let v = self.push(Val::Local { id, spine: 0 })?;
        map_put(self.b, &mut self.reserved, &mut self.marker_vals, id, v)?;
        Ok(v)
    }
    fn is_marker(&self, v: u32) -> bool {
        matches!(self.vals[v as usize], Val::Local { id, spine: 0 } if id >= MARKER_BASE)
    }
    #[allow(clippy::too_many_arguments)]
    fn syn_eq(&mut self, e1: ExprId, v1: u32, l1: u32, e2: ExprId, v2: u32, l2: u32) -> R<bool> {
        self.step()?;
        if e1 == e2 && l1 == l2 {
            let r = self.exprs.get(e1, self.b)?.loose_range();
            if r == 0 || v1 == v2 {
                return Ok(true);
            }
        }
        let key = (e1.slot(), v1, l1, e2.slot(), v2, l2);
        if self.syn_ok.contains(&key) {
            return Ok(true);
        }
        let (n1, n2) = (self.exprs.get(e1, self.b)?, self.exprs.get(e2, self.b)?);
        // Every rule below pairs nodes of one kind, so matching trees have the
        // same shape. Stored depth also counts binder-name and universe depth,
        // which this comparison ignores: a mismatch can skip a match this probe
        // would have found. The probe is optional, so that only costs the
        // ordinary route; it never makes `false` a conclusion.
        if n1.depth() != n2.depth() {
            return Ok(false);
        }
        let k1 = n1.kind(self.exprs, self.levels, self.b)?;
        let k2 = n2.kind(self.exprs, self.levels, self.b)?;
        let r = match (k1, k2) {
            (ExprKind::Bound(i), ExprKind::Bound(j)) => {
                let (a, c) = (self.env_at(v1, i)?.val, self.env_at(v2, j)?.val);
                if a == c {
                    true
                } else if self.is_marker(a) || self.is_marker(c) {
                    false
                } else {
                    self.defeq(a, c)?
                }
            }
            (ExprKind::Sort(x), ExprKind::Sort(y)) => {
                let (x, y) = (self.subst_level(x, l1)?, self.subst_level(y, l2)?);
                self.level_eq(x, y)?
            }
            (ExprKind::Constant(n1, ls1), ExprKind::Constant(n2, ls2)) => {
                if ls1.len() != ls2.len() || self.canon(n1)? != self.canon(n2)? {
                    false
                } else {
                    let mut ok = true;
                    for i in 0..ls1.len() {
                        let (x, y) = (self.subst_level(ls1[i], l1)?, self.subst_level(ls2[i], l2)?);
                        if !self.level_eq(x, y)? {
                            ok = false;
                            break;
                        }
                    }
                    ok
                }
            }
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.syn_eq(f1, v1, l1, f2, v2, l2)? && self.syn_eq(a1, v1, l1, a2, v2, l2)?
            }
            (ExprKind::Lambda(_, d1, b1, _), ExprKind::Lambda(_, d2, b2, _))
            | (ExprKind::Pi(_, d1, b1, _), ExprKind::Pi(_, d2, b2, _)) => {
                if !self.syn_eq(d1, v1, l1, d2, v2, l2)? {
                    false
                } else {
                    let m = self.marker()?;
                    let (n1, n2) = (self.env_push(v1, m, NONE)?, self.env_push(v2, m, NONE)?);
                    let r = self.syn_eq(b1, n1, l1, b2, n2, l2);
                    self.markers -= 1;
                    r?
                }
            }
            (ExprKind::Let(_, t1, x1, b1, _), ExprKind::Let(_, t2, x2, b2, _)) => {
                if !self.syn_eq(t1, v1, l1, t2, v2, l2)? || !self.syn_eq(x1, v1, l1, x2, v2, l2)? {
                    false
                } else {
                    let m = self.marker()?;
                    let (n1, n2) = (self.env_push(v1, m, NONE)?, self.env_push(v2, m, NONE)?);
                    let r = self.syn_eq(b1, n1, l1, b2, n2, l2);
                    self.markers -= 1;
                    r?
                }
            }
            (ExprKind::Projection(s1, i1, x1), ExprKind::Projection(s2, i2, x2)) => {
                i1 == i2
                    && self.canon(s1)? == self.canon(s2)?
                    && self.syn_eq(x1, v1, l1, x2, v2, l2)?
            }
            (ExprKind::Natural(x), ExprKind::Natural(y))
            | (ExprKind::String(x), ExprKind::String(y)) => x == y,
            _ => false,
        };
        if r {
            self.syn_ok.insert(key, (), self.b, &mut self.reserved)?;
        }
        Ok(r)
    }
    pub(in super::super) fn closure_congruent(&mut self, x: Clo, y: Clo) -> R<bool> {
        if x.dom != y.dom || x.body != y.body || x.li != y.li {
            return Ok(false);
        }
        let r = self.exprs.get(x.dom, self.b)?.loose_range().max(
            self.exprs
                .get(x.body, self.b)?
                .loose_range()
                .saturating_sub(1),
        );
        let d = self.source_support(x.dom)?;
        let b = self.source_support(x.body)?;
        let mask = if d == u64::MAX || b == u64::MAX {
            u64::MAX
        } else {
            d | (b >> 1)
        };
        self.env_congruent(x.env, y.env, r, mask)
    }
}
