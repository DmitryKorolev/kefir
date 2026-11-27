//! Spine comparison, absent arguments and proof irrelevance.

use super::*;

impl<'e, 'w> Kernel<'e, 'w> {
    /// Arguments of two applications of the same head, root first. The head's
    /// Pi type is instantiated with the left arguments; once the earlier
    /// arguments are equal, both later arguments have the same expected type,
    /// and an argument whose expected type is a proposition is equal by proof
    /// irrelevance (all compared values come from checked terms).
    /// Bit `i` set: argument `i` of definition `ci` is absent. With the value
    /// `λ (x₀ : d₀) … (x_{k-1} : d_{k-1}), b` and the type
    /// `Π (x₀ : D₀) … (x_{k-1} : D_{k-1}), R`, `xᵢ` is absent when it is free
    /// neither in `b`, nor in any later lambda domain `d_j` (j > i), nor in the
    /// type after binder `i`. Then for any spine with more than `i` arguments,
    /// `c … aᵢ …` and `c … a'ᵢ …` unfold and beta-reduce to terms that differ
    /// only where the other arguments differ, also for a partial application
    /// whose remaining lambdas keep their domains; and the later arguments'
    /// expected types do not depend on `aᵢ`, so proof irrelevance at a later
    /// argument still compares proofs of one proposition.
    ///
    /// Support is syntactic and over-approximates use. Unknown support (a
    /// loose index at or above 63, metadata) marks that binder and every outer
    /// one present; so does a depth or stack limit while computing it. Delta
    /// must be definitional for `ci` wherever this is consulted (regular
    /// definitions in lazy delta). At most 62 binders; cached per attempt.
    pub(super) fn absent_args(&mut self, ci: u32) -> R<u64> {
        if let Some(&m) = self.absent.get(&ci) {
            return Ok(m);
        }
        let m = match self.compute_absent(ci) {
            Ok(m) => m,
            Err(KErr::Unsupported) => 0,
            Err(e) => return Err(e),
        };
        map_put(self.b, &mut self.reserved, &mut self.absent, ci, m)?;
        Ok(m)
    }
    fn compute_absent(&mut self, ci: u32) -> R<u64> {
        let (Some(mut value), Some(mut ty)) = (self.const_view(ci)?.value, self.const_view(ci)?.ty)
        else {
            return Ok(0);
        };
        // Pair the value's lambdas with the type's binders, outermost first.
        let mut binders = [(value, ty); 62];
        let mut k = 0;
        while k < binders.len() {
            self.step()?;
            let v = self.exprs.get(value, self.b)?;
            let t = self.exprs.get(ty, self.b)?;
            match (
                v.kind(self.exprs, self.levels, self.b)?,
                t.kind(self.exprs, self.levels, self.b)?,
            ) {
                (ExprKind::Lambda(_, domain, body, _), ExprKind::Pi(_, _, rest, _)) => {
                    binders[k] = (domain, rest);
                    value = body;
                    ty = rest;
                    k += 1;
                }
                _ => break,
            }
        }
        // Innermost first: `read` holds the variables the value reads below
        // the current binder, which is its bit 0.
        let mut read = self.bounded_support(value)?;
        let mut absent = 0u64;
        for j in (0..k).rev() {
            if read == u64::MAX {
                break;
            }
            let (domain, rest) = binders[j];
            let mentioned = self.bounded_support(rest)?;
            if read & 1 == 0 && mentioned & 1 == 0 && mentioned != u64::MAX {
                absent |= 1u64 << j;
            }
            let d = self.bounded_support(domain)?;
            read = if d == u64::MAX { d } else { (read >> 1) | d };
        }
        Ok(absent)
    }
    /// Source support for the absent mask, within its own small allowance:
    /// a definition's body can be large and unfolding may never visit most
    /// of it. Running out gives unknown support, which marks nothing absent.
    /// Completed nodes stay in the support memo.
    pub(in super::super) fn bounded_support(&mut self, e: ExprId) -> R<u64> {
        let saved = self.bounds;
        self.limit_total(self.steps.saturating_add(MASK_BUDGET));
        let r = self.source_support(e);
        self.restore_bounds(saved);
        match r {
            Err(KErr::Abort) if self.steps <= self.limit => Ok(u64::MAX),
            r => r,
        }
    }
    pub(super) fn same_spines(&mut self, a: u32, c: u32) -> R<bool> {
        Ok(self.spines(a, c, 0)? == Some(true))
    }
    /// `same_spines`, except that arguments whose bit is set in `skip` are
    /// not compared. Only `absent_args` of the shared head justifies a skip.
    pub(super) fn same_spines_skipping(&mut self, a: u32, c: u32, skip: u64) -> R<bool> {
        Ok(self.spines(a, c, skip)? == Some(true))
    }
    /// `Some(true)`: equal arguments; `Some(false)`: not shown equal; `None`:
    /// a visibly distinct non-proof argument pair (`visibly_distinct`).
    pub(in super::super) fn spines(&mut self, a: u32, c: u32, skip: u64) -> R<Option<bool>> {
        let (sa, sc, head) = match (self.vals[a as usize], self.vals[c as usize]) {
            (Val::Local { id, spine: x }, Val::Local { spine: y, .. }) => (x, y, Ok(id)),
            (Val::Const { ci, li, spine: x }, Val::Const { spine: y, .. }) => (x, y, Err((ci, li))),
            _ => return Ok(Some(false)),
        };
        if self.cells[sa as usize].len != self.cells[sc as usize].len {
            return Ok(Some(false));
        }
        if sa == sc {
            return Ok(Some(true));
        }
        // Short spines are read into stack arrays: comparisons nest as deeply
        // as the terms do, beyond what the buffer pool holds.
        let n = self.cells[sa as usize].len as usize;
        if n <= SMALL_SPINE {
            let (mut xs, mut ys) = ([0u32; SMALL_SPINE], [0u32; SMALL_SPINE]);
            let (mut p, mut q) = (sa, sc);
            for i in (0..n).rev() {
                let (cp, cq) = (self.cells[p as usize], self.cells[q as usize]);
                if cp.tag != 0 || cq.tag != 0 {
                    return self.same_cells(sa, sc).map(Some);
                }
                xs[i] = cp.item;
                ys[i] = cq.item;
                p = cp.prev;
                q = cq.prev;
            }
            return self.same_args(&xs[..n], &ys[..n], head, skip);
        }
        let Some(xs) = self.spine_args_opt(sa)? else {
            return self.same_cells(sa, sc).map(Some);
        };
        let ys = match self.spine_args_opt(sc) {
            Ok(Some(ys)) => ys,
            Ok(None) => {
                self.recycle(xs)?;
                return self.same_cells(sa, sc).map(Some);
            }
            Err(error) => return self.scratch_finish(Err(error), [xs]),
        };
        let res = self.same_args(&xs, &ys, head, skip);
        self.scratch_finish(res, [xs, ys])
    }
    /// Without evaluating: two applications of different constructors of one
    /// family, or two different literals. Such values are not definitionally
    /// equal unless they are proofs (proof irrelevance), which the caller
    /// excludes; structure eta and unit-like equality need a single
    /// constructor. Unevaluated thunks are never visibly distinct.
    pub(in super::super) fn visibly_distinct(&mut self, mut x: u32, mut y: u32) -> R<bool> {
        while let Val::Ind(t) = self.vals[x as usize] {
            x = t;
        }
        while let Val::Ind(t) = self.vals[y as usize] {
            y = t;
        }
        Ok(match (self.vals[x as usize], self.vals[y as usize]) {
            (Val::Const { ci: a, .. }, Val::Const { ci: b, .. }) => matches!(
                (self.const_view(a)?.ctor, self.const_view(b)?.ctor),
                (Some((fa, ia)), Some((fb, ib))) if fa == fb && ia != ib
            ),
            (Val::Nat(a), Val::Nat(b)) => {
                self.observe_pair(a, b)?;
                !nat_eq(&self.nats[a as usize], &self.nats[b as usize], self.b)?
            }
            _ => false,
        })
    }
    /// Arguments of two applications of `head`, root first; see `same_spines`.
    pub(in super::super) fn same_args(
        &mut self,
        xs: &[u32],
        ys: &[u32],
        head: Result<u32, (u32, u32)>,
        skip: u64,
    ) -> R<Option<bool>> {
        // A non-proof argument pair that is visibly different ends this
        // route before any earlier, possibly expensive, pair is compared.
        // `false` here is not a conclusion: argument-first comparison then
        // unfolds, and anywhere else the attempt may only be abandoned.
        let (mut fty, mut at) = (NONE, 0usize);
        for i in 0..xs.len() {
            if (i >= 64 || (skip >> i) & 1 == 0) && self.visibly_distinct(xs[i], ys[i])? {
                match self.arg_is_proof(&mut fty, &mut at, head, xs, i) {
                    Ok(Some(false) | None) => return Ok(None),
                    Ok(Some(true)) | Err(KErr::Unsupported) => {}
                    Err(e) => return Err(e),
                }
            }
        }
        let mut fty = NONE;
        let mut at = 0usize;
        let mut typed = true;
        for i in 0..xs.len() {
            let (x, y) = (xs[i], ys[i]);
            if i < 64 && (skip >> i) & 1 == 1 {
                continue;
            }
            if x == y || self.eq_ok.contains(&(x.min(y), x.max(y))) {
                continue;
            }
            let mut not_proof = false;
            if typed {
                match self.arg_is_proof(&mut fty, &mut at, head, xs, i) {
                    Ok(Some(true)) => continue,
                    Ok(Some(false)) => not_proof = true,
                    Ok(None) => {}
                    Err(KErr::Unsupported) => {
                        typed = false;
                    }
                    Err(e) => return Err(e),
                }
            }
            if !self.defeq_with(x, y, not_proof)? {
                return Ok(Some(false));
            }
        }
        Ok(Some(true))
    }
    /// Whether argument `i` of the head's type, instantiated with `xs`, is
    /// expected to be a proof: `Some(false)` when its domain's sort is known
    /// not to be zero, `None` when that sort is unknown.
    pub(in super::super) fn arg_is_proof(
        &mut self,
        fty: &mut u32,
        at: &mut usize,
        head: Result<u32, (u32, u32)>,
        xs: &[u32],
        i: usize,
    ) -> R<Option<bool>> {
        let original = if i < 8 || *fty == NONE {
            Some(match head {
                Ok(id) => self.locals[id as usize],
                Err((ci, li)) => self.const_type(ci, li)?,
            })
        } else {
            None
        };
        if *fty == NONE {
            *fty = original.ok_or(ResourceError::Invariant)?;
        }
        let head_key = original.filter(|_| i < 8).map(|ty| (ty, i as u32 + 1));
        if let Some(key) = head_key
            && let Some(&status) = self.arg_proof_status.get(&key)
        {
            // Leave the instantiation cursor unchanged. A later unguarded
            // argument still has to instantiate the complete missing prefix.
            return Ok(Some(status));
        }
        // The caller keeps this cursor for one fixed head and only advances
        // it by instantiation. Once initialized, a constant's exact type cache
        // entry remains present for the entire attempt: rereading it would be
        // an uncharged, infallible hit, not another typing or budget premise.
        while *at < i {
            let w = self.pi_like(*fty)?;
            *fty = self.instantiate(w, xs[*at])?;
            *at += 1;
        }
        let w = self.pi_like(*fty)?;
        let dom = self.binder_dom(w)?;
        // Reduced selectors can expose different Pi domains. Domain identity
        // always fixes the instantiated denotation within this attempt. Head
        // reuse additionally requires the explicit-prefix formation premise.
        let key = (dom, 0);
        if let Some(&status) = self.arg_proof_status.get(&key) {
            return Ok(Some(status));
        }
        let status = self.prop_status(dom)?;
        if let Some(proof) = status {
            let key = match head_key {
                Some(head_key) if self.explicit_proof_prefix(head_key.0, i)? => head_key,
                _ if !proof => key,
                _ => return Ok(status),
            };
            // Trial: completed proof observations use the same explicit-prefix
            // premise as non-proof observations. Domain-only fallback remains
            // non-proof-only; zero and nonzero positions are disjoint keys.
            map_put(
                self.b,
                &mut self.reserved,
                &mut self.arg_proof_status,
                key,
                proof,
            )?;
        }
        Ok(status)
    }
    /// A fixed original head/context/universe instance and an explicit Pi
    /// prefix prove that well-typed substitution preserves each domain's sort.
    /// Never reduce a selector (including let/projection/beta) to discover Pis.
    /// The exact scoped graph fixes this prefix across eligible restoration;
    /// only completed classifications fill `arg_proof_status`.
    pub(in super::super) fn explicit_proof_prefix(&mut self, original: u32, i: usize) -> R<bool> {
        if i >= 8 {
            return Ok(false);
        }
        self.steps_by(i as u64 + 1)?;
        let Val::Pi(c) = self.vals[original as usize] else {
            return Ok(false);
        };
        let mut body = c.body;
        for _ in 0..i {
            let node = self.exprs.get(body, self.b)?;
            let ExprKind::Pi(_, _, next, _) = node.kind(self.exprs, self.levels, self.b)? else {
                return Ok(false);
            };
            body = next;
        }
        Ok(true)
    }
    fn same_cells(&mut self, sa: u32, sc: u32) -> R<bool> {
        let (mut x, mut y) = (sa, sc);
        if self.cells[x as usize].len != self.cells[y as usize].len {
            return Ok(false);
        }
        while x != y {
            let (cx, cy) = (self.cells[x as usize], self.cells[y as usize]);
            if cx.tag != cy.tag {
                return Ok(false);
            }
            if cx.tag == 0 {
                if !self.defeq(cx.item, cy.item)? {
                    return Ok(false);
                }
            } else if cx.item != cy.item {
                return Ok(false);
            }
            x = cx.prev;
            y = cy.prev;
        }
        Ok(true)
    }
}
