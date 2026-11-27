//! Positive definitional comparison of evaluated terms.

use super::*;

mod arguments;
mod congruence;
mod delta;
mod eta;
mod nat;
mod syntax;

impl<'e, 'w> Kernel<'e, 'w> {
    pub(super) fn defeq(&mut self, a: u32, c: u32) -> R<bool> {
        self.defeq_with(a, c, false)
    }
    /// `not_proof`: the caller knows `a`'s type is not a proposition (its
    /// sort is not zero), so proof irrelevance cannot apply to this pair and
    /// its type is not inferred. Types are preserved by reduction, so the
    /// knowledge holds for every head form `a` reduces to.
    pub(super) fn defeq_with(&mut self, a: u32, c: u32, not_proof: bool) -> R<bool> {
        if a == c {
            return Ok(true);
        }
        self.enter()?;
        let r = self.defeq_inner(a, c, not_proof);
        self.leave();
        r
    }
    fn defeq_inner(&mut self, a: u32, c: u32, not_proof: bool) -> R<bool> {
        if let (
            Val::Delayed {
                e: e1,
                env: v1,
                li: l1,
            },
            Val::Delayed {
                e: e2,
                env: v2,
                li: l2,
            },
        ) = (self.vals[a as usize], self.vals[c as usize])
            && e1 == e2
            && l1 == l2
        {
            // These original delayed values keep their denotation when forced.
            // Reuse only completed equality in this exact scoped graph:
            // congruence's early return must not bypass positive pair reuse.
            let key = (a.min(c), a.max(c));
            if self.eq_ok.contains(&key) {
                return Ok(true);
            }
            let r = self.exprs.get(e1, self.b)?.loose_range();
            let mask = self.source_support(e1)?;
            if self.env_congruent(v1, v2, r, mask)? {
                // Keep useful forced-pair entries: early congruence may fill
                // a vacant bucket, but must not displace an existing fact.
                if self.eq_ok.bucket_vacant(&key) {
                    self.eq_ok.insert(key, (), self.b, &mut self.reserved)?;
                }
                return Ok(true);
            }
        }
        if let (
            Val::Delayed {
                e: e1,
                env: v1,
                li: l1,
            },
            Val::Delayed {
                e: e2,
                env: v2,
                li: l2,
            },
        ) = (self.vals[a as usize], self.vals[c as usize])
            && e1 != e2
            && self.syn_bounded(e1, v1, l1, e2, v2, l2)?
        {
            return Ok(true);
        }
        let a = self.force(a)?;
        let c = self.force(c)?;
        if a == c {
            return Ok(true);
        }
        let key = if a < c { (a, c) } else { (c, a) };
        if self.eq_ok.contains(&key) {
            return Ok(true);
        }
        if let Some(r) = self.quick(a, c)? {
            if r {
                self.eq_ok.insert(key, (), self.b, &mut self.reserved)?;
            }
            return Ok(r);
        }
        let r = self.defeq_slow(a, c, not_proof)?;
        if r {
            self.eq_ok.insert(key, (), self.b, &mut self.reserved)?;
        }
        Ok(r)
    }
    pub(super) fn defeq_slow(&mut self, a: u32, c: u32, not_proof: bool) -> R<bool> {
        if self.try_recursor_congruence(a, c)? {
            return Ok(true);
        }
        let a = self.whnf_core(a)?;
        let c = self.whnf_core(c)?;
        if a == c {
            return Ok(true);
        }
        if let Some(r) = self.quick(a, c)? {
            return Ok(r);
        }
        if self.proj_structs(a, c)? {
            return Ok(true);
        }
        // Proof irrelevance before any unfolding.
        if !not_proof
            && let Some(ta) = self.is_proof(a)?
            && let Some(tc) = self.infer_value(c)?
        {
            return self.defeq(ta, tc);
        }
        let offered = (a, c);
        let (a, c) = match self.lazy_delta(a, c, true)? {
            Lazy::Decided(r) => return Ok(r),
            Lazy::Stuck(a, c) => (a, c),
        };
        if self.try_projection_congruence(a, c, offered)? {
            return Ok(true);
        }
        // Stuck projections reduce their structures fully before the
        // structural rules.
        if matches!(self.vals[a as usize], Val::Proj { .. })
            || matches!(self.vals[c as usize], Val::Proj { .. })
        {
            let (wa, wc) = (self.whnf(a)?, self.whnf(c)?);
            if wa != a || wc != c {
                return self.defeq(wa, wc);
            }
        }
        // A string literal against anything else: compare its expansion.
        if let Val::Str(e) = self.vals[a as usize]
            && !matches!(self.vals[c as usize], Val::Str(_))
        {
            let x = self.expand_str(e)?;
            return self.defeq(x, c);
        }
        if let Val::Str(e) = self.vals[c as usize]
            && !matches!(self.vals[a as usize], Val::Str(_))
        {
            let x = self.expand_str(e)?;
            return self.defeq(a, x);
        }
        // Structural rules on weak head normal forms.
        let mut same_constructor_failed = false;
        match (self.vals[a as usize], self.vals[c as usize]) {
            #[allow(
                clippy::collapsible_match,
                reason = "a fallible guard would fall through to the later structural arms"
            )]
            (Val::Local { id: x, .. }, Val::Local { id: y, .. }) if x == y => {
                if self.same_spines(a, c)? {
                    return Ok(true);
                }
            }
            (Val::Const { ci: x, li: lx, .. }, Val::Const { ci: y, li: ly, .. })
                if x == y && self.same_levels(lx, ly)? =>
            {
                match self.spines(a, c, 0)? {
                    Some(true) => return Ok(true),
                    // One constructor with a visibly distinct non-proof
                    // field: structure eta would compare the same fields
                    // and unit-like equality needs none, so no later rule
                    // can succeed.
                    None if self.const_view(x)?.ctor.is_some() => return Ok(false),
                    // Arguments of one constructor compared without success
                    // structure eta in either direction would
                    // project back to these same field arguments and compare
                    // them again, with the same parameter pairs in its type
                    // premise, so skip it. This only removes an optional
                    // positive route; nothing negative is concluded.
                    Some(false) if self.const_view(x)?.ctor.is_some() => {
                        same_constructor_failed = true;
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        if matches!(self.vals[a as usize], Val::Lam(_)) {
            return self.eta(a, c);
        }
        if matches!(self.vals[c as usize], Val::Lam(_)) {
            return self.eta(c, a);
        }
        if self.nat_succ(a, c)? || self.nat_succ(c, a)? {
            return Ok(true);
        }
        if !same_constructor_failed && (self.struct_eta(a, c)? || self.struct_eta(c, a)?) {
            return Ok(true);
        }
        self.unit_like(a, c)
    }
}
