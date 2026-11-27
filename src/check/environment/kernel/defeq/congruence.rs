//! Comparison of stuck eliminators and projected structures.

use super::*;

impl<'e, 'w> Kernel<'e, 'w> {
    /// Only a full probe with room in its enclosing bounds can start backoff.
    /// Return its private deadline so nested or short overruns cannot renew it.
    pub(super) fn begin_argument_congruence(&mut self) -> Option<u64> {
        let start = self.argument_steps();
        let full = start >= self.full_argument_probe_after;
        let end = start.saturating_add(if full { ARGS_BUDGET } else { SYN_BUDGET });
        self.limit_arguments(end);
        full.then_some(end)
    }

    /// Called after restoring the enclosing bounds and only for a local abort.
    pub(super) fn argument_congruence_overran(&mut self, deadline: Option<u64>) {
        let now = self.argument_steps();
        if deadline.is_none_or(|end| now <= end) {
            return;
        }
        if self.quot_types.is_none() {
            if self.ordinary_argument_success || self.bounds.arguments != u64::MAX {
                return;
            }
            if !self.ordinary_argument_overrun {
                self.ordinary_argument_overrun = true;
                return;
            }
        }
        self.full_argument_probe_after = now.saturating_add(ARGS_BUDGET);
    }

    /// Only an outer, completed success supplies ordinary scheduling evidence.
    pub(super) fn argument_congruence_succeeded(&mut self) {
        if self.quot_types.is_none() && self.bounds.arguments == u64::MAX {
            self.ordinary_argument_success = true;
            self.full_argument_probe_after = 0;
        }
    }

    /// Isolated trial: typed congruence before iota. All production
    /// callers belong to an eligible safe, non-formation attempt. The matching
    /// committed head and compatible checked substitutions supply exactly the
    /// ordinary typed-spine premise; recursor metadata chooses order only.
    /// No failed comparison is remembered or used as a negative verdict.
    pub(in super::super) fn try_recursor_congruence(&mut self, a: u32, c: u32) -> R<bool> {
        if self.markers != 0 {
            return Ok(false);
        }
        let (
            Val::Const {
                ci: ca,
                li: la,
                spine: sa,
            },
            Val::Const {
                ci: cc,
                li: lc,
                spine: sc,
            },
        ) = (self.vals[a as usize], self.vals[c as usize])
        else {
            return Ok(false);
        };
        if ca != cc
            || self.const_view(ca)?.rec.is_none()
            || self.cells[sa as usize].len != self.cells[sc as usize].len
            // Identity already runs before this optional route. A shared
            // nonempty spine could contain projection tags; skip rather than
            // scan/charge a spine the original trial treats as constant work.
            || (sa == sc && sa != 0)
        {
            return Ok(false);
        }
        #[cfg(feature = "introspection")]
        let root = probe::recursor_begin();
        #[cfg(feature = "introspection")]
        let start = self.steps;
        let saved = self.bounds;
        let depth = self.binders.len();
        self.limit_arguments(self.argument_steps().saturating_add(ARGS_BUDGET));
        let result = (|| {
            if !self.same_levels(la, lc)? {
                return Ok(false);
            }
            if sa != sc {
                let n = u64::from(self.cells[sa as usize].len);
                if n > self.limit.saturating_sub(self.steps) {
                    return Ok(false);
                }
                // Precharge fixed linear spine passes before extraction. Each
                // recursive unequal-handle conversion charges its own frame;
                // nested probes can only narrow this inherited allowance.
                for _ in 0..n {
                    self.step()?;
                }
                let (mut p, mut q) = (sa, sc);
                for _ in 0..n {
                    let (x, y) = (self.cells[p as usize], self.cells[q as usize]);
                    if x.tag != 0 || y.tag != 0 {
                        return Ok(false);
                    }
                    p = x.prev;
                    q = y.prev;
                }
            }
            Ok(self.spines(a, c, 0)? == Some(true))
        })();
        self.restore_bounds(saved);
        self.binders.truncate(depth);
        let result = match result {
            Err(e @ (KErr::Resource(_) | KErr::LiteralArithmetic | KErr::StepLimit)) => Err(e),
            Err(KErr::Abort) if self.steps > self.limit => Err(KErr::Abort),
            _ if self.steps > step_cap() => step_limit(),
            Err(KErr::Unsupported | KErr::Abort) | Ok(false) => Ok(false),
            result => result,
        };
        #[cfg(feature = "introspection")]
        probe::recursor_end(&result, self.steps.saturating_sub(start), root);
        result
    }

    /// Optional positive congruence, scoped to one attempt's immutable committed
    /// frontier and value IDs. `args_fail` is scheduling evidence only: a skipped
    /// attempt never establishes inequality. Values were forced by conversion;
    /// their substitutions and argument typing satisfy the ordinary `spines`
    /// premise. Abbreviation metadata chooses order, never equality authority.
    pub(in super::super) fn try_abbrev_congruence(&mut self, a: u32, c: u32) -> R<bool> {
        let (
            Val::Const {
                ci: ca,
                li: la,
                spine: sa,
            },
            Val::Const {
                ci: cc,
                li: lc,
                spine: sc,
            },
        ) = (self.vals[a as usize], self.vals[c as usize])
        else {
            return Ok(false);
        };
        if ca != cc
            || !matches!(self.const_view(ca)?.delta, Some((2, _)))
            || self.args_fail.contains(&(a, c))
        {
            return Ok(false);
        }
        let saved = self.bounds;
        let depth = self.binders.len();
        let deadline = self.begin_argument_congruence();
        let result = (|| {
            if !self.same_levels(la, lc)? {
                return Ok(false);
            }
            let n = u64::from(self.cells[sa as usize].len);
            if n != u64::from(self.cells[sc as usize].len) {
                return Ok(false);
            }
            if sa != sc {
                if n > self.limit.saturating_sub(self.steps) {
                    // A short preflight leaves this pair eligible after recovery.
                    if deadline.is_none() {
                        return Err(KErr::Abort);
                    }
                    return Ok(false);
                }
                // Preflight before any spine scan/copy. Each unit accounts for
                // the helper's fixed linear passes; charging flushes coarsely.
                for _ in 0..n {
                    self.step()?;
                }
            }
            if self.abbrev_selects_field(ca, n)? {
                return Ok(false);
            }
            Ok(self.spines(a, c, 0)? == Some(true))
        })();
        self.restore_bounds(saved);
        self.binders.truncate(depth);
        // Preserve the exact exhaustion signal before the existing post-probe
        // boundary check. Mandatory failures keep their existing precedence.
        match &result {
            Err(KErr::Resource(_) | KErr::LiteralArithmetic | KErr::StepLimit) => {}
            Err(KErr::Abort) if self.steps > self.limit => {}
            _ if self.steps > step_cap() => return step_limit(),
            _ => {}
        }
        match result {
            Ok(true) => {
                self.argument_congruence_succeeded();
                Ok(true)
            }
            Ok(false) => {
                self.args_fail
                    .insert((a, c), (), self.b, &mut self.reserved)?;
                Ok(false)
            }
            // Respect the whole attempt's guard even if reached inside this
            // optional route. It abandons the value kernel, not the declaration.
            Err(KErr::Unsupported) if self.steps <= step_cap() => {
                // Skip only this optional route for these two values in this
                // attempt. Ordinary delta still has to establish conversion.
                self.args_fail
                    .insert((a, c), (), self.b, &mut self.reserved)?;
                Ok(false)
            }
            Err(KErr::Abort) if self.steps <= self.limit => {
                self.argument_congruence_overran(deadline);
                Ok(false)
            }
            Err(error) => Err(error),
        }
    }

    /// Scheduling-only recognition of an exactly applied raw field selector.
    /// Extra applications demand the selected function's arguments and do not
    /// match. This scan is bounded by cached arity and its caller's allowance;
    /// ordinary unfolding still validates and performs all projection work.
    pub(in super::super) fn abbrev_selects_field(&mut self, ci: u32, arguments: u64) -> R<bool> {
        let Some(mut body) = self.const_view(ci)?.value else {
            return Ok(false);
        };
        for arity in 0..=arguments {
            self.step()?;
            match self
                .exprs
                .get(body, self.b)?
                .kind(self.exprs, self.levels, self.b)?
            {
                ExprKind::Lambda(_, _, next, _) if arity < arguments => body = next,
                ExprKind::Projection(..) if arity == arguments => return Ok(true),
                _ => return Ok(false),
            }
        }
        Ok(false)
    }

    /// The bounded late retry. The early helper already saw `offered`;
    /// only a changed pair of matching projections gets another opportunity.
    /// The existing typed helper supplies all equality premises. Local failure
    /// supplies none, and nested work cannot replenish an enclosing allowance.
    pub(in super::super) fn try_projection_congruence(
        &mut self,
        a: u32,
        c: u32,
        offered: (u32, u32),
    ) -> R<bool> {
        if (a, c) == offered {
            return Ok(false);
        }
        let (
            Val::Proj {
                idx: ia, sci: sa, ..
            },
            Val::Proj {
                idx: ic, sci: sc, ..
            },
        ) = (self.vals[a as usize], self.vals[c as usize])
        else {
            return Ok(false);
        };
        if ia != ic || sa != sc {
            return Ok(false);
        }
        let saved = self.bounds;
        let depth = self.binders.len();
        self.limit_arguments(self.argument_steps().saturating_add(ARGS_BUDGET));
        let result = self.proj_structs(a, c);
        self.restore_bounds(saved);
        self.binders.truncate(depth);
        // Local abort precedes the coarse global checkpoint in step(). Restore
        // the outer scope, preserve detected mandatory/inherited failures, and
        // check the global boundary before interpreting a tentative result.
        // The ordinary finalizer still charges pending work and owns cleanup.
        match result {
            Err(error @ (KErr::Resource(_) | KErr::LiteralArithmetic | KErr::StepLimit)) => {
                Err(error)
            }
            Err(KErr::Abort) if self.steps > self.limit => Err(KErr::Abort),
            _ if self.steps > step_cap() => step_limit(),
            Err(KErr::Abort) => Ok(false),
            result => result,
        }
    }

    /// Two stuck projections of the same field: reduce their structures by
    /// lazy delta and, once neither unfolds further, compare the projected
    /// fields instead of the whole structures (Lean's lazy_delta_proj_reduction).
    pub(in super::super) fn proj_structs(&mut self, a: u32, c: u32) -> R<bool> {
        let (
            Val::Proj {
                x: xa,
                idx: ia,
                sci: sa,
            },
            Val::Proj {
                x: xc,
                idx: ic,
                sci: sc,
            },
        ) = (self.vals[a as usize], self.vals[c as usize])
        else {
            return Ok(false);
        };
        if ia != ic || sa != sc {
            return Ok(false);
        }
        let xa = self.whnf_core(xa)?;
        let xc = self.whnf_core(xc)?;
        if xa == xc {
            return Ok(true);
        }
        let (xa, xc) = match self.lazy_delta(xa, xc, false)? {
            Lazy::Decided(true) => return Ok(true),
            Lazy::Decided(false) => return Ok(false),
            Lazy::Stuck(xa, xc) => (xa, xc),
        };
        if let (Some(fa), Some(fc)) = (self.ctor_field(xa, ia, sa)?, self.ctor_field(xc, ic, sc)?) {
            return self.defeq(fa, fc);
        }
        self.defeq(xa, xc)
    }
}
