//! Definition exposure and lazy delta comparison.

use super::*;

impl<'e, 'w> Kernel<'e, 'w> {
    /// Lazy delta: unfold the side with the higher definitional priority one
    /// step at a time, trying cheap decisions after each step.
    pub(in super::super) fn lazy_delta(
        &mut self,
        mut a: u32,
        mut c: u32,
        arguments: bool,
    ) -> R<Lazy> {
        loop {
            if self.compare_before_natural_reduction(a, c)? {
                return Ok(Lazy::Decided(true));
            }
            let mut reduced = false;
            if let Some(n) = self.nat_reduce_in(a, true)? {
                a = self.whnf_core(n)?;
                reduced = true;
            }
            if let Some(n) = self.nat_reduce_in(c, true)? {
                c = self.whnf_core(n)?;
                reduced = true;
            }
            // A literal reduction can settle the comparison by itself.
            if reduced {
                if a == c {
                    return Ok(Lazy::Decided(true));
                }
                if let Some(r) = self.quick(a, c)? {
                    return Ok(Lazy::Decided(r));
                }
            }
            let pa = self.delta_of(a)?;
            let pc = self.delta_of(c)?;
            match (pa, pc) {
                (None, None) => return Ok(Lazy::Stuck(a, c)),
                (Some(_), None) => {
                    if let Some(exposed) = self.expose_stuck_projection(c)? {
                        c = exposed;
                    } else {
                        a = self.unfold_value(a)?;
                    }
                }
                (None, Some(_)) => {
                    if let Some(exposed) = self.expose_stuck_projection(a)? {
                        a = exposed;
                    } else {
                        c = self.unfold_value(c)?;
                    }
                }
                (Some(x), Some(y)) => {
                    // Positive typed congruence for committed abbreviations can
                    // settle the pair before unfolding exposes an expensive major.
                    // No argument is erased on this route.
                    if arguments
                        && x.0 == 2
                        && (self.try_abbrev_congruence(a, c)?
                            || self.try_alternative_exposure(a, c)?)
                    {
                        return Ok(Lazy::Decided(true));
                    }
                    // Regular definitions retain their ordinary argument route;
                    // other heads unfold after optional positive probes fail.
                    if let (Val::Const { ci: ca, li: la, .. }, Val::Const { ci: cc, li: lc, .. }) =
                        (self.vals[a as usize], self.vals[c as usize])
                        && ca == cc
                        && x.0 == 1
                        && !self.args_fail.contains(&(a, c))
                    {
                        // Outside the argument allowance: computed once per head.
                        let skip = self.absent_args(ca)?;
                        let saved = self.bounds;
                        let depth = self.binders.len();
                        let deadline = self.begin_argument_congruence();
                        let r = self.same_levels(la, lc).and_then(|eq| {
                            if eq {
                                self.same_spines_skipping(a, c, skip)
                            } else {
                                Ok(false)
                            }
                        });
                        self.restore_bounds(saved);
                        self.binders.truncate(depth);
                        match r {
                            Ok(true) => {
                                self.argument_congruence_succeeded();
                                return Ok(Lazy::Decided(true));
                            }
                            Ok(false) => {
                                self.args_fail
                                    .insert((a, c), (), self.b, &mut self.reserved)?;
                            }
                            // Our own allowance ran out: unfold instead, which is
                            // the complete route. An outer allowance propagates.
                            Err(KErr::Abort) if self.steps <= self.limit => {
                                if self.steps > step_cap() {
                                    return step_limit();
                                }
                                self.argument_congruence_overran(deadline);
                            }
                            Err(e) => return Err(e),
                        }
                    }
                    if let Some((left, exposed)) = self.expose_shared_argument(a, c)? {
                        if left {
                            a = exposed;
                        } else {
                            c = exposed;
                        }
                    } else if x < y {
                        c = self.unfold_value(c)?;
                    } else if y < x {
                        a = self.unfold_value(a)?;
                    } else {
                        a = self.unfold_value(a)?;
                        c = self.unfold_value(c)?;
                    }
                }
            }
            if a == c {
                return Ok(Lazy::Decided(true));
            }
            if let Some(r) = self.quick(a, c)? {
                return Ok(Lazy::Decided(r));
            }
        }
    }
    /// A visible argument is only a scheduling hint. Keep the opposite head
    /// intact through a short chain of reductions, then resume ordinary
    /// comparison, including its universe checks, on the actual reduct.
    pub(in super::super) fn expose_shared_argument(
        &mut self,
        a: u32,
        c: u32,
    ) -> R<Option<(bool, u32)>> {
        let (
            Val::Const {
                ci: ca, spine: sa, ..
            },
            Val::Const {
                ci: cc, spine: sc, ..
            },
        ) = (self.vals[a as usize], self.vals[c as usize])
        else {
            return Ok(None);
        };
        let (left, mut exposed, spine, target) = match (sa, sc) {
            (0, s) if s != 0 => (false, c, s, ca),
            (s, 0) if s != 0 => (true, a, s, cc),
            _ => return Ok(None),
        };
        let last = self.cells[spine as usize];
        if ca == cc || ![last, self.cells[last.prev as usize]].iter().any(|cell|
            cell.len != 0 && cell.tag == 0 &&
            matches!(self.vals[cell.item as usize], Val::Const { ci, spine: 0, .. } if ci == target)
        ) {
            return Ok(None);
        }
        let saved = self.bounds;
        let depth = self.binders.len();
        self.limit_total(self.steps.saturating_add(512));
        let result = (|| {
            for _ in 0..4 {
                let Val::Const { ci, spine, .. } = self.vals[exposed as usize] else {
                    break;
                };
                if spine == 0 || self.const_view(ci)?.delta.is_none() {
                    break;
                }
                self.steps_by(1 + u64::from(self.cells[spine as usize].len))?;
                exposed = self.unfold_value(exposed)?;
                if matches!(self.vals[exposed as usize], Val::Const { ci, spine: 0, .. } if ci == target)
                {
                    return Ok(Some((left, exposed)));
                }
            }
            Ok(None)
        })();
        self.restore_bounds(saved);
        self.binders.truncate(depth);
        match result {
            Err(e @ (KErr::Resource(_) | KErr::LiteralArithmetic | KErr::StepLimit)) => Err(e),
            Err(KErr::Abort) if self.steps > self.limit => Err(KErr::Abort),
            _ if self.steps > step_cap() => step_limit(),
            Err(KErr::Unsupported | KErr::Abort) => Ok(None),
            r => r,
        }
    }
    /// A projection opposite a delta head may hide the same cheap head. Expose
    /// it before demanding the opposite definition's computation.
    /// All values retain the existing validated projection-typing premises;
    /// this reduction grants no checkedness or comparison result. Each retry
    /// charges a step, and all inner normalization shares the enclosing limits.
    /// Alternative exposure and abbreviation argument comparison re-enter
    /// defeq/lazy_delta, so their one-sided projection pairs use this route too.
    pub(in super::super) fn expose_stuck_projection(&mut self, v: u32) -> R<Option<u32>> {
        let Val::Proj { x, idx, sci } = self.vals[v as usize] else {
            return Ok(None);
        };
        self.step()?;
        match self.proj(x, idx, sci).and_then(|next| self.whnf_core(next)) {
            Ok(next) => Ok((next != v).then_some(next)),
            Err(KErr::Unsupported) => Ok(None),
            Err(error) => Err(error),
        }
    }
    /// Bounded sequential exposure, not resumable interleaving. Only the
    /// unrestricted attempt may open this schedule; children share its finite
    /// allowance and cannot recursively start another alternative-order probe.
    /// Failed pairs are attempt-local scheduling facts, never inequality.
    pub(in super::super) fn try_alternative_exposure(&mut self, a: u32, c: u32) -> R<bool> {
        if self.bounds.total != u64::MAX
            || self.bounds.arguments != u64::MAX
            || self.args_fail.contains(&(a, c))
        {
            return Ok(false);
        }
        let (Val::Const { ci: ca, .. }, Val::Const { ci: cc, .. }) =
            (self.vals[a as usize], self.vals[c as usize])
        else {
            return Ok(false);
        };
        if ca == cc
            || !matches!(self.const_view(ca)?.delta, Some((2, _)))
            || !matches!(self.const_view(cc)?.delta, Some((2, _)))
        {
            return Ok(false);
        }
        let saved = self.bounds;
        let start = self.argument_steps();
        let end = start.saturating_add(ARGS_BUDGET).min(saved.arguments);
        for (right, allowance) in [(true, start.saturating_add(ARGS_BUDGET / 2)), (false, end)] {
            let depth = self.binders.len();
            self.limit_arguments(allowance.min(end));
            let result = (|| {
                let selected = if right { c } else { a };
                let Val::Const { spine, .. } = self.vals[selected as usize] else {
                    return Ok(false);
                };
                let n = u64::from(self.cells[spine as usize].len);
                if n > self.limit.saturating_sub(self.steps) {
                    return Ok(false);
                }
                for _ in 0..n {
                    self.step()?;
                }
                let Val::Const {
                    ci: selected_ci, ..
                } = self.vals[selected as usize]
                else {
                    return Ok(false);
                };
                // Self-delegation is another positive delta reduction, not
                // evidence about the other side. Preflight further spines
                // against the same finite allowance. A cached delta charges a
                // step; an uncached delta can reuse a cached WHNF. No new
                // checkedness is inferred by this scheduling loop.
                // Progress invariant: a committed abbreviation's closed body
                // refers only to its strict prior declaration frontier. Its
                // evaluation under the empty environment, including validated
                // generated reductions and universe substitution, cannot
                // introduce the abbreviation itself. Thus a bare selected
                // head leaves this loop after unfolding; returning that head
                // requires a nonempty input spine, which we charge below.
                let mut exposed = self.unfold_value(selected)?;
                while exposed != selected {
                    let Val::Const { ci, spine, .. } = self.vals[exposed as usize] else {
                        break;
                    };
                    if ci != selected_ci {
                        break;
                    }
                    let n = u64::from(self.cells[spine as usize].len);
                    if n > self.limit.saturating_sub(self.steps) {
                        return Ok(false);
                    }
                    for _ in 0..n {
                        self.step()?;
                    }
                    let next = self.unfold_value(exposed)?;
                    if next == exposed {
                        break;
                    }
                    exposed = next;
                }
                if right {
                    self.defeq(a, exposed)
                } else {
                    self.defeq(exposed, c)
                }
            })();
            self.restore_bounds(saved);
            self.binders.truncate(depth);
            // Preserve detected exhaustion and mandatory failures before the
            // existing post-probe boundary check; neither permits a verdict.
            match &result {
                Err(KErr::Resource(_) | KErr::LiteralArithmetic | KErr::StepLimit) => {}
                Err(KErr::Abort) if self.steps > self.limit => {}
                _ if self.steps > step_cap() => return step_limit(),
                _ => {}
            }
            match result {
                Ok(true) => return Ok(true),
                Ok(false) | Err(KErr::Unsupported) => {}
                Err(KErr::Abort) if self.steps <= self.limit => {}
                Err(error) => return Err(error),
            }
            if self.argument_steps() >= end {
                break;
            }
        }
        self.args_fail
            .insert((a, c), (), self.b, &mut self.reserved)?;
        Ok(false)
    }
    fn delta_of(&mut self, v: u32) -> R<Option<(u8, u32)>> {
        Ok(match self.vals[v as usize] {
            Val::Const { ci, .. } => self.const_view(ci)?.delta,
            _ => None,
        })
    }
    // Invariant: synthetic markers belong only to syn_eq environments and
    // are never evaluated here. Cached reductions carry no checkedness.
    pub(in super::super) fn unfold_value(&mut self, v: u32) -> R<u32> {
        let Val::Const { ci, li, spine } = self.vals[v as usize] else {
            return no();
        };
        let cached = self.meta[v as usize].delta;
        if cached != NONE {
            // Meter a chain of cached reductions; flushes use existing blocks.
            self.step()?;
            return Ok(cached);
        }
        // Only completed positive reductions are installed. An unsupported
        // route, unmatched rule guard, exhausted allowance or resource error
        // cannot create a cached result. It remains a term, not an equality or
        // checked-inference certificate.
        let reduced = if let Some(sel) = self.derived_unfold(ci, li, spine)? {
            self.whnf_core(sel)?
        } else {
            let n = self.unfold(ci, li, spine)?;
            self.whnf_core(n)?
        };
        self.meta[v as usize].delta = reduced;
        Ok(reduced)
    }
}
