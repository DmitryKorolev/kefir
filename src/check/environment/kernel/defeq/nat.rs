//! Natural successor comparison and bounded exposure before arithmetic reduction.

use super::*;

impl<'e, 'w> Kernel<'e, 'w> {
    pub(in super::super) fn expose_natural_successors(
        &mut self,
        mut n: u32,
        projections: bool,
    ) -> R<(u32, u32)> {
        let mut count = 0u32;
        for _ in 0..64 {
            self.steps_by(1)?;
            n = self.whnf_core(n)?;
            if projections && let Some(next) = self.expose_stuck_projection(n)? {
                n = next;
                continue;
            }
            let Val::Const { ci, spine, .. } = self.vals[n as usize] else {
                break;
            };
            if spine == 0 {
                break;
            }
            if self.cells[spine as usize].len == 1
                && let Some(argument) = self.arg_item(spine)
                && self.nat_ctors()?.is_some_and(|(_, _, succ)| succ == ci)
            {
                count += 1;
                n = argument;
            } else if self.const_view(ci)?.delta.is_some() {
                n = self.unfold_value(n)?;
            } else {
                break;
            }
        }
        Ok((n, count))
    }
    pub(super) fn compare_before_natural_reduction(&mut self, a: u32, c: u32) -> R<bool> {
        let (
            Val::Const {
                ci: ca, spine: sa, ..
            },
            Val::Const {
                ci: cc, spine: sc, ..
            },
        ) = (self.vals[a as usize], self.vals[c as usize])
        else {
            return Ok(false);
        };
        let ordinary_pair = |spine: u32| {
            let last = self.cells[spine as usize];
            last.len == 2 && last.tag == 0 && self.cells[last.prev as usize].tag == 0
        };
        let left_pair = ordinary_pair(sa);
        let right_pair = ordinary_pair(sc);
        let selected = |op| matches!(op, Some(Operation::Add | Operation::Div | Operation::Mod));
        let left_op =
            left_pair && self.const_view(ca)?.params.is_empty() && selected(self.natop(ca)?);
        let right_op =
            right_pair && self.const_view(cc)?.params.is_empty() && selected(self.natop(cc)?);
        if !left_op && !right_op {
            return Ok(false);
        }
        // The ordinary let-fold policy already bounds evaluation through a let.
        // Leave either marked argument to that route.
        let spine = if left_op { sa } else { sc };
        let last = self.cells[spine as usize];
        if !self.let_marks.is_empty()
            && [last.item, self.cells[last.prev as usize].item]
                .into_iter()
                .any(|mut value| {
                    for _ in 0..4 {
                        if self.let_bit(2 * u64::from(value)) {
                            return true;
                        }
                        match self.vals[value as usize] {
                            Val::Ind(next) => value = next,
                            _ => return false,
                        }
                    }
                    true
                })
        {
            return Ok(false);
        }
        let nesting = self.natural_probe_depth;
        if nesting >= 3 || (nesting == 0 && self.bounds.arguments != u64::MAX) {
            return Ok(false);
        }
        self.natural_probe_depth = nesting + 1;
        let saved = self.bounds;
        let depth = self.binders.len();
        self.limit_arguments(self.argument_steps().saturating_add(ARGS_BUDGET));
        let outcome = (|| -> R<bool> {
            let (target, mut other) = if left_op { (a, c) } else { (c, a) };
            for _ in 0..12 {
                self.steps_by(1)?;
                if other == target {
                    return Ok(true);
                }
                if let Some(exposed) = self.expose_stuck_projection(other)? {
                    other = exposed;
                    continue;
                }
                let Val::Const {
                    ci: x,
                    li: lx,
                    spine: sx,
                } = self.vals[other as usize]
                else {
                    break;
                };
                let Val::Const {
                    ci: y,
                    li: ly,
                    spine: sy,
                } = self.vals[target as usize]
                else {
                    break;
                };
                if x == y {
                    if self.cells[sx as usize].len != self.cells[sy as usize].len
                        || !self.same_levels(lx, ly)?
                    {
                        break;
                    }
                    if [sx, sy].iter().any(|&spine| {
                        let last = self.cells[spine as usize];
                        last.tag != 0 || self.cells[last.prev as usize].tag != 0
                    }) {
                        break;
                    }
                    self.steps_by(u64::from(self.cells[sx as usize].len))?;
                    let (left, right, ls, rs) = if left_op {
                        (target, other, sy, sx)
                    } else {
                        (other, target, sx, sy)
                    };
                    let left_base =
                        self.whnf_core(self.cells[self.cells[ls as usize].prev as usize].item)?;
                    let right_base =
                        self.whnf_core(self.cells[self.cells[rs as usize].prev as usize].item)?;
                    if left_base != right_base
                        && self.quick(left_base, right_base)? != Some(true)
                        && self.natop(x)? == Some(Operation::Add)
                    {
                        let (u, m) = self.expose_natural_successors(left, false)?;
                        let (v, n) = self.expose_natural_successors(right, false)?;
                        if m != 0 && m == n && (u == v || self.defeq(u, v)?) {
                            return Ok(true);
                        }
                    }
                    return Ok(self.spines(left, right, 0)? == Some(true));
                }
                if self.const_view(x)?.delta.is_none() {
                    break;
                }
                self.steps_by(u64::from(self.cells[sx as usize].len) + 1)?;
                other = self.unfold_value(other)?;
            }
            Ok(false)
        })();
        self.natural_probe_depth = nesting;
        self.restore_bounds(saved);
        self.binders.truncate(depth);
        match outcome {
            Err(e @ (KErr::Resource(_) | KErr::LiteralArithmetic | KErr::StepLimit)) => Err(e),
            Err(KErr::Abort) if self.steps > self.limit => Err(KErr::Abort),
            _ if self.steps > step_cap() => step_limit(),
            Err(KErr::Unsupported | KErr::Abort) => Ok(false),
            r => r,
        }
    }
    pub(super) fn nat_succ(&mut self, lit: u32, other: u32) -> R<bool> {
        let Val::Nat(n) = self.vals[lit as usize] else {
            return Ok(false);
        };
        let Some((_, zero, succ)) = self.nat_ctors()? else {
            return Ok(false);
        };
        let Val::Const { ci, spine, .. } = self.vals[other as usize] else {
            return Ok(false);
        };
        self.observe_natural(n, NONE)?;
        let lit = &self.nats[n as usize];
        if ci == zero && spine == 0 {
            return Ok(matches!(lit, NatLit::Small(0)));
        }
        if ci == succ && self.cells[spine as usize].len == 1 && !matches!(lit, NatLit::Small(0)) {
            let Some(arg) = self.arg_item(spine) else {
                return Ok(false);
            };
            let p = self.predecessor_value(n)?;
            return self.defeq(p, arg);
        }
        Ok(false)
    }
}
