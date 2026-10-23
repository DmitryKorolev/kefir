//! Completed inference with exact typed references. The existing long-context
//! entry admits larger sets and bounded small sets described. Keys fix source, levels, checking phase and ordered
//! referenced (value, stored context type) identities in the existing State-owned graph.
//! Untyped bindings bypass reuse; no evaluation or small-type cache is added.
use super::*;
type Mask = [u64; 4];
fn union(a: Option<Mask>, b: Option<Mask>) -> Option<Mask> {
    let (a, b) = (a?, b?);
    Some(std::array::from_fn(|i| a[i] | b[i]))
}
fn under_binder(m: Option<Mask>) -> Option<Mask> {
    let m = m?;
    Some(std::array::from_fn(|i| {
        (m[i] >> 1) | if i < 3 { m[i + 1] << 63 } else { 0 }
    }))
}
impl Kernel<'_, '_> {
    pub(super) fn read_plan(&mut self, e: ExprId) -> R<Option<Mask>> {
        if let Some(&m) = self.read_plans.get(&e.slot()) {
            return Ok(m);
        }
        let n = self.exprs.get(e, self.b)?;
        if n.loose_range() == 0 {
            return Ok(Some([0; 4]));
        }
        self.enter()?;
        let result: R<Option<Mask>> = (|| {
            let kind = self
                .exprs
                .get(e, self.b)?
                .kind(self.exprs, self.levels, self.b)?;
            let m = match kind {
                ExprKind::Bound(i) if i < 256 => {
                    let mut m = [0; 4];
                    m[(i / 64) as usize] = 1u64 << (i % 64);
                    Some(m)
                }
                ExprKind::App(a, b) => union(self.read_plan(a)?, self.read_plan(b)?),
                ExprKind::Lambda(_, d, b, _) | ExprKind::Pi(_, d, b, _) => {
                    union(self.read_plan(d)?, under_binder(self.read_plan(b)?))
                }
                ExprKind::Let(_, t, v, b, _) => union(
                    union(self.read_plan(t)?, self.read_plan(v)?),
                    under_binder(self.read_plan(b)?),
                ),
                ExprKind::Projection(_, _, x) => self.read_plan(x)?,
                _ => None,
            };
            Ok(m)
        })();
        self.leave();
        let m = result?;
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.read_plans,
            e.slot(),
            m,
        )?;
        Ok(m)
    }
}
/// Exact source, universe instance, checking phase, and an interned sequence
/// of all referenced (value,type) pairs. A token describes only a list, not a
/// type judgment; the separate result table stores only completed inference.
pub(super) type LargeReadKey = (u32, u32, u32, u32);
impl Kernel<'_, '_> {
    pub(super) fn large_type_key(
        &mut self,
        e: ExprId,
        mut env: u32,
        li: u32,
        checking: bool,
    ) -> R<Option<LargeReadKey>> {
        let Some(mask) = self.read_plan(e)? else {
            return Ok(None);
        };
        let n = mask.iter().map(|w| w.count_ones()).sum::<u32>();
        // Small sets share the same typed-context receipt. Restrict their
        // new eligibility to the priced range: sparse deep keys can cost
        // more to build than they save. Larger sets retain their old range.
        if n <= 2 || (n <= 8 && ((mask[0] >> 63) != 0 || mask[1..].iter().any(|&w| w != 0))) {
            return Ok(None);
        }
        let highest = mask
            .iter()
            .enumerate()
            .rev()
            .find(|(_, w)| **w != 0)
            .map_or(0, |(i, w)| {
                i as u64 * 64 + 64 - u64::from(w.leading_zeros())
            });
        // One known-size admission covers parent reads and prefix interning.
        self.steps_by(highest + u64::from(n))?;
        let (mut pos, mut token) = (0, 0);
        for (word, mut bits) in mask.into_iter().enumerate() {
            while bits != 0 {
                let index = word as u32 * 64 + bits.trailing_zeros();
                bits &= bits - 1;
                while pos < index {
                    if env == 0 {
                        return Ok(None);
                    }
                    env = self.envs[env as usize].parent;
                    pos += 1;
                }
                if env == 0 {
                    return Ok(None);
                }
                let node = self.envs[env as usize];
                if node.ty == NONE {
                    return Ok(None);
                }
                let key = (token, node.val, node.ty);
                token = match self.large_read_nodes.get(&key) {
                    Some(&id) => id,
                    None => {
                        let id = u32::try_from(self.large_read_nodes.len())
                            .ok()
                            .and_then(|x| x.checked_add(1))
                            .ok_or(ResourceError::Counter)?;
                        map_put(
                            self.b,
                            &mut self.reserved,
                            &mut self.large_read_nodes,
                            key,
                            id,
                        )?;
                        id
                    }
                };
            }
        }
        Ok(Some((e.slot(), li, u32::from(checking), token)))
    }
}
