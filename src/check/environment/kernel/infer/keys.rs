//! Scope and renaming for shared type inference.

use super::*;

impl<'e, 'w> Kernel<'e, 'w> {
    // Review trial: completed checked source judgments may be
    // transported under an injective renaming of exactly referenced locals.
    // Domains are exact closed types; aliases and universe instances match.
    // This is dependency metadata, never permission to evaluate syntax.
    pub(in super::super) fn known_support(&mut self, e: ExprId) -> R<Option<u64>> {
        let node = self.exprs.get(e, self.b)?;
        let r = node.loose_range();
        let mask = match r {
            0 => 0,
            1 => 1,
            64.. => u64::MAX,
            // The store increments every composite depth. Positive range with
            // depth zero therefore identifies a Bound node exactly.
            _ if node.depth() == 0 => 1u64 << (r - 1),
            _ => {
                if let Some(bits) = node.plain_binding_mask() {
                    // Sparse representatives are admitted only after explicit support
                    // demand. Retain that signal for possible interior holes.
                    let count = bits.count_ones();
                    if !(3..=16).contains(&count) || count + bits.trailing_zeros() == r {
                        return Ok(Some(u64::from(bits)));
                    }
                }
                return Ok(self.source_support.get(&e.slot()).copied());
            }
        };
        Ok(Some(mask))
    }
    pub(in super::super) fn source_support(&mut self, e: ExprId) -> R<u64> {
        if let Some(m) = self.known_support(e)? {
            return Ok(m);
        }
        // A published short mask supplies the same support as the recursive
        // calculation below. Remember demand for the representative table.
        if let Some(bits) = self.exprs.get(e, self.b)?.plain_binding_mask() {
            let m = u64::from(bits);
            map_put(
                self.b,
                &mut self.reserved,
                &mut self.source_support,
                e.slot(),
                m,
            )?;
            return Ok(m);
        }
        self.enter()?;
        let r: R<u64> = (|| {
            let k = self
                .exprs
                .get(e, self.b)?
                .kind(self.exprs, self.levels, self.b)?;
            let m = match k {
                ExprKind::Bound(i) if i < 63 => 1u64 << i,
                ExprKind::Bound(_) => u64::MAX,
                ExprKind::Sort(_)
                | ExprKind::Constant(..)
                | ExprKind::Natural(_)
                | ExprKind::String(_) => 0,
                ExprKind::App(f, a) => self.source_support(f)? | self.source_support(a)?,
                ExprKind::Lambda(_, d, b, _) | ExprKind::Pi(_, d, b, _) => {
                    let d = self.source_support(d)?;
                    let b = self.source_support(b)?;
                    if b == u64::MAX {
                        u64::MAX
                    } else {
                        d | (b >> 1)
                    }
                }
                ExprKind::Let(_, t, v, b, _) => {
                    let t = self.source_support(t)?;
                    let v = self.source_support(v)?;
                    let b = self.source_support(b)?;
                    if b == u64::MAX {
                        u64::MAX
                    } else {
                        t | v | (b >> 1)
                    }
                }
                ExprKind::Projection(_, _, v) => self.source_support(v)?,
                _ => u64::MAX,
            };
            Ok(m)
        })();
        self.leave();
        let m = r?;
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.source_support,
            e.slot(),
            m,
        )?;
        Ok(m)
    }
    pub(in super::super) fn alpha_key(
        &mut self,
        e: ExprId,
        mut env: u32,
        li: u32,
        r: u32,
    ) -> R<Option<(AlphaKey, [u32; 8])>> {
        // A referenced index >= 63 cannot have a supported exact mask.
        if r == 0 || r > 63 {
            return Ok(None);
        }
        // The highest loose index is necessarily read. Reject environments
        // that cannot qualify before computing the complete dependency mask.
        let mut top = env;
        for _ in 1..r {
            if top == 0 {
                return Ok(None);
            }
            top = self.envs[top as usize].parent;
        }
        if top == 0 {
            return Ok(None);
        }
        let highest = self.envs[top as usize];
        if !matches!(self.vals[highest.val as usize], Val::Local { id, spine: 0 } if id < MARKER_BASE)
            || highest.ty == NONE
            || !matches!(
                self.vals[highest.ty as usize],
                Val::Sort(_) | Val::Const { spine: 0, .. }
            )
        {
            return Ok(None);
        }
        let mut mask = self.source_support(e)?;
        if mask == u64::MAX || mask.count_ones() > 8 {
            return Ok(None);
        }
        let mut ts = [0; 8];
        let mut aliases = [0; 8];
        let mut ids = [0; 8];
        let mut i = 0;
        while mask != 0 {
            if env == 0 {
                return Ok(None);
            }
            let n = self.envs[env as usize];
            env = n.parent;
            let used = mask & 1 != 0;
            mask >>= 1;
            if !used {
                continue;
            }
            let Val::Local { id, spine: 0 } = self.vals[n.val as usize] else {
                return Ok(None);
            };
            if id >= MARKER_BASE || n.ty == NONE || self.locals[id as usize] != n.ty {
                return Ok(None);
            }
            if !matches!(
                self.vals[n.ty as usize],
                Val::Sort(_) | Val::Const { spine: 0, .. }
            ) {
                return Ok(None);
            }
            ts[i] = n.ty;
            ids[i] = id;
            aliases[i] = (0..i).find(|&j| ids[j] == id).unwrap_or(i) as u32;
            i += 1;
        }
        Ok(Some(((e.slot(), li, i as u32, ts, aliases), ids)))
    }
    fn rename_env(
        &mut self,
        env: u32,
        mask: u64,
        rn: u32,
        old: &[u32; 8],
        new: &[u32; 8],
        len: u32,
    ) -> R<u32> {
        if mask == 0 {
            return Ok(0);
        }
        if mask == u64::MAX || env == 0 {
            return no();
        }
        if let Some(&v) = self.renamed_envs.get(&(env, mask, rn)) {
            return Ok(v);
        }
        self.enter()?;
        let r = (|| {
            let n = self.envs[env as usize];
            let parent = self.rename_env(n.parent, mask >> 1, rn, old, new, len)?;
            let (v, t) = if mask & 1 == 0 {
                (n.val, n.ty)
            } else {
                let v = self.rename_value(n.val, rn, old, new, len)?;
                let t = if n.ty == NONE {
                    NONE
                } else {
                    self.rename_value(n.ty, rn, old, new, len)?
                };
                (v, t)
            };
            self.env_push(parent, v, t)
        })();
        self.leave();
        let v = r?;
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.renamed_envs,
            (env, mask, rn),
            v,
        )?;
        Ok(v)
    }
    fn rename_spine(
        &mut self,
        sp: u32,
        rn: u32,
        old: &[u32; 8],
        new: &[u32; 8],
        len: u32,
    ) -> R<u32> {
        if sp == 0 {
            return Ok(0);
        }
        if let Some(&v) = self.renamed_spines.get(&(sp, rn)) {
            return Ok(v);
        }
        self.enter()?;
        let r = (|| {
            let c = self.cells[sp as usize];
            let p = self.rename_spine(c.prev, rn, old, new, len)?;
            let v = if c.tag == 0 {
                self.rename_value(c.item, rn, old, new, len)?
            } else {
                c.item
            };
            self.cell(p, v, c.tag)
        })();
        self.leave();
        let v = r?;
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.renamed_spines,
            (sp, rn),
            v,
        )?;
        Ok(v)
    }
    pub(in super::super) fn rename_value(
        &mut self,
        t: u32,
        rn: u32,
        old: &[u32; 8],
        new: &[u32; 8],
        len: u32,
    ) -> R<u32> {
        if let Some(&v) = self.renamed_values.get(&(t, rn)) {
            return Ok(v);
        }
        self.enter()?;
        let r = (|| {
            let v = match self.vals[t as usize] {
                Val::Sort(_) | Val::Nat(_) | Val::Str(_) => return Ok(t),
                Val::Ind(v) => return self.rename_value(v, rn, old, new, len),
                Val::Delayed { e, env, li } => {
                    let m = self.source_support(e)?;
                    let env = self.rename_env(env, m, rn, old, new, len)?;
                    return self.thunk(e, env, li);
                }
                Val::Lam(c) | Val::Pi(c) | Val::LamTy(c) => {
                    let d = self.source_support(c.dom)?;
                    let b = self.source_support(c.body)?;
                    if d == u64::MAX || b == u64::MAX {
                        return no();
                    }
                    let m = d | (b >> 1);
                    let env = self.rename_env(c.env, m, rn, old, new, len)?;
                    let form = match self.vals[t as usize] {
                        Val::Lam(_) => 0,
                        Val::Pi(_) => 1,
                        _ => 2,
                    };
                    return self.push_clo(form, Clo { env, ..c }, 64 - m.leading_zeros());
                }
                Val::Arrow { dom, cod } => Val::Arrow {
                    dom: self.rename_value(dom, rn, old, new, len)?,
                    cod: self.rename_value(cod, rn, old, new, len)?,
                },
                Val::Local { id, spine } => {
                    let Some(i) = old[..len as usize].iter().position(|&x| x == id) else {
                        return no();
                    };
                    Val::Local {
                        id: new[i],
                        spine: self.rename_spine(spine, rn, old, new, len)?,
                    }
                }
                Val::Const { ci, li, spine } => Val::Const {
                    ci,
                    li,
                    spine: self.rename_spine(spine, rn, old, new, len)?,
                },
                Val::Proj { x, idx, sci } => Val::Proj {
                    x: self.rename_value(x, rn, old, new, len)?,
                    idx,
                    sci,
                },
            };
            self.push(v)
        })();
        self.leave();
        let v = r?;
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.renamed_values,
            (t, rn),
            v,
        )?;
        Ok(v)
    }
}
