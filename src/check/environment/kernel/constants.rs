//! Constant lookup and recognition of checked natural operations.

use super::*;

impl<'e, 'w> Kernel<'e, 'w> {
    pub(super) fn canon(&mut self, n: NameId) -> R<u32> {
        Ok(self.names.summary(n, self.b)?.canonical)
    }
    // Stable ci/name identity is owned by the retained graph. Borrowed views
    // belong only to this attempt and are resolved on demand through the same
    // visible-safe-constant lookup. A missing view grants no result.
    pub(super) fn const_info(&mut self, n: NameId) -> R<u32> {
        let canon = self.canon(n)?;
        if let Some(&ci) = self.const_by_canon.get(&canon) {
            return Ok(ci);
        }
        let info = self.read_const_info(n, canon)?;
        let ci = u32::try_from(self.constant_slots.len()).map_err(|_| ResourceError::Counter)?;
        let at = u32::try_from(self.consts.len()).map_err(|_| ResourceError::Counter)?;
        room(self.b, &mut self.reserved, &mut self.constant_slots, 1)?;
        self.constant_slots.push(ConstantSlot {
            name: n,
            epoch: 0,
            view: NONE,
        });
        room(self.b, &mut self.reserved, &mut self.consts, 1)?;
        self.consts.push(info);
        self.constant_slots[ci as usize].view = at;
        self.constant_slots[ci as usize].epoch = self.constant_epoch;
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.const_by_canon,
            canon,
            ci,
        )?;
        Ok(ci)
    }
    #[inline(always)]
    pub(super) fn const_view(&mut self, ci: u32) -> R<&CInfo<'e>> {
        // Construction invariant: in epoch1 each completed insertion appends
        // stable slot and dense view at the same index. Partial insertion
        // errors terminate the attempt. Only restore separates these indices
        // and it always installs epoch>=2; overflow discards the snapshot.
        if self.constant_epoch == 1 {
            return self
                .consts
                .get(ci as usize)
                .ok_or(KErr::Resource(ResourceError::Invariant));
        }
        let slot = *self
            .constant_slots
            .get(ci as usize)
            .ok_or(ResourceError::Invariant)?;
        if slot.epoch == self.constant_epoch {
            return Ok(&self.consts[slot.view as usize]);
        }
        self.load_const_view(ci, slot.name)
    }
    #[cold]
    fn load_const_view(&mut self, ci: u32, name: NameId) -> R<&CInfo<'e>> {
        let canon = self.canon(name)?;
        let info = self.read_const_info(name, canon)?;
        let at = u32::try_from(self.consts.len()).map_err(|_| ResourceError::Counter)?;
        room(self.b, &mut self.reserved, &mut self.consts, 1)?;
        self.consts.push(info);
        // Only completed lookup/allocation publishes a current-attempt view.
        self.constant_slots[ci as usize].view = at;
        self.constant_slots[ci as usize].epoch = self.constant_epoch;
        Ok(&self.consts[at as usize])
    }
    #[inline(always)]
    pub(super) fn const_view_mut(&mut self, ci: u32) -> R<&mut CInfo<'e>> {
        // The same completed-insertion invariant as const_view permits the
        // cold index; restored epochs hydrate and then use their stamped view.
        if self.constant_epoch == 1 {
            return self
                .consts
                .get_mut(ci as usize)
                .ok_or(KErr::Resource(ResourceError::Invariant));
        }
        self.const_view(ci)?;
        let at = self.constant_slots[ci as usize].view;
        Ok(&mut self.consts[at as usize])
    }
    fn read_const_info(&mut self, n: NameId, canon: u32) -> R<CInfo<'e>> {
        let env = self.env;
        let Some(sig) = env.lookup_visible(n, self.before, self.formation, self.names, self.b)?
        else {
            return no();
        };
        if sig.safety != Safety::Safe {
            return no();
        }
        let ty = match sig.ty {
            TypeSource::Original(t) => Some(t),
            // Validated quotient schemas, built by the caller only on demand.
            TypeSource::Quotient(role) => match self.quot_types {
                Some(q) => Some(q[role.index()]),
                None => {
                    self.wants_quot = true;
                    None
                }
            },
            _ => None,
        };
        let delta = match (sig.kind, sig.value) {
            (StoredKind::Ordinary(Kind::Definition), Some(_)) => Some(match sig.hint {
                Some(Hint::Abbrev) => (2, 0),
                Some(Hint::Opaque) | None => (0, 0),
                Some(Hint::Regular(bytes)) => {
                    let mut h = 0u32;
                    // A height outside u32 is not a Lean hint: decline, as
                    // the ordinary route does.
                    for &d in bytes {
                        if !d.is_ascii_digit() {
                            return no();
                        }
                        h = match h
                            .checked_mul(10)
                            .and_then(|h| h.checked_add((d - b'0') as u32))
                        {
                            Some(h) => h,
                            None => return no(),
                        };
                    }
                    (1, h)
                }
            }),
            (StoredKind::Ordinary(Kind::Theorem), Some(_)) => Some((0, 0)),
            _ => None,
        };
        let mut info = CInfo {
            name: sig.name,
            canon,
            ty,
            value: sig.value,
            params: sig.parameters,
            delta,
            rec: None,
            ctor: None,
            ind: None,
            natop: 0,
            natpred: 0,
            quot: match sig.kind {
                StoredKind::Quotient(role) => Some(role),
                _ => None,
            },
        };
        match sig.kind {
            StoredKind::Signature(SignatureKind::Recursor) => {
                if let Some(r) = env.recursor(n, self.before.min(env.len()), self.names, self.b)? {
                    info.rec = Some(Rec {
                        family: self.canon(r.family)?,
                        k: r.k,
                        eta: r.num_indices == 0
                            && r.rules.len() == 1
                            && env
                                .inductive(
                                    r.family,
                                    self.before.min(env.len()),
                                    self.names,
                                    self.b,
                                )?
                                .is_some_and(|i| {
                                    i.nonrecursive
                                        && i.num_indices == 0
                                        && i.constructors.len() == 1
                                }),
                        common: r.common_prefix,
                        cparams: r.constructor_params,
                        nidx: r.num_indices,
                        rules: r.rules,
                    });
                }
            }
            StoredKind::Signature(SignatureKind::Constructor) => {
                if let Some(c) =
                    env.constructor(n, self.before.min(env.len()), self.names, self.b)?
                {
                    info.ctor = Some((self.canon(c.family)?, c.index));
                }
            }
            StoredKind::Signature(SignatureKind::Inductive) => {
                if let Some(i) = env.inductive(n, self.before.min(env.len()), self.names, self.b)? {
                    info.ind = Some(Ind {
                        nparams: i.num_params,
                        nidx: i.num_indices,
                        nonrecursive: i.nonrecursive,
                        ctors: i.constructors,
                    });
                }
            }
            _ => {}
        }
        Ok(info)
    }
    pub(super) fn const_type(&mut self, ci: u32, li: u32) -> R<u32> {
        if let Some(&v) = self.const_type.get(&(ci, li)) {
            return Ok(v);
        }
        let Some(ty) = self.const_view(ci)?.ty else {
            return no();
        };
        let v = self.eval(ty, 0, li)?;
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.const_type,
            (ci, li),
            v,
        )?;
        Ok(v)
    }
    pub(super) fn const_body(&mut self, ci: u32, li: u32) -> R<u32> {
        if let Some(&v) = self.const_body.get(&(ci, li)) {
            return Ok(v);
        }
        let Some(body) = self.const_view(ci)?.value else {
            return no();
        };
        let v = self.eval(body, 0, li)?;
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.const_body,
            (ci, li),
            v,
        )?;
        Ok(v)
    }
    pub(super) fn nat_ctors(&mut self) -> R<Option<(u32, u32, u32)>> {
        if let Some(c) = self.nat_ctors {
            return Ok(Some(c));
        }
        let env = self.env;
        let Some((nat, zero, succ)) = env.natural_constructors(
            self.before,
            self.formation,
            self.expression_end,
            self.exprs,
            self.b,
        )?
        else {
            return Ok(None);
        };
        let c = (
            self.const_info(nat)?,
            self.const_info(zero)?,
            self.const_info(succ)?,
        );
        self.nat_ctors = Some(c);
        Ok(Some(c))
    }
    pub(super) fn nat_type(&mut self) -> R<u32> {
        if self.nat_type != NONE {
            return Ok(self.nat_type);
        }
        let Some((nat, _, _)) = self.nat_ctors()? else {
            return no();
        };
        let v = self.push(Val::Const {
            ci: nat,
            li: 0,
            spine: 0,
        })?;
        self.nat_type = v;
        Ok(v)
    }
    pub(super) fn natop(&mut self, ci: u32) -> R<Option<crate::check::natural::Operation>> {
        use crate::check::natural::Operation;
        const OPS: [Operation; 12] = [
            Operation::Add,
            Operation::Mul,
            Operation::Pow,
            Operation::Sub,
            Operation::Div,
            Operation::Mod,
            Operation::Gcd,
            Operation::Land,
            Operation::Lor,
            Operation::Xor,
            Operation::ShiftLeft,
            Operation::ShiftRight,
        ];
        let info = *self.const_view(ci)?;
        if info.natop == 0 {
            let env = self.env;
            let site = ConstantUse {
                name: info.name,
                arguments: &[],
                parameters: self.params,
                before: self.before,
                formation: self.formation,
                mode: self.mode,
                expression_end: self.expression_end,
                level_end: self.level_end,
            };
            let op = if info.params.is_empty() {
                match env.natural_arithmetic_kind(&site, self.levels, self.names, self.b) {
                    Ok(op) => op,
                    Err(UseError::Resource(e)) => return Err(e.into()),
                    Err(_) => None,
                }
            } else {
                None
            };
            self.const_view_mut(ci)?.natop = match op {
                None => 1,
                Some(op) => {
                    2 + OPS
                        .iter()
                        .position(|o| *o == op)
                        .ok_or(ResourceError::Invariant)? as u8
                }
            };
        }
        let code = self.const_view(ci)?.natop;
        Ok((code >= 2).then(|| OPS[(code - 2) as usize]))
    }

    /// Certified Nat predicate (same committed authority as the existing route).
    pub(super) fn natpred(&mut self, ci: u32) -> R<Option<bool>> {
        let info = *self.const_view(ci)?;
        if info.natpred == 0 {
            let env = self.env;
            let site = ConstantUse {
                name: info.name,
                arguments: &[],
                parameters: self.params,
                before: self.before,
                formation: self.formation,
                mode: self.mode,
                expression_end: self.expression_end,
                level_end: self.level_end,
            };
            let kind = if info.params.is_empty() {
                match env.natural_predicate_kind(&site, self.levels, self.names, self.b) {
                    Ok(k) => k,
                    Err(UseError::Resource(e)) => return Err(e.into()),
                    Err(_) => None,
                }
            } else {
                None
            };
            self.const_view_mut(ci)?.natpred = match kind {
                None => 1,
                Some(true) => 2,
                Some(false) => 3,
            };
        }
        Ok(match self.const_view(ci)?.natpred {
            2 => Some(true),
            3 => Some(false),
            _ => None,
        })
    }

    // ---------- evaluation ----------
}
