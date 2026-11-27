//! Universe substitution, canonicalization and level-instance sharing.

use super::*;

impl<'e, 'w> Kernel<'e, 'w> {
    pub(super) fn subst_level(&mut self, l: LevelId, li: u32) -> R<LevelId> {
        if li == 0 || !self.levels.get(l, self.b)?.has_param() {
            return Ok(l);
        }
        if let Some(&r) = self.level_subst.get(&(l.slot(), li)) {
            return Ok(r);
        }
        let inst = self.linsts[li as usize];
        let params = self.const_view(inst.ci)?.params;
        // The instance store is immutable during substitution. Borrow this
        // disjoint field rather than copying an unbounded replacement list.
        let args = &self.linst_levels[inst.start as usize..(inst.start + inst.len) as usize];
        let names = self.names;
        let r =
            self.levels
                .with_substitution(names, self.subst_end, params, args, self.b, |s| s.apply(l))?;
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.level_subst,
            (l.slot(), li),
            r,
        )?;
        Ok(r)
    }
    /// One representative per structurally equal level: the level store gives
    /// every constructed node a fresh identity, which would otherwise split
    /// equal constant instances and sorts.
    pub(super) fn canon_level(&mut self, l: LevelId) -> R<LevelId> {
        if l == LevelId::ZERO {
            return Ok(l);
        }
        if let Some(&c) = self.canon_of.get(&l.slot()) {
            return Ok(c);
        }
        let key = match self.levels.get(l, self.b)?.kind() {
            LevelKind::Zero => return Ok(LevelId::ZERO),
            LevelKind::Succ(a) => (1u8, self.canon_level(a)?.slot(), 0),
            LevelKind::Max(a, c) => (2, self.canon_level(a)?.slot(), self.canon_level(c)?.slot()),
            LevelKind::IMax(a, c) => (3, self.canon_level(a)?.slot(), self.canon_level(c)?.slot()),
            LevelKind::Param(n) => (4, self.canon(n)?, 0),
        };
        let c = match self.level_index.get(&key) {
            Some(&c) => c,
            None => {
                map_put(self.b, &mut self.reserved, &mut self.level_index, key, l)?;
                l
            }
        };
        map_put(self.b, &mut self.reserved, &mut self.canon_of, l.slot(), c)?;
        Ok(c)
    }
    pub(super) fn succ(&mut self, l: LevelId) -> R<LevelId> {
        if let Some(&r) = self.succ_of.get(&l.slot()) {
            return Ok(r);
        }
        let r = self.levels.append(LevelKind::Succ(l), self.names, self.b)?;
        map_put(self.b, &mut self.reserved, &mut self.succ_of, l.slot(), r)?;
        Ok(r)
    }
    pub(super) fn imax(&mut self, a: LevelId, c: LevelId) -> R<LevelId> {
        let names = self.names;
        Ok(self.levels.with_helpers(names, self.b, |h| h.imax(a, c))?)
    }
    pub(super) fn level_eq(&mut self, a: LevelId, c: LevelId) -> R<bool> {
        if a == c {
            return Ok(true);
        }
        let key = if a.slot() < c.slot() {
            (a.slot(), c.slot())
        } else {
            (c.slot(), a.slot())
        };
        if let Some(&r) = self.level_eq.get(&key) {
            return Ok(r);
        }
        let names = self.names;
        let r = self
            .levels
            .with_helpers(names, self.b, |h| h.compare_universes(a, c))?
            == UniverseComparison::Equal;
        map_put(self.b, &mut self.reserved, &mut self.level_eq, key, r)?;
        Ok(r)
    }
    pub(super) fn is_zero(&mut self, l: LevelId) -> R<bool> {
        Ok(self.levels.get(l, self.b)?.zero() == LevelZero::Zero)
    }
    pub(super) fn li_levels(&self, li: u32) -> &[LevelId] {
        let inst = self.linsts[li as usize];
        &self.linst_levels[inst.start as usize..(inst.start + inst.len) as usize]
    }
    /// Cold overflow for the existing typed universe substitution. Both callers
    /// validate exact arity first. No instance is published until every level
    /// has been substituted/canonicalized and `intern_li` has completed.
    ///
    /// The local owner reserves its rounded Vec payload in the run budget,
    /// independently of persistent attempt storage. No buffer is retained;
    /// drop precedes release on success, local abort and mandatory failure.
    #[cold]
    pub(super) fn wide_instance(&mut self, ci: u32, source: &[LevelId], li: u32) -> R<u32> {
        let mut buffer = Vec::new();
        let mut reserved = 0;
        let result = (|| {
            room(self.b, &mut reserved, &mut buffer, source.len())?;
            self.steps_by(source.len() as u64)?;
            for &level in source {
                let level = self.subst_level(level, li)?;
                buffer.push(self.canon_level(level)?);
            }
            self.intern_li(ci, &buffer)
        })();
        self.finish_level_buffer(result, buffer, reserved)
    }
    /// Retire the complete temporary payload before entering recursive typing.
    fn finish_level_buffer<T>(
        &mut self,
        result: R<T>,
        buffer: Vec<LevelId>,
        reserved: u64,
    ) -> R<T> {
        drop(buffer);
        if let Err(error) = self.b.release(reserved) {
            // As with scratch_finish, preserve an existing internal operation
            // error; otherwise an internal cleanup failure dominates decline.
            let internal = matches!(result, Err(KErr::Resource(e)) if
                e.failure_report().outcome == crate::resource::failure::FailureOutcome::InternalError);
            if !internal {
                return Err(error.into());
            }
        }
        result
    }
    /// Transfer exact ordered levels to another validated constant. Short
    /// lists use bounded stack workspace; long lists retire their charged
    /// buffer here, before callers recurse through constructor/projection types.
    pub(super) fn rebind_instance(&mut self, ci: u32, li: u32) -> R<u32> {
        if li == 0 || self.linsts[li as usize].ci == ci {
            return Ok(li);
        }
        let inst = self.linsts[li as usize];
        let (start, len) = (inst.start as usize, inst.len as usize);
        if len <= LEVEL_ARGS {
            let mut buffer = [LevelId::ZERO; LEVEL_ARGS];
            buffer[..len].copy_from_slice(&self.linst_levels[start..start + len]);
            return self.intern_li(ci, &buffer[..len]);
        }
        self.rebind_wide_instance(ci, start, len)
    }
    #[cold]
    fn rebind_wide_instance(&mut self, ci: u32, start: usize, len: usize) -> R<u32> {
        let mut buffer = Vec::new();
        let mut reserved = 0;
        let result = (|| {
            room(self.b, &mut reserved, &mut buffer, len)?;
            self.steps_by(len as u64)?;
            buffer.extend_from_slice(&self.linst_levels[start..start + len]);
            self.intern_li(ci, &buffer)
        })();
        self.finish_level_buffer(result, buffer, reserved)
    }
    pub(super) fn intern_li(&mut self, ci: u32, levels: &[LevelId]) -> R<u32> {
        if levels.is_empty() {
            return Ok(0);
        }
        use std::hash::Hasher;
        let mut h = FastHasher::new();
        h.write_u32(ci);
        for l in levels {
            h.write_u32(l.slot());
        }
        let key = h.finish();
        let mut cur = self.linst_index.get(&key).copied().unwrap_or(NONE);
        let head = cur;
        while cur != NONE {
            // The caller's initial span does not bound a collision chain.
            // Charge each wide candidate before inspection/comparison; the
            // fingerprint never substitutes for completed exact equality.
            if levels.len() > LEVEL_ARGS {
                self.steps_by(levels.len() as u64)?;
            }
            let inst = self.linsts[cur as usize];
            if inst.ci == ci && self.li_levels(cur) == levels {
                return Ok(cur);
            }
            cur = inst.next;
        }
        let id = self.linsts.len() as u32;
        let start = self.linst_levels.len() as u32;
        room(
            self.b,
            &mut self.reserved,
            &mut self.linst_levels,
            levels.len(),
        )?;
        room(self.b, &mut self.reserved, &mut self.linsts, 1)?;
        self.linst_levels.extend_from_slice(levels);
        self.linsts.push(LInst {
            ci,
            start,
            len: levels.len() as u32,
            next: head,
        });
        map_put(self.b, &mut self.reserved, &mut self.linst_index, key, id)?;
        Ok(id)
    }
    /// Same constant use under two instances: equal universe arguments.
    pub(super) fn same_levels(&mut self, a: u32, c: u32) -> R<bool> {
        if a == c {
            return Ok(true);
        }
        let (la, lc) = (self.linsts[a as usize], self.linsts[c as usize]);
        if la.len != lc.len {
            return Ok(false);
        }
        if la.len as usize > LEVEL_ARGS {
            self.steps_by(u64::from(la.len))?;
        }
        for offset in 0..la.len as usize {
            // Read stable handles before the mutating universe comparison;
            // no owned copies survive that operation.
            let x = self.linst_levels[la.start as usize + offset];
            let y = self.linst_levels[lc.start as usize + offset];
            if !self.level_eq(x, y)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    // ---------- constants ----------
}
