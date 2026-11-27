//! Value graph construction, local environments and scratch storage.

use super::*;

#[derive(Clone, Copy)]
pub(super) enum NeutralHead {
    Local(u32),
    Constant(u32, u32),
}

impl<'e, 'w> Kernel<'e, 'w> {
    /// Structural key of a value form; thunks and redirections are not interned.
    fn intern_key(&self, v: &Val) -> Option<ValueKey> {
        Some(match *v {
            Val::Sort(l) => (1, l.slot(), 0, 0, 0),
            Val::Const { ci, li, spine } => (2, ci, li, spine, 0),
            Val::Local { id, spine } => (3, id, spine, 0, 0),
            Val::Proj { x, idx, sci } => (4, x, idx, sci, 0),

            Val::Arrow { dom, cod } => (8, dom, cod, 0, 0),
            Val::Str(e) => (10, e.slot(), 0, 0, 0),
            Val::Nat(n) => match self.nats[n as usize] {
                NatLit::Small(x) => (9, x as u32, (x >> 32) as u32, 0, 0),
                NatLit::Big(_) | NatLit::Computed(..) | NatLit::Evicted(_) => return None,
            },
            _ => return None,
        })
    }
    pub(super) fn push(&mut self, mut v: Val) -> R<u32> {
        if let Val::Sort(l) = v {
            v = Val::Sort(self.canon_level(l)?);
        }
        let key = self.intern_key(&v).map(|key| {
            let hash = Lossy::<(u32, u32, u32, u32, u32), u32>::key_hash(&key);
            (key, hash)
        });
        if let Some((k, hash)) = key
            && let Some(id) = self.val_index.probe_hashed(&k, hash)
        {
            return Ok(id);
        }
        self.push_fresh(v, key)
    }
    /// The caller has missed or excluded the applicable interner. A supplied
    /// key/hash is the exact pair already probed for v; None performs no value
    /// interning. Keep the single ID guard and optional publication before room.
    #[inline(always)]
    pub(super) fn push_fresh(&mut self, v: Val, key: Option<(ValueKey, usize)>) -> R<u32> {
        let n = self.vals.len();
        let id = n as u32;
        if id == NONE - 1 {
            return no();
        }
        if let Some((k, hash)) = key {
            self.val_index
                .insert_hashed(k, id, hash, self.b, &mut self.reserved)?;
        }
        // At every semantic boundary vals.len() == meta.len(): new clears both,
        // retention moves the pair without intervening semantic use, and only
        // the paired pushes below grow them. Both fallible rooms precede either
        // push, so a failed reservation/allocation leaves both lengths unchanged.
        // Arena retirement may discard capacities independently; new clears the
        // retained lengths before either vector becomes a Kernel again.
        debug_assert_eq!(n, self.meta.len());
        let ready = n != 0
            && (n < 4 || !n.is_power_of_two())
            && self.vals.capacity() > n
            && self.meta.capacity() > n;
        if !ready {
            room(self.b, &mut self.reserved, &mut self.vals, 1)?;
            room(self.b, &mut self.reserved, &mut self.meta, 1)?;
        }
        self.vals.push(v);
        self.meta.push(Meta {
            delta: NONE,
            whnf: NONE,
            core: NONE,
        });
        Ok(id)
    }
    /// Interned: equal extensions of equal environments are the same node, so
    /// memoised evaluation shares results across repeated applications.
    #[inline(always)]
    pub(super) fn env_push(&mut self, parent: u32, val: u32, ty: u32) -> R<u32> {
        let hash = Lossy::<(u32, u32, u32), u32>::key_hash(&(parent, val, ty)) as u32 & 0x3fff_ffff;
        let at = match self.env_index.probe(hash, |id| {
            let e = self.envs[id as usize];
            (e.parent, e.val, e.ty) == (parent, val, ty)
        }) {
            Probe::Found(id) => return Ok(id),
            Probe::Vacant(at) => at,
        };
        let id = u32::try_from(self.envs.len()).map_err(|_| ResourceError::Storage)?;
        room(self.b, &mut self.reserved, &mut self.envs, 1)?;
        self.env_index
            .insert(at, hash, id, self.b, &mut self.reserved)?;
        self.envs.push(EnvNode { parent, val, ty });
        Ok(id)
    }
    #[inline]
    pub(super) fn env_at(&mut self, mut env: u32, mut i: u32) -> R<EnvNode> {
        self.steps_by(u64::from(i) + 1)?;
        while i > 0 {
            if env == 0 {
                return no();
            }
            env = self.envs[env as usize].parent;
            i -= 1;
        }
        if env == 0 {
            return no();
        }
        Ok(self.envs[env as usize])
    }
    /// A key for the entries an expression with loose range `r` can read:
    /// the entry values themselves for `r <= 2`, else the environment identity.
    /// Equal keys give equal results, with no environment copied.
    #[inline]
    pub(super) fn ekey(&self, env: u32, r: u32) -> (u32, u32, u32) {
        match r {
            0 => (0, 0, 0),
            1 | 2 if env != 0 => {
                let n0 = self.envs[env as usize];
                if r == 1 {
                    (1, n0.val, 0)
                } else if n0.parent != 0 {
                    (2, n0.val, self.envs[n0.parent as usize].val)
                } else {
                    (3, env, 0)
                }
            }
            _ => (3, env, 0),
        }
    }
    /// Source and universe identity remain in the outer memo key. Bindings
    /// selected here are immutable IDs in this attempt's own value graph.
    #[inline]
    pub(super) fn source_eval_key(
        &self,
        node: Expression<'_>,
        env: u32,
        range: u32,
    ) -> (u32, u32, u32) {
        if range <= 2 || node.has_free() {
            return self.ekey(env, range);
        }
        let Some(bits) = node.binding_mask() else {
            return (3, env, 0);
        };
        if bits.count_ones() <= 2 {
            return self
                .sparse_read_key(env, u64::from(bits))
                .unwrap_or((3, env, 0));
        }
        // Every source read is at or above skip. Equal suffix IDs give the
        // same values at those positions. Mark the key to distinguish the
        // suffix from an untrimmed or representative environment ID.
        let skip = bits.trailing_zeros();
        // An interior hole needs the existing position-sensitive key: two
        // environments can differ there while agreeing on every source read.
        if skip == 0 || bits.count_ones() + skip != range {
            return (3, env, 0);
        }
        let mut suffix = env;
        for _ in 0..skip {
            if suffix == 0 {
                return (3, env, 0);
            }
            suffix = self.envs[suffix as usize].parent;
        }
        (3, suffix, skip)
    }

    /// The source fixes the read positions. A triple uses the reserved
    /// packed-source namespace; the universe instance occupies eight bits
    /// and the third graph-local value occupies the other twenty-four.
    #[inline]
    pub(super) fn source_memo_key(
        &self,
        e: ExprId,
        node: Expression<'_>,
        env: u32,
        range: u32,
        li: u32,
    ) -> MemoKey {
        if range >= 3
            && li < 256
            && !node.has_free()
            && let Some(mut bits) = node.binding_mask()
            && bits.count_ones() == 3
        {
            let mut walk = env;
            let mut values = [0; 3];
            let mut count = 0;
            while bits != 0 && walk != 0 {
                let entry = self.envs[walk as usize];
                if bits & 1 != 0 {
                    values[count] = entry.val;
                    count += 1;
                }
                bits >>= 1;
                walk = entry.parent;
            }
            if count == 3 && values[2] < (1 << 24) {
                return (e.slot(), (li << 24) | values[2], 4, values[0], values[1]);
            }
        }
        let (tag, first, second) = self.source_eval_key(node, env, range);
        (e.slot(), li, tag, first, second)
    }
    // Exact values at source-fixed positions; at most two fit the current key.
    pub(super) fn sparse_read_key(&self, mut env: u32, mut mask: u64) -> Option<(u32, u32, u32)> {
        if mask == u64::MAX || mask.count_ones() > 2 {
            return None;
        }
        let mut vals = [0; 2];
        let mut n = 0;
        while mask != 0 {
            if env == 0 {
                return None;
            }
            let e = self.envs[env as usize];
            if mask & 1 != 0 {
                vals[n] = e.val;
                n += 1;
            }
            mask >>= 1;
            env = e.parent;
        }
        Some((n as u32, vals[0], vals[1]))
    }
    /// Dependency-sensitive extension of the existing source read key. The returned
    /// environment is a real earlier environment whose values agree at every
    /// position this exact source can read. Its source/universe memo identity
    /// is unchanged. An unavailable/full table supplies no semantic fact.
    #[inline]
    pub(super) fn evaluation_read_key(
        &mut self,
        e: ExprId,
        env: u32,
        loose: u32,
        has_free: bool,
        fallback: (u32, u32, u32),
    ) -> R<(u32, u32, u32)> {
        if loose > 2
            && loose <= 63
            && let Some(&mask) = self.source_support.get(&e.slot())
        {
            if let Some(key) = self.sparse_read_key(env, mask) {
                return Ok(key);
            }
            // The finite mask tracks Bound positions only; Free can contribute
            // zero. The derived has_free flag is an independent scope premise.
            // The sixteen-read admission bound below fits the fixed key array.
            if !has_free
                && self.formation.is_none()
                && self.checked_context.is_none()
                && self.steps >= 4096
            {
                let reads = mask.count_ones();
                if mask != u64::MAX && (3..=16).contains(&reads) && mask >> loose == 0 {
                    return self.representative_read_key(env, mask, reads);
                }
            }
        }
        // Keep new mask preparation off the existing <=63-position path.
        // Both callers have already missed the exact source/env/universe key.
        if (64..=MAX_EVAL_READ_RANGE).contains(&loose)
            && !has_free
            && self.formation.is_none()
            && self.checked_context.is_none()
            && self.steps >= 4096
        {
            return self.wide_evaluation_read_key(e, env);
        }
        Ok(fallback)
    }
    // Called only after the original narrow-key path is unavailable and the
    // exact existing scope/read-mask guards hold. Keep this larger setup out
    // of that path; its fallback for loose > 2 is exactly (3, env, 0).
    pub(super) fn representative_read_key(
        &mut self,
        env: u32,
        mask: u64,
        reads: u32,
    ) -> R<(u32, u32, u32)> {
        // Charge the complete traversal and short key construction once,
        // before touching the chain, including a miss or abandoned route.
        self.steps_by(u64::from(64 - mask.leading_zeros() + reads))?;
        if let Some(representative) = self.completed_value_keys.get(env, mask) {
            return Ok((3, representative, 0));
        }
        let mut values = [0; 16];
        let mut bits = mask;
        let mut walk = env;
        let mut n = 0;
        while bits != 0 {
            if walk == 0 {
                return no();
            }
            let node = self.envs[walk as usize];
            if bits & 1 != 0 {
                values[n] = node.val;
                n += 1;
            }
            walk = node.parent;
            bits >>= 1;
        }
        let key = (mask, values);
        if let Some(&representative) = self.read_environments.get(&key) {
            self.completed_value_keys.put(env, mask, representative);
            return Ok((3, representative, 0));
        }
        if self.read_environments.len() + self.wide_read_environments.len() < 131_072 {
            self.insert_read_environment(key, env)?;
            self.completed_value_keys.put(env, mask, env);
        }
        Ok((3, env, 0))
    }
    /// The exact-table helper owns logical growth and physical rehash overlap.
    /// Required failures retain their successful reservations for cleanup.
    pub(super) fn insert_read_environment(&mut self, key: (u64, [u32; 16]), env: u32) -> R<()> {
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.read_environments,
            key,
            env,
        )
    }
    pub(super) fn push_clo(&mut self, form: u32, c: Clo, loose: u32) -> R<u32> {
        let mut read_key = self.ekey(c.env, loose);
        if loose > 2 && loose <= 63 {
            let d = self.known_support(c.dom)?;
            let b = self.known_support(c.body)?;
            if let (Some(d), Some(b)) = (d, b)
                && d != u64::MAX
                && b != u64::MAX
                && let Some(k) = self.sparse_read_key(c.env, d | (b >> 1))
            {
                read_key = k;
            }
        }
        self.intern_closure(form, c, loose, read_key)
    }

    pub(super) fn intern_closure(
        &mut self,
        form: u32,
        c: Clo,
        loose: u32,
        read_key: (u32, u32, u32),
    ) -> R<u32> {
        let (kt, k1, k2) = read_key;
        let key = (form * 4 + kt, c.dom.slot(), c.body.slot(), c.li, k1, k2);
        let hash = Lossy::<(u32, u32, u32, u32, u32, u32), u32>::key_hash(&key);
        // Unlike env_lossy/val_index/cell_index, clo_index is never reviewed:
        // its lookup/hit counts are diagnostics, not cache-policy inputs.
        // Preserve the same full-key/generation read without production counts.
        #[cfg(feature = "introspection")]
        let cached = self.clo_index.probe_hashed(&key, hash);
        #[cfg(not(feature = "introspection"))]
        let cached = self.clo_index.get_hashed(&key, hash).copied();
        if let Some(v) = cached {
            return Ok(v);
        }
        let c = if loose == 0 { Clo { env: 0, ..c } } else { c };
        // All three forms have no intern_key and cannot be Sort. clo_index
        // above owns their reuse; append without repeating generic dispatch.
        let v = self.push_fresh(
            match form {
                0 => Val::Lam(c),
                1 => Val::Pi(c),
                _ => Val::LamTy(c),
            },
            None,
        )?;
        self.clo_index
            .insert_hashed(key, v, hash, self.b, &mut self.reserved)?;
        Ok(v)
    }
    /// Standalone cell construction reuses equal triples. A terminal cell
    /// published with its head can have a different ID for the same triple.
    pub(super) fn cell(&mut self, prev: u32, item: u32, tag: u32) -> R<u32> {
        let hash = Lossy::<(u32, u32, u32), u32>::key_hash(&(prev, item, tag)) as u32 & 0x3fff_ffff
            | 0x4000_0000;
        let at = match self.env_index.probe(hash, |id| {
            let c = self.cells[id as usize];
            (c.prev, c.item, c.tag) == (prev, item, tag)
        }) {
            Probe::Found(id) => return Ok(id),
            Probe::Vacant(at) => at,
        };
        let id = u32::try_from(self.cells.len()).map_err(|_| ResourceError::Storage)?;
        let len = self.cells[prev as usize].len + 1;
        room(self.b, &mut self.reserved, &mut self.cells, 1)?;
        self.env_index
            .insert(at, hash, id, self.b, &mut self.reserved)?;
        self.cells.push(Cell {
            prev,
            item,
            tag,
            len,
        });
        Ok(id)
    }
    /// The entry owns a complete neutral value, scoped to this graph. Hash
    /// domains separate its ID from cell and environment IDs. Matching both
    /// immutable rows is sufficient for reuse even when arguments are delayed.
    pub(super) fn extend_neutral(
        &mut self,
        head: NeutralHead,
        prev: u32,
        item: u32,
        tag: u32,
    ) -> R<u32> {
        let (domain, name, levels) = match head {
            NeutralHead::Local(id) => (0x8000_0000, id, 0),
            NeutralHead::Constant(ci, li) => (0xc000_0000, ci, li),
        };
        let key = (name, levels, prev, item, tag);
        let hash = Lossy::<ValueKey, u32>::key_hash(&key) as u32 & 0x3fff_ffff | domain;
        let at = match self.env_index.probe(hash, |id| {
            let spine = match (head, self.vals[id as usize]) {
                (NeutralHead::Local(local), Val::Local { id, spine }) if id == local => spine,
                (NeutralHead::Constant(c, l), Val::Const { ci, li, spine })
                    if (ci, li) == (c, l) =>
                {
                    spine
                }
                _ => return false,
            };
            let cell = self.cells[spine as usize];
            (cell.prev, cell.item, cell.tag) == (prev, item, tag)
        }) {
            Probe::Found(id) => return Ok(id),
            Probe::Vacant(at) => at,
        };
        let spine = u32::try_from(self.cells.len()).map_err(|_| ResourceError::Storage)?;
        let len = self.cells[prev as usize].len + 1;
        room(self.b, &mut self.reserved, &mut self.cells, 1)?;
        self.cells.push(Cell {
            prev,
            item,
            tag,
            len,
        });
        let value = match head {
            NeutralHead::Local(id) => Val::Local { id, spine },
            NeutralHead::Constant(ci, li) => Val::Const { ci, li, spine },
        };
        let id = self.push_fresh(value, None)?;
        self.env_index
            .insert(at, hash, id, self.b, &mut self.reserved)?;
        Ok(id)
    }
    /// Spine cells from root to tip, in a reusable buffer.
    pub(super) fn spine_items(&mut self, s: u32) -> R<Scratch> {
        self.spine_items_from(s, 0)
    }
    /// Cells strictly after `base` up to the tip `s`, root first.
    pub(super) fn spine_items_from(&mut self, mut s: u32, base: u32) -> R<Scratch> {
        let mut out = self.scratch.pop().unwrap_or_default();
        out.clear();
        // At most the spine's length; the loop then never allocates.
        if let Err(error) = self.scratch_room(&mut out, self.cells[s as usize].len as usize) {
            return self.scratch_finish(Err(error), [out]);
        }
        while s != base && s != 0 {
            out.push(s);
            s = self.cells[s as usize].prev;
        }
        out.reverse();
        Ok(out)
    }
    /// Arguments of a projection-free spine; `None` if it contains a projection.
    pub(super) fn spine_args_opt(&mut self, s: u32) -> R<Option<Scratch>> {
        match self.spine_args(s) {
            Ok(v) => Ok(Some(v)),
            Err(KErr::Unsupported) => Ok(None),
            Err(e) => Err(e),
        }
    }
    /// The cell just below the first (root-most) projection, if any.
    pub(super) fn proj_prefix(&self, mut s: u32) -> Option<u32> {
        let mut found = None;
        while s != 0 {
            let c = self.cells[s as usize];
            if c.tag != 0 {
                found = Some(c.prev);
            }
            s = c.prev;
        }
        found
    }
    pub(super) fn spine_args(&mut self, s: u32) -> R<Scratch> {
        let mut out = self.spine_items(s)?;
        for slot in out.iter_mut() {
            let c = self.cells[*slot as usize];
            if c.tag != 0 {
                self.recycle(std::mem::take(&mut out))?;
                return no();
            }
            *slot = c.item;
        }
        Ok(out)
    }
    /// The item of an argument cell; `None` for a projection cell.
    pub(super) fn arg_item(&self, s: u32) -> Option<u32> {
        let c = self.cells[s as usize];
        (c.tag == 0).then_some(c.item)
    }
    /// Admit a buffer's new logical layout while its old layout remains owned.
    /// Reused physical capacity does not affect charges. A failed allocator
    /// reservation is undone here; every successful payload reservation stays
    /// with exactly this buffer until replacement, explicit disposal or final
    /// whole-attempt retirement.
    #[inline]
    pub(super) fn scratch_room(&mut self, v: &mut Scratch, extra: usize) -> R<()> {
        let needed = v.len().checked_add(extra).ok_or(ResourceError::Counter)?;
        if needed <= v.slots {
            return Ok(());
        }
        self.scratch_grow(v, needed)
    }
    /// Keep allocation/admission code off the already-admitted reuse path.
    /// The requested layout and all charge/cleanup ordering are unchanged.
    #[cold]
    fn scratch_grow(&mut self, v: &mut Scratch, needed: usize) -> R<()> {
        let slots = needed
            .max(8)
            .checked_next_power_of_two()
            .ok_or(ResourceError::Counter)?;
        let bytes = slots
            .checked_mul(crate::resource::charged::bytes::<u32>())
            .ok_or(ResourceError::Counter)?;
        let old = (v.slots * crate::resource::charged::bytes::<u32>()) as u64;
        charge_bytes(self.b, &mut self.reserved, bytes)?;
        if v.capacity() < slots {
            let extra = slots - v.len();
            if v.values.try_reserve_exact(extra).is_err() {
                let bytes = bytes as u64;
                let remaining = self
                    .reserved
                    .checked_sub(bytes)
                    .ok_or(ResourceError::Invariant)?;
                self.b.release(bytes)?;
                self.reserved = remaining;
                return Err(alloc_failed());
            }
        }
        let remaining = self
            .reserved
            .checked_sub(old)
            .ok_or(ResourceError::Invariant)?;
        self.b.release(old)?;
        self.reserved = remaining;
        v.slots = slots;
        Ok(())
    }
    /// Return a still-charged buffer to the pool, or free it before releasing
    /// its payload reservation. The fixed pool-container bound is in `init`.
    #[inline]
    pub(super) fn recycle(&mut self, v: Scratch) -> Result<(), ResourceError> {
        let n = self.scratch.len();
        if n < 64 && n < self.scratch.capacity() {
            self.scratch.push(v);
            return Ok(());
        }
        self.recycle_slow(v)
    }
    /// Pool growth and disposal retain their existing admission/error order;
    /// already-allocated pool slots need neither allocator nor release code.
    #[cold]
    fn recycle_slow(&mut self, v: Scratch) -> Result<(), ResourceError> {
        if self.scratch.len() < 64 && spare(&mut self.scratch, 1).is_ok() {
            self.scratch.push(v);
            return Ok(());
        }
        let bytes = (v.slots * crate::resource::charged::bytes::<u32>()) as u64;
        drop(v);
        let remaining = self
            .reserved
            .checked_sub(bytes)
            .ok_or(ResourceError::Invariant)?;
        self.b.release(bytes)?;
        self.reserved = remaining;
        Ok(())
    }
    /// Complete every disposal even after failure. An internal cleanup error
    /// dominates local/resource incompletion, while an existing internal
    /// operation error retains its original precedence.
    #[inline(always)]
    pub(super) fn scratch_finish<T, const N: usize>(
        &mut self,
        mut result: R<T>,
        buffers: [Scratch; N],
    ) -> R<T> {
        for buffer in buffers {
            if let Err(error) = self.recycle(buffer) {
                let internal = matches!(result, Err(KErr::Resource(e)) if
                    e.failure_report().outcome == crate::resource::failure::FailureOutcome::InternalError);
                if !internal {
                    result = Err(error.into());
                }
            }
        }
        result
    }
    /// Open a binder: the local for (`ty`, current binder depth), a de Bruijn
    /// level. Binders open at the same time have distinct depths, so they never
    /// share a variable; a local's type mentions only shallower locals, so
    /// equal keys denote the same context position, and every value and cache
    /// entry built under it is shared by all scopes that reach that position.
    pub(super) fn open_local(&mut self, ty: u32) -> R<u32> {
        let top = self.binders.len() as u32;
        let x = match self.local_index.get(&(ty, top)) {
            Some(&x) => x,
            None => {
                let x = self.fresh_local(ty)?;
                map_put(
                    self.b,
                    &mut self.reserved,
                    &mut self.local_index,
                    (ty, top),
                    x,
                )?;
                x
            }
        };
        // The binder stack shrinks as binders close, so it is a temporary
        // bounded by the nesting depth limit, not a charged store.
        spare(&mut self.binders, 1)?;
        self.binders.push(x);
        Ok(x)
    }
    pub(super) fn close_local(&mut self) {
        self.binders.pop();
    }
    /// The owner keeps this checked context immutable for the entire query.
    /// Types/values mention only earlier active locals; insertion follows completed
    /// evaluation, and the cache is dropped before the borrowed context can change.
    pub(super) fn checked_free(&mut self, id: u32) -> R<u32> {
        if let Some(&v) = self.free_values.get(&id) {
            return Ok(v);
        }
        let Some(context) = self.checked_context else {
            return no();
        };
        let local = context.get(id, self.b)?;
        let ty = self.eval(local.ty(), 0, 0)?;
        let value = match local.value() {
            Some(value) => self.eval(value, 0, 0)?,
            None => self.fresh_local(ty)?,
        };
        map_put(self.b, &mut self.reserved, &mut self.free_values, id, value)?;
        Ok(value)
    }

    pub(super) fn fresh_local(&mut self, ty: u32) -> R<u32> {
        let id = self.locals.len() as u32;
        room(self.b, &mut self.reserved, &mut self.locals, 1)?;
        self.locals.push(ty);
        self.push(Val::Local { id, spine: 0 })
    }
    /// Every retained Big payload comes from reserved `parse_nat` or `nat_pred` construction.
    /// Operand observations borrow this append-only store. The byte
    /// reservation remains in `self.reserved` until this attempt retires.
    pub(super) fn nat(&mut self, n: NatLit) -> R<u32> {
        let id = self.nats.len() as u32;
        room(self.b, &mut self.reserved, &mut self.nats, 1)?;
        self.nats.push(n);
        self.push(Val::Nat(id))
    }

    // ---------- levels ----------
}
