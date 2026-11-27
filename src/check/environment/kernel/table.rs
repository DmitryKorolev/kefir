//! Bounded cache operations and charged storage growth.

use super::*;

#[inline]
fn mix2(h: u64, x: u32) -> u64 {
    (h ^ u64::from(x))
        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .rotate_left(29)
}

impl LossyKey for EnvKey {
    #[inline]
    fn mix(&self) -> u64 {
        (self.parent, self.val, NONE).mix()
    }
}
impl LossyKey for (u32, u32) {
    #[inline]
    fn mix(&self) -> u64 {
        mix2(mix2(0x243f_6a88, self.0), self.1)
    }
}
impl LossyKey for (u32, u32, u32) {
    #[inline]
    fn mix(&self) -> u64 {
        mix2(mix2(mix2(0x243f_6a88, self.0), self.1), self.2)
    }
}
impl LossyKey for (u32, u32, u32, u32, u32, u32) {
    #[inline]
    fn mix(&self) -> u64 {
        let h = mix2(mix2(mix2(0x243f_6a88, self.0), self.1), self.2);
        mix2(mix2(mix2(h, self.3), self.4), self.5)
    }
}
impl LossyKey for (u32, u32, u32, u32, u32) {
    #[inline]
    fn mix(&self) -> u64 {
        let h = mix2(mix2(mix2(0x243f_6a88, self.0), self.1), self.2);
        mix2(mix2(h, self.3), self.4)
    }
}
impl<K: LossyKey, V: Copy> Default for Lossy<K, V> {
    fn default() -> Self {
        Self {
            slots: Vec::new(),
            spare: Vec::new(),
            size: 0,
            used: 0,
            lookups: 0,
            hits: 0,
            off: false,
            generation: NonZeroU32::MIN,
        }
    }
}
impl<K: LossyKey, V: Copy> Lossy<K, V>
where
    Option<(NonZeroU32, K, V)>: crate::resource::charged::Charged,
{
    // Charge the adopted packed bucket representation. Logical live slots,
    // rather than allocator slack kept across attempts, decide reservations.
    pub(super) const SLOT: usize = crate::resource::charged::bytes::<Option<(NonZeroU32, K, V)>>();
    #[inline]
    pub(super) fn index(&self, k: &K, size: usize) -> usize {
        Self::key_hash(k) & (size - 1)
    }
    #[inline]
    pub(super) fn get(&self, k: &K) -> Option<&V> {
        if self.size == 0 {
            return None;
        }
        self.get_hashed(k, Self::key_hash(k))
    }
    /// The supplied hash is exactly key_hash(k), never a masked bucket index.
    /// Complete-key comparison and the existing generation/scope guard remain
    /// mandatory; a hash alone authorizes no reuse.
    #[inline]
    pub(super) fn get_hashed(&self, k: &K, hash: usize) -> Option<&V> {
        debug_assert_eq!(hash, Self::key_hash(k));
        if self.size == 0 {
            return None;
        }
        match &self.slots[hash & (self.size - 1)] {
            Some((g, key, v)) if *g == self.generation && key == k => Some(v),
            _ => None,
        }
    }
    /// Reuse the same folded full-key hash, never an old
    /// bucket index. A later growth still masks with the new logical size.
    /// Every hit still compares the complete key in the original cache scope.
    #[inline]
    pub(super) fn key_hash(k: &K) -> usize {
        let h = k.mix();
        (h ^ (h >> 31)) as usize
    }
    #[inline]
    pub(super) fn probe_hashed(&mut self, k: &K, hash: usize) -> Option<V> {
        self.lookups += 1;
        let r = self.get_hashed(k, hash).copied();
        if r.is_some() {
            self.hits += 1;
        }
        r
    }
    /// Forget every entry and return to logical size zero, keeping capacity.
    pub(super) fn reset(&mut self) {
        self.next_generation();
        self.size = 0;
        self.used = 0;
        self.lookups = 0;
        self.hits = 0;
        self.off = false;
    }
    pub(super) fn next_generation(&mut self) {
        if let Some(next) = NonZeroU32::new(self.generation.get().wrapping_add(1)) {
            self.generation = next;
        } else {
            // Before reusing epoch one, clear every physically held bucket.
            // This is also the old generation-wrap rule; zero is never live.
            self.slots.iter_mut().for_each(|s| *s = None);
            self.spare.iter_mut().for_each(|s| *s = None);
            self.generation = NonZeroU32::MIN;
        }
    }
    /// Off after enough lookups with a hit rate below 1/50 (sticky).
    pub(super) fn review(&mut self) {
        if !self.off && self.lookups > LOSSY_REVIEW && self.hits * 50 < self.lookups {
            self.off = true;
            self.used = 0;
        }
    }
    #[inline]
    pub(super) fn contains(&self, k: &K) -> bool {
        self.get(k).is_some()
    }
    /// Optional publishers may use only vacant current-generation buckets.
    /// Placement depends on logical size, even when physical slots are reused.
    #[inline]
    pub(super) fn bucket_vacant(&self, k: &K) -> bool {
        !self.off
            && (self.size == 0
                || !matches!(self.slots[self.index(k, self.size)], Some((g, ..)) if g == self.generation))
    }
    /// Insert, growing the logical table with its storage reserved first.
    #[inline(always)]
    pub(super) fn insert(&mut self, k: K, v: V, b: &mut Budget, reserved: &mut u64) -> R<()> {
        if self.off {
            return Ok(());
        }
        let hash = Self::key_hash(&k);
        self.insert_hashed(k, v, hash, b, reserved)
    }
    /// Caller hash is for exactly k; remask after any fallible logical growth.
    #[inline(always)]
    pub(super) fn insert_hashed(
        &mut self,
        k: K,
        v: V,
        hash: usize,
        b: &mut Budget,
        reserved: &mut u64,
    ) -> R<()> {
        if self.off {
            return Ok(());
        }
        if self.size == 0 || (self.used * 4 > self.size && self.size < LOSSY_CAP) {
            self.grow_for_insert(b, reserved)?;
        }
        let g = self.generation;
        debug_assert_eq!(hash, Self::key_hash(&k));
        let i = hash & (self.size - 1);
        if !matches!(self.slots[i], Some((x, ..)) if x == g) {
            self.used += 1;
        }
        self.slots[i] = Some((g, k, v));
        Ok(())
    }
    #[cold]
    #[inline(never)]
    fn grow_for_insert(&mut self, b: &mut Budget, reserved: &mut u64) -> R<()> {
        if self.size == 0 {
            charge_bytes(b, reserved, LOSSY_START * Self::SLOT)?;
            physical(&mut self.slots, LOSSY_START)?;
            self.size = LOSSY_START;
        } else if self.used * 4 > self.size && self.size < LOSSY_CAP {
            let grown = self.size * 2;
            charge_bytes(b, reserved, (grown - self.size) * Self::SLOT)?;
            physical(&mut self.slots, grown)?;
            // Doubling the mask splits old bucket i into i or i+size. Only
            // reset changes the generation, and size never shrinks within one,
            // so no upper-half bucket holds a current row: a row whose new
            // bit is set moves up and leaves its bucket vacant, every other
            // row stays. Migration preserves exactly `used` live rows and the
            // placement a fresh insertion at the grown size would choose.
            let g = self.generation;
            let (low, high) = self.slots[..grown].split_at_mut(self.size);
            for (row, up) in low.iter_mut().zip(high.iter_mut()) {
                if let Some((entry, key, _)) = row
                    && *entry == g
                    && Self::key_hash(key) & self.size != 0
                {
                    debug_assert!(!matches!(up, Some((e, ..)) if *e == g));
                    *up = row.take();
                }
            }
            self.size = grown;
        }
        Ok(())
    }
    /// Physical capacity held for reuse.
    pub(super) fn held(&self) -> usize {
        (self.slots.capacity() + self.spare.capacity()) * Self::SLOT
    }
}

impl Resettable for Exact {
    /// Clearing only the logical prefix relies on invariants kept by
    /// construction: `size <= slots.len()`, every non-vacant slot lies in
    /// `slots[..size]`, slots beyond it stay vacant (growth initializes the new
    /// tail before cyclic migration; reset clears the old logical prefix), and
    /// `spare` holds no live entry outside a resize.
    fn reset_table(&mut self) {
        let size = self.size.min(self.slots.len());
        self.slots[..size].fill(MEMO_VACANT);
        self.size = 0;
        self.used = 0;
    }
}
impl Exact {
    pub(super) const SLOT: usize = crate::resource::charged::bytes::<MemoSlot>();
    /// Entries at which a table of `size` slots doubles: always below `size`,
    /// so a vacancy remains for migration and probing.
    #[inline]
    fn grow_at(size: usize) -> usize {
        if size >= MEMO_DENSE {
            size / 4 * 3
        } else {
            size / 2
        }
    }
    #[inline]
    pub(super) fn pack(k: &MemoKey) -> Option<[u32; 4]> {
        let (e, li, tag, k1, k2) = *k;
        // The top source bit separates ordinary and triple-binding keys. A
        // source that cannot be represented simply bypasses this optional memo.
        if e >= 1 << 31 {
            return None;
        }
        if tag == 4 {
            return Some([e | (1 << 31), li, k1, k2]);
        }
        (li < MEMO_LEVEL_INSTANCES && tag < 4).then_some([e, li | tag << 30, k1, k2])
    }
    /// For fixed tail words every step on the expression word is reversible:
    /// a fixed xor, odd multiplication, or xor with a right shift. Equality
    /// of all four stored words is therefore exactly equality of packed keys.
    /// The first word alone is only a bucket hash, including after doubling.
    #[inline]
    pub(super) fn encode([expression, instance, first, second]: [u32; 4]) -> [u32; 4] {
        let salt = Self::salt(instance, first, second);
        let x = (expression ^ salt).wrapping_mul(0x9e37_79b1);
        [x ^ (x >> 16), instance, first, second]
    }

    #[inline]
    fn salt(instance: u32, first: u32, second: u32) -> u32 {
        let bindings = (u64::from(second) << 32) | u64::from(first);
        let scope = u64::from(instance).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        let h = (bindings ^ scope).wrapping_mul(0xd6e8_feb8_6659_fd93);
        (h ^ (h >> 32)) as u32
    }

    #[inline]
    pub(super) fn home(k: &[u32; 4], size: usize) -> usize {
        k[0] as usize & (size - 1)
    }
    #[inline]
    pub(super) fn get(&self, k: &MemoKey) -> Option<u32> {
        self.probe(k).0
    }
    #[inline]
    pub(super) fn probe(&self, k: &MemoKey) -> (Option<u32>, Option<MemoVacancy>) {
        if self.size == 0 {
            return (None, None);
        }
        let Some(k) = Self::pack(k) else {
            return (None, None);
        };
        let k = Self::encode(k);
        let mask = self.size - 1;
        let mut i = Self::home(&k, self.size);
        loop {
            let s = self.slots[i];
            if s.val == NONE {
                return (
                    None,
                    Some(MemoVacancy {
                        size: self.size,
                        index: i,
                        key: k,
                    }),
                );
            }
            if s.key == k {
                return (Some(s.val), None);
            }
            i = (i + 1) & mask;
        }
    }
    /// Reuse the vacant slot from this key's probe in the current attempt.
    /// Entries are never removed or moved without a resize during an attempt.
    /// A filled vacancy or a resize therefore needs the ordinary insertion.
    pub(super) fn insert_probed(
        &mut self,
        k: MemoKey,
        v: u32,
        vacancy: Option<MemoVacancy>,
        b: &mut Budget,
        reserved: &mut u64,
    ) -> R<()> {
        if let Some(vacancy) = vacancy
            && vacancy.size == self.size
            && self.used < Self::grow_at(self.size)
            && self.slots[vacancy.index].val == NONE
        {
            debug_assert_eq!(Some(vacancy.key), Self::pack(&k).map(Self::encode));
            if v == NONE {
                return Err(KErr::Resource(ResourceError::Invariant));
            }
            self.slots[vacancy.index] = MemoSlot {
                key: vacancy.key,
                val: v,
            };
            self.used += 1;
            Ok(())
        } else {
            self.insert(k, v, b, reserved)
        }
    }
    pub(super) fn insert(
        &mut self,
        k: MemoKey,
        v: u32,
        b: &mut Budget,
        reserved: &mut u64,
    ) -> R<()> {
        if v == NONE {
            return Err(KErr::Resource(ResourceError::Invariant));
        }
        let Some(k) = Self::pack(&k).map(Self::encode) else {
            return Ok(());
        };
        if self.size == 0 {
            charge_bytes(b, reserved, LOSSY_START * Self::SLOT)?;
            vacant_slots(&mut self.slots, LOSSY_START)?;
            self.size = LOSSY_START;
        } else if self.used >= Self::grow_at(self.size) {
            let grown = self.size.checked_mul(2).ok_or(ResourceError::Counter)?;
            let new_bytes = grown
                .checked_mul(Self::SLOT)
                .ok_or(ResourceError::Counter)?;
            let old_bytes = self
                .size
                .checked_mul(Self::SLOT)
                .ok_or(ResourceError::Counter)?;
            // The old logical buffer stays charged while physical backing
            // grows and entries migrate. A failed allocation leaves the
            // successful reservation with the attempt owner for retirement.
            charge_bytes(b, reserved, new_bytes)?;
            // Physical growth only. Logical admission reserves both
            // buffers above and retires the old logical charge below,
            // independent of allocator reuse.
            let old_size = self.size;
            let vacant = self.slots[..old_size]
                .iter()
                .position(|s| s.val == NONE)
                .ok_or(ResourceError::Invariant)?;
            vacant_slots(&mut self.slots, grown)?;
            // Start after an original vacancy and visit each old bucket once.
            // Each old cluster is visited from its home side. Reinserted entries
            // occupy an already-visited cyclic rank in either half. The two
            // cuts (vacant and vacant + old_size) stay empty: a home rank is
            // at most its original slot rank, so reinsertion stops by that rank
            // in its half. Later clearing cannot open a completed probe path.
            // Growth below full load guarantees an original vacancy and termination.
            let first = (vacant + 1) & (old_size - 1);
            for range in [first..old_size, 0..first] {
                for at in range {
                    let s = self.slots[at];
                    if s.val != NONE {
                        self.slots[at].val = NONE;
                        let mut i = Self::home(&s.key, grown);
                        while self.slots[i].val != NONE {
                            i = (i + 1) & (grown - 1);
                        }
                        self.slots[i] = s;
                    }
                }
            }
            self.size = grown;
            let old_bytes = u64::try_from(old_bytes).map_err(|_| ResourceError::Counter)?;
            let remaining = reserved
                .checked_sub(old_bytes)
                .ok_or(ResourceError::Invariant)?;
            b.release(old_bytes)?;
            *reserved = remaining;
        }
        let mask = self.size - 1;
        let mut i = Self::home(&k, self.size);
        loop {
            let s = &mut self.slots[i];
            if s.val == NONE {
                *s = MemoSlot { key: k, val: v };
                self.used += 1;
                return Ok(());
            }
            if s.key == k {
                s.val = v;
                return Ok(());
            }
            i = (i + 1) & mask;
        }
    }
    pub(super) fn held(&self) -> usize {
        (self.slots.capacity() + self.spare.capacity()) * Self::SLOT
    }
}
/// At least `n` vacant memo slots (fallible); existing slots keep their
/// contents.
fn vacant_slots(v: &mut Vec<MemoSlot>, n: usize) -> R<()> {
    if v.len() < n {
        v.try_reserve_exact(n - v.len())
            .map_err(|_| alloc_failed())?;
        v.resize(n, MEMO_VACANT);
    }
    Ok(())
}
/// At least `n` physical slots (fallible); new slots are vacant.
pub(super) fn physical<T: Copy>(v: &mut Vec<Option<T>>, n: usize) -> R<()> {
    if v.len() < n {
        v.try_reserve_exact(n - v.len())
            .map_err(|_| alloc_failed())?;
        v.resize(n, None);
    }
    Ok(())
}

pub(super) fn alloc_failed() -> KErr {
    KErr::Resource(ResourceError::Allocation)
}
/// Reserve `bytes` of storage before the allocator is entered.
pub(super) fn charge_bytes(b: &mut Budget, reserved: &mut u64, bytes: usize) -> R<()> {
    let bytes = u64::try_from(bytes).map_err(|_| KErr::Resource(ResourceError::Counter))?;
    b.reserve(bytes)?;
    *reserved += bytes;
    Ok(())
}
/// Logical capacity of a store holding `n` elements.
pub(super) fn logical(n: usize) -> usize {
    n.max(4).next_power_of_two()
}
/// Room for `extra` more elements of a long-lived store. Charges follow the
/// logical capacity, which depends only on this attempt's length: storage is
/// reserved whenever it doubles, before any fallible reallocation. Capacity
/// kept from earlier attempts is reused. Copying on growth is not charged as
/// work: it is bounded by twice the reserved storage.
#[inline]
pub(super) fn room<T: crate::resource::charged::Charged>(
    b: &mut Budget,
    reserved: &mut u64,
    v: &mut Vec<T>,
    extra: usize,
) -> R<()> {
    let n = v.len();
    // Only an empty store or a power-of-two length can cross a logical step.
    if extra == 1 && n != 0 && (n < 4 || !n.is_power_of_two()) && v.capacity() > n {
        return Ok(());
    }
    room_slow(b, reserved, v, extra)
}
#[cold]
fn room_slow<T: crate::resource::charged::Charged>(
    b: &mut Budget,
    reserved: &mut u64,
    v: &mut Vec<T>,
    extra: usize,
) -> R<()> {
    let (now, next) = (logical(v.len()), logical(v.len() + extra));
    if next > now || v.is_empty() {
        let from = if v.is_empty() { 0 } else { now };
        charge_bytes(
            b,
            reserved,
            (next - from) * crate::resource::charged::bytes::<T>(),
        )?;
    }
    if v.capacity() - v.len() < extra {
        v.try_reserve_exact(next - v.len())
            .map_err(|_| alloc_failed())?;
    }
    Ok(())
}
/// Fallible physical growth with no storage reservation of its own. The caller
/// must supply the owner's charge or an explicit fixed bound. In particular,
/// a bound on one spine does not bound nested buffers: all pooled u32 traversal
/// buffers use `scratch_room` instead of this helper.
pub(super) fn spare<T>(v: &mut Vec<T>, extra: usize) -> R<()> {
    if v.capacity() - v.len() >= extra {
        return Ok(());
    }
    let want = (v.len() + extra).max(v.capacity() * 2).max(8);
    v.try_reserve_exact(want - v.len())
        .map_err(|_| alloc_failed())
}
/// A fallible copy of a short slice (level instances, literal digits).
pub(super) fn copied<T: Copy>(s: &[T]) -> R<Vec<T>> {
    let mut v = Vec::new();
    spare(&mut v, s.len())?;
    v.extend_from_slice(s);
    Ok(v)
}
/// Bytes charged for a hash table able to hold `capacity` entries (at most
/// two buckets per entry, one control byte each, plus a group of slack).
pub(super) fn map_bytes<K, V>(capacity: usize) -> usize
where
    (K, V): crate::resource::charged::Charged,
{
    2 * capacity * (crate::resource::charged::bytes::<(K, V)>() + 1) + 16
}
/// Insert into an exact table, growing it fallibly with storage reserved first.
pub(super) fn map_put<K: std::hash::Hash + Eq, V>(
    b: &mut Budget,
    reserved: &mut u64,
    m: &mut Map<K, V>,
    k: K,
    v: V,
) -> R<()>
where
    (K, V): crate::resource::charged::Charged,
{
    let n = m.len();
    if n != 0 && (n < 4 || !n.is_power_of_two()) && n < m.capacity() {
        m.insert(k, v);
        return Ok(());
    }
    // Replacing an existing inline value creates no slot: neither logical
    // storage nor physical capacity grows, even at an admission checkpoint.
    if n != 0
        && let Some(old) = m.get_mut(&k)
    {
        *old = v;
        return Ok(());
    }
    // A nonempty physical rehash owns old and replacement buffers together,
    // even when logical capacity is unchanged (for example, at length seven).
    // Reuse the existing coarse replacement bound; failed admission/allocation
    // leaves every successful reservation with the attempt's cleanup owner.
    let overlap = if n != 0 && n == m.capacity() {
        map_bytes::<K, V>(logical(n + 1))
    } else {
        0
    };
    if overlap != 0 {
        charge_bytes(b, reserved, overlap)?;
    }
    // Charged by logical capacity, as `room` does.
    let (now, next) = (logical(m.len()), logical(m.len() + 1));
    if next > now || m.is_empty() {
        let from = if m.is_empty() {
            0
        } else {
            map_bytes::<K, V>(now)
        };
        charge_bytes(b, reserved, map_bytes::<K, V>(next) - from)?;
    }
    if m.len() == m.capacity() {
        m.try_reserve(next - m.len()).map_err(|_| alloc_failed())?;
    }
    m.insert(k, v);
    if overlap != 0 {
        let remaining = reserved
            .checked_sub(overlap as u64)
            .ok_or(ResourceError::Invariant)?;
        b.release(overlap as u64)?;
        *reserved = remaining;
    }
    Ok(())
}
