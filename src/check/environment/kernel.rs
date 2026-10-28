//! Positive-only value kernel, with bounded retention.
//!
//! Checks one ordinary declaration on closure/environment values. The result
//! is positive-only: `Ok(true)` means the declaration's type is a sort (a
//! proposition for theorems) and its value has that type; `Ok(false)` means
//! this route proved nothing, and the caller runs the existing checker on the
//! unchanged declaration. No path here rejects. A mandatory budget error is
//! returned as `Err` and stays terminal.
//!
//! Scope: exact graph/source/environment/universe identities in one attempt,
//! or the same State's completed retained graph. Borrowed views
//! and failed/speculative receipts never cross attempts. Formation, checked
//! contexts and quotient retries cannot reuse retained facts. Original syntax
//! is immutable; copied generated levels replay exact slots only at a matching
//! source frontier. No generated expression syntax is published.
//! Value identity implies equal denotation: values are immutable apart from a
//! thunk's redirection to its own value. Binder locals are canonical by
//! (type value, binder depth); binders open together have distinct depths, so
//! every cache keyed by value ids is sound for that exact graph (,
//! invariants). Universe substitution creates level nodes in the session's
//! level store, which the enclosing declaration session rolls back.
use super::constant_use::{ConstantUse, UseError};
use super::{
    Environment, Formation, NullaryRule, QuotientRole, SignatureKind, StoredKind, TypeSource,
};
use crate::check::environment::normalization::{Mode, Scope};
use crate::decode::primitive_decode::declarations::{Hint, Kind, Request, Safety};
use crate::resource::{Budget, ResourceError};
use crate::syntax::expressions::{ExprId, ExprKind, Expression, Expressions};
use crate::syntax::hash::FastHasher;
use crate::syntax::levels::{
    LevelId, LevelKind, LevelNames, LevelZero, Levels, NameId, UniverseComparison,
};
use crate::syntax::local_context::LocalContext;
use crate::syntax::names::Names;
use std::collections::HashMap;
use std::hash::BuildHasherDefault;
use std::mem::size_of;
use std::num::NonZeroU32;

mod derived;
mod read_large;
mod retention;
pub(super) use retention::{Retention, select_cleanup};
mod scratch;
use scratch::Scratch;

type Map<K, V> = HashMap<K, V, BuildHasherDefault<FastHasher>>;
type ValueKey = (u32, u32, u32, u32, u32);

/// A bounded, lossy direct-mapped cache. Every use is an optimisation: a
/// miss or an overwritten entry only loses sharing, never a conclusion, so a
/// table never rehashes beyond its cap and its memory stays bounded.
///
/// A cold table starts at `LOSSY_START`; a restored table keeps its
/// charged logical size and scoped entries. It doubles under load; only that size decides placement, growth and
/// charges, so behaviour never depends on capacity kept from an earlier
/// attempt. Physical slots are reused when they exist.
struct Lossy<K, V> {
    slots: Vec<Option<(NonZeroU32, K, V)>>,
    /// Empty compatibility buffer: keep the existing owner layout and charge.
    /// In-place growth uses only `slots`; wrap and held-capacity checks cover both.
    spare: Vec<Option<(NonZeroU32, K, V)>>,
    /// Logical size: zero (nothing inserted yet) or a power of two.
    size: usize,
    used: usize,
    lookups: u64,
    hits: u64,
    off: bool,
    /// Entries from earlier generations are vacant: O(1) reset.
    // Zero belongs exclusively to Option::None; live epochs are nonzero.
    generation: NonZeroU32,
}
const LOSSY_START: usize = 1 << 4;
/// Bytes of one store kept for reuse between attempts (uncharged).
const RETAIN: usize = 1 << 18;
/// Lossy tables stop doubling at this many slots; a full table evicts.
const LOSSY_CAP: usize = 1 << 19;
/// From this logical size the exact memo doubles at three-quarter load
/// instead of half load.
const MEMO_DENSE: usize = 1 << 21;
trait Resettable {
    fn reset_table(&mut self);
}
impl<K: LossyKey, V: Copy> Resettable for Lossy<K, V> {
    fn reset_table(&mut self) {
        self.reset();
    }
}
/// Keys of lossy tables: small tuples of u32, hashed by one multiply chain.
trait LossyKey: Copy + Eq {
    fn mix(&self) -> u64;
}
#[inline]
fn mix2(h: u64, x: u32) -> u64 {
    (h ^ u64::from(x))
        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .rotate_left(29)
}
// Only the untyped env_lossy branch owns this key: its omitted ty is NONE.
// Equality therefore matches the legacy (parent, val, NONE) domain exactly.
// Keep the third hash word so placement and growth winners remain unchanged.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct EnvKey {
    parent: u32,
    val: u32,
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
impl<K: LossyKey, V: Copy> Lossy<K, V> {
    // Charge the adopted packed bucket representation. Logical live slots,
    // rather than allocator slack kept across attempts, decide reservations.
    const SLOT: usize = size_of::<Option<(NonZeroU32, K, V)>>();
    #[inline]
    fn index(&self, k: &K, size: usize) -> usize {
        Self::key_hash(k) & (size - 1)
    }
    #[inline]
    fn get(&self, k: &K) -> Option<&V> {
        if self.size == 0 {
            return None;
        }
        self.get_hashed(k, Self::key_hash(k))
    }
    /// The supplied hash is exactly key_hash(k), never a masked bucket index.
    /// Complete-key comparison and the existing generation/scope guard remain
    /// mandatory; a hash alone authorizes no reuse.
    #[inline]
    fn get_hashed(&self, k: &K, hash: usize) -> Option<&V> {
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
    fn key_hash(k: &K) -> usize {
        let h = k.mix();
        (h ^ (h >> 31)) as usize
    }
    #[inline]
    fn probe_hashed(&mut self, k: &K, hash: usize) -> Option<V> {
        self.lookups += 1;
        let r = self.get_hashed(k, hash).copied();
        if r.is_some() {
            self.hits += 1;
        }
        r
    }
    /// Forget every entry and return to logical size zero, keeping capacity.
    fn reset(&mut self) {
        self.next_generation();
        self.size = 0;
        self.used = 0;
        self.lookups = 0;
        self.hits = 0;
        self.off = false;
    }
    fn next_generation(&mut self) {
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
    fn review(&mut self) {
        if !self.off && self.lookups > LOSSY_REVIEW && self.hits * 50 < self.lookups {
            self.off = true;
            self.used = 0;
        }
    }
    #[inline]
    fn contains(&self, k: &K) -> bool {
        self.get(k).is_some()
    }
    /// Optional publishers may use only vacant current-generation buckets.
    /// Placement depends on logical size, even when physical slots are reused.
    #[inline]
    fn bucket_vacant(&self, k: &K) -> bool {
        !self.off
            && (self.size == 0
                || !matches!(self.slots[self.index(k, self.size)], Some((g, ..)) if g == self.generation))
    }
    /// Insert, growing the logical table with its storage reserved first.
    #[inline(always)]
    fn insert(&mut self, k: K, v: V, b: &mut Budget, reserved: &mut u64) -> R<()> {
        if self.off {
            return Ok(());
        }
        let hash = Self::key_hash(&k);
        self.insert_hashed(k, v, hash, b, reserved)
    }
    /// Caller hash is for exactly k; remask after any fallible logical growth.
    #[inline(always)]
    fn insert_hashed(
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
    fn held(&self) -> usize {
        (self.slots.capacity() + self.spare.capacity()) * Self::SLOT
    }
}
/// An exact open-addressing table (linear probing) for the evaluation memo:
/// call-by-need sharing must never be lost, or a DAG-shaped term re-evaluates
/// shared subterms (measured: shared-subterm 13× with a lossy memo). It grows
/// at half load, or three-quarter load from `MEMO_DENSE` slots, under the
/// attempt storage budget; charges follow the logical size only. Resize
/// reserves both logical buffers before allocation and retires the old logical
/// charge only after in-place migration. No incomplete insertion supplies an
/// evaluation result.
///
/// A slot packs the key and value into five words (dense-entry
/// trial): expression slot, level instance with the read-key tag in its two
/// high bits, the two read-key words, and the value. `NONE` in the value word
/// marks a vacant slot. A key whose level instance needs more than 30 bits is
/// never stored or found: the memo only shares, so skipping it loses no
/// conclusion. Reset clears the finished attempt's logical table.
#[derive(Default)]
struct Exact {
    slots: Vec<MemoSlot>,
    spare: Vec<MemoSlot>,
    size: usize,
    used: usize,
}
/// Evaluation memo key: expression slot, level instance, read-key tag and
/// two read-key words.
type MemoKey = (u32, u32, u32, u32, u32);
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct MemoSlot {
    key: [u32; 4],
    val: u32,
}
const MEMO_VACANT: MemoSlot = MemoSlot {
    key: [0; 4],
    val: NONE,
};
/// Level instances below this bound leave two bits for the read-key tag.
const MEMO_LEVEL_INSTANCES: u32 = 1 << 30;
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
    const SLOT: usize = size_of::<MemoSlot>();
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
    fn pack(k: &MemoKey) -> Option<[u32; 4]> {
        let (e, li, tag, k1, k2) = *k;
        (li < MEMO_LEVEL_INSTANCES && tag < 4).then_some([e, li | tag << 30, k1, k2])
    }
    #[inline]
    fn home(k: &[u32; 4], size: usize) -> usize {
        let h = mix2(mix2(mix2(mix2(0x243f_6a88, k[0]), k[1]), k[2]), k[3]);
        ((h ^ (h >> 31)) as usize) & (size - 1)
    }
    #[inline]
    fn get(&self, k: &MemoKey) -> Option<u32> {
        if self.size == 0 {
            return None;
        }
        let k = Self::pack(k)?;
        let mask = self.size - 1;
        let mut i = Self::home(&k, self.size);
        loop {
            let s = self.slots[i];
            if s.val == NONE {
                return None;
            }
            if s.key == k {
                return Some(s.val);
            }
            i = (i + 1) & mask;
        }
    }
    fn insert(&mut self, k: MemoKey, v: u32, b: &mut Budget, reserved: &mut u64) -> R<()> {
        if v == NONE {
            return Err(KErr::Resource(ResourceError::Invariant));
        }
        let Some(k) = Self::pack(&k) else {
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
    fn held(&self) -> usize {
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
fn physical<T: Copy>(v: &mut Vec<Option<T>>, n: usize) -> R<()> {
    if v.len() < n {
        v.try_reserve_exact(n - v.len())
            .map_err(|_| alloc_failed())?;
        v.resize(n, None);
    }
    Ok(())
}

fn alloc_failed() -> KErr {
    KErr::Resource(ResourceError::Allocation)
}
/// Reserve `bytes` of storage before the allocator is entered.
fn charge_bytes(b: &mut Budget, reserved: &mut u64, bytes: usize) -> R<()> {
    let bytes = u64::try_from(bytes).map_err(|_| KErr::Resource(ResourceError::Counter))?;
    b.reserve(bytes)?;
    *reserved += bytes;
    Ok(())
}
/// Logical capacity of a store holding `n` elements.
fn logical(n: usize) -> usize {
    n.max(4).next_power_of_two()
}
/// Room for `extra` more elements of a long-lived store. Charges follow the
/// logical capacity, which depends only on this attempt's length: storage is
/// reserved whenever it doubles, before any fallible reallocation. Capacity
/// kept from earlier attempts is reused. Copying on growth is not charged as
/// work: it is bounded by twice the reserved storage.
#[inline]
fn room<T>(b: &mut Budget, reserved: &mut u64, v: &mut Vec<T>, extra: usize) -> R<()> {
    let n = v.len();
    // Only an empty store or a power-of-two length can cross a logical step.
    if extra == 1 && n != 0 && (n < 4 || !n.is_power_of_two()) && v.capacity() > n {
        return Ok(());
    }
    room_slow(b, reserved, v, extra)
}
#[cold]
fn room_slow<T>(b: &mut Budget, reserved: &mut u64, v: &mut Vec<T>, extra: usize) -> R<()> {
    let (now, next) = (logical(v.len()), logical(v.len() + extra));
    if next > now || v.is_empty() {
        let from = if v.is_empty() { 0 } else { now };
        charge_bytes(b, reserved, (next - from) * size_of::<T>())?;
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
fn spare<T>(v: &mut Vec<T>, extra: usize) -> R<()> {
    if v.capacity() - v.len() >= extra {
        return Ok(());
    }
    let want = (v.len() + extra).max(v.capacity() * 2).max(8);
    v.try_reserve_exact(want - v.len())
        .map_err(|_| alloc_failed())
}
/// A fallible copy of a short slice (level instances, literal digits).
fn copied<T: Copy>(s: &[T]) -> R<Vec<T>> {
    let mut v = Vec::new();
    spare(&mut v, s.len())?;
    v.extend_from_slice(s);
    Ok(v)
}
/// Bytes charged for a hash table able to hold `capacity` entries (at most
/// two buckets per entry, one control byte each, plus a group of slack).
fn map_bytes<K, V>(capacity: usize) -> usize {
    2 * capacity * (size_of::<(K, V)>() + 1) + 16
}
/// Insert into an exact table, growing it fallibly with storage reserved first.
fn map_put<K: std::hash::Hash + Eq, V>(
    b: &mut Budget,
    reserved: &mut u64,
    m: &mut Map<K, V>,
    k: K,
    v: V,
) -> R<()> {
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

const NONE: u32 = u32::MAX;
/// Stack capacity, not a semantic arity bound. Wider instances must not
/// introduce uncharged list copies or buffers spanning recursive inference.
const LEVEL_ARGS: usize = 16;
/// Optional attempt limits: exceeding either ends this attempt only.
const MAX_DEPTH: u32 = 400_000;
/// Stack reserved for the checking thread (`Run::check`).
pub(crate) const CHECK_STACK: usize = 2 << 30;
/// Stack the kernel may use below its thread's base before an attempt ends:
/// the reservation less a margin for the frames between checks.
const STACK_BUDGET: usize = CHECK_STACK - (64 << 20);
thread_local! {
    /// Approximate base of the checking thread's stack (0 when unknown).
    static STACK_BASE: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
/// Record the current frame as the checking thread's stack base.
pub(crate) fn mark_stack_base() {
    let probe = 0u8;
    STACK_BASE.with(|c| c.set(std::ptr::addr_of!(probe) as usize));
}
/// Steps one value attempt may take. An abandoned attempt is paid in full
/// before the ordinary route starts, so this bounds the work it can waste; it
/// sits well above the largest completed attempt measured.
const MAX_STEPS: u64 = 1 << 28;
#[inline(always)]
fn step_cap() -> u64 {
    MAX_STEPS
}
/// Work is charged to the mandatory budget in blocks of this many steps.
const CHARGE_BLOCK: u64 = 4096;
/// Step allowance for trying a shared head's arguments before unfolding it.
const ARGS_BUDGET: u64 = 1 << 14;
/// Allowance for reducing a let-bound operand to a literal before `lazy_delta`
/// folds it. A value that needs more is left to delta unfolding,
/// as Lean leaves a let-bound free variable unfolded there.
const LET_FOLD_BUDGET: u64 = 1 << 14;
/// Step allowance for one support walk while computing an absent mask.
const MASK_BUDGET: u64 = 256;
/// Spines of at most this many arguments are compared from stack arrays.
const SMALL_SPINE: usize = 8;
/// Lookups before a lossy table may switch itself off for a low hit rate.
const LOSSY_REVIEW: u64 = 1 << 14;
/// Syntax probes must not rescan long suffixes before ordinary conversion.
const SYN_BUDGET: u64 = 64;
/// Amortize optional context analysis only after an attempt has done real work.
const ALPHA_MIN_STEPS: u64 = 4096;
/// Local ids at and above this are syntactic-comparison placeholders.
const MARKER_BASE: u32 = 0xF000_0000;

#[derive(Clone, Copy, Debug)]
pub(crate) enum KErr {
    Unsupported,
    /// Exhaustion detected at an existing global step guard.
    StepLimit,
    LiteralArithmetic,
    /// A bounded optional sub-attempt ran out of its step allowance.
    Abort,
    Resource(ResourceError),
}
impl From<ResourceError> for KErr {
    fn from(e: ResourceError) -> Self {
        Self::Resource(e)
    }
}
impl From<UseError> for KErr {
    fn from(e: UseError) -> Self {
        match e {
            UseError::Resource(e) => Self::Resource(e),
            UseError::LiteralArithmetic => Self::LiteralArithmetic,
            _ => Self::Unsupported,
        }
    }
}
type R<T> = Result<T, KErr>;
#[cfg_attr(feature = "introspection", track_caller)]
fn no<T>() -> R<T> {
    #[cfg(feature = "introspection")]
    {
        let here = std::panic::Location::caller();
        probe::SITE.with(|c| c.set(Some(here)));
    }
    Err(KErr::Unsupported)
}

/// Attribute exhaustion to its detection site. The coarse guard preserves its
/// old `no` attribution; manual guards now report their own site instead of stale state.
#[cfg_attr(feature = "introspection", track_caller)]
fn step_limit<T>() -> R<T> {
    #[cfg(feature = "introspection")]
    {
        let here = std::panic::Location::caller();
        probe::SITE.with(|c| c.set(Some(here)));
    }
    Err(KErr::StepLimit)
}

/// Attempt diagnostics (introspection builds only, `KEFIR_KERNEL_TRACE`).
/// Everything here only reads counters the kernel already keeps: it forces no
/// value, renders no name and charges nothing, so it cannot change a step
/// count, budget charge or outcome.
#[cfg(feature = "introspection")]
mod probe {
    use std::cell::Cell;
    use std::panic::Location;
    thread_local! {
        /// The most recent incomplete-route site in this attempt. Caught
        /// sub-attempts can leave a stale site when the escaping error did
        /// not come from `no()` (e.g. a converted use error).
        pub(super) static SITE: Cell<Option<&'static Location<'static>>> =
            const { Cell::new(None) };
        static ATTEMPT: Cell<u64> = const { Cell::new(0) };
        // Fixed aggregates only. Abandoned spans overlap when probes nest;
        // root spans are separately reported, never summed as exclusive work.
        static RECURSOR: Cell<[u64; 6]> = const { Cell::new([0; 6]) };
        static RECURSOR_DEPTH: Cell<u32> = const { Cell::new(0) };
    }
    pub(super) fn recursor_begin() -> bool {
        RECURSOR.with(|c| {
            let mut counts = c.get();
            counts[0] = counts[0].saturating_add(1);
            c.set(counts);
        });
        RECURSOR_DEPTH.with(|c| {
            let old = c.get();
            c.set(old.saturating_add(1));
            old == 0
        })
    }
    pub(super) fn recursor_end(result: &super::R<bool>, steps: u64, root: bool) {
        RECURSOR_DEPTH.with(|c| c.set(c.get().saturating_sub(1)));
        RECURSOR.with(|c| {
            let mut counts = c.get();
            let slot = match result {
                Ok(true) => 1,
                Ok(false) => {
                    counts[3] = counts[3].saturating_add(steps);
                    if root {
                        counts[4] = counts[4].saturating_add(steps);
                    }
                    2
                }
                Err(_) => 5,
            };
            counts[slot] = counts[slot].saturating_add(1);
            c.set(counts);
        });
    }
    pub(super) fn report(
        name: u32,
        result: &super::R<()>,
        steps: u64,
        tables: [(&str, u64, u64, bool); 4],
    ) {
        let site = SITE.with(|c| c.take());
        let recursor = RECURSOR.with(|c| c.replace([0; 6]));
        let n = ATTEMPT.with(|c| {
            c.set(c.get() + 1);
            c.get()
        });
        if std::env::var_os("KEFIR_KERNEL_TRACE").is_none() {
            return;
        }
        let at = site.map_or(0, |l| l.line());
        let ok = result.is_ok();
        let error = result.as_ref().err();
        eprintln!(
            "KERNEL attempt={n} name={name} ok={ok} steps={steps} error={error:?} fallback_line={at}"
        );
        for (t, lookups, hits, off) in tables {
            eprintln!("KERNEL   table={t} lookups={lookups} hits={hits} off={off}");
        }
        let [
            admissions,
            positive,
            abandoned,
            abandoned_steps,
            root_abandoned_steps,
            terminal,
        ] = recursor;
        eprintln!(
            "KERNEL   recursor admissions={admissions} positive={positive} abandoned={abandoned} abandoned_steps_inclusive={abandoned_steps} root_abandoned_steps={root_abandoned_steps} terminal={terminal}"
        );
    }
}

type AlphaKey = (u32, u32, u32, [u32; 8], [u32; 8]);

/// A syntax body evaluated in an environment under a level instance.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Clo {
    dom: ExprId,
    body: ExprId,
    env: u32,
    li: u32,
}

/// Per-value caches: weak head normal form, its delta-free form, and type.
#[derive(Clone, Copy)]
struct Meta {
    // Successfully completed lazy-delta reduction, for this exact value ID.
    // Scope: this exact graph/source eligible monotone
    // frontier, or one attempt otherwise. Values fix constant/universe/spine;
    // local IDs have permanent types. Forcing preserves meaning. Only completed
    // observations survive capture. Capacity-only Arena reuse clears contents.
    delta: u32,
    whnf: u32,
    core: u32,
    ty: u32,
}

#[derive(Clone, Copy)]
enum Val {
    /// Unforced thunk.
    Delayed {
        e: ExprId,
        env: u32,
        li: u32,
    },
    /// Forced thunk: same meaning as the target value.
    Ind(u32),
    Sort(LevelId),
    Lam(Clo),
    Pi(Clo),
    /// The type of a lambda: `Π x : dom, typeof(body)` in the closure.
    LamTy(Clo),
    /// A non-dependent function type with evaluated domain and codomain.
    Arrow {
        dom: u32,
        cod: u32,
    },
    /// A projection whose structure has not been reduced yet.
    Proj {
        x: u32,
        idx: u32,
        sci: u32,
    },
    Local {
        id: u32,
        spine: u32,
    },
    Const {
        ci: u32,
        li: u32,
        spine: u32,
    },
    Nat(u32),
    /// A string literal (its original expression); expanded on demand.
    Str(ExprId),
}

/// Persistent spine cell; `tag == 0` is an argument, otherwise projection of
/// field `tag - 1` of structure constant `item`.
#[derive(Clone, Copy)]
struct Cell {
    prev: u32,
    item: u32,
    tag: u32,
    len: u32,
}

/// Construction invariant: ID zero is the initialized empty environment. Every
/// nonzero ID names an already appended node whose parent precedes it.
/// Retention moves IDs with their owning graph, and arena reset clears
/// every ID-bearing value and index before the graph is reused.
#[derive(Clone, Copy)]
struct EnvNode {
    parent: u32,
    val: u32,
    ty: u32,
}

#[derive(Clone, Copy)]
struct Rec<'e> {
    family: u32,
    k: bool,
    /// Validated nonrecursive, zero-index, single-constructor family.
    eta: bool,
    common: u32,
    cparams: u32,
    nidx: u32,
    rules: &'e [NullaryRule],
}
#[derive(Clone, Copy)]
struct Ind<'e> {
    nparams: u32,
    nidx: u32,
    nonrecursive: bool,
    ctors: &'e [NullaryRule],
}
impl Ind<'_> {
    /// Lean's structure-like families: one constructor, no indices, not
    /// recursive. Only these get structure eta (in conversion and for iota)
    /// and unit-like equality.
    fn structure_like(&self) -> bool {
        self.ctors.len() == 1 && self.nidx == 0 && self.nonrecursive
    }
}

#[derive(Clone, Copy)]
struct ConstantSlot {
    name: NameId,
    epoch: u32,
    view: u32,
}

#[derive(Clone, Copy)]
struct CInfo<'e> {
    name: NameId,
    canon: u32,
    ty: Option<ExprId>,
    value: Option<ExprId>,
    params: &'e [NameId],
    /// Unfolding priority (class, height) for definitions and theorems.
    delta: Option<(u8, u32)>,
    rec: Option<Rec<'e>>,
    ctor: Option<(u32, u32)>,
    ind: Option<Ind<'e>>,
    /// 0 unknown, 1 none, 2 + operation index.
    natop: u8,
    /// 0 unknown, 1 none, 2 equality (`Nat.beq`), 3 less-or-equal (`Nat.ble`).
    natpred: u8,
    /// Validated quotient primitive role.
    quot: Option<QuotientRole>,
}

enum Lazy {
    Decided(bool),
    Stuck(u32, u32),
}

#[derive(Clone, Copy)]
struct LInst {
    ci: u32,
    start: u32,
    len: u32,
    next: u32,
}

enum NatLit {
    Small(u64),
    /// Canonical decimal digits of a value above `u64::MAX`.
    Big(Vec<u8>),
}
impl NatLit {
    /// A fallible copy (big literals own their digits).
    fn dup(&self) -> R<Self> {
        Ok(match self {
            Self::Small(v) => Self::Small(*v),
            Self::Big(b) => Self::Big(copied(b)?),
        })
    }
}

/// Capacity reused across declaration attempts on one thread. Contents are
/// always cleared before reuse: no value, environment or cache entry survives
/// an attempt. Charges and table behaviour follow logical sizes, which depend
/// only on the attempt itself; reused capacity is bounded by `RETAIN`.
#[derive(Default)]
struct Arena {
    vals: Vec<Val>,
    meta: Vec<Meta>,
    cells: Vec<Cell>,
    envs: Vec<EnvNode>,
    locals: Vec<u32>,
    memo: Exact,
    clo_index: Lossy<(u32, u32, u32, u32, u32, u32), u32>,
    env_index: Map<(u32, u32, u32), u32>,
    env_lossy: Lossy<EnvKey, u32>,
    infer_cache: Map<(u32, u32, u32), (u32, bool)>,
    eq_ok: Lossy<(u32, u32), ()>,
    val_index: Lossy<(u32, u32, u32, u32, u32), u32>,
    cell_index: Lossy<(u32, u32, u32), u32>,
    syn_ok: Lossy<(u32, u32, u32, u32, u32, u32), ()>,
    args_fail: Lossy<(u32, u32), ()>,
    local_index: Map<(u32, u32), u32>,
}
thread_local! {
    static ARENA: std::cell::RefCell<Option<Arena>> = const { std::cell::RefCell::new(None) };
}

/// Bounds belong to one attempt. Total scopes count every admission; argument
/// scopes count total steps minus tracked span credit. They never
/// travel with a retained graph, and nested scopes only narrow their own clock.
#[derive(Clone, Copy)]
struct ProbeBounds {
    total: u64,
    arguments: u64,
}

pub(crate) struct Kernel<'e, 'w> {
    env: &'e Environment,
    names: &'w Names,
    exprs: &'w Expressions,
    levels: &'w mut Levels,
    b: &'w mut Budget,
    params: &'e [NameId],
    before: usize,
    formation: Option<Formation>,
    checked_context: Option<&'w LocalContext>,
    /// Completed values of checked free locals, scoped to this immutable query/context.
    /// Never transferred between queries, contexts, formation epochs or universe scopes.
    free_values: Map<u32, u32>,
    mode: Mode,
    expression_end: usize,
    level_end: usize,
    /// Source bound for universe substitution: original levels plus any
    /// quotient-schema levels built before this attempt began.
    subst_end: usize,

    vals: Vec<Val>,
    meta: Vec<Meta>,
    cells: Vec<Cell>,
    envs: Vec<EnvNode>,
    locals: Vec<u32>,
    consts: Vec<CInfo<'e>>,
    constant_slots: Vec<ConstantSlot>,
    constant_epoch: u32,
    const_by_canon: Map<u32, u32>,
    linsts: Vec<LInst>,
    linst_levels: Vec<LevelId>,
    linst_index: Map<u64, u32>,
    nats: Vec<NatLit>,
    /// Let-bound fold restriction: two bits per value ID, set
    /// only for let-bound thunks. Bit `2v` marks a let-bound value; bit
    /// `2v + 1` records that reducing it exceeded `LET_FOLD_BUDGET` with the
    /// whole allowance available. Scope: these exact value IDs in this State's
    /// retained graph; never another origin or formation context.
    /// It only withholds an optional literal fold; no result,
    /// equality or failure is stored or concluded from it.
    let_marks: Vec<u64>,

    /// Evaluation results and pending thunks by (expression, environment,
    /// level instance); closed expressions use environment 0.
    memo: Exact,
    /// Closures interned by (form, domain, body, level instance, read key).
    clo_index: Lossy<(u32, u32, u32, u32, u32, u32), u32>,
    /// Environment nodes interned by (parent, value, type).
    /// Exact: the inference cache is keyed by environment identity.
    env_index: Map<(u32, u32, u32), u32>,
    env_lossy: Lossy<EnvKey, u32>,
    /// Exact: DAG-shared subterms must be checked once (losing an entry can
    /// make checking exponential), so this one is not lossy.
    infer_cache: Map<(u32, u32, u32), (u32, bool)>,
    const_type: Map<(u32, u32), u32>,
    const_body: Map<(u32, u32), u32>,
    /// Arguments a definition ignores (see `absent_args`), by constant.
    absent: Map<u32, u64>,
    /// (instantiated domain, 0) known not to be a proposition for these exact
    /// value IDs; retained only with their graph and original source in the
    /// same State, without formation or checked-context queries.
    // Isolated trial: completed argument-sort facts for the same immutable
    // graph, including only existing eligible retention. Original
    // type/context/universe identities and typed substitutions stay fixed.
    // Position zero keys an instantiated domain and stores non-proof only;
    // positions 1..=8 require explicit_proof_prefix before publication.
    // True means proof, not checkedness of an argument. No failed observation
    // or abandoned guard is stored; terminal retirement drops the owner.
    arg_proof_status: Map<(u32, u32), bool>,
    rule_rhs: Map<(u32, u32, u32), u32>,
    level_subst: Map<(u32, u32), LevelId>,
    level_eq: Map<(u32, u32), bool>,
    canon_of: Map<u32, LevelId>,
    level_index: Map<(u8, u32, u32), LevelId>,
    succ_of: Map<u32, LevelId>,
    eq_ok: Lossy<(u32, u32), ()>,
    /// Structural interning of value forms and spine cells (hash-consing).
    val_index: Lossy<(u32, u32, u32, u32, u32), u32>,
    cell_index: Lossy<(u32, u32, u32), u32>,
    binders: Vec<u32>,
    markers: u32,
    marker_vals: Map<u32, u32>,
    syn_ok: Lossy<(u32, u32, u32, u32, u32, u32), ()>,
    local_index: Map<(u32, u32), u32>,
    args_fail: Lossy<(u32, u32), ()>,
    nat_type: u32,
    quot_types: Option<[ExprId; 4]>,
    wants_quot: bool,
    /// Derived rule trees and unfolding heat; this attempt only.
    derived: derived::Derived,
    str_expansion: Map<u32, u32>,
    nat_ctors: Option<(u32, u32, u32)>,
    scratch: Vec<Scratch>,

    depth: u32,
    /// The checking thread's stack base, read once per attempt (0: unknown).
    stack_base: usize,
    steps: u64,
    charged: u64,
    reserved: u64,
    /// Cached min(bounds.total, bounds.arguments + span_work), saturated.
    /// steps_by uses only this total-step bound; no second clock in its hot path.
    limit: u64,
    bounds: ProbeBounds,
    span_work: u64,
    source_support: Map<u32, u64>,
    /// Bounded eval/thunk environment representatives.
    /// Exact raw values at complete source-fixed positions select an actual
    /// representative environment. No result or checkedness is stored here.
    /// Scope: ordinary, nonstaged queries in one State's retained graph; no
    /// Free-containing sources or checked formation contexts. Source and
    /// universe remain in the memo key. Forcing preserves each value ID's
    /// meaning. Retains exact graph/environment IDs only with their
    /// immutable source and name origin, never across State or staging owners.
    read_environments: Map<(u64, [u32; 16]), u32>,
    /// Wide-mask representatives, same exact graph/source/owner scope as above.
    /// Combined with read_environments, at most131072 entries; no eviction.
    wide_read_environments: Map<read_wide::RepresentativeKey, u32>,
    // Exact source read masks, typed context-list tokens and completed actual
    // judgments. Retains these only with exact graph/context IDs and
    // the same immutable source/name origin; no Free or formation context.
    read_plans: Map<u32, Option<[u64; 4]>>,
    large_read_nodes: Map<(u32, u32, u32), u32>,
    large_read_types: Map<read_large::LargeReadKey, u32>,
    alpha_types: Map<AlphaKey, (u32, [u32; 8])>,
    rename_ids: Map<(u32, [u32; 8], [u32; 8]), u32>,
    renamed_values: Map<(u32, u32), u32>,
    renamed_spines: Map<(u32, u32), u32>,
    renamed_envs: Map<(u32, u64, u32), u32>,
}

impl<'e, 'w> Kernel<'e, 'w> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        env: &'e Environment,
        names: &'w Names,
        exprs: &'w Expressions,
        levels: &'w mut Levels,
        b: &'w mut Budget,
        scope: &Scope<'e>,
    ) -> Self {
        let subst_end = levels.len();
        let mut a = ARENA.with(|c| c.borrow_mut().take()).unwrap_or_default();
        a.vals.clear();
        a.meta.clear();
        a.cells.clear();
        a.envs.clear();
        a.locals.clear();
        for l in [
            &mut a.clo_index as &mut dyn Resettable,
            &mut a.env_lossy,
            &mut a.eq_ok,
            &mut a.val_index,
            &mut a.cell_index,
            &mut a.syn_ok,
            &mut a.args_fail,
        ] {
            l.reset_table();
        }
        a.memo.reset_table();
        a.env_index.clear();
        a.infer_cache.clear();
        a.local_index.clear();
        Self {
            env,
            names,
            exprs,
            levels,
            b,
            params: scope.parameters,
            before: scope.before,
            formation: scope.formation,
            checked_context: None,
            free_values: Map::default(),
            mode: scope.mode,
            expression_end: scope.expression_end,
            level_end: scope.level_end,
            subst_end,
            vals: a.vals,
            meta: a.meta,
            cells: a.cells,
            envs: a.envs,
            locals: a.locals,
            consts: Vec::new(),
            constant_slots: Vec::new(),
            constant_epoch: 1,
            const_by_canon: Map::default(),
            linsts: Vec::new(),
            linst_levels: Vec::new(),
            linst_index: Map::default(),
            nats: Vec::new(),
            let_marks: Vec::new(),
            memo: a.memo,
            clo_index: a.clo_index,
            env_index: a.env_index,
            env_lossy: a.env_lossy,
            infer_cache: a.infer_cache,
            const_type: Map::default(),
            const_body: Map::default(),
            absent: Map::default(),
            arg_proof_status: Map::default(),
            rule_rhs: Map::default(),
            level_subst: Map::default(),
            level_eq: Map::default(),
            canon_of: Map::default(),
            level_index: Map::default(),
            succ_of: Map::default(),
            eq_ok: a.eq_ok,
            val_index: a.val_index,
            cell_index: a.cell_index,
            binders: Vec::new(),
            markers: 0,
            marker_vals: Map::default(),
            syn_ok: a.syn_ok,
            local_index: a.local_index,
            args_fail: a.args_fail,
            nat_type: NONE,
            quot_types: None,
            wants_quot: false,
            derived: derived::Derived::default(),
            str_expansion: Map::default(),
            nat_ctors: None,
            scratch: Vec::new(),
            depth: 0,
            stack_base: STACK_BASE.with(std::cell::Cell::get),
            steps: 0,
            charged: 0,
            reserved: 0,
            limit: u64::MAX,
            bounds: ProbeBounds {
                total: u64::MAX,
                arguments: u64::MAX,
            },
            span_work: 0,
            alpha_types: Map::default(),
            rename_ids: Map::default(),
            renamed_values: Map::default(),
            renamed_spines: Map::default(),
            renamed_envs: Map::default(),
            source_support: Map::default(),
            read_environments: Map::default(),
            wide_read_environments: Map::default(),
            read_plans: Map::default(),
            large_read_nodes: Map::default(),
            large_read_types: Map::default(),
        }
    }

    // ---------- accounting ----------

    /// Reserve the reused arena capacity, then create the root spine cell,
    /// environment and level instance. Nothing allocates before this.
    fn init(&mut self) -> R<()> {
        // A fixed upper bound for the existing optional 64-entry pool itself.
        // Buffer payloads have separate live reservations, including in-pool.
        charge_bytes(self.b, &mut self.reserved, 64 * size_of::<Scratch>())?;
        room(self.b, &mut self.reserved, &mut self.cells, 1)?;
        self.cells.push(Cell {
            prev: 0,
            item: 0,
            tag: 0,
            len: 0,
        });
        room(self.b, &mut self.reserved, &mut self.envs, 1)?;
        self.envs.push(EnvNode {
            parent: 0,
            val: NONE,
            ty: NONE,
        });
        room(self.b, &mut self.reserved, &mut self.linsts, 1)?;
        self.linsts.push(LInst {
            ci: NONE,
            start: 0,
            len: 0,
            next: NONE,
        });
        Ok(())
    }

    fn argument_steps(&self) -> u64 {
        // Construction invariant: every installed span credit is also admitted
        // to total steps before returning, including when admission aborts.
        // Untracked outside-scope spans shift the next origin and bound equally.
        self.steps - self.span_work
    }
    fn refresh_limit(&mut self) {
        self.limit = self
            .bounds
            .total
            .min(self.bounds.arguments.saturating_add(self.span_work));
    }
    fn limit_arguments(&mut self, end: u64) {
        self.bounds.arguments = self.bounds.arguments.min(end);
        self.refresh_limit();
    }
    fn limit_total(&mut self, end: u64) {
        self.bounds.total = self.bounds.total.min(end);
        self.refresh_limit();
    }
    fn restore_bounds(&mut self, saved: ProbeBounds) {
        self.bounds = saved;
        self.refresh_limit();
    }
    /// Keep the mandatory ledger and attempt cap on total work, while granting
    /// only argument scopes credit for this known span. A strict total scope
    /// (syntax, support or let folding) remains authoritative.
    fn application_span(&mut self, count: u64) -> R<()> {
        // With no argument scope, shifting its future origin needs no stored
        // credit. Strict total scopes and the mandatory ledger still see it.
        if self.bounds.arguments == u64::MAX {
            return self.steps_by(count);
        }
        self.steps
            .checked_add(count)
            .ok_or(ResourceError::Counter)?;
        self.span_work = self
            .span_work
            .checked_add(count)
            .ok_or(ResourceError::Counter)?;
        self.refresh_limit();
        self.steps_by(count)
    }

    #[inline]
    fn step(&mut self) -> R<()> {
        self.steps_by(1)
    }
    /// One coarse admission for known traversal work. Lookups include their
    /// final entry read. The existing local allowance and global block flush
    /// count this work even on the cheap Bound-thunk path.
    #[inline]
    fn steps_by(&mut self, count: u64) -> R<()> {
        self.steps = self
            .steps
            .checked_add(count)
            .ok_or(ResourceError::Counter)?;
        if self.steps > self.limit {
            return Err(KErr::Abort);
        }
        let pending = self.steps - self.charged;
        if pending >= CHARGE_BLOCK {
            self.flush_steps(pending)?;
        }
        Ok(())
    }
    /// Admission checkpoints are rare compared with individual step updates.
    /// Preserve charge, review and exhaustion ordering outside their hot path.
    #[cold]
    fn flush_steps(&mut self, pending: u64) -> R<()> {
        self.b.charge_work(pending)?;
        self.charged = self.steps;
        self.env_lossy.review();
        self.val_index.review();
        self.cell_index.review();
        if self.steps > step_cap() {
            return step_limit();
        }
        Ok(())
    }
    #[inline]
    fn enter(&mut self) -> R<()> {
        let probe = 0u8;
        let used = self.stack_base.abs_diff(std::ptr::addr_of!(probe) as usize);
        if self.depth >= MAX_DEPTH || (self.stack_base != 0 && used > STACK_BUDGET) {
            return no();
        }
        // Count the frame only once the step is allowed, so an error here
        // (an exhausted allowance or budget) leaves the depth balanced.
        self.step()?;
        self.depth += 1;
        Ok(())
    }
    #[inline]
    fn leave(&mut self) {
        self.depth -= 1;
    }
    /// Return reusable capacity to the thread arena (contents are cleared on
    /// the next attempt's start).
    fn retire_arena(&mut self) {
        self.read_environments = Map::default();
        self.wide_read_environments = Map::default();
        // Attempt-local judgments are dead before value stores retire. Free
        // these owners first; their existing logical charge stays in reserved
        // until the unchanged attempt cleanup releases it. No receipt survives.
        self.read_plans = Map::default();
        self.large_read_nodes = Map::default();
        self.large_read_types = Map::default();
        // Keep only small stores between attempts: their capacity is not
        // charged to later attempts, so it stays a fixed per-thread amount
        // (at most `RETAIN` bytes per store; 16 stores, two buffers per lossy
        // table, so under 8 MiB). Larger stores are freed now.
        fn vec<T>(v: &mut Vec<T>) -> Vec<T> {
            let v = std::mem::take(v);
            if v.capacity() * size_of::<T>() <= RETAIN {
                v
            } else {
                Vec::new()
            }
        }
        fn map<K, V>(m: &mut Map<K, V>) -> Map<K, V> {
            let m = std::mem::take(m);
            if map_bytes::<K, V>(m.capacity()) <= RETAIN {
                m
            } else {
                Map::default()
            }
        }
        fn lossy<K: LossyKey, V: Copy>(t: &mut Lossy<K, V>) -> Lossy<K, V> {
            let t = std::mem::take(t);
            if t.held() <= 2 * RETAIN {
                t
            } else {
                Lossy::default()
            }
        }
        let a = Arena {
            vals: vec(&mut self.vals),
            meta: vec(&mut self.meta),
            cells: vec(&mut self.cells),
            envs: vec(&mut self.envs),
            locals: vec(&mut self.locals),
            memo: {
                let t = std::mem::take(&mut self.memo);
                if t.held() <= 2 * RETAIN {
                    t
                } else {
                    Exact::default()
                }
            },
            clo_index: lossy(&mut self.clo_index),
            env_index: map(&mut self.env_index),
            env_lossy: lossy(&mut self.env_lossy),
            infer_cache: map(&mut self.infer_cache),
            eq_ok: lossy(&mut self.eq_ok),
            val_index: lossy(&mut self.val_index),
            cell_index: lossy(&mut self.cell_index),
            syn_ok: lossy(&mut self.syn_ok),
            args_fail: lossy(&mut self.args_fail),
            local_index: map(&mut self.local_index),
        };
        ARENA.with(|c| *c.borrow_mut() = Some(a));
    }

    // ---------- values ----------

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
                NatLit::Big(_) => return None,
            },
            _ => return None,
        })
    }
    fn push(&mut self, mut v: Val) -> R<u32> {
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
    fn push_fresh(&mut self, v: Val, key: Option<(ValueKey, usize)>) -> R<u32> {
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
            ty: NONE,
        });
        Ok(id)
    }
    /// Interned: equal extensions of equal environments are the same node, so
    /// memoised evaluation shares results across repeated applications.
    #[inline(always)]
    fn env_push(&mut self, parent: u32, val: u32, ty: u32) -> R<u32> {
        let key = (parent, val, ty);
        // Typed (inference) environments are interned exactly: the inference
        // cache is keyed by their identity. Evaluation environments use the
        // lossy table, which only affects sharing.
        let typed = ty != NONE;
        let hash = if typed {
            0
        } else {
            Lossy::<EnvKey, u32>::key_hash(&EnvKey { parent, val })
        };
        let hit = if typed {
            self.env_index.get(&key).copied()
        } else {
            self.env_lossy.probe_hashed(&EnvKey { parent, val }, hash)
        };
        if let Some(id) = hit {
            return Ok(id);
        }
        self.env_push_miss(parent, val, ty, hash)
    }
    // The fast lookup keeps every original counter/key; only a miss needs
    // allocation, fallible charging and insertion. Preserve that order here.
    #[inline(never)]
    fn env_push_miss(&mut self, parent: u32, val: u32, ty: u32, hash: usize) -> R<u32> {
        let key = (parent, val, ty);
        let typed = ty != NONE;
        let id = self.envs.len() as u32;
        room(self.b, &mut self.reserved, &mut self.envs, 1)?;
        self.envs.push(EnvNode { parent, val, ty });
        if typed {
            map_put(self.b, &mut self.reserved, &mut self.env_index, key, id)?;
        } else {
            self.env_lossy.insert_hashed(
                EnvKey { parent, val },
                id,
                hash,
                self.b,
                &mut self.reserved,
            )?;
        }
        Ok(id)
    }
    #[inline]
    fn env_at(&mut self, mut env: u32, mut i: u32) -> R<EnvNode> {
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
    fn ekey(&self, env: u32, r: u32) -> (u32, u32, u32) {
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
    // Exact values at source-fixed positions; at most two fit the current key.
    fn sparse_read_key(&self, mut env: u32, mut mask: u64) -> Option<(u32, u32, u32)> {
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
    fn evaluation_read_key(
        &mut self,
        e: ExprId,
        env: u32,
        loose: u32,
        has_free: bool,
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
        if (64..=256).contains(&loose)
            && !has_free
            && self.formation.is_none()
            && self.checked_context.is_none()
            && self.steps >= 4096
        {
            return self.wide_evaluation_read_key(e, env);
        }
        Ok(self.ekey(env, loose))
    }
    // Called only after the original narrow-key path is unavailable and the
    // exact existing scope/read-mask guards hold. Keep this larger setup out
    // of that path; its fallback for loose > 2 is exactly (3, env, 0).
    fn representative_read_key(&mut self, env: u32, mask: u64, reads: u32) -> R<(u32, u32, u32)> {
        // Charge the complete traversal and short key construction once,
        // before touching the chain, including a miss or abandoned route.
        self.steps_by(u64::from(64 - mask.leading_zeros() + reads))?;
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
            return Ok((3, representative, 0));
        }
        if self.read_environments.len() + self.wide_read_environments.len() < 131_072 {
            self.insert_read_environment(key, env)?;
        }
        Ok((3, env, 0))
    }
    /// The exact-table helper owns logical growth and physical rehash overlap.
    /// Required failures retain their successful reservations for cleanup.
    fn insert_read_environment(&mut self, key: (u64, [u32; 16]), env: u32) -> R<()> {
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.read_environments,
            key,
            env,
        )
    }
    fn push_clo(&mut self, form: u32, c: Clo, loose: u32) -> R<u32> {
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
    /// Interned: equal spines are the same cell.
    fn cell(&mut self, prev: u32, item: u32, tag: u32) -> R<u32> {
        let key = (prev, item, tag);
        let hash = Lossy::<(u32, u32, u32), u32>::key_hash(&key);
        if let Some(id) = self.cell_index.probe_hashed(&key, hash) {
            return Ok(id);
        }
        let id = self.cells.len() as u32;
        let len = self.cells[prev as usize].len + 1;
        room(self.b, &mut self.reserved, &mut self.cells, 1)?;
        self.cells.push(Cell {
            prev,
            item,
            tag,
            len,
        });
        self.cell_index
            .insert_hashed(key, id, hash, self.b, &mut self.reserved)?;
        Ok(id)
    }
    /// Spine cells from root to tip, in a reusable buffer.
    fn spine_items(&mut self, s: u32) -> R<Scratch> {
        self.spine_items_from(s, 0)
    }
    /// Cells strictly after `base` up to the tip `s`, root first.
    fn spine_items_from(&mut self, mut s: u32, base: u32) -> R<Scratch> {
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
    fn spine_args_opt(&mut self, s: u32) -> R<Option<Scratch>> {
        match self.spine_args(s) {
            Ok(v) => Ok(Some(v)),
            Err(KErr::Unsupported) => Ok(None),
            Err(e) => Err(e),
        }
    }
    /// The cell just below the first (root-most) projection, if any.
    fn proj_prefix(&self, mut s: u32) -> Option<u32> {
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
    fn spine_args(&mut self, s: u32) -> R<Scratch> {
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
    fn arg_item(&self, s: u32) -> Option<u32> {
        let c = self.cells[s as usize];
        (c.tag == 0).then_some(c.item)
    }
    /// Admit a buffer's new logical layout while its old layout remains owned.
    /// Reused physical capacity does not affect charges. A failed allocator
    /// reservation is undone here; every successful payload reservation stays
    /// with exactly this buffer until replacement, explicit disposal or final
    /// whole-attempt retirement.
    #[inline]
    fn scratch_room(&mut self, v: &mut Scratch, extra: usize) -> R<()> {
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
            .checked_mul(size_of::<u32>())
            .ok_or(ResourceError::Counter)?;
        let old = (v.slots * size_of::<u32>()) as u64;
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
    fn recycle(&mut self, v: Scratch) -> Result<(), ResourceError> {
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
        let bytes = (v.slots * size_of::<u32>()) as u64;
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
    fn scratch_finish<T, const N: usize>(
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
    fn open_local(&mut self, ty: u32) -> R<u32> {
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
    fn close_local(&mut self) {
        self.binders.pop();
    }
    /// The owner keeps this checked context immutable for the entire query.
    /// Types/values mention only earlier active locals; insertion follows completed
    /// evaluation, and the cache is dropped before the borrowed context can change.
    fn checked_free(&mut self, id: u32) -> R<u32> {
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

    fn fresh_local(&mut self, ty: u32) -> R<u32> {
        let id = self.locals.len() as u32;
        room(self.b, &mut self.reserved, &mut self.locals, 1)?;
        self.locals.push(ty);
        self.push(Val::Local { id, spine: 0 })
    }
    /// Every retained Big payload comes from reserved `parse_nat` construction.
    /// `NatLit::dup` is temporary and must never be installed here. The byte
    /// reservation remains in `self.reserved` until this attempt retires.
    fn nat(&mut self, n: NatLit) -> R<u32> {
        let id = self.nats.len() as u32;
        room(self.b, &mut self.reserved, &mut self.nats, 1)?;
        self.nats.push(n);
        self.push(Val::Nat(id))
    }

    // ---------- levels ----------

    fn subst_level(&mut self, l: LevelId, li: u32) -> R<LevelId> {
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
    fn canon_level(&mut self, l: LevelId) -> R<LevelId> {
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
    fn succ(&mut self, l: LevelId) -> R<LevelId> {
        if let Some(&r) = self.succ_of.get(&l.slot()) {
            return Ok(r);
        }
        let r = self.levels.append(LevelKind::Succ(l), self.names, self.b)?;
        map_put(self.b, &mut self.reserved, &mut self.succ_of, l.slot(), r)?;
        Ok(r)
    }
    fn imax(&mut self, a: LevelId, c: LevelId) -> R<LevelId> {
        let names = self.names;
        Ok(self.levels.with_helpers(names, self.b, |h| h.imax(a, c))?)
    }
    fn level_eq(&mut self, a: LevelId, c: LevelId) -> R<bool> {
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
    fn is_zero(&mut self, l: LevelId) -> R<bool> {
        Ok(self.levels.get(l, self.b)?.zero() == LevelZero::Zero)
    }
    fn li_levels(&self, li: u32) -> &[LevelId] {
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
    fn wide_instance(&mut self, ci: u32, source: &[LevelId], li: u32) -> R<u32> {
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
    fn rebind_instance(&mut self, ci: u32, li: u32) -> R<u32> {
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
    fn intern_li(&mut self, ci: u32, levels: &[LevelId]) -> R<u32> {
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
    fn same_levels(&mut self, a: u32, c: u32) -> R<bool> {
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

    fn canon(&mut self, n: NameId) -> R<u32> {
        Ok(self.names.summary(n, self.b)?.canonical)
    }
    // Stable ci/name identity is owned by the retained graph. Borrowed views
    // belong only to this attempt and are resolved on demand through the same
    // visible-safe-constant lookup. A missing view grants no result.
    fn const_info(&mut self, n: NameId) -> R<u32> {
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
    fn const_view(&mut self, ci: u32) -> R<&CInfo<'e>> {
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
    fn const_view_mut(&mut self, ci: u32) -> R<&mut CInfo<'e>> {
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
    fn const_type(&mut self, ci: u32, li: u32) -> R<u32> {
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
    fn const_body(&mut self, ci: u32, li: u32) -> R<u32> {
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
    fn nat_ctors(&mut self) -> R<Option<(u32, u32, u32)>> {
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
    fn nat_type(&mut self) -> R<u32> {
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
    fn natop(&mut self, ci: u32) -> R<Option<crate::check::natural::Operation>> {
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
    fn natpred(&mut self, ci: u32) -> R<Option<bool>> {
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

    fn force(&mut self, mut v: u32) -> R<u32> {
        loop {
            match self.vals[v as usize] {
                Val::Ind(t) => v = t,
                Val::Delayed { e, env, li } => {
                    let r = self.eval(e, env, li)?;
                    self.vals[v as usize] = Val::Ind(r);
                    v = r;
                }
                _ => return Ok(v),
            }
        }
    }
    /// A lazily evaluated argument; cheap forms are evaluated directly.
    #[inline(always)]
    fn thunk(&mut self, e: ExprId, env: u32, li: u32) -> R<u32> {
        let node = self.exprs.get(e, self.b)?;
        let bound = node.bound_index();
        if let Some(index) = bound {
            // kind() would observe exactly this read; preserve diagnostics too.
            self.b.observe(crate::resource::Event::TableLookups, 1);
            return Ok(self.env_at(env, index)?.val);
        }
        self.thunk_general(e, env, li, node)
    }
    /// Same source/node identity as the caller. No fresh get or cache scope.
    #[inline(never)]
    fn thunk_general(&mut self, e: ExprId, env: u32, li: u32, node: Expression<'w>) -> R<u32> {
        // Variables and cheap forms first: they never need a thunk, and the
        // memo is consulted (once) only for delayed computations.
        let kind = node.kind(self.exprs, self.levels, self.b)?;
        match kind {
            ExprKind::Bound(i) => return Ok(self.env_at(env, i)?.val),
            ExprKind::Sort(_)
            | ExprKind::Constant(..)
            | ExprKind::Lambda(..)
            | ExprKind::Pi(..)
            | ExprKind::Natural(_)
            | ExprKind::String(_) => return self.eval_decoded(e, env, li, node, kind),
            _ => {}
        }
        let loose = node.loose_range();
        let (kt, k1, k2) = self.ekey(env, loose);
        let exact = (e.slot(), li, kt, k1, k2);
        if let Some(v) = self.memo.get(&exact) {
            return Ok(v);
        }
        let (kt, k1, k2) = self.evaluation_read_key(e, env, loose, node.has_free())?;
        let mkey = (e.slot(), li, kt, k1, k2);
        // The selected exact key owns the shared recipe. Do not duplicate it
        // under a raw-environment alias. Eligibility changes can
        // lose sharing, but a second valid recipe supplies no completion fact.
        if mkey != exact
            && let Some(v) = self.memo.get(&mkey)
        {
            return Ok(v);
        }
        let env = if loose == 0 { 0 } else { env };
        let v = self.push(Val::Delayed { e, env, li })?;
        self.memo.insert(mkey, v, self.b, &mut self.reserved)?;
        Ok(v)
    }
    fn eval(&mut self, e: ExprId, env: u32, li: u32) -> R<u32> {
        let node = self.exprs.get(e, self.b)?;
        let kind = node.kind(self.exprs, self.levels, self.b)?;
        self.eval_decoded(e, env, li, node, kind)
    }
    /// The decoded view borrows only the immutable expression store. It is
    /// consumed in this call, never retained in a value or across retirement.
    /// Construction contract: e, node and kind describe the same source slot
    /// in self.exprs; lifetimes alone do not prove their identity correspondence.
    #[inline(always)]
    fn eval_decoded(
        &mut self,
        e: ExprId,
        env: u32,
        li: u32,
        node: Expression<'w>,
        kind: ExprKind<'w>,
    ) -> R<u32> {
        let loose = node.loose_range();
        // Variables and closures need neither the memo nor a decode later.
        match kind {
            ExprKind::Bound(i) => {
                let v = self.env_at(env, i)?.val;
                return self.force(v);
            }
            ExprKind::Lambda(_, d, body, _) => {
                let c = Clo {
                    dom: d,
                    body,
                    env,
                    li,
                };
                return self.push_clo(0, c, loose);
            }
            ExprKind::Pi(_, d, body, _) => {
                let c = Clo {
                    dom: d,
                    body,
                    env,
                    li,
                };
                return self.push_clo(1, c, loose);
            }
            _ => {}
        }
        let (kt, k1, k2) = self.ekey(env, loose);
        let exact = (e.slot(), li, kt, k1, k2);
        let mut mkey = exact;
        let mut cached = self.memo.get(&exact);
        if cached.is_none() {
            let (kt, k1, k2) = self.evaluation_read_key(e, env, loose, node.has_free())?;
            mkey = (e.slot(), li, kt, k1, k2);
            if mkey != exact {
                cached = self.memo.get(&mkey);
            }
        }
        let env = if loose == 0 { 0 } else { env };
        let mut pending = NONE;
        if let Some(v) = cached {
            match self.vals[v as usize] {
                // The cached thunk is this very evaluation: run it once and
                // redirect the thunk to the result.
                Val::Delayed { .. } => pending = v,
                _ => return self.force(v),
            }
        }
        self.enter()?;
        let r = self.eval_inner(e, env, li, kind);
        self.leave();
        let r = r?;
        if pending != NONE {
            // The memo already maps this key to the thunk, now redirected to
            // its value: no second write is needed.
            self.vals[pending as usize] = Val::Ind(r);
        } else {
            self.memo.insert(mkey, r, self.b, &mut self.reserved)?;
        }
        Ok(r)
    }
    fn eval_inner(&mut self, e: ExprId, env: u32, li: u32, kind: ExprKind<'w>) -> R<u32> {
        match kind {
            ExprKind::Free(id) => self.checked_free(id),
            ExprKind::Bound(i) => {
                let v = self.env_at(env, i)?.val;
                self.force(v)
            }
            ExprKind::Sort(l) => {
                let l = self.subst_level(l, li)?;
                self.push(Val::Sort(l))
            }
            ExprKind::Constant(n, ls) => {
                let ci = self.const_info(n)?;
                // Common universe lists stay on the stack. Rare longer lists
                // use a charged temporary buffer without a fixed arity cap.
                if ls.len() != self.const_view(ci)?.params.len() {
                    return no();
                }
                if ls.len() > LEVEL_ARGS {
                    let li = self.wide_instance(ci, ls, li)?;
                    return self.push(Val::Const { ci, li, spine: 0 });
                }
                let mut buf = [LevelId::ZERO; LEVEL_ARGS];
                for (slot, &l) in buf.iter_mut().zip(ls) {
                    let l = self.subst_level(l, li)?;
                    *slot = self.canon_level(l)?;
                }
                let levels = &buf[..ls.len()];
                let li = self.intern_li(ci, levels)?;
                self.push(Val::Const { ci, li, spine: 0 })
            }
            ExprKind::App(first_f, first_a) => {
                let mut args = self.scratch.pop().unwrap_or_default();
                args.clear();
                let res = (|| {
                    // Construction contract: kind was decoded from e in the
                    // same immutable source; f/a are exactly that App's fields.
                    self.scratch_room(&mut args, 1)?;
                    args.push(first_a.slot());
                    let mut head = first_f;
                    let (node, kind) = loop {
                        let node = self.exprs.get(head, self.b)?;
                        let kind = node.kind(self.exprs, self.levels, self.b)?;
                        match kind {
                            ExprKind::App(f, a) => {
                                self.scratch_room(&mut args, 1)?;
                                args.push(a.slot());
                                head = f;
                            }
                            _ => break (node, kind),
                        }
                    };
                    // The retained view and kind were read from head in this
                    // loop and never cross a source mutation or retirement.
                    let f = self.eval_decoded(head, env, li, node, kind)?;
                    args.reverse();
                    for slot in args.iter_mut() {
                        *slot = self.thunk(ExprId::from_stored_original(*slot), env, li)?;
                    }
                    self.apply_many(f, &args)
                })();
                self.scratch_finish(res, [args])
            }
            ExprKind::Lambda(_, d, body, _) => self.push(Val::Lam(Clo {
                dom: d,
                body,
                env,
                li,
            })),
            ExprKind::Pi(_, d, body, _) => self.push(Val::Pi(Clo {
                dom: d,
                body,
                env,
                li,
            })),
            ExprKind::Let(_, _, v, body, _) => {
                let v = self.thunk(v, env, li)?;
                self.mark_let(v)?;
                let env = self.env_push(env, v, NONE)?;
                self.eval(body, env, li)
            }
            ExprKind::Projection(s, idx, x) => {
                let sci = self.const_info(s)?;
                let x = self.thunk(x, env, li)?;
                self.push(Val::Proj { x, idx, sci })
            }
            ExprKind::Natural(bytes) => {
                let lit = parse_nat(bytes, self.b, &mut self.reserved)?;
                self.nat(lit)
            }
            ExprKind::String(_) => self.push(Val::Str(e)),
            _ => no(),
        }
    }
    /// Expand a string literal to `String.ofList [Char.ofNat c₁, …]` under the
    /// committed String certificate, as the existing route does.
    fn expand_str(&mut self, e: ExprId) -> R<u32> {
        if let Some(&v) = self.str_expansion.get(&e.slot()) {
            return Ok(v);
        }
        let env = self.env;
        let Some([char_n, of_nat_n, nil_n, cons_n, of_list_n]) = env.string_symbols(
            self.before,
            self.formation,
            self.expression_end,
            self.exprs,
            self.levels,
            self.b,
        )?
        else {
            return no();
        };
        let ExprKind::String(bytes) =
            self.exprs
                .get(e, self.b)?
                .kind(self.exprs, self.levels, self.b)?
        else {
            return no();
        };
        let Ok(text) = std::str::from_utf8(bytes) else {
            return no();
        };
        self.b.charge_work(2 * bytes.len() as u64 + 32)?;

        let (char_ci, of_nat_ci, nil_ci, cons_ci, of_list_ci) = (
            self.const_info(char_n)?,
            self.const_info(of_nat_n)?,
            self.const_info(nil_n)?,
            self.const_info(cons_n)?,
            self.const_info(of_list_n)?,
        );
        let zero = self.canon_level(LevelId::ZERO)?;
        let list_li_nil = self.intern_li(nil_ci, &[zero])?;
        let list_li_cons = self.intern_li(cons_ci, &[zero])?;
        let char_ty = self.push(Val::Const {
            ci: char_ci,
            li: 0,
            spine: 0,
        })?;
        let nil_spine = self.cell(0, char_ty, 0)?;
        let mut tail = self.push(Val::Const {
            ci: nil_ci,
            li: list_li_nil,
            spine: nil_spine,
        })?;
        for c in text.chars().rev().map(u32::from) {
            self.step()?;
            let lit = self.nat(NatLit::Small(u64::from(c)))?;
            let ch_spine = self.cell(0, lit, 0)?;
            let ch = self.push(Val::Const {
                ci: of_nat_ci,
                li: 0,
                spine: ch_spine,
            })?;
            let s1 = self.cell(0, char_ty, 0)?;
            let s2 = self.cell(s1, ch, 0)?;
            let s3 = self.cell(s2, tail, 0)?;
            tail = self.push(Val::Const {
                ci: cons_ci,
                li: list_li_cons,
                spine: s3,
            })?;
        }
        let sp = self.cell(0, tail, 0)?;
        let v = self.push(Val::Const {
            ci: of_list_ci,
            li: 0,
            spine: sp,
        })?;
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.str_expansion,
            e.slot(),
            v,
        )?;
        Ok(v)
    }
    fn str_type(&mut self) -> R<u32> {
        let env = self.env;
        let Some(t) = env.string_type(
            self.before,
            self.formation,
            self.expression_end,
            self.exprs,
            self.levels,
            self.b,
        )?
        else {
            return no();
        };
        self.eval(t, 0, 0)
    }
    /// Apply `f` to several arguments, peeling consecutive lambdas into one
    /// environment extension instead of building a closure per beta step.
    fn apply_many(&mut self, mut f: u32, args: &[u32]) -> R<u32> {
        // Admit the known span once, before forcing or mutation.
        // The monotone index covers lambda peeling and remaining-spine loops;
        // nested reductions retain their own independent charges.
        let work = u64::try_from(args.len())
            .map_err(|_| ResourceError::Counter)?
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        self.application_span(work)?;
        let mut i = 0;
        while i < args.len() {
            f = self.force(f)?;
            match self.vals[f as usize] {
                Val::Lam(c) => {
                    let mut env = self.env_push(c.env, args[i], NONE)?;
                    i += 1;
                    let mut body = c.body;
                    while i < args.len() {
                        match self
                            .exprs
                            .get(body, self.b)?
                            .kind(self.exprs, self.levels, self.b)?
                        {
                            ExprKind::Lambda(_, _, inner, _) => {
                                env = self.env_push(env, args[i], NONE)?;
                                i += 1;
                                body = inner;
                            }
                            _ => break,
                        }
                    }
                    f = self.eval(body, env, c.li)?;
                }
                Val::Local { id, spine } => {
                    let mut spine = spine;
                    for &a in &args[i..] {
                        spine = self.cell(spine, a, 0)?;
                    }
                    return self.push(Val::Local { id, spine });
                }
                Val::Const { ci, li, spine } => {
                    let mut spine = spine;
                    for &a in &args[i..] {
                        spine = self.cell(spine, a, 0)?;
                    }
                    return self.push(Val::Const { ci, li, spine });
                }
                // Project without unfolding the field: a certified head such
                // as `Nat.sub` must meet its arguments before any delta.
                Val::Proj { x, idx, sci } => {
                    let w = self.proj(x, idx, sci)?;
                    let w = self.force(w)?;
                    // The field may itself be another delayed projection.
                    // This is an additional reduction, not argument-span credit.
                    if matches!(self.vals[w as usize], Val::Proj { .. }) {
                        self.step()?;
                    }
                    f = w;
                }
                _ => return no(),
            }
        }
        Ok(f)
    }
    fn apply(&mut self, mut f: u32, a: u32) -> R<u32> {
        f = self.force(f)?;
        loop {
            match self.vals[f as usize] {
                Val::Lam(c) => {
                    let env = self.env_push(c.env, a, NONE)?;
                    return self.eval(c.body, env, c.li);
                }
                Val::Local { id, spine } => {
                    let spine = self.cell(spine, a, 0)?;
                    return self.push(Val::Local { id, spine });
                }
                Val::Const { ci, li, spine } => {
                    let spine = self.cell(spine, a, 0)?;
                    return self.push(Val::Const { ci, li, spine });
                }
                Val::Proj { x, idx, sci } => {
                    // As in apply_many, a reduced field may be another
                    // projection. Iterate rather than consuming Rust stack.
                    let w = self.proj(x, idx, sci)?;
                    f = self.force(w)?;
                    if matches!(self.vals[f as usize], Val::Proj { .. }) {
                        self.step()?;
                    }
                }
                _ => return no(),
            }
        }
    }
    /// Instantiate a binder value (function, Pi type or lambda type) at `a`.
    fn instantiate(&mut self, f: u32, a: u32) -> R<u32> {
        let f = self.force(f)?;
        match self.vals[f as usize] {
            Val::Pi(c) => {
                let env = self.env_push(c.env, a, NONE)?;
                self.eval(c.body, env, c.li)
            }
            Val::LamTy(c) => {
                let dom = self.eval(c.dom, c.env, c.li)?;
                let env = self.env_push(c.env, a, dom)?;
                self.infer(c.body, env, c.li, false)
            }
            Val::Arrow { cod, .. } => Ok(cod),
            _ => self.apply(f, a),
        }
    }
    fn binder_dom(&mut self, f: u32) -> R<u32> {
        match self.vals[f as usize] {
            Val::Pi(c) | Val::LamTy(c) | Val::Lam(c) => self.eval(c.dom, c.env, c.li),
            Val::Arrow { dom, .. } => Ok(dom),
            _ => no(),
        }
    }
    /// Field `idx` of `xs` when it is already a constructor application of `sci`.
    fn ctor_field(&mut self, xs: u32, idx: u32, sci: u32) -> R<Option<u32>> {
        if let Val::Const { ci, spine, .. } = self.vals[xs as usize]
            && let Some((family, _)) = self.const_view(ci)?.ctor
            && family == self.const_view(sci)?.canon
            && let Some(ind) = self.const_view(sci)?.ind
        {
            let at = ind.nparams + idx;
            let len = self.cells[spine as usize].len;
            if at >= len {
                return Ok(None);
            }
            let mut s = spine;
            for _ in 0..(len - 1 - at) {
                s = self.cells[s as usize].prev;
            }
            let c = self.cells[s as usize];
            return Ok((c.tag == 0).then_some(c.item));
        }
        Ok(None)
    }
    fn proj(&mut self, x: u32, idx: u32, sci: u32) -> R<u32> {
        let mut w = self.whnf(x)?;
        if let Val::Str(e) = self.vals[w as usize] {
            let x = self.expand_str(e)?;
            w = self.whnf(x)?;
        }
        if let Val::Const { ci, spine, .. } = self.vals[w as usize]
            && let Some((family, _)) = self.const_view(ci)?.ctor
            && family == self.const_view(sci)?.canon
        {
            let Some(ind) = self.const_view(sci)?.ind else {
                return no();
            };
            // Preserve the full projection-free-spine check. Admit its known
            // passes even when source normalization and scratch capacity are warm.
            self.steps_by(u64::from(self.cells[spine as usize].len) + 1)?;
            let args = self.spine_args(spine)?;
            let field = args.get((ind.nparams + idx) as usize).copied();
            self.recycle(args)?;
            return field.map_or_else(no, Ok);
        }
        match self.vals[w as usize] {
            Val::Local { id, spine } => {
                let spine = self.cell(spine, sci, idx + 1)?;
                self.push(Val::Local { id, spine })
            }
            Val::Const { ci, li, spine } => {
                let spine = self.cell(spine, sci, idx + 1)?;
                self.push(Val::Const { ci, li, spine })
            }
            _ => no(),
        }
    }

    // ---------- weak head normalisation ----------

    fn whnf_core(&mut self, v: u32) -> R<u32> {
        let v = self.force(v)?;
        let cached = self.meta[v as usize].core;
        if cached != NONE {
            return Ok(cached);
        }
        self.enter()?;
        let mut cur = v;
        let r = (|| loop {
            let value = self.vals[cur as usize];
            match value {
                Val::Const { ci, li, spine } if self.const_view(ci)?.rec.is_some() => {
                    match self.iota(ci, li, spine) {
                        Ok(Some(next)) => match self.force(next) {
                            Ok(n) => cur = n,
                            Err(e) => break Err(e),
                        },
                        Ok(None) => break Ok(cur),
                        Err(e) => break Err(e),
                    }
                }
                Val::Const { ci, spine, .. } if self.const_view(ci)?.quot.is_some() => {
                    match self.quot_reduce(ci, spine) {
                        Ok(Some(next)) => match self.force(next) {
                            Ok(n) => cur = n,
                            Err(e) => break Err(e),
                        },
                        Ok(None) => break Ok(cur),
                        Err(e) => break Err(e),
                    }
                }
                Val::Proj { x, idx, sci } => match self.whnf_core(x) {
                    Ok(xs) => match self.ctor_field(xs, idx, sci) {
                        Ok(Some(f)) => match self.force(f) {
                            Ok(n) => cur = n,
                            Err(e) => break Err(e),
                        },
                        Ok(None) => break Ok(cur),
                        Err(e) => break Err(e),
                    },
                    Err(e) => break Err(e),
                },
                _ => break Ok(cur),
            }
        })();
        self.leave();
        let r = r?;
        self.meta[v as usize].core = r;
        Ok(r)
    }
    fn whnf(&mut self, v: u32) -> R<u32> {
        let v = self.force(v)?;
        let cached = self.meta[v as usize].whnf;
        if cached != NONE {
            return Ok(cached);
        }
        self.enter()?;
        let r = (|| -> R<u32> {
            let mut cur = self.whnf_core(v)?;
            loop {
                if let Some(next) = self.nat_reduce(cur)? {
                    cur = self.whnf_core(next)?;
                    continue;
                }
                let value = self.vals[cur as usize];
                match value {
                    Val::Const { ci, .. } if self.const_view(ci)?.delta.is_some() => {
                        // Reuse only a completed reduct of this exact value.
                        // Retains its denotation, explicit levels and
                        // typed bindings; no incomplete exposure is published.
                        cur = self.unfold_value(cur)?;
                    }
                    Val::Proj { x, idx, sci } => {
                        let next = self.proj(x, idx, sci)?;
                        cur = self.whnf_core(next)?;
                    }
                    _ => return Ok(cur),
                }
            }
        })();
        self.leave();
        let r = r?;
        self.meta[v as usize].whnf = r;
        Ok(r)
    }
    fn unfold(&mut self, ci: u32, li: u32, spine: u32) -> R<u32> {
        let body = self.const_body(ci, li)?;
        self.replay(body, spine)
    }
    fn replay(&mut self, acc: u32, spine: u32) -> R<u32> {
        self.replay_from(acc, spine, 0)
    }
    /// Replay the cells strictly after `base` (up to the tip) onto `acc`.
    fn replay_from(&mut self, mut acc: u32, spine: u32, base: u32) -> R<u32> {
        let mut items = self.spine_items_from(spine, base)?;
        let result = (|| {
            let mut start = 0;
            for at in 0..items.len() {
                // Invariant: unvisited entries are cell IDs; the completed
                // range start..at holds the original raw argument value IDs.
                // Nested application owns no borrow of the scratch pool.
                let c = self.cells[items[at] as usize];
                if c.tag == 0 {
                    items[at] = c.item;
                    continue;
                }
                acc = self.apply_many(acc, &items[start..at])?;
                acc = self.proj(acc, c.tag - 1, c.item)?;
                start = at + 1;
            }
            if start < items.len() {
                acc = self.apply_many(acc, &items[start..])?;
            }
            Ok(acc)
        })();
        items.clear();
        self.scratch_finish(result, [items])
    }
    fn let_bit(&self, bit: u64) -> bool {
        self.let_marks
            .get((bit / 64) as usize)
            .is_some_and(|word| word >> (bit % 64) & 1 == 1)
    }
    fn set_let_bit(&mut self, bit: u64) -> R<()> {
        let word = (bit / 64) as usize;
        if word >= self.let_marks.len() {
            let extra = word + 1 - self.let_marks.len();
            room(self.b, &mut self.reserved, &mut self.let_marks, extra)?;
            self.let_marks.resize(word + 1, 0);
        }
        self.let_marks[word] |= 1 << (bit % 64);
        Ok(())
    }
    /// Mark a let-bound value that may still need reduction.
    fn mark_let(&mut self, v: u32) -> R<()> {
        if matches!(self.vals[v as usize], Val::Delayed { .. } | Val::Ind(_)) {
            self.set_let_bit(2 * u64::from(v))?;
        }
        Ok(())
    }
    /// Whether `lazy_delta` may reduce `v` to fold it. Values not reached
    /// through a let-bound link, literals and values already reduced always
    /// may. A let-bound value is reduced within `LET_FOLD_BUDGET`, never past
    /// an enclosing allowance: at most half of the room it leaves. If the
    /// full allowance runs out, the link is recorded and not tried again.
    fn let_fold_allowed(&mut self, v: u32) -> R<bool> {
        if self.let_marks.is_empty() {
            return Ok(true);
        }
        let mut link = NONE;
        let mut w = v;
        loop {
            if link == NONE && self.let_bit(2 * u64::from(w)) {
                link = w;
            }
            match self.vals[w as usize] {
                Val::Ind(t) => w = t,
                _ => break,
            }
        }
        if link == NONE || matches!(self.vals[w as usize], Val::Nat(_)) {
            return Ok(true);
        }
        // Already reduced by another route: folding costs nothing more.
        if !matches!(self.vals[w as usize], Val::Delayed { .. })
            && self.meta[w as usize].whnf != NONE
        {
            return Ok(true);
        }
        if self.let_bit(2 * u64::from(link) + 1) {
            return Ok(false);
        }
        let saved = self.bounds;
        let room = self.limit.saturating_sub(self.steps) / 2;
        if room == 0 {
            return Ok(false);
        }
        let full = room >= LET_FOLD_BUDGET;
        let depth = self.binders.len();
        self.limit_total(self.steps.saturating_add(LET_FOLD_BUDGET.min(room)));
        let r = self.whnf(v);
        self.restore_bounds(saved);
        self.binders.truncate(depth);
        match r {
            Ok(_) => Ok(true),
            // Our own allowance ran out: no fold. An outer allowance
            // propagates.
            Err(KErr::Abort) if self.steps <= self.limit => {
                if full {
                    self.set_let_bit(2 * u64::from(link) + 1)?;
                }
                Ok(false)
            }
            Err(e) => Err(e),
        }
    }
    /// A natural literal for `v`. Inside `lazy_delta` (`lazy`), a let-bound
    /// operand is reduced only within `LET_FOLD_BUDGET`; past it there is no
    /// literal, and lazy delta continues by unfolding.
    fn nat_value_in(&mut self, v: u32, lazy: bool) -> R<Option<NatLit>> {
        if lazy && !self.let_fold_allowed(v)? {
            return Ok(None);
        }
        let w = self.whnf(v)?;
        match self.vals[w as usize] {
            Val::Nat(n) => Ok(Some(self.nats[n as usize].dup()?)),
            Val::Const { ci, spine: 0, .. } => {
                if let Some((_, zero, _)) = self.nat_ctors()?
                    && ci == zero
                {
                    return Ok(Some(NatLit::Small(0)));
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }
    // Optional-query admission, never a closedness certificate. A reached
    // open case withholds the fold; an inspection-cap exit retains the old
    // query under its existing budgets/errors. No value is forced here and
    // neither Boolean result grants equality, inequality or checkedness.
    fn admit_native_query(&mut self, root: u32) -> R<bool> {
        fn offer(stack: &mut [u32; 128], len: &mut usize, value: u32) -> bool {
            if *len == stack.len() {
                return false;
            }
            stack[*len] = value;
            *len += 1;
            true
        }
        let mut stack = [0; 128];
        stack[0] = root;
        let (mut len, mut visits) = (1, 0);
        while len != 0 {
            if visits == 128 {
                return Ok(true);
            }
            visits += 1;
            self.step()?;
            len -= 1;
            let value = self.vals[stack[len] as usize];
            let (mut env, loose, mut spine) = match value {
                Val::Local { .. } => return Ok(false),
                Val::Ind(v) | Val::Proj { x: v, .. } => {
                    if !offer(&mut stack, &mut len, v) {
                        return Ok(true);
                    }
                    continue;
                }
                Val::Delayed { e, env, .. } => {
                    let node = self.exprs.get(e, self.b)?;
                    if node.has_free() {
                        return Ok(false);
                    }
                    (env, node.loose_range(), 0)
                }
                Val::Lam(c) | Val::Pi(c) | Val::LamTy(c) => {
                    let dom = self.exprs.get(c.dom, self.b)?;
                    let body = self.exprs.get(c.body, self.b)?;
                    if dom.has_free() || body.has_free() {
                        return Ok(false);
                    }
                    let r = dom.loose_range().max(body.loose_range().saturating_sub(1));
                    (c.env, r, 0)
                }
                Val::Arrow { dom, cod } => {
                    if !offer(&mut stack, &mut len, dom) || !offer(&mut stack, &mut len, cod) {
                        return Ok(true);
                    }
                    continue;
                }
                Val::Const { spine, .. } => (0, 0, spine),
                Val::Sort(_) | Val::Nat(_) | Val::Str(_) => continue,
            };
            if loose > 128 || self.cells[spine as usize].len > 128 {
                return Ok(true);
            }
            self.steps_by(u64::from(loose) + u64::from(self.cells[spine as usize].len))?;
            for _ in 0..loose {
                if env == 0 {
                    return Ok(false);
                }
                let node = self.envs[env as usize];
                if !offer(&mut stack, &mut len, node.val) {
                    return Ok(true);
                }
                if matches!(value, Val::LamTy(_))
                    && node.ty != NONE
                    && !offer(&mut stack, &mut len, node.ty)
                {
                    return Ok(true);
                }
                env = node.parent;
            }
            while spine != 0 {
                let cell = self.cells[spine as usize];
                if cell.tag == 0 && !offer(&mut stack, &mut len, cell.item) {
                    return Ok(true);
                }
                spine = cell.prev;
            }
        }
        Ok(true)
    }
    fn nat_reduce(&mut self, v: u32) -> R<Option<u32>> {
        self.nat_reduce_in(v, false)
    }
    // Keep refusal on the conversion path small. Non-unary/non-binary
    // constants already fail both guards below without a query or charge.
    #[inline(always)]
    fn nat_reduce_in(&mut self, v: u32, lazy: bool) -> R<Option<u32>> {
        let Val::Const { ci, spine, .. } = self.vals[v as usize] else {
            return Ok(None);
        };
        let count = self.cells[spine as usize].len;
        if count != 1 && count != 2 {
            return Ok(None);
        }
        self.nat_reduce_candidate(v, lazy, ci, spine)
    }
    #[inline(never)]
    fn nat_reduce_candidate(&mut self, v: u32, lazy: bool, ci: u32, spine: u32) -> R<Option<u32>> {
        // `Nat.succ` of a literal is the next literal (Lean's reduce_nat).
        if self.cells[spine as usize].len == 1
            && let Some((_, _, succ)) = self.nat_ctors()?
            && ci == succ
        {
            let Some(arg) = self.arg_item(spine) else {
                return Ok(None);
            };
            if lazy && !self.admit_native_query(v)? {
                return Ok(None);
            }
            if let Some(x) = self.nat_value_in(arg, lazy)? {
                let next = match x {
                    NatLit::Small(n) if n < u64::MAX => NatLit::Small(n + 1),
                    other => {
                        let d = nat_digits(&other)?;
                        match crate::check::natural::successor(&d, self.b) {
                            Ok(d) => {
                                let lit = parse_nat(d.as_bytes(), self.b, &mut self.reserved);
                                d.retire(self.b)?;
                                lit?
                            }
                            Err(crate::check::natural::Error::Resource(e)) => return Err(e.into()),
                            Err(_) => return Ok(None),
                        }
                    }
                };
                return Ok(Some(self.nat(next)?));
            }
            return Ok(None);
        }
        if self.cells[spine as usize].len != 2 || !self.const_view(ci)?.params.is_empty() {
            return Ok(None);
        }
        let op = self.natop(ci)?;
        let pred = if op.is_none() {
            self.natpred(ci)?
        } else {
            None
        };
        if op.is_none() && pred.is_none() {
            return Ok(None);
        }
        if lazy && !self.admit_native_query(v)? {
            return Ok(None);
        }
        let Some(args) = self.spine_args_opt(spine)? else {
            return Ok(None);
        };
        let (a, c) = (args[0], args[1]);
        self.recycle(args)?;
        let Some(x) = self.nat_value_in(a, lazy)? else {
            return Ok(None);
        };
        let Some(y) = self.nat_value_in(c, lazy)? else {
            return Ok(None);
        };
        let Some(op) = op else {
            let equality = pred == Some(true);
            let (xs, ys) = (nat_digits(&x)?, nat_digits(&y)?);
            self.b.charge_work((xs.len() + ys.len() + 4) as u64)?;
            let order = xs.len().cmp(&ys.len()).then_with(|| xs.cmp(&ys));
            let answer = if equality {
                order.is_eq()
            } else {
                !order.is_gt()
            };
            let Some(name) = self.env.natural_predicate_constructor(answer) else {
                return no();
            };
            let bci = self.const_info(name)?;
            return Ok(Some(self.push(Val::Const {
                ci: bci,
                li: 0,
                spine: 0,
            })?));
        };
        // At most 129 machine remainders for u64 Euclid, admitted once.
        if op == crate::check::natural::Operation::Gcd {
            self.steps_by(129)?;
        }
        let r = match nat_small(op, &x, &y) {
            Some(r) => NatLit::Small(r),
            None => {
                let (xs, ys) = (nat_digits(&x)?, nat_digits(&y)?);
                match crate::check::natural::arithmetic(op, &xs, &ys, self.b) {
                    Ok(d) => {
                        let lit = parse_nat(d.as_bytes(), self.b, &mut self.reserved);
                        d.retire(self.b)?;
                        lit?
                    }
                    Err(crate::check::natural::Error::Resource(e)) => return Err(e.into()),
                    Err(crate::check::natural::Error::Unsupported) => {
                        return Err(KErr::LiteralArithmetic);
                    }
                }
            }
        };
        Ok(Some(self.nat(r)?))
    }
    /// `Quot.lift f h (Quot.mk r a) ↦ f a` and `Quot.ind h (Quot.mk r a) ↦ h a`.
    fn quot_reduce(&mut self, ci: u32, spine: u32) -> R<Option<u32>> {
        let (major_at, f_at) = match self.const_view(ci)?.quot {
            Some(QuotientRole::Lift) => (5usize, 3usize),
            Some(QuotientRole::Induction) => (4, 3),
            _ => return Ok(None),
        };
        if (self.cells[spine as usize].len as usize) <= major_at {
            return Ok(None);
        }
        let Some(args) = self.spine_args_opt(spine)? else {
            return Ok(None);
        };
        let res = (|| {
            let q = self.whnf(args[major_at])?;
            let Val::Const {
                ci: mk, spine: ms, ..
            } = self.vals[q as usize]
            else {
                return Ok(None);
            };
            if self.const_view(mk)?.quot != Some(QuotientRole::Constructor)
                || self.cells[ms as usize].len != 3
            {
                return Ok(None);
            }
            let Some(a) = self.arg_item(ms) else {
                return Ok(None);
            };
            let mut all = self.scratch.pop().unwrap_or_default();
            all.clear();
            let result = (|| {
                self.scratch_room(&mut all, args.len() - major_at)?;
                all.push(a);
                all.extend_from_slice(&args[major_at + 1..]);
                self.apply_many(args[f_at], &all).map(Some)
            })();
            self.scratch_finish(result, [all])
        })();
        self.scratch_finish(res, [args])
    }
    fn iota(&mut self, ci: u32, li: u32, spine: u32) -> R<Option<u32>> {
        let Some(rec) = self.const_view(ci)?.rec else {
            return Ok(None);
        };
        let major_at = (rec.common + rec.nidx) as usize;
        if (self.cells[spine as usize].len as usize) <= major_at {
            return Ok(None);
        }
        // A projected recursor application: reduce the application below the
        // first projection, then replay the projections and later arguments.
        if let Some(prefix) = self.proj_prefix(spine) {
            return match self.iota(ci, li, prefix)? {
                Some(r) => Ok(Some(self.replay_from(r, spine, prefix)?)),
                None => Ok(None),
            };
        }
        let args = self.spine_args(spine)?;
        let r = self.iota_args(ci, li, rec, &args, major_at);
        self.scratch_finish(r, [args])
    }
    fn iota_args(
        &mut self,
        ci: u32,
        li: u32,
        rec: Rec<'e>,
        args: &[u32],
        major_at: usize,
    ) -> R<Option<u32>> {
        // A checked major need not normalize. For eligible structure families,
        // eta exposes the constructor without demanding its fields.
        let mut ctor = None;
        if rec.eta {
            let original = self.force(args[major_at])?;
            ctor = self.ctor_app(original, rec.family)?;
            if ctor.is_none() {
                // Completed exact-value memos retain the graph's typed context.
                // Reuse an ordinary constructor before allocating eta fields;
                // a miss requests no new normalization and proves nothing.
                for cached in [
                    self.meta[original as usize].whnf,
                    self.meta[original as usize].core,
                ] {
                    if cached != NONE {
                        ctor = self.ctor_app(cached, rec.family)?;
                        if ctor.is_some() {
                            break;
                        }
                    }
                }
                if ctor.is_none() {
                    ctor = self.struct_ctor(original, rec.family)?;
                }
            }
        }
        // K first, on the major as it stands: a proof premise of a K-like
        // family is never reduced when its type already fixes the
        // constructor. `k_ctor` admits the constructor only after
        // its type is definitionally equal to the major's, so trying it
        // before reduction adds no rule; on a refusal reduction continues.
        if ctor.is_none() && rec.k {
            let original = self.force(args[major_at])?;
            ctor = self.ctor_app(original, rec.family)?;
            // Completed results for these exact graph values only: a miss
            // requests no normalization and proves nothing.
            for cached in [
                self.meta[original as usize].whnf,
                self.meta[original as usize].core,
            ] {
                if ctor.is_none() && cached != NONE {
                    ctor = self.ctor_app(cached, rec.family)?;
                }
            }
            if ctor.is_none() {
                ctor = self.k_ctor(original, rec, li)?;
            }
        }
        if ctor.is_none() {
            let mut major = self.whnf(args[major_at])?;
            if let Val::Str(e) = self.vals[major as usize] {
                let x = self.expand_str(e)?;
                major = self.whnf(x)?;
            }
            if let Val::Nat(n) = self.vals[major as usize]
                && let Some((nat, zero, succ)) = self.nat_ctors()?
                && self.const_view(nat)?.canon == rec.family
            {
                major = match self.nats[n as usize].dup()? {
                    NatLit::Small(0) => self.push(Val::Const {
                        ci: zero,
                        li: 0,
                        spine: 0,
                    })?,
                    lit => {
                        let pred = nat_pred(&lit, self.b, &mut self.reserved)?;
                        let pred = self.nat(pred)?;
                        let spine = self.cell(0, pred, 0)?;
                        self.push(Val::Const {
                            ci: succ,
                            li: 0,
                            spine,
                        })?
                    }
                };
            }
            ctor = self.ctor_app(major, rec.family)?;
            if ctor.is_none() && rec.k {
                ctor = self.k_ctor(major, rec, li)?;
            }
            if ctor.is_none() {
                ctor = self.struct_ctor(major, rec.family)?;
            }
        }
        let Some((cci, cspine)) = ctor else {
            return Ok(None);
        };
        let ccanon = self.const_view(cci)?.canon;
        let mut found = None;
        for (i, rule) in rec.rules.iter().enumerate() {
            if self.canon(rule.constructor)? == ccanon {
                found = Some((i as u32, *rule));
                break;
            }
        }
        let Some((index, rule)) = found else {
            return Ok(None);
        };
        let Some(cargs) = self.spine_args_opt(cspine)? else {
            return Ok(None);
        };
        if cargs.len() != (rec.cparams + rule.num_fields) as usize {
            self.recycle(cargs)?;
            return Ok(None);
        }
        let res = (|| {
            let key = (ci, li, index);
            let rhs = match self.rule_rhs.get(&key) {
                Some(&v) => v,
                None => {
                    let v = self.eval(rule.rhs, 0, li)?;
                    map_put(self.b, &mut self.reserved, &mut self.rule_rhs, key, v)?;
                    v
                }
            };
            let mut all = self.scratch.pop().unwrap_or_default();
            all.clear();
            let res = (|| {
                self.scratch_room(&mut all, args.len() + cargs.len())?;
                all.extend_from_slice(&args[..rec.common as usize]);
                all.extend_from_slice(&cargs[rec.cparams as usize..]);
                all.extend_from_slice(&args[major_at + 1..]);
                self.apply_many(rhs, &all)
            })();
            self.scratch_finish(res.map(Some), [all])
        })();
        self.scratch_finish(res, [cargs])
    }
    fn ctor_app(&mut self, v: u32, family: u32) -> R<Option<(u32, u32)>> {
        if let Val::Const { ci, spine, .. } = self.vals[v as usize]
            && let Some((fam, _)) = self.const_view(ci)?.ctor
            && fam == family
        {
            return Ok(Some((ci, spine)));
        }
        Ok(None)
    }
    /// K: a major of the right type is replaced by the unique field-free constructor.
    fn k_ctor(&mut self, major: u32, rec: Rec<'e>, _li: u32) -> R<Option<(u32, u32)>> {
        let Some(rule) = rec.rules.first().copied() else {
            return Ok(None);
        };
        if rule.num_fields != 0 {
            return Ok(None);
        }
        let Some(ty) = self.infer_value(major)? else {
            return Ok(None);
        };
        let ty = self.whnf(ty)?;
        let Val::Const {
            ci: ind,
            li: ind_li,
            spine,
        } = self.vals[ty as usize]
        else {
            return Ok(None);
        };
        let Some(info) = self.const_view(ind)?.ind else {
            return Ok(None);
        };
        if self.const_view(ind)?.canon != rec.family {
            return Ok(None);
        }
        let Some(args) = self.spine_args_opt(spine)? else {
            return Ok(None);
        };
        if args.len() != (info.nparams + info.nidx) as usize {
            self.recycle(args)?;
            return Ok(None);
        }
        let res = (|| {
            let cci = self.const_info(rule.constructor)?;
            let cli = self.rebind_instance(cci, ind_li)?;
            let c = self.push(Val::Const {
                ci: cci,
                li: cli,
                spine: 0,
            })?;
            let mut cspine = 0;
            for &p in &args[..info.nparams as usize] {
                cspine = self.cell(cspine, p, 0)?;
            }
            Ok((c, cspine, cci, cli))
        })();
        let (mut c, cspine, cci, cli) = self.scratch_finish(res, [args])?;
        if cspine != 0 {
            c = self.push(Val::Const {
                ci: cci,
                li: cli,
                spine: cspine,
            })?;
        }
        let Some(cty) = self.infer_value(c)? else {
            return Ok(None);
        };
        if !self.defeq(cty, ty)? {
            return Ok(None);
        }
        Ok(Some((cci, cspine)))
    }
    /// Structure eta for iota: expand a non-constructor major of a structure type.
    fn struct_ctor(&mut self, major: u32, family: u32) -> R<Option<(u32, u32)>> {
        if !matches!(
            self.vals[major as usize],
            Val::Local { .. } | Val::Const { .. }
        ) {
            return Ok(None);
        }
        // A warm ineligible family still avoids type observation. A cold
        // metadata slot is not evidence of ineligibility: observing the major's
        // type can itself load its committed family.
        if let Some(&fci) = self.const_by_canon.get(&family)
            && !self
                .const_view(fci)?
                .ind
                .is_some_and(|info| info.structure_like())
        {
            return Ok(None);
        }
        let Some(ty) = self.infer_value(major)? else {
            return Ok(None);
        };
        let ty = self.whnf(ty)?;
        let Val::Const {
            ci: ind,
            li: ind_li,
            spine,
        } = self.vals[ty as usize]
        else {
            return Ok(None);
        };
        // The exposed type supplies both the validated metadata and the family
        // identity. No cache entry or incomplete observation supplies authority.
        let fci = ind;
        if self.const_view(fci)?.canon != family {
            return Ok(None);
        }
        let Some(info) = self.const_view(fci)?.ind else {
            return Ok(None);
        };
        if !info.structure_like() {
            return Ok(None);
        }
        let Some(prop) = self.prop_status(ty)? else {
            return Ok(None);
        };
        let Some(params) = self.spine_args_opt(spine)? else {
            return Ok(None);
        };
        if params.len() != info.nparams as usize {
            self.recycle(params)?;
            return Ok(None);
        }
        let result = (|| {
            let rule = info.ctors[0];
            let cci = self.const_info(rule.constructor)?;
            let cli = self.rebind_instance(cci, ind_li)?;
            let mut telescope = self.const_type(cci, cli)?;
            let mut cspine = 0;
            for &p in params.iter() {
                cspine = self.cell(cspine, p, 0)?;
                let binder = self.pi_like(telescope)?;
                telescope = self.instantiate(binder, p)?;
            }
            for i in 0..rule.num_fields {
                let binder = self.pi_like(telescope)?;
                let field_type = self.binder_dom(binder)?;
                if prop && self.prop_status(field_type)? != Some(true) {
                    return Ok(None);
                }
                // Construction invariant: exact validated family/arity and this
                // instantiated constructor telescope justify the projection.
                // Prop projections admit proof fields only. Do not call proj:
                // it would WHNF the very major eta is intended not to demand.
                let field = self.push(Val::Proj {
                    x: major,
                    idx: i,
                    sci: fci,
                })?;
                self.meta[field as usize].ty = field_type;
                cspine = self.cell(cspine, field, 0)?;
                // Only a later field consumes this instantiated telescope.
                // Committed constructor validation already checks its result family.
                if i + 1 < rule.num_fields {
                    telescope = self.instantiate(binder, field)?;
                }
            }
            Ok(Some((cci, cspine)))
        })();
        self.scratch_finish(result, [params])
    }

    // ---------- inference ----------

    fn sort_of(&mut self, ty: u32) -> R<LevelId> {
        let w = self.whnf(ty)?;
        match self.vals[w as usize] {
            Val::Sort(l) => Ok(l),
            _ => no(),
        }
    }
    fn pi_like(&mut self, ty: u32) -> R<u32> {
        let w = self.whnf(ty)?;
        match self.vals[w as usize] {
            Val::Pi(_) | Val::LamTy(_) | Val::Arrow { .. } => Ok(w),
            _ => no(),
        }
    }
    // Review trial: completed checked source judgments may be
    // transported under an injective renaming of exactly referenced locals.
    // Domains are exact closed types; aliases and universe instances match.
    // This is dependency metadata, never permission to evaluate syntax.
    fn known_support(&mut self, e: ExprId) -> R<Option<u64>> {
        let node = self.exprs.get(e, self.b)?;
        let r = node.loose_range();
        let mask = match r {
            0 => 0,
            1 => 1,
            64.. => u64::MAX,
            // The store increments every composite depth. Positive range with
            // depth zero therefore identifies a Bound node exactly.
            _ if node.depth() == 0 => 1u64 << (r - 1),
            _ => return Ok(self.source_support.get(&e.slot()).copied()),
        };
        Ok(Some(mask))
    }
    fn source_support(&mut self, e: ExprId) -> R<u64> {
        if let Some(m) = self.known_support(e)? {
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
    fn alpha_key(
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
    fn rename_value(
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
    // With check=false, callers supply a well-typed-input/substitution premise;
    // this computes an intrinsic type and grants no checked-entry receipt.
    #[inline(always)]
    fn infer(&mut self, e: ExprId, env: u32, li: u32, check: bool) -> R<u32> {
        let node = self.exprs.get(e, self.b)?;
        let env_key = if node.loose_range() == 0 { 0 } else { env };
        let key = (e.slot(), env_key, li);
        if let Some(&(t, checked)) = self.infer_cache.get(&key)
            && (checked || !check)
        {
            return Ok(t);
        }
        self.infer_miss(e, env, li, check, node, key)
    }
    // Construction contract: node is the unchanged source e read by infer,
    // and key is its original normalized environment/universe inference key.
    // All cache guards and the initial query precede this call; the original
    // miss work, errors, charges and publication order remain below.
    #[inline(never)]
    fn infer_miss(
        &mut self,
        e: ExprId,
        env: u32,
        li: u32,
        check: bool,
        node: Expression<'w>,
        key: (u32, u32, u32),
    ) -> R<u32> {
        // At most eight free slots cannot form a large key; an index above
        // 255 makes the complete mask unknown. Skip only impossible keys,
        // avoiding preparation work/charges that we no longer perform.
        let large_key = if self.steps >= ALPHA_MIN_STEPS
            && node.depth() != 0
            && (9..=256).contains(&node.loose_range())
        {
            self.large_type_key(e, env, li, check)?
        } else {
            None
        };
        if let Some(ref k) = large_key
            && let Some(&t) = self.large_read_types.get(k)
        {
            return Ok(t);
        }
        let alpha = if check && self.steps >= ALPHA_MIN_STEPS && node.depth() != 0 {
            self.alpha_key(e, env, li, node.loose_range())?
        } else {
            None
        };
        if let Some((k, new)) = alpha
            && let Some(&(t, old)) = self.alpha_types.get(&k)
        {
            let rk = (k.2, old, new);
            let rn = match self.rename_ids.get(&rk) {
                Some(&n) => n,
                None => {
                    let n = self.rename_ids.len() as u32;
                    map_put(self.b, &mut self.reserved, &mut self.rename_ids, rk, n)?;
                    n
                }
            };
            match self.rename_value(t, rn, &old, &new, k.2) {
                Ok(v) => {
                    map_put(
                        self.b,
                        &mut self.reserved,
                        &mut self.infer_cache,
                        key,
                        (v, true),
                    )?;
                    return Ok(v);
                }
                Err(KErr::Unsupported) => {}
                Err(e) => return Err(e),
            }
        }
        self.enter()?;
        // Introspection event only; a no-op in production builds.
        self.b.observe(crate::resource::Event::Inferences, 1);
        let r = self.infer_inner(e, env, li, check, node);
        self.leave();
        let t = r?;
        if let Some(k) = large_key {
            map_put(self.b, &mut self.reserved, &mut self.large_read_types, k, t)?;
        }
        if let Some((key, ids)) = alpha {
            map_put(
                self.b,
                &mut self.reserved,
                &mut self.alpha_types,
                key,
                (t, ids),
            )?;
        }
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.infer_cache,
            key,
            (t, check),
        )?;
        Ok(t)
    }
    fn infer_inner(
        &mut self,
        e: ExprId,
        env: u32,
        li: u32,
        check: bool,
        node: Expression<'w>,
    ) -> R<u32> {
        // Construction contract: node is the same self.exprs slot e that the
        // inference wrapper read before its unchanged cache/checkedness probes.
        let kind = node.kind(self.exprs, self.levels, self.b)?;
        match kind {
            ExprKind::Free(id) => {
                let Some(context) = self.checked_context else {
                    return no();
                };
                let local = context.get(id, self.b)?;
                self.eval(local.ty(), 0, 0)
            }
            ExprKind::Bound(i) => {
                let n = self.env_at(env, i)?;
                if n.ty != NONE {
                    Ok(n.ty)
                } else {
                    self.infer_value(n.val)?.map_or_else(no, Ok)
                }
            }
            ExprKind::Sort(l) => {
                let l = self.subst_level(l, li)?;
                let s = self.succ(l)?;
                self.push(Val::Sort(s))
            }
            ExprKind::Constant(n, ls) => {
                let ci = self.const_info(n)?;
                if check {
                    let env = self.env;
                    env.check_use(
                        &ConstantUse {
                            name: n,
                            arguments: ls,
                            parameters: self.params,
                            before: self.before,
                            formation: self.formation,
                            mode: self.mode,
                            expression_end: self.expression_end,
                            level_end: self.level_end,
                        },
                        self.levels,
                        self.names,
                        self.b,
                    )
                    .or_else(|e| match e {
                        UseError::Resource(e) => Err(e.into()),
                        _ => no(),
                    })?;
                }
                // Common universe lists stay on the stack. Rare longer lists
                // use a charged temporary buffer without a fixed arity cap.
                if ls.len() != self.const_view(ci)?.params.len() {
                    return no();
                }
                if ls.len() > LEVEL_ARGS {
                    let cli = self.wide_instance(ci, ls, li)?;
                    return self.const_type(ci, cli);
                }
                let mut buf = [LevelId::ZERO; LEVEL_ARGS];
                for (slot, &l) in buf.iter_mut().zip(ls) {
                    let l = self.subst_level(l, li)?;
                    *slot = self.canon_level(l)?;
                }
                let levels = &buf[..ls.len()];
                let cli = self.intern_li(ci, levels)?;
                self.const_type(ci, cli)
            }
            ExprKind::App(..) => {
                let mut args = self.scratch.pop().unwrap_or_default();
                args.clear();
                let res = (|| {
                    let mut head = e;
                    while let ExprKind::App(f, a) =
                        self.exprs
                            .get(head, self.b)?
                            .kind(self.exprs, self.levels, self.b)?
                    {
                        self.scratch_room(&mut args, 1)?;
                        args.push(a.slot());
                        head = f;
                    }
                    let mut fty = self.infer(head, env, li, check)?;
                    // Syntactic Pi telescope. `pending` is a Pi whose
                    // closure was never built: it denotes exactly the Pi value
                    // `instantiate` would return (evaluating a syntactic Pi
                    // gives that closure, and a Pi closure is its own weak head
                    // normal form). Private loop state, never published.
                    let mut pending: Option<Clo> = None;
                    for i in (0..args.len()).rev() {
                        let a = ExprId::from_stored_original(args[i]);
                        let pi = match pending.take() {
                            Some(c) => c,
                            None => {
                                let w = self.pi_like(fty)?;
                                match self.vals[w as usize] {
                                    Val::Pi(c) => c,
                                    // Lambda types and arrows: the ordinary rule.
                                    _ => {
                                        if check {
                                            let dom = self.binder_dom(w)?;
                                            self.check_expr(a, dom, env)?;
                                        }
                                        let av = self.thunk(a, env, li)?;
                                        fty = self.instantiate(w, av)?;
                                        continue;
                                    }
                                }
                            }
                        };
                        if check {
                            let dom = self.eval(pi.dom, pi.env, pi.li)?;
                            self.check_expr(a, dom, env)?;
                        }
                        let av = self.thunk(a, env, li)?;
                        let bound = self.env_push(pi.env, av, NONE)?;
                        if i != 0
                            && let ExprKind::Pi(_, dom, body, _) = self
                                .exprs
                                .get(pi.body, self.b)?
                                .kind(self.exprs, self.levels, self.b)?
                        {
                            pending = Some(Clo {
                                dom,
                                body,
                                env: bound,
                                li: pi.li,
                            });
                        } else {
                            fty = self.eval(pi.body, bound, pi.li)?;
                        }
                    }
                    // The last argument always evaluates its codomain.
                    debug_assert!(pending.is_none());
                    Ok(fty)
                })();
                self.scratch_finish(res, [args])
            }
            ExprKind::Lambda(_, d, body, _) => {
                if check {
                    let dt = self.infer(d, env, li, true)?;
                    self.sort_of(dt)?;
                    let dv = self.eval(d, env, li)?;
                    let x = self.open_local(dv)?;
                    let env2 = self.env_push(env, x, dv)?;
                    let bt = self.infer(body, env2, li, true);
                    self.close_local();
                    let bt = bt?;
                    if !self.mentions(bt, x)? {
                        return self.push(Val::Arrow { dom: dv, cod: bt });
                    }
                }
                let loose = self.exprs.get(e, self.b)?.loose_range();
                let c = Clo {
                    dom: d,
                    body,
                    env,
                    li,
                };
                self.push_clo(2, c, loose)
            }
            ExprKind::Pi(_, d, body, _) => {
                let dt = self.infer(d, env, li, check)?;
                let u = self.sort_of(dt)?;
                let dv = self.eval(d, env, li)?;
                let x = self.open_local(dv)?;
                let env2 = self.env_push(env, x, dv)?;
                let bt = self
                    .infer(body, env2, li, check)
                    .and_then(|bt| self.sort_of(bt));
                self.close_local();
                let v = bt?;
                let l = self.imax(u, v)?;
                self.push(Val::Sort(l))
            }
            ExprKind::Let(_, t, v, body, _) => {
                if check {
                    let tt = self.infer(t, env, li, true)?;
                    self.sort_of(tt)?;
                }
                let tv = self.eval(t, env, li)?;
                if check {
                    self.check_expr(v, tv, env)?;
                }
                let vv = self.thunk(v, env, li)?;
                self.mark_let(vv)?;
                let env2 = self.env_push(env, vv, tv)?;
                self.infer(body, env2, li, check)
            }
            ExprKind::Projection(s, idx, x) => {
                let sci = self.const_info(s)?;
                let xt = self.infer(x, env, li, check)?;
                let xv = self.thunk(x, env, li)?;
                self.proj_type(xv, xt, idx, sci, check)
            }
            ExprKind::Natural(_) => self.nat_type(),
            ExprKind::String(_) => self.str_type(),
            _ => no(),
        }
    }
    fn proj_type(&mut self, xv: u32, xt: u32, idx: u32, sci: u32, check: bool) -> R<u32> {
        let w = self.whnf(xt)?;
        let Val::Const { ci, li, spine } = self.vals[w as usize] else {
            return no();
        };
        if ci != sci {
            return no();
        }
        let Some(ind) = self.const_view(ci)?.ind else {
            return no();
        };
        // Lean types a projection of any one-constructor family without
        // indices, recursive or not; only eta-like rules need `structure_like`.
        if ind.ctors.len() != 1 || ind.nidx != 0 || idx >= ind.ctors[0].num_fields {
            return no();
        }
        // A structure whose sort does not reduce to a Sort is left to the
        // existing checker (lean4#14807). Out of a proposition, only
        // proof fields may be projected; every earlier field is required to be a
        // proof too, a conservative superset of the fields the type depends on.
        let prop = match self.prop_status(w)? {
            Some(p) => p,
            None if check => return no(),
            None => false,
        };
        let params = self.spine_args(spine)?;
        if params.len() != ind.nparams as usize {
            self.recycle(params)?;
            return no();
        }
        let res = (|| {
            let cci = self.const_info(ind.ctors[0].constructor)?;
            let cli = self.rebind_instance(cci, li)?;
            let mut t = self.const_type(cci, cli)?;
            for &p in params.iter() {
                let pw = self.pi_like(t)?;
                t = self.instantiate(pw, p)?;
            }
            for j in 0..idx {
                let pw = self.pi_like(t)?;
                if check && prop {
                    let fd = self.binder_dom(pw)?;
                    if self.prop_status(fd)? != Some(true) {
                        return no();
                    }
                }
                let f = self.proj(xv, j, sci)?;
                t = self.instantiate(pw, f)?;
            }
            let pw = self.pi_like(t)?;
            let field = self.binder_dom(pw)?;
            if check && prop && self.prop_status(field)? != Some(true) {
                return no();
            }
            Ok(field)
        })();
        self.scratch_finish(res, [params])
    }
    fn check_expr(&mut self, e: ExprId, ty: u32, env: u32) -> R<()> {
        self.enter()?;
        let r = self.check_inner(e, ty, env);
        self.leave();
        r
    }
    fn check_inner(&mut self, e: ExprId, ty: u32, env: u32) -> R<()> {
        let kind = self
            .exprs
            .get(e, self.b)?
            .kind(self.exprs, self.levels, self.b)?;
        match kind {
            ExprKind::Lambda(_, d, body, _) => {
                let loose = self.exprs.get(e, self.b)?.loose_range();
                let key = (e.slot(), if loose == 0 { 0 } else { env }, 0);
                // A lambda already checked in this environment (DAG sharing)
                // only needs its recorded type compared with this one.
                let seen = matches!(self.infer_cache.get(&key), Some(&(_, true)));
                let w = self.whnf(ty)?;
                if !seen
                    && matches!(
                        self.vals[w as usize],
                        Val::Pi(_) | Val::LamTy(_) | Val::Arrow { .. }
                    )
                {
                    let dt = self.infer(d, env, 0, true)?;
                    self.sort_of(dt)?;
                    let dv = self.eval(d, env, 0)?;
                    let pd = self.binder_dom(w)?;
                    if !self.defeq(dv, pd)? {
                        return no();
                    }
                    let x = self.open_local(dv)?;
                    let r = self.instantiate(w, x).and_then(|cod| {
                        let env2 = self.env_push(env, x, dv)?;
                        self.check_expr(body, cod, env2)
                    });
                    self.close_local();
                    r?;
                    // The body is checked under a fresh local of this domain,
                    // so the lambda's own type is a checked inference result.
                    let lt = self.push(Val::LamTy(Clo {
                        dom: d,
                        body,
                        env: key.1,
                        li: 0,
                    }))?;
                    map_put(
                        self.b,
                        &mut self.reserved,
                        &mut self.infer_cache,
                        key,
                        (lt, true),
                    )?;
                    return Ok(());
                }
            }
            ExprKind::Let(_, t, v, body, _) => {
                let tt = self.infer(t, env, 0, true)?;
                self.sort_of(tt)?;
                let tv = self.eval(t, env, 0)?;
                self.check_expr(v, tv, env)?;
                // Private P2 screen: a completed judgment for this closed source
                // is preserved by the unused let binding. Exact type identity
                // supplies conversion; no expected type becomes an inferred fact.
                // Open source must still be checked after shifting the context.
                if body == v && tv == ty && self.exprs.get(v, self.b)?.loose_range() == 0 {
                    return Ok(());
                }
                let vv = self.thunk(v, env, 0)?;
                self.mark_let(vv)?;
                let env2 = self.env_push(env, vv, tv)?;
                return self.check_expr(body, ty, env2);
            }
            _ => {}
        }
        let t = self.infer(e, env, 0, true)?;
        if self.defeq(t, ty)? { Ok(()) } else { no() }
    }
    /// The type of a value, when it can be computed without checking.
    fn infer_value(&mut self, v: u32) -> R<Option<u32>> {
        let v = self.force(v)?;
        let cached = self.meta[v as usize].ty;
        if cached != NONE {
            return Ok(Some(cached));
        }
        let t = match self.vals[v as usize] {
            Val::Sort(l) => {
                let s = self.succ(l)?;
                self.push(Val::Sort(s))?
            }
            Val::Nat(_) => self.nat_type()?,
            Val::Str(_) => self.str_type()?,
            Val::Lam(c) => self.push(Val::LamTy(c))?,
            Val::Pi(c) => {
                let dt = self.infer(c.dom, c.env, c.li, false)?;
                let u = self.sort_of(dt)?;
                let dv = self.eval(c.dom, c.env, c.li)?;
                let x = self.open_local(dv)?;
                let env2 = self.env_push(c.env, x, dv)?;
                let bt = self
                    .infer(c.body, env2, c.li, false)
                    .and_then(|bt| self.sort_of(bt));
                self.close_local();
                let w = bt?;
                let l = self.imax(u, w)?;
                self.push(Val::Sort(l))?
            }
            Val::LamTy(c) => {
                // Sort of `Π x : dom, typeof(body)`.
                let dt = self.infer(c.dom, c.env, c.li, false)?;
                let u = self.sort_of(dt)?;
                let dv = self.eval(c.dom, c.env, c.li)?;
                let x = self.open_local(dv)?;
                let env2 = self.env_push(c.env, x, dv)?;
                let bs = self
                    .infer(c.body, env2, c.li, false)
                    .and_then(|bt| self.infer_value(bt));
                self.close_local();
                let Some(bs) = bs? else {
                    return Ok(None);
                };
                let w = self.sort_of(bs)?;
                let l = self.imax(u, w)?;
                self.push(Val::Sort(l))?
            }
            Val::Arrow { dom, cod } => {
                let (Some(ds), Some(cs)) = (self.infer_value(dom)?, self.infer_value(cod)?) else {
                    return Ok(None);
                };
                let u = self.sort_of(ds)?;
                let w = self.sort_of(cs)?;
                let l = self.imax(u, w)?;
                self.push(Val::Sort(l))?
            }
            Val::Local { id, spine } => {
                let t = self.locals[id as usize];
                match self.spine_type(t, spine, |s, sp| s.push(Val::Local { id, spine: sp }))? {
                    Some(t) => t,
                    None => return Ok(None),
                }
            }
            Val::Const { ci, li, spine } => {
                let t = self.const_type(ci, li)?;
                match self.spine_type(t, spine, |s, sp| s.push(Val::Const { ci, li, spine: sp }))? {
                    Some(t) => t,
                    None => return Ok(None),
                }
            }
            Val::Proj { x, idx, sci } => {
                let Some(xt) = self.infer_value(x)? else {
                    return Ok(None);
                };
                match self.proj_type(x, xt, idx, sci, false) {
                    Ok(t) => t,
                    Err(KErr::Unsupported) => return Ok(None),
                    Err(e) => return Err(e),
                }
            }
            _ => return Ok(None),
        };
        self.meta[v as usize].ty = t;
        Ok(Some(t))
    }
    fn spine_type(
        &mut self,
        head_ty: u32,
        spine: u32,
        rebuild: impl Fn(&mut Self, u32) -> R<u32>,
    ) -> R<Option<u32>> {
        let items = self.spine_items(spine)?;
        let mut t = head_ty;
        let mut res = Ok(Some(()));
        for &s in &items {
            let c = self.cells[s as usize];
            let step = if c.tag == 0 {
                self.pi_like(t).and_then(|w| self.instantiate(w, c.item))
            } else {
                let prefix = c.prev;
                rebuild(self, prefix).and_then(|sv| self.proj_type(sv, t, c.tag - 1, c.item, false))
            };
            match step {
                Ok(n) => t = n,
                Err(KErr::Unsupported) => {
                    res = Ok(None);
                    break;
                }
                Err(e) => {
                    res = Err(e);
                    break;
                }
            }
        }
        self.scratch_finish(res.map(|o| o.map(|()| t)), [items])
    }
    /// Whether a type is a proposition. `None` when its sort is not known to
    /// reduce to a `Sort` (lean4#14807): a stuck sort is never "not Prop".
    fn prop_status(&mut self, ty: u32) -> R<Option<bool>> {
        let Some(s) = self.infer_value(ty)? else {
            return Ok(None);
        };
        let w = self.whnf(s)?;
        match self.vals[w as usize] {
            Val::Sort(l) => Ok(Some(self.is_zero(l)?)),
            _ => Ok(None),
        }
    }
    /// Conservative: false only if value `v` provably does not depend on the
    /// local value `x`. Values created before `x` cannot depend on it.
    fn mentions(&mut self, v: u32, x: u32) -> R<bool> {
        let Val::Local { id: xid, .. } = self.vals[x as usize] else {
            return Ok(true);
        };
        let mut stack = self.scratch.pop().unwrap_or_default();
        stack.clear();
        let res = (|| {
            // The traversal visits at most `budget` values; each pushes at most
            // its environment range and spine, so room is made per visit.
            self.scratch_room(&mut stack, 1)?;
            stack.push(v);
            let mut budget = 256u32;
            let mut found = false;
            while let Some(v) = stack.pop() {
                if v < x {
                    continue;
                }
                if budget == 0 {
                    found = true;
                    break;
                }
                budget -= 1;
                let (env, loose, spine) = match self.vals[v as usize] {
                    Val::Ind(t) => {
                        self.scratch_room(&mut stack, 1)?;
                        stack.push(t);
                        continue;
                    }
                    Val::Delayed { e, env, .. } => {
                        (env, self.exprs.get(e, self.b)?.loose_range(), 0)
                    }
                    Val::Lam(c) | Val::Pi(c) | Val::LamTy(c) => {
                        let l = self.exprs.get(c.dom, self.b)?.loose_range().max(
                            self.exprs
                                .get(c.body, self.b)?
                                .loose_range()
                                .saturating_sub(1),
                        );
                        (c.env, l, 0)
                    }
                    Val::Arrow { dom, cod } => {
                        self.scratch_room(&mut stack, 2)?;
                        stack.push(dom);
                        stack.push(cod);
                        continue;
                    }
                    Val::Proj { x, .. } => {
                        self.scratch_room(&mut stack, 1)?;
                        stack.push(x);
                        continue;
                    }
                    Val::Local { id, spine } => {
                        if id == xid {
                            found = true;
                            break;
                        }
                        (0, 0, spine)
                    }
                    Val::Const { spine, .. } => (0, 0, spine),
                    Val::Sort(_) | Val::Nat(_) | Val::Str(_) => continue,
                };
                let mut env = env;
                for _ in 0..loose {
                    if env == 0 {
                        break;
                    }
                    let n = self.envs[env as usize];
                    // A lambda type reads an entry's declared type as well.
                    self.scratch_room(&mut stack, 2)?;
                    stack.push(n.val);
                    if n.ty != NONE {
                        stack.push(n.ty);
                    }
                    env = n.parent;
                }
                let mut s = spine;
                while s != 0 {
                    let c = self.cells[s as usize];
                    if c.tag == 0 {
                        self.scratch_room(&mut stack, 1)?;
                        stack.push(c.item);
                    }
                    s = c.prev;
                }
            }
            stack.clear();
            Ok(found)
        })();
        self.scratch_finish(res, [stack])
    }
    fn is_prop_type(&mut self, ty: u32) -> R<bool> {
        Ok(self.prop_status(ty)? == Some(true))
    }
    fn is_proof(&mut self, v: u32) -> R<Option<u32>> {
        if matches!(
            self.vals[v as usize],
            Val::Sort(_)
                | Val::Pi(_)
                | Val::LamTy(_)
                | Val::Arrow { .. }
                | Val::Nat(_)
                | Val::Str(_)
        ) {
            return Ok(None);
        }
        let Some(t) = self.infer_value(v)? else {
            return Ok(None);
        };
        Ok(self.is_prop_type(t)?.then_some(t))
    }

    // ---------- definitional equality (positive) ----------

    fn defeq(&mut self, a: u32, c: u32) -> R<bool> {
        self.defeq_with(a, c, false)
    }
    /// `not_proof`: the caller knows `a`'s type is not a proposition (its
    /// sort is not zero), so proof irrelevance cannot apply to this pair and
    /// its type is not inferred. Types are preserved by reduction, so the
    /// knowledge holds for every head form `a` reduces to.
    fn defeq_with(&mut self, a: u32, c: u32, not_proof: bool) -> R<bool> {
        if a == c {
            return Ok(true);
        }
        self.enter()?;
        let r = self.defeq_inner(a, c, not_proof);
        self.leave();
        r
    }
    fn quick(&mut self, a: u32, c: u32) -> R<Option<bool>> {
        Ok(Some(match (self.vals[a as usize], self.vals[c as usize]) {
            (Val::Sort(x), Val::Sort(y)) => self.level_eq(x, y)?,
            (Val::Nat(x), Val::Nat(y)) => nat_eq(&self.nats[x as usize], &self.nats[y as usize]),
            (Val::Str(x), Val::Str(y)) => {
                let bx = match self
                    .exprs
                    .get(x, self.b)?
                    .kind(self.exprs, self.levels, self.b)?
                {
                    ExprKind::String(b) => b,
                    _ => return no(),
                };
                let by = match self
                    .exprs
                    .get(y, self.b)?
                    .kind(self.exprs, self.levels, self.b)?
                {
                    ExprKind::String(b) => b,
                    _ => return no(),
                };
                if bx == by {
                    true
                } else {
                    return Ok(None);
                }
            }
            // Equal closures of the same form denote the same value. A Pi and
            // a lambda type built from the same syntax do not: `Π x, b` is not
            // `Π x, typeof(b)`, so mixed forms always compare by binders.
            (Val::Pi(x), Val::Pi(y))
            | (Val::Lam(x), Val::Lam(y))
            | (Val::LamTy(x), Val::LamTy(y)) => {
                if x == y {
                    true
                } else {
                    self.binders(a, c)?
                }
            }
            (Val::Pi(_), Val::LamTy(_)) | (Val::LamTy(_), Val::Pi(_)) => self.binders(a, c)?,
            (Val::Arrow { .. }, Val::Pi(_) | Val::LamTy(_) | Val::Arrow { .. })
            | (Val::Pi(_) | Val::LamTy(_), Val::Arrow { .. }) => self.binders(a, c)?,
            _ => return Ok(None),
        }))
    }
    fn binders(&mut self, a: u32, c: u32) -> R<bool> {
        if let (Val::Pi(x), Val::Pi(y))
        | (Val::Lam(x), Val::Lam(y))
        | (Val::LamTy(x), Val::LamTy(y)) = (self.vals[a as usize], self.vals[c as usize])
            && (self.closure_congruent(x, y)? || self.syn_clo(x, y)?)
        {
            return Ok(true);
        }
        let da = self.binder_dom(a)?;
        let dc = self.binder_dom(c)?;
        if !self.defeq(da, dc)? {
            return Ok(false);
        }
        let x = self.open_local(da)?;
        let r = (|| {
            let ba = self.instantiate(a, x)?;
            let bc = self.instantiate(c, x)?;
            self.defeq(ba, bc)
        })();
        self.close_local();
        r
    }
    /// Same syntax needs agreement only at its referenced slots. Unknown
    /// support retains the old full-prefix sufficient condition. Environments
    /// come from valid typing/evaluation: entry types are compatible with their
    /// values; fabricated annotations would not justify LamTy congruence.
    /// Computing source support is separately charged before this local probe
    /// allowance. This helper is bounded and proves only positive congruence.
    fn env_congruent(&mut self, e1: u32, e2: u32, r: u32, mask: u64) -> R<bool> {
        if e1 == e2 {
            return Ok(true);
        }
        let saved = self.bounds;
        let depth = self.binders.len();
        self.limit_arguments(self.argument_steps().saturating_add(ARGS_BUDGET));
        let res = (|| {
            let (mut x, mut y) = (e1, e2);
            for i in 0..r {
                if x == y {
                    return Ok(true);
                }
                if x == 0 || y == 0 {
                    return Ok(false);
                }
                let (nx, ny) = (self.envs[x as usize], self.envs[y as usize]);
                if (mask == u64::MAX || (i < 64 && mask & (1u64 << i) != 0))
                    && nx.val != ny.val
                    && !self.defeq(nx.val, ny.val)?
                {
                    return Ok(false);
                }
                x = nx.parent;
                y = ny.parent;
            }
            Ok(true)
        })();
        self.restore_bounds(saved);
        self.binders.truncate(depth);
        match res {
            Ok(r) => Ok(r),
            Err(KErr::Abort) if self.steps <= self.limit => Ok(false),
            Err(e) => Err(e),
        }
    }
    /// Syntactic equality modulo environments for two closures of the same
    /// form: equal structure with equal variable values denotes equal terms,
    /// decided without instantiating or unfolding (bounded, positive-only).
    fn syn_clo(&mut self, x: Clo, y: Clo) -> R<bool> {
        if x.dom == y.dom && x.body == y.body {
            return Ok(false);
        }
        let saved = self.bounds;
        self.limit_total(self.steps.saturating_add(SYN_BUDGET));
        let r = (|| {
            if !self.syn_eq(x.dom, x.env, x.li, y.dom, y.env, y.li)? {
                return Ok(false);
            }
            let m = self.marker()?;
            let (e1, e2) = (
                self.env_push(x.env, m, NONE)?,
                self.env_push(y.env, m, NONE)?,
            );
            let r = self.syn_eq(x.body, e1, x.li, y.body, e2, y.li);
            self.markers -= 1;
            r
        })();
        self.restore_bounds(saved);
        match r {
            Ok(r) => Ok(r),
            Err(KErr::Abort) if self.steps <= self.limit => Ok(false),
            Err(e) => Err(e),
        }
    }
    fn syn_bounded(
        &mut self,
        e1: ExprId,
        v1: u32,
        l1: u32,
        e2: ExprId,
        v2: u32,
        l2: u32,
    ) -> R<bool> {
        let saved = self.bounds;
        self.limit_total(self.steps.saturating_add(SYN_BUDGET));
        let r = self.syn_eq(e1, v1, l1, e2, v2, l2);
        self.restore_bounds(saved);
        match r {
            Ok(r) => Ok(r),
            Err(KErr::Abort) if self.steps <= self.limit => Ok(false),
            Err(e) => Err(e),
        }
    }
    /// A placeholder bound to the same binder on both sides of `syn_eq`; it
    /// is compared by identity only and never evaluated or typed.
    fn marker(&mut self) -> R<u32> {
        let id = MARKER_BASE + self.markers;
        self.markers += 1;
        if let Some(&v) = self.marker_vals.get(&id) {
            return Ok(v);
        }
        let v = self.push(Val::Local { id, spine: 0 })?;
        map_put(self.b, &mut self.reserved, &mut self.marker_vals, id, v)?;
        Ok(v)
    }
    fn is_marker(&self, v: u32) -> bool {
        matches!(self.vals[v as usize], Val::Local { id, spine: 0 } if id >= MARKER_BASE)
    }
    #[allow(clippy::too_many_arguments)]
    fn syn_eq(&mut self, e1: ExprId, v1: u32, l1: u32, e2: ExprId, v2: u32, l2: u32) -> R<bool> {
        self.step()?;
        if e1 == e2 && l1 == l2 {
            let r = self.exprs.get(e1, self.b)?.loose_range();
            if r == 0 || v1 == v2 {
                return Ok(true);
            }
        }
        let key = (e1.slot(), v1, l1, e2.slot(), v2, l2);
        if self.syn_ok.contains(&key) {
            return Ok(true);
        }
        let (n1, n2) = (self.exprs.get(e1, self.b)?, self.exprs.get(e2, self.b)?);
        // Every rule below pairs nodes of one kind, so matching trees have the
        // same shape. Stored depth also counts binder-name and universe depth,
        // which this comparison ignores: a mismatch can skip a match this probe
        // would have found. The probe is optional, so that only costs the
        // ordinary route; it never makes `false` a conclusion.
        if n1.depth() != n2.depth() {
            return Ok(false);
        }
        let k1 = n1.kind(self.exprs, self.levels, self.b)?;
        let k2 = n2.kind(self.exprs, self.levels, self.b)?;
        let r = match (k1, k2) {
            (ExprKind::Bound(i), ExprKind::Bound(j)) => {
                let (a, c) = (self.env_at(v1, i)?.val, self.env_at(v2, j)?.val);
                if a == c {
                    true
                } else if self.is_marker(a) || self.is_marker(c) {
                    false
                } else {
                    self.defeq(a, c)?
                }
            }
            (ExprKind::Sort(x), ExprKind::Sort(y)) => {
                let (x, y) = (self.subst_level(x, l1)?, self.subst_level(y, l2)?);
                self.level_eq(x, y)?
            }
            (ExprKind::Constant(n1, ls1), ExprKind::Constant(n2, ls2)) => {
                if ls1.len() != ls2.len() || self.canon(n1)? != self.canon(n2)? {
                    false
                } else {
                    let mut ok = true;
                    for i in 0..ls1.len() {
                        let (x, y) = (self.subst_level(ls1[i], l1)?, self.subst_level(ls2[i], l2)?);
                        if !self.level_eq(x, y)? {
                            ok = false;
                            break;
                        }
                    }
                    ok
                }
            }
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.syn_eq(f1, v1, l1, f2, v2, l2)? && self.syn_eq(a1, v1, l1, a2, v2, l2)?
            }
            (ExprKind::Lambda(_, d1, b1, _), ExprKind::Lambda(_, d2, b2, _))
            | (ExprKind::Pi(_, d1, b1, _), ExprKind::Pi(_, d2, b2, _)) => {
                if !self.syn_eq(d1, v1, l1, d2, v2, l2)? {
                    false
                } else {
                    let m = self.marker()?;
                    let (n1, n2) = (self.env_push(v1, m, NONE)?, self.env_push(v2, m, NONE)?);
                    let r = self.syn_eq(b1, n1, l1, b2, n2, l2);
                    self.markers -= 1;
                    r?
                }
            }
            (ExprKind::Let(_, t1, x1, b1, _), ExprKind::Let(_, t2, x2, b2, _)) => {
                if !self.syn_eq(t1, v1, l1, t2, v2, l2)? || !self.syn_eq(x1, v1, l1, x2, v2, l2)? {
                    false
                } else {
                    let m = self.marker()?;
                    let (n1, n2) = (self.env_push(v1, m, NONE)?, self.env_push(v2, m, NONE)?);
                    let r = self.syn_eq(b1, n1, l1, b2, n2, l2);
                    self.markers -= 1;
                    r?
                }
            }
            (ExprKind::Projection(s1, i1, x1), ExprKind::Projection(s2, i2, x2)) => {
                i1 == i2
                    && self.canon(s1)? == self.canon(s2)?
                    && self.syn_eq(x1, v1, l1, x2, v2, l2)?
            }
            (ExprKind::Natural(x), ExprKind::Natural(y))
            | (ExprKind::String(x), ExprKind::String(y)) => x == y,
            _ => false,
        };
        if r {
            self.syn_ok.insert(key, (), self.b, &mut self.reserved)?;
        }
        Ok(r)
    }
    fn closure_congruent(&mut self, x: Clo, y: Clo) -> R<bool> {
        if x.dom != y.dom || x.body != y.body || x.li != y.li {
            return Ok(false);
        }
        let r = self.exprs.get(x.dom, self.b)?.loose_range().max(
            self.exprs
                .get(x.body, self.b)?
                .loose_range()
                .saturating_sub(1),
        );
        let d = self.source_support(x.dom)?;
        let b = self.source_support(x.body)?;
        let mask = if d == u64::MAX || b == u64::MAX {
            u64::MAX
        } else {
            d | (b >> 1)
        };
        self.env_congruent(x.env, y.env, r, mask)
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
    fn defeq_slow(&mut self, a: u32, c: u32, not_proof: bool) -> R<bool> {
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
    /// Lazy delta: unfold the side with the higher definitional priority one
    /// step at a time, trying cheap decisions after each step.
    fn lazy_delta(&mut self, mut a: u32, mut c: u32, arguments: bool) -> R<Lazy> {
        loop {
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
                        self.limit_arguments(self.argument_steps().saturating_add(ARGS_BUDGET));
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
                            Ok(true) => return Ok(Lazy::Decided(true)),
                            Ok(false) => {
                                self.args_fail
                                    .insert((a, c), (), self.b, &mut self.reserved)?;
                            }
                            // Our own allowance ran out: unfold instead, which is
                            // the complete route. An outer allowance propagates.
                            Err(KErr::Abort) if self.steps <= self.limit => {}
                            Err(e) => return Err(e),
                        }
                    }
                    if x < y {
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
    /// A projection opposite a delta head may hide the same cheap head. Expose
    /// it before demanding the opposite definition's computation.
    /// All values retain the existing validated projection-typing premises;
    /// this reduction grants no checkedness or comparison result. Each retry
    /// charges a step, and all inner normalization shares the enclosing limits.
    /// Alternative exposure and abbreviation argument comparison re-enter
    /// defeq/lazy_delta, so their one-sided projection pairs use this route too.
    fn expose_stuck_projection(&mut self, v: u32) -> R<Option<u32>> {
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
    fn try_alternative_exposure(&mut self, a: u32, c: u32) -> R<bool> {
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
    /// Isolated trial: typed congruence before iota. All production
    /// callers belong to an eligible safe, non-formation attempt. The matching
    /// committed head and compatible checked substitutions supply exactly the
    /// ordinary typed-spine premise; recursor metadata chooses order only.
    /// No failed comparison is remembered or used as a negative verdict.
    fn try_recursor_congruence(&mut self, a: u32, c: u32) -> R<bool> {
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
    fn try_abbrev_congruence(&mut self, a: u32, c: u32) -> R<bool> {
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
        self.limit_arguments(self.argument_steps().saturating_add(ARGS_BUDGET));
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
            Ok(true) => Ok(true),
            Ok(false) => {
                self.args_fail
                    .insert((a, c), (), self.b, &mut self.reserved)?;
                Ok(false)
            }
            // Respect the whole attempt's guard even if reached inside this
            // optional route. It abandons the value kernel, not the declaration.
            Err(KErr::Unsupported) if self.steps <= step_cap() => Ok(false),
            Err(KErr::Abort) if self.steps <= self.limit => Ok(false),
            Err(error) => Err(error),
        }
    }

    /// Scheduling-only recognition of an exactly applied raw field selector.
    /// Extra applications demand the selected function's arguments and do not
    /// match. This scan is bounded by cached arity and its caller's allowance;
    /// ordinary unfolding still validates and performs all projection work.
    fn abbrev_selects_field(&mut self, ci: u32, arguments: u64) -> R<bool> {
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
    fn try_projection_congruence(&mut self, a: u32, c: u32, offered: (u32, u32)) -> R<bool> {
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
    fn proj_structs(&mut self, a: u32, c: u32) -> R<bool> {
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
    fn delta_of(&mut self, v: u32) -> R<Option<(u8, u32)>> {
        Ok(match self.vals[v as usize] {
            Val::Const { ci, .. } => self.const_view(ci)?.delta,
            _ => None,
        })
    }
    // Invariant: synthetic markers belong only to syn_eq environments and
    // are never evaluated here. Cached reductions carry no checkedness.
    fn unfold_value(&mut self, v: u32) -> R<u32> {
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
    /// Arguments of two applications of the same head, root first. The head's
    /// Pi type is instantiated with the left arguments; once the earlier
    /// arguments are equal, both later arguments have the same expected type,
    /// and an argument whose expected type is a proposition is equal by proof
    /// irrelevance (all compared values come from checked terms).
    /// Bit `i` set: argument `i` of definition `ci` is absent. With the value
    /// `λ (x₀ : d₀) … (x_{k-1} : d_{k-1}), b` and the type
    /// `Π (x₀ : D₀) … (x_{k-1} : D_{k-1}), R`, `xᵢ` is absent when it is free
    /// neither in `b`, nor in any later lambda domain `d_j` (j > i), nor in the
    /// type after binder `i`. Then for any spine with more than `i` arguments,
    /// `c … aᵢ …` and `c … a'ᵢ …` unfold and beta-reduce to terms that differ
    /// only where the other arguments differ, also for a partial application
    /// whose remaining lambdas keep their domains; and the later arguments'
    /// expected types do not depend on `aᵢ`, so proof irrelevance at a later
    /// argument still compares proofs of one proposition.
    ///
    /// Support is syntactic and over-approximates use. Unknown support (a
    /// loose index at or above 63, metadata) marks that binder and every outer
    /// one present; so does a depth or stack limit while computing it. Delta
    /// must be definitional for `ci` wherever this is consulted (regular
    /// definitions in lazy delta). At most 62 binders; cached per attempt.
    fn absent_args(&mut self, ci: u32) -> R<u64> {
        if let Some(&m) = self.absent.get(&ci) {
            return Ok(m);
        }
        let m = match self.compute_absent(ci) {
            Ok(m) => m,
            Err(KErr::Unsupported) => 0,
            Err(e) => return Err(e),
        };
        map_put(self.b, &mut self.reserved, &mut self.absent, ci, m)?;
        Ok(m)
    }
    fn compute_absent(&mut self, ci: u32) -> R<u64> {
        let (Some(mut value), Some(mut ty)) = (self.const_view(ci)?.value, self.const_view(ci)?.ty)
        else {
            return Ok(0);
        };
        // Pair the value's lambdas with the type's binders, outermost first.
        let mut binders = [(value, ty); 62];
        let mut k = 0;
        while k < binders.len() {
            self.step()?;
            let v = self.exprs.get(value, self.b)?;
            let t = self.exprs.get(ty, self.b)?;
            match (
                v.kind(self.exprs, self.levels, self.b)?,
                t.kind(self.exprs, self.levels, self.b)?,
            ) {
                (ExprKind::Lambda(_, domain, body, _), ExprKind::Pi(_, _, rest, _)) => {
                    binders[k] = (domain, rest);
                    value = body;
                    ty = rest;
                    k += 1;
                }
                _ => break,
            }
        }
        // Innermost first: `read` holds the variables the value reads below
        // the current binder, which is its bit 0.
        let mut read = self.bounded_support(value)?;
        let mut absent = 0u64;
        for j in (0..k).rev() {
            if read == u64::MAX {
                break;
            }
            let (domain, rest) = binders[j];
            let mentioned = self.bounded_support(rest)?;
            if read & 1 == 0 && mentioned & 1 == 0 && mentioned != u64::MAX {
                absent |= 1u64 << j;
            }
            let d = self.bounded_support(domain)?;
            read = if d == u64::MAX { d } else { (read >> 1) | d };
        }
        Ok(absent)
    }
    /// Source support for the absent mask, within its own small allowance:
    /// a definition's body can be large and unfolding may never visit most
    /// of it. Running out gives unknown support, which marks nothing absent.
    /// Completed nodes stay in the support memo.
    fn bounded_support(&mut self, e: ExprId) -> R<u64> {
        let saved = self.bounds;
        self.limit_total(self.steps.saturating_add(MASK_BUDGET));
        let r = self.source_support(e);
        self.restore_bounds(saved);
        match r {
            Err(KErr::Abort) if self.steps <= self.limit => Ok(u64::MAX),
            r => r,
        }
    }
    fn same_spines(&mut self, a: u32, c: u32) -> R<bool> {
        Ok(self.spines(a, c, 0)? == Some(true))
    }
    /// `same_spines`, except that arguments whose bit is set in `skip` are
    /// not compared. Only `absent_args` of the shared head justifies a skip.
    fn same_spines_skipping(&mut self, a: u32, c: u32, skip: u64) -> R<bool> {
        Ok(self.spines(a, c, skip)? == Some(true))
    }
    /// `Some(true)`: equal arguments; `Some(false)`: not shown equal; `None`:
    /// a visibly distinct non-proof argument pair (`visibly_distinct`).
    fn spines(&mut self, a: u32, c: u32, skip: u64) -> R<Option<bool>> {
        let (sa, sc, head) = match (self.vals[a as usize], self.vals[c as usize]) {
            (Val::Local { id, spine: x }, Val::Local { spine: y, .. }) => (x, y, Ok(id)),
            (Val::Const { ci, li, spine: x }, Val::Const { spine: y, .. }) => (x, y, Err((ci, li))),
            _ => return Ok(Some(false)),
        };
        if self.cells[sa as usize].len != self.cells[sc as usize].len {
            return Ok(Some(false));
        }
        if sa == sc {
            return Ok(Some(true));
        }
        // Short spines are read into stack arrays: comparisons nest as deeply
        // as the terms do, beyond what the buffer pool holds.
        let n = self.cells[sa as usize].len as usize;
        if n <= SMALL_SPINE {
            let (mut xs, mut ys) = ([0u32; SMALL_SPINE], [0u32; SMALL_SPINE]);
            let (mut p, mut q) = (sa, sc);
            for i in (0..n).rev() {
                let (cp, cq) = (self.cells[p as usize], self.cells[q as usize]);
                if cp.tag != 0 || cq.tag != 0 {
                    return self.same_cells(sa, sc).map(Some);
                }
                xs[i] = cp.item;
                ys[i] = cq.item;
                p = cp.prev;
                q = cq.prev;
            }
            return self.same_args(&xs[..n], &ys[..n], head, skip);
        }
        let Some(xs) = self.spine_args_opt(sa)? else {
            return self.same_cells(sa, sc).map(Some);
        };
        let ys = match self.spine_args_opt(sc) {
            Ok(Some(ys)) => ys,
            Ok(None) => {
                self.recycle(xs)?;
                return self.same_cells(sa, sc).map(Some);
            }
            Err(error) => return self.scratch_finish(Err(error), [xs]),
        };
        let res = self.same_args(&xs, &ys, head, skip);
        self.scratch_finish(res, [xs, ys])
    }
    /// Without evaluating: two applications of different constructors of one
    /// family, or two different literals. Such values are not definitionally
    /// equal unless they are proofs (proof irrelevance), which the caller
    /// excludes; structure eta and unit-like equality need a single
    /// constructor. Unevaluated thunks are never visibly distinct.
    fn visibly_distinct(&mut self, mut x: u32, mut y: u32) -> R<bool> {
        while let Val::Ind(t) = self.vals[x as usize] {
            x = t;
        }
        while let Val::Ind(t) = self.vals[y as usize] {
            y = t;
        }
        Ok(match (self.vals[x as usize], self.vals[y as usize]) {
            (Val::Const { ci: a, .. }, Val::Const { ci: b, .. }) => matches!(
                (self.const_view(a)?.ctor, self.const_view(b)?.ctor),
                (Some((fa, ia)), Some((fb, ib))) if fa == fb && ia != ib
            ),
            (Val::Nat(a), Val::Nat(b)) => !nat_eq(&self.nats[a as usize], &self.nats[b as usize]),
            _ => false,
        })
    }
    /// Arguments of two applications of `head`, root first; see `same_spines`.
    fn same_args(
        &mut self,
        xs: &[u32],
        ys: &[u32],
        head: Result<u32, (u32, u32)>,
        skip: u64,
    ) -> R<Option<bool>> {
        // A non-proof argument pair that is visibly different ends this
        // route before any earlier, possibly expensive, pair is compared.
        // `false` here is not a conclusion: argument-first comparison then
        // unfolds, and anywhere else the attempt may only be abandoned.
        let (mut fty, mut at) = (NONE, 0usize);
        for i in 0..xs.len() {
            if (i >= 64 || (skip >> i) & 1 == 0) && self.visibly_distinct(xs[i], ys[i])? {
                match self.arg_is_proof(&mut fty, &mut at, head, xs, i) {
                    Ok(Some(false) | None) => return Ok(None),
                    Ok(Some(true)) | Err(KErr::Unsupported) => {}
                    Err(e) => return Err(e),
                }
            }
        }
        let mut fty = NONE;
        let mut at = 0usize;
        let mut typed = true;
        for i in 0..xs.len() {
            let (x, y) = (xs[i], ys[i]);
            if i < 64 && (skip >> i) & 1 == 1 {
                continue;
            }
            if x == y || self.eq_ok.contains(&(x.min(y), x.max(y))) {
                continue;
            }
            let mut not_proof = false;
            if typed {
                match self.arg_is_proof(&mut fty, &mut at, head, xs, i) {
                    Ok(Some(true)) => continue,
                    Ok(Some(false)) => not_proof = true,
                    Ok(None) => {}
                    Err(KErr::Unsupported) => {
                        typed = false;
                    }
                    Err(e) => return Err(e),
                }
            }
            if !self.defeq_with(x, y, not_proof)? {
                return Ok(Some(false));
            }
        }
        Ok(Some(true))
    }
    /// Whether argument `i` of the head's type, instantiated with `xs`, is
    /// expected to be a proof: `Some(false)` when its domain's sort is known
    /// not to be zero, `None` when that sort is unknown.
    fn arg_is_proof(
        &mut self,
        fty: &mut u32,
        at: &mut usize,
        head: Result<u32, (u32, u32)>,
        xs: &[u32],
        i: usize,
    ) -> R<Option<bool>> {
        let original = if i < 8 || *fty == NONE {
            Some(match head {
                Ok(id) => self.locals[id as usize],
                Err((ci, li)) => self.const_type(ci, li)?,
            })
        } else {
            None
        };
        if *fty == NONE {
            *fty = original.ok_or(ResourceError::Invariant)?;
        }
        let head_key = original.filter(|_| i < 8).map(|ty| (ty, i as u32 + 1));
        if let Some(key) = head_key
            && let Some(&status) = self.arg_proof_status.get(&key)
        {
            // Leave the instantiation cursor unchanged. A later unguarded
            // argument still has to instantiate the complete missing prefix.
            return Ok(Some(status));
        }
        // The caller keeps this cursor for one fixed head and only advances
        // it by instantiation. Once initialized, a constant's exact type cache
        // entry remains present for the entire attempt: rereading it would be
        // an uncharged, infallible hit, not another typing or budget premise.
        while *at < i {
            let w = self.pi_like(*fty)?;
            *fty = self.instantiate(w, xs[*at])?;
            *at += 1;
        }
        let w = self.pi_like(*fty)?;
        let dom = self.binder_dom(w)?;
        // Reduced selectors can expose different Pi domains. Domain identity
        // always fixes the instantiated denotation within this attempt. Head
        // reuse additionally requires the explicit-prefix formation premise.
        let key = (dom, 0);
        if let Some(&status) = self.arg_proof_status.get(&key) {
            return Ok(Some(status));
        }
        let status = self.prop_status(dom)?;
        if let Some(proof) = status {
            let key = match head_key {
                Some(head_key) if self.explicit_proof_prefix(head_key.0, i)? => head_key,
                _ if !proof => key,
                _ => return Ok(status),
            };
            // Trial: completed proof observations use the same explicit-prefix
            // premise as non-proof observations. Domain-only fallback remains
            // non-proof-only; zero and nonzero positions are disjoint keys.
            map_put(
                self.b,
                &mut self.reserved,
                &mut self.arg_proof_status,
                key,
                proof,
            )?;
        }
        Ok(status)
    }
    /// A fixed original head/context/universe instance and an explicit Pi
    /// prefix prove that well-typed substitution preserves each domain's sort.
    /// Never reduce a selector (including let/projection/beta) to discover Pis.
    /// The exact scoped graph fixes this prefix across eligible restoration;
    /// only completed classifications fill `arg_proof_status`.
    fn explicit_proof_prefix(&mut self, original: u32, i: usize) -> R<bool> {
        if i >= 8 {
            return Ok(false);
        }
        self.steps_by(i as u64 + 1)?;
        let Val::Pi(c) = self.vals[original as usize] else {
            return Ok(false);
        };
        let mut body = c.body;
        for _ in 0..i {
            let node = self.exprs.get(body, self.b)?;
            let ExprKind::Pi(_, _, next, _) = node.kind(self.exprs, self.levels, self.b)? else {
                return Ok(false);
            };
            body = next;
        }
        Ok(true)
    }
    fn same_cells(&mut self, sa: u32, sc: u32) -> R<bool> {
        let (mut x, mut y) = (sa, sc);
        if self.cells[x as usize].len != self.cells[y as usize].len {
            return Ok(false);
        }
        while x != y {
            let (cx, cy) = (self.cells[x as usize], self.cells[y as usize]);
            if cx.tag != cy.tag {
                return Ok(false);
            }
            if cx.tag == 0 {
                if !self.defeq(cx.item, cy.item)? {
                    return Ok(false);
                }
            } else if cx.item != cy.item {
                return Ok(false);
            }
            x = cx.prev;
            y = cy.prev;
        }
        Ok(true)
    }
    fn eta(&mut self, lam: u32, other: u32) -> R<bool> {
        if !matches!(
            self.vals[other as usize],
            Val::Local { .. } | Val::Const { .. } | Val::Lam(_) | Val::Proj { .. }
        ) {
            return Ok(false);
        }
        // As in Lean, the other side's eta-expansion carries its own binder
        // domain, which must equal the lambda's.
        let Some(t) = self.infer_value(other)? else {
            return Ok(false);
        };
        let w = self.whnf(t)?;
        if !matches!(
            self.vals[w as usize],
            Val::Pi(_) | Val::LamTy(_) | Val::Arrow { .. }
        ) {
            return Ok(false);
        }
        let d = self.binder_dom(lam)?;
        let od = self.binder_dom(w)?;
        if !self.defeq(d, od)? {
            return Ok(false);
        }
        let x = self.open_local(d)?;
        let r = (|| {
            let l = self.apply(lam, x)?;
            let o = self.apply(other, x)?;
            self.defeq(l, o)
        })();
        self.close_local();
        r
    }
    fn nat_succ(&mut self, lit: u32, other: u32) -> R<bool> {
        let Val::Nat(n) = self.vals[lit as usize] else {
            return Ok(false);
        };
        let Some((_, zero, succ)) = self.nat_ctors()? else {
            return Ok(false);
        };
        let Val::Const { ci, spine, .. } = self.vals[other as usize] else {
            return Ok(false);
        };
        let lit = self.nats[n as usize].dup()?;
        if ci == zero && spine == 0 {
            return Ok(matches!(lit, NatLit::Small(0)));
        }
        if ci == succ && self.cells[spine as usize].len == 1 && !matches!(lit, NatLit::Small(0)) {
            let Some(arg) = self.arg_item(spine) else {
                return Ok(false);
            };
            let p = nat_pred(&lit, self.b, &mut self.reserved)?;
            let p = self.nat(p)?;
            return self.defeq(p, arg);
        }
        Ok(false)
    }
    #[allow(
        clippy::let_and_return,
        reason = "test-only observer omitted from public source"
    )]
    fn struct_eta(&mut self, x: u32, ctor: u32) -> R<bool> {
        let Val::Const { ci, li, spine } = self.vals[ctor as usize] else {
            return Ok(false);
        };
        let Some((family, _)) = self.const_view(ci)?.ctor else {
            return Ok(false);
        };
        let fci = match self.const_by_canon.get(&family) {
            Some(&fci) => fci,
            None => {
                // Committed constructor metadata fixes the original family.
                // Its availability cannot depend on an earlier value having
                // loaded that family's attempt-local CInfo. Resolve it under
                // the same immutable frontier and retain ordinary admission.
                let Some(c) = self.env.constructor(
                    self.const_view(ci)?.name,
                    self.before.min(self.env.len()),
                    self.names,
                    self.b,
                )?
                else {
                    return Ok(false);
                };
                let fci = self.const_info(c.family)?;
                fci
            }
        };
        let Some(ind) = self.const_view(fci)?.ind else {
            return Ok(false);
        };
        if !ind.structure_like() {
            return Ok(false);
        }
        let nf = ind.ctors[0].num_fields;
        if self.cells[spine as usize].len != ind.nparams + nf {
            return Ok(false);
        }
        let (Some(tx), Some(tc)) = (self.infer_value(x)?, self.infer_value(ctor)?) else {
            return Ok(false);
        };
        if !self.defeq(tx, tc)? {
            return Ok(false);
        }
        let Some(args) = self.spine_args_opt(spine)? else {
            return Ok(false);
        };
        let res = (|| {
            if nf == 0 {
                return Ok(true);
            }
            // Conversion's checked-term premise supplies field typing. Equal
            // parent types and earlier compared fields transport the actual
            // constructor domain to x's projection, including dependencies on
            // earlier proofs (by proof irrelevance). Classification alone is
            // never permission to compare an unchecked constructor.
            // Keep the existing restriction on projecting data from Prop.
            let mut typed = match self.prop_status(tc) {
                Ok(Some(false)) => true,
                Ok(_) | Err(KErr::Unsupported) => false,
                Err(error) => return Err(error),
            };
            let (mut fty, mut at) = (NONE, 0usize);
            for i in 0..nf {
                if typed {
                    let status = self.arg_is_proof(
                        &mut fty,
                        &mut at,
                        Err((ci, li)),
                        &args,
                        (ind.nparams + i) as usize,
                    );
                    match status {
                        Ok(Some(true)) => {
                            continue;
                        }
                        Ok(Some(false)) => {}
                        Ok(None) | Err(KErr::Unsupported) => typed = false,
                        Err(error) => return Err(error),
                    }
                }
                let p = self.proj(x, i, fci)?;
                if !self.defeq(p, args[(ind.nparams + i) as usize])? {
                    return Ok(false);
                }
            }
            Ok(true)
        })();
        self.scratch_finish(res, [args])
    }
    fn unit_like(&mut self, a: u32, c: u32) -> R<bool> {
        let Some(ta) = self.infer_value(a)? else {
            return Ok(false);
        };
        let w = self.whnf(ta)?;
        let Val::Const { ci, .. } = self.vals[w as usize] else {
            return Ok(false);
        };
        let Some(ind) = self.const_view(ci)?.ind else {
            return Ok(false);
        };
        if !ind.structure_like() || ind.ctors[0].num_fields != 0 {
            return Ok(false);
        }
        let Some(tc) = self.infer_value(c)? else {
            return Ok(false);
        };
        self.defeq(w, tc)
    }
}
fn parse_nat(bytes: &[u8], b: &mut Budget, reserved: &mut u64) -> R<NatLit> {
    let mut n: u64 = 0;
    for &d in bytes {
        match n
            .checked_mul(10)
            .and_then(|m| m.checked_add((d - b'0') as u64))
        {
            Some(m) => n = m,
            None => {
                // This is a retained payload, separate from source syntax or
                // Digits storage. `copied` requests max(len, 8); overflow of a
                // canonical u64 requires at least twenty digits. Reserve before
                // allocation and keep the charge through all admission failures.
                charge_bytes(b, reserved, bytes.len())?;
                return Ok(NatLit::Big(copied(bytes)?));
            }
        }
    }
    Ok(NatLit::Small(n))
}
fn nat_digits(n: &NatLit) -> R<Vec<u8>> {
    match n {
        NatLit::Small(v) => {
            let mut buf = [0u8; 20];
            let mut i = buf.len();
            let mut v = *v;
            loop {
                i -= 1;
                buf[i] = b'0' + (v % 10) as u8;
                v /= 10;
                if v == 0 {
                    break;
                }
            }
            copied(&buf[i..])
        }
        NatLit::Big(b) => copied(b),
    }
}
fn nat_eq(a: &NatLit, c: &NatLit) -> bool {
    match (a, c) {
        (NatLit::Small(x), NatLit::Small(y)) => x == y,
        (NatLit::Big(x), NatLit::Big(y)) => x == y,
        _ => false,
    }
}
fn nat_pred(n: &NatLit, budget: &mut Budget, reserved: &mut u64) -> R<NatLit> {
    match n {
        NatLit::Small(v) => Ok(NatLit::Small(v - 1)),
        NatLit::Big(b) => {
            let mut d = copied(b)?;
            let mut i = d.len();
            while i > 0 {
                i -= 1;
                if d[i] == b'0' {
                    d[i] = b'9';
                } else {
                    d[i] -= 1;
                    break;
                }
            }
            let start = d.iter().position(|&x| x != b'0').unwrap_or(d.len() - 1);
            parse_nat(&d[start..], budget, reserved)
        }
    }
}
fn nat_small(op: crate::check::natural::Operation, a: &NatLit, c: &NatLit) -> Option<u64> {
    use crate::check::natural::Operation::*;
    let (NatLit::Small(x), NatLit::Small(y)) = (a, c) else {
        return None;
    };
    let (x, y) = (*x, *y);
    match op {
        Add => x.checked_add(y),
        Mul => x.checked_mul(y),
        Sub => Some(x.saturating_sub(y)),
        Div => Some(x.checked_div(y).unwrap_or(0)),
        Mod => Some(if y == 0 { x } else { x % y }),
        Pow => u32::try_from(y).ok().and_then(|y| x.checked_pow(y)),
        Land => Some(x & y),
        Lor => Some(x | y),
        Xor => Some(x ^ y),
        ShiftRight => Some(if y >= 64 { 0 } else { x >> y }),
        ShiftLeft => {
            if x == 0 {
                Some(0)
            } else if y < 64 && x <= (u64::MAX >> y) {
                Some(x << y)
            } else {
                None
            }
        }
        Gcd => {
            let (mut a, mut b) = (x, y);
            while b != 0 {
                let next = a % b;
                a = b;
                b = next;
            }
            Some(a)
        }
    }
}

/// Whether the kernel attempts this declaration at all: safe declarations in
/// a safe scope outside formation phases.
pub(crate) fn eligible(request: &Request<'_>, scope: &Scope<'_>) -> bool {
    request.safety == Safety::Safe && scope.mode == Mode::Safe && scope.formation.is_none()
}

/// Positive-only attempt for one declaration; see the module comment.
#[allow(clippy::too_many_arguments)]
pub(super) fn check(
    environment: &Environment,
    request: &Request<'_>,
    scope: &Scope<'_>,
    names: &Names,
    exprs: &mut Expressions,
    levels: &mut Levels,
    budget: &mut Budget,
    retention: Option<&mut Retention>,
) -> Result<bool, super::normalization::HeadError> {
    if !eligible(request, scope) {
        return Ok(false);
    }
    let checked = check_inner(
        environment,
        request,
        scope,
        names,
        exprs,
        levels,
        budget,
        retention,
    )?;
    Ok(checked)
}

#[allow(clippy::too_many_arguments)]
fn check_inner(
    environment: &Environment,
    request: &Request<'_>,
    scope: &Scope<'_>,
    names: &Names,
    exprs: &mut Expressions,
    levels: &mut Levels,
    budget: &mut Budget,
    retention: Option<&mut Retention>,
) -> Result<bool, super::normalization::HeadError> {
    let (ok, wants_quot) = attempt(
        environment,
        request,
        scope,
        names,
        exprs,
        levels,
        budget,
        None,
        retention,
    )?;
    if ok || !wants_quot {
        return Ok(ok);
    }
    // Retry once with the validated quotient schemas, generated only for
    // declarations that need a quotient's type (session syntax, rolled back).
    let Some(package) = environment.quotient.as_ref() else {
        return Ok(false);
    };
    let expression_mark = exprs.watermark();
    let level_mark = levels.len();
    let mut types = [ExprId::from_stored_original(0); 4];
    for role in [
        QuotientRole::Type,
        QuotientRole::Constructor,
        QuotientRole::Lift,
        QuotientRole::Induction,
    ] {
        let mut params = Vec::new();
        params
            .try_reserve_exact(2)
            .map_err(|_| ResourceError::Allocation)?;
        for &n in &package.names[5..5 + role.arity()] {
            params.push(levels.append(LevelKind::Param(n), names, budget)?);
        }
        types[role.index()] = match super::quotient::schema::build(
            role,
            &package.names,
            &params,
            exprs,
            levels,
            names,
            budget,
        ) {
            Ok(t) => t,
            Err(crate::syntax::expressions::ExpressionError::Resource(e)) => return Err(e.into()),
            Err(_) => {
                exprs.discard_since(expression_mark, budget)?;
                levels.discard_since(level_mark, budget)?;
                return Ok(false);
            }
        };
    }
    let result = attempt(
        environment,
        request,
        scope,
        names,
        exprs,
        levels,
        budget,
        Some(types),
        None, // private quotient-schema retry never sees the ordinary cache
    );
    // Nothing built for the attempt survives it; the existing checker, if it
    // runs next, sees the session exactly as before.
    // Levels remain referenced if expression rollback fails. Preserve an
    // earlier internal failure even when this dependent cleanup exhausts work.
    let cleanup = exprs
        .discard_since(expression_mark, budget)
        .and_then(|()| levels.discard_since(level_mark, budget));
    finish_rollback(result, cleanup)
}

fn finish_rollback(
    result: Result<(bool, bool), super::normalization::HeadError>,
    cleanup: Result<(), ResourceError>,
) -> Result<bool, super::normalization::HeadError> {
    if let Some(error) = super::normalization::full::select_failure([
        result.as_ref().err().copied(),
        cleanup.err().map(Into::into),
    ]) {
        return Err(error);
    }
    result.map(|(ok, _)| ok)
}

/// Completed checked formation under the caller's immutable context and exact
/// signature-only staging phase. Computation metadata is committed only. Every
/// incomplete attempt falls back; mandatory charge/cleanup failures propagate.
/// Caller owns generated levels until its existing session retirement.
#[allow(clippy::too_many_arguments)]
pub(crate) fn formation_sort(
    environment: &Environment,
    root: ExprId,
    scope: &Scope<'_>,
    pre_staging: bool,
    context: &LocalContext,
    names: &Names,
    exprs: &Expressions,
    levels: &mut Levels,
    budget: &mut Budget,
) -> Result<Option<LevelId>, super::normalization::HeadError> {
    // A formation-free query needs the inductive pre-staging
    // authority; `check_scope` then requires exactly the committed
    // environment, so no staged signature or generated artifact is visible.
    if (scope.formation.is_none() && !pre_staging) || scope.mode != Mode::Safe {
        return Ok(None);
    }
    environment.check_scope(
        scope.before,
        scope.formation,
        scope.expression_end,
        scope.level_end,
    )?;
    let mut k = Kernel::new(environment, names, exprs, levels, budget, scope);
    k.checked_context = Some(context);
    let result = (|| {
        k.init()?;
        let ty = k.infer(root, 0, 0, true)?;
        k.sort_of(ty)
    })();
    let steps = k.steps - k.charged;
    let reserved = k.reserved;
    k.retire_arena();
    drop(k);
    let charge = budget.charge_work(steps);
    let release = budget.release(reserved);
    let (completed, _) = finish_attempt(
        result.as_ref().map(|_| ()).map_err(|e| *e),
        charge,
        release,
        false,
    )?;
    Ok(if completed { result.ok() } else { None })
}

/// Positive-only typed checking: check a generated rule against its independently
/// inferred expected type. No type syntax or checkedness escapes this query.
#[allow(clippy::too_many_arguments)]
pub(crate) fn formation_check(
    environment: &Environment,
    root: ExprId,
    expected: ExprId,
    scope: &Scope<'_>,
    context: &LocalContext,
    names: &Names,
    exprs: &Expressions,
    levels: &mut Levels,
    budget: &mut Budget,
) -> Result<bool, super::normalization::HeadError> {
    if scope.formation.is_none() || scope.mode != Mode::Safe {
        return Ok(false);
    }
    environment.check_scope(
        scope.before,
        scope.formation,
        scope.expression_end,
        scope.level_end,
    )?;
    let mut k = Kernel::new(environment, names, exprs, levels, budget, scope);
    k.checked_context = Some(context);
    let result = (|| {
        k.init()?;
        // Expected syntax is generated by the caller. Its construction alone
        // does not establish typing: this query checks it before consuming it.
        let et = k.infer(expected, 0, 0, true)?;
        k.sort_of(et)?;
        let expected = k.eval(expected, 0, 0)?;
        k.check_expr(root, expected, 0)
    })();
    let steps = k.steps - k.charged;
    let reserved = k.reserved;
    k.retire_arena();
    drop(k);
    let charge = budget.charge_work(steps);
    let release = budget.release(reserved);
    let (completed, _) = finish_attempt(result, charge, release, false)?;
    Ok(completed)
}

#[allow(clippy::too_many_arguments)]
fn attempt(
    environment: &Environment,
    request: &Request<'_>,
    scope: &Scope<'_>,
    names: &Names,
    exprs: &Expressions,
    levels: &mut Levels,
    budget: &mut Budget,
    quot_types: Option<[ExprId; 4]>,
    mut retention: Option<&mut Retention>,
) -> Result<(bool, bool), super::normalization::HeadError> {
    let mut k = Kernel::new(environment, names, exprs, levels, budget, scope);
    k.quot_types = quot_types;
    let retain = retention.is_some() && Retention::eligible(&k, request, quot_types.is_some());
    let mut restored_graph = false;
    let result = (|| -> R<()> {
        let restored = if retain {
            retention
                .as_deref_mut()
                .ok_or(ResourceError::Invariant)?
                .restore(&mut k)?
        } else {
            false
        };
        restored_graph = restored;
        if !restored {
            k.init()?;
        }
        let tt = k.infer(request.ty, 0, 0, true)?;
        let s = k.sort_of(tt)?;
        if request.kind == Kind::Theorem && !k.is_zero(s)? {
            return no();
        }
        if let Some(value) = request.value {
            let tv = k.eval(request.ty, 0, 0)?;
            k.check_expr(value, tv, 0)?;
        }
        Ok(())
    })();
    // Only a completed attempt may stage a snapshot. Publication belongs to
    // State, after all attempt/session cleanup and declaration installation.
    let result = match result {
        // Only completed cold checking can earn initial admission. Copy work
        // starts inside capture below; an already earned graph may survive a
        // cheap consumer. A failed restore leaves restored_graph false.
        Ok(()) if retain && (restored_graph || k.steps >= CHARGE_BLOCK) => retention
            .ok_or(ResourceError::Invariant)
            .map_err(KErr::from)
            .and_then(|owner| owner.capture(&mut k)),
        other => other,
    };
    let wants_quot = k.wants_quot && quot_types.is_none();
    let steps = k.steps - k.charged;
    let reserved = k.reserved;
    #[cfg(feature = "introspection")]
    probe::report(
        request.name.0,
        &result,
        k.steps,
        [
            (
                "clo",
                k.clo_index.lookups,
                k.clo_index.hits,
                k.clo_index.off,
            ),
            (
                "val",
                k.val_index.lookups,
                k.val_index.hits,
                k.val_index.off,
            ),
            (
                "cell",
                k.cell_index.lookups,
                k.cell_index.hits,
                k.cell_index.off,
            ),
            (
                "envl",
                k.env_lossy.lookups,
                k.env_lossy.hits,
                k.env_lossy.off,
            ),
        ],
    );
    k.retire_arena();
    drop(k);
    let charge = budget.charge_work(steps);
    let release = budget.release(reserved);
    finish_attempt(result, charge, release, wants_quot)
}

/// All three operations have completed before selecting a failure. A cleanup
/// internal error must dominate every support/resource decline.
fn finish_attempt(
    result: R<()>,
    charge: Result<(), ResourceError>,
    release: Result<(), ResourceError>,
    wants_quot: bool,
) -> Result<(bool, bool), super::normalization::HeadError> {
    let operation = match result {
        Err(KErr::Resource(error)) => Some(error.into()),
        _ => None,
    };
    let unsupported = matches!(result, Err(KErr::LiteralArithmetic))
        .then_some(UseError::LiteralArithmetic.into());
    if let Some(error) = super::normalization::full::select_failure([
        operation,
        charge.err().map(Into::into),
        release.err().map(Into::into),
        unsupported,
    ]) {
        return Err(error);
    }
    // An escaped Abort cannot happen with the unlimited outer allowance; it
    // would only end this attempt, like any other incomplete route.
    Ok((matches!(result, Ok(())), wants_quot))
}

mod read_wide;
