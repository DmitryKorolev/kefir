//! Bounded completed original theorem judgments in one State/Decoder.
//! Stores only T : Prop and p : T. It grants no declaration installation, name,
//! policy, metadata or whole-input verdict. Original syntax and committed names
//! cannot be recycled/rebound in this owner; extension preserves these judgments.
use crate::decode::primitive_decode::declarations::{Kind, Request, Safety};
use crate::resource::{Budget, ResourceError};
use std::mem::{size_of, take};

const SLOTS: usize = 4096;
const BUCKETS: usize = SLOTS;
const ADMISSION: u64 = 1 << 18;
const HIT_REFRESH_WORK: u64 = 24;
const PUBLICATION_WORK: u64 = 128;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Key {
    ty: u32,
    value: u32,
    parameters: [u32; 4],
    count: u8,
    policy: u8,
}
const _: () = assert!(size_of::<Key>() == 28);
const _: () = assert!(size_of::<Option<Key>>() == 32);
impl Key {
    fn bucket(self) -> usize {
        let mut h = 0x243f_6a88u64;
        for x in [
            self.ty,
            self.value,
            u32::from(self.count),
            u32::from(self.policy),
        ]
        .into_iter()
        .chain(self.parameters[..usize::from(self.count)].iter().copied())
        {
            h = (h ^ u64::from(x))
                .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                .rotate_left(29);
        }
        h as usize & (BUCKETS - 1)
    }
}

// Owned dense ring; full key remains the only positive authority. The visited
// bit is replacement metadata, never evidence of typing or inequality.
#[derive(Clone, Copy)]
struct Entry {
    key: Key,
    hash_previous: u16,
    hash_next: u16,
    visited: bool,
}
#[derive(Clone, Copy, Default)]
struct Bucket {
    head: u16,
    len: u16,
}
const _: () = assert!(size_of::<Entry>() == 36);
const _: () = assert!(size_of::<Bucket>() == 4);
// POISON is never an entry index. It fences any accidental standalone retry
// after spending scan credits without successful publication; retire accepts it.
const POISON: u16 = SLOTS as u16;

#[derive(Default)]
pub(super) struct Judgments {
    entries: Vec<Entry>,
    buckets: Vec<Bucket>,
    pending: Option<Key>,
    hand: u16,
    pending_skip: u16,
    pending_old_bucket: u16,
    pending_new_bucket: u16,
}
const _: () = assert!(size_of::<Judgments>() == 88);

impl Judgments {
    pub(super) fn new() -> Self {
        Self { ..Self::default() }
    }
    // The State/Decoder pair owns these original source IDs for one run.
    // No generated source, ValueId, local context or shortened hash is stored.
    pub(super) fn key(&self, request: &Request<'_>, policy: crate::AxiomPolicy) -> Option<Key> {
        if request.kind != Kind::Theorem
            || request.safety != Safety::Safe
            || request.parameters.len() > 4
        {
            return None;
        }
        let mut parameters = [0; 4];
        for (out, parameter) in parameters.iter_mut().zip(request.parameters) {
            *out = parameter.0;
        }
        Some(Key {
            ty: request.ty.slot(),
            value: request.value?.slot(),
            parameters,
            count: request.parameters.len() as u8,
            policy: match policy {
                crate::AxiomPolicy::ExcludeNativeMarked => 0,
                crate::AxiomPolicy::AllowAllDeclaredAxioms => 1,
            },
        })
    }
    // Construction: entries is a dense occupied prefix, and every live entry
    // occurs once in its full-key hash chain. Encoded links are index+1, zero null.
    // The same logical input Budget/Decoder remains paired with this State;
    // credits never cross input owners or argument-probe allowances.
    fn entry(&self, link: u16) -> Result<Entry, ResourceError> {
        let index = usize::from(link)
            .checked_sub(1)
            .ok_or(ResourceError::Invariant)?;
        self.entries
            .get(index)
            .copied()
            .ok_or(ResourceError::Invariant)
    }
    fn bucket(&self, index: usize) -> Result<Bucket, ResourceError> {
        let bucket = self
            .buckets
            .get(index)
            .copied()
            .ok_or(ResourceError::Invariant)?;
        let live = self.entries.len();
        if live > SLOTS
            || usize::from(bucket.len) > live
            || (bucket.head == 0) != (bucket.len == 0)
            || usize::from(bucket.head) > live
        {
            return Err(ResourceError::Invariant);
        }
        Ok(bucket)
    }
    // Pure membership, including preparation's independent duplicate probe.
    // The fixed base pays bounded hashing/header access. Prepay the complete
    // known chain before reading entries; there are no per-iteration charges.
    fn find(&self, key: Key, budget: &mut Budget) -> Result<(u16, u16), ResourceError> {
        budget.charge_work(1)?;
        if self.pending.is_some() || usize::from(self.hand) >= SLOTS {
            return Err(ResourceError::Invariant);
        }
        let index = key.bucket();
        if self.buckets.is_empty() {
            if !self.entries.is_empty() || self.hand != 0 {
                return Err(ResourceError::Invariant);
            }
            return Ok((0, index as u16));
        }
        if self.buckets.len() != BUCKETS {
            return Err(ResourceError::Invariant);
        }
        let bucket = self.bucket(index)?;
        budget.charge_work(u64::from(bucket.len))?;
        let (mut link, mut previous) = (bucket.head, 0);
        for offset in 0..bucket.len {
            let entry = self.entry(link)?;
            if entry.hash_previous != previous
                || entry.hash_next == link
                || usize::from(entry.hash_next) > self.entries.len()
                || (offset + 1 == bucket.len) != (entry.hash_next == 0)
            {
                return Err(ResourceError::Invariant);
            }
            if entry.key == key {
                return Ok((link, index as u16));
            }
            previous = link;
            link = entry.hash_next;
        }
        if link != 0 {
            return Err(ResourceError::Invariant);
        }
        Ok((0, index as u16))
    }
    fn validate_hash(&self, link: u16, index: usize) -> Result<(), ResourceError> {
        let bucket = self.bucket(index)?;
        let entry = self.entry(link)?;
        if bucket.len == 0
            || (entry.hash_previous == 0) != (bucket.head == link)
            || (bucket.len == 1) != (entry.hash_previous == 0 && entry.hash_next == 0)
            || entry.hash_previous == link
            || entry.hash_next == link
            || (entry.hash_previous != 0 && entry.hash_previous == entry.hash_next)
        {
            return Err(ResourceError::Invariant);
        }
        if self.entry(bucket.head)?.hash_previous != 0 {
            return Err(ResourceError::Invariant);
        }
        if entry.hash_previous != 0 && self.entry(entry.hash_previous)?.hash_next != link {
            return Err(ResourceError::Invariant);
        }
        if entry.hash_next != 0 && self.entry(entry.hash_next)?.hash_previous != link {
            return Err(ResourceError::Invariant);
        }
        Ok(())
    }
    // Fixed headers/neighbours only. No flag read or credit consumption occurs
    // before all no-op eligibility/floor/duplicate checks have completed.
    fn prevalidate_headers(&self, new_bucket: u16) -> Result<Bucket, ResourceError> {
        if self.entries.capacity() != SLOTS
            || self.buckets.capacity() != BUCKETS
            || self.buckets.len() != BUCKETS
            || self.entries.len() > SLOTS
            || usize::from(self.hand) >= SLOTS
            || (self.entries.len() < SLOTS && self.hand != 0)
        {
            return Err(ResourceError::Invariant);
        }
        let next = self.bucket(usize::from(new_bucket))?;
        if next.head != 0 && self.entry(next.head)?.hash_previous != 0 {
            return Err(ResourceError::Invariant);
        }
        Ok(next)
    }
    // Scan one immutable turn at most. A true bit witnesses one previously paid
    // false->true HIT credit: at most eight prepare operations per true bit.
    // The final cold probe (or bounded all-true terminal) uses PUBLICATION_WORK.
    // Caller has set POISON, so any later error cannot reuse an uncleared span.
    fn skipped(&self, hand: usize) -> usize {
        let mut skip = 0;
        while skip < SLOTS && self.entries[(hand + skip) & (SLOTS - 1)].visited {
            skip += 1;
        }
        skip
    }
    fn unlink_hash(&mut self, bucket: usize, entry: Entry) {
        if entry.hash_previous == 0 {
            self.buckets[bucket].head = entry.hash_next;
        } else {
            self.entries[usize::from(entry.hash_previous) - 1].hash_next = entry.hash_next;
        }
        if entry.hash_next != 0 {
            self.entries[usize::from(entry.hash_next) - 1].hash_previous = entry.hash_previous;
        }
        self.buckets[bucket].len -= 1;
    }
    // Only prevalidated, prepaid fixed writes; no fallible query or allocation.
    fn attach(&mut self, link: u16, bucket: usize) {
        let head = self.buckets[bucket].head;
        let entry = &mut self.entries[usize::from(link) - 1];
        entry.hash_previous = 0;
        entry.hash_next = head;
        if head != 0 {
            self.entries[usize::from(head) - 1].hash_previous = link;
        }
        self.buckets[bucket].head = link;
        self.buckets[bucket].len += 1;
    }
    // Call after current root-scope validation in safe ordinary empty context.
    // Never call between prepare and finish; find rejects an outstanding pending
    // key or poison sentinel before any HIT can manufacture a new credit.
    pub(super) fn lookup(
        &mut self,
        key: Option<Key>,
        budget: &mut Budget,
    ) -> Result<bool, ResourceError> {
        let Some(key) = key else { return Ok(false) };
        let (link, _) = self.find(key, budget)?;
        if link == 0 {
            return Ok(false);
        }
        budget.charge_work(HIT_REFRESH_WORK)?;
        // At most eight local checked operations; true->true overpayment is
        // conservative and creates no second stored credit. Charge before write.
        self.entries[usize::from(link) - 1].visited = true;
        Ok(true)
    }
    pub(super) fn prepare(
        &mut self,
        key: Option<Key>,
        work: u64,
        budget: &mut Budget,
    ) -> Result<(), ResourceError> {
        // Never silently replace an already funded outstanding span. The outer
        // State poisons every failed route before this owner can be called again.
        if self.pending.is_some() || usize::from(self.hand) >= SLOTS {
            self.pending = None;
            self.pending_skip = 0;
            self.pending_old_bucket = 0;
            self.pending_new_bucket = 0;
            self.hand = POISON;
            return Err(ResourceError::Invariant);
        }
        // Construction: pending=None on a healthy entry also means skip and
        // bucket fields are zero (new/finish/retire/error reset them together).
        // Thus every no-op retains all-zero pending metadata without hot stores.
        let Some(key) = key else { return Ok(()) };
        let admission = ADMISSION;
        if work < admission {
            return Ok(());
        }
        let (found, new_bucket) = self.find(key, budget)?;
        if found != 0 {
            return Ok(());
        }
        if self.buckets.is_empty() {
            budget.grow_vec(&mut self.entries, SLOTS)?;
            budget.grow_vec(&mut self.buckets, BUCKETS)?;
            budget.charge_work((BUCKETS + 2) as u64)?;
            self.buckets.resize(BUCKETS, Bucket::default());
        }
        budget.charge_work(PUBLICATION_WORK)?;
        let next = self.prevalidate_headers(new_bucket)?;
        let saved_hand = self.hand;
        let (skip, old_bucket) = if self.entries.len() == SLOTS {
            // From this moment exactly one finish(true), or terminal poison and
            // flat retirement, must follow. No-op returns and retry are forbidden.
            self.hand = POISON;
            let skip = self.skipped(usize::from(saved_hand));
            let victim = (usize::from(saved_hand) + skip) & (SLOTS - 1);
            let link = (victim + 1) as u16;
            let old_bucket = self.entries[victim].key.bucket();
            self.validate_hash(link, old_bucket)?;
            // Header was already checked before the immutable scan; only hand
            // changed meanwhile. Reuse the copied header, not another validation.
            if old_bucket != usize::from(new_bucket) && usize::from(next.len) >= SLOTS {
                return Err(ResourceError::Invariant);
            }
            (skip as u16, old_bucket as u16)
        } else {
            (0, 0)
        };
        self.hand = saved_hand;
        self.pending_skip = skip;
        self.pending_old_bucket = old_bucket;
        self.pending_new_bucket = new_bucket;
        self.pending = Some(key);
        Ok(())
    }
    // Called once after final Installed+cleanup. No mutation/query interleaves
    // after preparation; every skipped true flag and touched hash link was
    // prevalidated. Finish has no allocation, hash, scan search, query or charge.
    // Its bounded clearing pass uses the HIT-funded future-finish credits.
    pub(super) fn finish(&mut self, installed: bool) {
        let pending = self.pending.take();
        let skip = usize::from(take(&mut self.pending_skip));
        let old_bucket = usize::from(take(&mut self.pending_old_bucket));
        let new_bucket = usize::from(take(&mut self.pending_new_bucket));
        let Some(key) = pending else { return };
        if !installed {
            self.hand = POISON;
            return;
        }
        let link = if self.entries.len() == SLOTS {
            let hand = usize::from(self.hand);
            for offset in 0..skip {
                self.entries[(hand + offset) & (SLOTS - 1)].visited = false;
            }
            let victim = (hand + skip) & (SLOTS - 1);
            let link = (victim + 1) as u16;
            let entry = self.entries[victim];
            self.unlink_hash(old_bucket, entry);
            self.entries[victim] = Entry {
                key,
                hash_previous: 0,
                hash_next: 0,
                visited: false,
            };
            self.hand = ((victim + 1) & (SLOTS - 1)) as u16;
            link
        } else {
            self.entries.push(Entry {
                key,
                hash_previous: 0,
                hash_next: 0,
                visited: false,
            });
            self.entries.len() as u16
        };
        self.attach(link, new_bucket);
    }
    pub(super) fn retire(&mut self, budget: &mut Budget) -> Result<(), ResourceError> {
        // Accept poisoned hand: flat cleanup must not promote a Work/Storage
        // decline to INTERNAL merely because its credit owner was invalidated.
        self.pending = None;
        self.pending_skip = 0;
        self.pending_old_bucket = 0;
        self.pending_new_bucket = 0;
        self.hand = 0;
        let entries = take(&mut self.entries);
        let buckets = take(&mut self.buckets);
        let bytes =
            entries.capacity() * size_of::<Entry>() + buckets.capacity() * size_of::<Bucket>();
        drop(entries);
        drop(buckets);
        if bytes == 0 {
            Ok(())
        } else {
            budget.release(bytes as u64)
        }
    }
}
