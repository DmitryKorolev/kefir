//! (as amended) completed-universe-normalization table shared across
//! the U requests of one driver comparison operation.
//!
//! Keys are source level slots of the enclosing declaration's append-only
//! store; values are completed one-pass N results, which are pure functions of
//! the source's immutable subgraph and the fixed procedure, so a stored entry
//! remains the exact result for every later request in the same operation.
//! Every table dies in its owner's cleanup before the declaration can reclaim
//! generated syntax, so no key or value can dangle or be reused.
//!
//! This is an optional table: capacity lives inside the session cache
//! ledger shared by the operation's other tables. A capacity refusal stops
//! admission (no entry is retained, existing entries still serve lookups) and
//! the caller falls back to the per-request memo, which reproduces exactly the
//! unamended charges. Probe work is charged like any other table's probes; no
//! event or export surface exists.
use crate::resource::{Budget, ResourceError, SessionCacheBudget};
use std::hash::Hasher;
use std::mem::size_of;

#[derive(Clone, Copy, Default, PartialEq, Debug)]
struct Entry {
    source: u32,
    value: u32,
    hash: u32,
}
const _: () = assert!(size_of::<Entry>() == 12);

/// Exact u32-key table of completed N(source) results, mirroring the private
/// per-request memo's data shape with ledger accounting. Zero hash
/// marks a vacant slot; every hit compares the complete source key after a
/// hash match, never the hash alone.
#[derive(Default)]
pub(crate) struct SharedMemo {
    entries: Vec<Entry>,
    used: usize,
    stopped: bool,
}
const _: () = assert!(size_of::<SharedMemo>() == 40);

/// The borrowed table plus the session cache ledger that owns its capacity.
/// Both borrow from the same operation owner; neither escapes the operation.
pub(crate) struct SharedTable<'a> {
    pub(crate) memo: &'a mut SharedMemo,
    pub(crate) ledger: &'a mut SessionCacheBudget,
}

impl SharedMemo {
    fn key(source: u32) -> Entry {
        let mut h = crate::syntax::hash::FastHasher::new();
        h.write_u32(source);
        let hash = h.finish() as u32;
        Entry {
            source,
            hash: if hash == 0 { 1 } else { hash },
            ..Entry::default()
        }
    }

    fn position(entries: &[Entry], key: Entry, b: &mut Budget) -> Result<usize, ResourceError> {
        let mask = entries
            .len()
            .checked_sub(1)
            .ok_or(ResourceError::Invariant)?;
        let mut slot = key.hash as usize & mask;
        for _ in 0..entries.len() {
            b.charge_work(1)?;
            let entry = entries[slot];
            if entry.hash == 0 || (entry.hash == key.hash && entry.source == key.source) {
                return Ok(slot);
            }
            slot = (slot + 1) & mask;
        }
        Err(ResourceError::Invariant)
    }

    /// The stored completed result for `source`, if any. Served entries were
    /// installed only by completed normalizations; a stopped table keeps
    /// serving them, matching the cache discipline.
    pub(crate) fn get(&self, source: u32, b: &mut Budget) -> Result<Option<u32>, ResourceError> {
        if self.entries.is_empty() {
            return Ok(None);
        }
        let entry = self.entries[Self::position(&self.entries, Self::key(source), b)?];
        Ok((entry.hash != 0).then_some(entry.value))
    }

    /// Install one completed result. Returns whether the table retained it;
    /// `false` means the table had stopped admitting entries and the caller
    /// must keep its per-request memo authoritative. An occupied slot with a
    /// different value is a broken invariant: a completed immutable source
    /// cannot acquire another result within one operation.
    pub(crate) fn insert(
        &mut self,
        source: u32,
        value: u32,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<bool, ResourceError> {
        if self.stopped {
            return Ok(false);
        }
        let key = Entry {
            source,
            value,
            hash: Self::key(source).hash,
        };
        let mut available = None;
        if !self.entries.is_empty() {
            let slot = Self::position(&self.entries, key, b)?;
            if self.entries[slot].hash != 0 {
                if self.entries[slot].value != value {
                    return Err(ResourceError::Invariant);
                }
                return Ok(true);
            }
            available = Some(slot);
        }
        if self.used + 1 > self.entries.len() / 4 * 3 {
            if !self.grow(session, b)? {
                return Ok(false);
            }
            available = None;
        }
        let slot = match available {
            Some(slot) => slot,
            None => Self::position(&self.entries, key, b)?,
        };
        self.entries[slot] = key;
        self.used += 1;
        Ok(true)
    }

    fn grow(
        &mut self,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<bool, ResourceError> {
        let cap = self
            .entries
            .len()
            .checked_mul(2)
            .ok_or(ResourceError::Counter)?
            .max(16);
        let bytes = cap
            .checked_mul(size_of::<Entry>())
            .ok_or(ResourceError::Counter)? as u64;
        // No allocation or semantic reservation until BOTH complete peak checks
        // pass. Old table capacity remains charged throughout replacement.
        if !b.has_storage_headroom(bytes) || !session.reserve(bytes)? {
            self.stopped = true;
            return Ok(false);
        }
        let mut next = Vec::new();
        if let Err(error) = b.grow_vec(&mut next, cap) {
            // grow_vec rolls back failed actual allocations.
            session.release(bytes)?;
            return Err(error);
        }
        let result = (|| {
            b.charge_work(cap as u64 + 1)?;
            next.resize(cap, Entry::default());
            for entry in self.entries.iter().copied().filter(|entry| entry.hash != 0) {
                let slot = Self::position(&next, entry, b)?;
                next[slot] = entry;
            }
            Ok(())
        })();
        if let Err(error) = result {
            release(next, session, b)?;
            return Err(error);
        }
        release(std::mem::replace(&mut self.entries, next), session, b)?;
        Ok(true)
    }

    pub(crate) fn retire(
        self,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        release(self.entries, session, b)
    }
}

fn release(
    entries: Vec<Entry>,
    session: &mut SessionCacheBudget,
    b: &mut Budget,
) -> Result<(), ResourceError> {
    let bytes = entries
        .capacity()
        .checked_mul(size_of::<Entry>())
        .ok_or(ResourceError::Counter)? as u64;
    drop(entries);
    let a = session.release(bytes);
    let c = b.release(bytes);
    a.and(c)
}
