//! Completed-normalization table and shared admission accounting.
//! Used by the full traversal through its private borrowed session owner.
use super::Normal;
use crate::resource::{Budget, Event, ReductionPath, ResourceError, SessionCacheBudget, profile};
use crate::syntax::expressions::Expressions;
use std::hash::Hasher;
use std::mem::size_of;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Entry {
    source: u32,
    result: u32,
    height: u32,
    hash: u32,
}
const _: () = assert!(size_of::<Entry>() == 16);

/// Scope required BEFORE semantic use: one fixed ordinary declaration session,
/// expression/level/name origins, immutable validated environment/frontiers and
/// permission class. Exact expression handles only. Free identities must be
/// active, unique and immutable; caller supplies checked, well-scoped syntax.
/// The traversal owner supplies debug active-free assertions and fixed borrows.
/// No completed result may cross session,
/// context reclamation, permission change, or thread. Head results do not enter.
///
/// Only successful full normalization may call insert. Completion includes
/// binder abstraction/leave and all fallible child work. On ANY error/panic the
/// declaration owner must discard the table, locals and generated syntax. This
/// storage helper confers no checkedness and grants no input installation.
#[derive(Default)]
pub(crate) struct Cache {
    entries: Vec<Entry>,
    used: usize,
    stopped: bool,
}
const _: () = assert!(size_of::<Cache>() <= 40);
impl Cache {
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
    /// A hit must pass the route certificate BEFORE returning its stored handle.
    /// Invalid caller origins/scope are not repaired by an in-range handle.
    pub(super) fn get(
        &self,
        source: u32,
        incoming: ReductionPath,
        expressions: &Expressions,
        b: &mut Budget,
    ) -> Result<Option<Normal>, ResourceError> {
        // Attempted cache API lookup, including later budget/certificate failure;
        // internal hash-table probes and insertion searches are not these events.
        b.observe(Event::NormalizationCacheProbes, 1);
        b.charge_work(1)?;
        if self.entries.is_empty() {
            return Ok(None);
        }
        let entry = self.entries[Self::position(&self.entries, Self::key(source), b)?];
        if entry.hash == 0 {
            return Ok(None);
        }
        incoming.after_height(entry.height)?;
        let result = Normal {
            expression: expressions.resolve_slot(entry.result, b)?,
            height: entry.height,
        };
        b.observe(Event::NormalizationCacheHits, 1);
        Ok(Some(result))
    }
    pub(super) fn insert(
        &mut self,
        source: u32,
        result: Normal,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        b.charge_work(1)?;
        if result.height > profile::REDUCTION_PATH {
            return Err(ResourceError::Invariant);
        }
        if self.stopped {
            return Ok(());
        }
        let mut key = Self::key(source);
        key.result = result.expression.slot();
        key.height = result.height;
        let mut available = None;
        if !self.entries.is_empty() {
            let slot = Self::position(&self.entries, key, b)?;
            if self.entries[slot].hash != 0 {
                // Fresh result handles may differ, but the deterministic route
                // height must agree in this fixed session. Never hide a broken
                // certificate behind an existing entry.
                if self.entries[slot].height != result.height {
                    return Err(ResourceError::Invariant);
                }
                return Ok(());
            }
            available = Some(slot);
        }
        if self.used + 1 > self.entries.len() / 4 * 3 {
            if !self.grow(session, b)? {
                return Ok(());
            }
            available = None;
        }
        let slot = match available {
            Some(slot) => slot,
            None => Self::position(&self.entries, key, b)?,
        };
        self.entries[slot] = key;
        self.used += 1;
        // Exactly one new completed entry is now installed in this cache.
        b.observe(Event::NormalizationCacheInsertions, 1);
        Ok(())
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
            // grow_vec rolls back failed actual allocations. An unexpected
            // allocator layout invariant requires whole-run discard as elsewhere.
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
    pub(super) fn retire(
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
