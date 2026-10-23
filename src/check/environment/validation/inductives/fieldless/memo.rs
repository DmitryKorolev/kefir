//! Own-source open-addressing mechanics, specialized to completed raw absence.
//! One immutable raw family query; exact node/depth keys and fixed family/parameter
//! scope. Only postorder completed successes enter; no equality closure.
use super::*;
use std::hash::{Hash, Hasher};
use std::mem::size_of;

#[derive(Clone, Copy, Default)]
struct Entry {
    node: u32,
    depth: u32,
    hash: u32,
}
const _: () = assert!(size_of::<Entry>() == 12);
#[derive(Default)]
pub(super) struct Memo {
    entries: Vec<Entry>,
    used: usize,
}
const _: () = assert!(size_of::<Memo>() == 32);
impl Memo {
    fn key(node: ExprId, depth: u32) -> Entry {
        let mut h = crate::syntax::hash::FastHasher::new();
        (node.slot(), depth).hash(&mut h);
        Entry {
            node: node.slot(),
            depth,
            hash: (h.finish() as u32).max(1),
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
            let e = entries[slot];
            if e.hash == 0 || (e.hash == key.hash && e.node == key.node && e.depth == key.depth) {
                return Ok(slot);
            }
            slot = (slot + 1) & mask;
        }
        Err(ResourceError::Invariant)
    }
    pub(super) fn contains(
        &self,
        node: ExprId,
        depth: u32,
        b: &mut Budget,
    ) -> Result<bool, ResourceError> {
        b.charge_work(1)?;
        if self.entries.is_empty() {
            return Ok(false);
        }
        Ok(self.entries[Self::position(&self.entries, Self::key(node, depth), b)?].hash != 0)
    }
    pub(super) fn insert(
        &mut self,
        node: ExprId,
        depth: u32,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        if self.contains(node, depth, b)? {
            return Ok(());
        }
        if self.used + 1 > self.entries.len() / 4 * 3 {
            let cap = self
                .entries
                .len()
                .checked_mul(2)
                .ok_or(ResourceError::Counter)?
                .max(16);
            let mut next = Vec::new();
            b.grow_vec(&mut next, cap)?;
            let result = (|| {
                b.charge_work(cap as u64 + 1)?;
                next.resize(cap, Entry::default());
                for e in self.entries.iter().copied().filter(|e| e.hash != 0) {
                    let slot = Self::position(&next, e, b)?;
                    next[slot] = e;
                }
                Ok(())
            })();
            if let Err(e) = result {
                let bytes = next
                    .capacity()
                    .checked_mul(size_of::<Entry>())
                    .ok_or(ResourceError::Counter)?;
                drop(next);
                b.release(bytes as u64)?;
                return Err(e);
            }
            let old = std::mem::replace(&mut self.entries, next);
            let bytes = old
                .capacity()
                .checked_mul(size_of::<Entry>())
                .ok_or(ResourceError::Counter)?;
            drop(old);
            b.release(bytes as u64)?;
        }
        let key = Self::key(node, depth);
        let slot = Self::position(&self.entries, key, b)?;
        self.entries[slot] = key;
        self.used += 1;
        Ok(())
    }
    pub(super) fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let bytes = self
            .entries
            .capacity()
            .checked_mul(size_of::<Entry>())
            .ok_or(ResourceError::Counter)?;
        drop(self);
        b.release(bytes as u64)
    }
}
