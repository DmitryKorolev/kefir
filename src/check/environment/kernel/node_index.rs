//! Exact index for persistent environment extensions, spine cells and completed neutral steps in one value
//! graph. A hash selects candidates. Only full immediate-field equality in
//! the owning arena can return an ID. Zero is the empty cell/environment. Indexed neutral values are
//! nonzero because their head already exists before an extension is built.
//! Snapshot transfer moves the index with those arenas. Capacity reuse clears
//! all entries before the next graph assigns its first ID.
use super::*;

#[derive(Default)]
pub(super) struct NodeIndex {
    slots: Vec<(u32, u32)>,
    used: usize,
}

pub(super) enum Probe {
    Found(u32),
    Vacant(usize),
}

impl NodeIndex {
    pub(super) fn clear(&mut self) {
        self.slots.clear();
        self.used = 0;
    }

    pub(super) fn retire(&mut self) -> Self {
        let owner = std::mem::take(self);
        if owner.slots.capacity() * 8 <= RETAIN {
            owner
        } else {
            Self::default()
        }
    }

    #[inline]
    pub(super) fn probe(&self, hash: u32, same: impl Fn(u32) -> bool) -> Probe {
        if self.slots.is_empty() {
            return Probe::Vacant(0);
        }
        let mask = self.slots.len() - 1;
        let mut at = hash as usize & mask;
        loop {
            let (tag, id) = self.slots[at];
            if id == 0 {
                return Probe::Vacant(at);
            }
            if tag == hash && same(id) {
                return Probe::Found(id);
            }
            at = (at + 1) & mask;
        }
    }

    /// No index mutation may intervene between a vacant probe and insertion.
    /// The caller finishes any fallible arena reservation before publishing an ID.
    #[inline]
    pub(super) fn insert(
        &mut self,
        mut at: usize,
        hash: u32,
        id: u32,
        b: &mut Budget,
        reserved: &mut u64,
    ) -> R<()> {
        if self.used >= self.slots.len() - self.slots.len() / 4 {
            self.grow(b, reserved)?;
            let mask = self.slots.len() - 1;
            at = hash as usize & mask;
            while self.slots[at].1 != 0 {
                at = (at + 1) & mask;
            }
        }
        self.slots[at] = (hash, id);
        self.used += 1;
        Ok(())
    }

    #[cold]
    fn grow(&mut self, b: &mut Budget, reserved: &mut u64) -> R<()> {
        let old = self.slots.len();
        let size = old.checked_mul(2).ok_or(ResourceError::Counter)?.max(16);
        let bytes = size.checked_mul(8).ok_or(ResourceError::Counter)?;
        charge_bytes(b, reserved, bytes)?;
        let mut next = if old == 0 {
            std::mem::take(&mut self.slots)
        } else {
            Vec::new()
        };
        next.try_reserve_exact(size).map_err(|_| alloc_failed())?;
        next.resize(size, (0, 0));
        for &(hash, id) in &self.slots {
            if id == 0 {
                continue;
            }
            let mut at = hash as usize & (size - 1);
            while next[at].1 != 0 {
                at = (at + 1) & (size - 1);
            }
            next[at] = (hash, id);
        }
        self.slots = next;
        let old_bytes = (old as u64) * 8;
        b.release(old_bytes)?;
        *reserved = reserved
            .checked_sub(old_bytes)
            .ok_or(ResourceError::Invariant)?;
        Ok(())
    }
}
