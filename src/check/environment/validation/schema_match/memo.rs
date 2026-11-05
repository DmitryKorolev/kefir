//! Completed exact pairs, scoped to a single schema match over immutable stores.
//! Full ordered keys are compared on hits. No pending/negative entry is stored.
use super::Pair;
use crate::resource::{Budget, ResourceError};
use std::hash::Hasher;

#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub(super) struct Key {
    kind: u32,
    left: u32,
    right: u32,
}
impl From<Pair> for Key {
    fn from(pair: Pair) -> Self {
        match pair {
            Pair::Expression(a, b) => Self {
                kind: 1,
                left: a.slot(),
                right: b.slot(),
            },
            Pair::Level(a, b) => Self {
                kind: 2,
                left: a.slot(),
                right: b.slot(),
            },
        }
    }
}
impl Key {
    fn hash(self) -> usize {
        let mut h = crate::syntax::hash::FastHasher::new();
        h.write_u32(self.kind);
        h.write_u32(self.left);
        h.write_u32(self.right);
        h.finish() as usize
    }
}
#[derive(Default)]
pub(super) struct Memo {
    inline: [Key; 8],
    used: usize,
    slots: Vec<Key>,
}
fn position(slots: &[Key], key: Key, budget: &mut Budget) -> Result<usize, ResourceError> {
    let mask = slots.len().checked_sub(1).ok_or(ResourceError::Invariant)?;
    let mut i = key.hash() & mask;
    for _ in 0..slots.len() {
        budget.charge_work(1)?;
        if slots[i].kind == 0 || slots[i] == key {
            return Ok(i);
        }
        i = (i + 1) & mask;
    }
    Err(ResourceError::Invariant)
}
impl Memo {
    pub(super) fn contains(&self, key: Key, budget: &mut Budget) -> Result<bool, ResourceError> {
        if self.slots.is_empty() {
            budget.charge_work(self.used as u64 + 1)?;
            Ok(self.inline[..self.used].contains(&key))
        } else {
            Ok(self.slots[position(&self.slots, key, budget)?] == key)
        }
    }
    pub(super) fn insert(&mut self, key: Key, budget: &mut Budget) -> Result<(), ResourceError> {
        if self.slots.is_empty() && self.used < 8 {
            self.inline[self.used] = key;
            self.used += 1;
            return Ok(());
        }
        if self.slots.is_empty() || self.used >= self.slots.len() / 2 {
            self.grow(budget)?;
        }
        let i = position(&self.slots, key, budget)?;
        if self.slots[i].kind == 0 {
            self.slots[i] = key;
            self.used += 1;
        }
        Ok(())
    }
    fn grow(&mut self, budget: &mut Budget) -> Result<(), ResourceError> {
        let cap = self
            .slots
            .len()
            .checked_mul(2)
            .ok_or(ResourceError::Counter)?
            .max(32);
        let mut next = Vec::new();
        budget.grow_vec(&mut next, cap)?;
        let result = (|| {
            budget.charge_work(cap as u64 + 1)?;
            next.resize(cap, Key::default());
            let entries = if self.slots.is_empty() {
                &self.inline[..self.used]
            } else {
                &self.slots[..]
            };
            for key in entries.iter().copied().filter(|key| key.kind != 0) {
                let i = position(&next, key, budget)?;
                next[i] = key;
            }
            Ok(())
        })();
        if let Err(e) = result {
            release(next, budget)?;
            return Err(e);
        }
        release(std::mem::replace(&mut self.slots, next), budget)
    }
    pub(super) fn retire(self, budget: &mut Budget) -> Result<(), ResourceError> {
        release(self.slots, budget)
    }
}
fn release(slots: Vec<Key>, budget: &mut Budget) -> Result<(), ResourceError> {
    let bytes = slots.capacity() * crate::resource::charged::bytes::<Key>();
    drop(slots);
    budget.release(bytes as u64)
}
