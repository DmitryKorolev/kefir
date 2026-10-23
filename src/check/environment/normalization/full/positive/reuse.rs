//! One immutable C1 conjunction only; bounded obligation reuse.
use super::{Budget, Pair, ResourceError, release};
use crate::syntax::hash::FastHasher;
use std::hash::Hasher;

const ACTIVATE: usize = 4096;
const SLOTS: usize = 131072;
const PROBES: usize = 16;

#[derive(Default)]
pub(super) struct Reuse {
    slots: Vec<Option<Pair>>,
    visits: usize,
}

impl Reuse {
    pub(super) fn seen(
        &mut self,
        pair: Pair,
        budget: &mut Budget,
        eligible: impl FnOnce() -> bool,
    ) -> Result<bool, ResourceError> {
        if self.visits < ACTIVATE {
            self.visits += 1;
            return Ok(false);
        }
        // Constant-time leaves retain their exact comparison, without crowding
        // out obligations whose reuse avoids child traversal. Warmup stays cheap.
        if !eligible() {
            return Ok(false);
        }
        if self.slots.is_empty() {
            self.activate(budget)?;
        }
        // One coarse upper bound, independent of hit position and build mode.
        budget.charge_work(PROBES as u64)?;
        Ok(self.search(pair, Self::start(pair)))
    }

    #[cold]
    #[inline(never)]
    fn activate(&mut self, budget: &mut Budget) -> Result<(), ResourceError> {
        // Prepay initialization and flat retirement before admission/allocation.
        // A partially allocated owner is still retired on every caller exit.
        budget.charge_work(SLOTS as u64 + 1)?;
        budget.grow_vec(&mut self.slots, SLOTS)?;
        self.slots.resize(SLOTS, None);
        Ok(())
    }

    fn start(pair: Pair) -> usize {
        let mut hash = FastHasher::new();
        let (tag, left, right) = match pair {
            Pair::Expression(a, b) => (0, a.slot(), b.slot()),
            Pair::Level(a, b) => (1, a.slot(), b.slot()),
        };
        hash.write_u32(tag);
        hash.write_u32(left);
        hash.write_u32(right);
        hash.finish() as usize & (SLOTS - 1)
    }

    fn search(&mut self, pair: Pair, start: usize) -> bool {
        for offset in 0..PROBES {
            let slot = &mut self.slots[(start + offset) & (SLOTS - 1)];
            match *slot {
                Some(previous) if previous == pair => return true,
                None => {
                    // Record an obligation before its first expansion. Its children
                    // remain in this walk's conjunction. Every child must discharge
                    // before the walk succeeds; any mismatch/error abandons both
                    // worklist and table. This is never a failed-conversion fact.
                    *slot = Some(pair);
                    return false;
                }
                _ => {}
            }
        }
        // Collision saturation (including a full table) loses reuse only.
        // No eviction, growth, failure entry or negative conclusion.
        false
    }

    pub(super) fn retire(self, budget: &mut Budget) -> Result<(), ResourceError> {
        release(self.slots, budget)
    }
}
