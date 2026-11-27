//! Completed well-typedness of closed original syntax in one committed State.
//! Entries contain no graph-local ID. A hit supplies only the well-typed-input
//! premise of infer-only. Reconstruct the type in the current graph and check
//! the caller's independent expected type. Unchecked results are never staged.
use super::{Budget, NameId, ResourceError};

mod open;
pub(super) use open::{Cursor, Lexical};

const SLOTS: usize = 4096;
const PENDING: usize = 32;
pub(super) const OPEN_MIN_WORK: u64 = 1024;
pub(super) const MIN_WORK: u64 = 256;

#[derive(Clone, Copy, Default, Eq, PartialEq)]
struct Key {
    expr: u32,
    // Zero is an empty slot. Otherwise arity plus one, including arity zero.
    arity_plus_one: u8,
    confirmed: bool,
    params: [u32; 4],
}
crate::resource::charged::charged! { Key => 24 }

fn slot(expr: u32) -> usize {
    (expr.wrapping_mul(2654435761) >> 20) as usize
}

#[derive(Default)]
pub(super) struct SourceJudgments {
    pub(super) open: open::Open,
    slots: Vec<Key>,
    pending: Vec<Key>,
}

impl SourceJudgments {
    pub(super) fn contains(&self, expr: u32, params: &[NameId]) -> bool {
        self.matching(expr, params).is_some_and(|row| row.confirmed)
    }

    fn matching(&self, expr: u32, params: &[NameId]) -> Option<&Key> {
        self.slots.get(slot(expr)).filter(|row| {
            row.expr == expr
                && row.arity_plus_one as usize == params.len().saturating_add(1)
                && row.params.iter().zip(params).all(|(&a, b)| a == b.0)
        })
    }

    pub(super) fn stage(
        &mut self,
        expr: u32,
        params: &[NameId],
        budget: &mut Budget,
    ) -> Result<(), ResourceError> {
        if params.len() > 4 || self.pending.len() == PENDING {
            return Ok(());
        }
        let mut row = Key {
            expr,
            arity_plus_one: params.len() as u8 + 1,
            // Only installed observations can confirm this completed check.
            confirmed: self.matching(expr, params).is_some(),
            ..Key::default()
        };
        for (a, b) in row.params.iter_mut().zip(params) {
            *a = b.0;
        }
        // Prepay the bounded pending scan and eventual installation write.
        budget.charge_work(self.pending.len() as u64 + 1)?;
        if self.pending.contains(&row) {
            return Ok(());
        }
        if self.slots.is_empty() {
            budget.grow_vec(&mut self.slots, SLOTS)?;
            budget.charge_work(SLOTS as u64)?;
            self.slots.resize(SLOTS, Key::default());
        }
        if self.pending.capacity() == 0 {
            budget.grow_vec(&mut self.pending, PENDING)?;
        }
        self.pending.push(row);
        Ok(())
    }

    pub(super) fn abandon(&mut self) {
        self.open.clear();
        self.pending.clear();
    }

    pub(super) fn publish(&mut self) {
        self.open.publish();
        for row in self.pending.drain(..) {
            self.slots[slot(row.expr)] = row;
        }
    }

    pub(super) fn retire(&mut self, budget: &mut Budget) -> Result<(), ResourceError> {
        let old = std::mem::take(self);
        let bytes = old.open.held()
            + (old.slots.capacity() + old.pending.capacity())
                * crate::resource::charged::bytes::<Key>();
        drop(old);
        budget.release(bytes as u64)
    }
}
