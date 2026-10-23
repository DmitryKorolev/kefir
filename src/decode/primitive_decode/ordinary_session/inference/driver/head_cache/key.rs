//! Exact raw syntax keys for; never a conversion judgment.
use crate::resource::{Budget, ResourceError, failure::FailureOutcome};
use crate::syntax::expressions::{ExprId, ExprKind, Expressions};
use crate::syntax::levels::Levels;
use std::hash::Hasher;
use std::mem::size_of;

type Pair = (ExprId, ExprId);
const _: () = assert!(size_of::<Pair>() == 8);

#[derive(Clone, Copy, Default)]
struct Entry {
    left: u32,
    right: u32,
    hash: u32,
}
const _: () = assert!(size_of::<Entry>() == 12);

#[derive(Default)]
struct Seen {
    entries: Vec<Entry>,
    used: usize,
}

impl Seen {
    fn position(entries: &[Entry], key: Entry, b: &mut Budget) -> Result<usize, ResourceError> {
        let mask = entries
            .len()
            .checked_sub(1)
            .ok_or(ResourceError::Invariant)?;
        let mut slot = key.hash as usize & mask;
        for _ in 0..entries.len() {
            b.charge_work(1)?;
            let old = entries[slot];
            if old.hash == 0
                || (old.hash == key.hash && old.left == key.left && old.right == key.right)
            {
                return Ok(slot);
            }
            slot = (slot + 1) & mask;
        }
        Err(ResourceError::Invariant)
    }

    fn grow(&mut self, b: &mut Budget) -> Result<(), ResourceError> {
        let count = self
            .entries
            .len()
            .checked_mul(2)
            .ok_or(ResourceError::Counter)?
            .max(8);
        let mut next = Vec::new();
        let result = (|| {
            b.grow_vec(&mut next, count)?;
            b.charge_work(count as u64)?;
            next.resize(count, Entry::default());
            for old in &self.entries {
                b.charge_work(1)?;
                if old.hash != 0 {
                    let slot = Self::position(&next, *old, b)?;
                    next[slot] = *old;
                }
            }
            Ok(())
        })();
        if let Err(error) = result {
            let cleanup = release(next, b);
            return Err(select([Some(error), cleanup.err(), None, None]).unwrap());
        }
        let old = std::mem::replace(&mut self.entries, next);
        release(old, b)
    }

    /// These are scheduled conjunctions, not completed semantic facts. Every
    /// queued child must still finish before the enclosing query returns true.
    fn insert(&mut self, pair: Pair, b: &mut Budget) -> Result<bool, ResourceError> {
        let mut h = crate::syntax::hash::FastHasher::new();
        h.write_u32(pair.0.slot());
        h.write_u32(pair.1.slot());
        let hash = h.finish() as u32;
        let key = Entry {
            left: pair.0.slot(),
            right: pair.1.slot(),
            hash: hash.max(1),
        };
        if !self.entries.is_empty() {
            let slot = Self::position(&self.entries, key, b)?;
            if self.entries[slot].hash != 0 {
                return Ok(false);
            }
        }
        if self.used >= self.entries.len() - self.entries.len() / 4 {
            self.grow(b)?;
        }
        let slot = Self::position(&self.entries, key, b)?;
        self.entries[slot] = key;
        self.used = self.used.checked_add(1).ok_or(ResourceError::Counter)?;
        Ok(true)
    }
}

fn release<T: Copy>(values: Vec<T>, b: &mut Budget) -> Result<(), ResourceError> {
    let bytes = values
        .capacity()
        .checked_mul(size_of::<T>())
        .ok_or(ResourceError::Counter)?;
    drop(values);
    b.release(bytes as u64)
}

fn select(errors: [Option<ResourceError>; 4]) -> Option<ResourceError> {
    errors
        .into_iter()
        .flatten()
        .find(|e| e.failure_report().outcome == FailureOutcome::InternalError)
        .or_else(|| errors.into_iter().flatten().next())
}

fn push(stack: &mut Vec<Pair>, pair: Pair, b: &mut Budget) -> Result<(), ResourceError> {
    let count = stack.len().checked_add(1).ok_or(ResourceError::Counter)?;
    b.reserve_frames(1)?;
    if let Err(error) = b.grow_vec(stack, count) {
        let cleanup = b.release_frames(1);
        return Err(select([Some(error), cleanup.err(), None, None]).unwrap());
    }
    stack.push(pair);
    Ok(())
}

/// The caller fixes immutable expression/level origins for this one query.
/// Raw names, annotations and level handles are part of the key. No equality,
/// mismatch or interrupted obligation survives the query or grants checkedness.
pub(super) fn same(
    left: ExprId,
    right: ExprId,
    expressions: &Expressions,
    levels: &Levels,
    budget: &mut Budget,
) -> Result<bool, ResourceError> {
    budget.charge_work(1)?; // flat scratch retirement
    if left == right {
        // Stored-handle identity needs no traversal scratch, but still validate
        // the descriptor before treating this sufficient key condition as true.
        expressions
            .get(left, budget)?
            .kind(expressions, levels, budget)?;
        return Ok(true);
    }
    let mut stack = Vec::new();
    let mut seen = Seen::default();
    let result = (|| {
        push(&mut stack, (left, right), budget)?;
        while let Some((left, right)) = stack.pop() {
            budget.release_frames(1)?;
            budget.charge_work(1)?;
            let a = expressions.get(left, budget)?;
            let ak = a.kind(expressions, levels, budget)?;
            let z = expressions.get(right, budget)?;
            let zk = z.kind(expressions, levels, budget)?;
            if left == right {
                continue;
            }
            if a.syntax_fingerprint() != z.syntax_fingerprint() {
                return Ok(false);
            }
            if !seen.insert((left, right), budget)? {
                continue;
            }
            match (ak, zk) {
                (ExprKind::Bound(a), ExprKind::Bound(z))
                | (ExprKind::Free(a), ExprKind::Free(z))
                    if a == z => {}
                (ExprKind::Sort(a), ExprKind::Sort(z)) if a == z => {}
                (ExprKind::App(af, aa), ExprKind::App(zf, za)) => {
                    push(&mut stack, (aa, za), budget)?;
                    push(&mut stack, (af, zf), budget)?;
                }
                (ExprKind::Pi(an, ad, ab, ai), ExprKind::Pi(zn, zd, zb, zi))
                | (ExprKind::Lambda(an, ad, ab, ai), ExprKind::Lambda(zn, zd, zb, zi))
                    if an == zn && ai == zi =>
                {
                    push(&mut stack, (ab, zb), budget)?;
                    push(&mut stack, (ad, zd), budget)?;
                }
                (ExprKind::Let(an, at, av, ab, ai), ExprKind::Let(zn, zt, zv, zb, zi))
                    if an == zn && ai == zi =>
                {
                    push(&mut stack, (ab, zb), budget)?;
                    push(&mut stack, (av, zv), budget)?;
                    push(&mut stack, (at, zt), budget)?;
                }
                (ExprKind::Projection(an, ai, av), ExprKind::Projection(zn, zi, zv))
                    if an == zn && ai == zi =>
                {
                    push(&mut stack, (av, zv), budget)?;
                }
                (ExprKind::Constant(an, aa), ExprKind::Constant(zn, za))
                    if an == zn && aa.len() == za.len() =>
                {
                    budget.charge_work(aa.len() as u64)?;
                    if aa != za {
                        return Ok(false);
                    }
                }
                (ExprKind::Natural(a), ExprKind::Natural(z))
                | (ExprKind::String(a), ExprKind::String(z))
                    if a.len() == z.len() =>
                {
                    budget.charge_work(a.len() as u64)?;
                    if a != z {
                        return Ok(false);
                    }
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    })();
    let pending = stack.len();
    let stack_cleanup = release(stack, budget);
    let seen_cleanup = release(seen.entries, budget);
    let frame_cleanup = budget.release_frames(pending);
    match select([
        result.as_ref().err().copied(),
        stack_cleanup.err(),
        seen_cleanup.err(),
        frame_cleanup.err(),
    ]) {
        Some(error) => Err(error),
        None => result,
    }
}
