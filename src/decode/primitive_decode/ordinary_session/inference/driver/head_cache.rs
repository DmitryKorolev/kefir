//! One ordinary driver's exact closed-source completed exposure results.
//! Errors are terminal; a miss or stopped admission supplies no judgment.
use super::*;
use crate::check::environment::normalization::Exposure;
use crate::resource::SessionCacheBudget;
mod key;
#[derive(Clone, Copy, Default)]
struct Entry {
    source: u32,
    result: u32,
    height: u32,
    hash: u32,
    permission: u32,
}
const _: () = assert!(size_of::<Entry>() == 20);
const PROBES: usize = 8;
#[derive(Default)]
pub(super) struct Cache {
    entries: Vec<Entry>,
    used: usize,
    stopped: bool,
}
const _: () = assert!(size_of::<Cache>() == 40);
/// Immutable request identity, not proof that its evaluator completed. The
/// driver may consult this only in Completed::Head and publish after retirement.
#[derive(Clone, Copy)]
pub(super) struct Origin {
    pub epoch: u64,
    source: ExprId,
    incoming: ReductionPath,
    exposure: Exposure,
}
const _: () = assert!(size_of::<Origin>() == 24);
impl Origin {
    pub(super) fn new(source: ExprId, incoming: ReductionPath, exposure: Exposure) -> Self {
        Self {
            epoch: 0,
            source,
            incoming,
            exposure,
        }
    }
    pub(super) fn request(self, epoch: u64) -> Option<(ExprId, ReductionPath, Exposure)> {
        (self.epoch == epoch).then_some((self.source, self.incoming, self.exposure))
    }
}
#[derive(Clone, Copy)]
pub(super) struct Candidate {
    pub source: ExprId,
    pub result: ExprId,
    pub height: u32,
    pub exposure: Exposure,
}
pub(super) fn closed(
    root: ExprId,
    expressions: &Expressions,
    b: &mut Budget,
) -> Result<bool, ResourceError> {
    let node = expressions.get(root, b)?;
    Ok(node.loose_range() == 0 && !node.has_free())
}
fn permission(exposure: Exposure) -> u32 {
    match exposure {
        Exposure::Cheap => 1,
        Exposure::Full => 2,
        Exposure::NonDelta => 3,
    }
}
impl Cache {
    fn hash(
        source: ExprId,
        exposure: Exposure,
        expressions: &Expressions,
        b: &mut Budget,
    ) -> Result<u32, ResourceError> {
        Ok((expressions
            .get(source, b)?
            .syntax_fingerprint()
            .rotate_left(2)
            ^ permission(exposure))
        .max(1))
    }
    fn position(
        &self,
        source: ExprId,
        exposure: Exposure,
        hash: u32,
        expressions: &Expressions,
        levels: &Levels,
        b: &mut Budget,
    ) -> Result<Option<usize>, ResourceError> {
        let mask = self
            .entries
            .len()
            .checked_sub(1)
            .ok_or(ResourceError::Invariant)?;
        let mut slot = hash as usize & mask;
        for _ in 0..self.entries.len().min(PROBES) {
            b.charge_work(1)?;
            let entry = self.entries[slot];
            if entry.hash == 0 {
                return Ok(Some(slot));
            }
            if entry.hash == hash
                && entry.permission == permission(exposure)
                && key::same(
                    source,
                    expressions.resolve_slot(entry.source, b)?,
                    expressions,
                    levels,
                    b,
                )?
            {
                return Ok(Some(slot));
            }
            slot = (slot + 1) & mask;
        }
        Ok(None)
    }
    pub(super) fn get(
        &self,
        source: ExprId,
        exposure: Exposure,
        incoming: ReductionPath,
        work: &mut Working<'_>,
    ) -> Result<Option<Completed>, ResourceError> {
        if self.entries.is_empty() || !closed(source, work.expressions, work.budget)? {
            return Ok(None);
        }
        let hash = Self::hash(source, exposure, work.expressions, work.budget)?;
        let Some(slot) = self.position(
            source,
            exposure,
            hash,
            work.expressions,
            work.levels,
            work.budget,
        )?
        else {
            return Ok(None);
        };
        let entry = self.entries[slot];
        if entry.hash == 0 {
            return Ok(None);
        }
        let result = work.expressions.resolve_slot(entry.result, work.budget)?;
        // Resolve first and replay the complete height before minting status.
        // Equal stored IDs certify an unchanged completed hit; unequal IDs do
        // not certify reduction. No miss or incomplete computation is a reply.
        let head = Head {
            expression: result,
            path: incoming.after_height(entry.height)?,
        };
        Ok(Some(if entry.source == entry.result {
            Completed::UnchangedHead(head)
        } else {
            Completed::Head(head)
        }))
    }
    pub(super) fn insert(
        &mut self,
        candidate: Candidate,
        work: &mut Working<'_>,
    ) -> Result<(), ResourceError> {
        let Candidate {
            source,
            result,
            height,
            exposure,
        } = candidate;
        if self.stopped {
            return Ok(());
        }
        let hash = Self::hash(source, exposure, work.expressions, work.budget)?;
        if !self.entries.is_empty() {
            let Some(slot) = self.position(
                source,
                exposure,
                hash,
                work.expressions,
                work.levels,
                work.budget,
            )?
            else {
                return Ok(());
            };
            if self.entries[slot].hash != 0 {
                return Ok(());
            }
        }
        if self.used + 1 > self.entries.len() / 4 * 3 {
            let cap = self
                .entries
                .len()
                .checked_mul(2)
                .ok_or(ResourceError::Counter)?
                .max(16);
            let bytes = cap
                .checked_mul(size_of::<Entry>())
                .ok_or(ResourceError::Counter)? as u64;
            if !work.budget.has_storage_headroom(bytes) || !work.caches.reserve(bytes)? {
                self.stopped = true;
                return Ok(());
            }
            let mut next = Vec::new();
            if let Err(error) = work.budget.grow_vec(&mut next, cap) {
                // A post-allocation layout invariant can leave physical storage
                // owned here. Retire the charged requested layout, not allocator
                // excess capacity that was never admitted to either ledger.
                let allocated = next.capacity() != 0;
                drop(next);
                let cache = work.caches.release(bytes);
                let storage = if allocated {
                    work.budget.release(bytes)
                } else {
                    Ok(())
                };
                return Err(select(error, cache.and(storage).err()));
            }
            let mut retained = 0;
            let grown = (|| {
                work.budget.charge_work(cap as u64 + 1)?;
                next.resize(cap, Entry::default());
                for entry in self.entries.iter().copied().filter(|entry| entry.hash != 0) {
                    let mut slot = entry.hash as usize & (cap - 1);
                    // Optional entries that cannot retain bounded reachability
                    // are dropped; no semantic result depends on their presence.
                    for _ in 0..PROBES {
                        work.budget.charge_work(1)?;
                        if next[slot].hash == 0 {
                            next[slot] = entry;
                            retained += 1;
                            break;
                        }
                        slot = (slot + 1) & (cap - 1);
                    }
                }
                Ok(())
            })();
            if let Err(error) = grown {
                let cleanup = release(next, &mut work.caches, work.budget).err();
                return Err(select(error, cleanup));
            }
            release(
                std::mem::replace(&mut self.entries, next),
                &mut work.caches,
                work.budget,
            )?;
            self.used = retained;
        }
        let Some(slot) = self.position(
            source,
            exposure,
            hash,
            work.expressions,
            work.levels,
            work.budget,
        )?
        else {
            return Ok(());
        };
        self.entries[slot] = Entry {
            source: source.slot(),
            result: result.slot(),
            height,
            hash,
            permission: permission(exposure),
        };
        self.used += 1;
        Ok(())
    }
    pub(super) fn retire(self, work: &mut Working<'_>) -> Result<(), ResourceError> {
        release(self.entries, &mut work.caches, work.budget)
    }
}
fn release(
    values: Vec<Entry>,
    session: &mut SessionCacheBudget,
    b: &mut Budget,
) -> Result<(), ResourceError> {
    let bytes = values
        .capacity()
        .checked_mul(size_of::<Entry>())
        .ok_or(ResourceError::Counter)? as u64;
    drop(values);
    let cache = session.release(bytes);
    let storage = b.release(bytes);
    cache.and(storage)
}

fn select(error: ResourceError, cleanup: Option<ResourceError>) -> ResourceError {
    use crate::resource::failure::FailureOutcome;
    if error.failure_report().outcome == FailureOutcome::InternalError {
        return error;
    }
    cleanup
        .filter(|e| e.failure_report().outcome == FailureOutcome::InternalError)
        .unwrap_or(error)
}
