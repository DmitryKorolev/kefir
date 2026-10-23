//! One-pass normalization, private to one U comparison unless
//! an operation-scoped shared memo is supplied by the caller.
use super::{Helpers, memo::SharedTable, release_vec, substitution::Map};
use crate::resource::{Budget, ResourceError};
use crate::syntax::levels::{LevelId, LevelKind, OrderedLevelNames};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::mem::size_of;

mod domination;

// Test-only phase witness: (U root, collection stage); no production state.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum UniverseComparison {
    Equal,
    NotEqual,
}
#[derive(Clone, Copy)]
enum Frame {
    Visit(LevelId),
    IMax {
        source: LevelId,
        offset: u32,
    },
    Max {
        source: LevelId,
        offset: u32,
        frontier: usize,
        results: usize,
    },
}
const _: () = assert!(size_of::<Frame>() <= 32);
#[derive(Clone, Copy, Default)]
struct SeenEntry {
    source: u32,
    hash: u32,
}
const _: () = assert!(size_of::<SeenEntry>() == 8);
#[derive(Default)]
struct Seen {
    entries: Vec<SeenEntry>,
    used: usize,
}
impl Seen {
    fn hash(source: u32) -> u32 {
        let mut h = crate::syntax::hash::FastHasher::new();
        source.hash(&mut h);
        (h.finish() as u32).max(1)
    }
    fn position(
        entries: &[SeenEntry],
        key: SeenEntry,
        b: &mut Budget,
    ) -> Result<usize, ResourceError> {
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
    fn add(&mut self, source: LevelId, b: &mut Budget) -> Result<bool, ResourceError> {
        let key = SeenEntry {
            source: source.slot(),
            hash: Self::hash(source.slot()),
        };
        self.add_key(key, b)
    }
    // Hash is nonzero by construction; exact source still decides every hit.
    fn add_key(&mut self, key: SeenEntry, b: &mut Budget) -> Result<bool, ResourceError> {
        let mut slot = None;
        if !self.entries.is_empty() {
            let i = Self::position(&self.entries, key, b)?;
            if self.entries[i].hash != 0 {
                return Ok(false);
            }
            slot = Some(i);
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
                next.resize(cap, SeenEntry::default());
                for entry in self.entries.iter().copied().filter(|e| e.hash != 0) {
                    let i = Self::position(&next, entry, b)?;
                    next[i] = entry;
                }
                Ok(())
            })();
            if let Err(error) = result {
                release_vec(next, b)?;
                return Err(error);
            }
            release_vec(std::mem::replace(&mut self.entries, next), b)?;
            slot = Some(Self::position(&self.entries, key, b)?);
        }
        self.entries[slot.ok_or(ResourceError::Invariant)?] = key;
        self.used += 1;
        Ok(true)
    }
}
fn push<T: Copy>(v: &mut Vec<T>, value: T, b: &mut Budget) -> Result<(), ResourceError> {
    let needed = v.len().checked_add(1).ok_or(ResourceError::Counter)?;
    b.grow_vec(v, needed)?;
    v.push(value);
    Ok(())
}
fn frame<T: Copy>(v: &mut Vec<T>, value: T, b: &mut Budget) -> Result<(), ResourceError> {
    b.reserve_frames(1)?;
    if let Err(error) = push(v, value, b) {
        b.release_frames(1)?;
        return Err(error);
    }
    Ok(())
}
struct Normalizer<'r, 'h, 'a, N> {
    h: &'h mut Helpers<'a, N>,
    source_end: usize,
    // Only completed N(source) values for this frozen prefix and this U request.
    // Neither this map nor any normalized handle escapes U. Names remain immutable.
    memo: Map,
    // Optional operation-scoped table: also only completed N(source) values for
    // the same frozen prefix, but retained across the owner's U requests. Its
    // entries are retired by the table's owner before any slot can be reused.
    shared: Option<SharedTable<'r>>,
    frames: Vec<Frame>,
    results: Vec<LevelId>,
    frontier: Vec<LevelId>,
    scan: Vec<LevelId>,
}
#[derive(Clone, Copy)]
enum Roots {
    Raw(LevelId),
    Results { start: usize, end: usize },
}
impl<N: OrderedLevelNames> Helpers<'_, N> {
    /// Caller validates scope before U. The only decisive outcomes are completed
    /// algorithmic Equal/NotEqual, not a declarative equality/inequality closure.
    /// A failed comparison poisons the enclosing helper operation, even if ignored.
    pub(crate) fn compare_universes(
        &mut self,
        a: LevelId,
        c: LevelId,
    ) -> Result<UniverseComparison, ResourceError> {
        self.compare_universes_with(a, c, None)
    }
    /// Same contract as `compare_universes`, with an optional operation-scoped
    /// memo: completed results for sources of the enclosing declaration's
    /// frozen prefix are retained across this owner's U requests (as
    /// amended). The table borrows outlive every call; none of its state
    /// escapes the owner, which retires it before any slot can be reused.
    pub(crate) fn compare_universes_with(
        &mut self,
        a: LevelId,
        c: LevelId,
        shared: Option<SharedTable<'_>>,
    ) -> Result<UniverseComparison, ResourceError> {
        self.attempt(|h| {
            if h.structural(a, c)? {
                return Ok(UniverseComparison::Equal);
            }
            h.budget.charge_work(5)?; // all owned flat releases, including memo
            let source_end = h.levels.len();
            let mut n = Normalizer {
                h,
                source_end,
                memo: Map::default(),
                shared,
                frames: Vec::new(),
                results: Vec::new(),
                frontier: Vec::new(),
                scan: Vec::new(),
            };
            let result = (|| {
                let left = n.normalize(a)?;
                let right = n.normalize(c)?;
                Ok(if n.h.structural(left, right)? {
                    UniverseComparison::Equal
                } else {
                    UniverseComparison::NotEqual
                })
            })();
            let remaining = n.frames.len() + n.results.len() + n.scan.len();
            let frames = n.h.budget.release_frames(remaining);
            let a = release_vec(n.frames, n.h.budget);
            let c = release_vec(n.results, n.h.budget);
            let d = release_vec(n.frontier, n.h.budget);
            let e = release_vec(n.scan, n.h.budget);
            let f = release_vec(n.memo.entries, n.h.budget);
            frames?;
            a?;
            c?;
            d?;
            e?;
            f?;
            result
        })
    }
}
impl<N: OrderedLevelNames> Normalizer<'_, '_, '_, N> {
    fn completed(&mut self, source: LevelId, result: LevelId) -> Result<(), ResourceError> {
        // Cross-request reuse lives only in the operation-scoped table
        // The per-request memo stays authoritative
        // whenever the table declined to retain the entry, reproducing the
        // unamended charges exactly.
        let mut retained = false;
        if let Some(table) = self.shared.as_mut() {
            retained =
                table
                    .memo
                    .insert(source.slot(), result.slot(), table.ledger, self.h.budget)?;
        }
        if !retained {
            self.memo
                .insert(source.slot(), result.slot(), self.h.budget)?;
        }
        frame(&mut self.results, result, self.h.budget)
    }
    /// Memo consultation order: the shared table (a hit serves an earlier
    /// request's completed result for the same immutable source), then the
    /// per-request memo.
    fn memo_get(&mut self, source: u32) -> Result<Option<u32>, ResourceError> {
        let shared = match self.shared.as_mut() {
            Some(table) => table.memo.get(source, self.h.budget)?,
            None => None,
        };
        if let Some(value) = shared {
            return Ok(Some(value));
        }
        Ok(self
            .memo
            .get(source, self.h.budget)?
            .map(|entry| entry.value))
    }
    fn pop(&mut self) -> Result<LevelId, ResourceError> {
        let id = self.results.pop().ok_or(ResourceError::Invariant)?;
        self.h.budget.release_frames(1)?;
        Ok(id)
    }
    fn normalize(&mut self, root: LevelId) -> Result<LevelId, ResourceError> {
        if !self.frames.is_empty()
            || !self.results.is_empty()
            || !self.frontier.is_empty()
            || !self.scan.is_empty()
        {
            return Err(ResourceError::Invariant);
        }
        frame(&mut self.frames, Frame::Visit(root), self.h.budget)?;
        while let Some(f) = self.frames.pop() {
            self.h.budget.release_frames(1)?;
            self.h.budget.charge_work(1)?;
            self.h
                .budget
                .observe(crate::resource::Event::MachineSteps, 1);
            match f {
                Frame::Visit(id) => {
                    if id.slot() as usize >= self.source_end {
                        return Err(ResourceError::Invariant);
                    }
                    if let Some(value) = self.memo_get(id.slot())? {
                        let result = self.h.levels.resolve_slot(value, self.h.budget)?;
                        frame(&mut self.results, result, self.h.budget)?;
                        continue;
                    }
                    let (base, offset) = self.h.offset(id)?;
                    match self.h.levels.get(base, self.h.budget)?.kind() {
                        LevelKind::Zero | LevelKind::Param(_) => self.completed(id, id)?,
                        LevelKind::IMax(a, c) => {
                            frame(
                                &mut self.frames,
                                Frame::IMax { source: id, offset },
                                self.h.budget,
                            )?;
                            frame(&mut self.frames, Frame::Visit(c), self.h.budget)?;
                            frame(&mut self.frames, Frame::Visit(a), self.h.budget)?;
                        }
                        LevelKind::Max(..) => {
                            let start = self.frontier.len();
                            self.collect(Roots::Raw(base))?;
                            frame(
                                &mut self.frames,
                                Frame::Max {
                                    source: id,
                                    offset,
                                    frontier: start,
                                    results: self.results.len(),
                                },
                                self.h.budget,
                            )?;
                            for source in self.frontier[start..].iter().rev().copied() {
                                self.h.budget.charge_work(1)?;
                                frame(&mut self.frames, Frame::Visit(source), self.h.budget)?;
                            }
                        }
                        LevelKind::Succ(_) => return Err(ResourceError::Invariant),
                    }
                }
                Frame::IMax { source, offset } => {
                    let right = self.pop()?;
                    let left = self.pop()?;
                    let result = self.h.imax(left, right)?;
                    let result = self.successors(result, offset)?;
                    self.completed(source, result)?;
                }
                Frame::Max {
                    source,
                    offset,
                    frontier: start,
                    results: result_start,
                } => {
                    let normalized = self.frontier.len();
                    self.collect(Roots::Results {
                        start: result_start,
                        end: self.results.len(),
                    })?;
                    // Move only the Vec descriptor out to permit fallible helper
                    // calls while mutating its suffix; always restore ownership.
                    let mut values = std::mem::take(&mut self.frontier);
                    let result = self.rebuild_frontier(&mut values[normalized..], offset);
                    self.frontier = values;
                    let result = result?;
                    self.frontier.truncate(start);
                    self.h
                        .budget
                        .release_frames(self.results.len() - result_start)?;
                    self.results.truncate(result_start);
                    self.completed(source, result)?;
                }
            }
        }
        if self.results.len() != 1 || !self.frontier.is_empty() || !self.scan.is_empty() {
            return Err(ResourceError::Invariant);
        }
        self.pop()
    }
    fn collect(&mut self, roots: Roots) -> Result<(), ResourceError> {
        if !self.scan.is_empty() {
            return Err(ResourceError::Invariant);
        }
        self.h.budget.charge_work(1)?; // local seen table release, even on failure
        let mut seen = Seen::default();
        let result = (|| {
            let (start, end) = match roots {
                Roots::Raw(_) => (0, 1),
                Roots::Results { start, end } => (start, end),
            };
            for index in start..end {
                self.h.budget.charge_work(1)?;
                let root = match roots {
                    Roots::Raw(id) => id,
                    Roots::Results { .. } => self.results[index],
                };
                frame(&mut self.scan, root, self.h.budget)?;
                while let Some(id) = self.scan.pop() {
                    self.h.budget.release_frames(1)?;
                    self.h.budget.charge_work(1)?;
                    self.h
                        .budget
                        .observe(crate::resource::Event::MachineSteps, 1);
                    if !seen.add(id, self.h.budget)? {
                        continue;
                    }
                    match self.h.levels.get(id, self.h.budget)?.kind() {
                        LevelKind::Max(a, c) => {
                            frame(&mut self.scan, c, self.h.budget)?;
                            frame(&mut self.scan, a, self.h.budget)?;
                        }
                        _ => push(&mut self.frontier, id, self.h.budget)?,
                    }
                }
            }
            Ok(())
        })();
        // One table for ALL roots of this collection; never reused in another
        // raw/nested/second-stage collection. Generated Max results are flattened
        // here, never sent back to N. Cost includes generated vertices as well.
        release_vec(seen.entries, self.h.budget)?;
        result
    }
    fn successors(&mut self, mut root: LevelId, count: u32) -> Result<LevelId, ResourceError> {
        // Every append precharges its fixed construction work and checks depth.
        for _ in 0..count {
            root = self
                .h
                .levels
                .append(LevelKind::Succ(root), self.h.names, self.h.budget)?;
        }
        Ok(root)
    }

    fn rebuild_frontier(
        &mut self,
        values: &mut [LevelId],
        outer: u32,
    ) -> Result<LevelId, ResourceError> {
        if values.is_empty() {
            return Err(ResourceError::Invariant);
        }
        self.sort(values)?;
        let mut kept = 0;
        for read in 0..values.len() {
            self.h.budget.charge_work(1)?;
            let (base, k) = self.h.offset(values[read])?;
            if kept != 0 {
                let (prior, pk) = self.h.offset(values[kept - 1])?;
                if self.h.structural(prior, base)? {
                    if k > pk {
                        values[kept - 1] = values[read];
                    }
                    continue;
                }
            }
            values[kept] = values[read];
            kept += 1;
        }
        // Sorting places the zero-base group first. Remove it only when
        // another retained group provides at least that lower bound.
        let (first, c) = self.h.offset(values[0])?;
        let mut start = 0;
        if first == LevelId::ZERO && kept > 1 {
            for id in values[1..kept].iter().copied() {
                self.h.budget.charge_work(1)?;
                if self.h.offset(id)?.1 >= c {
                    start = 1;
                    break;
                }
            }
        }
        let mut result = self.successors(values[kept - 1], outer)?;
        for id in values[start..kept - 1].iter().rev().copied() {
            self.h.budget.charge_work(1)?;
            let left = self.successors(id, outer)?;
            result = self.h.max(left, result)?;
        }
        Ok(result)
    }

    /// In-place heapsort makes each comparison fallible without panic adapters,
    /// hidden recursion, allocation, or an error being replaced with Ordering.
    fn sort(&mut self, values: &mut [LevelId]) -> Result<(), ResourceError> {
        for root in (0..values.len() / 2).rev() {
            self.sift(values, root, values.len())?;
        }
        for end in (1..values.len()).rev() {
            self.h.budget.charge_work(1)?;
            values.swap(0, end);
            self.sift(values, 0, end)?;
        }
        Ok(())
    }

    fn sift(
        &mut self,
        values: &mut [LevelId],
        mut root: usize,
        end: usize,
    ) -> Result<(), ResourceError> {
        // The frontier is a bounded Vec<u32>; root*2+1 fits usize on supported
        // targets. Still check arithmetic rather than wrapping an input index.
        loop {
            self.h.budget.charge_work(1)?;
            let left = root
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ResourceError::Counter)?;
            if left >= end {
                return Ok(());
            }
            let mut largest = left;
            if left + 1 < end && self.h.order(values[left], values[left + 1])? == Ordering::Less {
                largest = left + 1;
            }
            if self.h.order(values[root], values[largest])? != Ordering::Less {
                return Ok(());
            }
            values.swap(root, largest);
            root = largest;
        }
    }
}
