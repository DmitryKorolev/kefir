//! Constructor helpers, with exact operation-local structural memos.
//! No entry is an algorithmic universe or conversion judgment. All referenced
//! nodes/names are immutable, and all memo storage is released at operation end.
use super::{LevelId, LevelKind, LevelNames, LevelPositive, Levels};
use crate::resource::{Budget, ResourceError};
use std::hash::Hasher;
use std::mem::{size_of, take};

mod memo;
#[allow(
    dead_code,
    reason = "Validated universe component awaits semantic conversion integration"
)]
mod order;
pub(crate) mod substitution;
pub(crate) use memo::{SharedMemo, SharedTable};
#[allow(
    dead_code,
    reason = "Validated universe component awaits semantic conversion integration"
)]
mod universe;
pub(crate) use universe::UniverseComparison;

#[derive(Clone, Copy, Default)]
struct Entry {
    a: u32,
    b: u32,
    value: u32,
    hash: u32,
}

const _: () = assert!(size_of::<Entry>() == 16);

/// PAIR: (a,b) -> Boolean in value. Otherwise: a -> (base=b,offset=value).
/// Occupancy <= 3/4, hash zero is vacant, full keys decide every hit. Insertion
/// happens only after the represented operation completed. No deletions/reuse
/// across operations, binders, contexts, declarations, table origins or threads.
#[derive(Default)]
struct Memo<const PAIR: bool> {
    entries: Vec<Entry>,
    used: usize,
}

impl<const PAIR: bool> Memo<PAIR> {
    fn hash(a: u32, b: u32) -> u32 {
        // Fixed-size hashing, not the structural summary hash: its low bits
        // must distribute sequential handles across power-of-two slot arrays.
        let mut hash = crate::syntax::hash::FastHasher::new();
        hash.write_u32(a);
        if PAIR {
            hash.write_u32(b);
        }
        let hash = hash.finish() as u32;
        if hash == 0 { 1 } else { hash }
    }

    fn position(
        entries: &[Entry],
        key: Entry,
        budget: &mut Budget,
    ) -> Result<usize, ResourceError> {
        let mask = entries
            .len()
            .checked_sub(1)
            .ok_or(ResourceError::Invariant)?;
        let mut slot = key.hash as usize & mask;
        for _ in 0..entries.len() {
            budget.charge_work(1)?;
            let e = entries[slot];
            if e.hash == 0 || (e.hash == key.hash && e.a == key.a && (!PAIR || e.b == key.b)) {
                return Ok(slot);
            }
            slot = (slot + 1) & mask;
        }
        Err(ResourceError::Invariant)
    }

    fn get(&self, a: u32, b: u32, budget: &mut Budget) -> Result<Option<Entry>, ResourceError> {
        if self.entries.is_empty() {
            return Ok(None);
        }
        let key = Entry {
            a,
            b,
            hash: Self::hash(a, b),
            value: 0,
        };
        let e = self.entries[Self::position(&self.entries, key, budget)?];
        Ok((e.hash != 0).then_some(e))
    }

    fn insert(
        &mut self,
        a: u32,
        b: u32,
        value: u32,
        budget: &mut Budget,
    ) -> Result<(), ResourceError> {
        let key = Entry {
            a,
            b,
            value,
            hash: Self::hash(a, b),
        };
        if self.used + 1 > self.entries.len() / 4 * 3 {
            self.grow(budget)?;
        }
        let slot = Self::position(&self.entries, key, budget)?;
        if self.entries[slot].hash == 0 {
            self.used += 1;
        } else if self.entries[slot].b != b || self.entries[slot].value != value {
            // A completed immutable query cannot acquire another result.
            return Err(ResourceError::Invariant);
        }
        self.entries[slot] = key;
        Ok(())
    }

    fn grow(&mut self, budget: &mut Budget) -> Result<(), ResourceError> {
        let capacity = self
            .entries
            .len()
            .checked_mul(2)
            .ok_or(ResourceError::Counter)?
            .max(16);
        let mut replacement = Vec::new();
        budget.grow_vec(&mut replacement, capacity)?;
        let result = (|| {
            budget.charge_work(capacity as u64 + 1)?;
            replacement.resize(capacity, Entry::default());
            // The new array is twice the old size; the preceding span charge
            // also covers this fixed-width scan, including vacant old entries.
            for e in self.entries.iter().copied().filter(|e| e.hash != 0) {
                let slot = Self::position(&replacement, e, budget)?;
                replacement[slot] = e;
            }
            Ok(())
        })();
        if let Err(error) = result {
            release_vec(replacement, budget)?;
            return Err(error);
        }
        let old = std::mem::replace(&mut self.entries, replacement);
        release_vec(old, budget)
    }
}

/// Flat Copy payloads have no child-following destruction. A caller precharges
/// its bounded number of allocation releases; cleanup still runs on failure.
fn release_vec<T: Copy>(values: Vec<T>, budget: &mut Budget) -> Result<(), ResourceError> {
    let bytes = values
        .capacity()
        .checked_mul(size_of::<T>())
        .ok_or(ResourceError::Counter)?;
    drop(values);
    budget.release(bytes as u64)
}

#[derive(Clone, Copy)]
enum Frame {
    Compare(LevelId, LevelId),
    Finish(LevelId, LevelId),
    Offset(LevelId),
}
const _: () = assert!(size_of::<Frame>() <= 16);

pub(crate) struct Helpers<'a, N> {
    levels: &'a mut Levels,
    names: &'a N,
    budget: &'a mut Budget,
    equal: Memo<true>,
    offsets: Memo<false>,
    frames: Vec<Frame>,
    failure: Option<ResourceError>,
}

impl Levels {
    /// One immutable-name/table operation, with no judgment or memo escaping.
    /// Generated raw nodes remain owned by the level store, under its declaration
    /// watermark obligation. A failed callback cannot yield a successful result.
    /// Panic invariant: no caller catches unwinding inside this operation. The
    /// top-level panic boundary must discard the whole run/table/ledger, since
    /// unwinding drops flat allocations but bypasses explicit ledger cleanup.
    pub(crate) fn with_helpers<N: LevelNames, T>(
        &mut self,
        names: &N,
        budget: &mut Budget,
        body: impl FnOnce(&mut Helpers<'_, N>) -> Result<T, ResourceError>,
    ) -> Result<T, ResourceError> {
        // Three flat scratch allocations can be released even if later fuel is
        // exhausted. This constant charge covers normal and error cleanup.
        budget.charge_work(3)?;
        let mut h = Helpers {
            levels: self,
            names,
            budget,
            equal: Memo::default(),
            offsets: Memo::default(),
            frames: Vec::new(),
            failure: None,
        };
        let result = body(&mut h);
        let remaining = h.frames.len();
        // Retain operation, callback and every cleanup cause until selection.
        // A failed route is sticky, but cannot downgrade a later internal error.
        // All flat stores retire even if another release finds a ledger defect.
        let errors = [
            h.failure,
            result.as_ref().err().copied(),
            release_vec(take(&mut h.frames), h.budget).err(),
            h.budget.release_frames(remaining).err(),
            release_vec(take(&mut h.equal.entries), h.budget).err(),
            release_vec(take(&mut h.offsets.entries), h.budget).err(),
        ];
        let selected = errors
            .into_iter()
            .flatten()
            .find(|error| {
                error.failure_report().outcome
                    == crate::resource::failure::FailureOutcome::InternalError
            })
            .or_else(|| errors.into_iter().flatten().next());
        match selected {
            Some(error) => Err(error),
            None => result,
        }
    }
}

impl<N: LevelNames> Helpers<'_, N> {
    /// Failure is sticky for this operation, including when a caller mistakenly
    /// ignores a helper error. Partial routes/memos cannot be used as a fallback.
    fn attempt<T>(
        &mut self,
        body: impl FnOnce(&mut Self) -> Result<T, ResourceError>,
    ) -> Result<T, ResourceError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        let result = body(self);
        if let Err(error) = result {
            self.failure = Some(error);
        }
        result
    }

    pub(crate) fn structural(&mut self, a: LevelId, b: LevelId) -> Result<bool, ResourceError> {
        self.attempt(|h| h.structural_inner(a, b))
    }

    pub(crate) fn offset(&mut self, root: LevelId) -> Result<(LevelId, u32), ResourceError> {
        self.attempt(|h| h.offset_inner(root))
    }

    pub(crate) fn max(&mut self, a: LevelId, b: LevelId) -> Result<LevelId, ResourceError> {
        self.attempt(|h| h.max_inner(a, b))
    }

    pub(crate) fn imax(&mut self, a: LevelId, b: LevelId) -> Result<LevelId, ResourceError> {
        self.attempt(|h| h.imax_inner(a, b))
    }
    fn push(&mut self, f: Frame) -> Result<(), ResourceError> {
        let len = self
            .frames
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        self.budget.reserve_frames(1)?;
        if let Err(error) = self.budget.grow_vec(&mut self.frames, len) {
            self.budget.release_frames(1)?;
            return Err(error);
        }
        self.frames.push(f);
        Ok(())
    }

    fn pop(&mut self) -> Result<Option<Frame>, ResourceError> {
        let result = self.frames.pop();
        if result.is_some() {
            self.budget.release_frames(1)?;
        }
        Ok(result)
    }

    fn known_equal(&mut self, a: LevelId, b: LevelId) -> Result<Option<bool>, ResourceError> {
        let (x, y) = (
            self.levels.get(a, self.budget)?,
            self.levels.get(b, self.budget)?,
        );
        if a == b {
            return Ok(Some(true));
        }
        if x.hash != y.hash {
            return Ok(Some(false));
        }
        self.equal
            .get(a.0, b.0, self.budget)?
            .map(|e| match e.value {
                0 => Ok(false),
                1 => Ok(true),
                _ => Err(ResourceError::Invariant),
            })
            .transpose()
    }

    /// Exact ordered syntax equality only. Hashes can rule out equal syntax,
    /// never establish it. Memos hold completed Booleans; no failed route is false.
    fn structural_inner(&mut self, a: LevelId, b: LevelId) -> Result<bool, ResourceError> {
        self.budget.charge_work(1)?;
        if let Some(result) = self.known_equal(a, b)? {
            return Ok(result);
        }
        if !self.frames.is_empty() {
            return Err(ResourceError::Invariant);
        }
        self.push(Frame::Compare(a, b))?;
        while let Some(frame) = self.pop()? {
            self.budget.charge_work(1)?;
            self.budget.observe(crate::resource::Event::MachineSteps, 1);
            match frame {
                Frame::Compare(a, b) => {
                    if self.known_equal(a, b)?.is_some() {
                        continue;
                    }
                    let (x, y) = (
                        self.levels.get(a, self.budget)?.kind,
                        self.levels.get(b, self.budget)?.kind,
                    );
                    let result = match (x, y) {
                        (LevelKind::Zero, LevelKind::Zero) => Some(true),
                        (LevelKind::Param(x), LevelKind::Param(y)) => Some(
                            self.names.summary(x, self.budget)?.canonical
                                == self.names.summary(y, self.budget)?.canonical,
                        ),
                        (LevelKind::Succ(x), LevelKind::Succ(y)) => {
                            self.push(Frame::Finish(a, b))?;
                            self.push(Frame::Compare(x, y))?;
                            None
                        }
                        (LevelKind::Max(x1, x2), LevelKind::Max(y1, y2))
                        | (LevelKind::IMax(x1, x2), LevelKind::IMax(y1, y2)) => {
                            self.push(Frame::Finish(a, b))?;
                            self.push(Frame::Compare(x2, y2))?;
                            self.push(Frame::Compare(x1, y1))?;
                            None
                        }
                        _ => Some(false),
                    };
                    if let Some(result) = result {
                        self.equal
                            .insert(a.0, b.0, u32::from(result), self.budget)?;
                    }
                }
                Frame::Finish(a, b) => {
                    let (x, y) = (
                        self.levels.get(a, self.budget)?.kind,
                        self.levels.get(b, self.budget)?.kind,
                    );
                    let result = match (x, y) {
                        (LevelKind::Succ(x), LevelKind::Succ(y)) => {
                            self.known_equal(x, y)?.ok_or(ResourceError::Invariant)?
                        }
                        (LevelKind::Max(x1, x2), LevelKind::Max(y1, y2))
                        | (LevelKind::IMax(x1, x2), LevelKind::IMax(y1, y2)) => {
                            self.known_equal(x1, y1)?.ok_or(ResourceError::Invariant)?
                                && self.known_equal(x2, y2)?.ok_or(ResourceError::Invariant)?
                        }
                        _ => return Err(ResourceError::Invariant),
                    };
                    self.equal
                        .insert(a.0, b.0, u32::from(result), self.budget)?;
                }
                Frame::Offset(_) => return Err(ResourceError::Invariant),
            }
        }
        self.known_equal(a, b)?.ok_or(ResourceError::Invariant)
    }

    /// Exact existing nonsuccessor base plus checked natural successor offset.
    fn offset_inner(&mut self, root: LevelId) -> Result<(LevelId, u32), ResourceError> {
        if !self.frames.is_empty() {
            return Err(ResourceError::Invariant);
        }
        let mut current = root;
        let (base, mut count) = loop {
            self.budget.charge_work(1)?;
            self.budget.observe(crate::resource::Event::MachineSteps, 1);
            let node = self.levels.get(current, self.budget)?;
            if let Some(e) = self.offsets.get(current.0, 0, self.budget)? {
                break (LevelId(e.b), e.value);
            }
            match node.kind {
                LevelKind::Succ(child) => {
                    self.push(Frame::Offset(current))?;
                    current = child;
                }
                _ => {
                    self.offsets.insert(current.0, current.0, 0, self.budget)?;
                    break (current, 0);
                }
            }
        };
        while let Some(frame) = self.pop()? {
            self.budget.charge_work(1)?;
            self.budget.observe(crate::resource::Event::MachineSteps, 1);
            let Frame::Offset(id) = frame else {
                return Err(ResourceError::Invariant);
            };
            count = count.checked_add(1).ok_or(ResourceError::Counter)?;
            self.offsets.insert(id.0, base.0, count, self.budget)?;
        }
        Ok((base, count))
    }

    /// Cheap M: applies the first applicable equation, without N.
    fn max_inner(&mut self, a: LevelId, b: LevelId) -> Result<LevelId, ResourceError> {
        self.budget.charge_work(1)?;
        let (abase, ak) = self.offset(a)?;
        let (bbase, bk) = self.offset(b)?;
        if abase == LevelId::ZERO && bbase == LevelId::ZERO {
            return Ok(if ak >= bk { a } else { b });
        }
        if self.structural(a, b)? {
            return Ok(a);
        }
        if a == LevelId::ZERO {
            return Ok(b);
        }
        if b == LevelId::ZERO {
            return Ok(a);
        }
        if let LevelKind::Max(x, y) = self.levels.get(b, self.budget)?.kind
            && (self.structural(a, x)? || self.structural(a, y)?)
        {
            return Ok(b);
        }
        if let LevelKind::Max(x, y) = self.levels.get(a, self.budget)?.kind
            && (self.structural(b, x)? || self.structural(b, y)?)
        {
            return Ok(a);
        }
        if self.structural(abase, bbase)? {
            return Ok(if ak >= bk { a } else { b });
        }
        self.levels
            .append(LevelKind::Max(a, b), self.names, self.budget)
    }

    /// Cheap I. Its structural-zero/one tests intentionally do not use the
    /// identically-zero summary; replacing them changes operational construction.
    fn imax_inner(&mut self, a: LevelId, b: LevelId) -> Result<LevelId, ResourceError> {
        self.budget.charge_work(1)?;
        let (x, y) = (
            self.levels.get(a, self.budget)?,
            self.levels.get(b, self.budget)?,
        );
        // One-sided probe: NotProven proves no converse and
        // only falls through to the structural imax construction below.
        if y.positive() == LevelPositive::Proven {
            return self.max(a, b);
        }
        if b == LevelId::ZERO {
            return Ok(b);
        }
        if a == LevelId::ZERO || x.kind == LevelKind::Succ(LevelId::ZERO) {
            return Ok(b);
        }
        if self.structural(a, b)? {
            return Ok(a);
        }
        self.levels
            .append(LevelKind::IMax(a, b), self.names, self.budget)
    }
}
