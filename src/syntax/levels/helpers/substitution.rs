//! Simultaneous substitution on a caller-validated frozen template.
//! Completed-source memo shares generated composites only within this operation;
//! generated results are forbidden as later sources. No U/N judgment is computed.
use super::*;
use crate::syntax::levels::NameId;

pub(crate) mod scope;

#[derive(Clone, Copy, Default)]
pub(super) struct Entry {
    a: u32,
    pub(super) value: u32,
    hash: u32,
}
const _: () = assert!(size_of::<Entry>() == 12);
/// Exact u32-key map. Separate instances hold canonical-name replacements and
/// completed original-source results. Both die with the fixed substitution.
/// The scope boundary also uses separate instances for declared canonical names
/// and discovered source handles; those die with that fixed-scope call.
/// U uses another instance for completed N(source) results across its two roots,
/// frozen to the original level prefix and immutable names; it dies with that U.
#[derive(Default)]
pub(super) struct Map {
    pub(super) entries: Vec<Entry>,
    used: usize,
}
impl Map {
    #[inline(always)]
    fn hash(a: u32) -> u32 {
        // Fixed-size hashing, not the structural summary hash: its low bits
        // must distribute sequential handles across power-of-two slot arrays.
        let mut hash = crate::syntax::hash::FastHasher::new();
        hash.write_u32(a);
        let hash = hash.finish() as u32;
        if hash == 0 { 1 } else { hash }
    }

    #[inline(always)]
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
            if e.hash == 0 || (e.hash == key.hash && e.a == key.a) {
                return Ok(slot);
            }
            slot = (slot + 1) & mask;
        }
        Err(ResourceError::Invariant)
    }

    #[inline(always)]
    pub(super) fn get(&self, a: u32, budget: &mut Budget) -> Result<Option<Entry>, ResourceError> {
        if self.entries.is_empty() {
            return Ok(None);
        }
        let key = Entry {
            a,
            hash: Self::hash(a),
            value: 0,
        };
        let e = self.entries[Self::position(&self.entries, key, budget)?];
        Ok((e.hash != 0).then_some(e))
    }

    #[inline(always)]
    pub(super) fn insert(
        &mut self,
        a: u32,
        value: u32,
        budget: &mut Budget,
    ) -> Result<(), ResourceError> {
        let key = Entry {
            a,
            value,
            hash: Self::hash(a),
        };
        if self.used + 1 > self.entries.len() / 4 * 3 {
            self.grow(budget)?;
        }
        let slot = Self::position(&self.entries, key, budget)?;
        if self.entries[slot].hash == 0 {
            self.used += 1;
        } else if self.entries[slot].value != value {
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

#[derive(Clone, Copy)]
struct Frame {
    source: LevelId,
    first: LevelId,
    second: bool,
}
const _: () = assert!(size_of::<Frame>() == 12);
pub(crate) struct Substitution<'h, 'a, N, const CACHED: bool = true> {
    h: &'h mut Helpers<'a, N>,
    source_end: usize,
    parameters: Map,
    completed: Map,
    frames: Vec<Frame>,
}
impl Levels {
    /// Caller obligations: parameters are unique by exact name and their ordered
    /// replacements are scope-valid; every source belongs to the original
    /// template frontier covered identity argument. source_end is
    /// frozen before generated syntax and does not certify those semantic facts.
    /// Mismatches below are internal API violations, never proof rejections.
    /// No panic may be caught inside the callback; unwind discards the whole run.
    pub(crate) fn with_substitution<N: LevelNames, T>(
        &mut self,
        names: &N,
        source_end: usize,
        parameters: &[NameId],
        replacements: &[LevelId],
        b: &mut Budget,
        body: impl FnOnce(&mut Substitution<'_, '_, N>) -> Result<T, ResourceError>,
    ) -> Result<T, ResourceError> {
        self.with_substitution_mode::<N, T, true>(
            names,
            source_end,
            parameters,
            replacements,
            b,
            body,
        )
    }
    fn with_substitution_mode<N: LevelNames, T, const CACHED: bool>(
        &mut self,
        names: &N,
        source_end: usize,
        parameters: &[NameId],
        replacements: &[LevelId],
        b: &mut Budget,
        body: impl FnOnce(&mut Substitution<'_, '_, N, CACHED>) -> Result<T, ResourceError>,
    ) -> Result<T, ResourceError> {
        self.with_helpers(names, b, |h| {
            h.budget.charge_work(3)?;
            let mut s = Substitution {
                h,
                source_end,
                parameters: Map::default(),
                completed: Map::default(),
                frames: Vec::new(),
            };
            let result = (|| {
                if source_end > s.h.levels.len() || parameters.len() != replacements.len() {
                    return Err(ResourceError::Invariant);
                }
                for (&name, &level) in parameters.iter().zip(replacements) {
                    s.h.budget.charge_work(1)?;
                    let key = s.h.names.summary(name, s.h.budget)?.canonical;
                    s.h.levels.get(level, s.h.budget)?;
                    if s.parameters.get(key, s.h.budget)?.is_some() {
                        return Err(ResourceError::Invariant);
                    }
                    s.parameters.insert(key, level.0, s.h.budget)?;
                }
                body(&mut s)
            })();
            let count = s.frames.len();
            release_vec(take(&mut s.frames), s.h.budget)?;
            s.h.budget.release_frames(count)?;
            release_vec(take(&mut s.parameters.entries), s.h.budget)?;
            release_vec(take(&mut s.completed.entries), s.h.budget)?;
            result
        })
    }
}
impl<N: LevelNames, const CACHED: bool> Substitution<'_, '_, N, CACHED> {
    fn cached(&self) -> bool {
        CACHED
    }
    fn push(&mut self, frame: Frame) -> Result<(), ResourceError> {
        self.h.budget.reserve_frames(1)?;
        let required = self.frames.len() + 1;
        if let Err(error) = self.h.budget.grow_vec(&mut self.frames, required) {
            self.h.budget.release_frames(1)?;
            return Err(error);
        }
        self.frames.push(frame);
        Ok(())
    }
    fn remember(&mut self, source: LevelId, result: LevelId) -> Result<LevelId, ResourceError> {
        if self.cached() {
            self.completed.insert(source.0, result.0, self.h.budget)?;
        }
        Ok(result)
    }
    pub(crate) fn apply(&mut self, root: LevelId) -> Result<LevelId, ResourceError> {
        if let Some(error) = self.h.failure {
            return Err(error);
        }
        let result = self.apply_inner(root);
        if let Err(error) = result {
            self.h.failure = Some(error);
        }
        result
    }
    fn apply_inner(&mut self, root: LevelId) -> Result<LevelId, ResourceError> {
        let mut current = root;
        'descend: loop {
            self.h.budget.charge_work(1)?;
            self.h
                .budget
                .observe(crate::resource::Event::MachineSteps, 1);
            if current.0 as usize >= self.source_end {
                return Err(ResourceError::Invariant);
            }
            let node = self.h.levels.get(current, self.h.budget)?;
            let mut result = if !node.has_param() {
                current
            } else if let Some(entry) = if self.cached() {
                self.completed.get(current.0, self.h.budget)?
            } else {
                None
            } {
                LevelId(entry.value)
            } else {
                match node.kind {
                    LevelKind::Param(name) => {
                        let key = self.h.names.summary(name, self.h.budget)?.canonical;
                        let result = self
                            .parameters
                            .get(key, self.h.budget)?
                            .ok_or(ResourceError::Invariant)?;
                        self.remember(current, LevelId(result.value))?
                    }
                    LevelKind::Succ(first)
                    | LevelKind::Max(first, _)
                    | LevelKind::IMax(first, _) => {
                        self.push(Frame {
                            source: current,
                            first: LevelId::ZERO,
                            second: false,
                        })?;
                        current = first;
                        continue;
                    }
                    LevelKind::Zero => return Err(ResourceError::Invariant),
                }
            };
            while let Some(frame) = self.frames.pop() {
                self.h.budget.release_frames(1)?;
                self.h.budget.charge_work(1)?;
                self.h
                    .budget
                    .observe(crate::resource::Event::MachineSteps, 1);
                result = match self.h.levels.get(frame.source, self.h.budget)?.kind {
                    LevelKind::Succ(original) => {
                        let result = if original == result {
                            frame.source
                        } else {
                            self.h.levels.append(
                                LevelKind::Succ(result),
                                self.h.names,
                                self.h.budget,
                            )?
                        };
                        self.remember(frame.source, result)?
                    }
                    kind @ (LevelKind::Max(a, second) | LevelKind::IMax(a, second)) => {
                        if !frame.second {
                            self.push(Frame {
                                source: frame.source,
                                first: result,
                                second: true,
                            })?;
                            current = second;
                            continue 'descend;
                        }
                        let result = if frame.first == a && result == second {
                            frame.source
                        } else if matches!(kind, LevelKind::Max(..)) {
                            self.h.max(frame.first, result)?
                        } else {
                            self.h.imax(frame.first, result)?
                        };
                        self.remember(frame.source, result)?
                    }
                    _ => return Err(ResourceError::Invariant),
                };
            }
            return Ok(result);
        }
    }
}

pub(crate) mod expressions;
