//! Each nonzero word points to an earlier producer in this State's committed
//! environment. Only finish(true) publishes. A hash collision, missing slot
//! match, or replacement cannot establish a theorem judgment.
use super::{Budget, Kind, MODERATE_ADMISSION, RequestKey, ResourceError, Safety};
use crate::check::environment::{Environment, StoredKind, view};

const WAYS: usize = 4;
const WORDS: usize = 1 << 16;

#[derive(Default)]
pub(super) struct CommittedSlots {
    poisoned: bool,
    words: Vec<u32>,
    pending: Option<(usize, u32)>,
}

impl CommittedSlots {
    pub(super) fn ready(&self) -> bool {
        !self.poisoned && self.pending.is_none()
    }

    fn start(key: RequestKey<'_>) -> usize {
        let mut hash = key.value ^ key.ty.wrapping_mul(0x9e37_79b9);
        hash ^= hash >> 16;
        hash = hash.wrapping_mul(0x85eb_ca6b);
        ((hash ^ (hash >> 13)) as usize & (WORDS / WAYS - 1)) * WAYS
    }

    pub(super) fn lookup(
        &mut self,
        key: Option<RequestKey<'_>>,
        environment: &Environment,
        budget: &mut Budget,
    ) -> Result<bool, ResourceError> {
        if self.poisoned || self.pending.is_some() {
            return Err(ResourceError::Invariant);
        }
        let Some(key) = key else { return Ok(false) };
        if self.words.is_empty() {
            return Ok(false);
        }
        budget.charge_work(Self::lookup_work(key)?)?;
        if let Some(found) = self.find(key, environment)? {
            self.refresh(found);
            return Ok(true);
        }
        Ok(false)
    }

    fn lookup_work(key: RequestKey<'_>) -> Result<u64, ResourceError> {
        // Bound all four full slice comparisons before inspecting the bucket.
        let names =
            u64::try_from(key.parameters.len().max(4)).map_err(|_| ResourceError::Counter)?;
        names
            .checked_add(1 + u64::from(key.kind == Kind::Definition))
            .and_then(|work| work.checked_mul(WAYS as u64))
            .and_then(|work| work.checked_add(1))
            .ok_or(ResourceError::Counter)
    }

    // A miss or unusable selector must leave the original scope-first route
    // its entire budget. Only an exact, already installed definition can pay
    // for the early lookup. No mutation can intervene between find and refresh.
    pub(super) fn completed_definition_scope(
        &mut self,
        key: RequestKey<'_>,
        environment: &Environment,
        budget: &mut Budget,
    ) -> Result<bool, ResourceError> {
        debug_assert!(self.ready() && key.kind == Kind::Definition);
        if key.parameters.len() > 4 {
            return Ok(false);
        }
        let charge = Self::lookup_work(key)?;
        if self.words.is_empty() || !budget.has_work_headroom(charge) {
            return Ok(false);
        }
        let Ok(Some(found)) = self.find(key, environment) else {
            return Ok(false);
        };
        budget.charge_work(charge)?;
        self.refresh(found);
        Ok(true)
    }

    fn refresh(&mut self, (start, way): (usize, usize)) {
        self.words[start..=start + way].rotate_right(1);
    }

    fn find(
        &self,
        key: RequestKey<'_>,
        environment: &Environment,
    ) -> Result<Option<(usize, usize)>, ResourceError> {
        let start = Self::start(key);
        let set = self
            .words
            .get(start..start + WAYS)
            .ok_or(ResourceError::Invariant)?;
        for (i, &word) in set.iter().enumerate() {
            if word == 0 {
                break;
            }
            let slot = ((word >> 1) as usize)
                .checked_sub(1)
                .ok_or(ResourceError::Invariant)?;
            if slot >= environment.len() {
                return Err(ResourceError::Invariant);
            }
            if word & 1 != u32::from(key.policy) {
                continue;
            }
            let entry = environment
                .entries
                .get(slot)
                .ok_or(ResourceError::Invariant)?;
            if !matches!(
                entry.kind,
                StoredKind::Ordinary(Kind::Theorem | Kind::Definition)
            ) || entry.safety != Safety::Safe
            {
                return Err(ResourceError::Invariant);
            }
            // Definition producers are ordinary safe singletons at preparation.
            // Re-read their committed group before using the saved typing premise.
            if entry.kind == StoredKind::Ordinary(key.kind)
                && entry.type_slot == key.ty
                && entry.value.is_some_and(|v| v.slot() == key.value)
                && view(&environment.names, entry.parameters)? == key.parameters
                && (key.kind != Kind::Definition
                    || view(&environment.names, entry.all)? == [entry.name])
            {
                return Ok(Some((start, i)));
            }
        }
        Ok(None)
    }

    pub(super) fn prepare(
        &mut self,
        key: Option<RequestKey<'_>>,
        work: u64,
        slot: usize,
        budget: &mut Budget,
    ) -> Result<(), ResourceError> {
        if self.poisoned || self.pending.is_some() {
            return Err(ResourceError::Invariant);
        }
        let Some(key) = key else { return Ok(()) };
        let Some(address) = u32::try_from(slot)
            .ok()
            .and_then(|n| n.checked_add(1))
            .and_then(|n| n.checked_mul(2))
        else {
            return Ok(());
        };
        if self.words.is_empty() {
            let activate = false;
            if !activate
                && (key.kind != Kind::Theorem
                    || key.parameters.len() > 4
                    || work < MODERATE_ADMISSION)
            {
                return Ok(());
            }
            budget.charge_work(WORDS as u64)?;
            budget.grow_vec(&mut self.words, WORDS)?;
            self.words.resize(WORDS, 0);
        }
        budget.charge_work(WAYS as u64)?;
        self.pending = Some((Self::start(key), address | u32::from(key.policy)));
        Ok(())
    }

    pub(super) fn finish(&mut self, installed: bool) {
        self.poisoned |= !installed && self.pending.is_some();
        if let Some((start, word)) = self.pending.take()
            && installed
        {
            let set = &mut self.words[start..start + WAYS];
            set.rotate_right(1);
            set[0] = word;
        }
    }

    pub(super) fn retire(&mut self, budget: &mut Budget) -> Result<(), ResourceError> {
        self.poisoned = false;
        self.pending = None;
        let words = std::mem::take(&mut self.words);
        let bytes = words.capacity() as u64 * 4;
        drop(words);
        if bytes > 0 {
            budget.release(bytes)?
        }
        Ok(())
    }
}
