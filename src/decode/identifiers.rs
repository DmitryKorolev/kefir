//! Exact serialization identities, independent of semantic names.
use crate::resource::{Budget, Event, ResourceError};
use std::hash::{Hash, Hasher};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum IndexError {
    Resource(ResourceError),
    InvalidId,
    Duplicate,
    SlotOrder,
}
impl From<ResourceError> for IndexError {
    fn from(error: ResourceError) -> Self {
        Self::Resource(error)
    }
}

struct Key<'a> {
    digits: &'a [u8],
    number: Option<u64>,
    hash: u64,
}
impl<'a> Key<'a> {
    fn parse(digits: &'a [u8]) -> Result<Self, IndexError> {
        if digits.is_empty() || (digits.len() > 1 && digits[0] == b'0') {
            return Err(IndexError::InvalidId);
        }
        if digits.len() <= 19 {
            let mut number = 0u64;
            for &byte in digits {
                let digit = byte.wrapping_sub(b'0');
                if digit > 9 {
                    return Err(IndexError::InvalidId);
                }
                // At most 19 validated decimal digits: every prefix is below
                // 10^19, which fits u64. Wrapping operations cannot wrap here.
                number = number.wrapping_mul(10).wrapping_add(u64::from(digit));
            }
            return Ok(Self {
                digits,
                number: Some(number),
                hash: 0,
            });
        }
        if !digits.iter().all(u8::is_ascii_digit) {
            return Err(IndexError::InvalidId);
        }
        let number = digits.iter().try_fold(0u64, |n, b| {
            n.checked_mul(10)?.checked_add(u64::from(b - b'0'))
        });
        Ok(Self {
            digits,
            number,
            hash: 0,
        })
    }
    fn hashed(mut self) -> Self {
        let mut hasher = crate::syntax::hash::FastHasher::new();
        self.digits.hash(&mut hasher);
        self.hash = hasher.finish() | 1;
        self
    }
}

#[derive(Clone, Copy, Default)]
struct Entry {
    hash: u64,
    key: u64,
    slot: u32,
    len: u32,
}
const _: () = assert!(std::mem::size_of::<Entry>() == 24);

/// Whole-input owner: these flat allocations stay live until the semantic
/// snapshot is frozen and the input budget is retired. Drop does not release
/// charges; reusing that budget after dropping an index requires explicit release.
pub(crate) struct IdIndex {
    prefix: u64,
    next_slot: u64,
    frozen: bool,
    entries: Vec<Entry>,
    digits: Vec<u8>,
    sparse_len: usize,
}

impl IdIndex {
    pub(crate) fn new(intrinsic_zero: bool) -> Self {
        let prefix = u64::from(intrinsic_zero);
        Self {
            prefix,
            next_slot: prefix,
            frozen: false,
            entries: Vec::new(),
            digits: Vec::new(),
            sparse_len: 0,
        }
    }

    /// Caller precharges token validation/parsing/hashing through 's
    /// fixed input chunks. Each token permits one resolve and one insert; callers
    /// outside that scan must precharge digits.len()+1 for each call. Probe work
    /// is charged here separately. Dense resolution needs no additional charge.
    /// Invariant: prefix IDs have same-numbered slots. Exceptions are disjoint,
    /// unique, immutable, and the table always has an empty slot. No deletions.
    pub(crate) fn resolve(
        &self,
        digits: &[u8],
        budget: &mut Budget,
    ) -> Result<Option<u32>, IndexError> {
        // Count this lookup request once, including malformed tokens, misses
        // and exhausted probe work. Internal buckets and inserts are excluded.
        budget.observe(Event::TableLookups, 1);
        let key = Key::parse(digits)?;
        if let Some(number) = key.number.filter(|number| *number < self.prefix) {
            return Ok(Some(
                u32::try_from(number).map_err(|_| IndexError::SlotOrder)?,
            ));
        }
        if self.entries.is_empty() {
            return Ok(None);
        }
        let position = self.position(&key.hashed(), budget)?;
        Ok((self.entries[position].hash != 0).then_some(self.entries[position].slot))
    }

    /// Caller has already validated that digits is the canonical decimal
    /// spelling of number. This transient input fact grants no checkedness.
    /// The immutable prefix maps each contained external ID to the same slot;
    /// an empty exception table proves all other IDs absent. Allocated tables,
    /// including an empty table left by failed growth, retain exact probe charges.
    /// Observation and work charges are identical to resolving the same token.
    #[inline]
    pub(crate) fn resolve_canonical_u32(
        &self,
        digits: &[u8],
        number: u32,
        budget: &mut Budget,
    ) -> Result<Option<u32>, IndexError> {
        if u64::from(number) < self.prefix || self.entries.is_empty() {
            budget.observe(Event::TableLookups, 1);
            Ok((u64::from(number) < self.prefix).then_some(number))
        } else {
            self.resolve(digits, budget)
        }
    }

    /// Same canonical-token premise as resolve_canonical_u32. The dense branch
    /// is exactly insert's successful prefix admission, after syntax publication.
    /// Every other case retains insert's original validation/failure ordering.
    #[inline]
    pub(crate) fn insert_canonical_u32(
        &mut self,
        digits: &[u8],
        number: u32,
        slot: u32,
        budget: &mut Budget,
    ) -> Result<(), IndexError> {
        if !self.frozen && u64::from(number) == self.prefix && u64::from(slot) == self.next_slot {
            self.prefix += 1;
            self.next_slot += 1;
            Ok(())
        } else {
            self.insert(digits, slot, budget)
        }
    }

    /// The same token-work precondition as resolve applies.
    /// Caller must validate all outgoing references and finish constructing the
    /// corresponding immutable syntax slot before publishing this mapping.
    pub(crate) fn insert(
        &mut self,
        digits: &[u8],
        slot: u32,
        budget: &mut Budget,
    ) -> Result<(), IndexError> {
        if u64::from(slot) != self.next_slot {
            return Err(IndexError::SlotOrder);
        }
        let key = Key::parse(digits)?;
        if key.number.is_some_and(|number| number < self.prefix) {
            return Err(IndexError::Duplicate);
        }
        if !self.frozen && key.number == Some(self.prefix) {
            self.prefix += 1;
            self.next_slot += 1;
            return Ok(());
        }
        let key = key.hashed();
        if !self.entries.is_empty() && self.entries[self.position(&key, budget)?].hash != 0 {
            return Err(IndexError::Duplicate);
        }
        if self.sparse_len + 1 > self.entries.len() / 4 * 3 {
            self.grow(budget)?;
        }
        let position = self.position(&key, budget)?;
        let (stored_key, len) = if let Some(number) = key.number {
            (number, 0)
        } else {
            let len = crate::resource::traced!("identifiers.slot_limit", key.digits.len(), {
                u32::try_from(key.digits.len()).map_err(|_| ResourceError::Storage)
            })?;
            let end = self
                .digits
                .len()
                .checked_add(key.digits.len())
                .ok_or(ResourceError::Counter)?;
            budget.charge_work(u64::from(len) + 1)?;
            budget.grow_vec(&mut self.digits, end)?;
            let offset = u64::try_from(self.digits.len()).map_err(|_| ResourceError::Counter)?;
            self.digits.extend_from_slice(key.digits);
            (offset, len)
        };
        // No fallible operation follows publication, including prefix freezing.
        self.entries[position] = Entry {
            hash: key.hash,
            key: stored_key,
            slot,
            len,
        };
        self.sparse_len += 1;
        self.next_slot += 1;
        self.frozen = true;
        Ok(())
    }

    fn position(&self, key: &Key<'_>, budget: &mut Budget) -> Result<usize, ResourceError> {
        let charge = u64::try_from(key.digits.len())
            .map_err(|_| ResourceError::Counter)?
            .checked_add(1)
            .and_then(|length| length.checked_mul(64))
            .ok_or(ResourceError::Counter)?;
        let mask = self.entries.len() - 1;
        let mut position = key.hash as usize & mask;
        for group in 0..self.entries.len().div_ceil(64) {
            budget.charge_work(charge)?;
            for _ in 0..64.min(self.entries.len() - group * 64) {
                let entry = self.entries[position];
                if entry.hash == 0 || (entry.hash == key.hash && self.equal(entry, key)) {
                    return Ok(position);
                }
                position = (position + 1) & mask;
            }
        }
        // Occupancy <= 75% guarantees an empty slot. Failure is an internal
        // invariant violation, never an absent reference or duplicate verdict.
        Err(ResourceError::Invariant)
    }

    fn equal(&self, entry: Entry, key: &Key<'_>) -> bool {
        if entry.len == 0 {
            key.number == Some(entry.key)
        } else {
            // By construction, every span was checked before copying and no
            // stored digit is subsequently removed or overwritten.
            let start = entry.key as usize;
            &self.digits[start..start + entry.len as usize] == key.digits
        }
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
            budget.charge_work(
                u64::try_from(capacity)
                    .map_err(|_| ResourceError::Counter)?
                    .checked_mul(24)
                    .ok_or(ResourceError::Counter)?,
            )?;
            replacement.resize(capacity, Entry::default());
            let mask = capacity - 1;
            for entry in self.entries.iter().copied().filter(|entry| entry.hash != 0) {
                let mut position = entry.hash as usize & mask;
                let mut inserted = false;
                for group in 0..capacity.div_ceil(64) {
                    budget.charge_work(64)?;
                    for _ in 0..64.min(capacity - group * 64) {
                        if replacement[position].hash == 0 {
                            replacement[position] = entry;
                            inserted = true;
                            break;
                        }
                        position = (position + 1) & mask;
                    }
                    if inserted {
                        break;
                    }
                }
                if !inserted {
                    return Err(ResourceError::Invariant);
                }
            }
            Ok(())
        })();
        if let Err(error) = result {
            let bytes = replacement.capacity() as u64 * 24;
            drop(replacement);
            budget.release(bytes)?;
            return Err(error);
        }
        let old = std::mem::replace(&mut self.entries, replacement);
        let bytes = old.capacity() as u64 * 24;
        drop(old);
        budget.release(bytes)
    }
}
