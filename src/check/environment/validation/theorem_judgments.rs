//! Bounded completed original theorem judgments in one State/Decoder.
//! Stores only T : Prop and p : T. It grants no declaration installation, name,
//! policy, metadata or whole-input verdict. Original syntax and committed names
//! cannot be recycled/rebound in this owner; extension preserves these judgments.
use crate::decode::primitive_decode::declarations::{Kind, Request, Safety};
use crate::resource::{Budget, ResourceError};
use std::mem::{size_of, take};

const SLOTS: usize = 4096;
const WAYS: usize = 4;
const BUCKETS: usize = SLOTS / WAYS;
const ADMISSION: u64 = 1 << 20;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Key {
    ty: u32,
    value: u32,
    parameters: [u32; 4],
    count: u8,
    policy: u8,
}
const _: () = assert!(size_of::<Key>() == 28);
const _: () = assert!(size_of::<Option<Key>>() == 32);
impl Key {
    fn bucket(self) -> usize {
        let mut h = 0x243f_6a88u64;
        for x in [
            self.ty,
            self.value,
            u32::from(self.count),
            u32::from(self.policy),
        ]
        .into_iter()
        .chain(self.parameters[..usize::from(self.count)].iter().copied())
        {
            h = (h ^ u64::from(x))
                .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                .rotate_left(29);
        }
        h as usize & (BUCKETS - 1)
    }
}

#[derive(Default)]
pub(super) struct Judgments {
    slots: Vec<Option<Key>>,
    cursors: Vec<u8>,
    pending: Option<Key>,
}
// Constant run owner only: two vectors and an invisible pending key.
const _: () = assert!(size_of::<Judgments>() == 80);
// The admission threshold override and hit count exist only in test binaries.
impl Judgments {
    pub(super) fn new() -> Self {
        Self { ..Self::default() }
    }
    // The State/Decoder pair owns these original source IDs for one run.
    // No generated source, ValueId, local context or shortened hash is stored.
    pub(super) fn key(&self, request: &Request<'_>, policy: crate::AxiomPolicy) -> Option<Key> {
        if request.kind != Kind::Theorem
            || request.safety != Safety::Safe
            || request.parameters.len() > 4
        {
            return None;
        }
        let mut parameters = [0; 4];
        for (out, parameter) in parameters.iter_mut().zip(request.parameters) {
            *out = parameter.0;
        }
        Some(Key {
            ty: request.ty.slot(),
            value: request.value?.slot(),
            parameters,
            count: request.parameters.len() as u8,
            policy: match policy {
                crate::AxiomPolicy::ExcludeNativeMarked => 0,
                crate::AxiomPolicy::AllowAllDeclaredAxioms => 1,
            },
        })
    }
    fn contains(&self, key: Key) -> bool {
        if self.slots.is_empty() {
            return false;
        }
        let base = key.bucket() * WAYS;
        self.slots[base..base + WAYS].contains(&Some(key))
    }
    // Call only after current root-scope validation, in safe ordinary empty
    // context. All IDs were minted by this State's original Decoder; this owner
    // is never transferred between decoders or used in formation/private staging.
    pub(super) fn lookup(
        &mut self,
        key: Option<Key>,
        budget: &mut Budget,
    ) -> Result<bool, ResourceError> {
        let Some(key) = key else { return Ok(false) };
        budget.charge_work(1)?;
        let found = self.contains(key);
        Ok(found)
    }
    // Called after completed checking/session rollback, before fallible metadata
    // preparation and installation. Allocation is still allowed to fail here.
    // This pending key is not visible to contains, and is dropped on any failure.
    pub(super) fn prepare(
        &mut self,
        key: Option<Key>,
        work: u64,
        budget: &mut Budget,
    ) -> Result<(), ResourceError> {
        self.pending = None;
        let Some(key) = key else { return Ok(()) };
        let admission = ADMISSION;
        if work < admission || self.contains(key) {
            return Ok(());
        }
        if self.slots.is_empty() {
            // Flat initialization, plus prepayment for the two flat retirements.
            // Charge at the known allocation boundary, never per element in a hot loop.
            budget.charge_work((SLOTS + BUCKETS + 2) as u64)?;
            budget.grow_vec(&mut self.slots, SLOTS)?;
            budget.grow_vec(&mut self.cursors, BUCKETS)?;
            self.slots.resize(SLOTS, None);
            self.cursors.resize(BUCKETS, 0);
        }
        self.pending = Some(key);
        Ok(())
    }
    // Only the outer State calls this after its final Installed+cleanup result.
    // All space is prepared; publication cannot allocate, charge, fail or query.
    pub(super) fn finish(&mut self, installed: bool) {
        if let Some(key) = self.pending.take().filter(|_| installed) {
            // Construction: prepare allocated exactly SLOTS/BUCKETS, and the
            // masked hash/cursor give bucket<BUCKETS and cursor<WAYS.
            let bucket = key.bucket();
            let cursor = usize::from(self.cursors[bucket]);
            self.slots[bucket * WAYS + cursor] = Some(key);
            self.cursors[bucket] = ((cursor + 1) & (WAYS - 1)) as u8;
        }
    }
    pub(super) fn retire(&mut self, budget: &mut Budget) -> Result<(), ResourceError> {
        self.pending = None;
        let slots = take(&mut self.slots);
        let cursors = take(&mut self.cursors);
        let bytes = slots.capacity() * size_of::<Option<Key>>() + cursors.capacity();
        drop(slots);
        drop(cursors);
        if bytes == 0 {
            Ok(())
        } else {
            budget.release(bytes as u64)
        }
    }
}
