//! One ordinary checked inference owner, fixed universe/template/safety scope.
//! Projected keys retain exact source and every referenced FreeId. FreeIds have
//! immutable checked types/let values, and remain active on a hit. Direct-Free
//! syntax and dependency shapes outside the bounded mask use exact-context keys.
//!
//! Weakening invariant: inference constructors introduce no ambient dependencies.
//! Atoms use their source or referenced local declaration; application substitutes
//! the checked argument into its function type; Pi/lambda close the introduced
//! local, and let closes then substitutes its checked value. Projection and head
//! demands derive only from these terms in the fixed declaration environment.
//! Thus a completed type contains only source dependencies and their earlier
//! context dependencies. An active referenced local keeps those earlier locals
//! active. Temporary binder/comparison locals cannot escape completed inference.
//! MemoResult publishes after all premises and binder cleanup; no observation,
//! failed route, negative or cross-owner result can enter this table.
use super::*;
use crate::resource::SessionCacheBudget;
use std::hash::{Hash, Hasher};

// Low hash bits distinguish disjoint key spaces, including metadata. Zero is
// vacant. Metadata height is 0 for a derived mask and 1 for unsupported syntax.
// Distribution-only fixed-word hashing; every lookup verifies exact fields.
struct KeyHash(u32);
impl Hasher for KeyHash {
    fn finish(&self) -> u64 {
        u64::from(self.0)
    }
    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 = mix(self.0, u32::from(*byte));
        }
    }
    fn write_u32(&mut self, value: u32) {
        self.0 = mix(self.0, value);
    }
}
const EXACT: u32 = 1;
const PROJECTED: u32 = 2;
const DEPENDENCIES: u32 = 3;
#[derive(Clone, Copy, Default)]
struct Entry {
    source: u32,
    environment: EnvId,
    context: u32,
    result: u32,
    height: u32,
    hash: u32,
    dependencies: u64,
}
const _: () = assert!(size_of::<Entry>() == 32);
#[derive(Default)]
pub(super) struct Memo {
    entries: Vec<Entry>,
}
const _: () = assert!(size_of::<Memo>() == 24);
impl Memo {
    // Bucket zero is the count header; all other buckets form one shared table.
    fn used(&self) -> usize {
        self.entries
            .first()
            .map_or(0, |header| header.source as usize)
    }
    fn tagged_hash(h: KeyHash, tag: u32) -> u32 {
        (h.finish() as u32 & !3) | tag
    }
    #[inline]
    fn key(view: View, context: u32) -> Entry {
        let mut h = KeyHash(0);
        (view.expression.slot(), view.environment, context).hash(&mut h);
        Entry {
            source: view.expression.slot(),
            environment: view.environment,
            context,
            hash: Self::tagged_hash(h, EXACT),
            ..Entry::default()
        }
    }
    fn dependency_key(source: ExprId) -> Entry {
        Entry {
            source: source.slot(),
            hash: (mix(0, source.slot()) & !3) | DEPENDENCIES,
            ..Entry::default()
        }
    }
    // Exact-key lookup also handles metadata and rehashing. Projected equality
    // is checked separately; rehashing never merges entries with equal hashes.
    fn position(entries: &[Entry], key: Entry, b: &mut Budget) -> Result<usize, ResourceError> {
        let mask = entries
            .len()
            .checked_sub(2)
            .ok_or(ResourceError::Invariant)?;
        let mut slot = 1 + ((key.hash >> 2) as usize & mask);
        for _ in 0..entries.len() {
            b.charge_work(1)?;
            let entry = entries[slot];
            if entry.hash == 0
                || (entry.hash == key.hash
                    && entry.source == key.source
                    && entry.environment == key.environment
                    && entry.context == key.context)
            {
                return Ok(slot);
            }
            slot = 1 + (slot & mask);
        }
        Err(ResourceError::Invariant)
    }
    fn dependency(
        &self,
        source: ExprId,
        b: &mut Budget,
    ) -> Result<Option<Option<u64>>, ResourceError> {
        if self.entries.is_empty() {
            return Ok(None);
        }
        let entry = self.entries[Self::position(&self.entries, Self::dependency_key(source), b)?];
        Ok((entry.hash != 0).then_some((entry.height == 0).then_some(entry.dependencies)))
    }
    fn save(&mut self, key: Entry, work: &mut Working<'_>) -> Result<bool, ResourceError> {
        if self.used() + 1 > self.entries.len().saturating_sub(1) / 4 * 3
            && !self.grow(&mut work.caches, work.budget)?
        {
            return Ok(false);
        }
        let slot = Self::position(&self.entries, key, work.budget)?;
        if self.entries[slot].hash == 0 {
            self.entries[slot] = key;
            self.entries[0].source = self.entries[0]
                .source
                .checked_add(1)
                .ok_or(ResourceError::Counter)?;
        }
        Ok(true)
    }
    fn dependencies(
        &mut self,
        source: ExprId,
        work: &mut Working<'_>,
    ) -> Result<Option<u64>, ResourceError> {
        // Existing validated summaries exclude free/wide syntax and prove the
        // empty dependency set; nonempty masks require the derivation below.
        let summary = work.expressions.get(source, work.budget)?;
        if summary.has_free() || summary.loose_range() > 64 {
            return Ok(None);
        }
        // Exact construction summaries prove the empty set without a DAG walk.
        if summary.loose_range() == 0 {
            return Ok(Some(0));
        }
        if let Some(mask) = self.dependency(source, work.budget)? {
            return Ok(mask);
        }
        let mut stack = Vec::new();
        let result = (|| {
            dependency_push(&mut stack, source, work.budget)?;
            while let Some(&id) = stack.last() {
                work.budget.charge_work(1)?;
                let kind = work.expressions.get(id, work.budget)?.kind(
                    work.expressions,
                    work.levels,
                    work.budget,
                )?;
                let mut children = [None; 3];
                let mut valid = true;
                let mut mask = 0;
                match kind {
                    ExprKind::Bound(i) => {
                        if i < 64 {
                            mask = 1u64 << i;
                        } else {
                            valid = false;
                        }
                    }
                    ExprKind::Free(_) | ExprKind::MData(..) => valid = false,
                    ExprKind::App(a, b) => {
                        children[0] = Some((a, false));
                        children[1] = Some((b, false));
                    }
                    ExprKind::Pi(_, a, b, _) | ExprKind::Lambda(_, a, b, _) => {
                        children[0] = Some((a, false));
                        children[1] = Some((b, true));
                    }
                    ExprKind::Let(_, a, v, b, _) => {
                        children[0] = Some((a, false));
                        children[1] = Some((v, false));
                        children[2] = Some((b, true));
                    }
                    ExprKind::Projection(_, _, a) => children[0] = Some((a, false)),
                    ExprKind::Sort(_)
                    | ExprKind::Constant(..)
                    | ExprKind::Natural(_)
                    | ExprKind::String(_) => {}
                }
                let mut missing = None;
                for (child, binds) in children.into_iter().flatten() {
                    match self.dependency(child, work.budget)? {
                        None => {
                            missing = Some(child);
                            break;
                        }
                        Some(None) => {
                            valid = false;
                            break;
                        }
                        Some(Some(m)) => mask |= if binds { m >> 1 } else { m },
                    }
                }
                if let Some(child) = missing {
                    dependency_push(&mut stack, child, work.budget)?;
                    continue;
                }
                let entry = Entry {
                    dependencies: mask,
                    height: u32::from(!valid),
                    ..Self::dependency_key(id)
                };
                if !self.save(entry, work)? {
                    return Ok(None);
                }
                stack.pop();
                work.budget.release_frames(1)?;
            }
            self.dependency(source, work.budget)?
                .ok_or(ResourceError::Invariant)
        })();
        let frames = stack.len();
        let bytes = (stack.capacity() * size_of::<ExprId>()) as u64;
        drop(stack);
        let a = work.budget.release_frames(frames);
        let b = work.budget.release(bytes);
        a.and(b)?;
        result
    }
    fn local(
        env: EnvId,
        index: u32,
        environments: &EvaluationEnvironments,
        work: &mut Working<'_>,
    ) -> Result<Option<u32>, ResourceError> {
        let binding = environments.lookup(env, index, work.budget)?;
        let id = work.expressions.resolve_slot(binding.slot(), work.budget)?;
        Ok(
            match work.expressions.get(id, work.budget)?.kind(
                work.expressions,
                work.levels,
                work.budget,
            )? {
                ExprKind::Free(id) => Some(id),
                _ => None,
            },
        )
    }
    fn lookup_key(
        &mut self,
        view: View,
        context: u32,
        environments: &EvaluationEnvironments,
        work: &mut Working<'_>,
    ) -> Result<Entry, ResourceError> {
        let Some(mask) = self.dependencies(view.expression, work)? else {
            return Ok(Self::key(view, context));
        };
        if mask != 0 && 64 - mask.leading_zeros() > environments.len(view.environment)? {
            return Ok(Self::key(view, context));
        }
        let mut hash = mix(0, view.expression.slot());
        let mut remaining = mask;
        while remaining != 0 {
            let index = remaining.trailing_zeros();
            remaining &= remaining - 1;
            let Some(local) = Self::local(view.environment, index, environments, work)? else {
                return Ok(Self::key(view, context));
            };
            work.context.get(local, work.budget)?;
            hash = mix(hash, local);
        }
        Ok(Entry {
            source: view.expression.slot(),
            environment: view.environment,
            hash: (hash & !3) | PROJECTED,
            dependencies: mask,
            ..Entry::default()
        })
    }
    fn locate(
        &self,
        key: Entry,
        environments: &EvaluationEnvironments,
        work: &mut Working<'_>,
    ) -> Result<usize, ResourceError> {
        if key.hash & 3 != PROJECTED {
            return Self::position(&self.entries, key, work.budget);
        }
        let mask = self
            .entries
            .len()
            .checked_sub(2)
            .ok_or(ResourceError::Invariant)?;
        let mut slot = 1 + ((key.hash >> 2) as usize & mask);
        for _ in 0..self.entries.len() {
            work.budget.charge_work(1)?;
            let entry = self.entries[slot];
            if entry.hash == 0 {
                return Ok(slot);
            }
            if entry.hash == key.hash
                && entry.source == key.source
                && entry.dependencies == key.dependencies
            {
                let mut remaining = key.dependencies;
                let mut equal = true;
                while remaining != 0 {
                    let index = remaining.trailing_zeros();
                    remaining &= remaining - 1;
                    // The current key already checked the active Free identity.
                    // Equal immutable binding handles need no repeated decoding;
                    // distinct handles still compare their exact FreeIds.
                    if entry.environment == key.environment {
                        break;
                    }
                    let old_binding = environments.lookup(entry.environment, index, work.budget)?;
                    let new_binding = environments.lookup(key.environment, index, work.budget)?;
                    if old_binding != new_binding {
                        let old = Self::local(entry.environment, index, environments, work)?;
                        let new = Self::local(key.environment, index, environments, work)?;
                        if old.is_none() || old != new {
                            equal = false;
                            break;
                        }
                    }
                }
                if equal {
                    return Ok(slot);
                }
            }
            slot = 1 + (slot & mask);
        }
        Err(ResourceError::Invariant)
    }
    pub(super) fn get(
        &mut self,
        view: View,
        context: u32,
        incoming: ReductionPath,
        environments: &EvaluationEnvironments,
        work: &mut Working<'_>,
    ) -> Result<Option<Inferred>, ResourceError> {
        work.budget.charge_work(1)?;
        let key = self.lookup_key(view, context, environments, work)?;
        if self.entries.is_empty() {
            return Ok(None);
        }
        let entry = self.entries[self.locate(key, environments, work)?];
        if entry.hash == 0 {
            return Ok(None);
        }
        Ok(Some(Inferred {
            ty: work.expressions.resolve_slot(entry.result, work.budget)?,
            path: incoming.after_height(entry.height)?,
        }))
    }
    pub(super) fn insert(
        &mut self,
        view: View,
        context: u32,
        result: Inferred,
        incoming: ReductionPath,
        environments: &EvaluationEnvironments,
        work: &mut Working<'_>,
    ) -> Result<(), ResourceError> {
        work.budget.charge_work(1)?;
        let mut key = self.lookup_key(view, context, environments, work)?;
        key.result = result.ty.slot();
        key.height = result.path.height_since(incoming)?;
        if !self.entries.is_empty() && self.entries[self.locate(key, environments, work)?].hash != 0
        {
            return Ok(());
        }
        self.save(key, work)?;
        Ok(())
    }
    fn grow(
        &mut self,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<bool, ResourceError> {
        let cap = self
            .entries
            .len()
            .saturating_sub(1)
            .checked_mul(2)
            .ok_or(ResourceError::Counter)?
            .max(16)
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        let bytes = cap
            .checked_mul(size_of::<Entry>())
            .ok_or(ResourceError::Counter)? as u64;
        // No allocation or semantic reservation until BOTH complete peak checks
        // pass. Old table capacity remains charged throughout replacement.
        if !b.has_storage_headroom(bytes) || !session.reserve(bytes)? {
            return Ok(false);
        }
        let mut next = Vec::new();
        if let Err(error) = b.grow_vec(&mut next, cap) {
            // grow_vec rolls back failed actual allocations. An unexpected
            // allocator layout invariant requires whole-run discard as elsewhere.
            session.release(bytes)?;
            return Err(error);
        }
        let result = (|| {
            b.charge_work(cap as u64 + 1)?;
            next.resize(cap, Entry::default());
            next[0].source = u32::try_from(self.used()).map_err(|_| ResourceError::Counter)?;
            for entry in self.entries.iter().copied().filter(|entry| entry.hash != 0) {
                let slot = Self::position(&next, entry, b)?;
                next[slot] = entry;
            }
            Ok(())
        })();
        if let Err(error) = result {
            release(next, session, b)?;
            return Err(error);
        }
        release(std::mem::replace(&mut self.entries, next), session, b)?;
        Ok(true)
    }
    pub(super) fn retire(
        self,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        release(self.entries, session, b)
    }
}
fn release(
    entries: Vec<Entry>,
    session: &mut SessionCacheBudget,
    b: &mut Budget,
) -> Result<(), ResourceError> {
    let bytes = entries
        .capacity()
        .checked_mul(size_of::<Entry>())
        .ok_or(ResourceError::Counter)? as u64;
    drop(entries);
    let a = session.release(bytes);
    let c = b.release(bytes);
    a.and(c)
}

// A filter only: equality always verifies exact keys, including local identities.
// Mix matches the existing expression fingerprint primitive; no cryptographic
// collision resistance is assumed, and every collision probe is charged.
fn mix(hash: u32, field: u32) -> u32 {
    hash.rotate_left(7)
        .wrapping_add(field)
        .wrapping_mul(0x85eb_ca6b)
}

fn dependency_push(
    stack: &mut Vec<ExprId>,
    id: ExprId,
    b: &mut Budget,
) -> Result<(), ResourceError> {
    let count = stack.len().checked_add(1).ok_or(ResourceError::Counter)?;
    b.reserve_frames(1)?;
    if let Err(e) = b.grow_vec(stack, count) {
        b.release_frames(1)?;
        return Err(e);
    }
    stack.push(id);
    Ok(())
}
