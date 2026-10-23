//! Completed original delta-body and recursor-rule transport, scoped to one fixed ordinary driver.
//! Caller validates committed source, visibility, safety and universe scope before
//! lookup. Only completed transport INCLUDING scratch retirement may insert.
//! Exact level identities are keys; syntax reuse supplies no checking judgment.
mod prefix;
use crate::resource::{Budget, ResourceError, SessionCacheBudget};
use crate::syntax::expressions::{ExprId, Expressions};
use crate::syntax::levels::LevelId;
use std::hash::Hasher;
use std::mem::size_of;

#[derive(Clone, Copy, Default)]
struct Entry {
    declaration: u32,
    result: u32,
    start: u32,
    len: u32,
    hash: u32,
}
const _: () = assert!(size_of::<Entry>() == 20);
const _: () = assert!(size_of::<LevelId>() == 4);

/// No source or result survives driver retirement or source-frontier changes.
/// Original committed bodies and universe substitution contain no term locals;
/// descendant local retirement therefore cannot invalidate an admitted result.
/// Any error requires caller cleanup/abort; this primitive grants no retry rights.
#[derive(Default)]
pub(crate) struct Cache {
    entries: Vec<Entry>,
    arguments: Vec<u32>,
    used: usize,
    stopped: bool,
    prefixes: prefix::Cache,
}
const _: () = assert!(size_of::<Cache>() == 88);
impl Cache {
    /// Raw completed beta reuse; the caller supplies the validated fixed prefix.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn reduce_rule_prefix(
        &mut self,
        source: ExprId,
        arguments: &[ExprId],
        incoming: crate::resource::ReductionPath,
        expressions: &mut Expressions,
        levels: &crate::syntax::levels::Levels,
        names: &crate::syntax::names::Names,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<
        Option<(ExprId, crate::resource::ReductionPath)>,
        crate::syntax::expressions::ExpressionError,
    > {
        self.prefixes.reduce(
            source,
            arguments,
            incoming,
            expressions,
            levels,
            names,
            session,
            b,
        )
    }
    fn hash<const RULE: bool>(
        declaration: u32,
        rule: u32,
        arguments: &[LevelId],
        b: &mut Budget,
    ) -> Result<u32, ResourceError> {
        b.charge_work(arguments.len() as u64 + u64::from(RULE) + 1)?;
        let mut h = crate::syntax::hash::FastHasher::new();
        h.write_u32(declaration);
        h.write_usize(arguments.len() + usize::from(RULE));
        if RULE {
            h.write_u32(rule);
        }
        for argument in arguments {
            h.write_u32(argument.slot());
        }
        Ok((h.finish() as u32).max(1))
    }
    fn position<const RULE: bool>(
        &self,
        declaration: u32,
        rule: u32,
        arguments: &[LevelId],
        hash: u32,
        b: &mut Budget,
    ) -> Result<usize, ResourceError> {
        let mask = self
            .entries
            .len()
            .checked_sub(1)
            .ok_or(ResourceError::Invariant)?;
        let mut slot = hash as usize & mask;
        for _ in 0..self.entries.len() {
            b.charge_work(1)?;
            let entry = self.entries[slot];
            if entry.hash == 0 {
                return Ok(slot);
            }
            if entry.hash == hash
                && entry.declaration == declaration
                && entry.len as usize == arguments.len() + usize::from(RULE)
            {
                let end = (entry.start as usize)
                    .checked_add(entry.len as usize)
                    .ok_or(ResourceError::Counter)?;
                let stored = self
                    .arguments
                    .get(entry.start as usize..end)
                    .ok_or(ResourceError::Invariant)?;
                b.charge_work(arguments.len() as u64 + u64::from(RULE) + 1)?;
                if (!RULE || stored.first() == Some(&rule))
                    && stored[usize::from(RULE)..]
                        .iter()
                        .zip(arguments)
                        .all(|(a, b)| *a == b.slot())
                {
                    return Ok(slot);
                }
            }
            slot = (slot + 1) & mask;
        }
        Err(ResourceError::Invariant)
    }
    // A validated declaration has exactly one immutable kind and universe arity.
    // Thus a delta-body key cannot alias a rule key for that declaration slot.
    pub(crate) fn get(
        &self,
        declaration: u32,
        arguments: &[LevelId],
        expressions: &Expressions,
        b: &mut Budget,
    ) -> Result<Option<ExprId>, ResourceError> {
        self.get_kind::<false>(declaration, 0, arguments, expressions, b)
    }
    pub(crate) fn get_rule(
        &self,
        declaration: u32,
        rule: u32,
        arguments: &[LevelId],
        expressions: &Expressions,
        b: &mut Budget,
    ) -> Result<Option<ExprId>, ResourceError> {
        self.get_kind::<true>(declaration, rule, arguments, expressions, b)
    }
    pub(crate) fn insert(
        &mut self,
        declaration: u32,
        arguments: &[LevelId],
        result: ExprId,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        self.insert_kind::<false>(declaration, 0, arguments, result, session, b)
    }
    pub(crate) fn insert_rule(
        &mut self,
        declaration: u32,
        rule: u32,
        arguments: &[LevelId],
        result: ExprId,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        self.insert_kind::<true>(declaration, rule, arguments, result, session, b)
    }
    fn get_kind<const RULE: bool>(
        &self,
        declaration: u32,
        rule: u32,
        arguments: &[LevelId],
        expressions: &Expressions,
        b: &mut Budget,
    ) -> Result<Option<ExprId>, ResourceError> {
        b.charge_work(1)?;
        if self.entries.is_empty() {
            return Ok(None);
        }
        let hash = Self::hash::<RULE>(declaration, rule, arguments, b)?;
        let entry = self.entries[self.position::<RULE>(declaration, rule, arguments, hash, b)?];
        if entry.hash == 0 {
            return Ok(None);
        }
        Ok(Some(expressions.resolve_slot(entry.result, b)?))
    }
    fn insert_kind<const RULE: bool>(
        &mut self,
        declaration: u32,
        rule: u32,
        arguments: &[LevelId],
        result: ExprId,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        b.charge_work(1)?;
        if self.stopped {
            return Ok(());
        }
        let hash = Self::hash::<RULE>(declaration, rule, arguments, b)?;
        if !self.entries.is_empty()
            && self.entries[self.position::<RULE>(declaration, rule, arguments, hash, b)?].hash != 0
        {
            // Completed deterministic construction may return a fresh equivalent
            // handle. Preserve the first result; no equality inference is made.
            return Ok(());
        }
        let len = u32::try_from(arguments.len() + usize::from(RULE))
            .map_err(|_| ResourceError::Counter)?;
        let start = u32::try_from(self.arguments.len()).map_err(|_| ResourceError::Counter)?;
        let needed = self
            .arguments
            .len()
            .checked_add(arguments.len() + usize::from(RULE))
            .ok_or(ResourceError::Counter)?;
        u32::try_from(needed).map_err(|_| ResourceError::Counter)?;
        let entry_cap = if self.used + 1 > self.entries.len() / 4 * 3 {
            self.entries
                .len()
                .checked_mul(2)
                .ok_or(ResourceError::Counter)?
                .max(16)
        } else {
            0
        };
        let argument_cap = if needed > self.arguments.capacity() {
            self.arguments
                .capacity()
                .checked_mul(2)
                .ok_or(ResourceError::Counter)?
                .max(needed)
                .max(8)
        } else {
            0
        };
        let bytes = entry_cap
            .checked_mul(size_of::<Entry>())
            .and_then(|n| {
                argument_cap
                    .checked_mul(size_of::<u32>())
                    .and_then(|m| n.checked_add(m))
            })
            .ok_or(ResourceError::Counter)? as u64;
        // Check both replacement arrays together while all old capacity is live.
        // Probe the shared allowance without retaining a second reservation.
        if !b.has_storage_headroom(bytes) || !session.reserve(bytes)? {
            self.stopped = true;
            return Ok(());
        }
        session.release(bytes)?;
        if entry_cap != 0 {
            self.grow_entries(entry_cap, session, b)?;
        }
        if argument_cap != 0 {
            let mut next = allocate(argument_cap, session, b)?;
            if let Err(error) = b.charge_work(self.arguments.len() as u64 + 1) {
                release(next, session, b)?;
                return Err(error);
            }
            next.extend_from_slice(&self.arguments);
            release(std::mem::replace(&mut self.arguments, next), session, b)?;
        }
        let slot = self.position::<RULE>(declaration, rule, arguments, hash, b)?;
        b.charge_work(arguments.len() as u64 + u64::from(RULE) + 1)?;
        // Capacity was secured above; neither append nor bucket publication can fail.
        if RULE {
            self.arguments.push(rule);
        }
        self.arguments.extend(arguments.iter().map(|id| id.slot()));
        self.entries[slot] = Entry {
            declaration,
            result: result.slot(),
            start,
            len,
            hash,
        };
        self.used += 1;
        Ok(())
    }
    fn grow_entries(
        &mut self,
        cap: usize,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        let mut next: Vec<Entry> = allocate(cap, session, b)?;
        let result = (|| {
            b.charge_work(cap as u64 + 1)?;
            next.resize(cap, Entry::default());
            for entry in self.entries.iter().copied().filter(|e| e.hash != 0) {
                let mut slot = entry.hash as usize & (cap - 1);
                loop {
                    b.charge_work(1)?;
                    if next[slot].hash == 0 {
                        break;
                    }
                    slot = (slot + 1) & (cap - 1);
                }
                next[slot] = entry;
            }
            Ok(())
        })();
        if let Err(error) = result {
            release(next, session, b)?;
            return Err(error);
        }
        release(std::mem::replace(&mut self.entries, next), session, b)
    }
    pub(crate) fn retire(
        self,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        let entries = release(self.entries, session, b);
        let arguments = release(self.arguments, session, b);
        let prefixes = self.prefixes.retire(session, b);
        entries.and(arguments).and(prefixes)
    }
}
fn allocate<T>(
    cap: usize,
    session: &mut SessionCacheBudget,
    b: &mut Budget,
) -> Result<Vec<T>, ResourceError> {
    let bytes = cap
        .checked_mul(size_of::<T>())
        .ok_or(ResourceError::Counter)? as u64;
    if !session.reserve(bytes)? {
        return Err(ResourceError::Invariant);
    }
    let mut next = Vec::new();
    if let Err(error) = b.grow_vec(&mut next, cap) {
        session.release(bytes)?;
        return Err(error);
    }
    Ok(next)
}
fn release<T>(
    values: Vec<T>,
    session: &mut SessionCacheBudget,
    b: &mut Budget,
) -> Result<(), ResourceError> {
    let bytes = values
        .capacity()
        .checked_mul(size_of::<T>())
        .ok_or(ResourceError::Counter)? as u64;
    drop(values);
    let a = session.release(bytes);
    let c = b.release(bytes);
    a.and(c)
}
