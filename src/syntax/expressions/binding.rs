//! Term binding operations; no level reconstruction or typing judgment.
pub(crate) mod plan;
use super::{ExprId, ExprKind, ExpressionError, Expressions};
use crate::resource::{Budget, ResourceError};
use crate::syntax::levels::{LevelNames, Levels};
use std::mem::size_of;

/// Vector position zero denotes the nearest replaced/abstracted binder.
/// Instantiate arguments must have no loose bound variables (free ids are okay).
/// Lower removes a range containing no occurrences; an occurrence in that range
/// is a broken caller invariant, never an inequality or input rejection.
#[derive(Clone, Copy)]
pub(crate) enum Binding<'a> {
    Instantiate(&'a [ExprId]),
    /// Lazy nearest-binder lookup in one fixed immutable evaluation environment.
    /// Every returned slot belongs to this expression store and is closed with
    /// respect to bound variables; validate each demanded replacement below.
    Environment {
        len: u32,
        lookup: &'a dyn Fn(u32, &mut Budget) -> Result<u32, ResourceError>,
    },
    Abstract(&'a [u32]),
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    Lift(u32),
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    Lower(u32),
}

#[derive(Clone, Copy, Default)]
struct Entry {
    source: u32,
    offset: u32,
    result: u32,
    hash: u32,
}
const _: () = assert!(size_of::<Entry>() == 16);

/// Completed (source, binder offset) -> result, for exactly one fixed operation,
/// vector, originating store, declaration and context. Never a judgment cache.
/// Only Abstract's unchanged results use canonical offset zero: fresh-append
/// construction proves absence of all target free IDs, independent of offset.
/// A separate instance indexes unique abstraction free ids -> vector positions.
#[derive(Default)]
struct Memo {
    entries: Vec<Entry>,
    used: usize,
}
/// Fixed wide-avalanche finalizer (splitmix64) for exact-key binding tables.
/// Distribution-only: every consumer recompares full keys, so collision
/// behavior costs probes, never correctness.
#[inline(always)]
fn mix64(mixed: u64) -> u64 {
    let z = (mixed ^ (mixed >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    let z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

impl Memo {
    // Keep the fixed-size hash and probe boundary visible to binding callers.
    // All three helpers are inlined together; keeping key inlined with them
    // lets the finalizer fold into the probe on the pinned compiler.
    #[inline(always)]
    fn key(source: u32, offset: u32) -> Entry {
        // Keys are two 32-bit halves, so a fixed wide-avalanche integer
        // finalizer avoids the streaming hasher call while distributing every
        // input bit across the word; entry comparisons stay exact (source,
        // offset), so hash quality affects only probe counts, never results.
        // Differentiating the halves by word position keeps the low 1<<n
        // bucket windows (binding::plan tables index identical (source,
        // offset) spaces) from folding distinct keys.
        let mixed = source as u64 | ((offset as u64) << 32);
        Entry {
            source,
            offset,
            result: 0,
            hash: (mix64(mixed) as u32).max(1),
        }
    }
    fn position(entries: &[Entry], key: Entry, b: &mut Budget) -> Result<usize, ResourceError> {
        let mask = entries
            .len()
            .checked_sub(1)
            .ok_or(ResourceError::Invariant)?;
        let mut slot = key.hash as usize & mask;
        for _ in 0..entries.len() {
            b.charge_work(1)?;
            let e = entries[slot];
            if e.hash == 0
                || (e.hash == key.hash && e.source == key.source && e.offset == key.offset)
            {
                return Ok(slot);
            }
            slot = (slot + 1) & mask;
        }
        Err(ResourceError::Invariant)
    }
    #[inline(always)]
    fn get(&self, source: u32, offset: u32, b: &mut Budget) -> Result<Option<u32>, ResourceError> {
        if self.entries.is_empty() {
            return Ok(None);
        }
        let e = self.entries[Self::position(&self.entries, Self::key(source, offset), b)?];
        Ok((e.hash != 0).then_some(e.result))
    }
    #[inline(always)]
    fn insert(
        &mut self,
        source: u32,
        offset: u32,
        result: u32,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        if self.used + 1 > self.entries.len() / 4 * 3 {
            self.grow(b)?;
        }
        let mut key = Self::key(source, offset);
        key.result = result;
        let slot = Self::position(&self.entries, key, b)?;
        if self.entries[slot].hash == 0 {
            self.used += 1;
        } else if self.entries[slot].result != result {
            return Err(ResourceError::Invariant);
        }
        self.entries[slot] = key;
        Ok(())
    }
    fn grow(&mut self, b: &mut Budget) -> Result<(), ResourceError> {
        let cap = self
            .entries
            .len()
            .checked_mul(2)
            .ok_or(ResourceError::Counter)?
            .max(16);
        let mut next = Vec::new();
        b.grow_vec(&mut next, cap)?;
        let r = (|| {
            b.charge_work(cap as u64 + 1)?;
            next.resize(cap, Entry::default());
            for e in self.entries.iter().copied().filter(|e| e.hash != 0) {
                let slot = Self::position(&next, e, b)?;
                next[slot] = e;
            }
            Ok(())
        })();
        if let Err(error) = r {
            release(next, b)?;
            return Err(error);
        }
        release(std::mem::replace(&mut self.entries, next), b)
    }
}
fn release<T: Copy>(v: Vec<T>, b: &mut Budget) -> Result<(), ResourceError> {
    let bytes = v
        .capacity()
        .checked_mul(size_of::<T>())
        .ok_or(ResourceError::Counter)?;
    drop(v);
    b.release(bytes as u64)
}
#[derive(Clone, Copy)]
enum Frame {
    Visit(ExprId, u32),
    Finish(ExprId, u32),
}
const _: () = assert!(size_of::<Frame>() <= 12);
#[derive(Default)]
struct Scratch {
    memo: Memo,
    variables: Memo,
    frames: Vec<Frame>,
    results: Vec<ExprId>,
}
impl Scratch {
    fn frame(&mut self, f: Frame, b: &mut Budget) -> Result<(), ResourceError> {
        let required = self
            .frames
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        b.reserve_frames(1)?;
        if let Err(e) = b.grow_vec(&mut self.frames, required) {
            b.release_frames(1)?;
            return Err(e);
        }
        self.frames.push(f);
        Ok(())
    }
    fn result(&mut self, id: ExprId, b: &mut Budget) -> Result<(), ResourceError> {
        let required = self
            .results
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        b.reserve_frames(1)?;
        if let Err(e) = b.grow_vec(&mut self.results, required) {
            b.release_frames(1)?;
            return Err(e);
        }
        self.results.push(id);
        Ok(())
    }
    fn pop_result(&mut self, b: &mut Budget) -> Result<ExprId, ResourceError> {
        let id = self.results.pop().ok_or(ResourceError::Invariant)?;
        b.release_frames(1)?;
        Ok(id)
    }
    fn dispose(self, b: &mut Budget) -> Result<(), ResourceError> {
        let count = self.frames.len() + self.results.len();
        // No native recursion or per-node destructor; all releases run even if
        // an earlier ledger release detects an invariant failure.
        let a = release(self.memo.entries, b);
        let c = release(self.variables.entries, b);
        let d = release(self.frames, b);
        let e = release(self.results, b);
        let f = b.release_frames(count);
        a.and(c).and(d).and(e).and(f)
    }
}

impl Expressions {
    /// Caller preserves table/context origins and uses free ids only in scope.
    /// Traversal schedules original children only; replacement syntax is never
    /// visited. A completed result may share rebuilt expression composites but
    /// transports every level handle unchanged.
    /// No callback can ignore an intermediate failure: only a completed root is
    /// returned. On panic the whole run/ledger must be discarded, not resumed.
    pub(crate) fn bind(
        &mut self,
        root: ExprId,
        cutoff: u32,
        operation: Binding<'_>,
        levels: &Levels,
        names: &impl LevelNames,
        b: &mut Budget,
    ) -> Result<ExprId, ExpressionError> {
        self.bind_mode::<true>(root, cutoff, operation, levels, names, b)
    }
    /// Nested template producer: no result memo may introduce fresh sharing.
    /// Same scope and replacement invariants as `bind`; replacement leaves stay exact.
    pub(crate) fn bind_template(
        &mut self,
        root: ExprId,
        arguments: &[ExprId],
        levels: &Levels,
        names: &impl LevelNames,
        b: &mut Budget,
    ) -> Result<ExprId, ExpressionError> {
        self.bind_mode::<false>(root, 0, Binding::Instantiate(arguments), levels, names, b)
    }
    fn bind_mode<const CACHED: bool>(
        &mut self,
        root: ExprId,
        cutoff: u32,
        operation: Binding<'_>,
        levels: &Levels,
        names: &impl LevelNames,
        b: &mut Budget,
    ) -> Result<ExprId, ExpressionError> {
        self.bind_validated_mode::<CACHED, false>(root, cutoff, operation, levels, names, b)
    }
    // Private structural-entry contract: VALIDATED is true only after get(root)
    // and complete Instantiate argument validation for this exact operation/store.
    // VALIDATED=true is restricted to Instantiate/Environment: Abstract also
    // builds a required variable map in the skipped block, so it must use false.
    // No typing judgment or callback result is carried by this flag.
    #[allow(clippy::too_many_arguments)]
    fn bind_validated_mode<const CACHED: bool, const VALIDATED: bool>(
        &mut self,
        root: ExprId,
        cutoff: u32,
        operation: Binding<'_>,
        levels: &Levels,
        names: &impl LevelNames,
        b: &mut Budget,
    ) -> Result<ExprId, ExpressionError> {
        // Precharge a fixed number of flat cleanup actions before scratch exists.
        b.charge_work(5)?;
        let mut s = Scratch::default();
        let result =
            self.bind_inner::<CACHED, VALIDATED>(root, cutoff, operation, levels, names, b, &mut s);
        let cleanup = s.dispose(b);
        cleanup?;
        result
    }
    #[allow(clippy::too_many_arguments)]
    fn bind_inner<const CACHED: bool, const VALIDATED: bool>(
        &mut self,
        root: ExprId,
        cutoff: u32,
        op: Binding<'_>,
        levels: &Levels,
        names: &impl LevelNames,
        b: &mut Budget,
        s: &mut Scratch,
    ) -> Result<ExprId, ExpressionError> {
        if !VALIDATED {
            self.get(root, b)?;
            match op {
                Binding::Instantiate(args) => {
                    u32::try_from(args.len()).map_err(|_| ExpressionError::NumericRange)?;
                    b.charge_work(args.len() as u64)?;
                    for arg in args {
                        if self.get(*arg, b)?.loose_range() != 0 {
                            return Err(ResourceError::Invariant.into());
                        }
                    }
                }
                Binding::Abstract(ids) => {
                    u32::try_from(ids.len()).map_err(|_| ExpressionError::NumericRange)?;
                    for (index, id) in ids.iter().copied().enumerate() {
                        b.charge_work(1)?;
                        if s.variables.get(id, 0, b)?.is_some() {
                            return Err(ResourceError::Invariant.into());
                        }
                        s.variables.insert(id, 0, index as u32, b)?;
                    }
                }
                _ => {}
            }
        }
        s.frame(Frame::Visit(root, cutoff), b)?;
        while let Some(frame) = s.frames.pop() {
            b.release_frames(1)?;
            b.charge_work(1)?;
            b.observe(crate::resource::Event::MachineSteps, 1);
            match frame {
                Frame::Visit(id, offset) => {
                    let node = self.get(id, b)?;
                    let skip = match op {
                        Binding::Abstract(_) => !node.has_free(),
                        _ => node.loose_range() <= offset,
                    };
                    if skip {
                        s.result(id, b)?;
                        continue;
                    }
                    // Abstract changes a targeted Free to a fresh Bound and
                    // rebuilds every changed ancestor with a fresh handle. Thus
                    // a completed source -> source entry proves target absence
                    // for this one fixed ID vector/store/call at every offset.
                    // Depth bounds all descendant binder increments: do not
                    // bypass NumericRange at an overflowing caller offset.
                    if CACHED
                        && matches!(op, Binding::Abstract(_))
                        && offset != 0
                        && offset <= u32::MAX - node.depth()
                        && s.memo.get(id.0, 0, b)? == Some(id.0)
                    {
                        s.result(id, b)?;
                        continue;
                    }
                    if CACHED && let Some(result) = s.memo.get(id.0, offset, b)? {
                        s.result(ExprId(result), b)?;
                        continue;
                    }
                    let leaf = match node.kind(self, levels, b)? {
                        ExprKind::Bound(index) => {
                            let next = match op {
                                Binding::Instantiate(args) if index >= offset => {
                                    if let Some(arg) = args.get((index - offset) as usize) {
                                        s.result(*arg, b)?;
                                        continue;
                                    }
                                    index
                                        .checked_sub(args.len() as u32)
                                        .ok_or(ResourceError::Invariant)?
                                }
                                Binding::Environment { len, lookup } if index >= offset => {
                                    let relative = index - offset;
                                    if relative < len {
                                        let arg = self.resolve_slot(lookup(relative, b)?, b)?;
                                        if self.get(arg, b)?.loose_range() != 0 {
                                            return Err(ResourceError::Invariant.into());
                                        }
                                        s.result(arg, b)?;
                                        continue;
                                    }
                                    index.checked_sub(len).ok_or(ResourceError::Invariant)?
                                }
                                Binding::Lift(n) if index >= offset => {
                                    index.checked_add(n).ok_or(ExpressionError::NumericRange)?
                                }
                                Binding::Lower(n) if index >= offset => {
                                    let lowered =
                                        index.checked_sub(n).ok_or(ResourceError::Invariant)?;
                                    if lowered < offset {
                                        return Err(ResourceError::Invariant.into());
                                    }
                                    lowered
                                }
                                _ => index,
                            };
                            Some(if next == index {
                                id
                            } else {
                                self.append(ExprKind::Bound(next), levels, names, b)?
                            })
                        }
                        ExprKind::Free(f) => Some(if matches!(op, Binding::Abstract(_)) {
                            if let Some(index) = s.variables.get(f, 0, b)? {
                                let index = offset
                                    .checked_add(index)
                                    .ok_or(ExpressionError::NumericRange)?;
                                self.append(ExprKind::Bound(index), levels, names, b)?
                            } else {
                                id
                            }
                        } else {
                            id
                        }),
                        ExprKind::Sort(_)
                        | ExprKind::Constant(..)
                        | ExprKind::Natural(_)
                        | ExprKind::String(_) => Some(id),
                        kind => {
                            // This descriptor belongs to the immutable source node.
                            // Scheduling only changes scratch: reuse the decoded
                            // kind without retaining a view across child rebuilding.
                            s.frame(Frame::Finish(id, offset), b)?;
                            match kind {
                                ExprKind::App(a, c) => {
                                    s.frame(Frame::Visit(c, offset), b)?;
                                    s.frame(Frame::Visit(a, offset), b)?;
                                }
                                ExprKind::Lambda(_, domain, body, _)
                                | ExprKind::Pi(_, domain, body, _) => {
                                    let inner = offset
                                        .checked_add(1)
                                        .ok_or(ExpressionError::NumericRange)?;
                                    s.frame(Frame::Visit(body, inner), b)?;
                                    s.frame(Frame::Visit(domain, offset), b)?;
                                }
                                ExprKind::Let(_, ty, value, body, _) => {
                                    let inner = offset
                                        .checked_add(1)
                                        .ok_or(ExpressionError::NumericRange)?;
                                    s.frame(Frame::Visit(body, inner), b)?;
                                    s.frame(Frame::Visit(value, offset), b)?;
                                    s.frame(Frame::Visit(ty, offset), b)?;
                                }
                                ExprKind::Projection(_, _, target) => {
                                    s.frame(Frame::Visit(target, offset), b)?
                                }
                                ExprKind::MData(_, wrapped) => {
                                    s.frame(Frame::Visit(wrapped, offset), b)?
                                }
                                _ => return Err(ResourceError::Invariant.into()),
                            }
                            None
                        }
                    };
                    if let Some(result) = leaf {
                        if CACHED {
                            s.memo.insert(
                                id.0,
                                memo_offset(op, id, result, offset),
                                result.0,
                                b,
                            )?;
                        }
                        s.result(result, b)?;
                        continue;
                    }
                }
                Frame::Finish(id, offset) => {
                    let node = self.get(id, b)?;
                    // Metadata wrappers rebuild through the retained payload
                    // span: a borrowed slice cannot cross the mutable append,
                    // and reusing the span shares the already-resident bytes
                    // instead of copying them a second time. The span layout
                    // is the tag-11 inverse in kind(): wrapped, offset, count.
                    if node.tag() == 11 {
                        let descriptor = node.raw_descriptor(self)?;
                        let wrapped = ExprId(descriptor.fields[0]);
                        let w = s.pop_result(b)?;
                        let result = if w == wrapped {
                            id
                        } else {
                            self.append_metadata_span(
                                w,
                                (descriptor.fields[1], descriptor.fields[2]),
                                b,
                            )?
                        };
                        if CACHED {
                            s.memo.insert(
                                id.0,
                                memo_offset(op, id, result, offset),
                                result.0,
                                b,
                            )?;
                        }
                        s.result(result, b)?;
                        continue;
                    }
                    let original_kind = node.kind(self, levels, b)?;
                    let kind = match original_kind {
                        ExprKind::App(a, c) => {
                            let y = s.pop_result(b)?;
                            let x = s.pop_result(b)?;
                            if (x, y) == (a, c) {
                                None
                            } else {
                                Some(ExprKind::App(x, y))
                            }
                        }
                        ExprKind::Lambda(name, domain, body, annotation)
                        | ExprKind::Pi(name, domain, body, annotation) => {
                            let r = s.pop_result(b)?;
                            let d = s.pop_result(b)?;
                            if (d, r) == (domain, body) {
                                None
                            } else if matches!(original_kind, ExprKind::Lambda(..)) {
                                Some(ExprKind::Lambda(name, d, r, annotation))
                            } else {
                                Some(ExprKind::Pi(name, d, r, annotation))
                            }
                        }
                        ExprKind::Let(name, ty, value, body, nondep) => {
                            let r = s.pop_result(b)?;
                            let v = s.pop_result(b)?;
                            let t = s.pop_result(b)?;
                            if (t, v, r) == (ty, value, body) {
                                None
                            } else {
                                Some(ExprKind::Let(name, t, v, r, nondep))
                            }
                        }
                        ExprKind::Projection(name, index, target) => {
                            let t = s.pop_result(b)?;
                            if t == target {
                                None
                            } else {
                                Some(ExprKind::Projection(name, index, t))
                            }
                        }
                        _ => return Err(ResourceError::Invariant.into()),
                    };
                    let result = if let Some(kind) = kind {
                        self.append(kind, levels, names, b)?
                    } else {
                        id
                    };
                    if CACHED {
                        s.memo
                            .insert(id.0, memo_offset(op, id, result, offset), result.0, b)?;
                    }
                    s.result(result, b)?;
                }
            }
        }
        let result = s.pop_result(b)?;
        if !s.results.is_empty() {
            return Err(ResourceError::Invariant.into());
        }
        Ok(result)
    }
}

/// Only completed unchanged Abstract results certify offset-independent absence.
/// The separate free-ID index never uses this result-memo key classification.
#[inline]
fn memo_offset(op: Binding<'_>, source: ExprId, result: ExprId, offset: u32) -> u32 {
    if matches!(op, Binding::Abstract(_)) && source == result {
        0
    } else {
        offset
    }
}
