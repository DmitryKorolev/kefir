//! Always-on semantic accounting, independent of optional diagnostics.
use std::mem::size_of;

// Test harness service is present in the separately compiled component tests too.

macro_rules! traced {
    ($label:literal, $inputs:expr, $body:block) => {{ { $body } }};
}
pub(crate) use traced;

pub(crate) mod failure;

#[allow(
    dead_code,
    reason = "Complete accepted profile is shared with build identity tooling"
)]
pub(crate) mod profile;

pub(crate) const CONTEXT_DEPTH: usize = profile::CONTEXT_DEPTH;
pub(crate) const INPUT_BYTES: u64 = profile::INPUT_BYTES;
pub(crate) const JSON_DEPTH: u32 = profile::JSON_DEPTH;
pub(crate) const READER_BUFFER_BYTES: usize = profile::READER_BUFFER_BYTES;
pub(crate) const RECORD_BYTES: usize = profile::RECORD_BYTES;
pub(crate) const STRUCTURE_DEPTH: u32 = profile::STRUCTURE_DEPTH;
const WORKLIST_FRAMES: usize = profile::WORKLIST_FRAMES;
const WORK: u64 = profile::WORK_CHARGED;
const STORAGE: u64 = profile::MANAGED_LIVE_BYTES;

#[derive(Clone, Copy)]
pub(crate) enum Bucket {
    Input,
    Report,
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    Runtime,
    Declaration,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ResourceError {
    InputBytes,
    RecordBytes,
    StructureDepth,
    ContextDepth,
    ReductionPath,
    Work,
    Storage,
    Report,
    Counter,
    Allocation,
    Invariant,
}

/// Counter for a demanded reduction route, not total work fuel.
/// Only a new independent declaration request may start at zero. Every child
/// continuation inherits its parent's current counter; completed reductions
/// carry the advanced counter onward. Copying it cannot authorize a reset.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ReductionPath(u32);
impl ReductionPath {
    fn limit() -> u32 {
        profile::REDUCTION_PATH
    }
    /// Join of completed independent premises, never their sum.
    pub(crate) fn maximum(self, other: Self) -> Self {
        traced!("reduction.maximum", (self.0, other.0), {
            Self(self.0.max(other.0))
        })
    }

    pub(crate) fn start() -> Self {
        traced!("reduction.start", (), { Self(0) })
    }
    /// Completed route distance, used certificates. The caller must
    /// supply this route's incoming counter, never an unrelated/reset route.
    pub(crate) fn height_since(self, incoming: Self) -> Result<u32, ResourceError> {
        traced!("reduction.height_since", (self.0, incoming.0), {
            self.0
                .checked_sub(incoming.0)
                .ok_or(ResourceError::Invariant)
        })
    }
    /// Replay a completed height certificate without executing or
    /// counting reductions. The caller must have validated cache scope/key.
    pub(crate) fn after_height(self, height: u32) -> Result<Self, ResourceError> {
        traced!("reduction.after_height", (self.0, height), {
            let next = self
                .0
                .checked_add(height)
                .ok_or(ResourceError::ReductionPath)?;
            if next > Self::limit() {
                return Err(ResourceError::ReductionPath);
            }
            Ok(Self(next))
        })
    }
    /// Reserve a possible successful step before executing it. This value is
    /// published only with a completed reduction; failure returns no new route.
    /// Fixed arithmetic is covered by the evaluator's charged worklist step.
    pub(crate) fn after_reduction(self) -> Result<Self, ResourceError> {
        traced!("reduction.after_reduction", self.0, {
            if self.0 >= Self::limit() {
                return Err(ResourceError::ReductionPath);
            }
            Ok(Self(self.0 + 1))
        })
    }
}
const _: () = assert!(size_of::<ReductionPath>() == 4);

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Snapshot {
    pub work_charged: u64,
    pub live_capacity_bytes: u64,
    pub peak_live_capacity_bytes: u64,
}

/// Mandatory reporting mirrors for one run, retained outside the checking stack.
/// These counts confer no completion evidence and never feed semantic budgets.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Progress {
    pub input_bytes: u64,
    pub records: u64,
    pub checked_declarations: u64,
}
const _: () = assert!(size_of::<Progress>() == 24);

pub(crate) struct Budget {
    work_limit: u64,
    storage_limit: u64,
    snapshot: Snapshot,
    progress: Progress,
    frames: usize,
    #[cfg(feature = "introspection")]
    diagnostics: Diagnostics,
    #[cfg(feature = "introspection")]
    rows: Option<crate::report::attribution::Rows>,
    #[cfg(feature = "introspection")]
    failure_snapshot: Option<crate::report::failure_snapshot::Snapshot>,
}

impl Budget {
    pub(crate) fn new() -> Self {
        let (work_limit, storage_limit) = (WORK, STORAGE);
        #[cfg(feature = "introspection")]
        let mut diagnostics = Diagnostics::default();
        #[cfg(feature = "introspection")]
        let rows = Some(crate::report::attribution::Rows::new(&mut diagnostics));
        Self {
            work_limit,
            storage_limit,
            snapshot: Snapshot::default(),
            progress: Progress::default(),
            frames: 0,
            #[cfg(feature = "introspection")]
            diagnostics,
            #[cfg(feature = "introspection")]
            rows,
            #[cfg(feature = "introspection")]
            failure_snapshot: None,
        }
    }

    pub(crate) fn progress(&self) -> Progress {
        self.progress
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn capture_failure(
        &mut self,
        mut snapshot: crate::report::failure_snapshot::Snapshot,
    ) {
        match &mut self.failure_snapshot {
            None => self.failure_snapshot = Some(snapshot),
            Some(current) if !current.has_rules() && snapshot.has_rules() => {
                snapshot.merge_context(current);
                *current = snapshot;
            }
            Some(current) if current.has_rules() && !snapshot.has_rules() => {
                current.merge_context(&snapshot);
            }
            Some(_) => {}
        }
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn replace_failure(&mut self, snapshot: crate::report::failure_snapshot::Snapshot) {
        self.failure_snapshot = Some(snapshot);
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn ensure_failure_invariant(
        &mut self,
        invariant: crate::report::failure_snapshot::Invariant,
    ) {
        if let Some(snapshot) = &mut self.failure_snapshot {
            snapshot.ensure_invariant(invariant);
        }
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn failure_snapshot(&self) -> Option<&crate::report::failure_snapshot::Snapshot> {
        self.failure_snapshot.as_ref()
    }
    // Called immediately after authoritative checked counter updates, before
    // fallible work or external callbacks. Never reset or reuse this run owner.
    pub(crate) fn admitted_input(&mut self, bytes: u64) {
        traced!("budget.admitted_input", (bytes, self.progress), {
            self.progress.input_bytes = bytes;
        })
    }
    pub(crate) fn decoded_records(&mut self, records: u64) {
        traced!("budget.decoded_records", (records, self.progress), {
            self.progress.records = records;
        })
    }
    pub(crate) fn checked_declarations(&mut self, count: u64) {
        traced!("budget.checked_declarations", (count, self.progress), {
            self.progress.checked_declarations = count;
        })
    }

    /// Diagnostic observation only. Never branch semantic execution on counters.
    /// Until the bucket owner exists this is an unsegmented run accumulator,
    /// not publishable declaration attribution. Production contains no state.
    #[inline]
    pub(crate) fn observe(&mut self, event: Event, count: u64) {
        #[cfg(feature = "introspection")]
        {
            self.diagnostics.event(event, count);
            if self.diagnostics.events().is_none()
                && let Some(rows) = &mut self.rows
            {
                rows.discard(&mut self.diagnostics);
            }
        }
        #[cfg(not(feature = "introspection"))]
        let _ = (event, count);
    }

    #[cfg(feature = "introspection")]
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn events(&self) -> Option<&[u64; 11]> {
        self.diagnostics.events()
    }

    #[cfg(feature = "introspection")]
    fn point(&self) -> Option<crate::report::attribution::Point> {
        Some(crate::report::attribution::Point {
            additive: [
                self.progress.input_bytes,
                self.progress.records,
                self.snapshot.work_charged,
            ],
            events: *self.diagnostics.events()?,
            live: self.snapshot.live_capacity_bytes,
        })
    }

    #[inline]
    pub(crate) fn switch_bucket(&mut self, bucket: Bucket) {
        #[cfg(feature = "introspection")]
        {
            let point = self.point();
            if let Some(rows) = &mut self.rows {
                match point {
                    Some(point) => rows.switch(bucket, point, &mut self.diagnostics),
                    None => rows.discard(&mut self.diagnostics),
                }
            }
        }
        #[cfg(not(feature = "introspection"))]
        let _ = bucket;
    }

    #[inline]
    pub(crate) fn begin_declaration(
        &mut self,
        ordinal: u64,
        name: crate::syntax::levels::NameId,
        names: &crate::syntax::names::Names,
    ) {
        #[cfg(feature = "introspection")]
        {
            let point = self.point();
            if let Some(rows) = &mut self.rows {
                match point {
                    Some(point) => {
                        rows.declaration(ordinal, name, names, point, &mut self.diagnostics)
                    }
                    None => rows.discard(&mut self.diagnostics),
                }
            }
        }
        #[cfg(not(feature = "introspection"))]
        let _ = (ordinal, name, names);
    }

    #[cfg(feature = "introspection")]
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn finish_detail(&mut self) -> Option<crate::report::attribution::Detail<'_>> {
        let point = self.point();
        let rows = self.rows.as_mut()?;
        match point {
            Some(point) => rows.finish(point, &mut self.diagnostics),
            None => {
                rows.discard(&mut self.diagnostics);
                None
            }
        }
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn encode_detail<'a>(&mut self, output: &'a mut [u8]) -> Option<&'a [u8]> {
        let point = self.point();
        let mut rows = self.rows.take()?;
        let result = if self.diagnostics.charge_work(64) {
            point
                .and_then(|point| rows.finish(point, &mut self.diagnostics))
                .and_then(|detail| detail.encode(output, &mut self.diagnostics))
        } else {
            None
        };
        rows.retire(&mut self.diagnostics);
        // Retirement itself can invalidate auxiliary accounting. A previously
        // encoded fragment is usable only while its originating ledger is valid.
        self.diagnostics.events().and(result)
    }

    #[cfg(feature = "introspection")]
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn retire_detail(&mut self) {
        if let Some(rows) = self.rows.take() {
            rows.retire(&mut self.diagnostics);
        }
    }

    /// Charge an entire bounded operation before starting it; never refund work.
    pub(crate) fn charge_work(&mut self, units: u64) -> Result<(), ResourceError> {
        traced!(
            "budget.charge_work",
            (units, self.snapshot, self.work_limit),
            {
                let next = self
                    .snapshot
                    .work_charged
                    .checked_add(units)
                    .ok_or(ResourceError::Counter)?;
                if next > self.work_limit {
                    return Err(ResourceError::Work);
                }
                self.snapshot.work_charged = next;
                Ok(())
            }
        )
    }

    /// Reserve the entire new requested layout while the old layout remains live.
    pub(crate) fn reserve(&mut self, bytes: u64) -> Result<(), ResourceError> {
        traced!(
            "budget.reserve",
            (bytes, self.snapshot, self.storage_limit),
            {
                let next = self
                    .snapshot
                    .live_capacity_bytes
                    .checked_add(bytes)
                    .ok_or(ResourceError::Counter)?;
                if next > self.storage_limit {
                    return Err(ResourceError::Storage);
                }
                self.snapshot.live_capacity_bytes = next;
                self.snapshot.peak_live_capacity_bytes =
                    self.snapshot.peak_live_capacity_bytes.max(next);
                #[cfg(feature = "introspection")]
                if let Some(rows) = &mut self.rows {
                    rows.observe_live(next, &mut self.diagnostics);
                }
                Ok(())
            }
        )
    }

    /// Deterministic optional-cache admission check; this does not reserve any
    /// storage. The owner must reserve immediately before attempting allocation.
    pub(crate) fn has_storage_headroom(&self, bytes: u64) -> bool {
        traced!(
            "budget.has_storage_headroom",
            (bytes, self.snapshot, self.storage_limit),
            {
                self.snapshot
                    .live_capacity_bytes
                    .checked_add(bytes)
                    .is_some_and(|next| next <= self.storage_limit)
            }
        )
    }
    /// Call only after the corresponding requested allocation is no longer owned.
    pub(crate) fn release(&mut self, bytes: u64) -> Result<(), ResourceError> {
        traced!("budget.release", (bytes, self.snapshot), {
            self.snapshot.live_capacity_bytes = self
                .snapshot
                .live_capacity_bytes
                .checked_sub(bytes)
                .ok_or(ResourceError::Invariant)?;
            Ok(())
        })
    }

    pub(crate) fn snapshot(&self) -> Snapshot {
        self.snapshot
    }

    /// All simultaneously owned semantic worklists share this count. Reserve
    /// before pushing, undo a failed push, and release only after removing frames.
    pub(crate) fn reserve_frames(&mut self, count: usize) -> Result<(), ResourceError> {
        traced!("budget.reserve_frames", (count, self.frames), {
            let next = self
                .frames
                .checked_add(count)
                .ok_or(ResourceError::Counter)?;
            if next > WORKLIST_FRAMES {
                return Err(ResourceError::Storage);
            }
            self.frames = next;
            Ok(())
        })
    }

    pub(crate) fn release_frames(&mut self, count: usize) -> Result<(), ResourceError> {
        traced!("budget.release_frames", (count, self.frames), {
            self.frames = self
                .frames
                .checked_sub(count)
                .ok_or(ResourceError::Invariant)?;
            Ok(())
        })
    }

    /// The vector's existing capacity must already be charged to this ledger.
    /// T must have constant-time drop without recursively following child links.
    pub(crate) fn grow_vec<T>(
        &mut self,
        values: &mut Vec<T>,
        required: usize,
    ) -> Result<(), ResourceError> {
        if required <= values.capacity() {
            return Ok(());
        }
        let old = values.capacity();
        let capacity = old
            .checked_mul(2)
            .ok_or(ResourceError::Counter)?
            .max(required)
            .max(8);
        let new_bytes = capacity
            .checked_mul(size_of::<T>())
            .ok_or(ResourceError::Counter)?;
        let old_bytes = old
            .checked_mul(size_of::<T>())
            .ok_or(ResourceError::Counter)?;
        // Reallocation can copy the entire old requested layout. Charge once
        // before entering the allocator; the loop is bounded by this byte span.
        self.charge_work(
            u64::try_from(old_bytes)
                .map_err(|_| ResourceError::Counter)?
                .checked_add(1)
                .ok_or(ResourceError::Counter)?,
        )?;
        self.reserve(u64::try_from(new_bytes).map_err(|_| ResourceError::Counter)?)?;
        if values.try_reserve_exact(capacity - values.len()).is_err() {
            self.release(new_bytes as u64)?;
            return Err(ResourceError::Allocation);
        }
        // One physically successful semantic allocator request.
        // A later invariant failure does not undo that observed allocation.
        self.observe(Event::Allocations, 1);
        // Rust may expose allocator excess capacity. Such an allocator requires a
        // separate layout argument; do not continue with undercharged storage.
        if values.capacity() != capacity {
            return Err(ResourceError::Invariant);
        }
        self.release(old_bytes as u64)
    }
}

/// One ledger shared by ALL optional cache tables of one ordinary declaration.
/// This tracks requested capacity, including simultaneous old/new arrays, not
/// occupied entries or retained expression graphs. Semantic storage remains in
/// Budget. Never give each table a fresh ledger to multiply the session limit.
#[derive(Default)]
pub(crate) struct SessionCacheBudget {
    live: u64,
}
const _: () = assert!(size_of::<SessionCacheBudget>() == 8);
impl SessionCacheBudget {
    pub(crate) fn reserve(&mut self, bytes: u64) -> Result<bool, ResourceError> {
        traced!("cache.reserve", (bytes, self.live), {
            let next = self.live.checked_add(bytes).ok_or(ResourceError::Counter)?;
            if next > profile::CACHE_BYTES_PER_SESSION {
                return Ok(false);
            }
            self.live = next;
            Ok(true)
        })
    }
    pub(crate) fn release(&mut self, bytes: u64) -> Result<(), ResourceError> {
        traced!("cache.release", (bytes, self.live), {
            self.live = self
                .live
                .checked_sub(bytes)
                .ok_or(ResourceError::Invariant)?;
            Ok(())
        })
    }
}

/// Closed event slots. These observations never authorize semantic work.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub(crate) enum Event {
    DeclarationsInstalled,
    Inferences,
    ConversionSteps,
    Reductions,
    Allocations,
    TableLookups,
    EnvironmentLookups,
    MachineSteps,
    NormalizationCacheProbes,
    NormalizationCacheHits,
    NormalizationCacheInsertions,
}
#[cfg(feature = "introspection")]
impl Event {
    pub(crate) const ALL: [Self; 11] = [
        Self::DeclarationsInstalled,
        Self::Inferences,
        Self::ConversionSteps,
        Self::Reductions,
        Self::Allocations,
        Self::TableLookups,
        Self::EnvironmentLookups,
        Self::MachineSteps,
        Self::NormalizationCacheProbes,
        Self::NormalizationCacheHits,
        Self::NormalizationCacheInsertions,
    ];
    pub(crate) fn wire_name(self) -> &'static str {
        match self {
            Self::DeclarationsInstalled => "declarations_installed",
            Self::Inferences => "inferences",
            Self::ConversionSteps => "conversion_steps",
            Self::Reductions => "reductions",
            Self::Allocations => "allocations",
            Self::TableLookups => "table_lookups",
            Self::EnvironmentLookups => "environment_lookups",
            Self::MachineSteps => "machine_steps",
            Self::NormalizationCacheProbes => "normalization_cache_probes",
            Self::NormalizationCacheHits => "normalization_cache_hits",
            Self::NormalizationCacheInsertions => "normalization_cache_insertions",
        }
    }
}

/// Auxiliary accounting has no reference to the semantic ledger. No caller may
/// branch a semantic operation on auxiliary availability. It only selects detail.
#[derive(Default)]
#[cfg_attr(
    not(feature = "introspection"),
    allow(
        dead_code,
        reason = "No production instrumentation; component tests retain the empty diagnostics type"
    )
)]
pub(crate) struct Diagnostics {
    #[cfg(feature = "introspection")]
    state: Auxiliary,
}

#[cfg(feature = "introspection")]
#[derive(Default)]
struct Auxiliary {
    live: u64,
    work: u64,
    events: [u64; 11],
    unavailable: bool,
}

impl Diagnostics {
    /// Optional copying/rendering work is never charged to semantic fuel.
    /// Exhaustion is sticky for the whole input, including later bucket changes.
    #[cfg(feature = "introspection")]
    pub(crate) fn charge_work(&mut self, units: u64) -> bool {
        if self.state.unavailable {
            return false;
        }
        match self.state.work.checked_add(units) {
            Some(next) if next <= profile::DETAIL_WORK => {
                self.state.work = next;
                true
            }
            _ => {
                self.state.unavailable = true;
                false
            }
        }
    }

    /// Diagnostic vectors have flat destruction and already-charged capacity.
    /// The caller must discard retained detail after false, never stop checking.
    /// No semantic allocation helper, syntax store or event is touched here.
    #[cfg(feature = "introspection")]
    pub(crate) fn grow_vec<T>(&mut self, values: &mut Vec<T>, required: usize) -> bool {
        if self.state.unavailable {
            return false;
        }
        if required <= values.capacity() {
            return true;
        }
        let old = values.capacity();
        let sizes = old
            .checked_mul(2)
            .map(|n| n.max(required).max(8))
            .and_then(|capacity| {
                Some((
                    capacity,
                    u64::try_from(old.checked_mul(size_of::<T>())?).ok()?,
                    u64::try_from(capacity.checked_mul(size_of::<T>())?).ok()?,
                ))
            });
        let Some((capacity, old_bytes, new_bytes)) = sizes else {
            self.allocation_failed();
            return false;
        };
        let Some(work) = old_bytes.checked_add(1) else {
            self.allocation_failed();
            return false;
        };
        if !self.charge_work(work) || !self.reserve(new_bytes) {
            return false;
        }
        let allocation = { values.try_reserve_exact(capacity - values.len()) };
        if allocation.is_err() {
            self.release(new_bytes);
            self.allocation_failed();
            return false;
        }
        if values.capacity() != capacity {
            // An unsupported allocator layout disables detail; its owner drops
            // the vector. Never publish a snapshot with undercharged storage.
            self.allocation_failed();
            return false;
        }
        self.release(old_bytes);
        !self.state.unavailable
    }

    #[inline]
    #[cfg_attr(
        not(feature = "introspection"),
        allow(
            dead_code,
            reason = "No production instrumentation; component tests retain the empty diagnostics type"
        )
    )]
    pub(crate) fn event(&mut self, event: Event, count: u64) {
        #[cfg(feature = "introspection")]
        if !self.state.unavailable {
            if let Some(next) = self.state.events[event as usize].checked_add(count) {
                self.state.events[event as usize] = next;
            } else {
                self.state.unavailable = true;
            }
        }
        #[cfg(not(feature = "introspection"))]
        let _ = (event, count);
    }

    /// No partial counter snapshot may be emitted after any auxiliary failure.
    /// This owner represents one active bucket; the future row owner must carry
    /// availability across the whole input and account for every retained row.
    #[cfg(feature = "introspection")]
    pub(crate) fn events(&self) -> Option<&[u64; 11]> {
        (!self.state.unavailable).then_some(&self.state.events)
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn reserve(&mut self, bytes: u64) -> bool {
        if self.state.unavailable {
            return false;
        }
        match self.state.live.checked_add(bytes) {
            Some(next) if next <= profile::DIAGNOSTIC_LIVE_BYTES => {
                self.state.live = next;
                true
            }
            _ => {
                self.state.unavailable = true;
                false
            }
        }
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn release(&mut self, bytes: u64) {
        match self.state.live.checked_sub(bytes) {
            Some(next) => self.state.live = next,
            None => self.state.unavailable = true,
        }
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn allocation_failed(&mut self) {
        self.state.unavailable = true;
    }
}
