//! Declaration-local identity and membership, not type validation.
use crate::resource::{Budget, CONTEXT_DEPTH, ResourceError};
use crate::syntax::expressions::{BinderInfo, ExprId, Expressions};
use crate::syntax::levels::{LevelNames, NameId};
use std::mem::size_of;

/// Monotone within one declaration. Never mix context/declaration origins.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct FreeId(u32);
impl FreeId {
    pub(crate) fn slot(self) -> u32 {
        self.0
    }
}

/// Rule 2 scoped checkedness certificate for a binder type: the caller
/// established `ty` by a completed checking-mode judgement in the preceding
/// active context and universe scope. The wrapper
/// is handle-sized; construction is the named gateway, so raw `ExprId` no
/// longer reaches the context unchecked (tests use the raw test-only entry).
#[derive(Clone, Copy, Debug)]
pub(crate) struct CheckedTy(ExprId);
const _: () = assert!(size_of::<CheckedTy>() == size_of::<ExprId>());
impl CheckedTy {
    /// Trusted construction: minting
    /// requires the zero-sized authority token of the authorizing region.
    /// Token constructors are module-private, so out-of-region minting is a
    /// compile error; `scripts/check_checked_mint_sites.py` holds the
    /// exhaustive production mint list with stale-entry detection.
    pub(crate) fn checked(
        ty: ExprId,
        _authority: crate::check::environment::CheckednessMint,
    ) -> Self {
        Self(ty)
    }

    /// Decode-session authority: the enclosing checked syntax (
    /// `expose_checked`) carries the checkedness inside the
    /// ordinary-session inference machine region.
    pub(crate) fn checked_decode_session(
        ty: ExprId,
        _authority: crate::decode::primitive_decode::ordinary_session::CheckednessMint,
    ) -> Self {
        Self(ty)
    }

    pub(crate) fn expr(self) -> ExprId {
        self.0
    }
}

/// Rule 2 scoped checkedness certificate for a binder value; same contract as
/// `CheckedTy` for the optional `let`/binder value handle.
#[derive(Clone, Copy, Debug)]
pub(crate) struct CheckedVal(ExprId);
const _: () = assert!(size_of::<CheckedVal>() == size_of::<ExprId>());
impl CheckedVal {
    /// Trusted construction (same token contract as `CheckedTy`): the
    /// decode-session authority, used by the ordinary-session inference
    /// machine where the enclosing checked syntax carries the value's
    /// checkedness. The environment region mints binder
    /// types only; a future environment-side value mint is a deliberate new
    /// authority decision, not a reuse of this gateway.
    pub(crate) fn checked_decode_session(
        value: ExprId,
        _authority: crate::decode::primitive_decode::ordinary_session::CheckednessMint,
    ) -> Self {
        Self(value)
    }

    pub(crate) fn expr(self) -> ExprId {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(C)]
pub(crate) struct Local {
    ty: ExprId,
    value: ExprId,
    name: NameId,
    annotation: BinderInfo,
    has_value: bool,
    reserved: [u8; 2],
}
const _: () = assert!(size_of::<Local>() == 16);
impl Local {
    pub(crate) fn ty(self) -> ExprId {
        self.ty
    }
    pub(crate) fn value(self) -> Option<ExprId> {
        self.has_value.then_some(self.value)
    }
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn name(self) -> NameId {
        self.name
    }
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn annotation(self) -> BinderInfo {
        self.annotation
    }
}

/// Active and premark entries never mutate. Appended inactive records may have
/// payloads retired before syntax rollback; identities are never reactivated.
/// Invariant: active ids are in increasing order;
/// each active id has exactly one set bit and stack entry, all others have no bit.
/// The bitmap and stack confer membership, never a typing or conversion judgment.
/// Keep this store with its original budget and syntax origins. Retire it before
/// syntax watermark compaction; all free-variable syntax retires with the context.
/// A panic requires whole-run/ledger discard, not resumption of this context.
pub(crate) struct LocalContext {
    entries: Vec<Local>,
    active: Vec<FreeId>,
    bitmap: Vec<u64>,
    // Diagnostic availability only; no production field or per-record flag.
    #[cfg(feature = "introspection")]
    diagnostic_retired_from: usize,
}
impl LocalContext {
    /// Historical payloads remain available until a finite suffix may retire.
    /// IDs beyond that diagnostic watermark are omitted when inactive; later
    /// active rows remain valid. This conservative availability filter carries
    /// no checkedness, verdict or budget authority.
    #[cfg(feature = "introspection")]
    pub(crate) fn diagnostic_get(&self, id: u32) -> Option<(Local, bool)> {
        let local = self.entries.get(id as usize).copied()?;
        let active =
            self.bitmap.get(id as usize / 64).copied().unwrap_or(0) & (1u64 << (id % 64)) != 0;
        (active || (id as usize) < self.diagnostic_retired_from).then_some((local, active))
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn diagnostic_len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn new(b: &mut Budget) -> Result<Self, ResourceError> {
        // Fixed cleanup actions are prepaid so exhausted work cannot prevent drop.
        b.charge_work(3)?;
        Ok(Self {
            entries: Vec::new(),
            active: Vec::new(),
            bitmap: Vec::new(),
            #[cfg(feature = "introspection")]
            diagnostic_retired_from: usize::MAX,
        })
    }
    /// Exact active-stack identity within this context owner. IDs are never
    /// reused or reactivated, so an equal top implies the same immutable stack.
    /// Zero names empty; an exhausted sentinel range disables memo admission.
    pub(crate) fn cache_identity(&self) -> Option<u32> {
        self.active
            .last()
            .map_or(Some(0), |id| id.slot().checked_add(1))
    }

    pub(crate) fn depth(&self) -> usize {
        self.active.len()
    }

    pub(crate) fn entry_count(&self) -> usize {
        self.entries.len()
    }

    /// All child owners/caches have retired and the original active stack has
    /// been restored. The mark and inert payload predate candidate generation.
    /// Increasing active IDs prove this whole appended suffix inactive without
    /// a second per-entry validation pass. No ID or bitmap slot is recycled.
    pub(crate) fn retire_inactive_since(
        &mut self,
        mark: usize,
        depth: usize,
        inert: ExprId,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        if mark > self.entries.len()
            || self.depth() != depth
            || self
                .active
                .last()
                .is_some_and(|id| id.slot() as usize >= mark)
        {
            return Err(ResourceError::Invariant);
        }
        b.charge_work((self.entries.len() - mark) as u64 + 1)?;
        for local in &mut self.entries[mark..] {
            local.ty = inert;
            local.value = inert;
            local.name = NameId::ANONYMOUS;
            local.has_value = false;
        }
        #[cfg(feature = "introspection")]
        if mark < self.entries.len() {
            self.diagnostic_retired_from = self.diagnostic_retired_from.min(mark);
        }
        Ok(())
    }

    /// Production entry: binder types and, when present, values must present
    /// scoped checkedness certificates — (checked
    /// before the local context is extended; obligations travel with terms).
    /// This routine validates table references and absence of loose indices,
    /// not the certificates' semantic obligations.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn enter_checked(
        &mut self,
        ty: CheckedTy,
        value: Option<CheckedVal>,
        name: NameId,
        annotation: BinderInfo,
        expressions: &Expressions,
        names: &impl LevelNames,
        b: &mut Budget,
    ) -> Result<FreeId, ResourceError> {
        self.enter_impl(
            ty.expr(),
            value.map(CheckedVal::expr),
            name,
            annotation,
            expressions,
            names,
            b,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn enter_impl(
        &mut self,
        ty: ExprId,
        value: Option<ExprId>,
        name: NameId,
        annotation: BinderInfo,
        expressions: &Expressions,
        names: &impl LevelNames,
        b: &mut Budget,
    ) -> Result<FreeId, ResourceError> {
        b.charge_work(1)?;
        if crate::resource::traced!("local_context.limit", (self.active.len(), CONTEXT_DEPTH), {
            self.active.len() >= CONTEXT_DEPTH
        }) {
            return Err(ResourceError::ContextDepth);
        }
        names.summary(name, b)?;
        if expressions.get(ty, b)?.loose_range() != 0 {
            return Err(ResourceError::Invariant);
        }
        if let Some(value) = value
            && expressions.get(value, b)?.loose_range() != 0
        {
            return Err(ResourceError::Invariant);
        }
        let slot = crate::resource::traced!("local_context.slot_limit", self.entries.len(), {
            u32::try_from(self.entries.len()).map_err(|_| ResourceError::Storage)
        })?;
        let count = self
            .entries
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        let words = count.checked_add(63).ok_or(ResourceError::Counter)? / 64;
        let active_count = self
            .active
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        b.grow_vec(&mut self.entries, count)?;
        b.grow_vec(&mut self.active, active_count)?;
        b.grow_vec(&mut self.bitmap, words)?;
        // All fallible steps precede logical publication. At most one zero word
        // is appended; no scan proportional to the number of previous locals.
        if words > self.bitmap.len() {
            self.bitmap.push(0);
        }
        let id = FreeId(slot);
        self.entries.push(Local {
            ty,
            value: value.unwrap_or(ty),
            name,
            annotation,
            has_value: value.is_some(),
            reserved: [0; 2],
        });
        self.active.push(id);
        self.bitmap[slot as usize / 64] |= 1u64 << (slot % 64);
        Ok(id)
    }
    /// The expected top id prevents an abandoned/nested route from popping a
    /// caller's binder. A failed leave makes no membership change.
    pub(crate) fn leave(&mut self, expected: FreeId, b: &mut Budget) -> Result<(), ResourceError> {
        b.charge_work(1)?;
        if self.active.last().copied() != Some(expected) {
            return Err(ResourceError::Invariant);
        }
        let word = self
            .bitmap
            .get_mut(expected.0 as usize / 64)
            .ok_or(ResourceError::Invariant)?;
        let mask = 1u64 << (expected.0 % 64);
        if *word & mask == 0 {
            return Err(ResourceError::Invariant);
        }
        *word &= !mask;
        self.active.pop();
        Ok(())
    }
    /// Driver-owned checkpoint from an immediate child's entry. Every owner
    /// and cache above that child must retire before this call; no abandoned
    /// handle may subsequently escape. Identities are never recycled. Failure
    /// requires whole-declaration discard, even after a partial unwind.
    pub(crate) fn unwind_to(&mut self, depth: usize, b: &mut Budget) -> Result<(), ResourceError> {
        if depth > self.active.len() {
            return Err(ResourceError::Invariant);
        }
        while self.active.len() > depth {
            let local = *self.active.last().ok_or(ResourceError::Invariant)?;
            self.leave(local, b)?;
        }
        Ok(())
    }

    #[cfg(debug_assertions)]
    pub(crate) fn debug_is_active(&self, id: u32) -> bool {
        self.bitmap.get(id as usize / 64).copied().unwrap_or(0) & (1u64 << (id % 64)) != 0
    }
    /// Unavailable local identity is an internal scope failure, never evidence
    /// that two terms differ or that a proof is invalid.
    pub(crate) fn get(&self, id: u32, b: &mut Budget) -> Result<Local, ResourceError> {
        b.charge_work(1)?;
        let word = self.bitmap.get(id as usize / 64).copied().unwrap_or(0);
        if word & (1u64 << (id % 64)) == 0 {
            return Err(ResourceError::Invariant);
        }
        self.entries
            .get(id as usize)
            .copied()
            .ok_or(ResourceError::Invariant)
    }
    /// Release even with active binders after an interrupted declaration. The
    /// caller must discard every free-containing expression and context cache.
    pub(crate) fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let a = release(self.entries, b);
        let c = release(self.active, b);
        let d = release(self.bitmap, b);
        a.and(c).and(d)
    }
}
fn release<T: Copy>(values: Vec<T>, b: &mut Budget) -> Result<(), ResourceError> {
    let bytes = values
        .capacity()
        .checked_mul(size_of::<T>())
        .ok_or(ResourceError::Counter)?;
    drop(values);
    b.release(bytes as u64)
}
