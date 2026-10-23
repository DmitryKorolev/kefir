//! Immutable level syntax and elementary observations.
//!
//! These are construction primitives, not a universe judgment or a scope check.
//! Raw input construction never simplifies or interns a level. The eventual
//! decoder must publish its identifier mapping only after `append` succeeds.
use crate::resource::{Budget, ResourceError, STRUCTURE_DEPTH};

mod helpers;
pub(crate) use helpers::UniverseComparison;
pub(crate) use helpers::substitution::expressions::Instance;
pub(crate) use helpers::substitution::scope::ScopeError;
pub(crate) use helpers::{SharedMemo, SharedTable};

/// Valid only in the originating run's level table. A numeric bounds check
/// cannot distinguish foreign handles: callers must never mix run/table origins.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct LevelId(u32);

impl LevelId {
    pub(crate) const ZERO: Self = Self(0);

    pub(crate) fn slot(self) -> u32 {
        self.0
    }
}

/// Valid only in the originating run's name table, paired with its level table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct NameId(pub(crate) u32);

/// Supplied by the name table, never by serialized derived metadata.
pub(crate) struct NameSummary {
    pub canonical: u32,
    pub depth: u32,
}

/// Internal integration boundary with the validated name table.
/// Invariant: canonical ids are injective on exact structured names, including
/// component kinds and embedded NUL; name handles themselves need not be unique
/// representatives. Failure to resolve a handle is an invariant error, not an
/// unequal parameter. This interface confers no declaration-scope permission.
pub(crate) trait LevelNames {
    /// Raw implementation hook: semantic callers use summary, not this hook.
    fn raw_summary(&self, name: NameId) -> Result<NameSummary, ResourceError>;
    #[inline]
    fn summary(&self, name: NameId, budget: &mut Budget) -> Result<NameSummary, ResourceError> {
        budget.observe(crate::resource::Event::TableLookups, 1);
        self.raw_summary(name)
    }
}

/// The exact structured-name order, implemented by the name table.
/// It must propagate failure, never substitute handle/canonical-id ordering.
#[allow(
    dead_code,
    reason = "Universe structural ordering is not yet used by semantic conversion"
)]
pub(crate) trait OrderedLevelNames: LevelNames {
    fn compare_names(
        &self,
        a: NameId,
        b: NameId,
        budget: &mut Budget,
    ) -> Result<std::cmp::Ordering, ResourceError>;
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u32)]
pub(crate) enum LevelKind {
    Zero,
    Succ(LevelId),
    Max(LevelId, LevelId),
    IMax(LevelId, LevelId),
    Param(NameId),
}

const HAS_PARAM: u32 = 1;
const POSITIVE: u32 = 2;
const ZERO: u32 = 4;

/// The total identically-zero decision, named in the type
/// : `Zero` means zero under every assignment, `NonZero` means not
/// identically zero. A `NonZero` outcome is a completed negative decision; it
/// never implies anything about positivity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LevelZero {
    Zero,
    NonZero,
}

/// The one-sided positivity probe, named in the type:
/// `Proven` means positive under every assignment; `NotProven` carries no
/// negative conclusion and never supports one.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LevelPositive {
    Proven,
    NotProven,
}

#[derive(Clone, Copy)]
pub(crate) struct Level {
    kind: LevelKind,
    hash: u32,
    depth: u32,
    flags: u32,
}

const _: () = assert!(std::mem::size_of::<LevelKind>() == 12);
const _: () = assert!(std::mem::size_of::<Level>() == 24);

impl Level {
    /// Collision-prone structural filter; never evidence of equality by itself.
    pub(crate) fn structural_hash(self) -> u32 {
        self.hash
    }

    pub(crate) fn kind(self) -> LevelKind {
        self.kind
    }

    pub(crate) fn depth(self) -> u32 {
        self.depth
    }

    pub(crate) fn has_param(self) -> bool {
        self.flags & HAS_PARAM != 0
    }

    /// The one-sided positivity probe: `Proven` means positive under
    /// every assignment; `NotProven` proves no converse.
    pub(crate) fn positive(self) -> LevelPositive {
        if self.flags & POSITIVE != 0 {
            LevelPositive::Proven
        } else {
            LevelPositive::NotProven
        }
    }

    /// The total identically-zero decision, not structural zero.
    pub(crate) fn zero(self) -> LevelZero {
        if self.flags & ZERO != 0 {
            LevelZero::Zero
        } else {
            LevelZero::NonZero
        }
    }
}

/// Whole-input flat syntax storage. Child handles precede the node that owns
/// them, so traversal and drop never follow Rust ownership recursively. Keep
/// this store with its ledger; dropping it retires that ledger too. Declaration
/// watermark compaction remains a separate integration obligation.
pub(crate) struct Levels {
    nodes: Vec<Level>,
}

impl Levels {
    /// Optional read-only inspection; unlike semantic accessors this is uncharged.
    #[cfg(feature = "introspection")]
    pub(crate) fn diagnostic_kind(&self, id: LevelId) -> Result<LevelKind, ResourceError> {
        self.raw_get(id).map(Level::kind)
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn diagnostic_resolve_slot(&self, slot: u32) -> Result<LevelId, ResourceError> {
        self.raw_resolve_slot(slot)
    }

    pub(crate) fn new(budget: &mut Budget) -> Result<Self, ResourceError> {
        budget.charge_work(1)?;
        let mut nodes = Vec::new();
        budget.grow_vec(&mut nodes, 1)?;
        nodes.push(Level {
            kind: LevelKind::Zero,
            hash: mix(0, 0, 0),
            depth: 0,
            flags: ZERO,
        });
        Ok(Self { nodes })
    }

    pub(crate) fn len(&self) -> usize {
        self.nodes.len()
    }

    /// No-retained-root rollback: `end` was captured from this store before
    /// generation. All generated references (including expression references)
    /// must already be retired. Decoded IDs and retained roots lie below `end`.
    /// Caller must enforce that invariant before any slot can be reused.
    /// Flat Copy nodes need no destructor work; capacity remains charged.
    pub(crate) fn discard_since(
        &mut self,
        end: usize,
        budget: &mut Budget,
    ) -> Result<(), ResourceError> {
        budget.charge_work(2)?;
        if end == 0 || end > self.nodes.len() {
            return Err(ResourceError::Invariant);
        }
        self.nodes.truncate(end);
        Ok(())
    }

    /// Only resolves an already completed slot. It does not resolve serialized
    /// ids or validate scope. In particular a future slot is never fabricated.
    pub(crate) fn resolve_slot(
        &self,
        slot: u32,
        budget: &mut Budget,
    ) -> Result<LevelId, ResourceError> {
        budget.observe(crate::resource::Event::TableLookups, 1);
        self.raw_resolve_slot(slot)
    }
    #[cfg(debug_assertions)]
    pub(crate) fn debug_resolve_slot(&self, slot: u32) -> Result<LevelId, ResourceError> {
        self.raw_resolve_slot(slot)
    }
    fn raw_resolve_slot(&self, slot: u32) -> Result<LevelId, ResourceError> {
        self.nodes
            .get(slot as usize)
            .map(|_| LevelId(slot))
            .ok_or(ResourceError::Invariant)
    }

    pub(crate) fn get(&self, id: LevelId, budget: &mut Budget) -> Result<Level, ResourceError> {
        budget.observe(crate::resource::Event::TableLookups, 1);
        self.raw_get(id)
    }

    /// Unobserved implementation hook; semantic callers must use get.
    // Internal snapshot. The caller coarsely charges copied rows and
    // charges the owned copy while both buffers coexist. These immutable rows
    // came from this store's completed append operations, never from input.
    pub(crate) fn retained_nodes_since(&self, base: usize) -> Result<&[Level], ResourceError> {
        if base == 0 {
            return Err(ResourceError::Invariant);
        }
        self.nodes.get(base..).ok_or(ResourceError::Invariant)
    }

    /// Internal bulk replay, never a constructor for input metadata.
    /// Construction invariant: rows were copied from this exact run/store's
    /// suffix at `base`, the original prefix and name origin are unchanged, and
    /// every row/child keeps its exact numeric slot. The retained owner must
    /// check its source frontier before calling. Thus all hash/depth/flag
    /// summaries remain the ones derived by append; no revalidation is needed.
    /// Caller charges row-copy work once, before this fallible mutation.
    pub(crate) fn restore_retained_nodes(
        &mut self,
        base: usize,
        rows: &[Level],
        budget: &mut Budget,
    ) -> Result<(), ResourceError> {
        budget.charge_work(1)?;
        if base == 0 || self.nodes.len() != base {
            return Err(ResourceError::Invariant);
        }
        let end = base.checked_add(rows.len()).ok_or(ResourceError::Counter)?;
        if end != 0 && u32::try_from(end - 1).is_err() {
            return Err(ResourceError::Storage);
        }
        budget.grow_vec(&mut self.nodes, end)?;
        self.nodes.extend_from_slice(rows);
        Ok(())
    }
    fn raw_get(&self, id: LevelId) -> Result<Level, ResourceError> {
        self.nodes
            .get(id.0 as usize)
            .copied()
            .ok_or(ResourceError::Invariant)
    }

    /// Fixed work per child, one coarse charge per construction. The caller
    /// resolves every name through the real name table; input data cannot supply
    /// a canonical id, hash, depth, or flag. Failure appends no node. Successful
    /// nonzero construction always allocates a new identity, even for equal data.
    /// Invariant: every call uses the same ledger and name-table origin as this
    /// run's previous construction. Existing names/summaries are immutable and
    /// canonical ids are stable. Existing child handles originate in this table.
    pub(crate) fn append(
        &mut self,
        kind: LevelKind,
        names: &impl LevelNames,
        budget: &mut Budget,
    ) -> Result<LevelId, ResourceError> {
        budget.charge_work(1)?;
        let (hash, child_depth, flags) = match kind {
            LevelKind::Zero => return Ok(LevelId::ZERO),
            LevelKind::Param(name) => {
                let name = names.summary(name, budget)?;
                (mix(4, name.canonical, 0), name.depth, HAS_PARAM)
            }
            LevelKind::Succ(a) => {
                let a = self.get(a, budget)?;
                (mix(1, a.hash, 0), a.depth, (a.flags & HAS_PARAM) | POSITIVE)
            }
            LevelKind::Max(a, b) | LevelKind::IMax(a, b) => {
                let (a, b) = (self.get(a, budget)?, self.get(b, budget)?);
                let is_max = matches!(kind, LevelKind::Max(..));
                // Flag-bit construction is the sole bool boundary of the
                // The cached POSITIVE/ZERO bits are
                // exactly what positive()/zero() later report.
                let positive = if is_max {
                    a.positive() == LevelPositive::Proven || b.positive() == LevelPositive::Proven
                } else {
                    b.positive() == LevelPositive::Proven
                };
                let zero = if is_max {
                    a.zero() == LevelZero::Zero && b.zero() == LevelZero::Zero
                } else {
                    b.zero() == LevelZero::Zero
                };
                (
                    mix(if is_max { 2 } else { 3 }, a.hash, b.hash),
                    a.depth.max(b.depth),
                    ((a.flags | b.flags) & HAS_PARAM)
                        | if positive { POSITIVE } else { 0 }
                        | if zero { ZERO } else { 0 },
                )
            }
        };
        let depth = child_depth.checked_add(1).ok_or(ResourceError::Counter)?;
        if crate::resource::traced!("levels.limit", (depth, STRUCTURE_DEPTH), {
            depth > STRUCTURE_DEPTH
        }) {
            return Err(ResourceError::StructureDepth);
        }
        let slot = crate::resource::traced!("levels.slot_limit", self.nodes.len(), {
            u32::try_from(self.nodes.len()).map_err(|_| ResourceError::Storage)
        })?;
        let required = self
            .nodes
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        budget.grow_vec(&mut self.nodes, required)?;
        self.nodes.push(Level {
            kind,
            hash,
            depth,
            flags,
        });
        Ok(LevelId(slot))
    }
}

/// A structural hash is a rejection filter only. Its exact bits carry no
/// semantic authority; collisions must reach a full constructor/name comparison.
fn mix(tag: u32, a: u32, b: u32) -> u32 {
    let x = tag.wrapping_add(0x9e37_79b9) ^ a.rotate_left(7) ^ b.rotate_left(19);
    x.wrapping_mul(0x85eb_ca6b) ^ (x >> 13)
}
