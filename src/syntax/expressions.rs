//! Raw expression storage. This is syntax, never a typing judgment.
//! Metadata payloads are preserved as bounded raw bytes; their interpretation
//! is a separate semantic decision and every semantic path declines.
use crate::resource::{Budget, ResourceError, STRUCTURE_DEPTH};
use crate::syntax::levels::{LevelId, LevelNames, Levels, NameId};

pub(crate) mod binding;

pub(crate) mod reduction;

/// A handle is meaningful only in its originating expression table and ledger.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ExprId(u32);
impl ExprId {
    /// Restore a slot previously captured from an original ExprId by private
    /// environment storage. The owner must preserve that table and frontier;
    /// this is never a decoder for an input integer or a checkedness witness.
    pub(crate) fn from_stored_original(slot: u32) -> Self {
        Self(slot)
    }
    pub(crate) fn slot(self) -> u32 {
        self.0
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn diagnostic_from_slot(slot: u32) -> Self {
        Self(slot)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub(crate) enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstanceImplicit,
}

/// Construction input, not a serialized format. Borrowed payloads are copied
/// into owned stores before publication. An MData wrapper preserves its exact
/// borrowed payload bytes (a validated JSON object) and its wrapped
/// expression; no semantic path interprets the payload.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ExprKind<'a> {
    Bound(u32),
    Free(u32),
    Sort(LevelId),
    App(ExprId, ExprId),
    Lambda(NameId, ExprId, ExprId, BinderInfo),
    Pi(NameId, ExprId, ExprId, BinderInfo),
    Constant(NameId, &'a [LevelId]),
    Let(NameId, ExprId, ExprId, ExprId, bool),
    Projection(NameId, u32, ExprId),
    Natural(&'a [u8]),
    String(&'a [u8]),
    MData(&'a [u8], ExprId),
}

const FREE: u32 = 1;
const PARAM: u32 = 2;
/// Marking a node as containing metadata. Like FREE/PARAM it propagates from
/// children; value 4 is reserved for the debug free-scope mark.
const META: u32 = 8;

#[derive(Clone, Copy)]
#[repr(C)]
struct Descriptor {
    // Construction invariant: tag < 16, binder < 4, flags < 16 and depth
    // fits the unchanged STRUCTURE_DEPTH limit. Every publication uses new;
    // only the debug-scope MARK bit may later change. No operand is narrowed.
    header: u32,
    fields: [u32; 3],
}
// Logical tags use bits 0..3. The stored representation uses bits 4..7
// privately, so every view dispatch masks the logical tag.
const TAG_MASK: u32 = 15;
const BINDER_SHIFT: u32 = 8;
const FLAGS_SHIFT: u32 = 10;
const FLAGS_MASK: u32 = 15;
const DEPTH_SHIFT: u32 = 14;
const DEPTH_MASK: u32 = u32::MAX >> DEPTH_SHIFT;
const _: () = assert!(STRUCTURE_DEPTH <= DEPTH_MASK);
const _: () = assert!(FREE <= FLAGS_MASK && PARAM <= FLAGS_MASK && META <= FLAGS_MASK);
const _: () = assert!(4 <= FLAGS_MASK); // Existing debug-scope mark.

impl Descriptor {
    fn new(tag: u8, binder: BinderInfo, depth: u32, flags: u32, fields: [u32; 3]) -> Self {
        debug_assert!(u32::from(tag) <= TAG_MASK);
        debug_assert!(flags <= FLAGS_MASK);
        debug_assert!(depth <= STRUCTURE_DEPTH);
        Self {
            header: u32::from(tag)
                | ((binder as u32) << BINDER_SHIFT)
                | (flags << FLAGS_SHIFT)
                | (depth << DEPTH_SHIFT),
            fields,
        }
    }
}

#[derive(Clone, Copy)]
#[repr(C)]
struct RawExpression {
    descriptor: Descriptor,
    // Construction invariant: identity under compare_structure's Identity level
    // rule implies equal fingerprints (a Let matches only a Let with equal nondep
    // flag, type, value and body). The Universe rule does not use fingerprints.
    // Pi/lambda and let labels are omitted; raw descriptors retain them. Neither a
    // match nor a mismatch establishes conversion equality or inequality.
    fingerprint: u32,
    loose: u32,
}

// Transient constructor arguments only; never retained with a node or handle.
// Child summaries and the existing checked depth increment precede these facts.
struct AppendFacts {
    tag: u8,
    binder: BinderInfo,
    depth: u32,
    flags: u32,
    fields: [u32; 3],
    loose: u32,
    hash_fields: [u32; 3],
}

// A view borrows a completed row in its originating store. Its loan prevents
// append/reallocation and suffix retirement while it remains in use. Consumers
// extract scalar/decoded results before mutation. Summary reads neither copy
// the row nor reconstruct operands; kind/full descriptor exposes exact words.
#[derive(Clone, Copy)]
#[repr(C)]
pub(crate) struct Expression<'a> {
    stored: &'a StoredExpression,
    id: ExprId,
}

// Private storage encoding, never an exposed descriptor. The unchanged depth
// bound leaves bit 31 free; bits 4..7 are also unused in the raw header. Tiny
// third operands live there (binder bodies use an exact short backward gap),
// otherwise they index a block-local escape array.
// Clearing STORED_BITS reconstructs every original descriptor bit exactly.
const STORED_ESCAPE: u32 = 1 << 31;
const STORED_ORDINAL_SHIFT: u32 = 4;
const STORED_ORDINAL_MASK: u32 = 15 << STORED_ORDINAL_SHIFT;
const STORED_BITS: u32 = STORED_ESCAPE | STORED_ORDINAL_MASK;
const OPERAND_BLOCK: usize = 16;
const _: () = assert!(STRUCTURE_DEPTH < (1 << 17));

#[derive(Clone, Copy)]
struct StoredExpression {
    header: u32,
    fields: [u32; 2],
    fingerprint: u32,
    loose: u32,
}
const _: () = assert!(std::mem::size_of::<StoredExpression>() == 20);

impl StoredExpression {
    fn depth(&self) -> u32 {
        (self.header & !STORED_ESCAPE) >> DEPTH_SHIFT
    }
    fn flags(&self) -> u32 {
        (self.header >> FLAGS_SHIFT) & FLAGS_MASK
    }
}

// A plan is minted before any fallible side-payload reservation. Its capacities
// and indices refer only to the current store/frontier. Until publish_node, no
// node, directory entry or escaped operand has been logically appended.
struct NodePlan {
    node: StoredExpression,
    block_base: Option<u32>,
    extra: Option<u32>,
}

const _: () = assert!(std::mem::size_of::<Descriptor>() == 16);
const _: () = assert!(std::mem::size_of::<Expression<'_>>() == 16);
const _: () = assert!(std::mem::size_of::<LevelId>() == 4);
const _: () = assert!(std::mem::size_of::<[u32; 5]>() == 20);

impl Expression<'_> {
    // Release fusion is a code-generation hint, never a semantic mode. Forcing
    // the decoder into recursive clients without optimization inflates their
    // stack frames; assertion/debug builds retain the identical Rust body
    // under the compiler's ordinary inlining policy. Charges/limits do not vary.
    fn tag(self) -> u8 {
        (self.stored.header & TAG_MASK) as u8
    }
    fn binder(self) -> BinderInfo {
        match (self.stored.header >> BINDER_SHIFT) & 3 {
            0 => BinderInfo::Default,
            1 => BinderInfo::Implicit,
            2 => BinderInfo::StrictImplicit,
            _ => BinderInfo::InstanceImplicit,
        }
    }
    // Construction contract: expressions is the originating store. The loan
    // protects row lifetime, but does not prove identity of this separate
    // argument; callers must never exchange stores or origin identities.
    #[cfg_attr(not(debug_assertions), inline(always))]
    fn third(self, expressions: &Expressions) -> Result<u32, ResourceError> {
        if matches!(self.tag(), 4 | 5) {
            return self.body(expressions);
        }
        let ordinal = (self.stored.header & STORED_ORDINAL_MASK) >> STORED_ORDINAL_SHIFT;
        if self.stored.header & STORED_ESCAPE == 0 {
            return Ok(ordinal);
        }
        self.escaped_third(expressions)
    }
    #[cfg_attr(not(debug_assertions), inline(always))]
    fn body(self, expressions: &Expressions) -> Result<u32, ResourceError> {
        if self.stored.header & STORED_ESCAPE != 0 {
            return self.escaped_third(expressions);
        }
        // Construction invariant: only Lambda/Pi readers call this method.
        // plan_node encodes a prior-slot gap 1..=16 as gap-1. Identity is the
        // immutable origin slot, so rollback/reappend cannot change this body.
        let gap = ((self.stored.header & STORED_ORDINAL_MASK) >> STORED_ORDINAL_SHIFT) + 1;
        // plan_node checked origin - body before publishing this encoding;
        // raw_get pairs the row with that same immutable origin. Retirement
        // cannot cross this loan, and reappend computes a new gap. Therefore
        // the subtraction cannot underflow for a completed inline binder.
        debug_assert!(self.id.0 >= gap);
        Ok(self.id.0.wrapping_sub(gap))
    }
    #[cfg_attr(not(debug_assertions), inline(always))]
    fn escaped_third(self, expressions: &Expressions) -> Result<u32, ResourceError> {
        let ordinal = (self.stored.header & STORED_ORDINAL_MASK) >> STORED_ORDINAL_SHIFT;
        let base = *expressions
            .extra_bases
            .get(self.id.0 as usize / OPERAND_BLOCK)
            .ok_or(ResourceError::Invariant)?;
        let index = base.checked_add(ordinal).ok_or(ResourceError::Invariant)?;
        expressions
            .extra_operands
            .get(index as usize)
            .copied()
            .ok_or(ResourceError::Invariant)
    }
    fn raw_descriptor(self, expressions: &Expressions) -> Result<Descriptor, ResourceError> {
        Ok(Descriptor {
            header: self.stored.header & !STORED_BITS,
            fields: [
                self.stored.fields[0],
                self.stored.fields[1],
                self.third(expressions)?,
            ],
        })
    }

    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn depth(self) -> u32 {
        self.stored.depth()
    }
    fn flags(self) -> u32 {
        self.stored.flags()
    }
    /// Necessary condition for structural identity, never semantic evidence.
    pub(crate) fn syntax_fingerprint(self) -> u32 {
        self.stored.fingerprint
    }
    pub(crate) fn loose_range(self) -> u32 {
        self.stored.loose
    }
    /// Equivalent to raw_kind's tag-zero arm, for this exact borrowed row.
    /// Reads no derived scope fact and creates no cache/checkedness authority.
    #[inline(always)]
    pub(crate) fn bound_index(self) -> Option<u32> {
        (self.tag() == 0).then_some(self.stored.fields[0])
    }
    pub(crate) fn has_free(self) -> bool {
        self.flags() & FREE != 0
    }
    pub(crate) fn has_param(self) -> bool {
        self.flags() & PARAM != 0
    }

    /// `expressions` must be the originating store; the row loan enforces
    /// lifetime but does not prove identity of this separate argument.
    #[cfg_attr(not(debug_assertions), inline(always))]
    pub(crate) fn kind<'a>(
        self,
        expressions: &'a Expressions,
        levels: &Levels,
        budget: &mut Budget,
    ) -> Result<ExprKind<'a>, ResourceError> {
        budget.observe(crate::resource::Event::TableLookups, 1);
        self.raw_kind(expressions, |slot| levels.resolve_slot(slot, budget))
    }
    #[cfg_attr(not(debug_assertions), inline(always))]
    fn raw_kind<'a>(
        self,
        expressions: &'a Expressions,
        resolve: impl FnOnce(u32) -> Result<LevelId, ResourceError>,
    ) -> Result<ExprKind<'a>, ResourceError> {
        let [a, b] = self.stored.fields;
        Ok(match self.tag() {
            0 => ExprKind::Bound(a),
            1 => ExprKind::Free(a),
            2 => ExprKind::Sort(resolve(a)?),
            3 => ExprKind::App(ExprId(a), ExprId(b)),
            4 => ExprKind::Lambda(
                NameId(a),
                ExprId(b),
                ExprId(self.body(expressions)?),
                self.binder(),
            ),
            5 => ExprKind::Pi(
                NameId(a),
                ExprId(b),
                ExprId(self.body(expressions)?),
                self.binder(),
            ),
            6 => ExprKind::Constant(
                NameId(a),
                span(&expressions.level_lists, b, self.third(expressions)?)?,
            ),
            7 => {
                let side = expressions
                    .lets
                    .get(a as usize)
                    .ok_or(ResourceError::Invariant)?;
                ExprKind::Let(
                    NameId(side[0]),
                    ExprId(side[1]),
                    ExprId(side[2]),
                    ExprId(side[3]),
                    side[4] != 0,
                )
            }
            8 => ExprKind::Projection(NameId(a), b, ExprId(self.third(expressions)?)),
            9 | 10 => {
                // Construction validates UTF-8/digits once. This borrowed byte
                // view needs no scan; consumers must charge any later traversal.
                let text = span(&expressions.bytes, a, b)?;
                if self.tag() == 9 {
                    ExprKind::Natural(text)
                } else {
                    ExprKind::String(text)
                }
            }
            // Descriptor layout for tag 11 is [wrapped, offset, count] —
            // the same order append and append_metadata_span write.
            11 => ExprKind::MData(
                span(&expressions.bytes, b, self.third(expressions)?)?,
                ExprId(a),
            ),
            _ => return Err(ResourceError::Invariant),
        })
    }
}

/// NumericRange is a support limit, not an invalid-proof verdict. Resource
/// errors retain their original category; reference errors are internal here.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ExpressionError {
    NumericRange,
    InvalidNatural,
    InvalidString,
    Resource(ResourceError),
}
impl From<ResourceError> for ExpressionError {
    fn from(value: ResourceError) -> Self {
        Self::Resource(value)
    }
}

/// Invariant: all operations use the same immutable name/level origins and budget.
/// Completed child handles precede their parents. Free ids are merely stored here;
/// the caller must establish local-context membership before semantic use.
/// Retiring this store retires its ledger. Generated-node watermark retention is
/// a separate integration obligation, not permission to retain declaration junk.
#[derive(Default)]
pub(crate) struct Expressions {
    nodes: Vec<StoredExpression>,
    // Structural index, not a judgment cache: scope is this originating store.
    // One base per 16 nodes; each escaped node stores its exact local ordinal.
    // Append publishes all three owners together, and suffix rollback retires
    // them together. No identity, binder/context/declaration authority is added.
    extra_bases: Vec<u32>,
    extra_operands: Vec<u32>,
    level_lists: Vec<LevelId>,
    lets: Vec<[u32; 5]>,
    bytes: Vec<u8>,
}

/// O(1) declaration-entry snapshot of node/escape and side-payload frontiers.
/// Never exchange between stores or reuse after discarding below its frontier.
#[derive(Clone, Copy)]
pub(crate) struct Watermark {
    nodes: usize,
    extra_operands: usize,
    level_lists: usize,
    lets: usize,
    bytes: usize,
}

impl Expressions {
    /// Optional diagnostics inspect immutable validated storage without touching
    /// semantic lookup events or fuel. This grants no scope or checking fact.
    #[cfg(feature = "introspection")]
    pub(crate) fn diagnostic_kind<'a>(
        &'a self,
        id: ExprId,
        levels: &Levels,
    ) -> Result<ExprKind<'a>, ResourceError> {
        self.raw_get(id)?
            .raw_kind(self, |slot| levels.diagnostic_resolve_slot(slot))
    }

    /// Debug-only scope assertion scratch. Flag value 4 is otherwise zero by every node
    /// constructor. Exclusive access forbids semantic operations while marked.
    /// Children strictly precede parents, so a reverse scan visits each reachable
    /// node once and clears all marks even when membership fails. The lowest
    /// discovered free-bearing slot bounds pending marks; the prefix below it
    /// cannot contain an unvisited mark. No allocation,
    /// recursion, semantic charge or extra retained field is introduced. A panic
    /// in the caller-supplied membership check requires whole-run discard.
    #[cfg(debug_assertions)]
    pub(crate) fn debug_free_scope(
        &mut self,
        root: ExprId,
        levels: &Levels,
        active: impl Fn(u32) -> bool,
    ) -> Result<bool, ResourceError> {
        const MARK: u32 = 4;
        if !self.raw_get(root)?.has_free() {
            return Ok(true);
        }
        self.nodes[root.0 as usize].header |= MARK << FLAGS_SHIFT;
        let mut valid = true;
        let mut floor = root.0 as usize;
        for index in (0..=root.0 as usize).rev() {
            if index < floor {
                break;
            }
            if (self.nodes[index].header >> FLAGS_SHIFT) & MARK == 0 {
                continue;
            }
            self.nodes[index].header &= !(MARK << FLAGS_SHIFT);
            let children = match self
                .raw_get(ExprId(index as u32))?
                .raw_kind(self, |slot| levels.debug_resolve_slot(slot))?
            {
                ExprKind::Free(id) => {
                    valid &= active(id);
                    [None; 3]
                }
                ExprKind::App(a, b) | ExprKind::Lambda(_, a, b, _) | ExprKind::Pi(_, a, b, _) => {
                    [Some(a), Some(b), None]
                }
                ExprKind::Let(_, ty, value, body, _) => [Some(ty), Some(value), Some(body)],
                ExprKind::Projection(_, _, child) => [Some(child), None, None],
                ExprKind::MData(_, child) => [Some(child), None, None],
                _ => [None; 3],
            };
            for child in children.into_iter().flatten() {
                if child.0 as usize >= index {
                    return Err(ResourceError::Invariant);
                }
                if self.raw_get(child)?.has_free() {
                    self.nodes[child.0 as usize].header |= MARK << FLAGS_SHIFT;
                    floor = floor.min(child.0 as usize);
                }
            }
        }
        Ok(valid)
    }
    pub(crate) fn len(&self) -> usize {
        self.nodes.len()
    }
    /// Reserve the complete private String expansion before appending.
    /// Failure can retain charged capacity but never changes logical lengths.
    pub(crate) fn reserve_string_expansion(
        &mut self,
        scalars: usize,
        budget: &mut Budget,
    ) -> Result<(), ResourceError> {
        let nodes = scalars
            .checked_mul(4)
            .and_then(|n| n.checked_add(8))
            .and_then(|n| self.nodes.len().checked_add(n))
            .ok_or(ResourceError::Counter)?;
        let levels = self
            .level_lists
            .len()
            .checked_add(2)
            .ok_or(ResourceError::Counter)?;
        let bytes = scalars
            .checked_mul(7)
            .and_then(|n| self.bytes.len().checked_add(n))
            .ok_or(ResourceError::Counter)?;
        // Ensure the compact side spans and node handles can represent the plan.
        u32::try_from(nodes).map_err(|_| ResourceError::Storage)?;
        u32::try_from(levels).map_err(|_| ResourceError::Storage)?;
        u32::try_from(bytes).map_err(|_| ResourceError::Storage)?;
        budget.grow_vec(&mut self.nodes, nodes)?;
        // The String expansion caller publishes only constants with 0/1
        // universe arguments, applications and natural literals: every third
        // descriptor word fits inline. Its complete reservation therefore needs
        // directory capacity, but no escaped-operand capacity.
        budget.grow_vec(&mut self.extra_bases, nodes.div_ceil(OPERAND_BLOCK))?;
        budget.grow_vec(&mut self.level_lists, levels)?;
        budget.grow_vec(&mut self.bytes, bytes)?;
        Ok(())
    }
    pub(crate) fn watermark(&self) -> Watermark {
        Watermark {
            nodes: self.nodes.len(),
            extra_operands: self.extra_operands.len(),
            level_lists: self.level_lists.len(),
            lets: self.lets.len(),
            bytes: self.bytes.len(),
        }
    }

    /// Discard only when NO generated root survives. The caller has retired
    /// locals, frames, caches, memos and candidate environment references first.
    /// `mark` belongs to this store and this generation interval. Private fields
    /// prevent fabricated combinations of node and side-store lengths, but
    /// origin/lifetime validity remains the caller's construction invariant.
    /// All retained nodes and decoded IDs predate `mark`, so truncation cannot
    /// invalidate their side spans or children. Nodes/lists/bytes have no Drop
    /// work; this is six constant-time truncations without freeing capacity.
    /// Failure changes no lengths and must propagate, never publish a verdict.
    pub(crate) fn discard_since(
        &mut self,
        mark: Watermark,
        budget: &mut Budget,
    ) -> Result<(), ResourceError> {
        budget.charge_work(7)?;
        if mark.nodes > self.nodes.len()
            || mark.extra_operands > self.extra_operands.len()
            || mark.level_lists > self.level_lists.len()
            || mark.lets > self.lets.len()
            || mark.bytes > self.bytes.len()
        {
            return Err(ResourceError::Invariant);
        }
        self.nodes.truncate(mark.nodes);
        self.extra_bases
            .truncate(mark.nodes.div_ceil(OPERAND_BLOCK));
        self.extra_operands.truncate(mark.extra_operands);
        self.level_lists.truncate(mark.level_lists);
        self.lets.truncate(mark.lets);
        self.bytes.truncate(mark.bytes);
        Ok(())
    }
    pub(crate) fn resolve_slot(
        &self,
        slot: u32,
        budget: &mut Budget,
    ) -> Result<ExprId, ResourceError> {
        budget.observe(crate::resource::Event::TableLookups, 1);
        self.raw_resolve_slot(slot)
    }
    fn raw_resolve_slot(&self, slot: u32) -> Result<ExprId, ResourceError> {
        self.nodes
            .get(slot as usize)
            .map(|_| ExprId(slot))
            .ok_or(ResourceError::Invariant)
    }
    pub(crate) fn get(
        &self,
        id: ExprId,
        budget: &mut Budget,
    ) -> Result<Expression<'_>, ResourceError> {
        budget.observe(crate::resource::Event::TableLookups, 1);
        self.raw_get(id)
    }
    fn raw_get(&self, id: ExprId) -> Result<Expression<'_>, ResourceError> {
        Ok(Expression {
            stored: self
                .nodes
                .get(id.0 as usize)
                .ok_or(ResourceError::Invariant)?,
            id,
        })
    }

    // Construction needs only child summaries. Do not fetch an escaped operand
    // just to read depth/flags/hash/loose. This is the same one lookup event as
    // get, with no cache or changed semantic charge.
    fn summary(&self, id: ExprId, budget: &mut Budget) -> Result<StoredExpression, ResourceError> {
        budget.observe(crate::resource::Event::TableLookups, 1);
        self.raw_summary(id)
    }

    fn raw_summary(&self, id: ExprId) -> Result<StoredExpression, ResourceError> {
        self.nodes
            .get(id.0 as usize)
            .copied()
            .ok_or(ResourceError::Invariant)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn plan_node(
        &mut self,
        expression: RawExpression,
        budget: &mut Budget,
    ) -> Result<NodePlan, ResourceError> {
        // Only completed raw descriptors enter here; their actual bounded
        // depth and reserved low bits cannot overlap the private encoding.
        debug_assert_eq!(expression.descriptor.header & STORED_BITS, 0);
        let required = self
            .nodes
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        let third = expression.descriptor.fields[2];
        let first = self.nodes.len().is_multiple_of(OPERAND_BLOCK);
        let inline = if matches!(expression.descriptor.header & TAG_MASK, 4 | 5) {
            u32::try_from(self.nodes.len())
                .map_err(|_| ResourceError::Storage)?
                .checked_sub(third)
                .filter(|gap| (1..=16).contains(gap))
                .map(|gap| gap - 1)
        } else {
            (third <= 15).then_some(third)
        };
        let escape = inline.is_none();
        let frontier = if first || escape {
            u32::try_from(self.extra_operands.len()).map_err(|_| ResourceError::Storage)?
        } else {
            0
        };
        let base = if first {
            frontier
        } else if escape {
            *self.extra_bases.last().ok_or(ResourceError::Invariant)?
        } else {
            0
        };
        let ordinal = if escape {
            let ordinal = frontier.checked_sub(base).ok_or(ResourceError::Invariant)?;
            if ordinal > 15 {
                return Err(ResourceError::Invariant);
            }
            ordinal
        } else {
            inline.ok_or(ResourceError::Invariant)?
        };
        let header = expression.descriptor.header
            | (ordinal << STORED_ORDINAL_SHIFT)
            | if escape { STORED_ESCAPE } else { 0 };
        // The budget helper has no charges/events when capacity suffices.
        // Keep that predicate at the caller to avoid its growth-path frame on
        // ordinary appends; every actual growth still uses the same helper.
        if required > self.nodes.capacity() {
            budget.grow_vec(&mut self.nodes, required)?;
        }
        if first {
            budget.grow_vec(&mut self.extra_bases, required.div_ceil(OPERAND_BLOCK))?;
        }
        if escape {
            let required = self
                .extra_operands
                .len()
                .checked_add(1)
                .ok_or(ResourceError::Counter)?;
            budget.grow_vec(&mut self.extra_operands, required)?;
        }
        Ok(NodePlan {
            node: StoredExpression {
                header,
                fields: [
                    expression.descriptor.fields[0],
                    expression.descriptor.fields[1],
                ],
                fingerprint: expression.fingerprint,
                loose: expression.loose,
            },
            block_base: first.then_some(base),
            extra: escape.then_some(third),
        })
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn publish_node(&mut self, plan: NodePlan) {
        // Construction invariant: plan_node reserved every owner, and only
        // unrelated side-payload publication can intervene. These pushes cannot
        // allocate or fail; no partially published node can be observed.
        if let Some(base) = plan.block_base {
            self.extra_bases.push(base);
        }
        if let Some(extra) = plan.extra {
            self.extra_operands.push(extra);
        }
        self.nodes.push(plan.node);
    }

    /// No simplification or interning; every successful append has a fresh id.
    /// Derive summaries from actual completed children before publishing the node.
    /// Loose range is max(domain range, body range minus one) at a binder:
    /// the binder does not bind its own domain. Names affect depth/hash, not scope.
    pub(crate) fn append(
        &mut self,
        kind: ExprKind<'_>,
        levels: &Levels,
        names: &impl LevelNames,
        budget: &mut Budget,
    ) -> Result<ExprId, ExpressionError> {
        budget.charge_work(1)?;
        match kind {
            ExprKind::App(a, b) => self.append_app(a, b, budget),
            _ => self.append_general(kind, levels, names, budget),
        }
    }

    /// Same charged construction as append(App); handles carry no checkedness.
    #[cfg_attr(not(debug_assertions), inline(always))]
    pub(crate) fn append_application(
        &mut self,
        function: ExprId,
        argument: ExprId,
        budget: &mut Budget,
    ) -> Result<ExprId, ExpressionError> {
        budget.charge_work(1)?;
        self.append_app(function, argument, budget)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn append_app(
        &mut self,
        a: ExprId,
        b: ExprId,
        budget: &mut Budget,
    ) -> Result<ExprId, ExpressionError> {
        // append or append_application charged before either child lookup. Keep
        // their order and all common validation/planning in prepare_append.
        let (x, y) = (self.summary(a, budget)?, self.summary(b, budget)?);
        let depth = x
            .depth()
            .max(y.depth())
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        let (slot, plan) = self.prepare_append(
            AppendFacts {
                tag: 3,
                binder: BinderInfo::Default,
                depth,
                flags: x.flags() | y.flags(),
                fields: [a.0, b.0, 0],
                loose: x.loose.max(y.loose),
                hash_fields: [x.fingerprint, y.fingerprint, 0],
            },
            budget,
        )?;
        self.publish_node(plan);
        Ok(ExprId(slot))
    }

    // Keep the multi-kind payload frame out of the small application route.
    #[inline(never)]
    fn append_general(
        &mut self,
        kind: ExprKind<'_>,
        levels: &Levels,
        names: &impl LevelNames,
        budget: &mut Budget,
    ) -> Result<ExprId, ExpressionError> {
        let mut tag = 0;
        let mut binder = BinderInfo::Default;
        let mut fields = [0; 3];
        // Whole-span work is charged before scans, hashing or copying. All stores
        // keep their logical lengths until every required allocation succeeds.
        let mut literal: &[u8] = &[];
        let (depth, loose, flags, hash_fields) = match kind {
            ExprKind::Bound(index) => {
                fields[0] = index;
                (
                    0,
                    index.checked_add(1).ok_or(ExpressionError::NumericRange)?,
                    0,
                    [index, 0, 0],
                )
            }
            ExprKind::Free(id) => {
                tag = 1;
                fields[0] = id;
                (0, 0, FREE, [id, 0, 0])
            }
            ExprKind::Sort(id) => {
                let level = levels.get(id, budget)?;
                tag = 2;
                fields[0] = id.slot();
                (
                    level.depth(),
                    0,
                    if level.has_param() { PARAM } else { 0 },
                    [level.structural_hash(), 0, 0],
                )
            }
            ExprKind::App(a, b) => {
                return self.append_app(a, b, budget);
            }
            ExprKind::Lambda(name, domain, body, annotation)
            | ExprKind::Pi(name, domain, body, annotation) => {
                let name_summary = names.summary(name, budget)?;
                let (domain_node, body_node) =
                    (self.summary(domain, budget)?, self.summary(body, budget)?);
                tag = if matches!(kind, ExprKind::Lambda(..)) {
                    4
                } else {
                    5
                };
                binder = annotation;
                fields = [name.0, domain.0, body.0];
                (
                    name_summary
                        .depth
                        .max(domain_node.depth())
                        .max(body_node.depth()),
                    domain_node.loose.max(body_node.loose.saturating_sub(1)),
                    domain_node.flags() | body_node.flags(),
                    [0, domain_node.fingerprint, body_node.fingerprint],
                )
            }
            ExprKind::Constant(name, args) => {
                budget
                    .charge_work(u64::try_from(args.len()).map_err(|_| ResourceError::Counter)?)?;
                let n = names.summary(name, budget)?;
                let (offset, count) = new_span(self.level_lists.len(), args.len())?;
                tag = 6;
                fields = [name.0, offset, count];
                let mut depth = n.depth;
                let mut flags = 0;
                let mut hash = 0;
                for arg in args {
                    let l = levels.get(*arg, budget)?;
                    depth = depth.max(l.depth());
                    flags |= if l.has_param() { PARAM } else { 0 };
                    hash = mix(hash, l.structural_hash());
                }
                (depth, 0, flags, [n.canonical, count, hash])
            }
            ExprKind::Let(name, ty, value, body, nondep) => {
                let n = names.summary(name, budget)?;
                let (t, v, r) = (
                    self.summary(ty, budget)?,
                    self.summary(value, budget)?,
                    self.summary(body, budget)?,
                );
                tag = 7;
                fields[0] =
                    u32::try_from(self.lets.len()).map_err(|_| ExpressionError::NumericRange)?;
                (
                    n.depth.max(t.depth()).max(v.depth()).max(r.depth()),
                    t.loose.max(v.loose).max(r.loose.saturating_sub(1)),
                    t.flags() | v.flags() | r.flags(),
                    [
                        // Let display names are irrelevant to C1 identity. Retain
                        // the raw name in the descriptor and its depth above.
                        0,
                        t.fingerprint,
                        mix(mix(v.fingerprint, r.fingerprint), u32::from(nondep)),
                    ],
                )
            }
            ExprKind::Projection(name, index, target) => {
                let n = names.summary(name, budget)?;
                let t = self.summary(target, budget)?;
                tag = 8;
                fields = [name.0, index, target.0];
                (
                    n.depth.max(t.depth()),
                    t.loose,
                    t.flags(),
                    [n.canonical, index, t.fingerprint],
                )
            }
            ExprKind::Natural(text) | ExprKind::String(text) => {
                budget
                    .charge_work(u64::try_from(text.len()).map_err(|_| ResourceError::Counter)?)?;
                literal = if matches!(kind, ExprKind::Natural(_)) {
                    if text.is_empty() || !text.iter().all(|b| b.is_ascii_digit()) {
                        return Err(ExpressionError::InvalidNatural);
                    }
                    let stripped =
                        &text[text.iter().position(|b| *b != b'0').unwrap_or(text.len())..];
                    if stripped.is_empty() { b"0" } else { stripped }
                } else {
                    std::str::from_utf8(text).map_err(|_| ExpressionError::InvalidString)?;
                    text
                };
                let (offset, count) = new_span(self.bytes.len(), literal.len())?;
                tag = if matches!(kind, ExprKind::Natural(_)) {
                    9
                } else {
                    10
                };
                fields = [offset, count, 0];
                let hash = literal
                    .iter()
                    .fold(0, |hash, byte| mix(hash, u32::from(*byte)));
                (0, 0, 0, [count, hash, 0])
            }
            ExprKind::MData(payload, wrapped) => {
                // The payload is already a validated JSON object when it
                // reaches this store; copy it verbatim. Identity invariants and
                // the cache rules treat metadata nodes as ordinary composites:
                // byte-identical payloads rebuild to the same fingerprint, and
                // any payload difference changes both hash and identity level.
                let child = self.summary(wrapped, budget)?;
                budget.charge_work(
                    u64::try_from(payload.len()).map_err(|_| ResourceError::Counter)? + 1,
                )?;
                literal = payload;
                let (offset, count) = new_span(self.bytes.len(), literal.len())?;
                tag = 11;
                fields = [wrapped.0, offset, count];
                let hash = literal
                    .iter()
                    .fold(0, |hash, byte| mix(hash, u32::from(*byte)));
                (
                    child.depth(),
                    child.loose,
                    child.flags() | META,
                    [child.fingerprint, count, hash],
                )
            }
        };
        let depth = if matches!(
            kind,
            ExprKind::Bound(_) | ExprKind::Free(_) | ExprKind::Natural(_) | ExprKind::String(_)
        ) {
            0
        } else {
            depth.checked_add(1).ok_or(ResourceError::Counter)?
        };
        let (slot, plan) = self.prepare_append(
            AppendFacts {
                tag,
                binder,
                depth,
                flags,
                fields,
                loose,
                hash_fields,
            },
            budget,
        )?;
        match kind {
            ExprKind::Constant(_, args) => {
                budget.grow_vec(
                    &mut self.level_lists,
                    fields[1] as usize + fields[2] as usize,
                )?;
                self.level_lists.extend_from_slice(args);
            }
            ExprKind::Let(name, ty, value, body, nondep) => {
                let required = self
                    .lets
                    .len()
                    .checked_add(1)
                    .ok_or(ResourceError::Counter)?;
                budget.grow_vec(&mut self.lets, required)?;
                self.lets
                    .push([name.0, ty.0, value.0, body.0, u32::from(nondep)]);
            }
            ExprKind::Natural(_) | ExprKind::String(_) | ExprKind::MData(_, _) => {
                // Natural/String spans are [offset, count, 0]; tag 11 is
                // [wrapped, offset, count]. Both must reserve the payload end
                // (offset + count): reserving fields[0] + fields[1] for tag 11
                // would use the wrapped slot, and extend_from_slice could then
                // grow the vector outside the Budget::grow_vec ledger.
                let (offset, count) = if tag == 11 {
                    (fields[1], fields[2])
                } else {
                    (fields[0], fields[1])
                };
                budget.grow_vec(&mut self.bytes, offset as usize + count as usize)?;
                self.bytes.extend_from_slice(literal);
            }
            _ => {}
        }
        self.publish_node(plan);
        Ok(ExprId(slot))
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn prepare_append(
        &mut self,
        facts: AppendFacts,
        budget: &mut Budget,
    ) -> Result<(u32, NodePlan), ExpressionError> {
        let AppendFacts {
            tag,
            binder,
            depth,
            flags,
            fields,
            loose,
            hash_fields,
        } = facts;
        if crate::resource::traced!("expressions.limit", (depth, STRUCTURE_DEPTH), {
            depth > STRUCTURE_DEPTH
        }) {
            return Err(ResourceError::StructureDepth.into());
        }
        let slot = crate::resource::traced!("expressions.slot_limit", self.nodes.len(), {
            u32::try_from(self.nodes.len()).map_err(|_| ResourceError::Storage)
        })?;
        // Alpha identity omits display names and annotations as before. All
        // constructors use this same checked slot and fingerprint derivation.
        let mut hash = u32::from(tag);
        for field in hash_fields {
            hash = hash
                .rotate_left(7)
                .wrapping_add(field)
                .wrapping_mul(0x85eb_ca6b);
        }
        let plan = self.plan_node(
            RawExpression {
                descriptor: Descriptor::new(tag, binder, depth, flags, fields),
                fingerprint: hash,
                loose,
            },
            budget,
        )?;
        Ok((slot, plan))
    }

    /// Rebuild a metadata wrapper around a changed child, reusing the retained
    /// payload span instead of copying its bytes a second time. The span must
    /// lie inside this store's current bytes and below every later truncation;
    /// revalidation and rehashing charge it once more. A rebuilt wrapper whose
    /// payload and child equal the original is byte-identical to it, so the
    /// Identity and cache rules see no difference.
    pub(crate) fn append_metadata_span(
        &mut self,
        wrapped: ExprId,
        payload: (u32, u32),
        budget: &mut Budget,
    ) -> Result<ExprId, ExpressionError> {
        budget.charge_work(u64::from(payload.1) + 2)?;
        span(&self.bytes, payload.0, payload.1)?;
        let child = self.summary(wrapped, budget)?;
        let bytes_hash = self.bytes[payload.0 as usize..payload.0 as usize + payload.1 as usize]
            .iter()
            .fold(0, |hash, byte| mix(hash, u32::from(*byte)));
        let hash = u32::from(11u8);
        let hash = [child.fingerprint, payload.1, bytes_hash]
            .into_iter()
            .fold(hash, |h, field| {
                h.rotate_left(7)
                    .wrapping_add(field)
                    .wrapping_mul(0x85eb_ca6b)
            });
        let depth = child.depth().checked_add(1).ok_or(ResourceError::Counter)?;
        if crate::resource::traced!("expressions.limit", (depth, STRUCTURE_DEPTH), {
            depth > STRUCTURE_DEPTH
        }) {
            return Err(ResourceError::StructureDepth.into());
        }
        let slot = crate::resource::traced!("expressions.slot_limit", self.nodes.len(), {
            u32::try_from(self.nodes.len()).map_err(|_| ResourceError::Storage)
        })?;
        let plan = self.plan_node(
            RawExpression {
                descriptor: Descriptor::new(
                    11,
                    BinderInfo::Default,
                    depth,
                    child.flags() | META,
                    [wrapped.0, payload.0, payload.1],
                ),
                fingerprint: hash,
                loose: child.loose,
            },
            budget,
        )?;
        self.publish_node(plan);
        Ok(ExprId(slot))
    }
}

fn mix(hash: u32, field: u32) -> u32 {
    hash.rotate_left(7)
        .wrapping_add(field)
        .wrapping_mul(0x85eb_ca6b)
}

fn new_span(start: usize, len: usize) -> Result<(u32, u32), ExpressionError> {
    let end = start
        .checked_add(len)
        .ok_or(ExpressionError::NumericRange)?;
    u32::try_from(end).map_err(|_| ExpressionError::NumericRange)?;
    Ok((
        u32::try_from(start).map_err(|_| ExpressionError::NumericRange)?,
        u32::try_from(len).map_err(|_| ExpressionError::NumericRange)?,
    ))
}

fn span<T>(values: &[T], start: u32, len: u32) -> Result<&[T], ResourceError> {
    let end = (start as usize)
        .checked_add(len as usize)
        .ok_or(ResourceError::Invariant)?;
    values
        .get(start as usize..end)
        .ok_or(ResourceError::Invariant)
}
