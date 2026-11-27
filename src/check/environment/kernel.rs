//! Positive-only value kernel, with bounded retention.
//!
//! Checks one ordinary declaration on closure/environment values. The result
//! is positive-only: `Ok(true)` means the declaration's type is a sort (a
//! proposition for theorems) and its value has that type; `Ok(false)` means
//! this route proved nothing, and the caller runs the existing checker on the
//! unchanged declaration. No path here rejects. A mandatory budget error is
//! returned as `Err` and stays terminal.
//!
//! Scope: exact graph/source/environment/universe identities in one attempt,
//! or the same State's completed retained graph. Borrowed views
//! and failed/speculative receipts never cross attempts. Formation, checked
//! contexts and quotient retries cannot reuse retained facts. Original syntax
//! is immutable; copied generated levels replay exact slots only at a matching
//! source frontier. No generated expression syntax is published.
//! Value identity implies equal denotation: values are immutable apart from a
//! thunk's redirection to its own value. Binder locals are canonical by
//! (type value, binder depth); binders open together have distinct depths, so
//! every cache keyed by value ids is sound for that exact graph (,
//! invariants). Universe substitution creates level nodes in the session's
//! level store, which the enclosing declaration session rolls back.
use super::constant_use::{ConstantUse, UseError};
use super::{
    Environment, Formation, NullaryRule, QuotientRole, SignatureKind, StoredKind, TypeSource,
};
use crate::check::environment::normalization::{Mode, Scope};
use crate::check::natural::Operation;
use crate::decode::primitive_decode::declarations::{Hint, Kind, Request, Safety};
use crate::resource::{Budget, ResourceError};
use crate::syntax::expressions::{ExprId, ExprKind, Expression, Expressions};
use crate::syntax::hash::FastHasher;
use crate::syntax::levels::{
    LevelId, LevelKind, LevelNames, LevelZero, Levels, NameId, UniverseComparison,
};
use crate::syntax::local_context::LocalContext;
use crate::syntax::names::Names;
use std::collections::HashMap;
use std::hash::BuildHasherDefault;
#[cfg(target_pointer_width = "64")]
use std::mem::size_of;
use std::num::NonZeroU32;

mod constants;
mod declaration_witness;
mod defeq;
mod derived;
mod eval;
mod infer;
mod levels;
mod natural;
mod node_index;
use node_index::{NodeIndex, Probe};
mod reduce;
mod table;
mod values;
pub(super) use declaration_witness::{Witness, different as different_theorem, witness_probe_fits};
pub(super) mod negative;
mod read_key_cache;
mod read_large;
mod retention;
mod source_judgments;
pub(super) use retention::{Retention, select_cleanup};
use source_judgments::SourceJudgments;
mod scratch;
use natural::*;
use scratch::Scratch;
use table::*;

type Map<K, V> = HashMap<K, V, BuildHasherDefault<FastHasher>>;
type ValueKey = (u32, u32, u32, u32, u32);

/// A bounded, lossy direct-mapped cache. Every use is an optimisation: a
/// miss or an overwritten entry only loses sharing, never a conclusion, so a
/// table never rehashes beyond its cap and its memory stays bounded.
///
/// A cold table starts at `LOSSY_START`; a restored table keeps its
/// charged logical size and scoped entries. It doubles under load; only that size decides placement, growth and
/// charges, so behaviour never depends on capacity kept from an earlier
/// attempt. Physical slots are reused when they exist.
struct Lossy<K, V> {
    slots: Vec<Option<(NonZeroU32, K, V)>>,
    /// Empty compatibility buffer: keep the existing owner layout and charge.
    /// In-place growth uses only `slots`; wrap and held-capacity checks cover both.
    spare: Vec<Option<(NonZeroU32, K, V)>>,
    /// Logical size: zero (nothing inserted yet) or a power of two.
    size: usize,
    used: usize,
    lookups: u64,
    hits: u64,
    off: bool,
    /// Entries from earlier generations are vacant: O(1) reset.
    // Zero belongs exclusively to Option::None; live epochs are nonzero.
    generation: NonZeroU32,
}
const LOSSY_START: usize = 1 << 4;
/// Bytes of one store kept for reuse between attempts (uncharged).
const RETAIN: usize = 1 << 18;
/// Lossy tables stop doubling at this many slots; a full table evicts.
const LOSSY_CAP: usize = 1 << 19;
/// From this logical size the exact memo doubles at three-quarter load
/// instead of half load.
const MEMO_DENSE: usize = 1 << 21;
/// Loose ranges one and two already have exact binding keys. Wider read
/// plans cover at most four 64-bit words (read_wide).
const MAX_EVAL_READ_RANGE: u32 = 256;
trait Resettable {
    fn reset_table(&mut self);
}
impl<K: LossyKey, V: Copy> Resettable for Lossy<K, V>
where
    Option<(NonZeroU32, K, V)>: crate::resource::charged::Charged,
{
    fn reset_table(&mut self) {
        self.reset();
    }
}
/// Keys of lossy tables: small tuples of u32, hashed by one multiply chain.
trait LossyKey: Copy + Eq {
    fn mix(&self) -> u64;
}
// Only the untyped env_lossy branch owns this key: its omitted ty is NONE.
// Equality therefore matches the legacy (parent, val, NONE) domain exactly.
// Keep the third hash word so placement and growth winners remain unchanged.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct EnvKey {
    parent: u32,
    val: u32,
}
/// An exact open-addressing table (linear probing) for the evaluation memo:
/// call-by-need sharing must never be lost, or a DAG-shaped term re-evaluates
/// shared subterms (measured: shared-subterm 13× with a lossy memo). It grows
/// at half load, or three-quarter load from `MEMO_DENSE` slots, under the
/// attempt storage budget; charges follow the logical size only. Resize
/// reserves both logical buffers before allocation and retires the old logical
/// charge only after in-place migration. No incomplete insertion supplies an
/// evaluation result.
///
/// A slot packs the key and value into five words (dense-entry
/// trial): expression slot, level instance with the read-key tag in its two
/// high bits, the two read-key words, and the value. `NONE` in the value word
/// marks a vacant slot. A key whose level instance needs more than 30 bits is
/// never stored or found: the memo only shares, so skipping it loses no
/// conclusion. Reset clears the finished attempt's logical table.
#[derive(Default)]
struct Exact {
    slots: Vec<MemoSlot>,
    spare: Vec<MemoSlot>,
    size: usize,
    used: usize,
}
/// Evaluation memo key: expression slot, level instance, read-key tag and
/// two read-key words.
type MemoKey = (u32, u32, u32, u32, u32);
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct MemoSlot {
    key: [u32; 4],
    val: u32,
}
struct MemoVacancy {
    size: usize,
    index: usize,
    key: [u32; 4],
}
const MEMO_VACANT: MemoSlot = MemoSlot {
    key: [0; 4],
    val: NONE,
};
/// Level instances below this bound leave two bits for the read-key tag.
const MEMO_LEVEL_INSTANCES: u32 = 1 << 30;

const NONE: u32 = u32::MAX;
/// Stack capacity, not a semantic arity bound. Wider instances must not
/// introduce uncharged list copies or buffers spanning recursive inference.
const LEVEL_ARGS: usize = 16;
/// Optional attempt limits: exceeding either ends this attempt only.
const MAX_DEPTH: u32 = 400_000;
/// Stack reserved for the checking thread (`Run::check`).
#[cfg(not(target_family = "wasm"))]
pub(crate) const CHECK_STACK: usize = 2 << 30;
/// wasm32: the linear-memory stack, passed to the linker by `build.rs`.
#[cfg(target_family = "wasm")]
pub(crate) const CHECK_STACK: usize = crate::resource::wasm_layout::STACK_BYTES as usize;
/// Stack the kernel may use below its thread's base before an attempt ends:
/// the reservation less a margin for the frames between checks.
const STACK_BUDGET: usize = CHECK_STACK - (64 << 20);
thread_local! {
    /// Approximate base of the checking thread's stack (0 when unknown).
    static STACK_BASE: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
/// Record the current frame as the checking thread's stack base.
pub(crate) fn mark_stack_base() {
    let probe = 0u8;
    STACK_BASE.with(|c| c.set(std::ptr::addr_of!(probe) as usize));
}
/// Steps one value attempt may take. An abandoned attempt is paid in full
/// before the ordinary route starts, so this bounds the work it can waste; it
/// sits well above the largest completed attempt measured.
const MAX_STEPS: u64 = 1 << 28;
#[inline(always)]
fn step_cap() -> u64 {
    MAX_STEPS
}
/// Work is charged to the mandatory budget in blocks of this many steps.
const CHARGE_BLOCK: u64 = 4096;
/// Step allowance for trying a shared head's arguments before unfolding it.
const ARGS_BUDGET: u64 = 1 << 14;
/// Allowance for reducing a let-bound operand to a literal before `lazy_delta`
/// folds it. A value that needs more is left to delta unfolding,
/// as Lean leaves a let-bound free variable unfolded there.
const LET_FOLD_BUDGET: u64 = 1 << 14;
/// Step allowance for one support walk while computing an absent mask.
const MASK_BUDGET: u64 = 256;
/// Spines of at most this many arguments are compared from stack arrays.
const SMALL_SPINE: usize = 8;
/// Lookups before a lossy table may switch itself off for a low hit rate.
const LOSSY_REVIEW: u64 = 1 << 14;
/// Syntax probes must not rescan long suffixes before ordinary conversion.
const SYN_BUDGET: u64 = 64;
/// Amortize optional context analysis only after an attempt has done real work.
const ALPHA_MIN_STEPS: u64 = 4096;
/// Short staged formation checks often visit a wide telescope only once.
const FORMATION_CONTEXT_KEY_MIN_STEPS: u64 = 1 << 20;
/// Local ids at and above this are syntactic-comparison placeholders.
const MARKER_BASE: u32 = 0xF000_0000;

#[derive(Clone, Copy, Debug)]
pub(crate) enum KErr {
    Unsupported,
    /// Exhaustion detected at an existing global step guard.
    StepLimit,
    LiteralArithmetic,
    /// A bounded optional sub-attempt ran out of its step allowance.
    Abort,
    Resource(ResourceError),
}
impl From<ResourceError> for KErr {
    fn from(e: ResourceError) -> Self {
        Self::Resource(e)
    }
}
impl From<UseError> for KErr {
    fn from(e: UseError) -> Self {
        match e {
            UseError::Resource(e) => Self::Resource(e),
            UseError::LiteralArithmetic => Self::LiteralArithmetic,
            _ => Self::Unsupported,
        }
    }
}
type R<T> = Result<T, KErr>;
#[cfg_attr(feature = "introspection", track_caller)]
fn no<T>() -> R<T> {
    #[cfg(feature = "introspection")]
    {
        let here = std::panic::Location::caller();
        probe::SITE.with(|c| c.set(Some(here)));
    }
    Err(KErr::Unsupported)
}

/// Attribute exhaustion to its detection site. The coarse guard preserves its
/// old `no` attribution; manual guards now report their own site instead of stale state.
#[cfg_attr(feature = "introspection", track_caller)]
fn step_limit<T>() -> R<T> {
    #[cfg(feature = "introspection")]
    {
        let here = std::panic::Location::caller();
        probe::SITE.with(|c| c.set(Some(here)));
    }
    Err(KErr::StepLimit)
}

/// Attempt diagnostics (introspection builds only, `KEFIR_KERNEL_TRACE`).
/// Everything here only reads counters the kernel already keeps: it forces no
/// value, renders no name and charges nothing, so it cannot change a step
/// count, budget charge or outcome.
#[cfg(feature = "introspection")]
mod probe {
    use std::cell::Cell;
    use std::panic::Location;
    thread_local! {
        /// The most recent incomplete-route site in this attempt. Caught
        /// sub-attempts can leave a stale site when the escaping error did
        /// not come from `no()` (e.g. a converted use error).
        pub(super) static SITE: Cell<Option<&'static Location<'static>>> =
            const { Cell::new(None) };
        static ATTEMPT: Cell<u64> = const { Cell::new(0) };
        // Fixed aggregates only. Abandoned spans overlap when probes nest;
        // root spans are separately reported, never summed as exclusive work.
        static RECURSOR: Cell<[u64; 6]> = const { Cell::new([0; 6]) };
        static RECURSOR_DEPTH: Cell<u32> = const { Cell::new(0) };
    }
    pub(super) fn recursor_begin() -> bool {
        RECURSOR.with(|c| {
            let mut counts = c.get();
            counts[0] = counts[0].saturating_add(1);
            c.set(counts);
        });
        RECURSOR_DEPTH.with(|c| {
            let old = c.get();
            c.set(old.saturating_add(1));
            old == 0
        })
    }
    pub(super) fn recursor_end(result: &super::R<bool>, steps: u64, root: bool) {
        RECURSOR_DEPTH.with(|c| c.set(c.get().saturating_sub(1)));
        RECURSOR.with(|c| {
            let mut counts = c.get();
            let slot = match result {
                Ok(true) => 1,
                Ok(false) => {
                    counts[3] = counts[3].saturating_add(steps);
                    if root {
                        counts[4] = counts[4].saturating_add(steps);
                    }
                    2
                }
                Err(_) => 5,
            };
            counts[slot] = counts[slot].saturating_add(1);
            c.set(counts);
        });
    }
    pub(super) fn report(
        name: u32,
        result: &super::R<()>,
        steps: u64,
        tables: [(&str, u64, u64, bool); 4],
    ) {
        let site = SITE.with(|c| c.take());
        let recursor = RECURSOR.with(|c| c.replace([0; 6]));
        let n = ATTEMPT.with(|c| {
            c.set(c.get() + 1);
            c.get()
        });
        if std::env::var_os("KEFIR_KERNEL_TRACE").is_none() {
            return;
        }
        let at = site.map_or(0, |l| l.line());
        let ok = result.is_ok();
        let error = result.as_ref().err();
        eprintln!(
            "KERNEL attempt={n} name={name} ok={ok} steps={steps} error={error:?} fallback_line={at}"
        );
        for (t, lookups, hits, off) in tables {
            eprintln!("KERNEL   table={t} lookups={lookups} hits={hits} off={off}");
        }
        let [
            admissions,
            positive,
            abandoned,
            abandoned_steps,
            root_abandoned_steps,
            terminal,
        ] = recursor;
        eprintln!(
            "KERNEL   recursor admissions={admissions} positive={positive} abandoned={abandoned} abandoned_steps_inclusive={abandoned_steps} root_abandoned_steps={root_abandoned_steps} terminal={terminal}"
        );
    }
}

type AlphaKey = (u32, u32, u32, [u32; 8], [u32; 8]);

/// A syntax body evaluated in an environment under a level instance.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Clo {
    dom: ExprId,
    body: ExprId,
    env: u32,
    li: u32,
}

/// Per-value caches: weak head normal form, its delta-free form, and type.
#[derive(Clone, Copy)]
struct Meta {
    // Successfully completed lazy-delta reduction, for this exact value ID.
    // Scope: this exact graph/source eligible monotone
    // frontier, or one attempt otherwise. Values fix constant/universe/spine;
    // local IDs have permanent types. Forcing preserves meaning. Only completed
    // observations survive capture. Capacity-only Arena reuse clears contents.
    delta: u32,
    whnf: u32,
    core: u32,
}

// Same completed intrinsic-type facts and exact value IDs as Meta.ty.
// Scope: this owned graph/source/typed-context instance. Both vectors move
// with retention and clear before capacity-only Arena reuse. No eviction.
#[derive(Default)]
struct TypePages {
    // Zero: absent page. Otherwise one plus a 256-aligned offset in values.
    directory: Vec<u32>,
    values: Vec<u32>,
}

#[derive(Clone, Copy)]
enum Val {
    /// Unforced thunk.
    Delayed {
        e: ExprId,
        env: u32,
        li: u32,
    },
    /// Forced thunk: same meaning as the target value.
    Ind(u32),
    Sort(LevelId),
    Lam(Clo),
    Pi(Clo),
    /// The type of a lambda: `Π x : dom, typeof(body)` in the closure.
    LamTy(Clo),
    /// A non-dependent function type with evaluated domain and codomain.
    Arrow {
        dom: u32,
        cod: u32,
    },
    /// A projection whose structure has not been reduced yet.
    Proj {
        x: u32,
        idx: u32,
        sci: u32,
    },
    Local {
        id: u32,
        spine: u32,
    },
    Const {
        ci: u32,
        li: u32,
        spine: u32,
    },
    Nat(u32),
    /// A string literal (its original expression); expanded on demand.
    Str(ExprId),
}

/// Persistent spine cell; `tag == 0` is an argument, otherwise projection of
/// field `tag - 1` of structure constant `item`.
#[derive(Clone, Copy)]
struct Cell {
    prev: u32,
    item: u32,
    tag: u32,
    len: u32,
}

/// Construction invariant: ID zero is the initialized empty environment. Every
/// nonzero ID names an already appended node whose parent precedes it.
/// Retention moves IDs with their owning graph, and arena reset clears
/// every ID-bearing value and index before the graph is reused.
#[derive(Clone, Copy)]
struct EnvNode {
    parent: u32,
    val: u32,
    ty: u32,
}

#[derive(Clone, Copy)]
struct Rec<'e> {
    family: u32,
    k: bool,
    /// Validated nonrecursive, zero-index, single-constructor family.
    eta: bool,
    common: u32,
    cparams: u32,
    nidx: u32,
    rules: &'e [NullaryRule],
}
#[derive(Clone, Copy)]
struct Ind<'e> {
    nparams: u32,
    nidx: u32,
    nonrecursive: bool,
    ctors: &'e [NullaryRule],
}
impl Ind<'_> {
    /// Lean's structure-like families: one constructor, no indices, not
    /// recursive. Only these get structure eta (in conversion and for iota)
    /// and unit-like equality.
    fn structure_like(&self) -> bool {
        self.ctors.len() == 1 && self.nidx == 0 && self.nonrecursive
    }
}

#[derive(Clone, Copy)]
struct ConstantSlot {
    name: NameId,
    epoch: u32,
    view: u32,
}

#[derive(Clone, Copy)]
struct CInfo<'e> {
    name: NameId,
    canon: u32,
    ty: Option<ExprId>,
    value: Option<ExprId>,
    params: &'e [NameId],
    /// Unfolding priority (class, height) for definitions and theorems.
    delta: Option<(u8, u32)>,
    rec: Option<Rec<'e>>,
    ctor: Option<(u32, u32)>,
    ind: Option<Ind<'e>>,
    /// 0 unknown, 1 none, 2 + operation index.
    natop: u8,
    /// 0 unknown, 1 none, 2 equality (`Nat.beq`), 3 less-or-equal (`Nat.ble`).
    natpred: u8,
    /// Validated quotient primitive role.
    quot: Option<QuotientRole>,
}

enum Lazy {
    Decided(bool),
    Stuck(u32, u32),
}

#[derive(Clone, Copy)]
struct LInst {
    ci: u32,
    start: u32,
    len: u32,
    next: u32,
}

mod natural_store;
use natural_store::{Recipe, Store};
enum NatLit {
    Small(u64),
    /// Canonical decimal digits of a value above `u64::MAX`.
    Big(Vec<u8>),
    Computed(
        Box<[crate::check::natural::BinaryNat; 1]>,
        std::cell::Cell<u64>,
    ),
    Evicted(Recipe),
}

/// Capacity reused across declaration attempts on one thread. Contents are
/// always cleared before reuse: no value, environment or cache entry survives
/// an attempt. Charges and table behaviour follow logical sizes, which depend
/// only on the attempt itself; reused capacity is bounded by `RETAIN`.
#[derive(Default)]
struct Arena {
    vals: Vec<Val>,
    meta: Vec<Meta>,
    type_cache: TypePages,
    cells: Vec<Cell>,
    envs: Vec<EnvNode>,
    locals: Vec<u32>,
    memo: Exact,
    clo_index: Lossy<(u32, u32, u32, u32, u32, u32), u32>,
    env_index: NodeIndex,
    env_lossy: Lossy<EnvKey, u32>,
    infer_cache: Map<(u32, u32, u32), (u32, bool)>,
    eq_ok: Lossy<(u32, u32), ()>,
    val_index: Lossy<(u32, u32, u32, u32, u32), u32>,
    cell_index: Lossy<(u32, u32, u32), u32>,
    syn_ok: Lossy<(u32, u32, u32, u32, u32, u32), ()>,
    args_fail: Lossy<(u32, u32), ()>,
    local_index: Map<(u32, u32), u32>,
}
thread_local! {
    static ARENA: std::cell::RefCell<Option<Arena>> = const { std::cell::RefCell::new(None) };
}

/// Bounds belong to one attempt. Total scopes count every admission; argument
/// scopes count total steps minus tracked span credit. They never
/// travel with a retained graph, and nested scopes only narrow their own clock.
#[derive(Clone, Copy)]
struct ProbeBounds {
    total: u64,
    arguments: u64,
}

pub(crate) struct Kernel<'e, 'w> {
    env: &'e Environment,
    names: &'w Names,
    exprs: &'w Expressions,
    levels: &'w mut Levels,
    b: &'w mut Budget,
    params: &'e [NameId],
    before: usize,
    formation: Option<Formation>,
    checked_context: Option<&'w LocalContext>,
    /// Completed values of checked free locals, scoped to this immutable query/context.
    /// Never transferred between queries, contexts, formation epochs or universe scopes.
    free_values: Map<u32, u32>,
    mode: Mode,
    expression_end: usize,
    level_end: usize,
    /// Source bound for universe substitution: original levels plus any
    /// quotient-schema levels built before this attempt began.
    subst_end: usize,

    vals: Vec<Val>,
    meta: Vec<Meta>,
    type_cache: TypePages,
    cells: Vec<Cell>,
    envs: Vec<EnvNode>,
    locals: Vec<u32>,
    consts: Vec<CInfo<'e>>,
    constant_slots: Vec<ConstantSlot>,
    constant_epoch: u32,
    const_by_canon: Map<u32, u32>,
    linsts: Vec<LInst>,
    linst_levels: Vec<LevelId>,
    linst_index: Map<u64, u32>,
    nats: Vec<NatLit>,
    natural_store: Store,
    /// Let-bound fold restriction: two bits per value ID, set
    /// only for let-bound thunks. Bit `2v` marks a let-bound value; bit
    /// `2v + 1` records that reducing it exceeded `LET_FOLD_BUDGET` with the
    /// whole allowance available. Scope: these exact value IDs in this State's
    /// retained graph; never another origin or formation context.
    /// It only withholds an optional literal fold; no result,
    /// equality or failure is stored or concluded from it.
    let_marks: Vec<u64>,

    /// Evaluation results and pending thunks by (expression, environment,
    /// level instance); closed expressions use environment 0.
    memo: Exact,
    /// Closures interned by (form, domain, body, level instance, read key).
    clo_index: Lossy<(u32, u32, u32, u32, u32, u32), u32>,
    /// Environment nodes interned by (parent, value, type).
    /// Exact: the inference cache is keyed by environment identity.
    env_index: NodeIndex,
    env_lossy: Lossy<EnvKey, u32>,
    // Present only for the eligible positive declaration attempt.
    source_judgments: Option<&'w mut SourceJudgments>,
    /// Exact: DAG-shared subterms must be checked once (losing an entry can
    /// make checking exponential), so this one is not lossy.
    infer_cache: Map<(u32, u32, u32), (u32, bool)>,
    const_type: Map<(u32, u32), u32>,
    const_body: Map<(u32, u32), u32>,
    /// Arguments a definition ignores (see `absent_args`), by constant.
    absent: Map<u32, u64>,
    /// (instantiated domain, 0) known not to be a proposition for these exact
    /// value IDs; retained only with their graph and original source in the
    /// same State, without formation or checked-context queries.
    // Isolated trial: completed argument-sort facts for the same immutable
    // graph, including only existing eligible retention. Original
    // type/context/universe identities and typed substitutions stay fixed.
    // Position zero keys an instantiated domain and stores non-proof only;
    // positions 1..=8 require explicit_proof_prefix before publication.
    // True means proof, not checkedness of an argument. No failed observation
    // or abandoned guard is stored; terminal retirement drops the owner.
    arg_proof_status: Map<(u32, u32), bool>,
    rule_rhs: Map<(u32, u32, u32), u32>,
    level_subst: Map<(u32, u32), LevelId>,
    level_eq: Map<(u32, u32), bool>,
    canon_of: Map<u32, LevelId>,
    level_index: Map<(u8, u32, u32), LevelId>,
    succ_of: Map<u32, LevelId>,
    eq_ok: Lossy<(u32, u32), ()>,
    /// Structural interning of value forms and spine cells (hash-consing).
    val_index: Lossy<(u32, u32, u32, u32, u32), u32>,
    cell_index: Lossy<(u32, u32, u32), u32>,
    lexical: source_judgments::Lexical,
    binders: Vec<u32>,
    markers: u32,
    marker_vals: Map<u32, u32>,
    syn_ok: Lossy<(u32, u32, u32, u32, u32, u32), ()>,
    local_index: Map<(u32, u32), u32>,
    args_fail: Lossy<(u32, u32), ()>,
    nat_type: u32,
    quot_types: Option<[ExprId; 4]>,
    wants_quot: bool,
    /// Derived rule trees and unfolding heat; this attempt only.
    derived: derived::Derived,
    str_expansion: Map<u32, u32>,
    nat_ctors: Option<(u32, u32, u32)>,
    scratch: Vec<Scratch>,

    depth: u32,
    /// The checking thread's stack base, read once per attempt (0: unknown).
    stack_base: usize,
    steps: u64,
    charged: u64,
    reserved: u64,
    /// Cached min(bounds.total, bounds.arguments + span_work), saturated.
    /// steps_by uses only this total-step bound; no second clock in its hot path.
    limit: u64,
    natural_probe_depth: u8,
    neutral_head_only: bool,
    /// Scheduling only, reset at every new attempt. A failed full comparison
    /// of captures has no bearing on equality of the source terms.
    full_capture_after: u64,
    // Attempt-local scheduling hints for optional capture agreement only.
    // Each exact pair previously returned Ok(false) from recursive comparison.
    // Never retained with the graph or read by ordinary term comparison.
    capture_misses: [u64; 8],
    /// Scheduling of optional same-head probes in this attempt only.
    full_argument_probe_after: u64,
    // An ordinary attempt that has settled an outer argument comparison
    // keeps full opportunities. This scheduling bit is never retained.
    ordinary_argument_success: bool,
    ordinary_argument_overrun: bool,
    bounds: ProbeBounds,
    span_work: u64,
    completed_value_keys: read_key_cache::ReadKeyCache,
    completed_type_keys: read_key_cache::ReadKeyCache,
    source_support: Map<u32, u64>,
    /// Bounded eval/thunk environment representatives.
    /// Exact raw values at complete source-fixed positions select an actual
    /// representative environment. No result or checkedness is stored here.
    /// Scope: ordinary, nonstaged queries in one State's retained graph; no
    /// Free-containing sources or checked formation contexts. Source and
    /// universe remain in the memo key. Forcing preserves each value ID's
    /// meaning. Retains exact graph/environment IDs only with their
    /// immutable source and name origin, never across State or staging owners.
    read_environments: Map<(u64, [u32; 16]), u32>,
    /// Wide-mask representatives, same exact graph/source/owner scope as above.
    /// Combined with read_environments, at most131072 entries; no eviction.
    wide_read_environments: Map<read_wide::RepresentativeKey, u32>,
    // Exact source read masks, typed context-list tokens and completed actual
    // judgments. Retains these only with exact graph/context IDs and
    // the same immutable source/name origin; no Free or formation context.
    read_plans: Map<u32, Option<[u64; 4]>>,
    large_read_nodes: Map<(u32, u32, u32), u32>,
    large_read_types: Map<read_large::LargeReadKey, u32>,
    alpha_types: Map<AlphaKey, (u32, [u32; 8])>,
    rename_ids: Map<(u32, [u32; 8], [u32; 8]), u32>,
    renamed_values: Map<(u32, u32), u32>,
    renamed_spines: Map<(u32, u32), u32>,
    renamed_envs: Map<(u32, u64, u32), u32>,
}

impl<'e, 'w> Kernel<'e, 'w> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        env: &'e Environment,
        names: &'w Names,
        exprs: &'w Expressions,
        levels: &'w mut Levels,
        b: &'w mut Budget,
        scope: &Scope<'e>,
    ) -> Self {
        let subst_end = levels.len();
        let mut a = ARENA.with(|c| c.borrow_mut().take()).unwrap_or_default();
        a.vals.clear();
        a.meta.clear();
        a.type_cache.directory.clear();
        a.type_cache.values.clear();
        a.cells.clear();
        a.envs.clear();
        a.locals.clear();
        for l in [
            &mut a.clo_index as &mut dyn Resettable,
            &mut a.env_lossy,
            &mut a.eq_ok,
            &mut a.val_index,
            &mut a.cell_index,
            &mut a.syn_ok,
            &mut a.args_fail,
        ] {
            l.reset_table();
        }
        a.memo.reset_table();
        a.env_index.clear();
        a.infer_cache.clear();
        a.local_index.clear();
        Self {
            env,
            names,
            exprs,
            levels,
            b,
            params: scope.parameters,
            before: scope.before,
            formation: scope.formation,
            checked_context: None,
            free_values: Map::default(),
            mode: scope.mode,
            expression_end: scope.expression_end,
            level_end: scope.level_end,
            subst_end,
            vals: a.vals,
            meta: a.meta,
            type_cache: a.type_cache,
            cells: a.cells,
            envs: a.envs,
            locals: a.locals,
            consts: Vec::new(),
            constant_slots: Vec::new(),
            constant_epoch: 1,
            const_by_canon: Map::default(),
            linsts: Vec::new(),
            linst_levels: Vec::new(),
            linst_index: Map::default(),
            nats: Vec::new(),
            natural_store: Store::default(),
            let_marks: Vec::new(),
            memo: a.memo,
            clo_index: a.clo_index,
            env_index: a.env_index,
            env_lossy: a.env_lossy,
            source_judgments: None,
            infer_cache: a.infer_cache,
            const_type: Map::default(),
            const_body: Map::default(),
            absent: Map::default(),
            arg_proof_status: Map::default(),
            rule_rhs: Map::default(),
            level_subst: Map::default(),
            level_eq: Map::default(),
            canon_of: Map::default(),
            level_index: Map::default(),
            succ_of: Map::default(),
            eq_ok: a.eq_ok,
            val_index: a.val_index,
            cell_index: a.cell_index,
            lexical: Default::default(),
            binders: Vec::new(),
            markers: 0,
            marker_vals: Map::default(),
            syn_ok: a.syn_ok,
            local_index: a.local_index,
            args_fail: a.args_fail,
            nat_type: NONE,
            quot_types: None,
            wants_quot: false,
            derived: derived::Derived::default(),
            str_expansion: Map::default(),
            nat_ctors: None,
            scratch: Vec::new(),
            depth: 0,
            stack_base: STACK_BASE.with(std::cell::Cell::get),
            steps: 0,
            charged: 0,
            reserved: 0,
            limit: u64::MAX,
            natural_probe_depth: 0,
            neutral_head_only: false,
            full_capture_after: 0,
            capture_misses: [0; 8],
            full_argument_probe_after: 0,
            ordinary_argument_success: false,
            ordinary_argument_overrun: false,
            bounds: ProbeBounds {
                total: u64::MAX,
                arguments: u64::MAX,
            },
            span_work: 0,
            alpha_types: Map::default(),
            rename_ids: Map::default(),
            renamed_values: Map::default(),
            renamed_spines: Map::default(),
            renamed_envs: Map::default(),
            completed_value_keys: Default::default(),
            completed_type_keys: Default::default(),
            source_support: Map::default(),
            read_environments: Map::default(),
            wide_read_environments: Map::default(),
            read_plans: Map::default(),
            large_read_nodes: Map::default(),
            large_read_types: Map::default(),
        }
    }

    // ---------- accounting ----------

    /// Reserve the reused arena capacity, then create the root spine cell,
    /// environment and level instance. Nothing allocates before this.
    fn init(&mut self) -> R<()> {
        // A fixed upper bound for the existing optional 64-entry pool itself.
        // Buffer payloads have separate live reservations, including in-pool.
        charge_bytes(
            self.b,
            &mut self.reserved,
            64 * crate::resource::charged::bytes::<Scratch>(),
        )?;
        room(self.b, &mut self.reserved, &mut self.cells, 1)?;
        self.cells.push(Cell {
            prev: 0,
            item: 0,
            tag: 0,
            len: 0,
        });
        room(self.b, &mut self.reserved, &mut self.envs, 1)?;
        self.envs.push(EnvNode {
            parent: 0,
            val: NONE,
            ty: NONE,
        });
        room(self.b, &mut self.reserved, &mut self.linsts, 1)?;
        self.linsts.push(LInst {
            ci: NONE,
            start: 0,
            len: 0,
            next: NONE,
        });
        Ok(())
    }

    fn argument_steps(&self) -> u64 {
        // Construction invariant: every installed span credit is also admitted
        // to total steps before returning, including when admission aborts.
        // Untracked outside-scope spans shift the next origin and bound equally.
        self.steps - self.span_work
    }
    fn refresh_limit(&mut self) {
        self.limit = self
            .bounds
            .total
            .min(self.bounds.arguments.saturating_add(self.span_work));
    }
    fn limit_arguments(&mut self, end: u64) {
        self.bounds.arguments = self.bounds.arguments.min(end);
        self.refresh_limit();
    }
    fn limit_total(&mut self, end: u64) {
        self.bounds.total = self.bounds.total.min(end);
        self.refresh_limit();
    }
    fn restore_bounds(&mut self, saved: ProbeBounds) {
        self.bounds = saved;
        self.refresh_limit();
    }
    /// Keep the mandatory ledger and attempt cap on total work, while granting
    /// only argument scopes credit for this known span. A strict total scope
    /// (syntax, support or let folding) remains authoritative.
    fn application_span(&mut self, count: u64) -> R<()> {
        // With no argument scope, shifting its future origin needs no stored
        // credit. Strict total scopes and the mandatory ledger still see it.
        if self.bounds.arguments == u64::MAX {
            return self.steps_by(count);
        }
        self.steps
            .checked_add(count)
            .ok_or(ResourceError::Counter)?;
        self.span_work = self
            .span_work
            .checked_add(count)
            .ok_or(ResourceError::Counter)?;
        self.refresh_limit();
        self.steps_by(count)
    }

    #[inline]
    fn step(&mut self) -> R<()> {
        self.steps_by(1)
    }
    /// One coarse admission for known traversal work. Lookups include their
    /// final entry read. The existing local allowance and global block flush
    /// count this work even on the cheap Bound-thunk path.
    #[inline]
    fn steps_by(&mut self, count: u64) -> R<()> {
        self.steps = self
            .steps
            .checked_add(count)
            .ok_or(ResourceError::Counter)?;
        if self.steps > self.limit {
            return Err(KErr::Abort);
        }
        let pending = self.steps - self.charged;
        if pending >= CHARGE_BLOCK {
            self.flush_steps(pending)?;
        }
        Ok(())
    }
    /// Admission checkpoints are rare compared with individual step updates.
    /// Preserve charge, review and exhaustion ordering outside their hot path.
    #[cold]
    fn flush_steps(&mut self, pending: u64) -> R<()> {
        self.b.charge_work(pending)?;
        self.charged = self.steps;
        self.env_lossy.review();
        self.val_index.review();
        self.cell_index.review();
        if self.steps > step_cap() {
            return step_limit();
        }
        Ok(())
    }
    #[inline]
    fn enter(&mut self) -> R<()> {
        let probe = 0u8;
        let used = self.stack_base.abs_diff(std::ptr::addr_of!(probe) as usize);
        if self.depth >= MAX_DEPTH || (self.stack_base != 0 && used > STACK_BUDGET) {
            return no();
        }
        // Count the frame only once the step is allowed, so an error here
        // (an exhausted allowance or budget) leaves the depth balanced.
        self.step()?;
        self.depth += 1;
        Ok(())
    }
    #[inline]
    fn leave(&mut self) {
        self.depth -= 1;
    }
    /// Return reusable capacity to the thread arena (contents are cleared on
    /// the next attempt's start).
    fn retire_arena(&mut self) {
        self.read_environments = Map::default();
        self.wide_read_environments = Map::default();
        // Attempt-local judgments are dead before value stores retire. Free
        // these owners first; their existing logical charge stays in reserved
        // until the unchanged attempt cleanup releases it. No receipt survives.
        self.read_plans = Map::default();
        self.large_read_nodes = Map::default();
        self.large_read_types = Map::default();
        // Keep only small stores between attempts: their capacity is not
        // charged to later attempts, so it stays a fixed per-thread amount
        // (at most `RETAIN` bytes per store; 16 stores, two buffers per lossy
        // table, so under 8 MiB). Larger stores are freed now.
        fn vec<T: crate::resource::charged::Charged>(v: &mut Vec<T>) -> Vec<T> {
            let v = std::mem::take(v);
            if v.capacity() * crate::resource::charged::bytes::<T>() <= RETAIN {
                v
            } else {
                Vec::new()
            }
        }
        fn map<K, V>(m: &mut Map<K, V>) -> Map<K, V>
        where
            (K, V): crate::resource::charged::Charged,
        {
            let m = std::mem::take(m);
            if map_bytes::<K, V>(m.capacity()) <= RETAIN {
                m
            } else {
                Map::default()
            }
        }
        fn lossy<K: LossyKey, V: Copy>(t: &mut Lossy<K, V>) -> Lossy<K, V>
        where
            Option<(NonZeroU32, K, V)>: crate::resource::charged::Charged,
        {
            let t = std::mem::take(t);
            if t.held() <= 2 * RETAIN {
                t
            } else {
                Lossy::default()
            }
        }
        let a = Arena {
            vals: vec(&mut self.vals),
            meta: vec(&mut self.meta),
            type_cache: TypePages {
                directory: vec(&mut self.type_cache.directory),
                values: vec(&mut self.type_cache.values),
            },
            cells: vec(&mut self.cells),
            envs: vec(&mut self.envs),
            locals: vec(&mut self.locals),
            memo: {
                let t = std::mem::take(&mut self.memo);
                if t.held() <= 2 * RETAIN {
                    t
                } else {
                    Exact::default()
                }
            },
            clo_index: lossy(&mut self.clo_index),
            env_index: self.env_index.retire(),
            env_lossy: lossy(&mut self.env_lossy),
            infer_cache: map(&mut self.infer_cache),
            eq_ok: lossy(&mut self.eq_ok),
            val_index: lossy(&mut self.val_index),
            cell_index: lossy(&mut self.cell_index),
            syn_ok: lossy(&mut self.syn_ok),
            args_fail: lossy(&mut self.args_fail),
            local_index: map(&mut self.local_index),
        };
        ARENA.with(|c| *c.borrow_mut() = Some(a));
    }

    // ---------- values ----------
}

/// Whether the kernel attempts this declaration at all: safe declarations in
/// a safe scope outside formation phases.
pub(crate) fn eligible(request: &Request<'_>, scope: &Scope<'_>) -> bool {
    request.safety == Safety::Safe && scope.mode == Mode::Safe && scope.formation.is_none()
}

/// Positive-only attempt for one declaration; see the module comment.
#[allow(clippy::too_many_arguments)]
pub(super) fn check(
    environment: &Environment,
    request: &Request<'_>,
    scope: &Scope<'_>,
    names: &Names,
    exprs: &mut Expressions,
    levels: &mut Levels,
    budget: &mut Budget,
    retention: Option<&mut Retention>,
) -> Result<bool, super::normalization::HeadError> {
    if !eligible(request, scope) {
        return Ok(false);
    }
    let checked = check_inner(
        environment,
        request,
        scope,
        names,
        exprs,
        levels,
        budget,
        retention,
    )?;
    Ok(checked)
}

#[allow(clippy::too_many_arguments)]
fn check_inner(
    environment: &Environment,
    request: &Request<'_>,
    scope: &Scope<'_>,
    names: &Names,
    exprs: &mut Expressions,
    levels: &mut Levels,
    budget: &mut Budget,
    retention: Option<&mut Retention>,
) -> Result<bool, super::normalization::HeadError> {
    let (ok, wants_quot) = attempt(
        environment,
        request,
        scope,
        names,
        exprs,
        levels,
        budget,
        None,
        retention,
    )?;
    if ok || !wants_quot {
        return Ok(ok);
    }
    // Retry once with the validated quotient schemas, generated only for
    // declarations that need a quotient's type (session syntax, rolled back).
    let Some(package) = environment.quotient.as_ref() else {
        return Ok(false);
    };
    let expression_mark = exprs.watermark();
    let level_mark = levels.len();
    let mut types = [ExprId::from_stored_original(0); 4];
    for role in [
        QuotientRole::Type,
        QuotientRole::Constructor,
        QuotientRole::Lift,
        QuotientRole::Induction,
    ] {
        let mut params = Vec::new();
        params
            .try_reserve_exact(2)
            .map_err(|_| ResourceError::Allocation)?;
        for &n in &package.names[5..5 + role.arity()] {
            params.push(levels.append(LevelKind::Param(n), names, budget)?);
        }
        types[role.index()] = match super::quotient::schema::build(
            role,
            &package.names,
            &params,
            exprs,
            levels,
            names,
            budget,
        ) {
            Ok(t) => t,
            Err(crate::syntax::expressions::ExpressionError::Resource(e)) => return Err(e.into()),
            Err(_) => {
                exprs.discard_since(expression_mark, budget)?;
                levels.discard_since(level_mark, budget)?;
                return Ok(false);
            }
        };
    }
    let result = attempt(
        environment,
        request,
        scope,
        names,
        exprs,
        levels,
        budget,
        Some(types),
        None, // private quotient-schema retry never sees the ordinary cache
    );
    // Nothing built for the attempt survives it; the existing checker, if it
    // runs next, sees the session exactly as before.
    // Levels remain referenced if expression rollback fails. Preserve an
    // earlier internal failure even when this dependent cleanup exhausts work.
    let cleanup = exprs
        .discard_since(expression_mark, budget)
        .and_then(|()| levels.discard_since(level_mark, budget));
    finish_rollback(result, cleanup)
}

fn finish_rollback(
    result: Result<(bool, bool), super::normalization::HeadError>,
    cleanup: Result<(), ResourceError>,
) -> Result<bool, super::normalization::HeadError> {
    if let Some(error) = super::normalization::full::select_failure([
        result.as_ref().err().copied(),
        cleanup.err().map(Into::into),
    ]) {
        return Err(error);
    }
    result.map(|(ok, _)| ok)
}

/// A formed field is scoped to the active staged constructor telescope that
/// opened it. Its owner supplies the checked-substitution premise immediately
/// before reconstruction. Ordinary queries always check the input expression.
pub(crate) enum FormationInput {
    Expression(ExprId),
    FormedField(crate::syntax::local_context::CheckedTy),
}

/// Completed checked formation under the caller's immutable context and exact
/// signature-only staging phase. Computation metadata is committed only. Every
/// incomplete attempt falls back; mandatory charge/cleanup failures propagate.
/// Caller owns generated levels until its existing session retirement.
#[allow(clippy::too_many_arguments)]
pub(crate) fn formation_sort(
    environment: &Environment,
    input: FormationInput,
    scope: &Scope<'_>,
    pre_staging: bool,
    context: &LocalContext,
    names: &Names,
    exprs: &Expressions,
    levels: &mut Levels,
    budget: &mut Budget,
) -> Result<Option<LevelId>, super::normalization::HeadError> {
    // A formation-free query needs the inductive pre-staging
    // authority; `check_scope` then requires exactly the committed
    // environment, so no staged signature or generated artifact is visible.
    if (scope.formation.is_none() && !pre_staging) || scope.mode != Mode::Safe {
        return Ok(None);
    }
    environment.check_scope(
        scope.before,
        scope.formation,
        scope.expression_end,
        scope.level_end,
    )?;
    let (root, check) = match input {
        FormationInput::Expression(root) => (root, true),
        FormationInput::FormedField(field) if scope.formation.is_some() => (field.expr(), false),
        FormationInput::FormedField(_) => return Ok(None),
    };
    let mut k = Kernel::new(environment, names, exprs, levels, budget, scope);
    k.checked_context = Some(context);
    let result = (|| {
        k.init()?;
        let ty = k.infer(root, 0, 0, check)?;
        k.sort_of(ty)
    })();
    let steps = k.steps - k.charged;
    let reserved = k.reserved;
    k.retire_arena();
    drop(k);
    let charge = budget.charge_work(steps);
    let release = budget.release(reserved);
    let (completed, _) = finish_attempt(
        result.as_ref().map(|_| ()).map_err(|e| *e),
        charge,
        release,
        false,
    )?;
    Ok(if completed { result.ok() } else { None })
}

/// Positive-only typed checking: check a generated rule against its independently
/// inferred expected type. No type syntax or checkedness escapes this query.
#[allow(clippy::too_many_arguments)]
pub(crate) fn formation_check(
    environment: &Environment,
    root: ExprId,
    expected: ExprId,
    scope: &Scope<'_>,
    context: &LocalContext,
    names: &Names,
    exprs: &Expressions,
    levels: &mut Levels,
    budget: &mut Budget,
) -> Result<bool, super::normalization::HeadError> {
    if scope.formation.is_none() || scope.mode != Mode::Safe {
        return Ok(false);
    }
    environment.check_scope(
        scope.before,
        scope.formation,
        scope.expression_end,
        scope.level_end,
    )?;
    let mut k = Kernel::new(environment, names, exprs, levels, budget, scope);
    k.checked_context = Some(context);
    let result = (|| {
        k.init()?;
        // Expected syntax is generated by the caller. Its construction alone
        // does not establish typing: this query checks it before consuming it.
        let et = k.infer(expected, 0, 0, true)?;
        k.sort_of(et)?;
        let expected = k.eval(expected, 0, 0)?;
        k.check_expr(root, expected, 0)
    })();
    let steps = k.steps - k.charged;
    let reserved = k.reserved;
    k.retire_arena();
    drop(k);
    let charge = budget.charge_work(steps);
    let release = budget.release(reserved);
    let (completed, _) = finish_attempt(result, charge, release, false)?;
    Ok(completed)
}

#[allow(clippy::too_many_arguments)]
fn attempt(
    environment: &Environment,
    request: &Request<'_>,
    scope: &Scope<'_>,
    names: &Names,
    exprs: &Expressions,
    levels: &mut Levels,
    budget: &mut Budget,
    quot_types: Option<[ExprId; 4]>,
    mut retention: Option<&mut Retention>,
) -> Result<(bool, bool), super::normalization::HeadError> {
    let mut k = Kernel::new(environment, names, exprs, levels, budget, scope);
    k.quot_types = quot_types;
    let retain = retention.is_some() && Retention::eligible(&k, request, quot_types.is_some());
    // Borrow the disjoint State-owned stores. Even a panic leaves their
    // allocations reachable for retirement by the poisoned State.
    let mut graph = None;
    if retain && let Some(owner) = retention.as_deref_mut() {
        let (snapshot, judgments) = owner.stores_for_attempt();
        // Retention::eligible established immutable Safe, ordinary, non-quotient
        // scope. The lexical cursor starts disabled for all other attempts.
        if k.params.len() <= 8 {
            k.lexical.enable();
        }
        k.source_judgments = Some(judgments);
        graph = Some(snapshot);
    }
    let mut restored_graph = false;
    let result = (|| -> R<()> {
        let restored = if retain {
            graph
                .as_deref_mut()
                .ok_or(ResourceError::Invariant)?
                .restore(&mut k)?
        } else {
            false
        };
        restored_graph = restored;
        if !restored {
            k.init()?;
        }
        let tt = k.infer(request.ty, 0, 0, true)?;
        let s = k.sort_of(tt)?;
        if request.kind == Kind::Theorem && !k.is_zero(s)? {
            return no();
        }
        if let Some(value) = request.value {
            let tv = k.eval(request.ty, 0, 0)?;
            k.check_expr(value, tv, 0)?;
        }
        Ok(())
    })();
    // Only a completed attempt may stage a snapshot. Publication belongs to
    // State, after all attempt/session cleanup and declaration installation.
    let result = match result {
        // Only completed cold checking can earn initial admission. Copy work
        // starts inside capture below; an already earned graph may survive a
        // cheap consumer. A failed restore leaves restored_graph false.
        Ok(()) if retain && (restored_graph || k.steps >= CHARGE_BLOCK) => graph
            .ok_or(ResourceError::Invariant)
            .map_err(KErr::from)
            .and_then(|owner| owner.capture(&mut k)),
        other => other,
    };
    let wants_quot = k.wants_quot && quot_types.is_none();
    let steps = k.steps - k.charged;
    let reserved = k.reserved;
    #[cfg(feature = "introspection")]
    probe::report(
        request.name.0,
        &result,
        k.steps,
        [
            (
                "clo",
                k.clo_index.lookups,
                k.clo_index.hits,
                k.clo_index.off,
            ),
            (
                "val",
                k.val_index.lookups,
                k.val_index.hits,
                k.val_index.off,
            ),
            (
                "cell",
                k.cell_index.lookups,
                k.cell_index.hits,
                k.cell_index.off,
            ),
            (
                "envl",
                k.env_lossy.lookups,
                k.env_lossy.hits,
                k.env_lossy.off,
            ),
        ],
    );
    k.retire_arena();
    drop(k);
    let charge = budget.charge_work(steps);
    let release = budget.release(reserved);
    let finished = finish_attempt(result, charge, release, wants_quot);
    if !matches!(finished, Ok((true, _)))
        && let Some(owner) = retention
    {
        owner.abandon_source_judgments();
    }
    finished
}

/// All three operations have completed before selecting a failure. A cleanup
/// internal error must dominate every support/resource decline.
fn finish_attempt(
    result: R<()>,
    charge: Result<(), ResourceError>,
    release: Result<(), ResourceError>,
    wants_quot: bool,
) -> Result<(bool, bool), super::normalization::HeadError> {
    let operation = match result {
        Err(KErr::Resource(error)) => Some(error.into()),
        _ => None,
    };
    let unsupported = matches!(result, Err(KErr::LiteralArithmetic))
        .then_some(UseError::LiteralArithmetic.into());
    if let Some(error) = super::normalization::full::select_failure([
        operation,
        charge.err().map(Into::into),
        release.err().map(Into::into),
        unsupported,
    ]) {
        return Err(error);
    }
    // An escaped Abort cannot happen with the unlimited outer allowance; it
    // would only end this attempt, like any other incomplete route.
    Ok((matches!(result, Ok(())), wants_quot))
}

mod read_wide;

// Charged sizes (64-bit layout) of this module's stored types.
crate::resource::charged::charged! {
    ConstantSlot => 12,
    NatLit => 24,
    LInst => 16,
    ((u32, u32, u32, [u32; 8], [u32; 8]), (u32, [u32; 8])) => 112,
    ((u32, u32, u32, u32), u32) => 20,
    ((u32, [u32; 8], [u32; 8]), u32) => 72,
    ((u32, u64, u32), u32) => 24,
    (u32, u64) => 16,
    (u64, u32) => 16,
    ((u32, u32), bool) => 12,
    (u32, LevelId) => 8,
    ((u8, u32, u32), LevelId) => 16,
    ((u32, u32), LevelId) => 12,
    ((u64, [u32; 16]), u32) => 80,
    ((u32, u32), u32) => 12,
    ((u32, u32, u32), (u32, bool)) => 20,
    ((u32, u32, u32), u32) => 16,
    EnvNode => 12,
    Cell => 16,
    Meta => 12,
    Val => 20,
    Option<(NonZeroU32, (u32, u32, u32, u32, u32, u32), u32)> => 32,
    Option<(NonZeroU32, (u32, u32, u32, u32, u32, u32), ())> => 28,
    Option<(NonZeroU32, (u32, u32, u32), u32)> => 20,
    Option<(NonZeroU32, (u32, u32, u32, u32, u32), u32)> => 28,
    Option<(NonZeroU32, (u32, u32), ())> => 12,
    Option<(NonZeroU32, EnvKey, u32)> => 16,
    CInfo<'_> => 144,
    MemoSlot => 20,
}
