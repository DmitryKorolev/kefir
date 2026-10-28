//! Completed semantic state owned by one validation::State.
//! Original syntax/name origin is the enclosing State's existing caller premise.
//! No TLS, borrowed metadata, ambient parameter slice or private staging escapes.
use super::*;

struct Owned {
    constant_slots: Vec<ConstantSlot>,
    constant_epoch: u32,
    const_by_canon: Map<u32, u32>,
    vals: Vec<Val>,
    meta: Vec<Meta>,
    cells: Vec<Cell>,
    envs: Vec<EnvNode>,
    locals: Vec<u32>,
    linsts: Vec<LInst>,
    linst_levels: Vec<LevelId>,
    linst_index: Map<u64, u32>,
    nats: Vec<NatLit>,
    let_marks: Vec<u64>,
    memo: Exact,
    clo_index: Lossy<(u32, u32, u32, u32, u32, u32), u32>,
    env_index: Map<(u32, u32, u32), u32>,
    env_lossy: Lossy<EnvKey, u32>,
    infer_cache: Map<(u32, u32, u32), (u32, bool)>,
    const_type: Map<(u32, u32), u32>,
    const_body: Map<(u32, u32), u32>,
    absent: Map<u32, u64>,
    arg_proof_status: Map<(u32, u32), bool>,
    rule_rhs: Map<(u32, u32, u32), u32>,
    level_subst: Map<(u32, u32), LevelId>,
    canon_of: Map<u32, LevelId>,
    level_index: Map<(u8, u32, u32), LevelId>,
    succ_of: Map<u32, LevelId>,
    eq_ok: Lossy<(u32, u32), ()>,
    val_index: Lossy<(u32, u32, u32, u32, u32), u32>,
    cell_index: Lossy<(u32, u32, u32), u32>,
    local_index: Map<(u32, u32), u32>,
    str_expansion: Map<u32, u32>,
    scratch: Vec<Scratch>,
    source_support: Map<u32, u64>,
    read_environments: Map<(u64, [u32; 16]), u32>,
    wide_read_environments: Map<read_wide::RepresentativeKey, u32>,
    read_plans: Map<u32, Option<[u64; 4]>>,
    large_read_nodes: Map<(u32, u32, u32), u32>,
    large_read_types: Map<read_large::LargeReadKey, u32>,
    alpha_types: Map<AlphaKey, (u32, [u32; 8])>,
    rename_ids: Map<(u32, [u32; 8], [u32; 8]), u32>,
    renamed_values: Map<(u32, u32), u32>,
    renamed_spines: Map<(u32, u32), u32>,
    renamed_envs: Map<(u32, u64, u32), u32>,
    nat_type: u32,
    nat_ctors: Option<(u32, u32, u32)>,
    derived: derived::Kept,
}
impl Owned {
    fn take(k: &mut Kernel<'_, '_>) -> Self {
        Self {
            constant_slots: std::mem::take(&mut k.constant_slots),
            constant_epoch: k.constant_epoch,
            const_by_canon: std::mem::take(&mut k.const_by_canon),
            vals: std::mem::take(&mut k.vals),
            meta: std::mem::take(&mut k.meta),
            cells: std::mem::take(&mut k.cells),
            envs: std::mem::take(&mut k.envs),
            locals: std::mem::take(&mut k.locals),
            linsts: std::mem::take(&mut k.linsts),
            linst_levels: std::mem::take(&mut k.linst_levels),
            linst_index: std::mem::take(&mut k.linst_index),
            nats: std::mem::take(&mut k.nats),
            let_marks: std::mem::take(&mut k.let_marks),
            memo: std::mem::take(&mut k.memo),
            clo_index: std::mem::take(&mut k.clo_index),
            env_index: std::mem::take(&mut k.env_index),
            env_lossy: std::mem::take(&mut k.env_lossy),
            infer_cache: std::mem::take(&mut k.infer_cache),
            const_type: std::mem::take(&mut k.const_type),
            const_body: std::mem::take(&mut k.const_body),
            absent: std::mem::take(&mut k.absent),
            arg_proof_status: std::mem::take(&mut k.arg_proof_status),
            rule_rhs: std::mem::take(&mut k.rule_rhs),
            level_subst: std::mem::take(&mut k.level_subst),
            canon_of: std::mem::take(&mut k.canon_of),
            level_index: std::mem::take(&mut k.level_index),
            succ_of: std::mem::take(&mut k.succ_of),
            eq_ok: std::mem::take(&mut k.eq_ok),
            val_index: std::mem::take(&mut k.val_index),
            cell_index: std::mem::take(&mut k.cell_index),
            local_index: std::mem::take(&mut k.local_index),
            str_expansion: std::mem::take(&mut k.str_expansion),
            scratch: std::mem::take(&mut k.scratch),
            source_support: std::mem::take(&mut k.source_support),
            read_environments: std::mem::take(&mut k.read_environments),
            wide_read_environments: std::mem::take(&mut k.wide_read_environments),
            read_plans: std::mem::take(&mut k.read_plans),
            large_read_nodes: std::mem::take(&mut k.large_read_nodes),
            large_read_types: std::mem::take(&mut k.large_read_types),
            alpha_types: std::mem::take(&mut k.alpha_types),
            rename_ids: std::mem::take(&mut k.rename_ids),
            renamed_values: std::mem::take(&mut k.renamed_values),
            renamed_spines: std::mem::take(&mut k.renamed_spines),
            renamed_envs: std::mem::take(&mut k.renamed_envs),
            nat_type: k.nat_type,
            nat_ctors: k.nat_ctors,
            derived: k.derived.take_kept(),
        }
    }
    fn install(self, k: &mut Kernel<'_, '_>) {
        k.constant_slots = self.constant_slots;
        // start checks overflow before ownership transfer; old view stamps are stale.
        k.constant_epoch = self.constant_epoch + 1;
        k.const_by_canon = self.const_by_canon;
        k.vals = self.vals;
        k.meta = self.meta;
        k.cells = self.cells;
        k.envs = self.envs;
        k.locals = self.locals;
        k.linsts = self.linsts;
        k.linst_levels = self.linst_levels;
        k.linst_index = self.linst_index;
        k.nats = self.nats;
        k.let_marks = self.let_marks;
        k.memo = self.memo;
        k.clo_index = self.clo_index;
        k.env_index = self.env_index;
        k.env_lossy = self.env_lossy;
        k.infer_cache = self.infer_cache;
        k.const_type = self.const_type;
        k.const_body = self.const_body;
        k.absent = self.absent;
        k.arg_proof_status = self.arg_proof_status;
        k.rule_rhs = self.rule_rhs;
        k.level_subst = self.level_subst;
        k.canon_of = self.canon_of;
        k.level_index = self.level_index;
        k.succ_of = self.succ_of;
        k.eq_ok = self.eq_ok;
        k.val_index = self.val_index;
        k.cell_index = self.cell_index;
        k.local_index = self.local_index;
        k.str_expansion = self.str_expansion;
        k.scratch = self.scratch;
        k.source_support = self.source_support;
        k.read_environments = self.read_environments;
        k.wide_read_environments = self.wide_read_environments;
        k.read_plans = self.read_plans;
        k.large_read_nodes = self.large_read_nodes;
        k.large_read_types = self.large_read_types;
        k.alpha_types = self.alpha_types;
        k.rename_ids = self.rename_ids;
        k.renamed_values = self.renamed_values;
        k.renamed_spines = self.renamed_spines;
        k.renamed_envs = self.renamed_envs;
        k.nat_type = self.nat_type;
        k.nat_ctors = self.nat_ctors;
        k.derived.install_kept(self.derived);
    }
}

struct Snapshot {
    state: Owned,
    levels: Vec<crate::syntax::levels::Level>,
    base: usize,
    before: usize,
    // Payload only. The persistent one-slot allocation belongs to Retention.
    reserved: u64,
}

const QUOTA: u64 = 16 << 20;

// Constant-size reachability evidence in test binaries only; no production
// state, event, charge or per-declaration telemetry is added.

/// At most one exclusive attempt can borrow this State-owned container.
/// Construction invariant: slot capacity/length are at most one; a populated
/// unpublished slot is pending and cannot be queried before State installs it.
/// The header stays charged while empty; payload charges move with its graph.
#[derive(Default)]
pub(in crate::check::environment) struct Retention {
    slot: Vec<Snapshot>,
    published: bool,
}
const _: () = assert!(size_of::<Retention>() == 32);

/// Evaluate every cleanup first. An internal failure dominates a resource
/// decline, matching the existing attempt/session cleanup selection.
pub(in crate::check::environment) fn select_cleanup<const N: usize>(
    results: [Result<(), ResourceError>; N],
) -> Result<(), ResourceError> {
    let errors = results.map(Result::err);
    let selected = errors
        .into_iter()
        .flatten()
        .find(|error| {
            error.failure_report().outcome
                == crate::resource::failure::FailureOutcome::InternalError
        })
        .or_else(|| errors.into_iter().flatten().next());
    selected.map_or(Ok(()), Err)
}

fn retire_snapshot(snapshot: Snapshot, budget: &mut Budget) -> Result<(), ResourceError> {
    let bytes = snapshot.reserved;
    // All other retained elements have constant-time destruction. Big literal
    // digit buffers need one deallocation per literal, charged once by count.
    let work = budget.charge_work(snapshot.state.nats.len() as u64 + 1);
    drop(snapshot);
    let release = budget.release(bytes);
    select_cleanup([work, release])
}

fn release(k: &mut Kernel<'_, '_>, bytes: u64) -> R<()> {
    let remaining = k
        .reserved
        .checked_sub(bytes)
        .ok_or(ResourceError::Invariant)?;
    k.b.release(bytes)?;
    k.reserved = remaining;
    Ok(())
}
fn drop_vec<T>(k: &mut Kernel<'_, '_>, values: Vec<T>) -> R<()> {
    let bytes = if values.is_empty() {
        0
    } else {
        logical(values.len()) * size_of::<T>()
    };
    drop(values);
    release(k, bytes as u64)
}
pub(super) fn drop_map<K, V>(k: &mut Kernel<'_, '_>, values: Map<K, V>) -> R<()> {
    let bytes = if values.is_empty() {
        0
    } else {
        map_bytes::<K, V>(logical(values.len()))
    };
    drop(values);
    release(k, bytes as u64)
}
fn drop_lossy<K: LossyKey, V: Copy>(k: &mut Kernel<'_, '_>, values: Lossy<K, V>) -> R<()> {
    let bytes = values.size * Lossy::<K, V>::SLOT;
    drop(values);
    release(k, bytes as u64)
}

impl Retention {
    pub(super) fn eligible(
        k: &Kernel<'_, '_>,
        request: &Request<'_>,
        quotient_retry: bool,
    ) -> bool {
        !quotient_retry
            && k.formation.is_none()
            && k.checked_context.is_none()
            && k.mode == Mode::Safe
            && request.safety == Safety::Safe
            && matches!(request.kind, Kind::Definition | Kind::Theorem)
            && k.levels.len() == k.level_end
    }

    fn allocate_header(&mut self, budget: &mut Budget) -> Result<(), ResourceError> {
        if self.slot.capacity() == 1 {
            return Ok(());
        }
        if self.slot.capacity() != 0 || !self.slot.is_empty() {
            return Err(ResourceError::Invariant);
        }
        budget.charge_work(1)?;
        let bytes = size_of::<Snapshot>() as u64;
        budget.reserve(bytes)?;
        let mut slot = Vec::new();
        if slot.try_reserve_exact(1).is_err() {
            let release = budget.release(bytes);
            return select_cleanup([Err(ResourceError::Allocation), release]);
        }
        if slot.capacity() != 1 {
            drop(slot);
            let release = budget.release(bytes);
            return select_cleanup([Err(ResourceError::Invariant), release]);
        }
        budget.observe(crate::resource::Event::Allocations, 1);
        self.slot = slot;
        Ok(())
    }

    pub(super) fn restore(&mut self, k: &mut Kernel<'_, '_>) -> R<bool> {
        if k.reserved != 0
            || self.slot.len() > 1
            || self.slot.capacity() > 1
            || self.published == self.slot.is_empty()
        {
            return Err(ResourceError::Invariant.into());
        }
        self.published = false; // clear before any fallible work or ownership move
        let Some(snapshot) = self.slot.pop() else {
            return Ok(false);
        };
        if snapshot.base != k.level_end
            || snapshot.before > k.before
            || snapshot.state.constant_epoch == u32::MAX
        {
            retire_snapshot(snapshot, k.b)?;
            return Ok(false);
        }
        let Snapshot {
            state,
            levels,
            base,
            before: _,
            reserved,
        } = snapshot;
        k.reserved = reserved;
        // Same State means the same syntax/name origin. Root universe scope was
        // checked by validation before entry. Exact explicit levels and typed
        // bindings, not ambient parameter-list positions, key retained facts.
        k.steps_by(levels.len() as u64)?;
        k.levels.restore_retained_nodes(base, &levels, k.b)?;
        drop_vec(k, levels)?;
        state.install(k);
        // Taking the graph ends its old attempt. Replayed generated levels
        // remain values only; subst_end stays the original source frontier.
        Ok(true)
    }

    pub(super) fn capture(&mut self, k: &mut Kernel<'_, '_>) -> R<()> {
        if k.markers != 0 || !k.binders.is_empty() || !k.free_values.is_empty() || k.wants_quot {
            return Ok(());
        }
        if !self.slot.is_empty() || self.published {
            return Err(ResourceError::Invariant.into());
        }
        let base = k.level_end;
        let count = k
            .levels
            .len()
            .checked_sub(base)
            .ok_or(ResourceError::Invariant)?;
        let level_bytes = if count == 0 {
            0
        } else {
            logical(count) * size_of::<crate::syntax::levels::Level>()
        };
        // Borrowed metadata and speculative/failed-route receipts never escape.
        let views = std::mem::take(&mut k.consts);
        drop_vec(k, views)?;
        let failures = std::mem::take(&mut k.args_fail);
        drop_lossy(k, failures)?;
        let comparisons = std::mem::take(&mut k.level_eq);
        drop_map(k, comparisons)?;
        let syntax = std::mem::take(&mut k.syn_ok);
        drop_lossy(k, syntax)?;
        let markers = std::mem::take(&mut k.marker_vals);
        drop_map(k, markers)?;
        // Only positive rule trees travel with the graph.
        k.keep_trees()?;
        // Count the persistent header exactly once, even before its allocation.
        if k.reserved
            .saturating_add(level_bytes as u64)
            .saturating_add(size_of::<Snapshot>() as u64)
            > QUOTA
        {
            return Ok(());
        }
        self.allocate_header(k.b)?;
        k.steps_by(count as u64)?;
        let mut levels = Vec::new();
        if count != 0 {
            room(k.b, &mut k.reserved, &mut levels, count)?;
            levels.extend_from_slice(k.levels.retained_nodes_since(base)?);
        }
        // No semantic operation may use k after this take; only attempt cleanup
        // follows. Every retained reference is original or inside this graph.
        let state = Owned::take(k);
        let reserved = std::mem::replace(&mut k.reserved, 0);
        self.slot.push(Snapshot {
            state,
            levels,
            base,
            before: k.before,
            reserved,
        });
        Ok(())
    }

    /// Called only after session cleanup, publication and checked-count update.
    /// No allocation, charge or other fallible operation follows installation.
    pub(in crate::check::environment) fn publish(&mut self) {
        self.published = !self.slot.is_empty();
    }

    /// Idempotent terminal retirement, including early justified rejection.
    /// Drop every owner before selecting errors; a resource failure proves no
    /// negative and can never leave enough state to resume checking.
    pub(in crate::check::environment) fn retire(
        &mut self,
        budget: &mut Budget,
    ) -> Result<(), ResourceError> {
        self.published = false;
        let mut slot = std::mem::take(&mut self.slot);
        let header = (slot.capacity() * size_of::<Snapshot>()) as u64;
        let invalid = slot.capacity() > 1 || slot.len() > 1;
        let snapshot = slot.pop();
        // The single-slot invariant is by construction; retain an internal
        // failure if a future edit violates it rather than dropping extra facts.
        let mut result = if invalid {
            Err(ResourceError::Invariant)
        } else {
            Ok(())
        };
        for extra in slot.drain(..) {
            let cleanup = retire_snapshot(extra, budget);
            result = select_cleanup([result, cleanup]);
        }
        drop(slot);
        if let Some(snapshot) = snapshot {
            let cleanup = retire_snapshot(snapshot, budget);
            result = select_cleanup([result, cleanup]);
        }
        let release = budget.release(header);
        select_cleanup([result, release])
    }
}
