//! Bounded experiment: exact live-source binding topology, no results.
//! Each replay resolves this call's demanded replacements before construction.
//! Only immutable topology and scratch capacity survive; completed substitutions
//! are not cached across calls (the owner-agreed result-memo removal).
use super::*;
use crate::resource::SessionCacheBudget;
const RECORD_LIMIT: usize = 256;
const TABLE_LIMIT: usize = 8192;
const CACHE_LIMIT: usize = 1024 * 1024;
const BUILD_BYTES: usize = 35 * 1024;
const WINDOW: usize = 8;
#[derive(Clone, Copy)]
struct Record {
    source: ExprId,
    role: u32,
    operands: [u32; 3],
}
// Full-width roles never steal bits from expression handles or binder offsets.
const PRESERVE: u32 = 0;
const REPLACE: u32 = 1;
const LOWER: u32 = 2;
const APP: u32 = 3;
const LAMBDA: u32 = 4;
const PI: u32 = 5;
const LET: u32 = 6;
const PROJECTION: u32 = 7;
const HEAD_FIRST: u32 = 8;
const HEAD_NEXT: u32 = 9;
const SPINE_LIMIT: usize = 8;

pub(crate) struct HeadSpine {
    pub(crate) head: ExprId,
    // Innermost first; pending applications must be pushed in reverse order.
    arguments: [ExprId; SPINE_LIMIT],
    len: usize,
}
impl HeadSpine {
    pub(crate) fn arguments(&self) -> &[ExprId] {
        &self.arguments[..self.len]
    }
}
const _: () = assert!(size_of::<HeadSpine>() == 48);

const _: () = assert!(size_of::<Record>() == 20);
#[derive(Clone, Copy, Default)]
struct Entry {
    root: u32,
    cutoff: u32,
    len: u32,
    operation: u32,
    hash: u32,
    state: u32,
    start: u32,
    count: u32,
}
const _: () = assert!(size_of::<Entry>() == 32);
const _: () = assert!(TABLE_LIMIT * size_of::<Entry>() == 256 * 1024);
#[derive(Default)]
pub(crate) struct Cache {
    entries: Vec<Entry>,
    records: Vec<Record>,
    // Capacity only survives a call; live results belong to that call alone.
    workspace: Vec<ExprId>,
    // Per-call demanded-handle scan; capacity survives, contents never do.
    scan: Vec<u32>,
    used: usize,
}
const _: () = assert!(size_of::<Cache>() == 104);
/// Resolve each demanded replacement once, in the plan's original occurrence
/// order. Capacity survives for reuse, but each call clears the contents before
/// resolution; neither previous values nor a failed scan can authorize replay.
fn resolve_replacements(
    e: &mut Expressions,
    op: &Binding<'_>,
    rows: &[Record],
    scan: &mut Vec<u32>,
    b: &mut Budget,
) -> Result<(), ResourceError> {
    scan.clear();
    // One replacement per row at most; preserve the existing coarse charge and
    // one allocation attempt before invoking any Environment callback.
    b.charge_work(1)?;
    b.grow_vec(scan, rows.len())?;
    for row in rows {
        if row.role != REPLACE {
            continue;
        }
        let relative = row.operands[0];
        let handle = match op {
            Binding::Instantiate(a) => *a.get(relative as usize).ok_or(ResourceError::Invariant)?,
            Binding::Environment { len, lookup } if relative < *len => {
                let resolved = e.resolve_slot(lookup(relative, b)?, b)?;
                if e.get(resolved, b)?.loose_range() != 0 {
                    return Err(ResourceError::Invariant);
                }
                resolved
            }
            _ => return Err(ResourceError::Invariant),
        };
        scan.push(handle.0);
    }
    Ok(())
}

impl Cache {
    /// Only the plan table and record store consume session cache admission.
    /// Per-call scan/workspace capacity is charged to the ordinary budget.
    fn bytes(&self) -> usize {
        self.entries.capacity() * 32 + self.records.capacity() * 20
    }
    fn key(root: ExprId, cutoff: u32, op: Binding<'_>) -> Option<Entry> {
        let (operation, len) = match op {
            Binding::Instantiate(a) => (1, u32::try_from(a.len()).ok()?),
            Binding::Environment { len, .. } => (2, len),
            _ => return None,
        };
        // Same distribution-only finalizer discipline as Memo::key (exact
        // fields decide every hit): two packed words fold through the shared
        // finalizer instead of a four-round streaming hasher call.
        let low = u64::from(root.0) | (u64::from(cutoff) << 32);
        let high = u64::from(operation) | (u64::from(len) << 32);
        Some(Entry {
            root: root.0,
            cutoff,
            len,
            operation,
            hash: (mix64(low ^ mix64(high)) as u32).max(1),
            ..Entry::default()
        })
    }
    fn position(
        entries: &[Entry],
        key: Entry,
        b: &mut Budget,
    ) -> Result<Option<usize>, ResourceError> {
        if entries.is_empty() {
            return Ok(None);
        }
        for i in 0..WINDOW.min(entries.len()) {
            b.charge_work(1)?;
            let pos = (key.hash as usize + i) & (entries.len() - 1);
            let e = entries[pos];
            if e.state == 0
                || (e.hash == key.hash
                    && (e.root, e.cutoff, e.len, e.operation)
                        == (key.root, key.cutoff, key.len, key.operation))
            {
                return Ok(Some(pos));
            }
        }
        Ok(None)
    }
    fn grow_table(
        &mut self,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        let cap = (self.entries.len() * 2).clamp(16, TABLE_LIMIT);
        if cap == self.entries.len() {
            return Ok(());
        }
        let bytes = cap * 32;
        if self.bytes() + bytes > CACHE_LIMIT || !session.reserve(bytes as u64)? {
            return Ok(());
        }
        let mut next = Vec::new();
        let result = (|| {
            b.grow_vec(&mut next, cap)?;
            b.charge_work(cap as u64 + 1)?;
            next.resize(cap, Entry::default());
            let mut used = 0;
            for e in self.entries.iter().copied().filter(|e| e.state != 0) {
                if let Some(i) = Self::position(&next, e, b)? {
                    next[i] = e;
                    used += 1;
                }
            }
            Ok(used)
        })();
        match result {
            Ok(used) => {
                let old = std::mem::replace(&mut self.entries, next);
                let oldbytes = old.capacity() * 32;
                let a = release(old, b);
                let c = session.release(oldbytes as u64);
                a.and(c)?;
                self.used = used;
                Ok(())
            }
            Err(error) => Err(release_failed_growth(next, bytes, session, b, error)),
        }
    }
    fn publish(
        &mut self,
        rows: &[Record],
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<Option<u32>, ResourceError> {
        let required = self
            .records
            .len()
            .checked_add(rows.len())
            .ok_or(ResourceError::Counter)?;
        if required > self.records.capacity() {
            let cap = (self.records.capacity() * 2).max(required).max(8);
            let bytes = cap.checked_mul(20).ok_or(ResourceError::Counter)?;
            if self.bytes() + BUILD_BYTES + bytes > CACHE_LIMIT || !session.reserve(bytes as u64)? {
                return Ok(None);
            }
            let mut next = Vec::new();
            let result = (|| {
                b.grow_vec(&mut next, cap)?;
                b.charge_work(self.records.len() as u64 + 1)?;
                next.extend_from_slice(&self.records);
                Ok(())
            })();
            if let Err(error) = result {
                return Err(release_failed_growth(next, bytes, session, b, error));
            }
            let old = std::mem::replace(&mut self.records, next);
            let oldbytes = old.capacity() * 20;
            let a = release(old, b);
            let c = session.release(oldbytes as u64);
            a.and(c)?;
        }
        let start = u32::try_from(self.records.len()).map_err(|_| ResourceError::Counter)?;
        b.charge_work(rows.len() as u64 + 1)?;
        self.records.extend_from_slice(rows);
        Ok(Some(start))
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn bind(
        &mut self,
        e: &mut Expressions,
        root: ExprId,
        cutoff: u32,
        op: Binding<'_>,
        levels: &Levels,
        names: &impl LevelNames,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<ExprId, ExpressionError> {
        self.bind_mode::<false>(e, root, cutoff, op, levels, names, session, &mut None, b)
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn bind_head(
        &mut self,
        e: &mut Expressions,
        root: ExprId,
        op: Binding<'_>,
        levels: &Levels,
        names: &impl LevelNames,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<(ExprId, Option<HeadSpine>), ExpressionError> {
        let mut spine = None;
        let expression =
            self.bind_mode::<true>(e, root, 0, op, levels, names, session, &mut spine, b)?;
        Ok((expression, spine))
    }
    #[allow(clippy::too_many_arguments)]
    fn bind_mode<const HEAD: bool>(
        &mut self,
        e: &mut Expressions,
        root: ExprId,
        cutoff: u32,
        op: Binding<'_>,
        levels: &Levels,
        names: &impl LevelNames,
        session: &mut SessionCacheBudget,
        spine: &mut Option<HeadSpine>,
        b: &mut Budget,
    ) -> Result<ExprId, ExpressionError> {
        // Exact source validity precedes cache and argument shortcuts.
        let root_node = e.get(root, b)?;
        if let Binding::Instantiate(args) = op {
            u32::try_from(args.len()).map_err(|_| ExpressionError::NumericRange)?;
            b.charge_work(args.len() as u64)?;
            for arg in args {
                if e.get(*arg, b)?.loose_range() != 0 {
                    return Err(ResourceError::Invariant.into());
                }
            }
        }
        let Some(key) = Self::key(root, cutoff, op) else {
            return e.bind(root, cutoff, op, levels, names, b);
        };
        if HEAD && key.len == 0 {
            // A zero-length binding changes no node. Plan classification can
            // still mark an application with loose bounds, so return its
            // exact source handle instead of creating a pending spine.
            return Ok(root);
        }
        if root_node.loose_range() <= cutoff {
            return Ok(root);
        }
        if matches!(root_node.kind(e, levels, b)?, ExprKind::Bound(_)) {
            return e.bind_validated_mode::<true, true>(root, cutoff, op, levels, names, b);
        }
        if self.entries.is_empty() || self.used + 1 > self.entries.len() / 4 * 3 {
            self.grow_table(session, b)?;
        }
        let Some(slot) = Self::position(&self.entries, key, b)? else {
            return e.bind_validated_mode::<true, true>(root, cutoff, op, levels, names, b);
        };
        match self.entries[slot].state {
            0 => {
                self.entries[slot] = Entry { state: 1, ..key };
                self.used += 1;
            }
            1 => {
                self.entries[slot].state = 2; // Refusals are not repeatedly rebuilt.
                if self.bytes() + BUILD_BYTES <= CACHE_LIMIT
                    && session.reserve(BUILD_BYTES as u64)?
                {
                    let built = build(e, root, cutoff, key.len, levels, b);
                    let result = match built {
                        Ok(Some(rows)) => {
                            let published = self.publish(&rows, session, b);
                            let cleanup = release(rows, b);
                            cleanup.and(published)
                        }
                        Ok(None) => Ok(None),
                        Err(error) => {
                            session.release(BUILD_BYTES as u64)?;
                            return Err(error);
                        }
                    };
                    session.release(BUILD_BYTES as u64)?;
                    if let Some(start) = result? {
                        self.entries[slot].start = start;
                        self.entries[slot].count = self.records.len() as u32 - start;
                        self.entries[slot].state = 3;
                    }
                }
            }
            2 | 3 => {}
            _ => return Err(ResourceError::Invariant.into()),
        }
        let entry = self.entries[slot];
        if entry.state != 3 {
            return e.bind_validated_mode::<true, true>(root, cutoff, op, levels, names, b);
        }
        let start = entry.start as usize;
        let end = start
            .checked_add(entry.count as usize)
            .ok_or(ResourceError::Counter)?;
        let rows = self
            .records
            .get(start..end)
            .ok_or(ResourceError::Invariant)?;
        // Resolve current replacements exactly once before replay, including
        // every demanded Environment callback and its closedness check.
        let mut scan = std::mem::take(&mut self.scan);
        let resolved = resolve_replacements(e, &op, rows, &mut scan, b);
        self.scan = scan;
        if let Err(error) = resolved {
            self.scan.clear();
            return Err(error.into());
        }
        let result = replay_mode::<HEAD>(
            rows,
            e,
            &self.scan,
            levels,
            names,
            &mut self.workspace,
            spine,
            b,
        );
        self.scan.clear();
        result
    }
    pub(crate) fn retire(
        self,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        let bytes = self.bytes();
        let a = release(self.entries, b);
        let c = release(self.records, b);
        let d = session.release(bytes as u64);
        let workspace = release(self.workspace, b);
        let scan = release(self.scan, b);
        a.and(c).and(d).and(workspace).and(scan)
    }
}
struct Builder {
    rows: Vec<Record>,
    frames: Vec<Frame>,
    results: Vec<u32>,
    memo: Memo,
    started: usize,
}
impl Builder {
    fn frame(&mut self, f: Frame, b: &mut Budget) -> Result<(), ResourceError> {
        b.reserve_frames(1)?;
        let required = self.frames.len() + 1;
        if let Err(e) = b.grow_vec(&mut self.frames, required) {
            b.release_frames(1)?;
            return Err(e);
        }
        self.frames.push(f);
        Ok(())
    }
    fn result(&mut self, r: u32, b: &mut Budget) -> Result<(), ResourceError> {
        b.reserve_frames(1)?;
        let required = self.results.len() + 1;
        if let Err(e) = b.grow_vec(&mut self.results, required) {
            b.release_frames(1)?;
            return Err(e);
        }
        self.results.push(r);
        Ok(())
    }
    fn pop(&mut self, b: &mut Budget) -> Result<u32, ResourceError> {
        let r = self.results.pop().ok_or(ResourceError::Invariant)?;
        b.release_frames(1)?;
        Ok(r)
    }
    fn emit(
        &mut self,
        id: ExprId,
        role: u32,
        args: [u32; 3],
        b: &mut Budget,
    ) -> Result<u32, ResourceError> {
        let i = u32::try_from(self.rows.len()).map_err(|_| ResourceError::Counter)?;
        let required = self.rows.len() + 1;
        b.grow_vec(&mut self.rows, required)?;
        self.rows.push(Record {
            source: id,
            role,
            operands: args,
        });
        Ok(i)
    }
    fn run(
        &mut self,
        e: &Expressions,
        root: ExprId,
        cutoff: u32,
        len: u32,
        levels: &Levels,
        b: &mut Budget,
    ) -> Result<bool, ExpressionError> {
        self.frame(Frame::Visit(root, cutoff), b)?;
        while let Some(frame) = self.frames.pop() {
            b.release_frames(1)?;
            b.charge_work(1)?;
            b.observe(crate::resource::Event::MachineSteps, 1);
            match frame {
                Frame::Visit(id, offset) => {
                    let node = e.get(id, b)?;
                    let skip = node.loose_range() <= offset;
                    if !skip && let Some(index) = self.memo.get(id.0, offset, b)? {
                        self.result(index, b)?;
                        continue;
                    }
                    // Count before descent; duplicate demanded Bound occurrences each count.
                    if self.started == RECORD_LIMIT {
                        return Ok(false);
                    }
                    self.started += 1;
                    if skip {
                        let index = self.emit(id, PRESERVE, [0; 3], b)?;
                        self.result(index, b)?;
                        continue;
                    }
                    match node.kind(e, levels, b)? {
                        ExprKind::App(a, c) => {
                            self.frame(Frame::Finish(id, offset), b)?;
                            self.frame(Frame::Visit(c, offset), b)?;
                            self.frame(Frame::Visit(a, offset), b)?;
                        }
                        ExprKind::Lambda(_, d, r, _) | ExprKind::Pi(_, d, r, _) => {
                            let inner =
                                offset.checked_add(1).ok_or(ExpressionError::NumericRange)?;
                            self.frame(Frame::Finish(id, offset), b)?;
                            self.frame(Frame::Visit(r, inner), b)?;
                            self.frame(Frame::Visit(d, offset), b)?;
                        }
                        ExprKind::Let(_, t, v, r, _) => {
                            let inner =
                                offset.checked_add(1).ok_or(ExpressionError::NumericRange)?;
                            self.frame(Frame::Finish(id, offset), b)?;
                            self.frame(Frame::Visit(r, inner), b)?;
                            self.frame(Frame::Visit(v, offset), b)?;
                            self.frame(Frame::Visit(t, offset), b)?;
                        }
                        ExprKind::Projection(_, _, t) => {
                            self.frame(Frame::Finish(id, offset), b)?;
                            self.frame(Frame::Visit(t, offset), b)?;
                        }
                        kind => {
                            let (role, operand) = match kind {
                                ExprKind::Bound(i) if i >= offset && i - offset < len => {
                                    (REPLACE, i - offset)
                                }
                                ExprKind::Bound(i) if i >= offset && len != 0 => {
                                    (LOWER, i.checked_sub(len).ok_or(ResourceError::Invariant)?)
                                }
                                _ => (PRESERVE, 0),
                            };
                            let index = self.emit(id, role, [operand, 0, 0], b)?;
                            // Baseline demanded replacements bypass memo insertion; preserve calls.
                            if !matches!(kind,ExprKind::Bound(i) if i>=offset && i-offset<len) {
                                self.memo.insert(id.0, offset, index, b)?;
                            }
                            self.result(index, b)?;
                        }
                    }
                }
                Frame::Finish(id, offset) => {
                    let kind = e.get(id, b)?.kind(e, levels, b)?;
                    let mut args = [0; 3];
                    let (role, count) = match kind {
                        ExprKind::App(..) => (APP, 2),
                        ExprKind::Lambda(..) => (LAMBDA, 2),
                        ExprKind::Pi(..) => (PI, 2),
                        ExprKind::Let(..) => (LET, 3),
                        ExprKind::Projection(..) => (PROJECTION, 1),
                        _ => return Err(ResourceError::Invariant.into()),
                    };
                    for j in (0..count).rev() {
                        args[j] = self.pop(b)?;
                    }
                    // Each predecessor retains the exact original child source, even
                    // when memo sharing reuses a source at this checked offset.
                    let index = self.emit(id, role, args, b)?;
                    self.memo.insert(id.0, offset, index, b)?;
                    self.result(index, b)?;
                }
            }
        }
        let last = self.pop(b)?;
        if !self.results.is_empty() || last as usize + 1 != self.rows.len() {
            return Err(ResourceError::Invariant.into());
        }
        classify_head_spine(&mut self.rows, b)?;
        Ok(true)
    }
}
// Every marked non-root row has exactly one incoming edge, from the next
// marked function row. Thus no argument or binder can read an omitted result.
fn classify_head_spine(rows: &mut [Record], b: &mut Budget) -> Result<(), ResourceError> {
    if rows.is_empty() || rows.len() > RECORD_LIMIT {
        return Err(ResourceError::Invariant);
    }
    if rows.last().ok_or(ResourceError::Invariant)?.role != APP {
        return Ok(());
    }
    b.charge_work(rows.len() as u64 * 3 + SPINE_LIMIT as u64)?;
    let mut uses = [0u16; RECORD_LIMIT];
    for (index, row) in rows.iter().enumerate() {
        let count = match row.role {
            APP | LAMBDA | PI => 2,
            LET => 3,
            PROJECTION => 1,
            PRESERVE | REPLACE | LOWER => 0,
            _ => return Err(ResourceError::Invariant),
        };
        for &operand in &row.operands[..count] {
            if operand as usize >= index {
                return Err(ResourceError::Invariant);
            }
            uses[operand as usize] += 1; // At most 3 * RECORD_LIMIT edges.
        }
    }
    let mut spine = [0usize; SPINE_LIMIT];
    let mut count = 0;
    let mut index = rows.len() - 1;
    while rows[index].role == APP {
        if count == SPINE_LIMIT || (count != 0 && uses[index] != 1) {
            return Ok(());
        }
        spine[count] = index;
        count += 1;
        index = rows[index].operands[0] as usize;
    }
    for (position, &index) in spine[..count].iter().enumerate() {
        rows[index].role = if position + 1 == count {
            HEAD_FIRST
        } else {
            HEAD_NEXT
        };
    }
    Ok(())
}
fn build(
    e: &Expressions,
    root: ExprId,
    cutoff: u32,
    len: u32,
    levels: &Levels,
    b: &mut Budget,
) -> Result<Option<Vec<Record>>, ExpressionError> {
    b.charge_work(6)?;
    let mut s = Builder {
        rows: Vec::new(),
        frames: Vec::new(),
        results: Vec::new(),
        memo: Memo::default(),
        started: 0,
    };
    let result = s.run(e, root, cutoff, len, levels, b);
    let frames = s.frames.len() + s.results.len();
    let a = release(s.frames, b);
    let c = release(s.results, b);
    let d = release(s.memo.entries, b);
    let f = b.release_frames(frames);
    let cleanup = a.and(c).and(d).and(f);
    if let Err(error) = cleanup {
        release(s.rows, b)?;
        return Err(error.into());
    }
    match result {
        Ok(true) => Ok(Some(s.rows)),
        Ok(false) => {
            release(s.rows, b)?;
            Ok(None)
        }
        Err(error) => {
            release(s.rows, b)?;
            Err(error)
        }
    }
}
// A callback may unwind after producing some results. Clearing even then keeps
// every later invocation's readable prefix independent of previous bindings.
struct ClearWorkspace<'a>(&'a mut Vec<ExprId>);
impl Drop for ClearWorkspace<'_> {
    fn drop(&mut self) {
        self.0.clear();
    }
}
#[allow(clippy::too_many_arguments)]
fn replay_mode<const HEAD: bool>(
    rows: &[Record],
    e: &mut Expressions,
    replacements: &[u32],
    levels: &Levels,
    names: &impl LevelNames,
    workspace: &mut Vec<ExprId>,
    spine: &mut Option<HeadSpine>,
    b: &mut Budget,
) -> Result<ExprId, ExpressionError> {
    // By construction only completed prefixes are readable, including after a
    // prior failure or unwind. The cap also bounds retained capacity to 510 slots.
    if !workspace.is_empty() || rows.len() > RECORD_LIMIT {
        return Err(ResourceError::Invariant.into());
    }
    b.charge_work(3)?; // Includes fixed workspace cleanup/retirement prepayment.
    b.reserve_frames(rows.len())?;
    let reset = ClearWorkspace(workspace);
    let results = &mut *reset.0;
    // The demanded handles were resolved in row order for this exact call.
    let mut demanded = 0usize;
    let outcome = (|| {
        b.grow_vec(results, rows.len())?;
        for row in rows {
            b.charge_work(1)?;
            b.observe(crate::resource::Event::MachineSteps, 1);
            // Roles contain topology only. Replacement handles were resolved
            // once for this call and are consumed in row order.
            match row.role {
                PRESERVE => results.push(row.source),
                REPLACE => {
                    let r = ExprId(*replacements.get(demanded).ok_or(ResourceError::Invariant)?);
                    demanded += 1;
                    results.push(r);
                }
                LOWER => {
                    results.push(e.append(ExprKind::Bound(row.operands[0]), levels, names, b)?)
                }
                APP | HEAD_FIRST | HEAD_NEXT | LAMBDA | PI | LET | PROJECTION => {
                    let count = match row.role {
                        LET => 3,
                        PROJECTION => 1,
                        _ => 2,
                    };
                    let mut children = [row.source; 3];
                    let mut same = true;
                    for (i, child) in children.iter_mut().enumerate().take(count) {
                        let index = row.operands[i] as usize;
                        // Completed predecessors are strictly earlier records.
                        *child = *results.get(index).ok_or(ResourceError::Invariant)?;
                        let predecessor = rows.get(index).ok_or(ResourceError::Invariant)?;
                        same &= *child == predecessor.source;
                    }
                    if HEAD && row.role == HEAD_FIRST && e.get(children[0], b)?.loose_range() == 0 {
                        // The builder preserves every unaffected application
                        // verbatim. A marked edge contains a bound occurrence
                        // changed by this binding, so its source application
                        // could not be reused even if head exposure stalls.
                        *spine = Some(HeadSpine {
                            head: children[0],
                            arguments: [children[0]; SPINE_LIMIT],
                            len: 0,
                        });
                    }
                    if HEAD
                        && matches!(row.role, HEAD_FIRST | HEAD_NEXT)
                        && let Some(spine) = spine.as_mut()
                    {
                        if spine.len == SPINE_LIMIT || e.get(children[1], b)?.loose_range() != 0 {
                            return Err(ResourceError::Invariant.into());
                        }
                        spine.arguments[spine.len] = children[1];
                        spine.len += 1;
                        // Only the next marked function edge can consume this
                        // placeholder. The caller receives the completed spine.
                        results.push(spine.head);
                        continue;
                    }
                    if same {
                        results.push(row.source);
                        continue;
                    }
                    // Apps need no descriptor. Other changed composites retain
                    // every original scalar, including binder and Let metadata.
                    let kind = if matches!(row.role, APP | HEAD_FIRST | HEAD_NEXT) {
                        ExprKind::App(children[0], children[1])
                    } else {
                        match (row.role, e.get(row.source, b)?.kind(e, levels, b)?) {
                            (LAMBDA, ExprKind::Lambda(n, _, _, a)) => {
                                ExprKind::Lambda(n, children[0], children[1], a)
                            }
                            (PI, ExprKind::Pi(n, _, _, a)) => {
                                ExprKind::Pi(n, children[0], children[1], a)
                            }
                            (LET, ExprKind::Let(n, _, _, _, d)) => {
                                ExprKind::Let(n, children[0], children[1], children[2], d)
                            }
                            (PROJECTION, ExprKind::Projection(n, i, _)) => {
                                ExprKind::Projection(n, i, children[0])
                            }
                            _ => return Err(ResourceError::Invariant.into()),
                        }
                    };
                    results.push(e.append(kind, levels, names, b)?);
                }
                _ => return Err(ResourceError::Invariant.into()),
            }
        }
        results
            .last()
            .copied()
            .ok_or(ResourceError::Invariant.into())
    })();
    b.release_frames(rows.len())?;
    outcome
}

/// A failed cleanup reports through only when its cause is internal-error
/// class and the original error is not: an invariant break never hides behind
/// a decline, and a decline never outranks a real cause.
fn worse_resource_error(error: ResourceError, cleanup: Option<ResourceError>) -> ResourceError {
    use crate::resource::failure::FailureOutcome;
    if error.failure_report().outcome == FailureOutcome::InternalError {
        return error;
    }
    cleanup
        .filter(|e| e.failure_report().outcome == FailureOutcome::InternalError)
        .unwrap_or(error)
}

fn release_failed_growth<T>(
    next: Vec<T>,
    bytes: usize,
    session: &mut SessionCacheBudget,
    b: &mut Budget,
    error: ResourceError,
) -> ResourceError {
    let allocated = next.capacity() != 0;
    drop(next);
    let a = session.release(bytes as u64);
    let c = if allocated {
        b.release(bytes as u64)
    } else {
        Ok(())
    };
    worse_resource_error(error, a.and(c).err())
}
