//! Call-by-need evaluation, application and weak-head observation.

use super::values::NeutralHead;
use super::*;

impl<'e, 'w> Kernel<'e, 'w> {
    pub(super) fn force(&mut self, mut v: u32) -> R<u32> {
        loop {
            match self.vals[v as usize] {
                Val::Ind(t) => v = t,
                Val::Delayed { e, env, li } => {
                    let r = self.eval(e, env, li)?;
                    self.vals[v as usize] = Val::Ind(r);
                    v = r;
                }
                _ => return Ok(v),
            }
        }
    }
    /// A lazily evaluated argument; cheap forms are evaluated directly.
    #[inline(always)]
    pub(super) fn thunk(&mut self, e: ExprId, env: u32, li: u32) -> R<u32> {
        let node = self.exprs.get(e, self.b)?;
        let bound = node.bound_index();
        if let Some(index) = bound {
            // kind() would observe exactly this read; preserve diagnostics too.
            self.b.observe(crate::resource::Event::TableLookups, 1);
            return Ok(self.env_at(env, index)?.val);
        }
        self.thunk_general(e, env, li, node)
    }
    /// Same source/node identity as the caller. No fresh get or cache scope.
    #[inline(never)]
    fn thunk_general(&mut self, e: ExprId, env: u32, li: u32, node: Expression<'w>) -> R<u32> {
        // Variables and cheap forms first: they never need a thunk, and the
        // memo is consulted (once) only for delayed computations.
        if node.is_application() {
            // Delaying an application does not use its operands. Keep the
            // lookup observation made by kind() and decode them on demand.
            self.b.observe(crate::resource::Event::TableLookups, 1);
        } else {
            let kind = node.kind(self.exprs, self.levels, self.b)?;
            match kind {
                ExprKind::Bound(i) => return Ok(self.env_at(env, i)?.val),
                ExprKind::Sort(_)
                | ExprKind::Constant(..)
                | ExprKind::Lambda(..)
                | ExprKind::Pi(..)
                | ExprKind::Natural(_)
                | ExprKind::String(_) => return self.eval_decoded(e, env, li, node, kind),
                _ => {}
            }
        }
        let loose = node.loose_range();
        let exact = self.source_memo_key(e, node, env, loose, li);
        let (_, _, kt, k1, k2) = exact;
        let (cached, mut vacancy) = self.memo.probe(&exact);
        if let Some(v) = cached {
            return Ok(v);
        }
        // Only eligible ranges can produce a second key. The selected key
        // owns the recipe without a raw-environment alias.
        let mut mkey = exact;
        if kt == 3 && k2 == 0 && (3..=MAX_EVAL_READ_RANGE).contains(&loose) {
            let refined = self.evaluation_read_key(e, env, loose, node.has_free(), (kt, k1, k2))?;
            if refined != (kt, k1, k2) {
                mkey = (e.slot(), li, refined.0, refined.1, refined.2);
                let (cached, slot) = self.memo.probe(&mkey);
                if let Some(v) = cached {
                    return Ok(v);
                }
                vacancy = slot;
            }
        }
        let env = if loose == 0 { 0 } else { env };
        // Delayed values have no structural interner key.
        let v = self.push_fresh(Val::Delayed { e, env, li }, None)?;
        self.memo
            .insert_probed(mkey, v, vacancy, self.b, &mut self.reserved)?;
        Ok(v)
    }
    pub(super) fn eval(&mut self, e: ExprId, env: u32, li: u32) -> R<u32> {
        let node = self.exprs.get(e, self.b)?;
        let kind = node.kind(self.exprs, self.levels, self.b)?;
        self.eval_decoded(e, env, li, node, kind)
    }
    /// The decoded view borrows only the immutable expression store. It is
    /// consumed in this call, never retained in a value or across retirement.
    /// Construction contract: e, node and kind describe the same source slot
    /// in self.exprs; lifetimes alone do not prove their identity correspondence.
    #[inline(always)]
    fn eval_decoded(
        &mut self,
        e: ExprId,
        env: u32,
        li: u32,
        node: Expression<'w>,
        kind: ExprKind<'w>,
    ) -> R<u32> {
        let loose = node.loose_range();
        // Variables and closures need neither the memo nor a decode later.
        match kind {
            ExprKind::Bound(i) => {
                let v = self.env_at(env, i)?.val;
                return self.force(v);
            }
            ExprKind::Lambda(_, d, body, _) => {
                let c = Clo {
                    dom: d,
                    body,
                    env,
                    li,
                };
                return self.intern_closure(0, c, loose, self.source_eval_key(node, env, loose));
            }
            ExprKind::Pi(_, d, body, _) => {
                let c = Clo {
                    dom: d,
                    body,
                    env,
                    li,
                };
                return self.intern_closure(1, c, loose, self.source_eval_key(node, env, loose));
            }
            _ => {}
        }
        let exact = self.source_memo_key(e, node, env, loose, li);
        let (_, _, kt, k1, k2) = exact;
        let mut mkey = exact;
        let mut cached = self.memo.get(&exact);
        if cached.is_none() && kt == 3 && k2 == 0 && (3..=MAX_EVAL_READ_RANGE).contains(&loose) {
            let (kt, k1, k2) =
                self.evaluation_read_key(e, env, loose, node.has_free(), (kt, k1, k2))?;
            mkey = (e.slot(), li, kt, k1, k2);
            if mkey != exact {
                cached = self.memo.get(&mkey);
            }
        }
        let env = if loose == 0 { 0 } else { env };
        let mut pending = NONE;
        if let Some(v) = cached {
            match self.vals[v as usize] {
                // The cached thunk is this very evaluation: run it once and
                // redirect the thunk to the result.
                Val::Delayed { .. } => pending = v,
                _ => return self.force(v),
            }
        }
        self.enter()?;
        let r = self.eval_inner(e, env, li, kind);
        self.leave();
        let r = r?;
        if pending != NONE {
            // The memo already maps this key to the thunk, now redirected to
            // its value: no second write is needed.
            self.vals[pending as usize] = Val::Ind(r);
        } else {
            self.memo.insert(mkey, r, self.b, &mut self.reserved)?;
        }
        Ok(r)
    }
    pub(super) fn eval_inner(
        &mut self,
        e: ExprId,
        env: u32,
        li: u32,
        kind: ExprKind<'w>,
    ) -> R<u32> {
        match kind {
            ExprKind::Free(id) => self.checked_free(id),
            ExprKind::Bound(i) => {
                let v = self.env_at(env, i)?.val;
                self.force(v)
            }
            ExprKind::Sort(l) => {
                let l = self.subst_level(l, li)?;
                self.push(Val::Sort(l))
            }
            ExprKind::Constant(n, ls) => {
                let ci = self.const_info(n)?;
                // Common universe lists stay on the stack. Rare longer lists
                // use a charged temporary buffer without a fixed arity cap.
                if ls.len() != self.const_view(ci)?.params.len() {
                    return no();
                }
                if ls.len() > LEVEL_ARGS {
                    let li = self.wide_instance(ci, ls, li)?;
                    return self.push(Val::Const { ci, li, spine: 0 });
                }
                let mut buf = [LevelId::ZERO; LEVEL_ARGS];
                for (slot, &l) in buf.iter_mut().zip(ls) {
                    let l = self.subst_level(l, li)?;
                    *slot = self.canon_level(l)?;
                }
                let levels = &buf[..ls.len()];
                let li = self.intern_li(ci, levels)?;
                self.push(Val::Const { ci, li, spine: 0 })
            }
            ExprKind::App(first_f, first_a) => self.small_application(first_f, first_a, env, li),
            ExprKind::Lambda(_, d, body, _) => self.push(Val::Lam(Clo {
                dom: d,
                body,
                env,
                li,
            })),
            ExprKind::Pi(_, d, body, _) => self.push(Val::Pi(Clo {
                dom: d,
                body,
                env,
                li,
            })),
            ExprKind::Let(_, _, v, body, _) => {
                let v = self.thunk(v, env, li)?;
                self.mark_let(v)?;
                let env = self.env_push(env, v, NONE)?;
                self.eval(body, env, li)
            }
            ExprKind::Projection(s, idx, x) => {
                let sci = self.const_info(s)?;
                let x = self.thunk(x, env, li)?;
                self.push(Val::Proj { x, idx, sci })
            }
            ExprKind::Natural(bytes) => {
                let lit = parse_nat(bytes, self.b, &mut self.reserved)?;
                self.nat(lit)
            }
            ExprKind::String(_) => self.push(Val::Str(e)),
            _ => no(),
        }
    }
    // Same source argument order, decoded head and original thunk identities.
    // Stack-only until the ninth argument; spill owns/recycles its charged buffer.
    fn small_application(&mut self, first_f: ExprId, first_a: ExprId, env: u32, li: u32) -> R<u32> {
        let mut slots = [0u32; 8];
        let mut start = slots.len() - 1;
        slots[start] = first_a.slot();
        let mut head = first_f;
        loop {
            let node = self.exprs.get(head, self.b)?;
            if let Some((function, argument)) = node.application_operands(self.b) {
                if start == 0 {
                    // The spilled path gathers outermost arguments first.
                    slots.reverse();
                    return self.spilled_application(&slots, function, argument, env, li);
                }
                start -= 1;
                slots[start] = argument.slot();
                head = function;
            } else {
                let kind = node.kind(self.exprs, self.levels, self.b)?;
                let f = self.eval_decoded(head, env, li, node, kind)?;
                let args = &mut slots[start..];
                for slot in args.iter_mut() {
                    *slot = self.thunk(ExprId::from_stored_original(*slot), env, li)?;
                }
                return self.apply_many(f, args);
            }
        }
    }
    fn spilled_application(
        &mut self,
        prefix: &[u32],
        first_f: ExprId,
        first_a: ExprId,
        env: u32,
        li: u32,
    ) -> R<u32> {
        let mut args = self.scratch.pop().unwrap_or_default();
        args.clear();
        let res = (|| {
            self.scratch_room(&mut args, prefix.len() + 1)?;
            args.values.extend_from_slice(prefix);
            args.push(first_a.slot());
            let mut head = first_f;
            let (node, kind) = loop {
                let node = self.exprs.get(head, self.b)?;
                if let Some((function, argument)) = node.application_operands(self.b) {
                    self.scratch_room(&mut args, 1)?;
                    args.push(argument.slot());
                    head = function;
                } else {
                    break (node, node.kind(self.exprs, self.levels, self.b)?);
                }
            };
            let f = self.eval_decoded(head, env, li, node, kind)?;
            args.reverse();
            for slot in args.iter_mut() {
                *slot = self.thunk(ExprId::from_stored_original(*slot), env, li)?;
            }
            self.apply_many(f, &args)
        })();
        self.scratch_finish(res, [args])
    }
    /// Expand a string literal to `String.ofList [Char.ofNat c₁, …]` under the
    /// committed String certificate, as the existing route does.
    pub(super) fn expand_str(&mut self, e: ExprId) -> R<u32> {
        if let Some(&v) = self.str_expansion.get(&e.slot()) {
            return Ok(v);
        }
        let env = self.env;
        let Some([char_n, of_nat_n, nil_n, cons_n, of_list_n]) = env.string_symbols(
            self.before,
            self.formation,
            self.expression_end,
            self.exprs,
            self.levels,
            self.b,
        )?
        else {
            return no();
        };
        let ExprKind::String(bytes) =
            self.exprs
                .get(e, self.b)?
                .kind(self.exprs, self.levels, self.b)?
        else {
            return no();
        };
        let Ok(text) = std::str::from_utf8(bytes) else {
            return no();
        };
        self.b.charge_work(2 * bytes.len() as u64 + 32)?;

        let (char_ci, of_nat_ci, nil_ci, cons_ci, of_list_ci) = (
            self.const_info(char_n)?,
            self.const_info(of_nat_n)?,
            self.const_info(nil_n)?,
            self.const_info(cons_n)?,
            self.const_info(of_list_n)?,
        );
        let zero = self.canon_level(LevelId::ZERO)?;
        let list_li_nil = self.intern_li(nil_ci, &[zero])?;
        let list_li_cons = self.intern_li(cons_ci, &[zero])?;
        let char_ty = self.push(Val::Const {
            ci: char_ci,
            li: 0,
            spine: 0,
        })?;
        let nil_spine = self.cell(0, char_ty, 0)?;
        let mut tail = self.push(Val::Const {
            ci: nil_ci,
            li: list_li_nil,
            spine: nil_spine,
        })?;
        for c in text.chars().rev().map(u32::from) {
            self.step()?;
            let lit = self.nat(NatLit::Small(u64::from(c)))?;
            let ch_spine = self.cell(0, lit, 0)?;
            let ch = self.push(Val::Const {
                ci: of_nat_ci,
                li: 0,
                spine: ch_spine,
            })?;
            let s1 = self.cell(0, char_ty, 0)?;
            let s2 = self.cell(s1, ch, 0)?;
            let s3 = self.cell(s2, tail, 0)?;
            tail = self.push(Val::Const {
                ci: cons_ci,
                li: list_li_cons,
                spine: s3,
            })?;
        }
        let sp = self.cell(0, tail, 0)?;
        let v = self.push(Val::Const {
            ci: of_list_ci,
            li: 0,
            spine: sp,
        })?;
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.str_expansion,
            e.slot(),
            v,
        )?;
        Ok(v)
    }
    pub(super) fn str_type(&mut self) -> R<u32> {
        let env = self.env;
        let Some(t) = env.string_type(
            self.before,
            self.formation,
            self.expression_end,
            self.exprs,
            self.levels,
            self.b,
        )?
        else {
            return no();
        };
        self.eval(t, 0, 0)
    }
    /// Apply `f` to several arguments, peeling consecutive lambdas into one
    /// environment extension instead of building a closure per beta step.
    pub(super) fn apply_many(&mut self, mut f: u32, args: &[u32]) -> R<u32> {
        // Admit the known span once, before forcing or mutation.
        // The monotone index covers lambda peeling and remaining-spine loops;
        // nested reductions retain their own independent charges.
        let work = u64::try_from(args.len())
            .map_err(|_| ResourceError::Counter)?
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        self.application_span(work)?;
        let mut i = 0;
        while i < args.len() {
            f = self.force(f)?;
            match self.vals[f as usize] {
                Val::Lam(c) => {
                    let mut env = self.env_push(c.env, args[i], NONE)?;
                    i += 1;
                    let mut body = c.body;
                    while i < args.len() {
                        match self
                            .exprs
                            .get(body, self.b)?
                            .kind(self.exprs, self.levels, self.b)?
                        {
                            ExprKind::Lambda(_, _, inner, _) => {
                                env = self.env_push(env, args[i], NONE)?;
                                i += 1;
                                body = inner;
                            }
                            _ => break,
                        }
                    }
                    f = self.eval(body, env, c.li)?;
                }
                Val::Local { id, spine } => {
                    let mut spine = spine;
                    for &a in &args[i..args.len() - 1] {
                        spine = self.cell(spine, a, 0)?;
                    }
                    return self.extend_neutral(
                        NeutralHead::Local(id),
                        spine,
                        args[args.len() - 1],
                        0,
                    );
                }
                Val::Const { ci, li, spine } => {
                    let mut spine = spine;
                    for &a in &args[i..args.len() - 1] {
                        spine = self.cell(spine, a, 0)?;
                    }
                    return self.extend_neutral(
                        NeutralHead::Constant(ci, li),
                        spine,
                        args[args.len() - 1],
                        0,
                    );
                }
                // Project without unfolding the field: a certified head such
                // as `Nat.sub` must meet its arguments before any delta.
                Val::Proj { x, idx, sci } => {
                    let w = self.proj(x, idx, sci)?;
                    let w = self.force(w)?;
                    // The field may itself be another delayed projection.
                    // This is an additional reduction, not argument-span credit.
                    if matches!(self.vals[w as usize], Val::Proj { .. }) {
                        self.step()?;
                    }
                    f = w;
                }
                _ => return no(),
            }
        }
        Ok(f)
    }
    pub(super) fn apply(&mut self, mut f: u32, a: u32) -> R<u32> {
        f = self.force(f)?;
        loop {
            match self.vals[f as usize] {
                Val::Lam(c) => {
                    let env = self.env_push(c.env, a, NONE)?;
                    return self.eval(c.body, env, c.li);
                }
                Val::Local { id, spine } => {
                    return self.extend_neutral(NeutralHead::Local(id), spine, a, 0);
                }
                Val::Const { ci, li, spine } => {
                    return self.extend_neutral(NeutralHead::Constant(ci, li), spine, a, 0);
                }
                Val::Proj { x, idx, sci } => {
                    // As in apply_many, a reduced field may be another
                    // projection. Iterate rather than consuming Rust stack.
                    let w = self.proj(x, idx, sci)?;
                    f = self.force(w)?;
                    if matches!(self.vals[f as usize], Val::Proj { .. }) {
                        self.step()?;
                    }
                }
                _ => return no(),
            }
        }
    }
    /// Instantiate a binder value (function, Pi type or lambda type) at `a`.
    pub(super) fn instantiate(&mut self, f: u32, a: u32) -> R<u32> {
        let f = self.force(f)?;
        match self.vals[f as usize] {
            Val::Pi(c) => {
                let env = self.env_push(c.env, a, NONE)?;
                self.eval(c.body, env, c.li)
            }
            Val::LamTy(c) => {
                let dom = self.eval(c.dom, c.env, c.li)?;
                let env = self.env_push(c.env, a, dom)?;
                self.infer(c.body, env, c.li, false)
            }
            Val::Arrow { cod, .. } => Ok(cod),
            _ => self.apply(f, a),
        }
    }
    pub(super) fn binder_dom(&mut self, f: u32) -> R<u32> {
        match self.vals[f as usize] {
            Val::Pi(c) | Val::LamTy(c) | Val::Lam(c) => self.eval(c.dom, c.env, c.li),
            Val::Arrow { dom, .. } => Ok(dom),
            _ => no(),
        }
    }
    /// Field `idx` of `xs` when it is already a constructor application of `sci`.
    pub(super) fn ctor_field(&mut self, xs: u32, idx: u32, sci: u32) -> R<Option<u32>> {
        if let Val::Const { ci, spine, .. } = self.vals[xs as usize]
            && let Some((family, _)) = self.const_view(ci)?.ctor
            && family == self.const_view(sci)?.canon
            && let Some(ind) = self.const_view(sci)?.ind
        {
            let at = ind.nparams + idx;
            let len = self.cells[spine as usize].len;
            if at >= len {
                return Ok(None);
            }
            let mut s = spine;
            for _ in 0..(len - 1 - at) {
                s = self.cells[s as usize].prev;
            }
            let c = self.cells[s as usize];
            return Ok((c.tag == 0).then_some(c.item));
        }
        Ok(None)
    }
    pub(super) fn proj(&mut self, x: u32, idx: u32, sci: u32) -> R<u32> {
        let mut w = self.whnf(x)?;
        if let Val::Str(e) = self.vals[w as usize] {
            let x = self.expand_str(e)?;
            w = self.whnf(x)?;
        }
        if let Val::Const { ci, spine, .. } = self.vals[w as usize]
            && let Some((family, _)) = self.const_view(ci)?.ctor
            && family == self.const_view(sci)?.canon
        {
            let Some(ind) = self.const_view(sci)?.ind else {
                return no();
            };
            // Preserve the full projection-free-spine check. Admit its known
            // passes even when source normalization and scratch capacity are warm.
            self.steps_by(u64::from(self.cells[spine as usize].len) + 1)?;
            let args = self.spine_args(spine)?;
            let field = args.get((ind.nparams + idx) as usize).copied();
            self.recycle(args)?;
            return field.map_or_else(no, Ok);
        }
        match self.vals[w as usize] {
            Val::Local { id, spine } => {
                self.extend_neutral(NeutralHead::Local(id), spine, sci, idx + 1)
            }
            Val::Const { ci, li, spine } => {
                self.extend_neutral(NeutralHead::Constant(ci, li), spine, sci, idx + 1)
            }
            _ => no(),
        }
    }

    // ---------- weak head normalisation ----------

    pub(super) fn whnf_core(&mut self, v: u32) -> R<u32> {
        let v = self.force(v)?;
        let cached = self.meta[v as usize].core;
        if cached != NONE {
            return Ok(cached);
        }
        self.enter()?;
        let mut cur = v;
        let r = (|| loop {
            let value = self.vals[cur as usize];
            match value {
                Val::Const { ci, li, spine } if self.const_view(ci)?.rec.is_some() => {
                    match self.iota(ci, li, spine) {
                        Ok(Some(next)) => match self.force(next) {
                            Ok(n) => cur = n,
                            Err(e) => break Err(e),
                        },
                        Ok(None) => break Ok(cur),
                        Err(e) => break Err(e),
                    }
                }
                Val::Const { ci, spine, .. } if self.const_view(ci)?.quot.is_some() => {
                    match self.quot_reduce(ci, spine) {
                        Ok(Some(next)) => match self.force(next) {
                            Ok(n) => cur = n,
                            Err(e) => break Err(e),
                        },
                        Ok(None) => break Ok(cur),
                        Err(e) => break Err(e),
                    }
                }
                Val::Proj { x, idx, sci } => match self.whnf_core(x) {
                    Ok(xs) => match self.ctor_field(xs, idx, sci) {
                        Ok(Some(f)) => match self.force(f) {
                            Ok(n) => cur = n,
                            Err(e) => break Err(e),
                        },
                        Ok(None) => break Ok(cur),
                        Err(e) => break Err(e),
                    },
                    Err(e) => break Err(e),
                },
                _ => break Ok(cur),
            }
        })();
        self.leave();
        let r = r?;
        self.meta[v as usize].core = r;
        Ok(r)
    }
    pub(super) fn whnf(&mut self, v: u32) -> R<u32> {
        let v = self.force(v)?;
        let cached = self.meta[v as usize].whnf;
        if cached != NONE {
            return Ok(cached);
        }
        self.enter()?;
        let r = (|| -> R<u32> {
            let mut cur = self.whnf_core(v)?;
            loop {
                if let Some(next) = self.nat_reduce(cur)? {
                    cur = self.whnf_core(next)?;
                    continue;
                }
                let value = self.vals[cur as usize];
                match value {
                    Val::Const { ci, .. } if self.const_view(ci)?.delta.is_some() => {
                        // Reuse only a completed reduct of this exact value.
                        // Retains its denotation, explicit levels and
                        // typed bindings; no incomplete exposure is published.
                        cur = self.unfold_value(cur)?;
                    }
                    Val::Proj { x, idx, sci } => {
                        let next = self.proj(x, idx, sci)?;
                        cur = self.whnf_core(next)?;
                    }
                    _ => return Ok(cur),
                }
            }
        })();
        self.leave();
        let r = r?;
        self.meta[v as usize].whnf = r;
        Ok(r)
    }
    pub(super) fn unfold(&mut self, ci: u32, li: u32, spine: u32) -> R<u32> {
        let body = self.const_body(ci, li)?;
        self.replay(body, spine)
    }
    fn replay(&mut self, acc: u32, spine: u32) -> R<u32> {
        self.replay_from(acc, spine, 0)
    }
    /// Replay the cells strictly after `base` (up to the tip) onto `acc`.
    pub(super) fn replay_from(&mut self, mut acc: u32, spine: u32, base: u32) -> R<u32> {
        let mut items = self.spine_items_from(spine, base)?;
        let result = (|| {
            let mut start = 0;
            for at in 0..items.len() {
                // Invariant: unvisited entries are cell IDs; the completed
                // range start..at holds the original raw argument value IDs.
                // Nested application owns no borrow of the scratch pool.
                let c = self.cells[items[at] as usize];
                if c.tag == 0 {
                    items[at] = c.item;
                    continue;
                }
                acc = self.apply_many(acc, &items[start..at])?;
                acc = self.proj(acc, c.tag - 1, c.item)?;
                start = at + 1;
            }
            if start < items.len() {
                acc = self.apply_many(acc, &items[start..])?;
            }
            Ok(acc)
        })();
        items.clear();
        self.scratch_finish(result, [items])
    }
}
