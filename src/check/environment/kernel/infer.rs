//! Type inference and checking for terms and evaluated values.

use super::*;

mod keys;

impl<'e, 'w> Kernel<'e, 'w> {
    pub(super) fn sort_of(&mut self, ty: u32) -> R<LevelId> {
        let w = self.whnf(ty)?;
        match self.vals[w as usize] {
            Val::Sort(l) => Ok(l),
            _ => no(),
        }
    }
    pub(super) fn pi_like(&mut self, ty: u32) -> R<u32> {
        let w = self.whnf(ty)?;
        match self.vals[w as usize] {
            Val::Pi(_) | Val::LamTy(_) | Val::Arrow { .. } => Ok(w),
            _ => no(),
        }
    }
    // The caller restores the cursor before inspecting the body result. A
    // failed extension hides its entire subtree, including nested substitutions.
    fn enter_lexical(
        &mut self,
        parent: u32,
        env: u32,
        domain: ExprId,
        value: Option<ExprId>,
        binder: (ExprId, Expression<'w>),
        checked: bool,
    ) -> source_judgments::Cursor {
        let saved = self.lexical.cursor;
        if checked
            && self.markers == 0
            && self
                .lexical
                .can_extend(parent, self.binders.len(), value.is_none())
        {
            // Domain and let RHS are strict original children at the enclosing
            // depth; their free flags and loose ranges contribute unchanged.
            if (binder.0.slot() as usize) < self.expression_end
                && !binder.1.has_free()
                && binder.1.loose_range() <= u32::from(saved.depth)
            {
                // A let value is an earlier source record than its containing Let,
                // so its slot cannot equal the variable-frame sentinel u32::MAX.
                self.lexical.enter(
                    env,
                    self.binders.len(),
                    [domain.slot(), value.map_or(NONE, ExprId::slot)],
                );
                return saved;
            }
        }
        self.lexical.disable();
        saved
    }
    // With check=false, callers supply a well-typed-input/substitution premise;
    // this computes an intrinsic type and grants no checked-entry receipt.
    #[inline(always)]
    pub(super) fn infer(&mut self, e: ExprId, env: u32, li: u32, check: bool) -> R<u32> {
        let node = self.exprs.get(e, self.b)?;
        let env_key = if node.loose_range() == 0 { 0 } else { env };
        let key = (e.slot(), env_key, li);
        if let Some(&(t, checked)) = self.infer_cache.get(&key)
            && (checked || !check)
        {
            return Ok(t);
        }
        self.infer_miss(e, env, li, check, node, key)
    }
    // Construction contract: node is the unchanged source e read by infer,
    // and key is its original normalized environment/universe inference key.
    // All cache guards and the initial query precede this call; the original
    // miss work, errors, charges and publication order remain below.
    #[inline(never)]
    fn infer_miss(
        &mut self,
        e: ExprId,
        env: u32,
        li: u32,
        check: bool,
        node: Expression<'w>,
        key: (u32, u32, u32),
    ) -> R<u32> {
        // Only a prior completed positive judgment may provide the premise of
        // infer-only. No source-store handle or value is copied into this graph.
        if check
            && li == 0
            && node.is_application()
            && node.loose_range() != 0
            && let Some(frames) = self.lexical.active(env, self.binders.len())
        {
            let scope_ok = || {
                !node.has_free()
                    && (e.slot() as usize) < self.expression_end
                    && self.markers == 0
                    && node.loose_range() as usize <= frames.len()
            };
            if let Some(rows) = self.source_judgments.as_ref()
                && rows.open.might_match(e.slot())
                && scope_ok()
                && rows.open.contains(e.slot(), frames, self.params, self.b)?
            {
                return self.infer(e, env, 0, false);
            }
            let depth = frames.len();
            let start = self.steps;
            let ty = self.infer_miss_body(e, env, li, true, node, key)?;
            if self.steps - start >= source_judgments::OPEN_MIN_WORK
                && !node.has_free()
                && (e.slot() as usize) < self.expression_end
                && self.markers == 0
                && node.loose_range() as usize <= depth
                && let Some(frames) = self.lexical.active(env, self.binders.len())
                && let Some(rows) = self.source_judgments.as_mut()
            {
                rows.open.stage(e.slot(), frames, self.params, self.b)?;
            }
            return Ok(ty);
        }
        if !check
            || self.source_judgments.is_none()
            || li != 0
            || node.loose_range() != 0
            || node.has_free()
            || (e.slot() as usize) >= self.expression_end
        {
            return self.infer_miss_body(e, env, li, check, node, key);
        }
        let params = if node.has_param() { self.params } else { &[] };
        if self
            .source_judgments
            .as_ref()
            .is_some_and(|rows| rows.contains(e.slot(), params))
        {
            return self.infer(e, 0, 0, false);
        }
        let start = self.steps;
        let t = self.infer_miss_body(e, env, li, check, node, key)?;
        if self.steps - start >= source_judgments::MIN_WORK
            && let Some(rows) = &mut self.source_judgments
        {
            rows.stage(e.slot(), params, self.b)?;
        }
        Ok(t)
    }

    #[inline(always)]
    fn infer_miss_body(
        &mut self,
        e: ExprId,
        env: u32,
        li: u32,
        check: bool,
        node: Expression<'w>,
        key: (u32, u32, u32),
    ) -> R<u32> {
        let key_admitted = self.steps >= ALPHA_MIN_STEPS
            && (self.formation.is_none() || self.steps >= FORMATION_CONTEXT_KEY_MIN_STEPS);
        let large_key =
            if key_admitted && node.depth() != 0 && (9..=256).contains(&node.loose_range()) {
                self.large_type_key(e, env, li, check)?
            } else {
                None
            };
        if let Some(ref k) = large_key
            && let Some(&t) = self.large_read_types.get(k)
        {
            return Ok(t);
        }
        let alpha = if check && key_admitted && node.depth() != 0 {
            self.alpha_key(e, env, li, node.loose_range())?
        } else {
            None
        };
        if let Some((k, new)) = alpha
            && let Some(&(t, old)) = self.alpha_types.get(&k)
        {
            let rk = (k.2, old, new);
            let rn = match self.rename_ids.get(&rk) {
                Some(&n) => n,
                None => {
                    let n = self.rename_ids.len() as u32;
                    map_put(self.b, &mut self.reserved, &mut self.rename_ids, rk, n)?;
                    n
                }
            };
            match self.rename_value(t, rn, &old, &new, k.2) {
                Ok(v) => {
                    map_put(
                        self.b,
                        &mut self.reserved,
                        &mut self.infer_cache,
                        key,
                        (v, true),
                    )?;
                    return Ok(v);
                }
                Err(KErr::Unsupported) => {}
                Err(e) => return Err(e),
            }
        }
        self.enter()?;
        // Introspection event only; a no-op in production builds.
        self.b.observe(crate::resource::Event::Inferences, 1);
        let r = self.infer_inner(e, env, li, check, node);
        self.leave();
        let t = r?;
        if let Some(k) = large_key {
            map_put(self.b, &mut self.reserved, &mut self.large_read_types, k, t)?;
        }
        if let Some((key, ids)) = alpha {
            map_put(
                self.b,
                &mut self.reserved,
                &mut self.alpha_types,
                key,
                (t, ids),
            )?;
        }
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.infer_cache,
            key,
            (t, check),
        )?;
        Ok(t)
    }
    fn infer_inner(
        &mut self,
        e: ExprId,
        env: u32,
        li: u32,
        check: bool,
        node: Expression<'w>,
    ) -> R<u32> {
        // Construction contract: node is the same self.exprs slot e that the
        // inference wrapper read before its unchanged cache/checkedness probes.
        let kind = node.kind(self.exprs, self.levels, self.b)?;
        match kind {
            ExprKind::Free(id) => {
                let Some(context) = self.checked_context else {
                    return no();
                };
                let local = context.get(id, self.b)?;
                self.eval(local.ty(), 0, 0)
            }
            ExprKind::Bound(i) => {
                let n = self.env_at(env, i)?;
                if n.ty != NONE {
                    Ok(n.ty)
                } else {
                    self.infer_value(n.val)?.map_or_else(no, Ok)
                }
            }
            ExprKind::Sort(l) => {
                let l = self.subst_level(l, li)?;
                let s = self.succ(l)?;
                self.push(Val::Sort(s))
            }
            ExprKind::Constant(n, ls) => {
                let ci = self.const_info(n)?;
                if check {
                    let env = self.env;
                    env.check_use(
                        &ConstantUse {
                            name: n,
                            arguments: ls,
                            parameters: self.params,
                            before: self.before,
                            formation: self.formation,
                            mode: self.mode,
                            expression_end: self.expression_end,
                            level_end: self.level_end,
                        },
                        self.levels,
                        self.names,
                        self.b,
                    )
                    .or_else(|e| match e {
                        UseError::Resource(e) => Err(e.into()),
                        _ => no(),
                    })?;
                }
                // Common universe lists stay on the stack. Rare longer lists
                // use a charged temporary buffer without a fixed arity cap.
                if ls.len() != self.const_view(ci)?.params.len() {
                    return no();
                }
                if ls.len() > LEVEL_ARGS {
                    let cli = self.wide_instance(ci, ls, li)?;
                    return self.const_type(ci, cli);
                }
                let mut buf = [LevelId::ZERO; LEVEL_ARGS];
                for (slot, &l) in buf.iter_mut().zip(ls) {
                    let l = self.subst_level(l, li)?;
                    *slot = self.canon_level(l)?;
                }
                let levels = &buf[..ls.len()];
                let cli = self.intern_li(ci, levels)?;
                self.const_type(ci, cli)
            }
            ExprKind::App(..) => {
                let mut args = self.scratch.pop().unwrap_or_default();
                args.clear();
                let res = (|| {
                    let mut head = e;
                    let split_closed = node.loose_range() != 0 && self.source_judgments.is_some();
                    let mut head_env = env;
                    loop {
                        let part = self.exprs.get(head, self.b)?;
                        let ExprKind::App(f, a) = part.kind(self.exprs, self.levels, self.b)?
                        else {
                            break;
                        };
                        if split_closed && part.loose_range() == 0 && !part.has_free() {
                            // This proper prefix reads no binding in the current context.
                            // Its ordinary checkedness and universe premises still apply.
                            head_env = 0;
                            break;
                        }
                        self.scratch_room(&mut args, 1)?;
                        args.push(a.slot());
                        head = f;
                    }
                    let mut fty = self.infer(head, head_env, li, check)?;
                    // Syntactic Pi telescope. `pending` is a Pi whose
                    // closure was never built: it denotes exactly the Pi value
                    // `instantiate` would return (evaluating a syntactic Pi
                    // gives that closure, and a Pi closure is its own weak head
                    // normal form). Private loop state, never published.
                    let mut pending: Option<Clo> = None;
                    for i in (0..args.len()).rev() {
                        let a = ExprId::from_stored_original(args[i]);
                        let pi = match pending.take() {
                            Some(c) => c,
                            None => {
                                let w = self.pi_like(fty)?;
                                match self.vals[w as usize] {
                                    Val::Pi(c) => c,
                                    // Lambda types and arrows: the ordinary rule.
                                    _ => {
                                        if check {
                                            let dom = self.binder_dom(w)?;
                                            self.check_expr(a, dom, env)?;
                                        }
                                        let av = self.thunk(a, env, li)?;
                                        fty = self.instantiate(w, av)?;
                                        continue;
                                    }
                                }
                            }
                        };
                        if check {
                            let dom = self.eval(pi.dom, pi.env, pi.li)?;
                            self.check_expr(a, dom, env)?;
                        }
                        let av = self.thunk(a, env, li)?;
                        let bound = self.env_push(pi.env, av, NONE)?;
                        if i != 0
                            && let ExprKind::Pi(_, dom, body, _) = self
                                .exprs
                                .get(pi.body, self.b)?
                                .kind(self.exprs, self.levels, self.b)?
                        {
                            pending = Some(Clo {
                                dom,
                                body,
                                env: bound,
                                li: pi.li,
                            });
                        } else {
                            fty = self.eval(pi.body, bound, pi.li)?;
                        }
                    }
                    // The last argument always evaluates its codomain.
                    debug_assert!(pending.is_none());
                    Ok(fty)
                })();
                self.scratch_finish(res, [args])
            }
            ExprKind::Lambda(_, d, body, _) => {
                if check {
                    let dt = self.infer(d, env, li, true)?;
                    self.sort_of(dt)?;
                    let dv = self.eval(d, env, li)?;
                    let x = self.open_local(dv)?;
                    let bt = self.env_push(env, x, dv).and_then(|env2| {
                        let scope = self.enter_lexical(env, env2, d, None, (e, node), li == 0);
                        let result = self.infer(body, env2, li, true);
                        self.lexical.cursor = scope;
                        result
                    });
                    self.close_local();
                    let bt = bt?;
                    if !self.mentions(bt, x)? {
                        return self.push(Val::Arrow { dom: dv, cod: bt });
                    }
                }
                let loose = self.exprs.get(e, self.b)?.loose_range();
                let c = Clo {
                    dom: d,
                    body,
                    env,
                    li,
                };
                self.push_clo(2, c, loose)
            }
            ExprKind::Pi(_, d, body, _) => {
                let dt = self.infer(d, env, li, check)?;
                let u = self.sort_of(dt)?;
                let dv = self.eval(d, env, li)?;
                let x = self.open_local(dv)?;
                let bt = self.env_push(env, x, dv).and_then(|env2| {
                    let scope = self.enter_lexical(env, env2, d, None, (e, node), check && li == 0);
                    let result = self.infer(body, env2, li, check);
                    self.lexical.cursor = scope;
                    result
                });
                let bt = bt.and_then(|bt| self.sort_of(bt));
                self.close_local();
                let v = bt?;
                let l = self.imax(u, v)?;
                self.push(Val::Sort(l))
            }
            ExprKind::Let(_, t, v, body, _) => {
                if check {
                    let tt = self.infer(t, env, li, true)?;
                    self.sort_of(tt)?;
                }
                let tv = self.eval(t, env, li)?;
                if check {
                    self.check_expr(v, tv, env)?;
                }
                let vv = self.thunk(v, env, li)?;
                self.mark_let(vv)?;
                let env2 = self.env_push(env, vv, tv)?;
                let scope = self.enter_lexical(env, env2, t, Some(v), (e, node), check && li == 0);
                let result = self.infer(body, env2, li, check);
                self.lexical.cursor = scope;
                result
            }
            ExprKind::Projection(s, idx, x) => {
                let sci = self.const_info(s)?;
                let xt = self.infer(x, env, li, check)?;
                let xv = self.thunk(x, env, li)?;
                self.proj_type(xv, xt, idx, sci, check)
            }
            ExprKind::Natural(_) => self.nat_type(),
            ExprKind::String(_) => self.str_type(),
            _ => no(),
        }
    }
    /// A checked constructor domain headed by a fully applied inductive with
    /// literal result sort Prop is a proposition for every term and universe
    /// substitution. The one positive entry lives only for this telescope walk.
    pub(super) fn raw_prop_field(
        &mut self,
        mut head: ExprId,
        last: &mut Option<(ExprId, u32)>,
    ) -> R<bool> {
        let mut arity = 0;
        let (name, universes) = loop {
            self.step()?;
            if *last == Some((head, arity)) {
                return Ok(true);
            }
            match self
                .exprs
                .get(head, self.b)?
                .kind(self.exprs, self.levels, self.b)?
            {
                ExprKind::App(f, _) if arity < SMALL_SPINE as u32 => {
                    arity += 1;
                    head = f;
                }
                ExprKind::Constant(n, us) => break (n, us.len()),
                _ => return Ok(false),
            }
        };
        let ci = match self.const_info(name) {
            Ok(ci) => ci,
            Err(KErr::Unsupported) => return Ok(false),
            Err(e) => return Err(e),
        };
        let info = *self.const_view(ci)?;
        let (Some(ind), Some(mut ty)) = (info.ind, info.ty) else {
            return Ok(false);
        };
        if info.params.len() != universes || ind.nparams.checked_add(ind.nidx) != Some(arity) {
            return Ok(false);
        }
        for _ in 0..arity {
            self.step()?;
            let ExprKind::Pi(_, _, body, _) =
                self.exprs
                    .get(ty, self.b)?
                    .kind(self.exprs, self.levels, self.b)?
            else {
                return Ok(false);
            };
            ty = body;
        }
        let proven = matches!(self.exprs.get(ty, self.b)?.kind(self.exprs, self.levels, self.b)?, ExprKind::Sort(level) if level == LevelId::ZERO);
        if proven {
            *last = Some((head, arity));
        }
        Ok(proven)
    }

    /// Every consumed field has separately passed the Prop guard. Extend the
    /// actual constructor closure with the projection of the same scrutinee;
    /// reductions in a dependent field can subsequently force this value.
    pub(super) fn proof_field_prefix(
        &mut self,
        t: u32,
        xv: u32,
        sci: u32,
        selected: u32,
    ) -> R<(u32, u32)> {
        let binder = self.pi_like(t)?;
        let Val::Pi(mut c) = self.vals[binder as usize] else {
            return Ok((0, binder));
        };
        let mut last = None;
        let mut skipped = 0;
        while skipped < selected {
            let ExprKind::Pi(_, dom, body, _) =
                self.exprs
                    .get(c.body, self.b)?
                    .kind(self.exprs, self.levels, self.b)?
            else {
                break;
            };
            if !self.raw_prop_field(c.dom, &mut last)? {
                break;
            }
            let field = self.push(Val::Proj {
                x: xv,
                idx: skipped,
                sci,
            })?;
            c = Clo {
                dom,
                body,
                env: self.env_push(c.env, field, NONE)?,
                li: c.li,
            };
            skipped += 1;
        }
        if skipped == 0 {
            Ok((0, binder))
        } else {
            Ok((skipped, self.push(Val::Pi(c))?))
        }
    }

    pub(super) fn proj_type(
        &mut self,
        xv: u32,
        xt: u32,
        idx: u32,
        sci: u32,
        check: bool,
    ) -> R<u32> {
        let w = self.whnf(xt)?;
        let Val::Const { ci, li, spine } = self.vals[w as usize] else {
            return no();
        };
        if ci != sci {
            return no();
        }
        let Some(ind) = self.const_view(ci)?.ind else {
            return no();
        };
        // Lean types a projection of any one-constructor family without
        // indices, recursive or not; only eta-like rules need `structure_like`.
        if ind.ctors.len() != 1 || ind.nidx != 0 || idx >= ind.ctors[0].num_fields {
            return no();
        }
        // A structure whose sort does not reduce to a Sort is left to the
        // existing checker (lean4#14807). Out of a proposition, only
        // proof fields may be projected; every earlier field is required to be a
        // proof too, a conservative superset of the fields the type depends on.
        let prop = match self.prop_status(w)? {
            Some(p) => p,
            None if check => return no(),
            None => false,
        };
        let params = self.spine_args(spine)?;
        if params.len() != ind.nparams as usize {
            self.recycle(params)?;
            return no();
        }
        let res = (|| {
            let cci = self.const_info(ind.ctors[0].constructor)?;
            let cli = self.rebind_instance(cci, li)?;
            let mut t = self.const_type(cci, cli)?;
            for &p in params.iter() {
                let pw = self.pi_like(t)?;
                t = self.instantiate(pw, p)?;
            }
            let mut start = 0;
            // The source certificate is the installed constructor declaration.
            // Keep all staged checking on its original semantic path.
            if check && prop && idx >= 4 && self.formation.is_none() {
                (start, t) = self.proof_field_prefix(t, xv, sci, idx)?;
            }
            for j in start..idx {
                let pw = self.pi_like(t)?;
                if check && prop {
                    let fd = self.binder_dom(pw)?;
                    if self.prop_status(fd)? != Some(true) {
                        return no();
                    }
                }
                // The constructor telescope takes the preceding field itself.
                // Its type may never demand the field's normal form.
                let f = if self.meta[xv as usize].whnf != NONE
                    || matches!(self.vals[xv as usize], Val::Local { .. })
                {
                    self.proj(xv, j, sci)?
                } else {
                    self.push(Val::Proj { x: xv, idx: j, sci })?
                };
                t = self.instantiate(pw, f)?;
            }
            let pw = self.pi_like(t)?;
            let field = self.binder_dom(pw)?;
            if check && prop && self.prop_status(field)? != Some(true) {
                return no();
            }
            Ok(field)
        })();
        self.scratch_finish(res, [params])
    }
    pub(super) fn check_expr(&mut self, e: ExprId, ty: u32, env: u32) -> R<()> {
        self.enter()?;
        let r = self.check_inner(e, ty, env);
        self.leave();
        r
    }
    fn check_inner(&mut self, e: ExprId, ty: u32, env: u32) -> R<()> {
        let node = self.exprs.get(e, self.b)?;
        let kind = node.kind(self.exprs, self.levels, self.b)?;
        match kind {
            ExprKind::Lambda(_, d, body, _) => {
                let loose = self.exprs.get(e, self.b)?.loose_range();
                let key = (e.slot(), if loose == 0 { 0 } else { env }, 0);
                // A lambda already checked in this environment (DAG sharing)
                // only needs its recorded type compared with this one.
                let seen = matches!(self.infer_cache.get(&key), Some(&(_, true)));
                let w = self.whnf(ty)?;
                if !seen
                    && matches!(
                        self.vals[w as usize],
                        Val::Pi(_) | Val::LamTy(_) | Val::Arrow { .. }
                    )
                {
                    let dt = self.infer(d, env, 0, true)?;
                    self.sort_of(dt)?;
                    let dv = self.eval(d, env, 0)?;
                    let pd = self.binder_dom(w)?;
                    if !self.defeq(dv, pd)? {
                        return no();
                    }
                    let x = self.open_local(dv)?;
                    let r = self.instantiate(w, x).and_then(|cod| {
                        let env2 = self.env_push(env, x, dv)?;
                        let scope = self.enter_lexical(env, env2, d, None, (e, node), true);
                        let result = self.check_expr(body, cod, env2);
                        self.lexical.cursor = scope;
                        result
                    });
                    self.close_local();
                    r?;
                    // The body is checked under a fresh local of this domain,
                    // so the lambda's own type is a checked inference result.
                    let lt = self.push(Val::LamTy(Clo {
                        dom: d,
                        body,
                        env: key.1,
                        li: 0,
                    }))?;
                    map_put(
                        self.b,
                        &mut self.reserved,
                        &mut self.infer_cache,
                        key,
                        (lt, true),
                    )?;
                    return Ok(());
                }
            }
            ExprKind::Let(_, t, v, body, _) => {
                let tt = self.infer(t, env, 0, true)?;
                self.sort_of(tt)?;
                let tv = self.eval(t, env, 0)?;
                self.check_expr(v, tv, env)?;
                // Private P2 screen: a completed judgment for this closed source
                // is preserved by the unused let binding. Exact type identity
                // supplies conversion; no expected type becomes an inferred fact.
                // Open source must still be checked after shifting the context.
                if body == v && tv == ty && self.exprs.get(v, self.b)?.loose_range() == 0 {
                    return Ok(());
                }
                let vv = self.thunk(v, env, 0)?;
                self.mark_let(vv)?;
                let env2 = self.env_push(env, vv, tv)?;
                let scope = self.enter_lexical(env, env2, t, Some(v), (e, node), true);
                let result = self.check_expr(body, ty, env2);
                self.lexical.cursor = scope;
                return result;
            }
            _ => {}
        }
        let t = self.infer(e, env, 0, true)?;
        if self.defeq(t, ty)? { Ok(()) } else { no() }
    }
    #[inline]
    pub(super) fn cached_type(&self, v: u32) -> u32 {
        let Some(&page) = self.type_cache.directory.get((v >> 8) as usize) else {
            return NONE;
        };
        if page == 0 {
            return NONE;
        }
        // Published offsets own a complete initialized page; no absent page
        // or out-of-scope value can supply a completed cached type.
        self.type_cache.values[(page - 1) as usize + (v & 255) as usize]
    }
    pub(super) fn cache_type(&mut self, v: u32, ty: u32) -> R<()> {
        if v as usize >= self.vals.len() {
            return Err(ResourceError::Invariant.into());
        }
        let index = (v >> 8) as usize;
        if self.type_cache.directory.len() <= index {
            let extra = index + 1 - self.type_cache.directory.len();
            room(
                self.b,
                &mut self.reserved,
                &mut self.type_cache.directory,
                extra,
            )?;
            self.type_cache.directory.resize(index + 1, 0);
        }
        if self.type_cache.directory[index] == 0 {
            let start = self.type_cache.values.len();
            let end = start.checked_add(256).ok_or(ResourceError::Counter)?;
            let page = u32::try_from(start.checked_add(1).ok_or(ResourceError::Counter)?)
                .map_err(|_| ResourceError::Counter)?;
            room(self.b, &mut self.reserved, &mut self.type_cache.values, 256)?;
            self.type_cache.values.resize(end, NONE);
            // Publish only a completely initialized page after every fallible
            // reservation/allocation; the type fact itself is already complete.
            self.type_cache.directory[index] = page;
        }
        let at = (self.type_cache.directory[index] - 1) as usize + (v & 255) as usize;
        self.type_cache.values[at] = ty;
        Ok(())
    }
    /// The type of a value, when it can be computed without checking.
    pub(super) fn infer_value(&mut self, v: u32) -> R<Option<u32>> {
        let v = self.force(v)?;
        let cached = self.cached_type(v);
        if cached != NONE {
            return Ok(Some(cached));
        }
        let t = match self.vals[v as usize] {
            Val::Sort(l) => {
                let s = self.succ(l)?;
                self.push(Val::Sort(s))?
            }
            Val::Nat(_) => self.nat_type()?,
            Val::Str(_) => self.str_type()?,
            Val::Lam(c) => self.push(Val::LamTy(c))?,
            Val::Pi(c) => {
                let dt = self.infer(c.dom, c.env, c.li, false)?;
                let u = self.sort_of(dt)?;
                let dv = self.eval(c.dom, c.env, c.li)?;
                let x = self.open_local(dv)?;
                let env2 = self.env_push(c.env, x, dv)?;
                let bt = self
                    .infer(c.body, env2, c.li, false)
                    .and_then(|bt| self.sort_of(bt));
                self.close_local();
                let w = bt?;
                let l = self.imax(u, w)?;
                self.push(Val::Sort(l))?
            }
            Val::LamTy(c) => {
                // Sort of `Π x : dom, typeof(body)`.
                let dt = self.infer(c.dom, c.env, c.li, false)?;
                let u = self.sort_of(dt)?;
                let dv = self.eval(c.dom, c.env, c.li)?;
                let x = self.open_local(dv)?;
                let env2 = self.env_push(c.env, x, dv)?;
                let bs = self
                    .infer(c.body, env2, c.li, false)
                    .and_then(|bt| self.infer_value(bt));
                self.close_local();
                let Some(bs) = bs? else {
                    return Ok(None);
                };
                let w = self.sort_of(bs)?;
                let l = self.imax(u, w)?;
                self.push(Val::Sort(l))?
            }
            Val::Arrow { dom, cod } => {
                let (Some(ds), Some(cs)) = (self.infer_value(dom)?, self.infer_value(cod)?) else {
                    return Ok(None);
                };
                let u = self.sort_of(ds)?;
                let w = self.sort_of(cs)?;
                let l = self.imax(u, w)?;
                self.push(Val::Sort(l))?
            }
            Val::Local { id, spine } => {
                let t = self.locals[id as usize];
                match self.spine_type(t, spine, |s, sp| s.push(Val::Local { id, spine: sp }))? {
                    Some(t) => t,
                    None => return Ok(None),
                }
            }
            Val::Const { ci, li, spine } => {
                let t = self.const_type(ci, li)?;
                match self.spine_type(t, spine, |s, sp| s.push(Val::Const { ci, li, spine: sp }))? {
                    Some(t) => t,
                    None => return Ok(None),
                }
            }
            Val::Proj { x, idx, sci } => {
                let Some(xt) = self.infer_value(x)? else {
                    return Ok(None);
                };
                match self.proj_type(x, xt, idx, sci, false) {
                    Ok(t) => t,
                    Err(KErr::Unsupported) => return Ok(None),
                    Err(e) => return Err(e),
                }
            }
            _ => return Ok(None),
        };
        self.cache_type(v, t)?;
        Ok(Some(t))
    }
    fn spine_type(
        &mut self,
        head_ty: u32,
        spine: u32,
        rebuild: impl Fn(&mut Self, u32) -> R<u32>,
    ) -> R<Option<u32>> {
        let items = self.spine_items(spine)?;
        let mut t = head_ty;
        let mut res = Ok(Some(()));
        for &s in &items {
            let c = self.cells[s as usize];
            let step = if c.tag == 0 {
                self.pi_like(t).and_then(|w| self.instantiate(w, c.item))
            } else {
                let prefix = c.prev;
                rebuild(self, prefix).and_then(|sv| self.proj_type(sv, t, c.tag - 1, c.item, false))
            };
            match step {
                Ok(n) => t = n,
                Err(KErr::Unsupported) => {
                    res = Ok(None);
                    break;
                }
                Err(e) => {
                    res = Err(e);
                    break;
                }
            }
        }
        self.scratch_finish(res.map(|o| o.map(|()| t)), [items])
    }
    /// Whether a type is a proposition. `None` when its sort is not known to
    /// reduce to a `Sort` (lean4#14807): a stuck sort is never "not Prop".
    pub(super) fn prop_status(&mut self, ty: u32) -> R<Option<bool>> {
        let Some(s) = self.infer_value(ty)? else {
            return Ok(None);
        };
        let w = self.whnf(s)?;
        match self.vals[w as usize] {
            Val::Sort(l) => Ok(Some(self.is_zero(l)?)),
            _ => Ok(None),
        }
    }
    /// Conservative: false only if value `v` provably does not depend on the
    /// local value `x`. Values created before `x` cannot depend on it.
    fn mentions(&mut self, v: u32, x: u32) -> R<bool> {
        let Val::Local { id: xid, .. } = self.vals[x as usize] else {
            return Ok(true);
        };
        let mut stack = self.scratch.pop().unwrap_or_default();
        stack.clear();
        let res = (|| {
            // The traversal visits at most `budget` values; each pushes at most
            // its environment range and spine, so room is made per visit.
            self.scratch_room(&mut stack, 1)?;
            stack.push(v);
            let mut budget = 256u32;
            let mut found = false;
            while let Some(v) = stack.pop() {
                if v < x {
                    continue;
                }
                if budget == 0 {
                    found = true;
                    break;
                }
                budget -= 1;
                let (env, loose, spine) = match self.vals[v as usize] {
                    Val::Ind(t) => {
                        self.scratch_room(&mut stack, 1)?;
                        stack.push(t);
                        continue;
                    }
                    Val::Delayed { e, env, .. } => {
                        (env, self.exprs.get(e, self.b)?.loose_range(), 0)
                    }
                    Val::Lam(c) | Val::Pi(c) | Val::LamTy(c) => {
                        let l = self.exprs.get(c.dom, self.b)?.loose_range().max(
                            self.exprs
                                .get(c.body, self.b)?
                                .loose_range()
                                .saturating_sub(1),
                        );
                        (c.env, l, 0)
                    }
                    Val::Arrow { dom, cod } => {
                        self.scratch_room(&mut stack, 2)?;
                        stack.push(dom);
                        stack.push(cod);
                        continue;
                    }
                    Val::Proj { x, .. } => {
                        self.scratch_room(&mut stack, 1)?;
                        stack.push(x);
                        continue;
                    }
                    Val::Local { id, spine } => {
                        if id == xid {
                            found = true;
                            break;
                        }
                        (0, 0, spine)
                    }
                    Val::Const { spine, .. } => (0, 0, spine),
                    Val::Sort(_) | Val::Nat(_) | Val::Str(_) => continue,
                };
                let mut env = env;
                for _ in 0..loose {
                    if env == 0 {
                        break;
                    }
                    let n = self.envs[env as usize];
                    // A lambda type reads an entry's declared type as well.
                    self.scratch_room(&mut stack, 2)?;
                    stack.push(n.val);
                    if n.ty != NONE {
                        stack.push(n.ty);
                    }
                    env = n.parent;
                }
                let mut s = spine;
                while s != 0 {
                    let c = self.cells[s as usize];
                    if c.tag == 0 {
                        self.scratch_room(&mut stack, 1)?;
                        stack.push(c.item);
                    }
                    s = c.prev;
                }
            }
            stack.clear();
            Ok(found)
        })();
        self.scratch_finish(res, [stack])
    }
    fn is_prop_type(&mut self, ty: u32) -> R<bool> {
        Ok(self.prop_status(ty)? == Some(true))
    }
    pub(super) fn is_proof(&mut self, v: u32) -> R<Option<u32>> {
        if matches!(
            self.vals[v as usize],
            Val::Sort(_)
                | Val::Pi(_)
                | Val::LamTy(_)
                | Val::Arrow { .. }
                | Val::Nat(_)
                | Val::Str(_)
        ) {
            return Ok(None);
        }
        let Some(t) = self.infer_value(v)? else {
            return Ok(None);
        };
        Ok(self.is_prop_type(t)?.then_some(t))
    }

    // ---------- definitional equality (positive) ----------
}
