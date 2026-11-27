//! Checked reductions for lets, naturals, quotients and recursors.

use super::*;

impl<'e, 'w> Kernel<'e, 'w> {
    pub(super) fn let_bit(&self, bit: u64) -> bool {
        self.let_marks
            .get((bit / 64) as usize)
            .is_some_and(|word| word >> (bit % 64) & 1 == 1)
    }
    pub(super) fn set_let_bit(&mut self, bit: u64) -> R<()> {
        let word = (bit / 64) as usize;
        if word >= self.let_marks.len() {
            let extra = word + 1 - self.let_marks.len();
            room(self.b, &mut self.reserved, &mut self.let_marks, extra)?;
            self.let_marks.resize(word + 1, 0);
        }
        self.let_marks[word] |= 1 << (bit % 64);
        Ok(())
    }
    /// Mark a let-bound value that may still need reduction.
    pub(super) fn mark_let(&mut self, v: u32) -> R<()> {
        if matches!(self.vals[v as usize], Val::Delayed { .. } | Val::Ind(_)) {
            self.set_let_bit(2 * u64::from(v))?;
        }
        Ok(())
    }
    /// Whether `lazy_delta` may reduce `v` to fold it. Values not reached
    /// through a let-bound link, literals and values already reduced always
    /// may. A let-bound value is reduced within `LET_FOLD_BUDGET`, never past
    /// an enclosing allowance: at most half of the room it leaves. If the
    /// full allowance runs out, the link is recorded and not tried again.
    pub(super) fn let_fold_allowed(&mut self, v: u32) -> R<bool> {
        if self.let_marks.is_empty() {
            return Ok(true);
        }
        let mut link = NONE;
        let mut w = v;
        loop {
            if link == NONE && self.let_bit(2 * u64::from(w)) {
                link = w;
            }
            match self.vals[w as usize] {
                Val::Ind(t) => w = t,
                _ => break,
            }
        }
        if link == NONE || matches!(self.vals[w as usize], Val::Nat(_)) {
            return Ok(true);
        }
        // Already reduced by another route: folding costs nothing more.
        if !matches!(self.vals[w as usize], Val::Delayed { .. })
            && self.meta[w as usize].whnf != NONE
        {
            return Ok(true);
        }
        if self.let_bit(2 * u64::from(link) + 1) {
            return Ok(false);
        }
        let saved = self.bounds;
        let room = self.limit.saturating_sub(self.steps) / 2;
        if room == 0 {
            return Ok(false);
        }
        let full = room >= LET_FOLD_BUDGET;
        let depth = self.binders.len();
        self.limit_total(self.steps.saturating_add(LET_FOLD_BUDGET.min(room)));
        let r = self.whnf(v);
        self.restore_bounds(saved);
        self.binders.truncate(depth);
        match r {
            Ok(_) => Ok(true),
            // Our own allowance ran out: no fold. An outer allowance
            // propagates.
            Err(KErr::Abort) if self.steps <= self.limit => {
                if full {
                    self.set_let_bit(2 * u64::from(link) + 1)?;
                }
                Ok(false)
            }
            Err(e) => Err(e),
        }
    }
    /// A natural literal for `v`. Inside `lazy_delta` (`lazy`), a let-bound
    /// operand is reduced only within `LET_FOLD_BUDGET`; past it there is no
    /// literal, and lazy delta continues by unfolding.
    /// Returns an append-only literal-store ID; NONE denotes canonical zero.
    /// Hold IDs, never copied digit buffers, across recursive normalization.
    pub(super) fn nat_value_in(&mut self, v: u32, lazy: bool) -> R<Option<u32>> {
        if lazy && !self.let_fold_allowed(v)? {
            return Ok(None);
        }
        let w = self.whnf(v)?;
        match self.vals[w as usize] {
            Val::Nat(n) => Ok(Some(n)),
            Val::Const { ci, spine: 0, .. } => {
                if let Some((_, zero, _)) = self.nat_ctors()?
                    && ci == zero
                {
                    return Ok(Some(NONE));
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }
    // Optional-query admission, never a closedness certificate. A reached
    // open case withholds the fold; an inspection-cap exit retains the old
    // query under its existing budgets/errors. No value is forced here and
    // neither Boolean result grants equality, inequality or checkedness.
    pub(super) fn admit_native_query(&mut self, root: u32) -> R<bool> {
        fn offer(stack: &mut [u32; 128], len: &mut usize, value: u32) -> bool {
            if *len == stack.len() {
                return false;
            }
            stack[*len] = value;
            *len += 1;
            true
        }
        let mut stack = [0; 128];
        stack[0] = root;
        let (mut len, mut visits) = (1, 0);
        while len != 0 {
            if visits == 128 {
                return Ok(true);
            }
            visits += 1;
            self.step()?;
            len -= 1;
            let value = self.vals[stack[len] as usize];
            let (mut env, loose, mut spine) = match value {
                Val::Local { .. } => return Ok(false),
                Val::Ind(v) | Val::Proj { x: v, .. } => {
                    if !offer(&mut stack, &mut len, v) {
                        return Ok(true);
                    }
                    continue;
                }
                Val::Delayed { e, env, .. } => {
                    let node = self.exprs.get(e, self.b)?;
                    if node.has_free() {
                        return Ok(false);
                    }
                    (env, node.loose_range(), 0)
                }
                Val::Lam(c) | Val::Pi(c) | Val::LamTy(c) => {
                    let dom = self.exprs.get(c.dom, self.b)?;
                    let body = self.exprs.get(c.body, self.b)?;
                    if dom.has_free() || body.has_free() {
                        return Ok(false);
                    }
                    let r = dom.loose_range().max(body.loose_range().saturating_sub(1));
                    (c.env, r, 0)
                }
                Val::Arrow { dom, cod } => {
                    if !offer(&mut stack, &mut len, dom) || !offer(&mut stack, &mut len, cod) {
                        return Ok(true);
                    }
                    continue;
                }
                Val::Const { spine, .. } => (0, 0, spine),
                Val::Sort(_) | Val::Nat(_) | Val::Str(_) => continue,
            };
            if loose > 128 || self.cells[spine as usize].len > 128 {
                return Ok(true);
            }
            self.steps_by(u64::from(loose) + u64::from(self.cells[spine as usize].len))?;
            for _ in 0..loose {
                if env == 0 {
                    return Ok(false);
                }
                let node = self.envs[env as usize];
                if !offer(&mut stack, &mut len, node.val) {
                    return Ok(true);
                }
                if matches!(value, Val::LamTy(_))
                    && node.ty != NONE
                    && !offer(&mut stack, &mut len, node.ty)
                {
                    return Ok(true);
                }
                env = node.parent;
            }
            while spine != 0 {
                let cell = self.cells[spine as usize];
                if cell.tag == 0 && !offer(&mut stack, &mut len, cell.item) {
                    return Ok(true);
                }
                spine = cell.prev;
            }
        }
        Ok(true)
    }
    pub(super) fn nat_reduce(&mut self, v: u32) -> R<Option<u32>> {
        self.nat_reduce_in(v, false)
    }
    // Keep refusal on the conversion path small. Non-unary/non-binary
    // constants already fail both guards below without a query or charge.
    #[inline(always)]
    pub(super) fn nat_reduce_in(&mut self, v: u32, lazy: bool) -> R<Option<u32>> {
        if self.neutral_head_only {
            return Ok(None);
        }
        let Val::Const { ci, spine, .. } = self.vals[v as usize] else {
            return Ok(None);
        };
        let count = self.cells[spine as usize].len;
        if count != 1 && count != 2 {
            return Ok(None);
        }
        self.nat_reduce_candidate(v, lazy, ci, spine)
    }
    #[inline(never)]
    fn nat_reduce_candidate(&mut self, v: u32, lazy: bool, ci: u32, spine: u32) -> R<Option<u32>> {
        // `Nat.succ` of a literal is the next literal (Lean's reduce_nat).
        if self.cells[spine as usize].len == 1
            && let Some((_, _, succ)) = self.nat_ctors()?
            && ci == succ
        {
            let Some(arg) = self.arg_item(spine) else {
                return Ok(None);
            };
            if lazy && !self.admit_native_query(v)? {
                return Ok(None);
            }
            if let Some(x) = self.nat_value_in(arg, lazy)? {
                self.observe_natural(x, NONE)?;
                let next = match nat_literal(&self.nats, x) {
                    NatLit::Small(n) if *n < u64::MAX => NatLit::Small(n + 1),
                    NatLit::Computed(..) => {
                        return self.adjacent_computed(x, Operation::Add).map(Some);
                    }
                    other => {
                        let d = nat_digits(other)?;
                        match crate::check::natural::successor(d.as_bytes(), self.b) {
                            Ok(d) => {
                                let lit = parse_nat(d.as_bytes(), self.b, &mut self.reserved);
                                d.retire(self.b)?;
                                lit?
                            }
                            Err(crate::check::natural::Error::Resource(e)) => return Err(e.into()),
                            Err(_) => return Ok(None),
                        }
                    }
                };
                return Ok(Some(self.nat(next)?));
            }
            return Ok(None);
        }
        if self.cells[spine as usize].len != 2 || !self.const_view(ci)?.params.is_empty() {
            return Ok(None);
        }
        let op = self.natop(ci)?;
        let pred = if op.is_none() {
            self.natpred(ci)?
        } else {
            None
        };
        if op.is_none() && pred.is_none() {
            return Ok(None);
        }
        if lazy && !self.admit_native_query(v)? {
            return Ok(None);
        }
        let Some(args) = self.spine_args_opt(spine)? else {
            return Ok(None);
        };
        let (a, c) = (args[0], args[1]);
        self.recycle(args)?;
        let Some(x) = self.nat_value_in(a, lazy)? else {
            return Ok(None);
        };
        let Some(y) = self.nat_value_in(c, lazy)? else {
            return Ok(None);
        };
        // Both recursive observations are complete before borrowing digits.
        // Literal entries are immutable and cannot retire within this attempt.
        self.observe_pair(x, y)?;
        let Some(op) = op else {
            let equality = pred == Some(true);
            let order = compare_naturals(
                nat_literal(&self.nats, x),
                nat_literal(&self.nats, y),
                self.b,
            )?;
            let answer = if equality {
                order.is_eq()
            } else {
                !order.is_gt()
            };
            let Some(name) = self.env.natural_predicate_constructor(answer) else {
                return no();
            };
            let bci = self.const_info(name)?;
            return Ok(Some(self.push(Val::Const {
                ci: bci,
                li: 0,
                spine: 0,
            })?));
        };
        // At most 129 machine remainders for u64 Euclid, admitted once.
        if op == crate::check::natural::Operation::Gcd {
            self.steps_by(129)?;
        }
        let recipe = Recipe {
            op,
            left: x,
            right: y,
        };
        let (x, y) = (nat_literal(&self.nats, x), nat_literal(&self.nats, y));
        let r = match nat_small(op, x, y) {
            Some(r) => NatLit::Small(r),
            None if use_binary_operation(op, x, y) => {
                return self.store_product(recipe).map(Some);
            }
            None => {
                let (xs, ys) = (nat_digits(x)?, nat_digits(y)?);
                match crate::check::natural::arithmetic(op, xs.as_bytes(), ys.as_bytes(), self.b) {
                    Ok(d) => {
                        let lit = parse_nat(d.as_bytes(), self.b, &mut self.reserved);
                        d.retire(self.b)?;
                        lit?
                    }
                    Err(crate::check::natural::Error::Resource(e)) => return Err(e.into()),
                    Err(crate::check::natural::Error::Unsupported) => {
                        return Err(KErr::LiteralArithmetic);
                    }
                }
            }
        };
        Ok(Some(self.nat(r)?))
    }
    /// `Quot.lift f h (Quot.mk r a) ↦ f a` and `Quot.ind h (Quot.mk r a) ↦ h a`.
    pub(super) fn quot_reduce(&mut self, ci: u32, spine: u32) -> R<Option<u32>> {
        let (major_at, f_at) = match self.const_view(ci)?.quot {
            Some(QuotientRole::Lift) => (5usize, 3usize),
            Some(QuotientRole::Induction) => (4, 3),
            _ => return Ok(None),
        };
        if (self.cells[spine as usize].len as usize) <= major_at {
            return Ok(None);
        }
        let Some(args) = self.spine_args_opt(spine)? else {
            return Ok(None);
        };
        let res = (|| {
            let q = self.whnf(args[major_at])?;
            let Val::Const {
                ci: mk, spine: ms, ..
            } = self.vals[q as usize]
            else {
                return Ok(None);
            };
            if self.const_view(mk)?.quot != Some(QuotientRole::Constructor)
                || self.cells[ms as usize].len != 3
            {
                return Ok(None);
            }
            let Some(a) = self.arg_item(ms) else {
                return Ok(None);
            };
            let mut all = self.scratch.pop().unwrap_or_default();
            all.clear();
            let result = (|| {
                self.scratch_room(&mut all, args.len() - major_at)?;
                all.push(a);
                all.extend_from_slice(&args[major_at + 1..]);
                self.apply_many(args[f_at], &all).map(Some)
            })();
            self.scratch_finish(result, [all])
        })();
        self.scratch_finish(res, [args])
    }
    pub(super) fn iota(&mut self, ci: u32, li: u32, spine: u32) -> R<Option<u32>> {
        let Some(rec) = self.const_view(ci)?.rec else {
            return Ok(None);
        };
        let major_at = (rec.common + rec.nidx) as usize;
        if (self.cells[spine as usize].len as usize) <= major_at {
            return Ok(None);
        }
        // A projected recursor application: reduce the application below the
        // first projection, then replay the projections and later arguments.
        if let Some(prefix) = self.proj_prefix(spine) {
            return match self.iota(ci, li, prefix)? {
                Some(r) => Ok(Some(self.replay_from(r, spine, prefix)?)),
                None => Ok(None),
            };
        }
        let args = self.spine_args(spine)?;
        let r = self.iota_args(ci, li, rec, &args, major_at);
        self.scratch_finish(r, [args])
    }
    fn iota_args(
        &mut self,
        ci: u32,
        li: u32,
        rec: Rec<'e>,
        args: &[u32],
        major_at: usize,
    ) -> R<Option<u32>> {
        // A checked major need not normalize. For eligible structure families,
        // eta exposes the constructor without demanding its fields.
        let mut ctor = None;
        if rec.eta {
            let original = self.force(args[major_at])?;
            ctor = self.ctor_app(original, rec.family)?;
            if ctor.is_none() {
                // Completed exact-value memos retain the graph's typed context.
                // Reuse an ordinary constructor before allocating eta fields;
                // a miss requests no new normalization and proves nothing.
                for cached in [
                    self.meta[original as usize].whnf,
                    self.meta[original as usize].core,
                ] {
                    if cached != NONE {
                        ctor = self.ctor_app(cached, rec.family)?;
                        if ctor.is_some() {
                            break;
                        }
                    }
                }
                if ctor.is_none() {
                    ctor = self.struct_ctor(original, rec.family)?;
                }
            }
        }
        // K first, on the major as it stands: a proof premise of a K-like
        // family is never reduced when its type already fixes the
        // constructor. `k_ctor` admits the constructor only after
        // its type is definitionally equal to the major's, so trying it
        // before reduction adds no rule; on a refusal reduction continues.
        if ctor.is_none() && rec.k {
            let original = self.force(args[major_at])?;
            ctor = self.ctor_app(original, rec.family)?;
            // Completed results for these exact graph values only: a miss
            // requests no normalization and proves nothing.
            for cached in [
                self.meta[original as usize].whnf,
                self.meta[original as usize].core,
            ] {
                if ctor.is_none() && cached != NONE {
                    ctor = self.ctor_app(cached, rec.family)?;
                }
            }
            if ctor.is_none() {
                ctor = self.k_ctor(original, rec, li)?;
            }
        }
        if ctor.is_none() {
            let mut major = self.whnf(args[major_at])?;
            if let Val::Str(e) = self.vals[major as usize] {
                let x = self.expand_str(e)?;
                major = self.whnf(x)?;
            }
            if let Val::Nat(n) = self.vals[major as usize]
                && let Some((nat, zero, succ)) = self.nat_ctors()?
                && self.const_view(nat)?.canon == rec.family
            {
                self.observe_natural(n, NONE)?;
                major = match &self.nats[n as usize] {
                    NatLit::Small(0) => self.push(Val::Const {
                        ci: zero,
                        li: 0,
                        spine: 0,
                    })?,
                    _ => {
                        let pred = self.predecessor_value(n)?;
                        let spine = self.cell(0, pred, 0)?;
                        self.push(Val::Const {
                            ci: succ,
                            li: 0,
                            spine,
                        })?
                    }
                };
            }
            ctor = self.ctor_app(major, rec.family)?;
            if ctor.is_none() && rec.k {
                ctor = self.k_ctor(major, rec, li)?;
            }
            if ctor.is_none() {
                ctor = self.struct_ctor(major, rec.family)?;
            }
        }
        let Some((cci, cspine)) = ctor else {
            return Ok(None);
        };
        let ccanon = self.const_view(cci)?.canon;
        let mut found = None;
        for (i, rule) in rec.rules.iter().enumerate() {
            if self.canon(rule.constructor)? == ccanon {
                found = Some((i as u32, *rule));
                break;
            }
        }
        let Some((index, rule)) = found else {
            return Ok(None);
        };
        let Some(cargs) = self.spine_args_opt(cspine)? else {
            return Ok(None);
        };
        if cargs.len() != (rec.cparams + rule.num_fields) as usize {
            self.recycle(cargs)?;
            return Ok(None);
        }
        let res = (|| {
            let key = (ci, li, index);
            let rhs = match self.rule_rhs.get(&key) {
                Some(&v) => v,
                None => {
                    let v = self.eval(rule.rhs, 0, li)?;
                    map_put(self.b, &mut self.reserved, &mut self.rule_rhs, key, v)?;
                    v
                }
            };
            let mut all = self.scratch.pop().unwrap_or_default();
            all.clear();
            let res = (|| {
                self.scratch_room(&mut all, args.len() + cargs.len())?;
                all.extend_from_slice(&args[..rec.common as usize]);
                all.extend_from_slice(&cargs[rec.cparams as usize..]);
                all.extend_from_slice(&args[major_at + 1..]);
                self.apply_many(rhs, &all)
            })();
            self.scratch_finish(res.map(Some), [all])
        })();
        self.scratch_finish(res, [cargs])
    }
    fn ctor_app(&mut self, v: u32, family: u32) -> R<Option<(u32, u32)>> {
        if let Val::Const { ci, spine, .. } = self.vals[v as usize]
            && let Some((fam, _)) = self.const_view(ci)?.ctor
            && fam == family
        {
            return Ok(Some((ci, spine)));
        }
        Ok(None)
    }
    /// K: a major of the right type is replaced by the unique field-free constructor.
    fn k_ctor(&mut self, major: u32, rec: Rec<'e>, _li: u32) -> R<Option<(u32, u32)>> {
        let Some(rule) = rec.rules.first().copied() else {
            return Ok(None);
        };
        if rule.num_fields != 0 {
            return Ok(None);
        }
        let Some(ty) = self.infer_value(major)? else {
            return Ok(None);
        };
        let ty = self.whnf(ty)?;
        let Val::Const {
            ci: ind,
            li: ind_li,
            spine,
        } = self.vals[ty as usize]
        else {
            return Ok(None);
        };
        let Some(info) = self.const_view(ind)?.ind else {
            return Ok(None);
        };
        if self.const_view(ind)?.canon != rec.family {
            return Ok(None);
        }
        let Some(args) = self.spine_args_opt(spine)? else {
            return Ok(None);
        };
        if args.len() != (info.nparams + info.nidx) as usize {
            self.recycle(args)?;
            return Ok(None);
        }
        let res = (|| {
            let cci = self.const_info(rule.constructor)?;
            let cli = self.rebind_instance(cci, ind_li)?;
            let c = self.push(Val::Const {
                ci: cci,
                li: cli,
                spine: 0,
            })?;
            let mut cspine = 0;
            for &p in &args[..info.nparams as usize] {
                cspine = self.cell(cspine, p, 0)?;
            }
            Ok((c, cspine, cci, cli))
        })();
        let (mut c, cspine, cci, cli) = self.scratch_finish(res, [args])?;
        if cspine != 0 {
            c = self.push(Val::Const {
                ci: cci,
                li: cli,
                spine: cspine,
            })?;
        }
        let Some(cty) = self.infer_value(c)? else {
            return Ok(None);
        };
        if !self.defeq(cty, ty)? {
            return Ok(None);
        }
        Ok(Some((cci, cspine)))
    }
    /// Structure eta for iota: expand a non-constructor major of a structure type.
    pub(super) fn struct_ctor(&mut self, major: u32, family: u32) -> R<Option<(u32, u32)>> {
        if !matches!(
            self.vals[major as usize],
            Val::Local { .. } | Val::Const { .. }
        ) {
            return Ok(None);
        }
        // A warm ineligible family still avoids type observation. A cold
        // metadata slot is not evidence of ineligibility: observing the major's
        // type can itself load its committed family.
        if let Some(&fci) = self.const_by_canon.get(&family)
            && !self
                .const_view(fci)?
                .ind
                .is_some_and(|info| info.structure_like())
        {
            return Ok(None);
        }
        let Some(ty) = self.infer_value(major)? else {
            return Ok(None);
        };
        let ty = self.whnf(ty)?;
        let Val::Const {
            ci: ind,
            li: ind_li,
            spine,
        } = self.vals[ty as usize]
        else {
            return Ok(None);
        };
        // The exposed type supplies both the validated metadata and the family
        // identity. No cache entry or incomplete observation supplies authority.
        let fci = ind;
        if self.const_view(fci)?.canon != family {
            return Ok(None);
        }
        let Some(info) = self.const_view(fci)?.ind else {
            return Ok(None);
        };
        if !info.structure_like() {
            return Ok(None);
        }
        let Some(prop) = self.prop_status(ty)? else {
            return Ok(None);
        };
        let Some(params) = self.spine_args_opt(spine)? else {
            return Ok(None);
        };
        if params.len() != info.nparams as usize {
            self.recycle(params)?;
            return Ok(None);
        }
        let result = (|| {
            let rule = info.ctors[0];
            let cci = self.const_info(rule.constructor)?;
            let cli = self.rebind_instance(cci, ind_li)?;
            let mut telescope = self.const_type(cci, cli)?;
            let mut cspine = 0;
            for &p in params.iter() {
                cspine = self.cell(cspine, p, 0)?;
                let binder = self.pi_like(telescope)?;
                telescope = self.instantiate(binder, p)?;
            }
            for i in 0..rule.num_fields {
                let binder = self.pi_like(telescope)?;
                let field_type = self.binder_dom(binder)?;
                if prop && self.prop_status(field_type)? != Some(true) {
                    return Ok(None);
                }
                // Construction invariant: exact validated family/arity and this
                // instantiated constructor telescope justify the projection.
                // Prop projections admit proof fields only. Do not call proj:
                // it would WHNF the very major eta is intended not to demand.
                let field = self.push(Val::Proj {
                    x: major,
                    idx: i,
                    sci: fci,
                })?;
                self.cache_type(field, field_type)?;
                cspine = self.cell(cspine, field, 0)?;
                // Only a later field consumes this instantiated telescope.
                // Committed constructor validation already checks its result family.
                if i + 1 < rule.num_fields {
                    telescope = self.instantiate(binder, field)?;
                }
            }
            Ok(Some((cci, cspine)))
        })();
        self.scratch_finish(result, [params])
    }

    // ---------- inference ----------
}
