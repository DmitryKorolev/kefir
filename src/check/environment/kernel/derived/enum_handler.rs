//! Recognize and replay a checked enumeration whose branches forward a field
//! to an argument-supplied handler.
use super::*;

#[derive(Clone, Copy)]
pub(super) struct EnumHandler {
    ctors: [u32; 2],
    handlers: [u8; 2],
    tag: u8,
    payload: u8,
}

impl Template {
    fn node(self, derived: &Derived, reference: TRef) -> Option<TNode> {
        match reference {
            TRef::Node(index) => Some(derived.tnodes[self.nodes as usize + index as usize]),
            TRef::Closed(_) => None,
        }
    }
}

impl Kernel<'_, '_> {
    pub(super) fn enum_handler(
        &mut self,
        template: Template,
        split: &Split,
        symbolic: u32,
    ) -> R<Option<EnumHandler>> {
        let Some(TNode::Const { ci, items, len, .. }) = template.node(&self.derived, template.root)
        else {
            return Ok(None);
        };
        let Some(rec) = self.const_view(ci)?.rec else {
            return Ok(None);
        };
        let common = rec.common as usize;
        if common > MAX_ARITY
            || rec.cparams != 0
            || rec.nidx != 0
            || rec.k
            || rec.eta
            || rec.rules.len() != 2
            || rec.rules.iter().any(|r| r.num_fields != 0)
            || len as usize != common + 2
        {
            return Ok(None);
        }
        let Val::Const { ci: original, .. } = self.vals[symbolic as usize] else {
            return Ok(None);
        };
        let Some((family, _)) = self.const_view(original)?.ctor else {
            return Ok(None);
        };
        let start = (template.items + items) as usize;
        self.steps_by(u64::from(len))?;
        let row = &self.derived.titems[start..start + len as usize];
        // A projection anywhere in the spine changes recursor replay. Copy its
        // bounded argument references only after establishing the prefix.
        let mut refs = [TRef::Closed(0); MAX_ARITY + 2];
        for (slot, item) in refs.iter_mut().zip(row) {
            let TItem::Arg(arg) = *item else {
                return Ok(None);
            };
            *slot = arg;
        }
        let mut fields = [0; 2];
        for (field, &reference) in fields.iter_mut().zip(&refs[common..]) {
            let Some(TNode::Proj { x, idx, sci }) = template.node(&self.derived, reference) else {
                return Ok(None);
            };
            if idx >= u32::from(split.guard.nfields)
                || !matches!(template.node(&self.derived, x), Some(TNode::Matched(0)))
                || self.const_view(sci)?.canon != family
            {
                return Ok(None);
            }
            *field = idx as u8;
        }
        let mut handlers = [0; 2];
        let mut ctors = [0; 2];
        for (i, rule) in rec.rules.iter().enumerate() {
            let Some(at) = self.enum_minor(rule.rhs, common)? else {
                return Ok(None);
            };
            let Some(handler) = self.forwarding_handler(template, refs[at])? else {
                return Ok(None);
            };
            handlers[i] = handler;
            ctors[i] = self.canon(rule.constructor)?;
        }
        let [tag, payload] = fields;
        Ok(Some(EnumHandler {
            ctors,
            handlers,
            tag,
            payload,
        }))
    }

    /// The checked RHS must select a common argument, with no application or
    /// dependence on a universe instance after its binders are removed.
    fn enum_minor(&mut self, mut rhs: ExprId, common: usize) -> R<Option<usize>> {
        self.steps_by(common as u64 + 1)?;
        for _ in 0..common {
            let ExprKind::Lambda(_, _, body, _) =
                self.exprs
                    .get(rhs, self.b)?
                    .kind(self.exprs, self.levels, self.b)?
            else {
                return Ok(None);
            };
            rhs = body;
        }
        Ok(self
            .exprs
            .get(rhs, self.b)?
            .bound_index()
            .and_then(|i| common.checked_sub(i as usize + 1)))
    }

    /// Resolve the captured `h` of precisely `fun x => h x` from recorded
    /// untyped environment nodes. Replay will supply both actual values.
    fn forwarding_handler(&mut self, t: Template, minor: TRef) -> R<Option<u8>> {
        let Some(TNode::Clo {
            form: 0,
            body,
            mut env,
            ..
        }) = t.node(&self.derived, minor)
        else {
            return Ok(None);
        };
        let ExprKind::App(h, x) =
            self.exprs
                .get(body, self.b)?
                .kind(self.exprs, self.levels, self.b)?
        else {
            return Ok(None);
        };
        if self.exprs.get(x, self.b)?.bound_index() != Some(0) {
            return Ok(None);
        }
        let Some(depth) = self
            .exprs
            .get(h, self.b)?
            .bound_index()
            .and_then(|i| i.checked_sub(1))
        else {
            return Ok(None);
        };
        if depth >= u32::from(t.len) {
            return Ok(None);
        }
        self.steps_by(u64::from(depth) + 1)?;
        for _ in 0..depth {
            let Some(TNode::Env { parent, .. }) = t.node(&self.derived, env) else {
                return Ok(None);
            };
            env = parent;
        }
        let Some(TNode::Env { val, .. }) = t.node(&self.derived, env) else {
            return Ok(None);
        };
        Ok(match t.node(&self.derived, val) {
            Some(TNode::Slot(Slot::Arg(i))) => Some(i),
            _ => None,
        })
    }

    pub(super) fn apply_enum_handler(
        &mut self,
        template: Template,
        rule: &Rule,
        args: &[Arg; MAX_ARITY],
        matched: Head,
    ) -> R<Option<u32>> {
        // Construction invariant: the leaf's descriptor immediately follows
        // its fallback nodes. Both move with the same retained graph.
        let at = template.nodes as usize + template.len as usize;
        let TNode::EnumHandler(op) = self.derived.tnodes[at] else {
            return Err(ResourceError::Invariant.into());
        };
        let Head::Ctor { spine, .. } = matched else {
            return Ok(None);
        };
        let guard = rule.guards[0];
        let source = self.materialize(args[guard.arg as usize])?;
        let original = self.whnf(source)?;
        if !matches!(self.vals[original as usize], Val::Const { spine: actual, .. } if actual == spine)
        {
            return Ok(None);
        }
        let len = self.cells[spine as usize].len;
        self.steps_by(3 * u64::from(len) + 1)?;
        if self.proj_prefix(spine).is_some() {
            return Ok(None);
        }
        let value = self.field(guard, matched, op.tag)?;
        let value = self.materialize(value)?;
        let tag = self.whnf(value)?;
        let Val::Const { ci, spine: 0, .. } = self.vals[tag as usize] else {
            return Ok(None);
        };
        let canon = self.const_view(ci)?.canon;
        let Some(branch) = op.ctors.iter().position(|&c| c == canon) else {
            return Ok(None);
        };
        let handler = self.materialize(args[op.handlers[branch] as usize])?;
        let argument = self.field(guard, matched, op.payload)?;
        let argument = self.materialize(argument)?;
        self.apply(handler, argument).map(Some)
    }
}
