//! Derived reduction rules. A definition freshly unfolded `HOT` times
//! in one attempt gets a small rule tree derived from its own body by symbolic
//! reduction: constructor guards on arguments, and a leaf that is a field, an
//! argument or a call of the same definition. Rules are used while a guard
//! matches; anything else unfolds ordinarily.
//!
//! Scope: one `(constant, level instance)` in one attempt's graph. Trees hold
//! argument and field positions and canonical constructor ids; templates also
//! hold value and environment ids of closed parts of this graph, which never
//! truncates its stores. A snapshot keeps the positive trees and
//! their templates with the graph whose constant slots and level instances key
//! them; heat, the derivation count and "no rule" entries stay with the
//! attempt. A failed or abandoned derivation stores only "no rule", drops the
//! templates it recorded, and proves nothing.
//! A full-allowance derivation that finds no rule also sets the constant's bit
//! in the environment's run-lifetime memo, and later attempts skip detection
//! for it. The bit only withholds a derivation: a constant whose bit is set
//! unfolds exactly as with derived rules off.
//!
//! A path whose result is neither a pattern variable nor a self-call ends in a
//! template: the residual weak head normal form recorded over the
//! path's pattern variables, rebuilt by substitution at use. A template with no
//! guards is a fused body: one use replaces the matcher, `casesOn`, instance and
//! abbreviation layers derivation reduced through. A call with more arguments
//! than the tree's arity uses the rules on the first ones and applies the
//! result to the rest.
//!
//! Invariant (the reason a rule is a reduction): derivation established
//! `f ā[xᵢ := C ȳ] ⟶* r` and, for a self-call leaf, `f ā' ⟶* r'` with `r` and
//! `r'` structurally identical (`same`). Reduction is closed under
//! substitution, so for matching arguments both calls reach the same term and
//! have the same weak head normal form. `same` uses no conversion rule. A
//! template denotes exactly `r` with pattern variables as holes, and a guarded
//! argument's matched constructor as the argument itself; instantiating it is
//! the substitution. For a well-typed call the result and the call reduce to a
//! common term: the argument reduces to the matched constructor, whose
//! parameters equal derivation's by typing.
use super::*;

/// Fresh unfoldings of one constant in an attempt before it is derived.
const HOT: u32 = 32;
/// Derivations one attempt may run, successful or not.
const MAX_DERIVATIONS: u32 = 256;
/// Step allowance of one derivation.
const DERIVE_BUDGET: u64 = 1 << 14;
/// Arguments of a derived definition.
const MAX_ARITY: usize = 16;
/// Nested splits on one path.
const MAX_SPLITS: usize = 3;
/// Constructors of a split family.
const MAX_CTORS: usize = 8;
/// Fields of one split constructor.
const MAX_FIELDS: usize = 16;
/// Rules of one tree.
const MAX_RULES: usize = 64;
/// Node pairs one structural comparison may visit.
const SAME_BUDGET: u32 = 4096;
/// Nodes of one template.
const TEMPLATE_NODES: usize = 256;
/// Nodes of a template with no guards (a fused body). Larger fused bodies
/// build more than an ordinary unfolding forces.
const FUSED_NODES: usize = 16;
/// Values and environments one template readback may visit.
const TEMPLATE_VISITS: usize = 1024;
/// Nesting one template readback may follow.
const TEMPLATE_DEPTH: u32 = 64;

/// Argument `arg` is a constructor named by canonical `ctor` with
/// `nparams + nfields` arguments.
#[derive(Clone, Copy, Default)]
struct Guard {
    arg: u8,
    nparams: u8,
    nfields: u8,
    ctor: u32,
}
/// An argument, or field `1` of the constructor matched by guard `0`.
#[derive(Clone, Copy)]
enum Slot {
    Arg(u8),
    Field(u8, u8),
}
/// A pattern variable; the same definition called with each guarded
/// argument replaced by field `k[g]` of its matched constructor, every other
/// argument unchanged; or a template.
#[derive(Clone, Copy)]
enum Leaf {
    Value(Slot),
    Call([u8; MAX_SPLITS]),
    /// Index into the template store, little-endian in three bytes so a
    /// leaf stays byte-aligned and a whole rule fits in 32 bytes.
    Template([u8; 3]),
}
/// A recorded residual: `len` nodes from `nodes` in the node store, spine
/// items counted from `items` in the item store; `root` is the result.
#[derive(Clone, Copy)]
struct Template {
    nodes: u32,
    items: u32,
    len: u16,
    root: TRef,
}
/// A template child: a value or environment of this graph that mentions no
/// pattern variable, or node `k` of the same template.
#[derive(Clone, Copy, PartialEq, Eq)]
enum TRef {
    Closed(u32),
    Node(u16),
}
/// One template node; children precede their parents.
#[derive(Clone, Copy)]
enum TNode {
    /// A pattern variable.
    Slot(Slot),
    /// The argument guard `g` matched, as the call passed it.
    Matched(u8),
    /// A pattern variable applied to the arguments `items .. items + len`.
    App {
        head: TRef,
        items: u32,
        len: u32,
    },
    Const {
        ci: u32,
        li: u32,
        items: u32,
        len: u32,
    },
    Delayed {
        e: ExprId,
        li: u32,
        env: TRef,
    },
    /// `form` 0 lambda, 1 Pi, 2 lambda type; `loose` is the binder's loose
    /// range, as `eval` passes it, so instantiated closures share as theirs do.
    Clo {
        form: u8,
        loose: u32,
        dom: ExprId,
        body: ExprId,
        li: u32,
        env: TRef,
    },
    Arrow {
        dom: TRef,
        cod: TRef,
    },
    Proj {
        x: TRef,
        idx: u32,
        sci: u32,
    },
    Env {
        parent: TRef,
        val: TRef,
        ty: Option<TRef>,
    },
}
/// A spine entry: an argument, or a projection cell copied as it is.
#[derive(Clone, Copy)]
enum TItem {
    Arg(TRef),
    Proj { tag: u32, sci: u32 },
}
/// Readback state for one template: the path's pattern variables by local id
/// (an original argument or a field; a split argument's own local and its
/// constructor value stand for the matched argument), and the nodes so far.
struct Readback {
    pats: Vec<(u32, TNode)>,
    ctors: [(u32, u8); MAX_SPLITS],
    nctors: usize,
    nodes: Vec<TNode>,
    items: Vec<TItem>,
    memo: Map<(bool, u32), TRef>,
    visits: usize,
    /// Values and environments below these were made before the derivation
    /// and mention no pattern variable, when every pattern local is newer.
    closed_below: (u32, u32),
}
#[derive(Clone, Copy)]
struct Rule {
    guards: [Guard; MAX_SPLITS],
    len: u8,
    leaf: Leaf,
}
// A template leaf is an index, so templates do not widen every rule.
const _: () = assert!(size_of::<Rule>() == 32);
#[derive(Clone, Copy)]
struct Tree {
    arity: u8,
    start: u32,
    len: u32,
}

/// Per-attempt state. Charged through the attempt's ordinary storage rules;
/// `trees`, `list` and `rules` may move with a snapshot (`Kept`).
#[derive(Default)]
pub(super) struct Derived {
    heat: Map<u32, u32>,
    /// `(constant, level instance)` → tree index + 1, or 0 for no rule.
    trees: Map<(u32, u32), u32>,
    list: Vec<Tree>,
    rules: Vec<Rule>,
    /// Templates, and their nodes and spine items.
    templates: Vec<Template>,
    tnodes: Vec<TNode>,
    titems: Vec<TItem>,
    /// Value and environment counts when the current derivation started.
    base: (u32, u32),
    derivations: u32,
    deriving: bool,
    /// The current derivation unfolded an operation the kernel computes
    /// natively on literals; see `explore`.
    native: bool,
    /// Canonical `Nat.zero` and `Nat.succ`, once looked up.
    nat: Option<Option<(u32, u32)>>,
}

/// Positive rule trees a snapshot keeps with its graph. Every
/// entry of `trees` is nonzero and indexes `list`, whose ranges index `rules`.
#[derive(Default)]
pub(super) struct Kept {
    trees: Map<(u32, u32), u32>,
    list: Vec<Tree>,
    rules: Vec<Rule>,
    templates: Vec<Template>,
    tnodes: Vec<TNode>,
    titems: Vec<TItem>,
}
impl Derived {
    /// Move the trees out for capture, after `keep_trees`.
    pub(super) fn take_kept(&mut self) -> Kept {
        Kept {
            trees: std::mem::take(&mut self.trees),
            list: std::mem::take(&mut self.list),
            rules: std::mem::take(&mut self.rules),
            templates: std::mem::take(&mut self.templates),
            tnodes: std::mem::take(&mut self.tnodes),
            titems: std::mem::take(&mut self.titems),
        }
    }
    /// Install restored trees into a fresh attempt's state.
    pub(super) fn install_kept(&mut self, kept: Kept) {
        self.trees = kept.trees;
        self.list = kept.list;
        self.rules = kept.rules;
        self.templates = kept.templates;
        self.tnodes = kept.tnodes;
        self.titems = kept.titems;
    }
}

/// A rule-use argument: a value id, or with `NAT` set a small natural
/// literal not yet allocated (only a field of a `succ` guard produces one).
type Arg = u64;
const NAT: u64 = 1 << 63;
/// The constructor form of an argument, computed once per rule-use step.
#[derive(Clone, Copy)]
enum Head {
    Nat(u64),
    BigNat(u32),
    Ctor { canon: u32, spine: u32 },
    Stuck,
}

/// A pending comparison: two values, or two environments restricted to the
/// entries a syntax reads (`None`: all entries).
#[derive(Clone, Copy)]
enum Pair {
    Value(u32, u32),
    Env(u32, u32, Option<[u64; 4]>),
}

/// One split taken during derivation: the guard and its field values.
#[derive(Clone, Copy)]
struct Split {
    guard: Guard,
    fields: [u32; MAX_FIELDS],
    /// The unique field of the split family, if any.
    recursive: Option<u8>,
}

impl Kernel<'_, '_> {
    /// Rule use for `ci` at level instance `li` applied to `spine`, counting the
    /// fresh unfolding first. `Some(v)`: `v` is on the reduction path of the
    /// call. `None`: unfold ordinarily.
    pub(super) fn derived_unfold(&mut self, ci: u32, li: u32, spine: u32) -> R<Option<u32>> {
        // At most two arguments: a partly applied native operation unfolds
        // to its structural body too, and a template would replay it on the
        // literals the full call later meets.
        if self.derived.deriving
            && !self.derived.native
            && self.cells[spine as usize].len <= 2
            && (self.natop(ci)?.is_some() || self.natpred(ci)?.is_some())
        {
            self.derived.native = true;
        }
        let tree = match self.derived.trees.get(&(ci, li)) {
            Some(&t) => t,
            None => {
                if self.derived.deriving
                    || self.derived.derivations >= MAX_DERIVATIONS
                    || self.env.no_rule(self.const_view(ci)?.canon)
                {
                    return Ok(None);
                }
                let heat = match self.derived.heat.get_mut(&ci) {
                    Some(h) => {
                        *h += 1;
                        *h
                    }
                    None => {
                        map_put(self.b, &mut self.reserved, &mut self.derived.heat, ci, 1)?;
                        1
                    }
                };
                if heat < HOT {
                    return Ok(None);
                }
                self.derive(ci, li)?
            }
        };
        if tree == 0 {
            return Ok(None);
        }
        let t = self.derived.list[tree as usize - 1];
        let n = t.arity as usize;
        let total = self.cells[spine as usize].len as usize;
        if total < n || total - n > MAX_ARITY {
            return Ok(None);
        }
        // Arguments beyond the arity are applied to the rule's result.
        let ne = total - n;
        let mut extra = [0u32; MAX_ARITY];
        let mut args: [Arg; MAX_ARITY] = [0; MAX_ARITY];
        let mut s = spine;
        for e in extra[..ne].iter_mut().rev() {
            let c = self.cells[s as usize];
            if c.tag != 0 {
                return Ok(None);
            }
            *e = c.item;
            s = c.prev;
        }
        for a in args[..n].iter_mut().rev() {
            let c = self.cells[s as usize];
            if c.tag != 0 {
                return Ok(None);
            }
            *a = u64::from(c.item);
            s = c.prev;
        }
        let mut calls = 0u32;
        loop {
            self.step()?;
            let mut heads = [(u8::MAX, Head::Stuck); MAX_SPLITS];
            let Some(at) = self.match_rule(t, &args, &mut heads)? else {
                break;
            };
            let rule = self.derived.rules[at as usize];
            match rule.leaf {
                Leaf::Value(Slot::Arg(j)) => {
                    let v = self.materialize(args[j as usize])?;
                    return Ok(Some(self.apply_extra(v, &extra[..ne])?));
                }
                Leaf::Value(Slot::Field(g, k)) => {
                    let v = self.field(rule.guards[g as usize], heads[g as usize].1, k)?;
                    let v = self.materialize(v)?;
                    return Ok(Some(self.apply_extra(v, &extra[..ne])?));
                }
                Leaf::Template([a, b, c]) => {
                    let at = u32::from_le_bytes([a, b, c, 0]);
                    let tp = self.derived.templates[at as usize];
                    let v = self.instantiate_template(tp, &rule, &args, &heads)?;
                    return Ok(Some(self.apply_extra(v, &extra[..ne])?));
                }
                Leaf::Call(fields) => {
                    // Fields come from the heads of the old arguments, so the
                    // replacements can be written in place.
                    for g in 0..rule.len as usize {
                        let guard = rule.guards[g];
                        args[guard.arg as usize] = self.field(guard, heads[g].1, fields[g])?;
                    }
                    calls += 1;
                }
            }
        }
        if calls == 0 {
            return Ok(None);
        }
        let mut s = 0;
        for &a in &args[..n] {
            let v = self.materialize(a)?;
            s = self.cell(s, v, 0)?;
        }
        let v = self.push(Val::Const { ci, li, spine: s })?;
        Ok(Some(self.apply_extra(v, &extra[..ne])?))
    }

    /// `v` applied to the arguments beyond a tree's arity.
    #[inline]
    fn apply_extra(&mut self, v: u32, extra: &[u32]) -> R<u32> {
        if extra.is_empty() {
            Ok(v)
        } else {
            self.apply_many(v, extra)
        }
    }

    /// Rebuild template `tp` with the matched rule's pattern variables: each
    /// node once, children first. Charges one step per node.
    fn instantiate_template(
        &mut self,
        tp: Template,
        rule: &Rule,
        args: &[Arg; MAX_ARITY],
        heads: &[(u8, Head); MAX_SPLITS],
    ) -> R<u32> {
        let mut out = self.scratch.pop().unwrap_or_default();
        out.clear();
        let r = (|| {
            self.scratch_room(&mut out, tp.len as usize)?;
            for k in 0..tp.len as usize {
                self.step()?;
                let node = self.derived.tnodes[tp.nodes as usize + k];
                let at = |t: TRef, out: &[u32]| match t {
                    TRef::Closed(v) => v,
                    TRef::Node(j) => out[j as usize],
                };
                let v = match node {
                    TNode::Slot(Slot::Arg(j)) => self.materialize(args[j as usize])?,
                    TNode::Slot(Slot::Field(g, f)) => {
                        let a = self.field(rule.guards[g as usize], heads[g as usize].1, f)?;
                        self.materialize(a)?
                    }
                    TNode::Matched(g) => {
                        self.materialize(args[rule.guards[g as usize].arg as usize])?
                    }
                    TNode::App { head, items, len } => {
                        // Readback keeps applications to at most MAX_ARITY items.
                        let mut xs = [0u32; MAX_ARITY];
                        let start = (tp.items + items) as usize;
                        let row = self
                            .derived
                            .titems
                            .get(start..start + len as usize)
                            .filter(|row| row.len() <= MAX_ARITY)
                            .ok_or(ResourceError::Invariant)?;
                        for (x, item) in xs.iter_mut().zip(row) {
                            let TItem::Arg(a) = *item else {
                                return Err(ResourceError::Invariant.into());
                            };
                            *x = at(a, &out);
                        }
                        self.apply_many(at(head, &out), &xs[..len as usize])?
                    }
                    TNode::Const { ci, li, items, len } => {
                        let mut sp = 0;
                        for i in 0..len as usize {
                            sp = match self.derived.titems[(tp.items + items) as usize + i] {
                                TItem::Arg(a) => self.cell(sp, at(a, &out), 0)?,
                                TItem::Proj { tag, sci } => self.cell(sp, sci, tag)?,
                            };
                        }
                        self.push(Val::Const { ci, li, spine: sp })?
                    }
                    TNode::Delayed { e, li, env } => self.push(Val::Delayed {
                        e,
                        env: at(env, &out),
                        li,
                    })?,
                    TNode::Clo {
                        form,
                        loose,
                        dom,
                        body,
                        li,
                        env,
                    } => {
                        let c = Clo {
                            dom,
                            body,
                            env: at(env, &out),
                            li,
                        };
                        self.push_clo(u32::from(form), c, loose)?
                    }
                    TNode::Arrow { dom, cod } => self.push(Val::Arrow {
                        dom: at(dom, &out),
                        cod: at(cod, &out),
                    })?,
                    TNode::Proj { x, idx, sci } => self.push(Val::Proj {
                        x: at(x, &out),
                        idx,
                        sci,
                    })?,
                    TNode::Env { parent, val, ty } => {
                        let ty = ty.map_or(NONE, |t| at(t, &out));
                        self.env_push(at(parent, &out), at(val, &out), ty)?
                    }
                };
                out.push(v);
            }
            Ok(match tp.root {
                TRef::Closed(v) => v,
                TRef::Node(j) => out[j as usize],
            })
        })();
        self.scratch_finish(r, [out])
    }

    fn materialize(&mut self, a: Arg) -> R<u32> {
        if a & NAT != 0 {
            return self.nat(NatLit::Small(a & !NAT));
        }
        Ok(a as u32)
    }

    /// Field `k` of the constructor `h` matched by guard `g`: read from its
    /// spine, or a literal's predecessor.
    #[inline]
    fn field(&mut self, g: Guard, h: Head, k: u8) -> R<Arg> {
        match h {
            Head::Nat(n) if n != 0 => Ok((n - 1) | NAT),
            Head::BigNat(n) => {
                let lit = self.nats[n as usize].dup()?;
                let pred = nat_pred(&lit, self.b, &mut self.reserved)?;
                Ok(u64::from(self.nat(pred)?))
            }
            Head::Ctor { spine, .. } => {
                // Constructor arguments are params then fields, root first.
                let len = self.cells[spine as usize].len;
                let at = u32::from(g.nparams) + u32::from(k);
                let mut s = spine;
                for _ in 0..len.checked_sub(at + 1).ok_or(ResourceError::Invariant)? {
                    s = self.cells[s as usize].prev;
                }
                let c = self.cells[s as usize];
                if c.tag != 0 {
                    return Err(ResourceError::Invariant.into());
                }
                Ok(u64::from(c.item))
            }
            _ => Err(ResourceError::Invariant.into()),
        }
    }

    /// The index of the first rule whose guards all match; `heads[g]` is the
    /// matched form of guard `g`'s argument. Each argument is reduced at most
    /// once per call.
    fn match_rule(
        &mut self,
        t: Tree,
        args: &[Arg; MAX_ARITY],
        heads: &mut [(u8, Head); MAX_SPLITS],
    ) -> R<Option<u32>> {
        let mut seen = [(u8::MAX, Head::Stuck); MAX_SPLITS];
        let mut count = 0;
        'rules: for at in t.start..t.start + t.len {
            let len = self.derived.rules[at as usize].len as usize;
            for (g, slot) in heads.iter_mut().enumerate().take(len) {
                let guard = self.derived.rules[at as usize].guards[g];
                let h = match seen[..count].iter().find(|(a, _)| *a == guard.arg) {
                    Some(&(_, h)) => h,
                    None => {
                        let h = self.head(args[guard.arg as usize])?;
                        if count < MAX_SPLITS {
                            seen[count] = (guard.arg, h);
                            count += 1;
                        }
                        h
                    }
                };
                if !self.guard_matches(guard, h)? {
                    continue 'rules;
                }
                *slot = (guard.arg, h);
            }
            return Ok(Some(at));
        }
        Ok(None)
    }

    /// The constructor form of an argument's weak head normal form. Ordinary
    /// reduction demands the same argument at this point of the same
    /// definition, so reducing it here adds no demand.
    fn head(&mut self, a: Arg) -> R<Head> {
        if a & NAT != 0 {
            return Ok(Head::Nat(a & !NAT));
        }
        let v = a as u32;
        let mut w = self.whnf(v)?;
        if let Val::Str(e) = self.vals[w as usize] {
            let x = self.expand_str(e)?;
            w = self.whnf(x)?;
        }
        let value = self.vals[w as usize];
        Ok(match value {
            Val::Nat(n) => match self.nats[n as usize] {
                NatLit::Small(k) if k & NAT == 0 => Head::Nat(k),
                _ => Head::BigNat(n),
            },
            Val::Const { ci, spine, .. } => {
                let info = self.const_view(ci)?;
                if info.ctor.is_some() {
                    Head::Ctor {
                        canon: info.canon,
                        spine,
                    }
                } else {
                    Head::Stuck
                }
            }
            _ => Head::Stuck,
        })
    }

    /// Whether `h` is the guard's constructor. A natural literal is `zero` or
    /// `succ` of its predecessor.
    fn guard_matches(&mut self, g: Guard, h: Head) -> R<bool> {
        Ok(match h {
            Head::Nat(k) => {
                let Some((zero, succ)) = self.nat_canons()? else {
                    return Ok(false);
                };
                (g.ctor == zero && k == 0 && g.nfields == 0)
                    || (g.ctor == succ && k != 0 && g.nfields == 1)
            }
            Head::BigNat(_) => {
                let Some((_, succ)) = self.nat_canons()? else {
                    return Ok(false);
                };
                g.ctor == succ && g.nfields == 1
            }
            Head::Ctor { canon, spine } => {
                canon == g.ctor
                    && self.cells[spine as usize].len == u32::from(g.nparams) + u32::from(g.nfields)
            }
            Head::Stuck => false,
        })
    }

    /// Canonical names of `Nat.zero` and `Nat.succ`, once per attempt.
    fn nat_canons(&mut self) -> R<Option<(u32, u32)>> {
        if let Some(c) = self.derived.nat {
            return Ok(c);
        }
        let c = match self.nat_ctors()? {
            Some((_, zero, succ)) => {
                Some((self.const_view(zero)?.canon, self.const_view(succ)?.canon))
            }
            None => None,
        };
        self.derived.nat = Some(c);
        Ok(c)
    }

    /// Capture: release heat and "no rule" entries, which belong to
    /// this attempt (a starved derivation's 0 says nothing about a later
    /// one), and keep only positive trees in `trees`. `list` and `rules` hold
    /// positive trees only and are kept as they are, with their templates.
    pub(super) fn keep_trees(&mut self) -> R<()> {
        self.steps_by(self.derived.trees.len() as u64 + 1)?;
        let heat = std::mem::take(&mut self.derived.heat);
        retention::drop_map(self, heat)?;
        let all = std::mem::take(&mut self.derived.trees);
        let mut kept = Map::default();
        for (&key, &tree) in &all {
            if tree != 0 {
                map_put(self.b, &mut self.reserved, &mut kept, key, tree)?;
            }
        }
        retention::drop_map(self, all)?;
        self.derived.trees = kept;
        Ok(())
    }

    /// Derive and install a tree for `(ci, li)`; returns its index + 1 or 0.
    #[cold]
    fn derive(&mut self, ci: u32, li: u32) -> R<u32> {
        self.derived.derivations += 1;
        let saved = self.bounds;
        let allowance = self.limit.saturating_sub(self.steps) / 2;
        let mut tree = 0;
        let stores = (
            self.derived.templates.len(),
            self.derived.tnodes.len(),
            self.derived.titems.len(),
        );
        if allowance != 0 {
            let depth = self.binders.len();
            self.derived.base = (self.vals.len() as u32, self.envs.len() as u32);
            self.derived.deriving = true;
            self.limit_total(self.steps.saturating_add(DERIVE_BUDGET.min(allowance)));
            let mut rules = Vec::new();
            let r = self.derive_rules(ci, li, &mut rules);
            self.restore_bounds(saved);
            self.binders.truncate(depth);
            self.derived.deriving = false;
            match r {
                Ok(Some(arity)) if !rules.is_empty() => {
                    // Paths that diverge test different constructors of one
                    // argument, so at most one rule matches and order is free:
                    // try self-calls first, the usual step of a walk.
                    rules.sort_by_key(|r| !matches!(r.leaf, Leaf::Call(_)));
                    let start = u32::try_from(self.derived.rules.len())
                        .map_err(|_| ResourceError::Counter)?;
                    room_for(self, rules.len())?;
                    self.derived.rules.extend_from_slice(&rules);
                    room(self.b, &mut self.reserved, &mut self.derived.list, 1)?;
                    self.derived.list.push(Tree {
                        arity,
                        start,
                        len: rules.len() as u32,
                    });
                    tree = self.derived.list.len() as u32;
                }
                Ok(_) | Err(KErr::Unsupported | KErr::LiteralArithmetic) => {}
                // Our own allowance ran out; an outer allowance propagates.
                Err(KErr::Abort) if self.steps <= self.limit => {}
                Err(e) => return Err(e),
            }
        }
        // Templates recorded by a derivation that installs no tree are
        // unreferenced; their charged storage stays with the attempt.
        if tree == 0 {
            self.derived.templates.truncate(stores.0);
            self.derived.tnodes.truncate(stores.1);
            self.derived.titems.truncate(stores.2);
        }
        // Remember "no rule" for the run only when the derivation had its whole
        // allowance and a body to read; a starved derivation says nothing.
        if tree == 0 && allowance >= DERIVE_BUDGET {
            let info = *self.const_view(ci)?;
            if info.value.is_some() {
                self.env.set_no_rule(info.canon);
            }
        }
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.derived.trees,
            (ci, li),
            tree,
        )?;
        Ok(tree)
    }

    /// Open the telescope and explore splits; `Some(arity)` when the
    /// definition has a usable shape. `rules` is scratch, bounded by `MAX_RULES`.
    fn derive_rules(&mut self, ci: u32, li: u32, rules: &mut Vec<Rule>) -> R<Option<u8>> {
        let info = *self.const_view(ci)?;
        let (Some(mut value), Some(mut ty)) = (info.value, info.ty) else {
            return Ok(None);
        };
        // Arity: leading lambdas of the value. Dependence: which arguments a
        // later binder domain mentions (unknown support mentions everything).
        let mut arity = 0;
        let mut mentioned = 0u64;
        while arity < MAX_ARITY {
            self.step()?;
            let v = self.exprs.get(value, self.b)?;
            let ExprKind::Lambda(_, _, body, _) = v.kind(self.exprs, self.levels, self.b)? else {
                break;
            };
            let t = self.exprs.get(ty, self.b)?;
            let ExprKind::Pi(_, domain, rest, _) = t.kind(self.exprs, self.levels, self.b)? else {
                return Ok(None);
            };
            let support = self.bounded_support(domain)?;
            for i in 0..arity {
                if support == u64::MAX || support >> (arity - 1 - i) & 1 == 1 {
                    mentioned |= 1 << i;
                }
            }
            value = body;
            ty = rest;
            arity += 1;
        }
        if arity == 0 {
            return Ok(None);
        }
        let mut xs = [0u32; MAX_ARITY];
        let mut t = self.const_type(ci, li)?;
        for x in xs.iter_mut().take(arity) {
            let tw = self.whnf(t)?;
            let dom = self.binder_dom(tw)?;
            *x = self.open_local(dom)?;
            t = self.instantiate(tw, *x)?;
        }
        let mut splits = [Split {
            guard: Guard::default(),
            fields: [0; MAX_FIELDS],
            recursive: None,
        }; MAX_SPLITS];
        self.explore(ci, li, arity, &xs, xs, mentioned, &mut splits, 0, rules)?;
        Ok(Some(arity as u8))
    }

    /// Reduce `f args`; split on the blocking original argument or classify
    /// the leaf. `xs` are the original argument locals.
    #[allow(clippy::too_many_arguments)]
    fn explore(
        &mut self,
        ci: u32,
        li: u32,
        n: usize,
        xs: &[u32; MAX_ARITY],
        args: [u32; MAX_ARITY],
        mentioned: u64,
        splits: &mut [Split; MAX_SPLITS],
        depth: usize,
        rules: &mut Vec<Rule>,
    ) -> R<()> {
        // A rule must not replace an operation the kernel computes natively on
        // literals: `Nat.blt` would derive `blt (n+1) (m+1) ⟶ blt n m` and walk
        // literals one constructor at a time, millions of steps where a
        // concrete call makes one native comparison. A native operation on the
        // way to a guard drops the whole subtree; one in a leaf's own result
        // drops that leaf.
        self.derived.native = false;
        let call = self.call(ci, li, &args[..n])?;
        let r = self.whnf(call)?;
        let native = self.derived.native;

        let open: u64 = (0..n)
            .filter(|&i| args[i] == xs[i] && mentioned >> i & 1 == 0)
            .fold(0, |m, i| m | 1 << i);
        if depth < MAX_SPLITS
            && let Some(i) = self.blocker(r, &args[..n], open)?
        {
            if native {
                return Ok(());
            }
            let before = rules.len();
            self.split(ci, li, n, xs, args, mentioned, splits, depth, rules, i)?;
            if rules.len() != before || self.is_nat(args[i])? {
                return Ok(());
            }
            // No branch gave a rule: this path's residual, stuck on the
            // argument, is still a reduct of the call.
        }
        if native || rules.len() >= MAX_RULES {
            return Ok(());
        }
        let mut guards = [Guard::default(); MAX_SPLITS];
        for (g, s) in guards.iter_mut().zip(splits.iter()).take(depth) {
            *g = s.guard;
        }
        let rule = |leaf| Rule {
            guards,
            len: depth as u8,
            leaf,
        };
        // Field or argument leaf: the result is a pattern variable itself.
        if let Some(s) = self.slot_of(r, &args[..n], &splits[..depth])? {
            spare(rules, 1)?;
            rules.push(rule(Leaf::Value(s)));
            return Ok(());
        }
        // Self-call leaf: every split argument replaced by its own-family field.
        if depth > 0 && splits[..depth].iter().all(|s| s.recursive.is_some()) {
            let mut next = args;
            let mut fields = [0u8; MAX_SPLITS];
            for (g, s) in splits.iter().enumerate().take(depth) {
                let k = s.recursive.ok_or(ResourceError::Invariant)?;
                next[s.guard.arg as usize] = s.fields[k as usize];
                fields[g] = k;
            }
            let folded = self.call(ci, li, &next[..n])?;
            let r2 = self.whnf(folded)?;
            if !self.derived.native && self.same(r, r2)? {
                spare(rules, 1)?;
                rules.push(rule(Leaf::Call(fields)));
                return Ok(());
            }
        }
        // Template leaf: the residual itself. Under a natural
        // number guard only an application of a pattern variable to pattern
        // variables: a template that rebuilds constant applications there can
        // replay recursion over a literal one constructor at a time, which a
        // cached structural unfolding of a native operation hides from the
        // `native` check.
        let apps_only = self.nat_guarded(&splits[..depth])?;
        if let Some(t) = self.template_leaf(r, &args[..n], xs, &splits[..depth], apps_only)? {
            // An index that does not fit withholds the leaf.
            let Ok(at) = u32::try_from(self.derived.templates.len()) else {
                return Ok(());
            };
            if at >= 1 << 24 {
                return Ok(());
            }
            room(self.b, &mut self.reserved, &mut self.derived.templates, 1)?;
            self.derived.templates.push(t);
            let [a, b, c, _] = at.to_le_bytes();
            spare(rules, 1)?;
            rules.push(rule(Leaf::Template([a, b, c])));
        }
        Ok(())
    }

    /// Record `r` as a template over this path's pattern variables and store
    /// it; `None` when it is too large, mentions another local, or has a form
    /// readback does not record. Giving up only withholds a rule.
    fn template_leaf(
        &mut self,
        r: u32,
        args: &[u32],
        xs: &[u32; MAX_ARITY],
        splits: &[Split],
        apps_only: bool,
    ) -> R<Option<Template>> {
        let local = |k: &Kernel<'_, '_>, x: u32| match k.vals[x as usize] {
            Val::Local { id, spine: 0 } => Some(id),
            _ => None,
        };
        let mut rb = Readback {
            pats: Vec::new(),
            ctors: [(NONE, 0); MAX_SPLITS],
            nctors: 0,
            nodes: Vec::new(),
            items: Vec::new(),
            memo: Map::default(),
            visits: 0,
            closed_below: (0, 0),
        };
        spare(&mut rb.pats, MAX_ARITY + MAX_SPLITS * (MAX_FIELDS + 1))?;
        let mut newest_ok = true;
        for (j, &a) in args.iter().enumerate() {
            if a == xs[j] {
                let id = local(self, a).ok_or(ResourceError::Invariant)?;
                rb.pats.push((id, TNode::Slot(Slot::Arg(j as u8))));
                newest_ok &= a >= self.derived.base.0;
            }
        }
        for (g, s) in splits.iter().enumerate() {
            let i = s.guard.arg as usize;
            let id = local(self, xs[i]).ok_or(ResourceError::Invariant)?;
            rb.pats.push((id, TNode::Matched(g as u8)));
            newest_ok &= xs[i] >= self.derived.base.0;
            rb.ctors[g] = (args[i], g as u8);
            for k in 0..s.guard.nfields as usize {
                let y = s.fields[k];
                let id = local(self, y).ok_or(ResourceError::Invariant)?;
                rb.pats
                    .push((id, TNode::Slot(Slot::Field(g as u8, k as u8))));
                newest_ok &= y >= self.derived.base.0;
            }
        }
        rb.nctors = splits.len();
        if newest_ok {
            rb.closed_below = self.derived.base;
        }
        // Temporaries start small and grow within the fixed bounds above.
        spare(&mut rb.nodes, 16)?;
        spare(&mut rb.items, 16)?;
        rb.memo.try_reserve(16).map_err(|_| alloc_failed())?;
        let Some(root) = self.read_value(&mut rb, r, 0, splits)? else {
            return Ok(None);
        };
        if splits.is_empty() && rb.nodes.len() > FUSED_NODES {
            return Ok(None);
        }
        let app = |n: &TNode| matches!(n, TNode::Slot(_) | TNode::Matched(_) | TNode::App { .. });
        if apps_only && (!rb.nodes.iter().all(app) || matches!(root, TRef::Closed(_))) {
            return Ok(None);
        }
        let nodes = u32::try_from(self.derived.tnodes.len()).map_err(|_| ResourceError::Counter)?;
        let items = u32::try_from(self.derived.titems.len()).map_err(|_| ResourceError::Counter)?;
        room(
            self.b,
            &mut self.reserved,
            &mut self.derived.tnodes,
            rb.nodes.len(),
        )?;
        self.derived.tnodes.extend_from_slice(&rb.nodes);
        room(
            self.b,
            &mut self.reserved,
            &mut self.derived.titems,
            rb.items.len(),
        )?;
        self.derived.titems.extend_from_slice(&rb.items);
        Ok(Some(Template {
            nodes,
            items,
            len: rb.nodes.len() as u16,
            root,
        }))
    }

    /// Whether a guard on the path tests a natural number constructor.
    fn nat_guarded(&mut self, splits: &[Split]) -> R<bool> {
        let Some((zero, succ)) = self.nat_canons()? else {
            return Ok(false);
        };
        Ok(splits
            .iter()
            .any(|s| s.guard.ctor == zero || s.guard.ctor == succ))
    }

    /// Whether `x`'s type is the natural numbers.
    fn is_nat(&mut self, x: u32) -> R<bool> {
        let Some(family) = self.nat_family()? else {
            return Ok(false);
        };
        let Val::Local { id, .. } = self.vals[x as usize] else {
            return Ok(false);
        };
        let ty = self.locals[id as usize];
        let ty = self.whnf(ty)?;
        Ok(match self.vals[ty as usize] {
            Val::Const { ci, .. } => self.const_view(ci)?.canon == family,
            _ => false,
        })
    }

    /// Canonical id of the natural number family.
    fn nat_family(&mut self) -> R<Option<u32>> {
        Ok(match self.nat_ctors()? {
            Some((nat, _, _)) => Some(self.const_view(nat)?.canon),
            None => None,
        })
    }

    fn read_node(rb: &mut Readback, node: TNode) -> R<Option<TRef>> {
        if rb.nodes.len() >= TEMPLATE_NODES {
            return Ok(None);
        }
        spare(&mut rb.nodes, 1)?;
        rb.nodes.push(node);
        Ok(Some(TRef::Node((rb.nodes.len() - 1) as u16)))
    }

    fn read_memo(rb: &mut Readback, key: (bool, u32), t: TRef) -> R<()> {
        if rb.memo.len() == rb.memo.capacity() {
            rb.memo
                .try_reserve(rb.memo.len().max(16))
                .map_err(|_| alloc_failed())?;
        }
        rb.memo.insert(key, t);
        Ok(())
    }

    /// The template of value `v`; `Closed(v)` when it mentions no pattern
    /// variable.
    fn read_value(
        &mut self,
        rb: &mut Readback,
        mut v: u32,
        depth: u32,
        splits: &[Split],
    ) -> R<Option<TRef>> {
        // A let-bound thunk keeps its mark only as itself: rebuilding it would
        // lose `let_fold_allowed`'s budget, so it stays only when closed.
        if self.let_bit(2 * u64::from(v)) {
            return Ok((v < rb.closed_below.0).then_some(TRef::Closed(v)));
        }
        while let Val::Ind(t) = self.vals[v as usize] {
            v = t;
        }
        if let Some(&t) = rb.memo.get(&(false, v)) {
            return Ok(Some(t));
        }
        if v < rb.closed_below.0 {
            return Ok(Some(TRef::Closed(v)));
        }
        rb.visits += 1;
        if rb.visits > TEMPLATE_VISITS || depth > TEMPLATE_DEPTH {
            return Ok(None);
        }
        self.step()?;
        let out = 'out: {
            // A split argument's constructor stands for the matched argument.
            for &(c, g) in &rb.ctors[..rb.nctors] {
                if c == v {
                    break 'out Self::read_node(rb, TNode::Matched(g))?;
                }
            }
            match self.vals[v as usize] {
                Val::Local { id, spine } => {
                    let Some(&(_, pat)) = rb.pats.iter().find(|p| p.0 == id) else {
                        break 'out None;
                    };
                    let Some(head) = Self::read_node(rb, pat)? else {
                        break 'out None;
                    };
                    if spine == 0 {
                        break 'out Some(head);
                    }
                    if self.cells[spine as usize].len as usize > MAX_ARITY {
                        break 'out None;
                    }
                    let Some((items, len, _)) = self.read_spine(rb, spine, depth, splits, false)?
                    else {
                        break 'out None;
                    };
                    Self::read_node(rb, TNode::App { head, items, len })?
                }
                Val::Const { ci, li, spine } => {
                    let Some((items, len, closed)) =
                        self.read_spine(rb, spine, depth, splits, true)?
                    else {
                        break 'out None;
                    };
                    // A natural number recursor waiting on a pattern variable
                    // would walk a literal one constructor at a time.
                    if !closed
                        && let Some(rec) = self.const_view(ci)?.rec
                        && Some(rec.family) == self.nat_family()?
                    {
                        let major = (rec.common + rec.nidx) as usize;
                        if major < len as usize
                            && matches!(rb.items[items as usize + major], TItem::Arg(TRef::Node(_)))
                        {
                            break 'out None;
                        }
                    }
                    if closed {
                        rb.items.truncate(items as usize);
                        break 'out Some(TRef::Closed(v));
                    }
                    Self::read_node(rb, TNode::Const { ci, li, items, len })?
                }
                Val::Delayed { e, env, li } => match self.read_env(rb, env, depth + 1, splits)? {
                    None => None,
                    Some(TRef::Closed(_)) => Some(TRef::Closed(v)),
                    Some(env) => Self::read_node(rb, TNode::Delayed { e, li, env })?,
                },
                Val::Lam(c) | Val::Pi(c) | Val::LamTy(c) => {
                    let form = match self.vals[v as usize] {
                        Val::Lam(_) => 0,
                        Val::Pi(_) => 1,
                        _ => 2,
                    };
                    let dl = self.exprs.get(c.dom, self.b)?.loose_range();
                    let bl = self.exprs.get(c.body, self.b)?.loose_range();
                    let loose = dl.max(bl.saturating_sub(1));
                    match self.read_env(rb, c.env, depth + 1, splits)? {
                        None => None,
                        Some(TRef::Closed(_)) => Some(TRef::Closed(v)),
                        Some(env) => Self::read_node(
                            rb,
                            TNode::Clo {
                                form,
                                loose,
                                dom: c.dom,
                                body: c.body,
                                li: c.li,
                                env,
                            },
                        )?,
                    }
                }
                Val::Arrow { dom, cod } => {
                    let (Some(d), Some(c)) = (
                        self.read_value(rb, dom, depth + 1, splits)?,
                        self.read_value(rb, cod, depth + 1, splits)?,
                    ) else {
                        break 'out None;
                    };
                    if matches!((d, c), (TRef::Closed(_), TRef::Closed(_))) {
                        Some(TRef::Closed(v))
                    } else {
                        Self::read_node(rb, TNode::Arrow { dom: d, cod: c })?
                    }
                }
                Val::Proj { x, idx, sci } => match self.read_value(rb, x, depth + 1, splits)? {
                    None => None,
                    Some(TRef::Closed(_)) => Some(TRef::Closed(v)),
                    Some(x) => Self::read_node(rb, TNode::Proj { x, idx, sci })?,
                },
                Val::Nat(_) | Val::Sort(_) | Val::Str(_) => Some(TRef::Closed(v)),
                Val::Ind(_) => return Err(ResourceError::Invariant.into()),
            }
        };
        if let Some(t) = out {
            Self::read_memo(rb, (false, v), t)?;
        }
        Ok(out)
    }

    /// Items of spine `s`, root first, appended to the item store: `(start,
    /// len, every item closed)`. Projection cells are copied unless `proj` is
    /// false, which gives up on them.
    fn read_spine(
        &mut self,
        rb: &mut Readback,
        s: u32,
        depth: u32,
        splits: &[Split],
        proj: bool,
    ) -> R<Option<(u32, u32, bool)>> {
        let len = self.cells[s as usize].len as usize;
        if len > TEMPLATE_VISITS {
            return Ok(None);
        }
        let cells = self.spine_items(s)?;
        let r = (|| {
            let start = rb.items.len() as u32;
            let mut closed = true;
            // Children first: read every argument, then append the items.
            let mut refs = [TRef::Closed(0); 64];
            if cells.len() > refs.len() {
                return Ok(None);
            }
            for (k, &c) in cells.iter().enumerate() {
                let cell = self.cells[c as usize];
                if cell.tag != 0 {
                    if !proj {
                        return Ok(None);
                    }
                    continue;
                }
                let Some(t) = self.read_value(rb, cell.item, depth + 1, splits)? else {
                    return Ok(None);
                };
                closed &= matches!(t, TRef::Closed(_));
                refs[k] = t;
            }
            let start = start.max(rb.items.len() as u32);
            if rb.items.len() + cells.len() > TEMPLATE_VISITS {
                return Ok(None);
            }
            spare(&mut rb.items, cells.len())?;
            for (k, &c) in cells.iter().enumerate() {
                let cell = self.cells[c as usize];
                rb.items.push(if cell.tag != 0 {
                    TItem::Proj {
                        tag: cell.tag,
                        sci: cell.item,
                    }
                } else {
                    TItem::Arg(refs[k])
                });
            }
            Ok(Some((start, cells.len() as u32, closed)))
        })();
        self.scratch_finish(r, [cells])
    }

    /// The template of environment `env`.
    fn read_env(
        &mut self,
        rb: &mut Readback,
        env: u32,
        depth: u32,
        splits: &[Split],
    ) -> R<Option<TRef>> {
        if env == 0 || env < rb.closed_below.1 {
            return Ok(Some(TRef::Closed(env)));
        }
        if let Some(&t) = rb.memo.get(&(true, env)) {
            return Ok(Some(t));
        }
        rb.visits += 1;
        if rb.visits > TEMPLATE_VISITS || depth > TEMPLATE_DEPTH {
            return Ok(None);
        }
        self.step()?;
        let node = self.envs[env as usize];
        // A typed environment asserts its value's type; rebuilding it with a
        // caller's argument is left to ordinary evaluation.
        if node.ty != NONE {
            return Ok(None);
        }
        let Some(parent) = self.read_env(rb, node.parent, depth + 1, splits)? else {
            return Ok(None);
        };
        let Some(val) = self.read_value(rb, node.val, depth + 1, splits)? else {
            return Ok(None);
        };
        let ty = if node.ty == NONE {
            None
        } else {
            let Some(t) = self.read_value(rb, node.ty, depth + 1, splits)? else {
                return Ok(None);
            };
            Some(t)
        };
        let closed = |t: TRef| matches!(t, TRef::Closed(_));
        let out = if closed(parent) && closed(val) && ty.is_none_or(closed) {
            Some(TRef::Closed(env))
        } else {
            Self::read_node(rb, TNode::Env { parent, val, ty })?
        };
        if let Some(t) = out {
            Self::read_memo(rb, (true, env), t)?;
        }
        Ok(out)
    }

    /// Split on argument `i`: one branch per constructor of its family.
    #[allow(clippy::too_many_arguments)]
    fn split(
        &mut self,
        ci: u32,
        li: u32,
        n: usize,
        xs: &[u32; MAX_ARITY],
        args: [u32; MAX_ARITY],
        mentioned: u64,
        splits: &mut [Split; MAX_SPLITS],
        depth: usize,
        rules: &mut Vec<Rule>,
        i: usize,
    ) -> R<()> {
        let Val::Local { id, spine: 0 } = self.vals[args[i] as usize] else {
            return Ok(());
        };
        let ty = self.locals[id as usize];
        let ty = self.whnf(ty)?;
        let Val::Const {
            ci: family,
            li: family_li,
            spine: params,
        } = self.vals[ty as usize]
        else {
            return Ok(());
        };
        let fam = *self.const_view(family)?;
        let Some(ind) = fam.ind else {
            return Ok(());
        };
        if ind.nidx != 0
            || ind.ctors.len() > MAX_CTORS
            || ind.nparams as usize > MAX_ARITY
            || self.cells[params as usize].len != ind.nparams
        {
            return Ok(());
        }
        let Some(ps) = self.spine_args_opt(params)? else {
            return Ok(());
        };
        let mut pv = [0u32; MAX_ARITY];
        pv[..ps.len()].copy_from_slice(&ps);
        self.recycle(ps)?;
        let np = ind.nparams as usize;
        let binders = self.binders.len();
        for rule in ind.ctors {
            if rule.num_fields as usize > MAX_FIELDS {
                continue;
            }
            let c = self.const_info(rule.constructor)?;
            let canon = self.const_view(c)?.canon;
            let mut t = self.const_type(c, family_li)?;
            let mut s = 0;
            for &p in &pv[..np] {
                let tw = self.whnf(t)?;
                t = self.instantiate(tw, p)?;
                s = self.cell(s, p, 0)?;
            }
            let mut fields = [0u32; MAX_FIELDS];
            let mut recursive = None;
            let mut unique = true;
            for (k, field) in fields.iter_mut().enumerate().take(rule.num_fields as usize) {
                let tw = self.whnf(t)?;
                let dom = self.binder_dom(tw)?;
                let y = self.open_local(dom)?;
                let dw = self.whnf(dom)?;
                if let Val::Const { ci: d, .. } = self.vals[dw as usize]
                    && self.const_view(d)?.canon == fam.canon
                {
                    unique &= recursive.is_none();
                    recursive = Some(k as u8);
                }
                *field = y;
                s = self.cell(s, y, 0)?;
                t = self.instantiate(tw, y)?;
            }
            let value = self.push(Val::Const {
                ci: c,
                li: family_li,
                spine: s,
            })?;
            splits[depth] = Split {
                guard: Guard {
                    arg: i as u8,
                    nparams: np as u8,
                    nfields: rule.num_fields as u8,
                    ctor: canon,
                },
                fields,
                recursive: if unique { recursive } else { None },
            };
            let mut next = args;
            next[i] = value;
            self.explore(ci, li, n, xs, next, mentioned, splits, depth + 1, rules)?;
            self.binders.truncate(binders);
        }
        Ok(())
    }

    /// `ci` at `li` applied to `args`.
    fn call(&mut self, ci: u32, li: u32, args: &[u32]) -> R<u32> {
        let mut s = 0;
        for &a in args {
            s = self.cell(s, a, 0)?;
        }
        self.push(Val::Const { ci, li, spine: s })
    }

    /// The original argument whose value a stuck recursor in `r` waits on.
    fn blocker(&mut self, mut r: u32, args: &[u32], open: u64) -> R<Option<usize>> {
        for _ in 0..8 {
            r = self.force(r)?;
            match self.vals[r as usize] {
                Val::Const { ci, spine, .. } => {
                    let Some(rec) = self.const_view(ci)?.rec else {
                        return Ok(None);
                    };
                    let major_at = (rec.common + rec.nidx) as usize;
                    let prefix = self.proj_prefix(spine).unwrap_or(spine);
                    if self.cells[prefix as usize].len as usize <= major_at {
                        return Ok(None);
                    }
                    let Some(items) = self.spine_args_opt(prefix)? else {
                        return Ok(None);
                    };
                    let major = items[major_at];
                    self.recycle(items)?;
                    let m = self.whnf(major)?;
                    return Ok((0..args.len()).find(|&i| open >> i & 1 == 1 && args[i] == m));
                }
                Val::Proj { x, .. } => r = self.whnf(x)?,
                _ => return Ok(None),
            }
        }
        Ok(None)
    }

    /// The pattern variable `r` is, if any.
    fn slot_of(&mut self, r: u32, args: &[u32], splits: &[Split]) -> R<Option<Slot>> {
        let r = self.force(r)?;
        if !matches!(self.vals[r as usize], Val::Local { spine: 0, .. }) {
            return Ok(None);
        }
        for (g, s) in splits.iter().enumerate() {
            for k in 0..s.guard.nfields as usize {
                if s.fields[k] == r {
                    return Ok(Some(Slot::Field(g as u8, k as u8)));
                }
            }
        }
        Ok(args
            .iter()
            .position(|&a| a == r)
            .map(|j| Slot::Arg(j as u8)))
    }

    /// Exact structural identity of two values: same forms, constants, level
    /// instances, locals, literals and closure syntax, with identical spines
    /// and identical environment entries wherever the closure or thunk syntax
    /// reads its environment (an entry it never reads cannot affect its
    /// meaning). No reduction or conversion rule is used; `false` proves
    /// nothing.
    ///
    /// The work stack is a temporary with a fixed bound: at most three pushes
    /// per visit and `SAME_BUDGET` visits.
    fn same(&mut self, a: u32, c: u32) -> R<bool> {
        let mut todo: Vec<Pair> = Vec::new();
        spare(&mut todo, 16)?;
        todo.push(Pair::Value(a, c));
        let mut visits = 0u32;
        while let Some(pair) = todo.pop() {
            visits += 1;
            if visits > SAME_BUDGET {
                return Ok(false);
            }
            self.step()?;
            let (mut x, mut y) = match pair {
                Pair::Env(x, y, read) => {
                    if !self.same_env(x, y, read, &mut todo)? {
                        return Ok(false);
                    }
                    continue;
                }
                Pair::Value(x, y) => (x, y),
            };
            while let Val::Ind(t) = self.vals[x as usize] {
                x = t;
            }
            while let Val::Ind(t) = self.vals[y as usize] {
                y = t;
            }
            if x == y {
                continue;
            }
            // A thunk that does not match the other side syntactically is
            // forced: evaluation only takes reduction steps, so both sides
            // still reduce to the compared values.
            let delayed = |v: Val| matches!(v, Val::Delayed { .. });
            let (vx, vy) = (self.vals[x as usize], self.vals[y as usize]);
            let syntactic = matches!((vx, vy), (Val::Delayed { e, li, .. }, Val::Delayed { e: e2, li: l2, .. }) if e == e2 && li == l2);
            if !syntactic && (delayed(vx) || delayed(vy)) {
                x = self.force(x)?;
                y = self.force(y)?;
                spare(&mut todo, 1)?;
                todo.push(Pair::Value(x, y));
                continue;
            }
            spare(&mut todo, 2)?;
            match (self.vals[x as usize], self.vals[y as usize]) {
                (
                    Val::Delayed { e, env: v, li },
                    Val::Delayed {
                        e: e2,
                        env: v2,
                        li: l2,
                    },
                ) if e == e2 && li == l2 => {
                    let read = self.read_plan(e)?;
                    todo.push(Pair::Env(v, v2, read));
                }
                (Val::Lam(p), Val::Lam(q))
                | (Val::Pi(p), Val::Pi(q))
                | (Val::LamTy(p), Val::LamTy(q))
                    if p.dom == q.dom && p.body == q.body && p.li == q.li =>
                {
                    let read = match (self.read_plan(p.dom)?, self.read_plan(p.body)?) {
                        (Some(d), Some(b)) => Some(std::array::from_fn(|i| {
                            d[i] | (b[i] >> 1) | if i < 3 { b[i + 1] << 63 } else { 0 }
                        })),
                        _ => None,
                    };
                    todo.push(Pair::Env(p.env, q.env, read));
                }
                (Val::Arrow { dom, cod }, Val::Arrow { dom: d2, cod: c2 }) => {
                    todo.push(Pair::Value(dom, d2));
                    todo.push(Pair::Value(cod, c2));
                }
                (
                    Val::Proj { x: p, idx, sci },
                    Val::Proj {
                        x: q,
                        idx: i2,
                        sci: s2,
                    },
                ) if idx == i2 && sci == s2 => {
                    todo.push(Pair::Value(p, q));
                }
                (Val::Local { id, spine }, Val::Local { id: i2, spine: s2 }) if id == i2 => {
                    if !self.same_spine(spine, s2, &mut todo)? {
                        return Ok(false);
                    }
                }
                (
                    Val::Const { ci, li, spine },
                    Val::Const {
                        ci: c2,
                        li: l2,
                        spine: s2,
                    },
                ) if ci == c2 && li == l2 => {
                    if !self.same_spine(spine, s2, &mut todo)? {
                        return Ok(false);
                    }
                }
                (Val::Nat(p), Val::Nat(q)) => {
                    let equal = match (&self.nats[p as usize], &self.nats[q as usize]) {
                        (NatLit::Small(u), NatLit::Small(v)) => u == v,
                        (NatLit::Big(u), NatLit::Big(v)) => u == v,
                        _ => false,
                    };
                    if !equal {
                        return Ok(false);
                    }
                }
                (Val::Sort(p), Val::Sort(q)) if p == q => {}
                (Val::Str(p), Val::Str(q)) if p == q => {}
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    /// Pair the entries of two environments that `read` selects (every entry
    /// when the read set is unknown). Entry `i` is the `i`-th from the top.
    fn same_env(
        &mut self,
        mut x: u32,
        mut y: u32,
        read: Option<[u64; 4]>,
        todo: &mut Vec<Pair>,
    ) -> R<bool> {
        let mut i = 0usize;
        loop {
            if x == y {
                return Ok(true);
            }
            let remaining = match read {
                None => true,
                Some(m) => (i..256).any(|k| m[k / 64] >> (k % 64) & 1 == 1),
            };
            if !remaining {
                return Ok(true);
            }
            if x == 0 || y == 0 || i >= 256 && read.is_some() {
                return Ok(false);
            }
            self.step()?;
            let (p, q) = (self.envs[x as usize], self.envs[y as usize]);
            let wanted = read.is_none_or(|m| m[i / 64] >> (i % 64) & 1 == 1);
            if wanted {
                if (p.ty == NONE) != (q.ty == NONE) {
                    return Ok(false);
                }
                spare(todo, 2)?;
                todo.push(Pair::Value(p.val, q.val));
                if p.ty != NONE {
                    todo.push(Pair::Value(p.ty, q.ty));
                }
            }
            x = p.parent;
            y = q.parent;
            i += 1;
        }
    }

    /// Pair the cells of two spines; projection cells must agree exactly.
    fn same_spine(&mut self, mut s: u32, mut t: u32, todo: &mut Vec<Pair>) -> R<bool> {
        if self.cells[s as usize].len != self.cells[t as usize].len {
            return Ok(false);
        }
        while s != t && s != 0 {
            self.step()?;
            let (p, q) = (self.cells[s as usize], self.cells[t as usize]);
            if p.tag != q.tag {
                return Ok(false);
            }
            if p.tag == 0 {
                spare(todo, 1)?;
                todo.push(Pair::Value(p.item, q.item));
            } else if p.item != q.item {
                return Ok(false);
            }
            s = p.prev;
            t = q.prev;
        }
        Ok(s == t)
    }
}

/// Charge room for `n` more rules in the attempt's rule store.
fn room_for(k: &mut Kernel<'_, '_>, n: usize) -> R<()> {
    room(k.b, &mut k.reserved, &mut k.derived.rules, n)
}
