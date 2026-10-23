//! Materialized theorem value-then-type copy and sharing.
//! No checking starts until both roots complete. No copied node is a declaration
//! publication root; the caller's declaration watermark owns generated syntax.
use crate::resource::{Budget, ResourceError};
use crate::syntax::expressions::{ExprId, ExprKind, ExpressionError, Expressions};
use crate::syntax::levels::{LevelId, LevelKind, Levels, NameId};
use crate::syntax::names::{Component, NameError, Names};
use std::hash::Hasher;
use std::mem::size_of;
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Error {
    Resource(ResourceError),
    NumericRange,
}
impl From<ResourceError> for Error {
    fn from(e: ResourceError) -> Self {
        Self::Resource(e)
    }
}
impl From<ExpressionError> for Error {
    fn from(e: ExpressionError) -> Self {
        match e {
            ExpressionError::Resource(e) => e.into(),
            ExpressionError::NumericRange => Self::NumericRange,
            _ => ResourceError::Invariant.into(),
        }
    }
}
impl From<NameError> for Error {
    fn from(e: NameError) -> Self {
        match e {
            NameError::Resource(e) => e.into(),
            NameError::NumericRange => Self::NumericRange,
            _ => ResourceError::Invariant.into(),
        }
    }
}
#[derive(Clone, Copy, Default)]
struct Bucket {
    key: u32,
    value: u32,
}
const _: () = assert!(size_of::<Bucket>() == 8);
/// value zero is vacant. Every indexed destination is a fresh non-atom node:
/// name/level zero bypass both indices; expression copies follow >=1 originals.
/// Thus all actual destinations are nonzero, including a valid u32::MAX slot.
struct Index {
    entries: Vec<Bucket>,
    used: usize,
    raw: bool,
}
impl Index {
    fn new(raw: bool) -> Self {
        Self {
            entries: Vec::new(),
            used: 0,
            raw,
        }
    }
    fn hash(&self, key: u32) -> u32 {
        if self.raw {
            key
        } else {
            let mut h = crate::syntax::hash::FastHasher::new();
            h.write_u32(key);
            h.finish() as u32
        }
    }
    fn find(
        &self,
        key: u32,
        b: &mut Budget,
        mut equal: impl FnMut(u32, &mut Budget) -> Result<bool, ResourceError>,
    ) -> Result<Option<u32>, ResourceError> {
        if self.entries.is_empty() {
            return Ok(None);
        }
        let mask = self.entries.len() - 1;
        let mut slot = self.hash(key) as usize & mask;
        for _ in 0..self.entries.len() {
            b.charge_work(1)?;
            let e = self.entries[slot];
            if e.value == 0 {
                return Ok(None);
            }
            if e.key == key && equal(e.value, b)? {
                return Ok(Some(e.value));
            }
            slot = (slot + 1) & mask;
        }
        Err(ResourceError::Invariant)
    }
    fn empty(entries: &[Bucket], hash: u32, b: &mut Budget) -> Result<usize, ResourceError> {
        let mask = entries
            .len()
            .checked_sub(1)
            .ok_or(ResourceError::Invariant)?;
        let mut slot = hash as usize & mask;
        for _ in 0..entries.len() {
            b.charge_work(1)?;
            if entries[slot].value == 0 {
                return Ok(slot);
            }
            slot = (slot + 1) & mask;
        }
        Err(ResourceError::Invariant)
    }
    fn insert(&mut self, key: u32, value: u32, b: &mut Budget) -> Result<(), ResourceError> {
        if value == 0 {
            return Err(ResourceError::Invariant);
        }
        if self.used + 1 > self.entries.len() / 4 * 3 {
            let capacity = self
                .entries
                .len()
                .checked_mul(2)
                .ok_or(ResourceError::Counter)?
                .max(16);
            let mut next = Vec::new();
            b.grow_vec(&mut next, capacity)?;
            let r = (|| {
                b.charge_work(capacity as u64 + 1)?;
                next.resize(capacity, Bucket::default());
                for e in self.entries.iter().copied().filter(|e| e.value != 0) {
                    let slot = Self::empty(&next, self.hash(e.key), b)?;
                    next[slot] = e;
                }
                Ok(())
            })();
            if let Err(e) = r {
                release(next, b)?;
                return Err(e);
            }
            let old = std::mem::replace(&mut self.entries, next);
            release(old, b)?;
        }
        let slot = Self::empty(&self.entries, self.hash(key), b)?;
        self.entries[slot] = Bucket { key, value };
        self.used += 1;
        Ok(())
    }
}
fn release<T>(v: Vec<T>, b: &mut Budget) -> Result<(), ResourceError> {
    let bytes = v
        .capacity()
        .checked_mul(size_of::<T>())
        .ok_or(ResourceError::Counter)?;
    drop(v);
    b.release(bytes as u64)
}
#[derive(Clone, Copy)]
struct Node {
    arena: u32,
    id: u32,
}
impl Node {
    fn name(id: NameId) -> Self {
        Self { arena: 0, id: id.0 }
    }
    fn level(id: LevelId) -> Self {
        Self {
            arena: 1,
            id: id.slot(),
        }
    }
    fn expr(id: ExprId) -> Self {
        Self {
            arena: 2,
            id: id.slot(),
        }
    }
}
#[derive(Clone, Copy)]
struct Frame {
    node: Node,
    next: u32,
}
const _: () = assert!(size_of::<Frame>() == 12);
struct Stores<'a> {
    names: &'a mut Names,
    levels: &'a mut Levels,
    expressions: &'a mut Expressions,
}
struct Copier<'a> {
    stores: Stores<'a>,
    ends: [usize; 3],
    sources: [Index; 3],
    raw: [Index; 3],
    frames: Vec<Frame>,
    bytes: Vec<u8>,
    universes: Vec<LevelId>,
}
/// Caller owns all three same-origin tables and one ledger. Panic unwinds the
/// entire run; partial copies never escape as a pair or as unchanged originals.
pub(crate) fn copy(
    names: &mut Names,
    levels: &mut Levels,
    expressions: &mut Expressions,
    value: ExprId,
    ty: ExprId,
    b: &mut Budget,
) -> Result<(ExprId, ExprId), Error> {
    copy_inner(names, levels, expressions, value, ty, b)
}
fn copy_inner(
    names: &mut Names,
    levels: &mut Levels,
    expressions: &mut Expressions,
    value: ExprId,
    ty: ExprId,
    b: &mut Budget,
) -> Result<(ExprId, ExprId), Error> {
    b.charge_work(10)?;
    let ends = [names.len(), levels.len(), expressions.len()];
    let mut c = Copier {
        stores: Stores {
            names,
            levels,
            expressions,
        },
        ends,
        sources: std::array::from_fn(|_| Index::new(false)),
        raw: std::array::from_fn(|_| Index::new(true)),
        frames: Vec::new(),
        bytes: Vec::new(),
        universes: Vec::new(),
    };
    let result = (|| {
        let value = c.root(value, b)?;
        let ty = c.root(ty, b)?;
        Ok((value, ty))
    })();
    // Evaluate every cleanup even if an earlier release finds a broken ledger.
    let mut cleanup = Ok(());
    for index in c.sources.into_iter().chain(c.raw) {
        cleanup = cleanup.and(release(index.entries, b));
    }
    cleanup = cleanup.and(b.release_frames(c.frames.len()));
    cleanup = cleanup.and(release(c.frames, b));
    cleanup = cleanup.and(release(c.bytes, b));
    cleanup = cleanup.and(release(c.universes, b));
    cleanup?;
    result
}
fn mapped(sources: &[Index; 3], n: Node, b: &mut Budget) -> Result<u32, ResourceError> {
    if n.arena < 2 && n.id == 0 {
        return Ok(0);
    }
    sources[n.arena as usize]
        .find(n.id, b, |_, _| Ok(true))?
        .ok_or(ResourceError::Invariant)
}
impl Copier<'_> {
    fn push(&mut self, f: Frame, b: &mut Budget) -> Result<(), ResourceError> {
        let count = self.frames.len() + 1;
        b.reserve_frames(1)?;
        if let Err(e) = b.grow_vec(&mut self.frames, count) {
            b.release_frames(1)?;
            return Err(e);
        }
        self.frames.push(f);
        Ok(())
    }
    fn root(&mut self, root: ExprId, b: &mut Budget) -> Result<ExprId, Error> {
        self.push(
            Frame {
                node: Node::expr(root),
                next: 0,
            },
            b,
        )?;
        while let Some(mut f) = self.frames.pop() {
            b.release_frames(1)?;
            b.charge_work(1)?;
            b.observe(crate::resource::Event::MachineSteps, 1);
            let arena = f.node.arena as usize;
            if f.node.id as usize >= self.ends[arena] {
                return Err(ResourceError::Invariant.into());
            }
            if f.next == 0
                && ((arena < 2 && f.node.id == 0)
                    || self.sources[arena]
                        .find(f.node.id, b, |_, _| Ok(true))?
                        .is_some())
            {
                continue;
            }
            if let Some(child) = child(&self.stores, f.node, f.next, b)? {
                f.next = f.next.checked_add(1).ok_or(ResourceError::Counter)?;
                self.push(f, b)?;
                self.push(
                    Frame {
                        node: child,
                        next: 0,
                    },
                    b,
                )?;
                continue;
            }
            let key = key(
                &self.stores,
                &self.sources,
                f.node,
                &mut self.bytes,
                &mut self.universes,
                b,
            )?;
            let hash = hash(&key, b)?;
            let destination = if let Some(id) =
                self.raw[arena].find(hash, b, |id, b| matches(&self.stores, &key, id, b))?
            {
                id
            } else {
                let id = append(&mut self.stores, &key, b)?;
                self.raw[arena].insert(hash, id, b)?;
                id
            };
            self.sources[arena].insert(f.node.id, destination, b)?;
        }
        Ok(self
            .stores
            .expressions
            .resolve_slot(mapped(&self.sources, Node::expr(root), b)?, b)?)
    }
}
fn child(
    s: &Stores<'_>,
    n: Node,
    position: u32,
    b: &mut Budget,
) -> Result<Option<Node>, ResourceError> {
    let p = position as usize;
    Ok(match n.arena {
        0 => s
            .names
            .prefix(NameId(n.id), b)?
            .and_then(|prefix| (p == 0).then_some(Node::name(prefix))),
        1 => match s.levels.get(s.levels.resolve_slot(n.id, b)?, b)?.kind() {
            LevelKind::Zero => None,
            LevelKind::Param(name) => (p == 0).then_some(Node::name(name)),
            LevelKind::Succ(a) => (p == 0).then_some(Node::level(a)),
            LevelKind::Max(a, c) | LevelKind::IMax(a, c) => {
                [Node::level(a), Node::level(c)].get(p).copied()
            }
        },
        2 => match s
            .expressions
            .get(s.expressions.resolve_slot(n.id, b)?, b)?
            .kind(s.expressions, s.levels, b)?
        {
            ExprKind::Bound(_) | ExprKind::Free(_) | ExprKind::Natural(_) | ExprKind::String(_) => {
                None
            }
            ExprKind::Sort(l) => (p == 0).then_some(Node::level(l)),
            ExprKind::App(a, c) => [Node::expr(a), Node::expr(c)].get(p).copied(),
            ExprKind::Lambda(name, a, c, _) | ExprKind::Pi(name, a, c, _) => {
                [Node::name(name), Node::expr(a), Node::expr(c)]
                    .get(p)
                    .copied()
            }
            ExprKind::Let(name, a, c, d, _) => [
                Node::name(name),
                Node::expr(a),
                Node::expr(c),
                Node::expr(d),
            ]
            .get(p)
            .copied(),
            ExprKind::Projection(name, _, a) => [Node::name(name), Node::expr(a)].get(p).copied(),
            ExprKind::Constant(name, levels) => {
                if p == 0 {
                    Some(Node::name(name))
                } else {
                    levels.get(p - 1).copied().map(Node::level)
                }
            }
            ExprKind::MData(_, wrapped) => (p == 0).then_some(Node::expr(wrapped)),
        },
        _ => return Err(ResourceError::Invariant),
    })
}
#[derive(Clone, Copy)]
enum Key<'a> {
    Name(NameId, bool, &'a [u8]),
    Level(LevelKind),
    Expr(ExprKind<'a>),
}
fn copy_bytes<'a>(
    bytes: &[u8],
    scratch: &'a mut Vec<u8>,
    b: &mut Budget,
) -> Result<&'a [u8], ResourceError> {
    b.charge_work(bytes.len() as u64 + 1)?;
    scratch.clear();
    b.grow_vec(scratch, bytes.len())?;
    scratch.extend_from_slice(bytes);
    Ok(scratch)
}
fn key<'a>(
    s: &Stores<'_>,
    maps: &[Index; 3],
    n: Node,
    bytes: &'a mut Vec<u8>,
    us: &'a mut Vec<LevelId>,
    b: &mut Budget,
) -> Result<Key<'a>, ResourceError> {
    let name = |id, b: &mut Budget| mapped(maps, Node::name(id), b).map(NameId);
    let level = |id, b: &mut Budget| s.levels.resolve_slot(mapped(maps, Node::level(id), b)?, b);
    let expr = |id, b: &mut Budget| {
        s.expressions
            .resolve_slot(mapped(maps, Node::expr(id), b)?, b)
    };
    Ok(match n.arena {
        0 => {
            let (prefix, component) = s
                .names
                .view(NameId(n.id), b)?
                .ok_or(ResourceError::Invariant)?;
            let number = matches!(component, Component::Number(_));
            let original = match component {
                Component::Number(v) => v,
                Component::String(v) => v.as_bytes(),
            };
            Key::Name(name(prefix, b)?, number, copy_bytes(original, bytes, b)?)
        }
        1 => Key::Level(
            match s.levels.get(s.levels.resolve_slot(n.id, b)?, b)?.kind() {
                LevelKind::Zero => return Err(ResourceError::Invariant),
                LevelKind::Param(n) => LevelKind::Param(name(n, b)?),
                LevelKind::Succ(a) => LevelKind::Succ(level(a, b)?),
                LevelKind::Max(a, c) => LevelKind::Max(level(a, b)?, level(c, b)?),
                LevelKind::IMax(a, c) => LevelKind::IMax(level(a, b)?, level(c, b)?),
            },
        ),
        2 => Key::Expr(
            match s
                .expressions
                .get(s.expressions.resolve_slot(n.id, b)?, b)?
                .kind(s.expressions, s.levels, b)?
            {
                ExprKind::Bound(v) => ExprKind::Bound(v),
                ExprKind::Free(v) => ExprKind::Free(v),
                ExprKind::Sort(v) => ExprKind::Sort(level(v, b)?),
                ExprKind::App(a, c) => ExprKind::App(expr(a, b)?, expr(c, b)?),
                ExprKind::Lambda(n, a, c, i) => {
                    ExprKind::Lambda(name(n, b)?, expr(a, b)?, expr(c, b)?, i)
                }
                ExprKind::Pi(n, a, c, i) => ExprKind::Pi(name(n, b)?, expr(a, b)?, expr(c, b)?, i),
                ExprKind::Let(n, a, c, d, i) => {
                    ExprKind::Let(name(n, b)?, expr(a, b)?, expr(c, b)?, expr(d, b)?, i)
                }
                ExprKind::Projection(n, i, a) => ExprKind::Projection(name(n, b)?, i, expr(a, b)?),
                ExprKind::Natural(v) => ExprKind::Natural(copy_bytes(v, bytes, b)?),
                ExprKind::String(v) => ExprKind::String(copy_bytes(v, bytes, b)?),
                ExprKind::MData(v, wrapped) => {
                    ExprKind::MData(copy_bytes(v, bytes, b)?, expr(wrapped, b)?)
                }
                ExprKind::Constant(n, levels) => {
                    us.clear();
                    b.charge_work(levels.len() as u64 + 1)?;
                    b.grow_vec(us, levels.len())?;
                    for &l in levels {
                        us.push(level(l, b)?);
                    }
                    ExprKind::Constant(name(n, b)?, us)
                }
            },
        ),
        _ => return Err(ResourceError::Invariant),
    })
}
fn hash(key: &Key<'_>, b: &mut Budget) -> Result<u32, ResourceError> {
    let mut h = crate::syntax::hash::FastHasher::new();
    match key {
        Key::Name(prefix, number, bytes) => {
            b.charge_work(bytes.len() as u64 + 1)?;
            h.write_u32(prefix.0);
            h.write_u8(u8::from(*number));
            h.write(bytes);
        }
        Key::Level(k) => match k {
            LevelKind::Zero => h.write_u8(0),
            LevelKind::Param(n) => {
                h.write_u8(1);
                h.write_u32(n.0)
            }
            LevelKind::Succ(a) => {
                h.write_u8(2);
                h.write_u32(a.slot())
            }
            LevelKind::Max(a, c) | LevelKind::IMax(a, c) => {
                h.write_u8(if matches!(k, LevelKind::Max(..)) {
                    3
                } else {
                    4
                });
                h.write_u32(a.slot());
                h.write_u32(c.slot())
            }
        },
        Key::Expr(k) => match k {
            ExprKind::Bound(v) | ExprKind::Free(v) => {
                h.write_u8(if matches!(k, ExprKind::Bound(_)) {
                    0
                } else {
                    1
                });
                h.write_u32(*v)
            }
            ExprKind::Sort(v) => {
                h.write_u8(2);
                h.write_u32(v.slot())
            }
            ExprKind::App(a, c) => {
                h.write_u8(3);
                h.write_u32(a.slot());
                h.write_u32(c.slot())
            }
            ExprKind::Lambda(n, a, c, i) | ExprKind::Pi(n, a, c, i) => {
                h.write_u8(if matches!(k, ExprKind::Lambda(..)) {
                    4
                } else {
                    5
                });
                h.write_u32(n.0);
                h.write_u32(a.slot());
                h.write_u32(c.slot());
                h.write_u8(*i as u8)
            }
            ExprKind::Let(n, a, c, d, i) => {
                h.write_u8(6);
                h.write_u32(n.0);
                h.write_u32(a.slot());
                h.write_u32(c.slot());
                h.write_u32(d.slot());
                h.write_u8(u8::from(*i))
            }
            ExprKind::Projection(n, i, a) => {
                h.write_u8(7);
                h.write_u32(n.0);
                h.write_u32(*i);
                h.write_u32(a.slot())
            }
            ExprKind::Constant(n, us) => {
                b.charge_work(us.len() as u64 + 1)?;
                h.write_u8(8);
                h.write_u32(n.0);
                for l in *us {
                    h.write_u32(l.slot())
                }
            }
            ExprKind::Natural(v) | ExprKind::String(v) => {
                b.charge_work(v.len() as u64 + 1)?;
                h.write_u8(if matches!(k, ExprKind::Natural(_)) {
                    9
                } else {
                    10
                });
                h.write(v)
            }
            ExprKind::MData(v, w) => {
                b.charge_work(v.len() as u64 + 1)?;
                h.write_u8(11);
                h.write(v);
                h.write_u32(w.slot())
            }
        },
    }
    Ok(h.finish() as u32)
}
fn matches(s: &Stores<'_>, key: &Key<'_>, id: u32, b: &mut Budget) -> Result<bool, ResourceError> {
    Ok(match key {
        Key::Name(prefix, number, bytes) => {
            let (p, c) = s
                .names
                .view(NameId(id), b)?
                .ok_or(ResourceError::Invariant)?;
            b.charge_work(bytes.len() as u64 + 1)?;
            p == *prefix
                && match c {
                    Component::Number(v) => *number && v == *bytes,
                    Component::String(v) => !*number && v.as_bytes() == *bytes,
                }
        }
        Key::Level(kind) => s.levels.get(s.levels.resolve_slot(id, b)?, b)?.kind() == *kind,
        Key::Expr(kind) => {
            match kind {
                ExprKind::Constant(_, v) => b.charge_work(v.len() as u64 + 1)?,
                ExprKind::Natural(v) | ExprKind::String(v) => b.charge_work(v.len() as u64 + 1)?,
                ExprKind::MData(v, _) => b.charge_work(v.len() as u64 + 1)?,
                _ => (),
            };
            s.expressions
                .get(s.expressions.resolve_slot(id, b)?, b)?
                .kind(s.expressions, s.levels, b)?
                == *kind
        }
    })
}
fn append(s: &mut Stores<'_>, key: &Key<'_>, b: &mut Budget) -> Result<u32, Error> {
    Ok(match key {
        Key::Name(prefix, number, bytes) => {
            s.names
                .append(
                    *prefix,
                    if *number {
                        Component::Number(bytes)
                    } else {
                        Component::String(
                            std::str::from_utf8(bytes).map_err(|_| ResourceError::Invariant)?,
                        )
                    },
                    b,
                )?
                .0
        }
        Key::Level(kind) => s.levels.append(*kind, s.names, b)?.slot(),
        Key::Expr(kind) => s.expressions.append(*kind, s.levels, s.names, b)?.slot(),
    })
}
