//! One fixed-manifest query over immutable original stores. Completed expression
//! pairs only; raw binders are never opened, so depth is not part of the key.
use super::*;
use crate::syntax::{expressions::ExprKind, levels::LevelKind, names::Component};
use std::hash::{Hash, Hasher};

#[derive(Clone, Copy, Default, Eq, PartialEq)]
struct Pair {
    expected: u32,
    actual: u32,
}
#[derive(Clone, Copy)]
struct Frame {
    pair: Pair,
    mode: u32,
}
#[derive(Default)]
struct Scan {
    pairs: Vec<Pair>,
    frames: Vec<Frame>,
}
const _: () = assert!(size_of::<Pair>() == 8 && size_of::<Frame>() == 12);
const _: () = assert!(size_of::<Scan>() == 48);

pub(super) fn name(
    expected: u32,
    mut actual: NameId,
    n: &Names,
    b: &mut Budget,
) -> Result<bool, ResourceError> {
    let mut code = expected;
    while code != 0 {
        let item = manifest::NAMES
            .get(code as usize - 1)
            .ok_or(ResourceError::Invariant)?;
        let Some((parent, Component::String(component))) = n.view(actual, b)? else {
            return Ok(false);
        };
        if component != item.component {
            return Ok(false);
        }
        actual = parent;
        code = item.parent;
    }
    Ok(actual == NameId::ANONYMOUS)
}
impl Scan {
    fn position(entries: &[Pair], pair: Pair, b: &mut Budget) -> Result<usize, ResourceError> {
        let count = entries
            .len()
            .checked_sub(1)
            .ok_or(ResourceError::Invariant)?;
        if count == 0 || !count.is_power_of_two() {
            return Err(ResourceError::Invariant);
        }
        let mut hash = crate::syntax::hash::FastHasher::new();
        (pair.expected, pair.actual).hash(&mut hash);
        let mut at = hash.finish() as usize & (count - 1);
        for _ in 0..count {
            b.charge_work(1)?;
            let value = entries[at + 1];
            if value.expected == 0 || value == pair {
                return Ok(at + 1);
            }
            at = (at + 1) & (count - 1);
        }
        Err(ResourceError::Invariant)
    }
    fn contains(&self, pair: Pair, b: &mut Budget) -> Result<bool, ResourceError> {
        if self.pairs.is_empty() {
            return Ok(false);
        }
        Ok(self.pairs[Self::position(&self.pairs, pair, b)?].expected != 0)
    }
    fn insert(&mut self, pair: Pair, b: &mut Budget) -> Result<(), ResourceError> {
        if self.contains(pair, b)? {
            return Ok(());
        }
        // Bucket zero is an occupancy header, never an expression pair. Expected
        // descriptors are one-based; all probes remain in slots 1..len.
        if self.pairs.is_empty() || self.pairs[0].actual as usize + 1 > (self.pairs.len() - 1) / 2 {
            let count = self
                .pairs
                .len()
                .saturating_sub(1)
                .checked_mul(2)
                .ok_or(ResourceError::Counter)?
                .max(16);
            let mut next = Vec::new();
            let result = (|| {
                b.grow_vec(&mut next, count + 1)?;
                b.charge_work((count + 1) as u64)?;
                next.resize(count + 1, Pair::default());
                for value in self
                    .pairs
                    .iter()
                    .skip(1)
                    .copied()
                    .filter(|x| x.expected != 0)
                {
                    let at = Self::position(&next, value, b)?;
                    next[at] = value;
                    next[0].actual += 1;
                }
                Ok(())
            })();
            if let Err(error) = result {
                let bytes = next.capacity() * size_of::<Pair>();
                drop(next);
                b.release(bytes as u64)?;
                return Err(error);
            }
            let old = std::mem::replace(&mut self.pairs, next);
            let bytes = old.capacity() * size_of::<Pair>();
            drop(old);
            b.release(bytes as u64)?;
        }
        let at = Self::position(&self.pairs, pair, b)?;
        self.pairs[at] = pair;
        self.pairs[0].actual += 1;
        Ok(())
    }
    fn push(
        &mut self,
        expected: u32,
        actual: u32,
        mode: u32,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        b.charge_work(1)?;
        let required = self.frames.len() + 1;
        b.grow_vec(&mut self.frames, required)?;
        b.reserve_frames(1)?;
        self.frames.push(Frame {
            pair: Pair { expected, actual },
            mode,
        });
        Ok(())
    }
    fn run(
        &mut self,
        expected: u32,
        actual: ExprId,
        e: &Expressions,
        l: &Levels,
        n: &Names,
        b: &mut Budget,
    ) -> Result<bool, ResourceError> {
        self.push(expected, actual.slot(), 0, b)?;
        while let Some(Frame { pair, mode }) = self.frames.pop() {
            b.release_frames(1)?;
            b.charge_work(1)?;
            if mode == 1 {
                self.insert(pair, b)?;
                continue;
            }
            if mode == 2 {
                let Level([tag, a, c]) = *manifest::LEVELS
                    .get(pair.expected as usize - 1)
                    .ok_or(ResourceError::Invariant)?;
                let id = l.resolve_slot(pair.actual, b)?;
                match (tag, l.get(id, b)?.kind()) {
                    (0, LevelKind::Zero) => {}
                    (1, LevelKind::Succ(x)) => self.push(a, x.slot(), 2, b)?,
                    (2, LevelKind::Param(x)) if name(a, x, n, b)? => {}
                    (3, LevelKind::Max(x, y)) => {
                        self.push(c, y.slot(), 2, b)?;
                        self.push(a, x.slot(), 2, b)?;
                    }
                    _ => return Ok(false),
                }
                continue;
            }
            if self.contains(pair, b)? {
                continue;
            }
            let Expression([tag, a, c, d]) = *manifest::EXPRESSIONS
                .get(pair.expected as usize - 1)
                .ok_or(ResourceError::Invariant)?;
            let actual = ExprId::from_stored_original(pair.actual);
            let kind = e.get(actual, b)?.kind(e, l, b)?;
            // Completion is below every child (including exact universe checks).
            self.push(pair.expected, pair.actual, 1, b)?;
            match (tag, kind) {
                (0, ExprKind::Bound(x)) if a == x => {}
                (7, ExprKind::Natural(bytes))
                    if (a == 0 && bytes == b"0") || (a == 1 && bytes == b"1") => {}
                (1, ExprKind::Sort(x)) => self.push(a, x.slot(), 2, b)?,
                (2, ExprKind::App(x, y))
                | (3, ExprKind::Pi(_, x, y, _))
                | (4, ExprKind::Lambda(_, x, y, _)) => {
                    self.push(c, y.slot(), 0, b)?;
                    self.push(a, x.slot(), 0, b)?;
                }
                // Constant universe arguments pack as [u0, u1, u2] across the
                // low two bytes of c and word 3; with three arguments the low
                // byte triple is exhausted, so the third reference lives in d
                // (the retained encoder emits it there; the count rides in
                // c's third byte).
                (5, ExprKind::Constant(x, us))
                    if name(a, x, n, b)? && us.len() == (c >> 16) as usize =>
                {
                    for (i, u) in us.iter().enumerate() {
                        let expected = if i < 2 { (c >> (8 * i)) & 255 } else { d };
                        self.push(expected, u.slot(), 2, b)?;
                    }
                }
                (6, ExprKind::Projection(x, i, source)) if name(a, x, n, b)? && c == i => {
                    self.push(d, source.slot(), 0, b)?
                }
                // Adopted narrow letE matcher. The let main row is
                // [8, payload_ref, 0, 0]; reserved words must be zero and the
                // payload must be in range — violations are generated-data
                // corruption, a terminal invariant, not a mismatch. The
                // binder compares exactly by name and the nondep flag must
                // equal the runtime flag; both are ordinary mismatches.
                // Children compare raw under the already-encoded binder: no
                // matcher-side index shifting, opening, or substitution.
                (8, ExprKind::Let(x, ty, val, body, nondep)) => {
                    if c != 0 || d != 0 {
                        return Err(ResourceError::Invariant);
                    }
                    let LetPayload([name_ref, type_ref, value_ref, body_ref, flags]) =
                        *manifest::LET_PAYLOADS
                            .get(
                                (a as usize)
                                    .checked_sub(1)
                                    .ok_or(ResourceError::Invariant)?,
                            )
                            .ok_or(ResourceError::Invariant)?;
                    if flags > 1 {
                        return Err(ResourceError::Invariant);
                    }
                    if (flags != 0) != nondep || !name(name_ref, x, n, b)? {
                        return Ok(false);
                    }
                    self.push(body_ref, body.slot(), 0, b)?;
                    self.push(value_ref, val.slot(), 0, b)?;
                    self.push(type_ref, ty.slot(), 0, b)?;
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
    fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let frames = self.frames.len();
        let bytes =
            self.frames.capacity() * size_of::<Frame>() + self.pairs.capacity() * size_of::<Pair>();
        drop(self);
        let storage = b.release(bytes as u64);
        let frames = b.release_frames(frames);
        storage.and(frames)
    }
}
pub(super) fn expression(
    expected: u32,
    actual: ExprId,
    e: &Expressions,
    l: &Levels,
    n: &Names,
    b: &mut Budget,
) -> Result<bool, ResourceError> {
    let mut scan = Scan::default();
    let result = scan.run(expected, actual, e, l, n, b);
    scan.retire(b)?;
    result
}
