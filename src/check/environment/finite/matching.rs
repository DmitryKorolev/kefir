//! One fixed-manifest query over immutable original stores. Completed expression
//! pairs only; raw binders are never opened, so depth is not part of the key.
use super::manifest;
use crate::resource::{Budget, ResourceError};
use crate::syntax::expressions::{ExprId, Expressions};
use crate::syntax::levels::{Levels, NameId};
use crate::syntax::names::Names;
use crate::syntax::{expressions::ExprKind, levels::LevelKind, names::Component};
use std::hash::{Hash, Hasher};
use std::mem::size_of;

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

fn row<const N: usize>(rows: &[[u32; N]], id: u32) -> Result<[u32; N], ResourceError> {
    let index = id.checked_sub(1).ok_or(ResourceError::Invariant)? as usize;
    rows.get(index).copied().ok_or(ResourceError::Invariant)
}

fn bytes(start: u32, len: u32) -> Result<&'static [u8], ResourceError> {
    let end = (start as usize)
        .checked_add(len as usize)
        .ok_or(ResourceError::Counter)?;
    manifest::UTF8_BYTES
        .get(start as usize..end)
        .ok_or(ResourceError::Invariant)
}

pub(super) fn sequence(id: u32) -> Result<&'static [u32], ResourceError> {
    let [start, len] = row(&manifest::SEQUENCES, id)?;
    let end = (start as usize)
        .checked_add(len as usize)
        .ok_or(ResourceError::Counter)?;
    manifest::SEQUENCE_WORDS
        .get(start as usize..end)
        .ok_or(ResourceError::Invariant)
}

pub(super) fn name(
    mut expected: u32,
    mut actual: NameId,
    n: &Names,
    b: &mut Budget,
) -> Result<bool, ResourceError> {
    while expected != 0 {
        let [parent, tag, a, c] = row(&manifest::NAMES, expected)?;
        b.charge_work(1)?;
        let Some((actual_parent, component)) = n.view(actual, b)? else {
            return Ok(false);
        };
        let matched = match (tag, component) {
            (0, Component::String(value)) => {
                let expected = bytes(a, c)?;
                b.charge_work(expected.len() as u64 + 1)?;
                value.as_bytes() == expected
            }
            (1, Component::Number(value)) => {
                // Names validates canonical decimal payloads. Overflow is a
                // completed mismatch with this finite u64 descriptor, not error.
                b.charge_work(value.len() as u64 + 1)?;
                let number = std::str::from_utf8(value)
                    .ok()
                    .and_then(|s| s.parse::<u64>().ok());
                number == Some(u64::from(a) | (u64::from(c) << 32))
            }
            (0 | 1, _) => false,
            _ => return Err(ResourceError::Invariant),
        };
        if !matched {
            return Ok(false);
        }
        actual = actual_parent;
        expected = parent;
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
        let mut hash = std::collections::hash_map::DefaultHasher::new();
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
    fn level_children(
        &mut self,
        [tag, a, c]: [u32; 3],
        actual: LevelKind,
        names: &Names,
        budget: &mut Budget,
    ) -> Result<bool, ResourceError> {
        match (tag, actual) {
            (0, LevelKind::Zero) => {}
            (1, LevelKind::Succ(x)) => self.push(a, x.slot(), 2, budget)?,
            (2, LevelKind::Param(x)) if name(a, x, names, budget)? => {}
            (3, LevelKind::Max(x, y)) | (4, LevelKind::IMax(x, y)) => {
                self.push(c, y.slot(), 2, budget)?;
                self.push(a, x.slot(), 2, budget)?;
            }
            _ => return Ok(false),
        }
        Ok(true)
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
                let [tag, a, c] = row(&manifest::LEVELS, pair.expected)?;
                let id = l.resolve_slot(pair.actual, b)?;
                if !self.level_children([tag, a, c], l.get(id, b)?.kind(), n, b)? {
                    return Ok(false);
                }
                continue;
            }
            if self.contains(pair, b)? {
                continue;
            }
            let [tag, a, c, d] = row(&manifest::EXPRESSIONS, pair.expected)?;
            let actual = e.resolve_slot(pair.actual, b)?;
            let kind = e.get(actual, b)?.kind(e, l, b)?;
            // Completion is below every child (including exact universe checks).
            self.push(pair.expected, pair.actual, 1, b)?;
            match (tag, kind) {
                (0, ExprKind::Bound(x)) if a == x => {}
                (7, ExprKind::Natural(value)) | (9, ExprKind::String(value)) => {
                    let expected = bytes(a, c)?;
                    b.charge_work(expected.len() as u64 + 1)?;
                    if value != expected {
                        return Ok(false);
                    }
                }
                (1, ExprKind::Sort(x)) => self.push(a, x.slot(), 2, b)?,
                (2, ExprKind::App(x, y))
                | (3, ExprKind::Pi(_, x, y, _))
                | (4, ExprKind::Lambda(_, x, y, _)) => {
                    self.push(c, y.slot(), 0, b)?;
                    self.push(a, x.slot(), 0, b)?;
                }
                (5, ExprKind::Constant(x, us)) => {
                    let expected = sequence(c)?;
                    if !name(a, x, n, b)? || us.len() != expected.len() {
                        return Ok(false);
                    }
                    for (&expected, actual) in expected.iter().zip(us).rev() {
                        self.push(expected, actual.slot(), 2, b)?;
                    }
                }
                (8, ExprKind::Let(actual_name, ty, value, body, nondep)) => {
                    if c != 0 || d != 0 {
                        return Err(ResourceError::Invariant);
                    }
                    let [name_id, type_id, value_id, body_id, flags] =
                        row(&manifest::LET_PAYLOADS, a)?;
                    if flags > 1 || name_id as usize > manifest::NAMES.len() {
                        return Err(ResourceError::Invariant);
                    }
                    if nondep != (flags == 1) || !name(name_id, actual_name, n, b)? {
                        return Ok(false);
                    }
                    self.push(body_id, body.slot(), 0, b)?;
                    self.push(value_id, value.slot(), 0, b)?;
                    self.push(type_id, ty.slot(), 0, b)?;
                }
                (6, ExprKind::Projection(x, i, source)) if name(a, x, n, b)? && c == i => {
                    self.push(d, source.slot(), 0, b)?
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
