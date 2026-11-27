//! Installed open applications in one monotone State. No graph-local value or
//! environment ID escapes the attempt. Only the active cursor contains such an ID.
use super::{Budget, NameId, PENDING, ResourceError, SLOTS};
use crate::resource::charged::{bytes, charged};

const DEPTH: usize = 16;
const PARAMS: usize = 8;
type Frame = [u32; 2];

#[derive(Default, Clone, Copy)]
pub(in super::super) struct Cursor {
    pub(in super::super) env: u32,
    pub(in super::super) depth: u8,
    pub(in super::super) locals: u8,
}

const _: () = assert!(size_of::<Cursor>() == 8);

pub(in super::super) struct Lexical {
    pub(in super::super) cursor: Cursor,
    frames: [Frame; DEPTH],
}

impl Default for Lexical {
    fn default() -> Self {
        Self {
            cursor: Cursor {
                depth: DEPTH as u8 + 1,
                ..Cursor::default()
            },
            frames: [[0; 2]; DEPTH],
        }
    }
}
impl Lexical {
    pub(in super::super) fn enable(&mut self) {
        self.cursor = Cursor::default();
    }

    pub(in super::super) fn enter(&mut self, env: u32, locals: usize, frame: Frame) {
        self.frames[usize::from(self.cursor.depth)] = frame;
        self.cursor = Cursor {
            env,
            depth: self.cursor.depth + 1,
            // An eligible chain starts with zero locals and adds at most one per frame.
            locals: locals as u8,
        };
    }

    pub(in super::super) fn can_extend(&self, parent: u32, locals: usize, variable: bool) -> bool {
        let c = self.cursor;
        usize::from(c.depth) < DEPTH
            && c.env == parent
            && usize::from(c.locals) + usize::from(variable) == locals
    }

    pub(in super::super) fn active(&self, env: u32, locals: usize) -> Option<&[Frame]> {
        let c = self.cursor;
        (env != 0
            && usize::from(c.depth) <= DEPTH
            && c.env == env
            && usize::from(c.locals) == locals)
            .then(|| &self.frames[..usize::from(c.depth)])
    }

    pub(in super::super) fn disable(&mut self) {
        self.cursor.depth = DEPTH as u8 + 1;
    }
}

#[derive(Default, Clone, Copy, Eq, PartialEq)]
struct Row {
    expr: u32,
    depth: u32,
    arity: u32,
    params: [u32; PARAMS],
    frames: [Frame; DEPTH],
}
charged! { Row => 172 }

#[derive(Default)]
pub(in super::super) struct Open {
    rows: Vec<Row>,
    pending: Vec<Row>,
}
fn slot(expr: u32) -> usize {
    let x = expr.wrapping_mul(0x85ebca6b);
    ((x ^ (x >> 16)) as usize) & (SLOTS - 1)
}
impl Open {
    pub(in super::super) fn might_match(&self, expr: u32) -> bool {
        self.rows
            .get(slot(expr))
            .is_some_and(|row| row.expr == expr && row.depth != 0)
    }

    pub(in super::super) fn contains(
        &self,
        expr: u32,
        frames: &[Frame],
        params: &[NameId],
        b: &mut Budget,
    ) -> Result<bool, ResourceError> {
        if !(1..=DEPTH).contains(&frames.len()) || params.len() > PARAMS {
            return Ok(false);
        }
        let Some(row) = self.rows.get(slot(expr)) else {
            return Ok(false);
        };
        if row.expr != expr
            || row.depth as usize != frames.len()
            || row.arity as usize != params.len()
        {
            return Ok(false);
        }
        b.charge_work(3 + 2 * frames.len() as u64 + params.len() as u64)?;
        Ok(row.frames[..frames.len()] == *frames
            && row.params.iter().zip(params).all(|(a, b)| *a == b.0))
    }

    pub(in super::super) fn stage(
        &mut self,
        expr: u32,
        frames: &[Frame],
        params: &[NameId],
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        if !(1..=DEPTH).contains(&frames.len())
            || self.pending.len() == PENDING
            || params.len() > PARAMS
        {
            return Ok(());
        }
        // A duplicate source can suppress admission in a different context.
        // This positive-only heuristic never authorizes a lookup.
        b.charge_work(1 + self.pending.len() as u64)?;
        if self.pending.iter().any(|r| r.expr == expr) {
            return Ok(());
        }
        // Prepay key construction and the installation copy in u32 words.
        const WORDS: u64 = (bytes::<Row>() / 4) as u64;
        b.charge_work(2 * WORDS)?;
        let mut row = Row {
            expr,
            depth: frames.len() as u32,
            arity: params.len() as u32,
            ..Row::default()
        };
        row.frames[..frames.len()].copy_from_slice(frames);
        for (a, b) in row.params.iter_mut().zip(params) {
            *a = b.0;
        }
        if self.rows.is_empty() {
            b.grow_vec(&mut self.rows, SLOTS)?;
            b.charge_work(SLOTS as u64 * WORDS)?;
            self.rows.resize(SLOTS, Row::default());
        }
        if self.pending.capacity() == 0 {
            b.grow_vec(&mut self.pending, PENDING)?;
        }
        self.pending.push(row);
        Ok(())
    }
    pub(super) fn clear(&mut self) {
        self.pending.clear();
    }
    pub(super) fn publish(&mut self) {
        for row in self.pending.drain(..) {
            self.rows[slot(row.expr)] = row;
        }
    }
    pub(super) fn held(&self) -> usize {
        (self.rows.capacity() + self.pending.capacity()) * bytes::<Row>()
    }
}
