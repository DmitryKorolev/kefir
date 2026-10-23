//! Completed closed beta prefixes of validated recursor rules.
//! Entries certify raw partial application only, never a head or typing result.
use super::{allocate, release};
use crate::resource::{Budget, Event, ReductionPath, ResourceError, SessionCacheBudget};
use crate::syntax::expressions::{
    ExprId, ExprKind, ExpressionError, Expressions, binding::Binding,
};
use crate::syntax::levels::Levels;
use crate::syntax::names::Names;
use std::mem::size_of;

pub(crate) const LIMIT: usize = 8;
const SLOTS: usize = 64;
#[derive(Clone, Copy, Default)]
struct Entry {
    source: u32,
    result: u32,
    arguments: [u32; LIMIT],
    len: u8,
    state: u8, // 0 empty; 1 closed key seen; 2 completed beta prefix.
}
const _: () = assert!(size_of::<Entry>() == 44);
#[derive(Default)]
pub(super) struct Cache {
    entries: Vec<Entry>,
}
const _: () = assert!(size_of::<Cache>() == 24);
impl Cache {
    /// Caller has revalidated the rule and supplies the full fixed prefix in
    /// nearest-binder-first order. Fields and outer arguments are NOT consumed.
    /// The driver owns one immutable arena/frontier until retirement. Only closed
    /// keys enter the table, so an exact hit cannot capture a retired free local.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn reduce(
        &mut self,
        source: ExprId,
        arguments: &[ExprId],
        incoming: ReductionPath,
        expressions: &mut Expressions,
        levels: &Levels,
        names: &Names,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<Option<(ExprId, ReductionPath)>, ExpressionError> {
        if arguments.is_empty() || arguments.len() > LIMIT {
            return Ok(None);
        }
        b.charge_work(arguments.len() as u64 + 2)?;
        let mut key = Entry {
            source: source.slot(),
            len: arguments.len() as u8,
            state: 1,
            ..Entry::default()
        };
        let mut hash = source.slot().wrapping_mul(0x9e37_79b1);
        for (slot, argument) in key.arguments.iter_mut().zip(arguments) {
            *slot = argument.slot();
            hash = hash.rotate_left(7) ^ argument.slot().wrapping_mul(0x85eb_ca6b);
        }
        let index = hash as usize & (SLOTS - 1);
        let previous = self.entries.get(index).copied().unwrap_or_default();
        let same = previous.state != 0
            && previous.source == key.source
            && previous.len == key.len
            && previous.arguments[..arguments.len()] == key.arguments[..arguments.len()];
        if same && previous.state == 2 {
            // The certificate's height is the exact number of consumed binders;
            // reuse cannot evade a near-cap demanded route.
            let path = incoming.after_height(arguments.len() as u32)?;
            return Ok(Some((expressions.resolve_slot(previous.result, b)?, path)));
        }
        if !same {
            let node = expressions.get(source, b)?;
            if node.loose_range() != 0 || node.has_free() {
                return Ok(None);
            }
            for &argument in arguments {
                let node = expressions.get(argument, b)?;
                if node.loose_range() != 0 || node.has_free() {
                    return Ok(None);
                }
            }
            if self.entries.is_empty() {
                let bytes = (SLOTS * size_of::<Entry>()) as u64;
                // Probe optional admission, then undo the probe: allocate below
                // owns the actual session reservation and storage charge.
                if !b.has_storage_headroom(bytes) || !session.reserve(bytes)? {
                    return Ok(None);
                }
                session.release(bytes)?;
                let mut entries = allocate(SLOTS, session, b)?;
                if let Err(error) = b.charge_work(SLOTS as u64 + 1) {
                    release(entries, session, b)?;
                    return Err(error.into());
                }
                entries.resize(SLOTS, Entry::default());
                self.entries = entries;
            }
            self.entries[index] = key;
            return Ok(None);
        }
        // A repeated closed key warrants constructing this partial application.
        // By validated RHS construction these are literal leading lambdas, not
        // inferred function types or arbitrary reducible function expressions.
        let mut body = source;
        let mut path = incoming;
        for _ in arguments {
            let ExprKind::Lambda(_, _, next, _) =
                expressions.get(body, b)?.kind(expressions, levels, b)?
            else {
                return Err(ResourceError::Invariant.into());
            };
            path = path.after_reduction()?;
            body = next;
        }
        let result =
            expressions.bind(body, 0, Binding::Instantiate(arguments), levels, names, b)?;
        // bind returned only after complete readback and scratch retirement.
        // The result remains closed by capture-free substitution of closed
        // arguments into the complete leading prefix of a closed source.
        key.result = result.slot();
        key.state = 2;
        self.entries[index] = key;
        b.observe(Event::Reductions, arguments.len() as u64);
        Ok(Some((result, path)))
    }
    pub(super) fn retire(
        self,
        session: &mut SessionCacheBudget,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        release(self.entries, session, b)
    }
}
