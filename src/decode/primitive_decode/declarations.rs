//! Temporary ordinary-declaration requests. Availability of
//! referenced syntax is not scope validity, checkedness or installation.
use super::*;

pub(crate) mod policy;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Kind {
    Axiom,
    Definition,
    Theorem,
    Opaque,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Safety {
    Safe,
    Unsafe,
    Partial,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Hint<'a> {
    Opaque,
    Abbrev,
    Regular(&'a [u8]),
}
/// Valid only with the originating decoder stores. Borrowing scratch prevents
/// reuse while this request is live; semantic validation must copy installed
/// fields before releasing it. No constructor here grants checkedness.
pub(crate) struct Request<'a> {
    pub kind: Kind,
    pub name: NameId,
    pub parameters: &'a [NameId],
    pub ty: ExprId,
    pub value: Option<ExprId>,
    pub all: &'a [NameId],
    pub safety: Safety,
    pub hint: Option<Hint<'a>>,
}
#[derive(Default)]
pub(super) struct Payload {
    pub(super) parameters: Vec<NameId>,
    pub(super) all: Vec<NameId>,
    pub(super) hint: Vec<u8>,
}
impl Payload {
    pub(super) fn clear(&mut self) {
        self.parameters.clear();
        self.all.clear();
        self.hint.clear();
    }
    pub(super) fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let bytes = (self.parameters.capacity() + self.all.capacity()) * size_of::<NameId>()
            + self.hint.capacity();
        drop(self);
        b.release(bytes as u64)
    }
    pub(super) fn request(&self, fields: Fields) -> Request<'_> {
        Request {
            kind: fields.kind,
            name: fields.name,
            parameters: &self.parameters,
            ty: fields.ty,
            value: fields.value,
            all: &self.all,
            safety: fields.safety,
            hint: fields.hint.map(|kind| match kind {
                0 => Hint::Opaque,
                1 => Hint::Abbrev,
                _ => Hint::Regular(&self.hint),
            }),
        }
    }
}
pub(super) struct Fields {
    pub(super) kind: Kind,
    pub(super) name: NameId,
    pub(super) ty: ExprId,
    pub(super) value: Option<ExprId>,
    pub(super) safety: Safety,
    pub(super) hint: Option<u8>,
}
