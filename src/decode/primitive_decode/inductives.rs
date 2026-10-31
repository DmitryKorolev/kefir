//! Transient grouped transport. Schema/reference validity is not checkedness.
//! Lists preserve input order and multiplicity; spans belong to this payload only.
use super::*;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Span {
    pub start: u32,
    pub len: u32,
}
#[derive(Clone, Copy, Debug)]
pub(crate) struct Inductive {
    pub name: NameId,
    pub parameters: Span,
    pub ty: ExprId,
    pub num_params: u32,
    pub num_indices: u32,
    pub all: Span,
    pub constructors: Span,
    pub num_nested: u32,
    pub is_recursive: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}
#[derive(Clone, Copy, Debug)]
pub(crate) struct Constructor {
    pub name: NameId,
    pub parameters: Span,
    pub ty: ExprId,
    pub inductive: NameId,
    pub index: u32,
    pub num_params: u32,
    pub num_fields: u32,
    pub is_unsafe: bool,
}
#[derive(Clone, Copy, Debug)]
pub(crate) struct Recursor {
    pub name: NameId,
    pub parameters: Span,
    pub ty: ExprId,
    pub all: Span,
    pub num_params: u32,
    pub num_indices: u32,
    pub num_motives: u32,
    pub num_minors: u32,
    pub rules: Span,
    pub k: bool,
    pub is_unsafe: bool,
}
#[derive(Clone, Copy, Debug)]
pub(crate) struct Rule {
    pub constructor: NameId,
    pub num_fields: u32,
    pub rhs: ExprId,
}
/// Borrows scratch until the consumer has copied anything it will install.
/// No request survives clear/retire; no semantic admission follows from finish.
pub(crate) struct Request<'a> {
    pub types: &'a [Inductive],
    pub constructors: &'a [Constructor],
    pub recursors: &'a [Recursor],
    pub rules: &'a [Rule],
    pub names: &'a [NameId],
}
#[derive(Default)]
pub(super) struct Payload {
    pub(super) types: Vec<Inductive>,
    pub(super) constructors: Vec<Constructor>,
    pub(super) recursors: Vec<Recursor>,
    pub(super) rules: Vec<Rule>,
    pub(super) names: Vec<NameId>,
}
// Numeric payloads are exact u32. On supported targets descriptors have no
// per-member allocation: 48/36/52/12 bytes, name entries 4 bytes, pending numeric
// token fixups at most 32 bytes each until validation. Capacity, including growth
// overlap, is charged by grow_vec; fixed capture holds at most two builders.
#[cfg(target_pointer_width = "64")]
const _: () = assert!(size_of::<Inductive>() == 48);
#[cfg(target_pointer_width = "64")]
const _: () = assert!(size_of::<Constructor>() == 36);
#[cfg(target_pointer_width = "64")]
const _: () = assert!(size_of::<Recursor>() == 52);
#[cfg(target_pointer_width = "64")]
const _: () = assert!(size_of::<Rule>() == 12);
#[cfg(target_pointer_width = "64")]
const _: () = assert!(size_of::<NameId>() == 4);
impl Payload {
    pub(super) fn request(&self) -> Request<'_> {
        Request {
            types: &self.types,
            constructors: &self.constructors,
            recursors: &self.recursors,
            rules: &self.rules,
            names: &self.names,
        }
    }
    pub(super) fn clear(&mut self) {
        self.types.clear();
        self.constructors.clear();
        self.recursors.clear();
        self.rules.clear();
        self.names.clear();
    }
    pub(super) fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let bytes = self.types.capacity() * crate::resource::charged::bytes::<Inductive>()
            + self.constructors.capacity() * crate::resource::charged::bytes::<Constructor>()
            + self.recursors.capacity() * crate::resource::charged::bytes::<Recursor>()
            + self.rules.capacity() * crate::resource::charged::bytes::<Rule>()
            + self.names.capacity() * crate::resource::charged::bytes::<NameId>();
        drop(self);
        b.release(bytes as u64)
    }
}

// Charged sizes (64-bit layout) of this module's stored types.
crate::resource::charged::charged! {
    Inductive => 48,
    Constructor => 36,
    Recursor => 52,
    Rule => 12,
}
