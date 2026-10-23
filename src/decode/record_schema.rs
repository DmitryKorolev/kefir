//! lean4export 3.1.0 field vocabularies, from the pinned format.
//! These describe syntax, never checkedness. References require the subsequent
//! prior-table lookup before publication; a matching shape cannot install anything.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Table {
    Name,
    Level,
    Expr,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Shape {
    Natural,
    String,
    NaturalString,
    Boolean,
    Reference(Table),
    List(Table),
    Pair(Table),
    Object(Object),
    Objects(Object),
    BinderInfo,
    Safety,
    QuotKind,
    Hint,
    JsonObject,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Object {
    Root,
    Meta,
    Exporter,
    Lean,
    Format,
    NameStr,
    NameNum,
    Constant,
    App,
    Binder,
    Let,
    Projection,
    Metadata,
    Axiom,
    Definition,
    Theorem,
    Opaque,
    Quotient,
    InductiveGroup,
    Inductive,
    Constructor,
    Recursor,
    Rule,
    RegularHint,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Field {
    pub name: &'static [u8],
    pub shape: Shape,
}
macro_rules! fields {
    ($($name:literal => $shape:expr),* $(,)?) => {
        {
            const FIELDS: &[Field] = &[$(Field { name: $name, shape: $shape }),*];
            const _: () = assert!(valid_vocabulary(FIELDS));
            FIELDS
        }
    };
}
// Every bit has exactly one spelling within its object's vocabulary. Keep this
// construction invariant checked at compile time, including the u64 capacity.
const fn valid_vocabulary(fields: &[Field]) -> bool {
    if fields.len() >= 64 {
        return false;
    }
    let mut i = 0;
    while i < fields.len() {
        let mut j = i + 1;
        while j < fields.len() {
            let (a, b) = (fields[i].name, fields[j].name);
            if a.len() == b.len() {
                let mut k = 0;
                while k < a.len() && a[k] == b[k] {
                    k += 1;
                }
                if k == a.len() {
                    return false;
                }
            }
            j += 1;
        }
        i += 1;
    }
    true
}
use Shape::*;
use Table::{Expr as E, Level as L, Name as N};
impl Object {
    /// Fixed vocabulary, independent of field order and any discriminant value.
    /// The index is its duplicate-key mask bit. Unknown keys take the cold path.
    pub(crate) fn fields(self) -> &'static [Field] {
        match self {
            Self::Root => fields![
                b"meta" => Shape::Object(Object::Meta),
                b"str" => Shape::Object(Object::NameStr), b"num" => Shape::Object(Object::NameNum),
                b"succ" => Reference(L), b"max" => Pair(L), b"imax" => Pair(L), b"param" => Reference(N),
                b"bvar" => Natural, b"sort" => Reference(L), b"const" => Shape::Object(Object::Constant),
                b"app" => Shape::Object(Object::App), b"lam" => Shape::Object(Object::Binder), b"forallE" => Shape::Object(Object::Binder),
                b"letE" => Shape::Object(Object::Let), b"proj" => Shape::Object(Object::Projection),
                b"natVal" => NaturalString, b"strVal" => String, b"mdata" => Shape::Object(Object::Metadata),
                b"axiom" => Shape::Object(Object::Axiom), b"def" => Shape::Object(Object::Definition),
                b"thm" => Shape::Object(Object::Theorem), b"opaque" => Shape::Object(Object::Opaque),
                b"quot" => Shape::Object(Object::Quotient), b"inductive" => Shape::Object(Object::InductiveGroup),
                b"in" => Natural, b"il" => Natural, b"ie" => Natural,
            ],
            Self::Meta => {
                fields![b"exporter" => Shape::Object(Object::Exporter), b"lean" => Shape::Object(Object::Lean), b"format" => Shape::Object(Object::Format)]
            }
            Self::Exporter => fields![b"name" => String, b"version" => String],
            Self::Lean => fields![b"githash" => String, b"version" => String],
            Self::Format => fields![b"version" => String],
            Self::NameStr => fields![b"pre" => Reference(N), b"str" => String],
            Self::NameNum => fields![b"pre" => Reference(N), b"i" => Natural],
            Self::Constant => fields![b"name" => Reference(N), b"us" => List(L)],
            Self::App => fields![b"fn" => Reference(E), b"arg" => Reference(E)],
            Self::Binder => {
                fields![b"name" => Reference(N), b"type" => Reference(E), b"body" => Reference(E), b"binderInfo" => BinderInfo]
            }
            Self::Let => {
                fields![b"name" => Reference(N), b"type" => Reference(E), b"value" => Reference(E), b"body" => Reference(E), b"nondep" => Boolean]
            }
            Self::Projection => {
                fields![b"typeName" => Reference(N), b"idx" => Natural, b"struct" => Reference(E)]
            }
            Self::Metadata => fields![b"expr" => Reference(E), b"data" => JsonObject],
            Self::Axiom => {
                fields![b"name" => Reference(N), b"levelParams" => List(N), b"type" => Reference(E), b"isUnsafe" => Boolean]
            }
            Self::Definition => {
                fields![b"name" => Reference(N), b"levelParams" => List(N), b"type" => Reference(E), b"value" => Reference(E), b"hints" => Hint, b"safety" => Safety, b"all" => List(N)]
            }
            Self::Theorem => {
                fields![b"name" => Reference(N), b"levelParams" => List(N), b"type" => Reference(E), b"value" => Reference(E), b"all" => List(N)]
            }
            Self::Opaque => {
                fields![b"name" => Reference(N), b"levelParams" => List(N), b"type" => Reference(E), b"value" => Reference(E), b"isUnsafe" => Boolean, b"all" => List(N)]
            }
            Self::Quotient => {
                fields![b"name" => Reference(N), b"levelParams" => List(N), b"type" => Reference(E), b"kind" => QuotKind]
            }
            Self::InductiveGroup => {
                fields![b"types" => Objects(Object::Inductive), b"ctors" => Objects(Object::Constructor), b"recs" => Objects(Object::Recursor)]
            }
            Self::Inductive => {
                fields![b"name" => Reference(N), b"levelParams" => List(N), b"type" => Reference(E), b"numParams" => Natural, b"numIndices" => Natural, b"all" => List(N), b"ctors" => List(N), b"numNested" => Natural, b"isRec" => Boolean, b"isUnsafe" => Boolean, b"isReflexive" => Boolean]
            }
            Self::Constructor => {
                fields![b"name" => Reference(N), b"levelParams" => List(N), b"type" => Reference(E), b"induct" => Reference(N), b"cidx" => Natural, b"numParams" => Natural, b"numFields" => Natural, b"isUnsafe" => Boolean]
            }
            Self::Recursor => {
                fields![b"name" => Reference(N), b"levelParams" => List(N), b"type" => Reference(E), b"all" => List(N), b"numParams" => Natural, b"numIndices" => Natural, b"numMotives" => Natural, b"numMinors" => Natural, b"rules" => Objects(Object::Rule), b"k" => Boolean, b"isUnsafe" => Boolean]
            }
            Self::Rule => {
                fields![b"ctor" => Reference(N), b"nfields" => Natural, b"rhs" => Reference(E)]
            }
            Self::RegularHint => fields![b"regular" => Natural],
        }
    }
    pub(crate) fn field(self, key: &[u8]) -> Option<(u8, Shape)> {
        self.fields()
            .iter()
            .enumerate()
            .find_map(|(bit, field)| (field.name == key).then_some((bit as u8, field.shape)))
    }
    /// All nested-schema fields are required. Root alternatives are validated
    /// separately; returning no mask prevents treating them all as optional.
    pub(crate) fn required(self) -> Option<u64> {
        if self == Self::Root {
            None
        } else {
            Some((1u64 << self.fields().len()) - 1)
        }
    }
    /// These are known forbidden fields, not unsupported extensions.
    pub(crate) fn prohibited(self, key: &[u8]) -> bool {
        self == Self::Axiom && key == b"value"
    }
}
