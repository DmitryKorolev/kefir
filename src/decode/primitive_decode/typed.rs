//! Production typed deserialization adapted from our direct comparison.
//! Schema validity and table availability never grant semantic authority.
use super::*;
use serde::de::{DeserializeSeed, Deserializer, MapAccess, Visitor, value::MapAccessDeserializer};
use std::{fmt, marker::PhantomData};
mod fast;
mod integrity;
use crate::decode::record_schema::Table;
use serde::Deserialize;
use serde_json::value::RawValue;
use std::borrow::Cow;
use std::cell::Cell;
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Nat<'a>(&'a [u8]);
impl<'de: 'a, 'a> Deserialize<'de> for Nat<'a> {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let raw = <&'a RawValue>::deserialize(d)?;
        Ok(Self(raw.get().as_bytes()))
    }
}
impl Nat<'_> {
    fn bytes(&self) -> &[u8] {
        self.0
    }
    fn valid(&self) -> Result<(), Cause> {
        if !self.bytes().is_empty() && self.bytes().iter().all(u8::is_ascii_digit) {
            Ok(())
        } else {
            Err(Cause::InvalidRecord)
        }
    }
}
enum Refs<'a> {
    Typed(Vec<Ref<'a>>),
    Canonical { bytes: &'a [u8], count: usize },
}
impl<'de: 'a, 'a> Deserialize<'de> for Refs<'a> {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Vec::<Ref<'a>>::deserialize(d).map(Self::Typed)
    }
}
impl Refs<'_> {
    fn len(&self) -> usize {
        match self {
            Self::Typed(values) => values.len(),
            Self::Canonical { count, .. } => *count,
        }
    }

    fn for_each(&self, mut f: impl FnMut(&[u8]) -> Result<(), Cause>) -> Result<(), Cause> {
        match self {
            Self::Typed(values) => {
                for value in values {
                    f(value.raw.bytes())?;
                }
            }
            Self::Canonical { bytes, count } => {
                let mut cursor = 0;
                if bytes.get(cursor) != Some(&b'[') {
                    return Err(Cause::Resource(ResourceError::Invariant));
                }
                cursor += 1;
                let mut seen = 0;
                if bytes.get(cursor) == Some(&b']') {
                    cursor += 1;
                } else {
                    loop {
                        let start = cursor;
                        while bytes.get(cursor).is_some_and(u8::is_ascii_digit) {
                            cursor += 1;
                        }
                        if start == cursor {
                            return Err(Cause::Resource(ResourceError::Invariant));
                        }
                        f(&bytes[start..cursor])?;
                        seen += 1;
                        match bytes.get(cursor) {
                            Some(b',') => cursor += 1,
                            Some(b']') => {
                                cursor += 1;
                                break;
                            }
                            _ => return Err(Cause::Resource(ResourceError::Invariant)),
                        }
                    }
                }
                if cursor != bytes.len() || seen != *count {
                    return Err(Cause::Resource(ResourceError::Invariant));
                }
            }
        }
        Ok(())
    }
}

/// Cache scope: one freshly parsed record, before publication. Parsed values
/// are canonical external u32 IDs established by fast::Cursor, not table slots
/// or checkedness. Check overwrites them with resolved session-local slots.
#[derive(Clone, Copy)]
enum RefState {
    Raw,
    Parsed(u32),
    Resolved(u32),
}
const _: () = assert!(std::mem::size_of::<RefState>() == std::mem::size_of::<Option<u32>>());

struct Ref<'a> {
    raw: Nat<'a>,
    slot: Cell<RefState>,
}
#[cfg(target_pointer_width = "64")]
const _: () = assert!(std::mem::size_of::<Ref<'_>>() == 24);

impl<'de: 'a, 'a> Deserialize<'de> for Ref<'a> {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Ok(Self {
            raw: Nat::deserialize(d)?,
            slot: Cell::new(RefState::Raw),
        })
    }
}
impl Ref<'_> {
    #[cfg_attr(not(debug_assertions), inline(always))]
    fn check(&self, table: Table, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        let index = match table {
            Table::Name => &d.name_ids,
            Table::Level => &d.level_ids,
            Table::Expr => &d.expression_ids,
        };
        let resolved = match self.slot.get() {
            RefState::Parsed(number) => index.resolve_canonical_u32(self.raw.bytes(), number, b),
            RefState::Raw | RefState::Resolved(_) => {
                self.raw.valid()?;
                index.resolve(self.raw.bytes(), b)
            }
        };
        let slot = resolved.map_err(index_error)?.ok_or(Cause::InvalidRecord)?;
        let slot = if matches!(table, Table::Name) {
            d.imported_name_slot(slot).map_err(Cause::Resource)?
        } else {
            slot
        };
        self.slot.set(RefState::Resolved(slot));
        Ok(())
    }
    fn slot(&self) -> Result<u32, Cause> {
        match self.slot.get() {
            RefState::Resolved(slot) => Ok(slot),
            RefState::Raw | RefState::Parsed(_) => Err(Cause::Resource(ResourceError::Invariant)),
        }
    }
    fn resolved(&self, table: Table) -> Result<Resolved, Cause> {
        Ok(Resolved {
            table,
            slot: self.slot()?,
        })
    }
}
trait Check {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause>;
}
type Meta<'a> = ObjectOnly<MetaFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct MetaFields<'a> {
    #[serde(rename = "exporter", borrow)]
    f_exporter: Exporter<'a>,
    #[serde(rename = "lean", borrow)]
    f_lean: Lean<'a>,
    #[serde(rename = "format", borrow)]
    f_format: Format<'a>,
}
impl Check for Meta<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_exporter.check(d, b)?;
        self.f_lean.check(d, b)?;
        self.f_format.check(d, b)?;
        Ok(())
    }
}
type Exporter<'a> = ObjectOnly<ExporterFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ExporterFields<'a> {
    #[serde(rename = "name", borrow)]
    f_name: Cow<'a, str>,
    #[serde(rename = "version", borrow)]
    f_version: Cow<'a, str>,
}
impl Check for Exporter<'_> {
    fn check(&self, _d: &Decoder, _b: &mut Budget) -> Result<(), Cause> {
        Ok(())
    }
}
type Lean<'a> = ObjectOnly<LeanFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct LeanFields<'a> {
    #[serde(rename = "githash", borrow)]
    f_githash: Cow<'a, str>,
    #[serde(rename = "version", borrow)]
    f_version: Cow<'a, str>,
}
impl Check for Lean<'_> {
    fn check(&self, _d: &Decoder, _b: &mut Budget) -> Result<(), Cause> {
        Ok(())
    }
}
type Format<'a> = ObjectOnly<FormatFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FormatFields<'a> {
    #[serde(rename = "version", borrow)]
    f_version: Cow<'a, str>,
}
impl Check for Format<'_> {
    fn check(&self, _d: &Decoder, _b: &mut Budget) -> Result<(), Cause> {
        Ok(())
    }
}
type NameStr<'a> = ObjectOnly<NameStrFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct NameStrFields<'a> {
    #[serde(rename = "pre", borrow)]
    f_pre: Ref<'a>,
    #[serde(rename = "str", borrow)]
    f_str: Cow<'a, str>,
}
impl Check for NameStr<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_pre.check(Table::Name, d, b)?;

        Ok(())
    }
}
type NameNum<'a> = ObjectOnly<NameNumFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct NameNumFields<'a> {
    #[serde(rename = "pre", borrow)]
    f_pre: Ref<'a>,
    #[serde(rename = "i", borrow)]
    f_i: Nat<'a>,
}
impl Check for NameNum<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_pre.check(Table::Name, d, b)?;
        self.f_i.valid()?;
        Ok(())
    }
}
type Constant<'a> = ObjectOnly<ConstantFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ConstantFields<'a> {
    #[serde(rename = "name", borrow)]
    f_name: Ref<'a>,
    #[serde(rename = "us", borrow)]
    f_us: Refs<'a>,
}
impl Check for Constant<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_name.check(Table::Name, d, b)?;
        Ok(())
    }
}
type App<'a> = ObjectOnly<AppFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AppFields<'a> {
    #[serde(rename = "fn", borrow)]
    f_fn: Ref<'a>,
    #[serde(rename = "arg", borrow)]
    f_arg: Ref<'a>,
}
impl Check for App<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_fn.check(Table::Expr, d, b)?;
        self.f_arg.check(Table::Expr, d, b)?;
        Ok(())
    }
}
type Binder<'a> = ObjectOnly<BinderFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct BinderFields<'a> {
    #[serde(rename = "name", borrow)]
    f_name: Ref<'a>,
    #[serde(rename = "type", borrow)]
    f_type: Ref<'a>,
    #[serde(rename = "body", borrow)]
    f_body: Ref<'a>,
    #[serde(rename = "binderInfo", borrow)]
    f_binder_info: Cow<'a, str>,
}
impl Check for Binder<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_name.check(Table::Name, d, b)?;
        self.f_type.check(Table::Expr, d, b)?;
        self.f_body.check(Table::Expr, d, b)?;
        if !matches!(
            self.f_binder_info.as_ref(),
            "default" | "implicit" | "strictImplicit" | "instImplicit"
        ) {
            return Err(Cause::InvalidRecord);
        }
        Ok(())
    }
}
type Let<'a> = ObjectOnly<LetFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct LetFields<'a> {
    #[serde(rename = "name", borrow)]
    f_name: Ref<'a>,
    #[serde(rename = "type", borrow)]
    f_type: Ref<'a>,
    #[serde(rename = "value", borrow)]
    f_value: Ref<'a>,
    #[serde(rename = "body", borrow)]
    f_body: Ref<'a>,
    #[serde(rename = "nondep")]
    f_nondep: bool,
}
impl Check for Let<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_name.check(Table::Name, d, b)?;
        self.f_type.check(Table::Expr, d, b)?;
        self.f_value.check(Table::Expr, d, b)?;
        self.f_body.check(Table::Expr, d, b)?;

        Ok(())
    }
}
type Projection<'a> = ObjectOnly<ProjectionFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProjectionFields<'a> {
    #[serde(rename = "typeName", borrow)]
    f_type_name: Ref<'a>,
    #[serde(rename = "idx", borrow)]
    f_idx: Nat<'a>,
    #[serde(rename = "struct", borrow)]
    f_struct: Ref<'a>,
}
impl Check for Projection<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_type_name.check(Table::Name, d, b)?;
        self.f_idx.valid()?;
        self.f_struct.check(Table::Expr, d, b)?;
        Ok(())
    }
}
type Metadata<'a> = ObjectOnly<MetadataFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct MetadataFields<'a> {
    #[serde(rename = "expr", borrow)]
    f_expr: Ref<'a>,
    #[serde(rename = "data", borrow)]
    f_data: &'a RawValue,
}
impl Check for Metadata<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_expr.check(Table::Expr, d, b)?;
        // The payload is arbitrary bounded JSON whose member names are exempt
        // from the extra-field rule; duplicate keys, Unicode, depth and
        // resource rules still apply to it. Preserving it verbatim
        // requires the object shape before any node exists.
        integrity::validate_payload(self.f_data.get().as_bytes(), b)
    }
}
type Axiom<'a> = ObjectOnly<AxiomFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AxiomFields<'a> {
    #[serde(rename = "name", borrow)]
    f_name: Ref<'a>,
    #[serde(rename = "levelParams", borrow)]
    f_level_params: Refs<'a>,
    #[serde(rename = "type", borrow)]
    f_type: Ref<'a>,
    #[serde(rename = "isUnsafe")]
    f_is_unsafe: bool,
}
impl Check for Axiom<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_name.check(Table::Name, d, b)?;
        self.f_type.check(Table::Expr, d, b)?;

        Ok(())
    }
}
type Definition<'a> = ObjectOnly<DefinitionFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DefinitionFields<'a> {
    #[serde(rename = "name", borrow)]
    f_name: Ref<'a>,
    #[serde(rename = "levelParams", borrow)]
    f_level_params: Refs<'a>,
    #[serde(rename = "type", borrow)]
    f_type: Ref<'a>,
    #[serde(rename = "value", borrow)]
    f_value: Ref<'a>,
    #[serde(rename = "hints", borrow)]
    f_hints: Hint<'a>,
    #[serde(rename = "safety", borrow)]
    f_safety: Cow<'a, str>,
    #[serde(rename = "all", borrow)]
    f_all: Refs<'a>,
}
impl Check for Definition<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_name.check(Table::Name, d, b)?;
        self.f_type.check(Table::Expr, d, b)?;
        self.f_value.check(Table::Expr, d, b)?;
        self.f_hints.check(d, b)?;
        if !matches!(self.f_safety.as_ref(), "safe" | "unsafe" | "partial") {
            return Err(Cause::InvalidRecord);
        }
        Ok(())
    }
}
type Theorem<'a> = ObjectOnly<TheoremFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TheoremFields<'a> {
    #[serde(rename = "name", borrow)]
    f_name: Ref<'a>,
    #[serde(rename = "levelParams", borrow)]
    f_level_params: Refs<'a>,
    #[serde(rename = "type", borrow)]
    f_type: Ref<'a>,
    #[serde(rename = "value", borrow)]
    f_value: Ref<'a>,
    #[serde(rename = "all", borrow)]
    f_all: Refs<'a>,
}
impl Check for Theorem<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_name.check(Table::Name, d, b)?;
        self.f_type.check(Table::Expr, d, b)?;
        self.f_value.check(Table::Expr, d, b)?;
        Ok(())
    }
}
type Opaque<'a> = ObjectOnly<OpaqueFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct OpaqueFields<'a> {
    #[serde(rename = "name", borrow)]
    f_name: Ref<'a>,
    #[serde(rename = "levelParams", borrow)]
    f_level_params: Refs<'a>,
    #[serde(rename = "type", borrow)]
    f_type: Ref<'a>,
    #[serde(rename = "value", borrow)]
    f_value: Ref<'a>,
    #[serde(rename = "isUnsafe")]
    f_is_unsafe: bool,
    #[serde(rename = "all", borrow)]
    f_all: Refs<'a>,
}
impl Check for Opaque<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_name.check(Table::Name, d, b)?;
        self.f_type.check(Table::Expr, d, b)?;
        self.f_value.check(Table::Expr, d, b)?;
        Ok(())
    }
}
type Quotient<'a> = ObjectOnly<QuotientFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct QuotientFields<'a> {
    #[serde(rename = "name", borrow)]
    f_name: Ref<'a>,
    #[serde(rename = "levelParams", borrow)]
    f_level_params: Vec<Ref<'a>>,
    #[serde(rename = "type", borrow)]
    f_type: Ref<'a>,
    #[serde(rename = "kind", borrow)]
    f_kind: Cow<'a, str>,
}
impl Check for Quotient<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_name.check(Table::Name, d, b)?;
        for v in &self.f_level_params {
            v.check(Table::Name, d, b)?;
        }
        self.f_type.check(Table::Expr, d, b)?;
        quotients::Role::parse(&self.f_kind)?;
        Ok(())
    }
}
type InductiveGroup<'a> = ObjectOnly<InductiveGroupFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct InductiveGroupFields<'a> {
    #[serde(rename = "types", borrow)]
    f_types: Vec<Inductive<'a>>,
    #[serde(rename = "ctors", borrow)]
    f_ctors: Vec<Constructor<'a>>,
    #[serde(rename = "recs", borrow)]
    f_recs: Vec<Recursor<'a>>,
}
impl Check for InductiveGroup<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        for v in &self.f_types {
            v.check(d, b)?;
        }
        for v in &self.f_ctors {
            v.check(d, b)?;
        }
        for v in &self.f_recs {
            v.check(d, b)?;
        }
        Ok(())
    }
}
type Inductive<'a> = ObjectOnly<InductiveFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct InductiveFields<'a> {
    #[serde(rename = "name", borrow)]
    f_name: Ref<'a>,
    #[serde(rename = "levelParams", borrow)]
    f_level_params: Vec<Ref<'a>>,
    #[serde(rename = "type", borrow)]
    f_type: Ref<'a>,
    #[serde(rename = "numParams", borrow)]
    f_num_params: Nat<'a>,
    #[serde(rename = "numIndices", borrow)]
    f_num_indices: Nat<'a>,
    #[serde(rename = "all", borrow)]
    f_all: Vec<Ref<'a>>,
    #[serde(rename = "ctors", borrow)]
    f_ctors: Vec<Ref<'a>>,
    #[serde(rename = "numNested", borrow)]
    f_num_nested: Nat<'a>,
    #[serde(rename = "isRec")]
    f_is_rec: bool,
    #[serde(rename = "isUnsafe")]
    f_is_unsafe: bool,
    #[serde(rename = "isReflexive")]
    f_is_reflexive: bool,
}
impl Check for Inductive<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_name.check(Table::Name, d, b)?;
        for v in &self.f_level_params {
            v.check(Table::Name, d, b)?;
        }
        self.f_type.check(Table::Expr, d, b)?;
        self.f_num_params.valid()?;
        self.f_num_indices.valid()?;
        for v in &self.f_all {
            v.check(Table::Name, d, b)?;
        }
        for v in &self.f_ctors {
            v.check(Table::Name, d, b)?;
        }
        self.f_num_nested.valid()?;

        Ok(())
    }
}
type Constructor<'a> = ObjectOnly<ConstructorFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ConstructorFields<'a> {
    #[serde(rename = "name", borrow)]
    f_name: Ref<'a>,
    #[serde(rename = "levelParams", borrow)]
    f_level_params: Vec<Ref<'a>>,
    #[serde(rename = "type", borrow)]
    f_type: Ref<'a>,
    #[serde(rename = "induct", borrow)]
    f_induct: Ref<'a>,
    #[serde(rename = "cidx", borrow)]
    f_cidx: Nat<'a>,
    #[serde(rename = "numParams", borrow)]
    f_num_params: Nat<'a>,
    #[serde(rename = "numFields", borrow)]
    f_num_fields: Nat<'a>,
    #[serde(rename = "isUnsafe")]
    f_is_unsafe: bool,
}
impl Check for Constructor<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_name.check(Table::Name, d, b)?;
        for v in &self.f_level_params {
            v.check(Table::Name, d, b)?;
        }
        self.f_type.check(Table::Expr, d, b)?;
        self.f_induct.check(Table::Name, d, b)?;
        self.f_cidx.valid()?;
        self.f_num_params.valid()?;
        self.f_num_fields.valid()?;

        Ok(())
    }
}
type Recursor<'a> = ObjectOnly<RecursorFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RecursorFields<'a> {
    #[serde(rename = "name", borrow)]
    f_name: Ref<'a>,
    #[serde(rename = "levelParams", borrow)]
    f_level_params: Vec<Ref<'a>>,
    #[serde(rename = "type", borrow)]
    f_type: Ref<'a>,
    #[serde(rename = "all", borrow)]
    f_all: Vec<Ref<'a>>,
    #[serde(rename = "numParams", borrow)]
    f_num_params: Nat<'a>,
    #[serde(rename = "numIndices", borrow)]
    f_num_indices: Nat<'a>,
    #[serde(rename = "numMotives", borrow)]
    f_num_motives: Nat<'a>,
    #[serde(rename = "numMinors", borrow)]
    f_num_minors: Nat<'a>,
    #[serde(rename = "rules", borrow)]
    f_rules: Vec<Rule<'a>>,
    #[serde(rename = "k")]
    f_k: bool,
    #[serde(rename = "isUnsafe")]
    f_is_unsafe: bool,
}
impl Check for Recursor<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_name.check(Table::Name, d, b)?;
        for v in &self.f_level_params {
            v.check(Table::Name, d, b)?;
        }
        self.f_type.check(Table::Expr, d, b)?;
        for v in &self.f_all {
            v.check(Table::Name, d, b)?;
        }
        self.f_num_params.valid()?;
        self.f_num_indices.valid()?;
        self.f_num_motives.valid()?;
        self.f_num_minors.valid()?;
        for v in &self.f_rules {
            v.check(d, b)?;
        }

        Ok(())
    }
}
type Rule<'a> = ObjectOnly<RuleFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RuleFields<'a> {
    #[serde(rename = "ctor", borrow)]
    f_ctor: Ref<'a>,
    #[serde(rename = "nfields", borrow)]
    f_nfields: Nat<'a>,
    #[serde(rename = "rhs", borrow)]
    f_rhs: Ref<'a>,
}
impl Check for Rule<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        self.f_ctor.check(Table::Name, d, b)?;
        self.f_nfields.valid()?;
        self.f_rhs.check(Table::Expr, d, b)?;
        Ok(())
    }
}
type RegularHint<'a> = ObjectOnly<RegularHintFields<'a>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RegularHintFields<'a> {
    #[serde(rename = "regular", borrow)]
    f_regular: Nat<'a>,
}
impl Check for RegularHint<'_> {
    fn check(&self, _d: &Decoder, _b: &mut Budget) -> Result<(), Cause> {
        self.f_regular.valid()?;
        Ok(())
    }
}
enum Hint<'a> {
    String(Cow<'a, str>),
    Regular(RegularHint<'a>),
}
impl<'de: 'a, 'a> Deserialize<'de> for Hint<'a> {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        struct V;
        impl<'de> serde::de::Visitor<'de> for V {
            type Value = Hint<'de>;
            fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_str("hint string or regular object")
            }
            fn visit_borrowed_str<E: serde::de::Error>(
                self,
                s: &'de str,
            ) -> Result<Self::Value, E> {
                Ok(Hint::String(Cow::Borrowed(s)))
            }
            fn visit_str<E: serde::de::Error>(self, s: &str) -> Result<Self::Value, E> {
                Ok(Hint::String(Cow::Owned(s.to_owned())))
            }
            fn visit_map<M: serde::de::MapAccess<'de>>(
                self,
                mut m: M,
            ) -> Result<Self::Value, M::Error> {
                let key: Option<Cow<'de, str>> = m.next_key()?;
                if key.as_deref() != Some("regular") {
                    return Err(serde::de::Error::custom("regular key required"));
                }
                let value = m.next_value()?;
                if m.next_key::<serde::de::IgnoredAny>()?.is_some() {
                    return Err(serde::de::Error::custom("extra hint key"));
                }
                Ok(Hint::Regular(ObjectOnly(RegularHintFields {
                    f_regular: value,
                })))
            }
        }
        d.deserialize_any(V)
    }
}
impl Check for Hint<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        match self {
            Self::String(s) if matches!(s.as_ref(), "opaque" | "abbrev") => Ok(()),
            Self::Regular(r) => r.check(d, b),
            _ => Err(Cause::InvalidRecord),
        }
    }
}
#[derive(Clone, Copy, Deserialize, Eq, PartialEq)]
enum RootKey {
    #[serde(rename = "meta")]
    Meta,
    #[serde(rename = "in")]
    NameId,
    #[serde(rename = "il")]
    LevelId,
    #[serde(rename = "ie")]
    ExprId,
    #[serde(rename = "str")]
    NameStr,
    #[serde(rename = "num")]
    NameNum,
    #[serde(rename = "succ")]
    Succ,
    #[serde(rename = "max")]
    Max,
    #[serde(rename = "imax")]
    IMax,
    #[serde(rename = "param")]
    Param,
    #[serde(rename = "bvar")]
    Bvar,
    #[serde(rename = "sort")]
    Sort,
    #[serde(rename = "const")]
    Constant,
    #[serde(rename = "app")]
    App,
    #[serde(rename = "lam")]
    Lambda,
    #[serde(rename = "forallE")]
    Pi,
    #[serde(rename = "letE")]
    Let,
    #[serde(rename = "proj")]
    Projection,
    #[serde(rename = "natVal")]
    NatVal,
    #[serde(rename = "strVal")]
    StrVal,
    #[serde(rename = "mdata")]
    Metadata,
    #[serde(rename = "axiom")]
    Axiom,
    #[serde(rename = "def")]
    Definition,
    #[serde(rename = "thm")]
    Theorem,
    #[serde(rename = "opaque")]
    Opaque,
    #[serde(rename = "quot")]
    Quotient,
    #[serde(rename = "inductive")]
    Inductive,
}

enum SyntaxPlan<'a> {
    NameStr(NameStr<'a>),
    NameNum(NameNum<'a>),
    Succ(Ref<'a>),
    Max(bool, [Ref<'a>; 2]),
    Param(Ref<'a>),
    Bvar(Nat<'a>),
    Sort(Ref<'a>),
    Constant(Constant<'a>),
    App(App<'a>),
    Binder(bool, Binder<'a>),
    Let(Let<'a>),
    Projection(Projection<'a>),
    NatVal(Cow<'a, str>),
    StrVal(Cow<'a, str>),
    Metadata(Metadata<'a>),
}
impl SyntaxPlan<'_> {
    fn check(&self, d: &Decoder, b: &mut Budget) -> Result<(), Cause> {
        match self {
            Self::NameStr(v) => v.check(d, b),
            Self::NameNum(v) => v.check(d, b),
            Self::Succ(v) | Self::Param(v) | Self::Sort(v) => v.check(
                match self {
                    Self::Succ(_) => Table::Level,
                    Self::Param(_) => Table::Name,
                    Self::Sort(_) => Table::Level,
                    _ => unreachable!(),
                },
                d,
                b,
            ),
            Self::Max(_, values) => {
                for value in values {
                    value.check(Table::Level, d, b)?;
                }
                Ok(())
            }
            Self::Bvar(v) => v.valid(),
            Self::Constant(v) => v.check(d, b),
            Self::App(v) => v.check(d, b),
            Self::Binder(_, v) => v.check(d, b),
            Self::Let(v) => v.check(d, b),
            Self::Projection(v) => v.check(d, b),
            Self::NatVal(v) => {
                if v.is_empty() || !v.bytes().all(|byte| byte.is_ascii_digit()) {
                    Err(Cause::InvalidRecord)
                } else {
                    Ok(())
                }
            }
            Self::StrVal(_) => Ok(()),
            Self::Metadata(v) => v.check(d, b),
        }
    }
}

enum Plan<'a> {
    Header(Meta<'a>),
    Syntax {
        id: Nat<'a>,
        id_number: Option<u32>,
        payload: SyntaxPlan<'a>,
    },
    Axiom(Axiom<'a>),
    Definition(Definition<'a>),
    Theorem(Theorem<'a>),
    Opaque(Opaque<'a>),
    Quotient(Quotient<'a>),
    Inductive(InductiveGroup<'a>),
}

fn id_key(key: RootKey) -> Option<RootKey> {
    Some(match key {
        RootKey::NameStr | RootKey::NameNum => RootKey::NameId,
        RootKey::Succ | RootKey::Max | RootKey::IMax | RootKey::Param => RootKey::LevelId,
        RootKey::Bvar
        | RootKey::Sort
        | RootKey::Constant
        | RootKey::App
        | RootKey::Lambda
        | RootKey::Pi
        | RootKey::Let
        | RootKey::Projection
        | RootKey::NatVal
        | RootKey::StrVal
        | RootKey::Metadata => RootKey::ExprId,
        _ => return None,
    })
}

fn syntax_value<'de, M: MapAccess<'de>>(
    key: RootKey,
    map: &mut M,
) -> Result<SyntaxPlan<'de>, M::Error> {
    Ok(match key {
        RootKey::NameStr => SyntaxPlan::NameStr(map.next_value()?),
        RootKey::NameNum => SyntaxPlan::NameNum(map.next_value()?),
        RootKey::Succ => SyntaxPlan::Succ(map.next_value()?),
        RootKey::Max => SyntaxPlan::Max(false, map.next_value()?),
        RootKey::IMax => SyntaxPlan::Max(true, map.next_value()?),
        RootKey::Param => SyntaxPlan::Param(map.next_value()?),
        RootKey::Bvar => SyntaxPlan::Bvar(map.next_value()?),
        RootKey::Sort => SyntaxPlan::Sort(map.next_value()?),
        RootKey::Constant => SyntaxPlan::Constant(map.next_value()?),
        RootKey::App => SyntaxPlan::App(map.next_value()?),
        RootKey::Lambda => SyntaxPlan::Binder(false, map.next_value()?),
        RootKey::Pi => SyntaxPlan::Binder(true, map.next_value()?),
        RootKey::Let => SyntaxPlan::Let(map.next_value()?),
        RootKey::Projection => SyntaxPlan::Projection(map.next_value()?),
        RootKey::NatVal => SyntaxPlan::NatVal(map.next_value()?),
        RootKey::StrVal => SyntaxPlan::StrVal(map.next_value()?),
        RootKey::Metadata => SyntaxPlan::Metadata(map.next_value()?),
        _ => return Err(serde::de::Error::custom("record kind")),
    })
}

struct PlanSeed;
impl<'de> DeserializeSeed<'de> for PlanSeed {
    type Value = Plan<'de>;

    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<Self::Value, D::Error> {
        d.deserialize_map(PlanVisitor)
    }
}

struct PlanVisitor;
impl<'de> Visitor<'de> for PlanVisitor {
    type Value = Plan<'de>;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("one lean4export record object")
    }

    fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<Self::Value, M::Error> {
        let first = map
            .next_key::<RootKey>()?
            .ok_or_else(|| serde::de::Error::custom("empty record"))?;
        let plan = match first {
            RootKey::Meta => Plan::Header(map.next_value()?),
            RootKey::Axiom => Plan::Axiom(map.next_value()?),
            RootKey::Definition => Plan::Definition(map.next_value()?),
            RootKey::Theorem => Plan::Theorem(map.next_value()?),
            RootKey::Opaque => Plan::Opaque(map.next_value()?),
            RootKey::Quotient => Plan::Quotient(map.next_value()?),
            RootKey::Inductive => Plan::Inductive(map.next_value()?),
            RootKey::NameId | RootKey::LevelId | RootKey::ExprId => {
                let id: Nat<'de> = map.next_value()?;
                let kind = map
                    .next_key::<RootKey>()?
                    .ok_or_else(|| serde::de::Error::custom("missing payload"))?;
                if id_key(kind) != Some(first) {
                    return Err(serde::de::Error::custom("wrong identifier kind"));
                }
                Plan::Syntax {
                    id,
                    id_number: None,
                    payload: syntax_value(kind, &mut map)?,
                }
            }
            kind if id_key(kind).is_some() => {
                let payload = syntax_value(kind, &mut map)?;
                let found = map
                    .next_key::<RootKey>()?
                    .ok_or_else(|| serde::de::Error::custom("missing identifier"))?;
                if Some(found) != id_key(kind) {
                    return Err(serde::de::Error::custom("wrong identifier kind"));
                }
                Plan::Syntax {
                    id: map.next_value()?,
                    id_number: None,
                    payload,
                }
            }
            _ => return Err(serde::de::Error::custom("record kind")),
        };
        if map.next_key::<RootKey>()?.is_some() {
            return Err(serde::de::Error::custom("extra root field"));
        }
        Ok(plan)
    }
}

struct Ordinary<'a, 'de> {
    name: &'a Ref<'de>,
    parameters: &'a Refs<'de>,
    ty: &'a Ref<'de>,
    value: Option<&'a Ref<'de>>,
    all: Option<&'a Refs<'de>>,
    hint: Option<&'a Hint<'de>>,
    kind: declarations::Kind,
    safety: declarations::Safety,
}
fn ordinary(
    d: &Decoder,
    s: &mut Scratch,
    b: &mut Budget,
    fields: Ordinary<'_, '_>,
) -> Result<declarations::Fields, Cause> {
    let Ordinary {
        name,
        parameters,
        ty,
        value,
        all,
        hint,
        kind,
        safety,
    } = fields;
    let name = d
        .names
        .resolve_slot(name.slot()?, b)
        .map_err(Cause::Resource)?;
    let ty = d
        .expressions
        .resolve_slot(ty.slot()?, b)
        .map_err(Cause::Resource)?;
    let value = value
        .map(|value| {
            d.expressions
                .resolve_slot(value.slot()?, b)
                .map_err(Cause::Resource)
        })
        .transpose()?;
    // Resolve every borrowed list before persistent scratch growth. The local
    // vectors are bounded by the record length (at least two input bytes per
    // element) and are covered by the live 256N parser reservation. This keeps
    // malformed-reference observations ahead of scratch storage exhaustion.
    let parameters = resolved_names(d, parameters, b)?;
    let all = all.map(|values| resolved_names(d, values, b)).transpose()?;
    b.grow_vec(&mut s.declaration.parameters, parameters.len())
        .map_err(Cause::Resource)?;
    if let Some(values) = &all {
        b.grow_vec(&mut s.declaration.all, values.len())
            .map_err(Cause::Resource)?;
    }
    s.declaration.parameters.extend_from_slice(&parameters);
    if let Some(values) = &all {
        s.declaration.all.extend_from_slice(values);
    }
    if let Some(Hint::Regular(r)) = hint {
        let digits = r.f_regular.bytes();
        b.charge_work(digits.len() as u64 + 1)
            .map_err(Cause::Resource)?;
        b.grow_vec(&mut s.declaration.hint, digits.len())
            .map_err(Cause::Resource)?;
        s.declaration.hint.extend_from_slice(digits);
    }
    Ok(declarations::Fields {
        kind,
        name,
        ty,
        value,
        safety,
        hint: hint.map(|h| match h {
            Hint::String(s) if s == "opaque" => 0,
            Hint::String(_) => 1,
            Hint::Regular(_) => 2,
        }),
    })
}
impl Decoder {
    #[cfg_attr(not(debug_assertions), inline(always))]
    fn publish_plan(
        &mut self,
        plan: Plan<'_>,
        s: &mut Scratch,
        b: &mut Budget,
    ) -> Result<Parsed, Cause> {
        s.universes.clear();
        // Only the matching Parsed variant can expose a payload through item;
        // inactive payload lengths are unreachable. Clear an owner before its
        // next use, retaining exactly the same capacities and budget charges.
        match plan {
            Plan::Header(v) => {
                v.check(self, b)?;
                Err(Cause::Metadata)
            }
            Plan::Quotient(v) => {
                s.declaration.clear();
                v.check(self, b)?;
                b.grow_vec(&mut s.declaration.parameters, v.f_level_params.len())
                    .map_err(Cause::Resource)?;
                for parameter in &v.f_level_params {
                    s.declaration.parameters.push(name(self, parameter, b)?);
                }
                Ok(Parsed::Quotient(quotients::Fields {
                    role: quotients::Role::parse(&v.f_kind)?,
                    name: name(self, &v.f_name, b)?,
                    ty: expr(self, &v.f_type, b)?,
                }))
            }
            Plan::Axiom(v) => {
                s.declaration.clear();
                v.check(self, b)?;
                ordinary(
                    self,
                    s,
                    b,
                    Ordinary {
                        name: &v.f_name,
                        parameters: &v.f_level_params,
                        ty: &v.f_type,
                        value: None,
                        all: None,
                        hint: None,
                        kind: declarations::Kind::Axiom,
                        safety: if v.f_is_unsafe {
                            declarations::Safety::Unsafe
                        } else {
                            declarations::Safety::Safe
                        },
                    },
                )
                .map(Parsed::Declaration)
            }
            Plan::Definition(v) => {
                s.declaration.clear();
                v.check(self, b)?;
                ordinary(
                    self,
                    s,
                    b,
                    Ordinary {
                        name: &v.f_name,
                        parameters: &v.f_level_params,
                        ty: &v.f_type,
                        value: Some(&v.f_value),
                        all: Some(&v.f_all),
                        hint: Some(&v.f_hints),
                        kind: declarations::Kind::Definition,
                        safety: match v.f_safety.as_ref() {
                            "safe" => declarations::Safety::Safe,
                            "unsafe" => declarations::Safety::Unsafe,
                            "partial" => declarations::Safety::Partial,
                            _ => return Err(Cause::InvalidRecord),
                        },
                    },
                )
                .map(Parsed::Declaration)
            }
            Plan::Theorem(v) => {
                s.declaration.clear();
                v.check(self, b)?;
                ordinary(
                    self,
                    s,
                    b,
                    Ordinary {
                        name: &v.f_name,
                        parameters: &v.f_level_params,
                        ty: &v.f_type,
                        value: Some(&v.f_value),
                        all: Some(&v.f_all),
                        hint: None,
                        kind: declarations::Kind::Theorem,
                        safety: declarations::Safety::Safe,
                    },
                )
                .map(Parsed::Declaration)
            }
            Plan::Opaque(v) => {
                s.declaration.clear();
                v.check(self, b)?;
                ordinary(
                    self,
                    s,
                    b,
                    Ordinary {
                        name: &v.f_name,
                        parameters: &v.f_level_params,
                        ty: &v.f_type,
                        value: Some(&v.f_value),
                        all: Some(&v.f_all),
                        hint: None,
                        kind: declarations::Kind::Opaque,
                        safety: if v.f_is_unsafe {
                            declarations::Safety::Unsafe
                        } else {
                            declarations::Safety::Safe
                        },
                    },
                )
                .map(Parsed::Declaration)
            }
            Plan::Inductive(v) => {
                s.inductive.clear();
                v.check(self, b)?;
                group(self, &mut s.inductive, &v, b)?;
                Ok(Parsed::Inductive)
            }
            Plan::Syntax {
                id,
                id_number,
                payload,
            } => {
                if id_number.is_none() {
                    id.valid()?;
                }
                payload.check(self, b)?;
                self.publish_syntax_plan(id, id_number, payload, s, b)
                    .map(Parsed::Syntax)
                    .map_err(|failure| failure.cause)
            }
        }
    }

    fn publish_syntax_plan(
        &mut self,
        id: Nat<'_>,
        id_number: Option<u32>,
        payload: SyntaxPlan<'_>,
        s: &mut Scratch,
        b: &mut Budget,
    ) -> Result<Published, Failure> {
        let mut p = Pending::default();
        macro_rules! r {
            ($v:expr,$t:ident) => {
                $v.resolved(Table::$t).map_err(|cause| Failure {
                    observed: empty(),
                    cause,
                })?
            };
        }
        match &payload {
            SyntaxPlan::NameStr(v) => {
                p.kind = Some(Kind::Str);
                p.refs[0] = Some(r!(v.f_pre, Name));
                p.component = Some(PendingComponent::Text(&v.f_str));
            }
            SyntaxPlan::NameNum(v) => {
                p.kind = Some(Kind::Num);
                p.refs[0] = Some(r!(v.f_pre, Name));
                p.component = Some(PendingComponent::Number(v.f_i.bytes()));
            }
            SyntaxPlan::Succ(v) => {
                p.kind = Some(Kind::Succ);
                p.refs[0] = Some(r!(v, Level));
            }
            SyntaxPlan::Max(imax, v) => {
                p.kind = Some(if *imax { Kind::IMax } else { Kind::Max });
                p.refs[0] = Some(r!(v[0], Level));
                p.refs[1] = Some(r!(v[1], Level));
            }
            SyntaxPlan::Param(v) => {
                p.kind = Some(Kind::Param);
                p.refs[0] = Some(r!(v, Name));
            }
            SyntaxPlan::Bvar(v) => {
                p.kind = Some(Kind::Bvar);
                p.component = Some(PendingComponent::Number(v.bytes()));
            }
            SyntaxPlan::Sort(v) => {
                p.kind = Some(Kind::Sort);
                p.refs[0] = Some(r!(v, Level));
            }
            SyntaxPlan::Constant(v) => {
                p.kind = Some(Kind::Constant);
                p.refs[0] = Some(r!(v.f_name, Name));
                let universes = resolved_levels(self, &v.f_us, b).map_err(|cause| Failure {
                    observed: empty(),
                    cause,
                })?;
                b.grow_vec(&mut s.universes, universes.len())
                    .map_err(resource)?;
                s.universes.extend_from_slice(&universes);
            }
            SyntaxPlan::App(v) => {
                p.kind = Some(Kind::App);
                p.refs[0] = Some(r!(v.f_fn, Expr));
                p.refs[1] = Some(r!(v.f_arg, Expr));
            }
            SyntaxPlan::Binder(pi, v) => {
                p.kind = Some(if *pi { Kind::Pi } else { Kind::Lambda });
                p.refs[0] = Some(r!(v.f_name, Name));
                p.refs[1] = Some(r!(v.f_type, Expr));
                p.refs[2] = Some(r!(v.f_body, Expr));
                p.component = Some(PendingComponent::Text(&v.f_binder_info));
            }
            SyntaxPlan::Let(v) => {
                p.kind = Some(Kind::Let);
                p.refs = [
                    Some(r!(v.f_name, Name)),
                    Some(r!(v.f_type, Expr)),
                    Some(r!(v.f_body, Expr)),
                    Some(r!(v.f_value, Expr)),
                ];
                p.component = Some(PendingComponent::Boolean(v.f_nondep));
            }
            SyntaxPlan::Projection(v) => {
                p.kind = Some(Kind::Projection);
                p.refs[0] = Some(r!(v.f_type_name, Name));
                p.refs[1] = Some(r!(v.f_struct, Expr));
                p.component = Some(PendingComponent::Number(v.f_idx.bytes()));
            }
            SyntaxPlan::NatVal(v) => {
                p.kind = Some(Kind::NatVal);
                p.component = Some(PendingComponent::Text(v));
            }
            SyntaxPlan::StrVal(v) => {
                p.kind = Some(Kind::StrVal);
                p.component = Some(PendingComponent::Text(v));
            }
            SyntaxPlan::Metadata(v) => {
                p.kind = Some(Kind::MData);
                p.refs[0] = Some(r!(v.f_expr, Expr));
                p.component = Some(PendingComponent::Text(v.f_data.get()));
            }
        }
        p.id = Some(id.bytes());
        p.id_number = id_number;
        self.publish(p, empty(), &s.universes, b)
    }
}

fn fallback_plan(input: &[u8]) -> Result<Plan<'_>, Cause> {
    let mut deserializer = serde_json::Deserializer::from_slice(input);
    let plan = PlanSeed
        .deserialize(&mut deserializer)
        .map_err(|_| Cause::Framing)?;
    deserializer.end().map_err(|_| Cause::Framing)?;
    Ok(plan)
}

fn with_selected_plan<T>(
    input: &[u8],
    mut found: impl FnMut(Plan<'_>) -> Result<T, Cause>,
) -> Result<T, Cause> {
    match fast::recognize_with(input, &mut found) {
        Some(result) => result,
        None => found(fallback_plan(input)?),
    }
}

// Derive receives a MapAccessDeserializer only: positional struct arrays are
// never an alternate wire representation, including nested group elements.
struct ObjectOnly<T>(T);
impl<T> std::ops::Deref for ObjectOnly<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}
impl<'de, T: Deserialize<'de>> Deserialize<'de> for ObjectOnly<T> {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        struct V<T>(PhantomData<T>);
        impl<'de, T: Deserialize<'de>> Visitor<'de> for V<T> {
            type Value = ObjectOnly<T>;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("object")
            }
            fn visit_map<M: MapAccess<'de>>(self, map: M) -> Result<Self::Value, M::Error> {
                T::deserialize(MapAccessDeserializer::new(map)).map(ObjectOnly)
            }
        }
        d.deserialize_map(V(PhantomData))
    }
}
impl Decoder {
    pub(super) fn typed_decode(
        &mut self,
        input: &[u8],
        s: &mut Scratch,
        b: &mut Budget,
    ) -> Result<Parsed, Failure> {
        if input.is_empty() || input.len() > crate::resource::RECORD_BYTES || !framed(input) {
            return Err(Failure {
                observed: empty(),
                cause: Cause::Framing,
            });
        }
        let reservation = reservation(input, b).map_err(resource)?;
        // typed_inner's root and its serde error are destroyed before the cold
        // pass. The conservative parser reservation remains live through both.
        let result = with_selected_plan(input, |plan| self.publish_plan(plan, s, b));
        let result = match result {
            Ok(value) => Ok(value),
            Err(Cause::Resource(e)) => Err(resource(e)),
            Err(cause) => Err(integrity::failure(input, Some(self), cause, b)),
        };
        let released = b.release(reservation).map_err(resource);
        released.and(result)
    }
}
fn reservation(input: &[u8], b: &mut Budget) -> Result<u64, ResourceError> {
    if input.is_empty() || input.len() > crate::resource::RECORD_BYTES {
        return Err(ResourceError::Invariant);
    }
    let n = (input.len() as u64)
        .checked_mul(256)
        .ok_or(ResourceError::Counter)?;
    b.reserve(n)?;
    Ok(n)
}
fn resolve_raw(d: &Decoder, table: Table, raw: &[u8], b: &mut Budget) -> Result<Resolved, Cause> {
    Nat(raw).valid()?;
    let index = match table {
        Table::Name => &d.name_ids,
        Table::Level => &d.level_ids,
        Table::Expr => &d.expression_ids,
    };
    let slot = index
        .resolve(raw, b)
        .map_err(index_error)?
        .ok_or(Cause::InvalidRecord)?;
    let slot = if matches!(table, Table::Name) {
        d.imported_name_slot(slot).map_err(Cause::Resource)?
    } else {
        slot
    };
    Ok(Resolved { table, slot })
}
fn resolved_names(d: &Decoder, refs: &Refs<'_>, b: &mut Budget) -> Result<Vec<NameId>, Cause> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(refs.len())
        .map_err(|_| Cause::Resource(ResourceError::Allocation))?;
    refs.for_each(|raw| {
        let reference = resolve_raw(d, Table::Name, raw, b)?;
        values.push(
            d.names
                .resolve_slot(reference.slot, b)
                .map_err(Cause::Resource)?,
        );
        Ok(())
    })?;
    Ok(values)
}
fn resolved_levels(d: &Decoder, refs: &Refs<'_>, b: &mut Budget) -> Result<Vec<LevelId>, Cause> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(refs.len())
        .map_err(|_| Cause::Resource(ResourceError::Allocation))?;
    refs.for_each(|raw| {
        let reference = resolve_raw(d, Table::Level, raw, b)?;
        values.push(
            d.levels
                .resolve_slot(reference.slot, b)
                .map_err(Cause::Resource)?,
        );
        Ok(())
    })?;
    Ok(values)
}
fn name(d: &Decoder, r: &Ref<'_>, b: &mut Budget) -> Result<NameId, Cause> {
    d.names.resolve_slot(r.slot()?, b).map_err(Cause::Resource)
}
fn expr(d: &Decoder, r: &Ref<'_>, b: &mut Budget) -> Result<ExprId, Cause> {
    d.expressions
        .resolve_slot(r.slot()?, b)
        .map_err(Cause::Resource)
}
fn numeric(n: &Nat<'_>) -> Result<u32, Cause> {
    n.bytes()
        .iter()
        .try_fold(0u32, |x, c| {
            x.checked_mul(10)?.checked_add(u32::from(*c - b'0'))
        })
        .ok_or(Cause::NumericRange)
}
fn names(
    d: &Decoder,
    s: &mut inductives::Payload,
    rs: &[Ref<'_>],
    b: &mut Budget,
) -> Result<inductives::Span, Cause> {
    let start = u32::try_from(s.names.len()).map_err(|_| Cause::NumericRange)?;
    let len = u32::try_from(rs.len()).map_err(|_| Cause::NumericRange)?;
    let needed = s
        .names
        .len()
        .checked_add(rs.len())
        .ok_or(Cause::Resource(ResourceError::Counter))?;
    b.grow_vec(&mut s.names, needed).map_err(Cause::Resource)?;
    for r in rs {
        let value = name(d, r, b)?;
        s.names.push(value);
    }
    Ok(inductives::Span { start, len })
}
fn group(
    d: &Decoder,
    s: &mut inductives::Payload,
    v: &InductiveGroup<'_>,
    b: &mut Budget,
) -> Result<(), Cause> {
    b.grow_vec(&mut s.types, v.f_types.len())
        .map_err(Cause::Resource)?;
    b.grow_vec(&mut s.constructors, v.f_ctors.len())
        .map_err(Cause::Resource)?;
    b.grow_vec(&mut s.recursors, v.f_recs.len())
        .map_err(Cause::Resource)?;
    for t in &v.f_types {
        let row = inductives::Inductive {
            name: name(d, &t.f_name, b)?,
            parameters: names(d, s, &t.f_level_params, b)?,
            ty: expr(d, &t.f_type, b)?,
            num_params: numeric(&t.f_num_params)?,
            num_indices: numeric(&t.f_num_indices)?,
            all: names(d, s, &t.f_all, b)?,
            constructors: names(d, s, &t.f_ctors, b)?,
            num_nested: numeric(&t.f_num_nested)?,
            is_recursive: t.f_is_rec,
            is_unsafe: t.f_is_unsafe,
            is_reflexive: t.f_is_reflexive,
        };
        s.types.push(row);
    }
    for t in &v.f_ctors {
        let row = inductives::Constructor {
            name: name(d, &t.f_name, b)?,
            parameters: names(d, s, &t.f_level_params, b)?,
            ty: expr(d, &t.f_type, b)?,
            inductive: name(d, &t.f_induct, b)?,
            index: numeric(&t.f_cidx)?,
            num_params: numeric(&t.f_num_params)?,
            num_fields: numeric(&t.f_num_fields)?,
            is_unsafe: t.f_is_unsafe,
        };
        s.constructors.push(row);
    }
    for t in &v.f_recs {
        let start = u32::try_from(s.rules.len()).map_err(|_| Cause::NumericRange)?;
        let len = u32::try_from(t.f_rules.len()).map_err(|_| Cause::NumericRange)?;
        let needed = s
            .rules
            .len()
            .checked_add(t.f_rules.len())
            .ok_or(Cause::Resource(ResourceError::Counter))?;
        b.grow_vec(&mut s.rules, needed).map_err(Cause::Resource)?;
        for r in &t.f_rules {
            let row = inductives::Rule {
                constructor: name(d, &r.f_ctor, b)?,
                num_fields: numeric(&r.f_nfields)?,
                rhs: expr(d, &r.f_rhs, b)?,
            };
            s.rules.push(row);
        }
        let row = inductives::Recursor {
            name: name(d, &t.f_name, b)?,
            parameters: names(d, s, &t.f_level_params, b)?,
            ty: expr(d, &t.f_type, b)?,
            all: names(d, s, &t.f_all, b)?,
            num_params: numeric(&t.f_num_params)?,
            num_indices: numeric(&t.f_num_indices)?,
            num_motives: numeric(&t.f_num_motives)?,
            num_minors: numeric(&t.f_num_minors)?,
            rules: inductives::Span { start, len },
            k: t.f_k,
            is_unsafe: t.f_is_unsafe,
        };
        s.recursors.push(row);
    }
    Ok(())
}

pub(super) fn header(
    input: &[u8],
    b: &mut Budget,
) -> Result<crate::decode::export_header::Header, crate::decode::export_header::Failure> {
    use crate::decode::export_header as h;
    let blank = Findings::default();
    if input.is_empty() || input.len() > crate::resource::RECORD_BYTES || !framed(input) {
        return Err(h::Failure {
            observed: blank,
            cause: h::Cause::Framing,
        });
    }
    let reserved = reservation(input, b).map_err(|e| h::Failure {
        observed: blank,
        cause: h::Cause::Resource(e),
    })?;
    let parse = (|| {
        let mut deserializer = serde_json::Deserializer::from_slice(input);
        let plan = PlanSeed
            .deserialize(&mut deserializer)
            .map_err(|_| Cause::Framing)?;
        deserializer.end().map_err(|_| Cause::Framing)?;
        let Plan::Header(meta) = plan else {
            return Err(Cause::Metadata);
        };
        let fields = [
            meta.f_exporter.f_name.as_bytes(),
            meta.f_exporter.f_version.as_bytes(),
            meta.f_lean.f_githash.as_bytes(),
            meta.f_lean.f_version.as_bytes(),
            meta.f_format.f_version.as_bytes(),
        ];
        h::Header::from_values(fields, b).map_err(|e| match e {
            h::Cause::Resource(e) => Cause::Resource(e),
            h::Cause::UnsupportedFormat => Cause::Unsupported(Unsupported::Field),
            _ => Cause::Metadata,
        })
    })();
    let result = match parse {
        Ok(header) => Ok(header),
        Err(Cause::Resource(e)) => Err(h::Failure {
            observed: blank,
            cause: h::Cause::Resource(e),
        }),
        Err(cause) => {
            let f = integrity::failure(input, None, cause, b);
            let cause = match f.cause {
                Cause::Framing => h::Cause::Framing,
                Cause::Resource(e) => h::Cause::Resource(e),
                Cause::Unsupported(_)
                    if f.observed.shape.extension || f.observed.shape.unknown_record =>
                {
                    h::Cause::UnsupportedField
                }
                Cause::Unsupported(_) => h::Cause::UnsupportedFormat,
                _ => h::Cause::Metadata,
            };
            Err(h::Failure {
                observed: f.observed.shape,
                cause,
            })
        }
    };
    b.release(reserved).map_err(|e| h::Failure {
        observed: blank,
        cause: h::Cause::Resource(e),
    })?;
    result
}

// Physical-record outer padding remains space/tab only. Serde owns all JSON
// tokenization, escapes and grammar inside these record framing boundaries.
fn framed(input: &[u8]) -> bool {
    let first = input.iter().find(|c| !matches!(c, b' ' | b'\t'));
    let last = input.iter().rfind(|c| !matches!(c, b' ' | b'\t'));
    first == Some(&b'{') && last == Some(&b'}')
}
