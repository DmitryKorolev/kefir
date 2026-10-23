//! Cold integrity traversal after typed deserialization fails. Serde retains
//! numeric tokens as borrowed RawValue slices; no f64 conversion or lexical parser.
//! All nested slices share the original depth counter. Rescanning work is charged
//! for each slice before parsing it. No syntax or declaration is published here.
use super::*;
use crate::decode::record_schema::{Object, Shape};
use serde::de::SeqAccess;
use std::collections::HashSet;

struct State<'a> {
    observed: CheckedShape,
    decoder: Option<&'a Decoder>,
    interrupted: Option<Cause>,
    metadata: bool,
    duplicate_id: bool,
}
pub(super) fn failure(
    input: &[u8],
    decoder: Option<&mut Decoder>,
    initial: Cause,
    b: &mut Budget,
) -> Failure {
    let mut state = State {
        observed: empty(),
        decoder: decoder.as_deref(),
        interrupted: None,
        metadata: false,
        duplicate_id: false,
    };
    let scan = walk(input, Some(Shape::Object(Object::Root)), 0, &mut state, b);
    let cause = match scan {
        Err(c) => c,
        Ok(()) if state.metadata && state.decoder.is_some() => Cause::Metadata,
        Ok(())
            if state.observed.shape.field
                || state.observed.shape.duplicate
                || state.observed.missing_reference =>
        {
            Cause::InvalidRecord
        }
        Ok(()) if state.duplicate_id => Cause::DuplicateId,
        Ok(()) if state.observed.shape.unknown_record => {
            Cause::Unsupported(Unsupported::Record(DeclarationKind::Unknown))
        }
        Ok(()) if state.observed.shape.extension => Cause::Unsupported(Unsupported::Field),
        Ok(()) => initial,
    };
    let observed = state.observed;
    let metadata = state.metadata;
    if let Some(d) = decoder {
        d.metadata_seen = metadata;
    }
    Failure { observed, cause }
}
/// Hot-path validation of a metadata `data` payload: it must be a JSON object
/// obeying the same duplicate-key, Unicode, depth and resource rules as any
/// other object. The cold pass only runs on failure, so the success path
/// needs this gate before a payload may be preserved. Publishes nothing.
pub(super) fn validate_payload(input: &[u8], b: &mut Budget) -> Result<(), Cause> {
    let mut state = State {
        observed: empty(),
        decoder: None,
        interrupted: None,
        metadata: false,
        duplicate_id: false,
    };
    walk(input, Some(Shape::JsonObject), 0, &mut state, b)?;
    if state.observed.shape.duplicate || state.observed.shape.field {
        return Err(Cause::InvalidRecord);
    }
    match input.first().copied() {
        Some(b'{') => Ok(()),
        _ => Err(Cause::Resource(ResourceError::Invariant)),
    }
}
fn walk(
    input: &[u8],
    shape: Option<Shape>,
    depth: usize,
    s: &mut State<'_>,
    b: &mut Budget,
) -> Result<(), Cause> {
    b.charge_work(input.len() as u64 + 1)
        .map_err(Cause::Resource)?;
    std::str::from_utf8(input).map_err(|_| Cause::Framing)?;
    let raw: &RawValue = serde_json::from_slice(input).map_err(|_| Cause::Framing)?;
    let bytes = raw.get().as_bytes();
    match bytes.first().copied() {
        Some(b'{') | Some(b'[') => {
            if depth + 1 >= crate::resource::JSON_DEPTH as usize {
                return Err(Cause::Framing);
            }
            let object = bytes[0] == b'{';
            let (schema, element, pair) = match (object, shape) {
                (true, Some(Shape::Object(o))) => (Some(o), None, false),
                (true, Some(Shape::Hint)) => (Some(Object::RegularHint), None, false),
                (true, Some(Shape::JsonObject)) | (true, None) => (None, None, false),
                (false, Some(Shape::List(t))) => (None, Some(Shape::Reference(t)), false),
                (false, Some(Shape::Pair(t))) => (None, Some(Shape::Reference(t)), true),
                (false, Some(Shape::Objects(o))) => (None, Some(Shape::Object(o)), false),
                (false, None) => (None, None, false),
                _ => {
                    s.observed.shape.field = true;
                    (None, None, false)
                }
            };
            let mut d = serde_json::Deserializer::from_slice(bytes);
            let visitor = Container {
                state: s,
                budget: b,
                depth: depth + 1,
                schema,
                element,
                pair,
            };
            let result = if object {
                serde::Deserializer::deserialize_map(&mut d, visitor)
            } else {
                serde::Deserializer::deserialize_seq(&mut d, visitor)
            };
            if result.is_err() {
                return Err(s.interrupted.take().unwrap_or(Cause::Framing));
            }
            d.end().map_err(|_| Cause::Framing)?;
        }
        _ => {
            // RawValue checks JSON token boundaries but does not decode escaped
            // strings. Validate Unicode even for unknown or wrongly typed scalars.
            let decoded = if bytes.first() == Some(&b'"') {
                Some(serde_json::from_slice::<Cow<'_, str>>(bytes).map_err(|_| Cause::Framing)?)
            } else {
                None
            };
            let valid = match shape {
                None => true,
                Some(Shape::Natural | Shape::Reference(_)) => {
                    !bytes.is_empty() && bytes.iter().all(u8::is_ascii_digit)
                }
                Some(Shape::Boolean) => matches!(bytes, b"true" | b"false"),
                Some(
                    Shape::String
                    | Shape::NaturalString
                    | Shape::BinderInfo
                    | Shape::Safety
                    | Shape::QuotKind
                    | Shape::Hint,
                ) => {
                    if let Some(text) = decoded.as_ref() {
                        match shape {
                            Some(Shape::NaturalString) => {
                                !text.is_empty() && text.as_bytes().iter().all(u8::is_ascii_digit)
                            }
                            Some(Shape::BinderInfo) => matches!(
                                text.as_ref(),
                                "default" | "implicit" | "strictImplicit" | "instImplicit"
                            ),
                            Some(Shape::Safety) => {
                                matches!(text.as_ref(), "safe" | "unsafe" | "partial")
                            }
                            Some(Shape::QuotKind) => {
                                matches!(text.as_ref(), "type" | "ctor" | "lift" | "ind")
                            }
                            Some(Shape::Hint) => matches!(text.as_ref(), "opaque" | "abbrev"),
                            _ => true,
                        }
                    } else {
                        false
                    }
                }
                _ => false,
            };
            if !valid {
                s.observed.shape.field = true;
            }
            if valid
                && let Some(Shape::Reference(table)) = shape
                && let Some(d) = s.decoder
            {
                let index = match table {
                    Table::Name => &d.name_ids,
                    Table::Level => &d.level_ids,
                    Table::Expr => &d.expression_ids,
                };
                if index.resolve(bytes, b).map_err(index_error)?.is_none() {
                    s.observed.missing_reference = true;
                }
            }
        }
    }
    Ok(())
}
struct Container<'a, 'b> {
    state: &'a mut State<'b>,
    budget: &'a mut Budget,
    depth: usize,
    schema: Option<Object>,
    element: Option<Shape>,
    pair: bool,
}
impl<'de> Visitor<'de> for Container<'_, '_> {
    type Value = ();
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("JSON container")
    }
    fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<(), M::Error> {
        // Query-local decoded-key set; live key bytes/entries belong to disjoint
        // input prefixes across parents. 256N covers replacement overlap and
        // serde scratch. It drops before the enclosing reservation is released.
        // Cow entries cost24 bytes plus table controls. Even old/new bucket
        // overlap at7/8 occupancy costs <112 bytes/key (<=28N at the minimum
        // four-byte member prefix); key clones and parser/string scratch fit
        // another12N. Tiny minimum-capacity objects still fit256N. Parent key
        // prefixes are disjoint; no typed root or first error overlaps this pass.
        let mut keys = HashSet::<Cow<'de, str>>::new();
        let mut seen = 0u64;
        let mut root_extension = false;
        let mut ids = [None; 3];
        while let Some(key) = map.next_key::<Cow<'de, str>>()? {
            self.budget.charge_work(key.len() as u64 + 1).map_err(|e| {
                self.state.interrupted = Some(Cause::Resource(e));
                serde::de::Error::custom("work budget")
            })?;
            if !keys.insert(key.clone()) {
                self.state.observed.shape.duplicate = true;
            }
            let shape = if let Some(schema) = self.schema {
                if schema == Object::Root && key == "meta" {
                    self.state.metadata = true;
                }
                if let Some((bit, shape)) = schema.field(key.as_bytes()) {
                    seen |= 1u64 << bit;
                    Some(shape)
                } else {
                    if schema.prohibited(key.as_bytes()) {
                        self.state.observed.shape.field = true;
                    } else {
                        self.state.observed.shape.extension = true;
                        root_extension = true;
                    }
                    None
                }
            } else {
                None
            };
            let value: &RawValue = map.next_value()?;
            if self.schema == Some(Object::Root) {
                match key.as_ref() {
                    "in" => ids[0] = Some(value),
                    "il" => ids[1] = Some(value),
                    "ie" => ids[2] = Some(value),
                    _ => (),
                }
            }
            if let Err(c) = walk(
                value.get().as_bytes(),
                shape,
                self.depth,
                self.state,
                self.budget,
            ) {
                self.state.interrupted = Some(c);
                return Err(serde::de::Error::custom("integrity traversal"));
            }
        }
        if let Some(schema) = self.schema {
            if let Some(required) = schema.required() {
                self.state.observed.shape.field |= seen != required;
            } else {
                let (valid, unknown) =
                    crate::decode::record_validation::root_fields(seen, root_extension);
                self.state.observed.shape.field |= !valid;
                self.state.observed.shape.unknown_record |= unknown;
                if valid
                    && !unknown
                    && let Some(d) = self.state.decoder
                {
                    for (raw, index) in
                        ids.into_iter()
                            .zip([&d.name_ids, &d.level_ids, &d.expression_ids])
                    {
                        if let Some(raw) = raw
                            && raw.get().as_bytes().iter().all(u8::is_ascii_digit)
                        {
                            match index.resolve(raw.get().as_bytes(), self.budget) {
                                Ok(Some(_)) => self.state.duplicate_id = true,
                                Ok(None) => (),
                                Err(e) => {
                                    self.state.interrupted = Some(index_error(e));
                                    return Err(serde::de::Error::custom("identifier lookup"));
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }
    fn visit_seq<M: SeqAccess<'de>>(self, mut seq: M) -> Result<(), M::Error> {
        let mut count = 0usize;
        while let Some(value) = seq.next_element::<&RawValue>()? {
            count += 1;
            if let Err(c) = walk(
                value.get().as_bytes(),
                self.element,
                self.depth,
                self.state,
                self.budget,
            ) {
                self.state.interrupted = Some(c);
                return Err(serde::de::Error::custom("integrity traversal"));
            }
        }
        if self.pair && count != 2 {
            self.state.observed.shape.field = true;
        }
        Ok(())
    }
}
