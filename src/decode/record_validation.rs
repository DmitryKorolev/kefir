//! Structural observations; never semantic authority.
use crate::decode::record_schema::Object;
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Findings {
    pub duplicate: bool,
    pub field: bool,
    pub extension: bool,
    pub unknown_record: bool,
}
// The root vocabulary is fixed by record_schema, not by input order. Classify
// its known tag using its spelling, avoiding coupling table IDs to enum ordinals.
pub(crate) fn root_fields(seen: u64, extension: bool) -> (bool, bool) {
    let fields = Object::Root.fields();
    let mut tags = 0;
    let mut expected_id: Option<&[u8]> = None;
    let mut ids = 0;
    let mut actual_id: Option<&[u8]> = None;
    let mut remaining = seen;
    while remaining != 0 {
        let bit = remaining.trailing_zeros() as usize;
        remaining &= remaining - 1;
        // Invariant: seen bits arise only from this root's fixed vocabulary.
        let field = &fields[bit];
        match field.name {
            b"in" | b"il" | b"ie" => {
                ids += 1;
                actual_id = Some(field.name);
            }
            tag => {
                tags += 1;
                expected_id = match tag {
                    b"str" | b"num" => Some(b"in"),
                    b"succ" | b"max" | b"imax" | b"param" => Some(b"il"),
                    b"bvar" | b"sort" | b"const" | b"app" | b"lam" | b"forallE" | b"letE"
                    | b"proj" | b"natVal" | b"strVal" | b"mdata" => Some(b"ie"),
                    _ => None,
                };
            }
        }
    }
    // With no known tag, unknown extension classification belongs to the caller.
    // Its opaque payload cannot be assigned a known tag's identifier requirement.
    if tags == 0 {
        return (extension, extension);
    }
    (tags == 1 && ids <= 1 && actual_id == expected_id, false)
}
