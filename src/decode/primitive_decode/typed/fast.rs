//! Side-effect-free recognition of lean4export's canonical record layouts.
//!
//! The cursor is bounded by the logical record slice supplied by framing. Every
//! successful recognizer consumes that slice exactly; no separator, padding,
//! stale buffer byte, or following record can complete a match.

use super::*;

struct Cursor<'a> {
    // Always a suffix of the exact logical record. No byte outside that record
    // may satisfy a token; successful finish requires an empty suffix.
    remaining: &'a [u8],
}

impl<'a> Cursor<'a> {
    #[inline(always)]
    fn new(input: &'a [u8]) -> Self {
        Self { remaining: input }
    }

    #[inline(always)]
    fn literal(&mut self, expected: &[u8]) -> Option<()> {
        let (prefix, tail) = self.remaining.split_at_checked(expected.len())?;
        if prefix != expected {
            return None;
        }
        // Alternative literals may be tried after failure: only a complete
        // match commits the cursor advance.
        self.remaining = tail;
        Some(())
    }

    #[inline(always)]
    fn byte(&self) -> Option<u8> {
        self.remaining.first().copied()
    }

    #[inline(always)]
    fn natural(&mut self) -> Option<Nat<'a>> {
        self.natural_with_value().map(|(raw, _)| raw)
    }

    #[inline(always)]
    fn natural_with_value(&mut self) -> Option<(Nat<'a>, u32)> {
        let input = self.remaining;
        let mut at = 0;
        let value = if let Some(bytes) = input.get(..8) {
            let word = u64::from_le_bytes(bytes.try_into().ok()?);
            let (head, digits) = digits8(word);
            // digits8 validates the first byte as part of the exact prefix.
            // Empty prefixes fail before constructing a Nat or moving the cursor.
            if digits == 0 || (digits > 1 && bytes[0] == b'0') {
                return None;
            }
            at = digits;
            let mut value = u32::try_from(head).ok()?;
            if digits == 8 && input.get(at).is_some_and(u8::is_ascii_digit) {
                for _ in 0..2 {
                    let Some(byte) = input.get(at).copied() else {
                        break;
                    };
                    if !byte.is_ascii_digit() {
                        break;
                    }
                    value = value.checked_mul(10)?.checked_add(u32::from(byte - b'0'))?;
                    at += 1;
                }
                if input.get(at).is_some_and(u8::is_ascii_digit) {
                    return None;
                }
            }
            value
        } else {
            let mut value = 0_u32;
            while let Some(byte) = input.get(at).copied() {
                if !byte.is_ascii_digit() {
                    break;
                }
                value = value.checked_mul(10)?.checked_add(u32::from(byte - b'0'))?;
                at += 1;
            }
            if at == 0 || (at > 1 && input[0] == b'0') {
                return None;
            }
            value
        };
        let (raw, tail) = input.split_at_checked(at)?;
        self.remaining = tail;
        Some((Nat(raw), value))
    }

    #[inline(always)]
    fn reference(&mut self) -> Option<Ref<'a>> {
        let (raw, number) = self.natural_with_value()?;
        Some(Ref {
            raw,
            slot: Cell::new(RefState::Parsed(number)),
        })
    }

    #[inline(always)]
    fn boolean(&mut self) -> Option<bool> {
        match self.byte()? {
            b't' => self.literal(b"true").map(|()| true),
            b'f' => self.literal(b"false").map(|()| false),
            _ => None,
        }
    }

    /// An unescaped JSON string body, bounded by the logical record. Controls
    /// and escapes fall back; the complete body must be UTF-8.
    fn string(&mut self) -> Option<&'a str> {
        let input = self.remaining;
        let mut at = 0_usize;
        loop {
            if let Some(bytes) = input.get(at..at.checked_add(8)?) {
                let word = u64::from_le_bytes(bytes.try_into().ok()?);
                if has_byte(word, b'"')
                    | has_byte(word, b'\\')
                    | has_less(word, 0x20)
                    | (word & 0x8080_8080_8080_8080)
                    == 0
                {
                    at += 8;
                    continue;
                }
            }
            match input.get(at).copied()? {
                b'"' => {
                    let (body, tail) = input.split_at_checked(at)?;
                    let text = std::str::from_utf8(body).ok()?;
                    self.remaining = tail.get(1..)?;
                    return Some(text);
                }
                b'\\' | 0..=0x1f => return None,
                _ => at += 1,
            }
        }
    }

    /// The validated list span is borrowed from this record; publication still
    /// allocates/resolves it once through the common plan.
    fn references(&mut self) -> Option<Refs<'a>> {
        let input = self.remaining;
        self.literal(b"[")?;
        let mut count = 0_usize;
        if self.byte()? != b']' {
            loop {
                self.natural()?;
                count = count.checked_add(1)?;
                match self.byte()? {
                    b',' => self.remaining = self.remaining.get(1..)?,
                    b']' => break,
                    _ => return None,
                }
            }
        }
        self.literal(b"]")?;
        // remaining is a suffix obtained only by checked splits above.
        let consumed = input.len().checked_sub(self.remaining.len())?;
        Some(Refs::Canonical {
            bytes: input.get(..consumed)?,
            count,
        })
    }

    #[inline(always)]
    fn finish<T, R>(&self, value: T, found: impl FnOnce(T) -> R) -> Option<R> {
        self.remaining.is_empty().then(|| found(value))
    }
}

/// Leading decimal digits of a little-endian word, converted eight at a time.
/// This is Lemire's multiply-shift SWAR conversion in safe integer operations.
#[inline(always)]
fn digits8(word: u64) -> (u64, usize) {
    let digits = word ^ 0x3030_3030_3030_3030;
    let non_digit = (digits | digits.wrapping_add(0x0606_0606_0606_0606)) & 0xf0f0_f0f0_f0f0_f0f0;
    let count = (non_digit.trailing_zeros() >> 3) as usize;
    let mut value =
        digits.wrapping_shl((64 - 8 * count) as u32) & ((count != 0) as u64).wrapping_neg();
    value = value.wrapping_mul(2561) >> 8;
    value = (value & 0x00ff_00ff_00ff_00ff).wrapping_mul(6_553_601) >> 16;
    value = (value & 0x0000_ffff_0000_ffff).wrapping_mul(42_949_672_960_001) >> 32;
    (value, count)
}

#[inline(always)]
fn has_byte(word: u64, byte: u8) -> u64 {
    has_less(word ^ (0x0101_0101_0101_0101 * u64::from(byte)), 1)
}

#[inline(always)]
fn has_less(word: u64, value: u8) -> u64 {
    word.wrapping_sub(0x0101_0101_0101_0101 * u64::from(value)) & !word & 0x8080_8080_8080_8080
}

fn object<T>(fields: T) -> ObjectOnly<T> {
    ObjectOnly(fields)
}

#[inline(always)]
fn app<'a, R>(input: &'a [u8], found: impl FnOnce(Plan<'a>) -> R) -> Option<R> {
    let mut c = Cursor::new(input);
    c.literal(b"{\"app\":{\"arg\":")?;
    let arg = c.reference()?;
    c.literal(b",\"fn\":")?;
    let function = c.reference()?;
    c.literal(b"},\"ie\":")?;
    let (id, id_number) = c.natural_with_value()?;
    c.literal(b"}")?;
    c.finish(
        Plan::Syntax {
            id,
            id_number: Some(id_number),
            payload: SyntaxPlan::App(object(AppFields {
                f_fn: function,
                f_arg: arg,
            })),
        },
        found,
    )
}

#[inline(always)]
fn pi<'a, R>(input: &'a [u8], found: impl FnOnce(Plan<'a>) -> R) -> Option<R> {
    let mut c = Cursor::new(input);
    c.literal(b"{\"forallE\":{\"binderInfo\":\"")?;
    let binder_info = c.string()?;
    if !matches!(
        binder_info,
        "default" | "implicit" | "strictImplicit" | "instImplicit"
    ) {
        return None;
    }
    c.literal(b",\"body\":")?;
    let body = c.reference()?;
    c.literal(b",\"name\":")?;
    let name = c.reference()?;
    c.literal(b",\"type\":")?;
    let ty = c.reference()?;
    c.literal(b"},\"ie\":")?;
    let (id, id_number) = c.natural_with_value()?;
    c.literal(b"}")?;
    c.finish(
        Plan::Syntax {
            id,
            id_number: Some(id_number),
            payload: SyntaxPlan::Binder(
                true,
                object(BinderFields {
                    f_name: name,
                    f_type: ty,
                    f_body: body,
                    f_binder_info: Cow::Borrowed(binder_info),
                }),
            ),
        },
        found,
    )
}

#[inline(always)]
fn bvar<'a, R>(input: &'a [u8], found: impl FnOnce(Plan<'a>) -> R) -> Option<R> {
    let mut c = Cursor::new(input);
    c.literal(b"{\"bvar\":")?;
    let index = c.natural()?;
    c.literal(b",\"ie\":")?;
    let (id, id_number) = c.natural_with_value()?;
    c.literal(b"}")?;
    c.finish(
        Plan::Syntax {
            id,
            id_number: Some(id_number),
            payload: SyntaxPlan::Bvar(index),
        },
        found,
    )
}

#[inline(always)]
fn level<'a, R>(input: &'a [u8], found: impl FnOnce(Plan<'a>) -> R) -> Option<R> {
    let mut c = Cursor::new(input);
    c.literal(b"{\"il\":")?;
    let (id, id_number) = c.natural_with_value()?;
    let payload = if c.literal(b",\"succ\":").is_some() {
        SyntaxPlan::Succ(c.reference()?)
    } else if c.literal(b",\"param\":").is_some() {
        SyntaxPlan::Param(c.reference()?)
    } else {
        let imax = if c.literal(b",\"imax\":[").is_some() {
            true
        } else {
            c.literal(b",\"max\":[")?;
            false
        };
        let first = c.reference()?;
        c.literal(b",")?;
        let second = c.reference()?;
        c.literal(b"]")?;
        SyntaxPlan::Max(imax, [first, second])
    };
    c.literal(b"}")?;
    c.finish(
        Plan::Syntax {
            id,
            id_number: Some(id_number),
            payload,
        },
        found,
    )
}

#[inline(always)]
fn expression_id_first<'a, R>(input: &'a [u8], found: impl FnOnce(Plan<'a>) -> R) -> Option<R> {
    let mut c = Cursor::new(input);
    c.literal(b"{\"ie\":")?;
    let (id, id_number) = c.natural_with_value()?;
    c.literal(b",\"")?;
    let payload = if c.literal(b"sort\":").is_some() {
        SyntaxPlan::Sort(c.reference()?)
    } else if c.literal(b"lam\":{\"binderInfo\":\"").is_some() {
        let binder_info = c.string()?;
        if !matches!(
            binder_info,
            "default" | "implicit" | "strictImplicit" | "instImplicit"
        ) {
            return None;
        }
        c.literal(b",\"body\":")?;
        let body = c.reference()?;
        c.literal(b",\"name\":")?;
        let name = c.reference()?;
        c.literal(b",\"type\":")?;
        let ty = c.reference()?;
        c.literal(b"}")?;
        SyntaxPlan::Binder(
            false,
            object(BinderFields {
                f_name: name,
                f_type: ty,
                f_body: body,
                f_binder_info: Cow::Borrowed(binder_info),
            }),
        )
    } else if c.literal(b"letE\":{\"body\":").is_some() {
        let body = c.reference()?;
        c.literal(b",\"name\":")?;
        let name = c.reference()?;
        c.literal(b",\"nondep\":")?;
        let nondep = c.boolean()?;
        c.literal(b",\"type\":")?;
        let ty = c.reference()?;
        c.literal(b",\"value\":")?;
        let value = c.reference()?;
        c.literal(b"}")?;
        SyntaxPlan::Let(object(LetFields {
            f_name: name,
            f_type: ty,
            f_value: value,
            f_body: body,
            f_nondep: nondep,
        }))
    } else if c.literal(b"proj\":{\"idx\":").is_some() {
        let index = c.natural()?;
        c.literal(b",\"struct\":")?;
        let structure = c.reference()?;
        c.literal(b",\"typeName\":")?;
        let type_name = c.reference()?;
        c.literal(b"}")?;
        SyntaxPlan::Projection(object(ProjectionFields {
            f_type_name: type_name,
            f_idx: index,
            f_struct: structure,
        }))
    } else {
        let natural = if c.literal(b"natVal\":\"").is_some() {
            true
        } else {
            c.literal(b"strVal\":\"")?;
            false
        };
        let text = c.string()?;
        if natural && (text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit())) {
            return None;
        }
        if natural {
            SyntaxPlan::NatVal(Cow::Borrowed(text))
        } else {
            SyntaxPlan::StrVal(Cow::Borrowed(text))
        }
    };
    c.literal(b"}")?;
    c.finish(
        Plan::Syntax {
            id,
            id_number: Some(id_number),
            payload,
        },
        found,
    )
}

#[inline(always)]
fn name<'a, R>(input: &'a [u8], found: impl FnOnce(Plan<'a>) -> R) -> Option<R> {
    let mut c = Cursor::new(input);
    c.literal(b"{\"in\":")?;
    let (id, id_number) = c.natural_with_value()?;
    let payload = if c.literal(b",\"str\":{\"pre\":").is_some() {
        let prefix = c.reference()?;
        c.literal(b",\"str\":\"")?;
        let text = c.string()?;
        c.literal(b"}")?;
        SyntaxPlan::NameStr(object(NameStrFields {
            f_pre: prefix,
            f_str: Cow::Borrowed(text),
        }))
    } else {
        c.literal(b",\"num\":{\"i\":")?;
        let component = c.natural()?;
        c.literal(b",\"pre\":")?;
        let prefix = c.reference()?;
        c.literal(b"}")?;
        SyntaxPlan::NameNum(object(NameNumFields {
            f_pre: prefix,
            f_i: component,
        }))
    };
    c.literal(b"}")?;
    c.finish(
        Plan::Syntax {
            id,
            id_number: Some(id_number),
            payload,
        },
        found,
    )
}

#[inline(always)]
fn constant<'a, R>(input: &'a [u8], found: impl FnOnce(Plan<'a>) -> R) -> Option<R> {
    let mut c = Cursor::new(input);
    c.literal(b"{\"const\":{\"name\":")?;
    let name = c.reference()?;
    c.literal(b",\"us\":")?;
    let universes = c.references()?;
    c.literal(b"},\"ie\":")?;
    let (id, id_number) = c.natural_with_value()?;
    c.literal(b"}")?;
    c.finish(
        Plan::Syntax {
            id,
            id_number: Some(id_number),
            payload: SyntaxPlan::Constant(object(ConstantFields {
                f_name: name,
                f_us: universes,
            })),
        },
        found,
    )
}

#[inline(always)]
fn theorem<'a, R>(input: &'a [u8], found: impl FnOnce(Plan<'a>) -> R) -> Option<R> {
    let mut c = Cursor::new(input);
    c.literal(b"{\"thm\":{\"all\":")?;
    let all = c.references()?;
    c.literal(b",\"levelParams\":")?;
    let parameters = c.references()?;
    c.literal(b",\"name\":")?;
    let name = c.reference()?;
    c.literal(b",\"type\":")?;
    let ty = c.reference()?;
    c.literal(b",\"value\":")?;
    let value = c.reference()?;
    c.literal(b"}}")?;
    c.finish(
        Plan::Theorem(object(TheoremFields {
            f_name: name,
            f_level_params: parameters,
            f_type: ty,
            f_value: value,
            f_all: all,
        })),
        found,
    )
}

#[inline(always)]
fn definition<'a, R>(input: &'a [u8], found: impl FnOnce(Plan<'a>) -> R) -> Option<R> {
    let mut c = Cursor::new(input);
    c.literal(b"{\"def\":{\"all\":")?;
    let all = c.references()?;
    c.literal(b",\"hints\":")?;
    let hint = if c.literal(b"{\"regular\":").is_some() {
        let regular = c.natural()?;
        c.literal(b"}")?;
        Hint::Regular(object(RegularHintFields { f_regular: regular }))
    } else if c.literal(b"\"opaque\"").is_some() {
        Hint::String(Cow::Borrowed("opaque"))
    } else {
        c.literal(b"\"abbrev\"")?;
        Hint::String(Cow::Borrowed("abbrev"))
    };
    c.literal(b",\"levelParams\":")?;
    let parameters = c.references()?;
    c.literal(b",\"name\":")?;
    let name = c.reference()?;
    c.literal(b",\"safety\":\"")?;
    let safety = c.string()?;
    if !matches!(safety, "safe" | "unsafe" | "partial") {
        return None;
    }
    c.literal(b",\"type\":")?;
    let ty = c.reference()?;
    c.literal(b",\"value\":")?;
    let value = c.reference()?;
    c.literal(b"}}")?;
    c.finish(
        Plan::Definition(object(DefinitionFields {
            f_name: name,
            f_level_params: parameters,
            f_type: ty,
            f_value: value,
            f_hints: hint,
            f_safety: Cow::Borrowed(safety),
            f_all: all,
        })),
        found,
    )
}

#[inline(always)]
fn opaque<'a, R>(input: &'a [u8], found: impl FnOnce(Plan<'a>) -> R) -> Option<R> {
    let mut c = Cursor::new(input);
    c.literal(b"{\"opaque\":{\"all\":")?;
    let all = c.references()?;
    c.literal(b",\"isUnsafe\":")?;
    let is_unsafe = c.boolean()?;
    c.literal(b",\"levelParams\":")?;
    let parameters = c.references()?;
    c.literal(b",\"name\":")?;
    let name = c.reference()?;
    c.literal(b",\"type\":")?;
    let ty = c.reference()?;
    c.literal(b",\"value\":")?;
    let value = c.reference()?;
    c.literal(b"}}")?;
    c.finish(
        Plan::Opaque(object(OpaqueFields {
            f_name: name,
            f_level_params: parameters,
            f_type: ty,
            f_value: value,
            f_is_unsafe: is_unsafe,
            f_all: all,
        })),
        found,
    )
}

#[inline(always)]
pub(super) fn recognize_with<'a, R>(
    input: &'a [u8],
    found: impl FnOnce(Plan<'a>) -> R,
) -> Option<R> {
    match (input.get(2), input.get(3)) {
        (Some(b'a'), _) => app(input, found),
        (Some(b'f'), _) => pi(input, found),
        (Some(b'b'), _) => bvar(input, found),
        (Some(b'i'), Some(b'l')) => level(input, found),
        (Some(b'i'), Some(b'e')) => expression_id_first(input, found),
        (Some(b'i'), Some(b'n')) => name(input, found),
        (Some(b'c'), _) => constant(input, found),
        (Some(b't'), _) => theorem(input, found),
        (Some(b'd'), _) => definition(input, found),
        (Some(b'o'), _) => opaque(input, found),
        _ => None,
    }
}
