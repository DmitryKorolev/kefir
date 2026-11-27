//! Natural-literal representation and exact arithmetic helpers.

use super::*;

pub(super) fn parse_nat(bytes: &[u8], b: &mut Budget, reserved: &mut u64) -> R<NatLit> {
    let mut n: u64 = 0;
    for &d in bytes {
        match n
            .checked_mul(10)
            .and_then(|m| m.checked_add((d - b'0') as u64))
        {
            Some(m) => n = m,
            None => {
                // This is a retained payload, separate from source syntax or
                // Digits storage. `copied` requests max(len, 8); overflow of a
                // canonical u64 requires at least twenty digits. Reserve before
                // allocation and keep the charge through all admission failures.
                charge_bytes(b, reserved, bytes.len())?;
                return Ok(NatLit::Big(copied(bytes)?));
            }
        }
    }
    Ok(NatLit::Small(n))
}
/// NONE is the zero constructor; other IDs come only from nat_value_in.
/// The literal store is append-only throughout operand observation.
pub(super) fn nat_literal(nats: &[NatLit], id: u32) -> &NatLit {
    if id == NONE {
        &NatLit::Small(0)
    } else {
        &nats[id as usize]
    }
}
/// Fixed stack formatting for machine operands; large digits stay borrowed.
pub(super) enum NatDigits<'a> {
    Small { bytes: [u8; 20], start: usize },
    Big(&'a [u8]),
}
impl NatDigits<'_> {
    pub(super) fn as_bytes(&self) -> &[u8] {
        match self {
            Self::Small { bytes, start } => &bytes[*start..],
            Self::Big(bytes) => bytes,
        }
    }
}
pub(super) fn nat_digits(n: &NatLit) -> R<NatDigits<'_>> {
    Ok(match n {
        NatLit::Small(v) => {
            let mut bytes = [0u8; 20];
            let mut start = bytes.len();
            let mut v = *v;
            loop {
                start -= 1;
                bytes[start] = b'0' + (v % 10) as u8;
                v /= 10;
                if v == 0 {
                    break;
                }
            }
            NatDigits::Small { bytes, start }
        }
        NatLit::Big(bytes) => NatDigits::Big(bytes),
        NatLit::Computed(..) | NatLit::Evicted(_) => return Err(ResourceError::Invariant.into()),
    })
}

use crate::check::natural::BinaryNat;

pub(super) fn use_binary_operation(op: Operation, left: &NatLit, right: &NatLit) -> bool {
    let wide = |n: &NatLit| {
        matches!(n, NatLit::Computed(..)) || matches!(n, NatLit::Big(digits) if digits.len() > 600)
    };
    wide(left)
        || wide(right)
        || matches!((op, right), (Operation::Pow | Operation::ShiftLeft, NatLit::Small(n)) if *n > 2016)
}

fn binary_error(error: crate::check::natural::Error) -> KErr {
    match error {
        crate::check::natural::Error::Resource(e) => KErr::Resource(e),
        crate::check::natural::Error::Unsupported => KErr::LiteralArithmetic,
    }
}

fn binary_operand<'a>(
    n: &'a NatLit,
    budget: &mut Budget,
    scratch: &mut u64,
) -> R<std::borrow::Cow<'a, BinaryNat>> {
    use std::borrow::Cow;
    Ok(match n {
        NatLit::Small(x) => Cow::Owned(BinaryNat::small(*x)),
        NatLit::Evicted(_) => return Err(ResourceError::Invariant.into()),
        NatLit::Computed(x, _) => Cow::Borrowed(&x[0]),
        NatLit::Big(bytes) => Cow::Owned(
            crate::check::natural::parse_binary(bytes, budget, scratch).map_err(binary_error)?,
        ),
    })
}

fn with_binary_operands<T>(
    a: &NatLit,
    b: &NatLit,
    budget: &mut Budget,
    f: impl FnOnce(&BinaryNat, &BinaryNat, &mut Budget) -> R<T>,
) -> R<T> {
    let mut scratch = 0;
    let result = (|| {
        let a = binary_operand(a, budget, &mut scratch)?;
        let b = binary_operand(b, budget, &mut scratch)?;
        f(&a, &b, budget)
    })();
    budget.release(scratch)?;
    result
}

pub(super) fn computed_nat(
    op: Operation,
    a: &NatLit,
    b: &NatLit,
    budget: &mut Budget,
    retained: &mut u64,
) -> R<NatLit> {
    let value = with_binary_operands(a, b, budget, |a, b, budget| {
        crate::check::natural::binary_arithmetic(op, a, b, budget, retained).map_err(binary_error)
    })?;
    Ok(match value.as_small() {
        Some(n) => NatLit::Small(n),
        None => {
            const { assert!(std::mem::size_of::<BinaryNat>() <= 40) };
            charge_bytes(budget, retained, 40)?;
            let mut slot = Vec::new();
            slot.try_reserve_exact(1).map_err(|_| alloc_failed())?;
            slot.push(value);
            NatLit::Computed(
                slot.into_boxed_slice()
                    .try_into()
                    .map_err(|_| ResourceError::Invariant)?,
                std::cell::Cell::new(0),
            )
        }
    })
}

pub(super) fn compare_naturals(
    a: &NatLit,
    b: &NatLit,
    budget: &mut Budget,
) -> R<std::cmp::Ordering> {
    if matches!(a, NatLit::Computed(..)) || matches!(b, NatLit::Computed(..)) {
        return with_binary_operands(a, b, budget, |a, b, budget| Ok(a.compare(b, budget)?));
    }
    let (x, y) = (nat_digits(a)?, nat_digits(b)?);
    let (x, y) = (x.as_bytes(), y.as_bytes());
    budget.charge_work((x.len() + y.len() + 4) as u64)?;
    Ok(x.len().cmp(&y.len()).then_with(|| x.cmp(y)))
}

pub(super) fn nat_eq(a: &NatLit, b: &NatLit, budget: &mut Budget) -> R<bool> {
    Ok(match (a, b) {
        (NatLit::Evicted(_), _) | (_, NatLit::Evicted(_)) => {
            return Err(ResourceError::Invariant.into());
        }
        (NatLit::Small(x), NatLit::Small(y)) => x == y,
        (NatLit::Big(x), NatLit::Big(y)) => x == y,
        (NatLit::Computed(..), _) | (_, NatLit::Computed(..)) => {
            compare_naturals(a, b, budget)?.is_eq()
        }
        _ => false,
    })
}
pub(super) fn nat_pred(n: &NatLit, budget: &mut Budget, reserved: &mut u64) -> R<NatLit> {
    match n {
        NatLit::Evicted(_) => Err(ResourceError::Invariant.into()),
        NatLit::Small(v) => Ok(NatLit::Small(v - 1)),
        x @ NatLit::Computed(..) => {
            computed_nat(Operation::Sub, x, &NatLit::Small(1), budget, reserved)
        }
        // This is the sole canonical big input whose predecessor is small.
        NatLit::Big(bytes) if bytes == b"18446744073709551616" => Ok(NatLit::Small(u64::MAX)),
        NatLit::Big(bytes) => {
            // The only owned buffer is the retained result. Reserve its actual
            // capacity before copying; failures retain ownership until rollback.
            charge_bytes(budget, reserved, bytes.len())?;
            let mut digits = copied(bytes)?;
            let mut i = digits.len();
            while i > 0 {
                i -= 1;
                if digits[i] == b'0' {
                    digits[i] = b'9';
                } else {
                    digits[i] -= 1;
                    break;
                }
            }
            if digits[0] == b'0' {
                digits.remove(0);
            }
            // Removing a leading zero does not shrink capacity or its charge.
            Ok(NatLit::Big(digits))
        }
    }
}

pub(super) fn nat_small(
    op: crate::check::natural::Operation,
    a: &NatLit,
    c: &NatLit,
) -> Option<u64> {
    use crate::check::natural::Operation::*;
    let (NatLit::Small(x), NatLit::Small(y)) = (a, c) else {
        return None;
    };
    let (x, y) = (*x, *y);
    match op {
        Add => x.checked_add(y),
        Mul => x.checked_mul(y),
        Sub => Some(x.saturating_sub(y)),
        Div => Some(x.checked_div(y).unwrap_or(0)),
        Mod => Some(if y == 0 { x } else { x % y }),
        Pow => u32::try_from(y).ok().and_then(|y| x.checked_pow(y)),
        Land => Some(x & y),
        Lor => Some(x | y),
        Xor => Some(x ^ y),
        ShiftRight => Some(if y >= 64 { 0 } else { x >> y }),
        ShiftLeft => {
            if x == 0 {
                Some(0)
            } else if y < 64 && x <= (u64::MAX >> y) {
                Some(x << y)
            } else {
                None
            }
        }
        Gcd => {
            let (mut a, mut b) = (x, y);
            while b != 0 {
                let next = a % b;
                a = b;
                b = next;
            }
            Some(a)
        }
    }
}
