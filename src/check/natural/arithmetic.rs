//! Exact BigUint arithmetic with coarse size-dependent admission.
use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Operation {
    Add,
    Mul,
    Pow,
    Sub,
    Div,
    Mod,
    Gcd,
    Land,
    Lor,
    Xor,
    ShiftLeft,
    ShiftRight,
}

#[derive(Clone, Copy)]
enum Action {
    Zero,
    One,
    Left,
    Right,
    Add,
    Mul,
    Pow(u32),
    Sub,
    Div(u32),
    Mod(u32),
    GeneralDiv,
    GeneralMod,
    Gcd,
    Land,
    Lor,
    Xor,
    ShiftLeft(usize),
    ShiftRight(usize),
}

/// Both operands are bounded before planning. The pinned borrowed division
/// backend uses normalized digit division; its quotient, remainder reuse and
/// clone/grow/shrink overlaps fit the reviewed additional envelope.
/// Zero is intercepted by the caller before this plan or any backend call.
fn general_division_plan(op: Operation, ab: u64, bb: u64) -> Result<(Action, u64, u64), Error> {
    let size = plans::add(&[ab.div_ceil(32), bb.div_ceil(32), 4])?;
    Ok((
        if op == Operation::Div {
            Action::GeneralDiv
        } else {
            Action::GeneralMod
        },
        plans::mul(&[128, size])?,
        plans::mul(&[128, size, size])?,
    ))
}

fn parse_plan(len: usize) -> Result<(u64, u64), Error> {
    let d = u64::try_from(len).map_err(|_| ResourceError::Counter)?;
    if d == 0 {
        return Err(ResourceError::Invariant.into());
    }
    plans::parse(d)
}

fn operation_plan(op: Operation, a: &BigUint, b: &BigUint) -> Result<(Action, u64, u64), Error> {
    let (ab, bb) = (a.bits(), b.bits());
    let bounded_left = || {
        let m = ab.div_ceil(32);
        Ok((
            Action::Left,
            plans::mul(&[24, plans::add(&[m, 1])?])?,
            plans::mul(&[32, plans::add(&[m, 2])?])?,
        ))
    };
    match op {
        Operation::Gcd => {
            if bb == 0 {
                return bounded_left();
            }
            if ab == 0 {
                let m = bb.div_ceil(32);
                return Ok((
                    Action::Right,
                    plans::mul(&[24, plans::add(&[m, 1])?])?,
                    plans::mul(&[32, plans::add(&[m, 2])?])?,
                ));
            }
            // Every two Euclidean iterations halve the smaller initial width.
            // Include working clones beside the audited borrowed remainder's
            // normalized division vectors; no recursive gcd or new dependency.
            let n = plans::add(&[ab.div_ceil(32), bb.div_ceil(32), 4])?;
            let iterations = plans::add(&[plans::mul(&[2, ab.min(bb)])?, 1])?;
            Ok((
                Action::Gcd,
                plans::mul(&[192, n])?,
                plans::mul(&[128, n, n, iterations])?,
            ))
        }
        Operation::Land | Operation::Lor | Operation::Xor => {
            let n = plans::add(&[ab.max(bb).div_ceil(32), 1])?;
            let action = match op {
                Operation::Land => Action::Land,
                Operation::Lor => Action::Lor,
                _ => Action::Xor,
            };
            Ok((action, plans::mul(&[48, n])?, plans::mul(&[64, n])?))
        }
        Operation::ShiftLeft | Operation::ShiftRight => {
            if ab == 0 {
                return Ok((Action::Zero, 32, 32));
            }
            let count = u64::try_from(b).ok();
            if op == Operation::ShiftRight && count.is_none_or(|n| n >= ab) {
                return Ok((Action::Zero, 32, 32));
            }
            let count = count.ok_or(Error::Unsupported)?;
            let bits = if op == Operation::ShiftLeft {
                ab.checked_add(count).ok_or(Error::Unsupported)?
            } else {
                ab - count
            };
            let shift = usize::try_from(count).map_err(|_| Error::Unsupported)?;
            let n = ab
                .div_ceil(32)
                .checked_add(bits.div_ceil(32))
                .and_then(|n| n.checked_add(4))
                .ok_or(Error::Unsupported)?;
            // A pure optional plan's representability failure is unsupported,
            // not a counter-corruption/internal failure and never an allocation.
            let bytes = n.checked_mul(48).ok_or(Error::Unsupported)?;
            let work = n.checked_mul(64).ok_or(Error::Unsupported)?;
            let action = if op == Operation::ShiftLeft {
                Action::ShiftLeft(shift)
            } else {
                Action::ShiftRight(shift)
            };
            Ok((action, bytes, work))
        }
        Operation::Add => {
            let m = ab.max(bb).div_ceil(32);
            Ok((
                Action::Add,
                plans::mul(&[24, plans::add(&[m, 1])?])?,
                plans::mul(&[32, plans::add(&[m, 2])?])?,
            ))
        }
        Operation::Mul => {
            if ab == 0 || bb == 0 {
                return Ok((Action::Zero, 32, 32));
            }
            if ab.checked_add(bb).ok_or(ResourceError::Counter)? > SCALAR_FORMAT_BITS + 1 {
                let (bytes, work) =
                    plans::multiply(plans::add(&[ab.div_ceil(32), bb.div_ceil(32)])?)?;
                return Ok((Action::Mul, bytes, work));
            }
            // The shorter operand has <=1008 bits, hence <=32 limbs even
            // with 32-bit BigDigits. The backend therefore uses schoolbook or
            // scalar multiplication, never its recursive multiplication paths.
            let (ma, mb) = (ab.div_ceil(32), bb.div_ceil(32));
            Ok((
                Action::Mul,
                32 * (ma.max(mb) + 1),
                64 * (ma + mb + 1).pow(2),
            ))
        }
        Operation::Sub => {
            // Truncating subtraction: a - b = 0 whenever a <= b. The result is at
            // most a, so a's bit length bounds its storage and formatting.
            if a <= b {
                return Ok((Action::Zero, 32, 32));
            }
            let m = ab.div_ceil(32);
            Ok((
                Action::Sub,
                plans::mul(&[24, plans::add(&[m, 1])?])?,
                plans::mul(&[32, plans::add(&[m, 2])?])?,
            ))
        }
        Operation::Pow => {
            // Ordering matters: 0^0=1. A huge exponent need not fit a host
            // integer for these exact constant results; parsing is still bounded.
            if bb == 0 || ab == 1 {
                return Ok((Action::One, 32, 32));
            }
            if ab == 0 {
                return Ok((Action::Zero, 32, 32));
            }
            let exponent = u32::try_from(b).map_err(|_| Error::Unsupported)?;
            if exponent == 1 {
                return bounded_left();
            }
            let bits = ab
                .checked_mul(u64::from(exponent))
                .ok_or(ResourceError::Counter)?;
            if bits > SCALAR_FORMAT_BITS {
                let n = plans::add(&[bits.div_ceil(32), 1])?;
                let (bytes, work) = plans::multiply(n)?;
                let products = 2 * u64::from(u32::BITS - exponent.leading_zeros()) + 1;
                return Ok((
                    Action::Pow(exponent),
                    plans::add(&[plans::mul(&[96, n])?, bytes])?,
                    plans::add(&[
                        plans::mul(&[products, work])?,
                        plans::mul(&[64, plans::add(&[n, 1])?, plans::add(&[n, 1])?, products])?,
                    ])?,
                ));
            }
            // Each intermediate denotes a power whose exponent is <=exponent;
            // each multiplication's factor bit lengths sum to <=bits. Thus the
            // same <=32-shorter-limb bound holds throughout the library loop.
            let m = bits.div_ceil(32);
            let width = u64::from(u32::BITS - exponent.leading_zeros());
            Ok((
                Action::Pow(exponent),
                96 * (m + 1),
                64 * (m + 2).pow(2) * (2 * width + 1),
            ))
        }
        Operation::Div => {
            // Lean's Nat.div returns zero at a zero divisor. The crate panics
            // there, so this branch must precede every backend division call.
            if bb == 0 || ab == 0 {
                return Ok((Action::Zero, 32, 32));
            }
            let Ok(divisor) = u32::try_from(b) else {
                return general_division_plan(op, ab, bb);
            };
            if divisor == 1 {
                return bounded_left();
            }
            let m = ab.div_ceil(32);
            // num-bigint's owning BigUint / u32 mutates one cloned digit vector
            // in place. The 24-byte-per-limb envelope exceeds both digit widths.
            Ok((
                Action::Div(divisor),
                plans::mul(&[24, plans::add(&[m, 1])?])?,
                plans::mul(&[64, plans::add(&[m, 2])?])?,
            ))
        }
        Operation::Mod => {
            // The exported recurrence returns the dividend at divisor zero.
            // Guard this before num-bigint's scalar remainder, which panics on
            // zero. A returned dividend still needs the formatter's bound.
            if bb == 0 {
                return bounded_left();
            }
            let Ok(divisor) = u32::try_from(b) else {
                return general_division_plan(op, ab, bb);
            };
            if divisor == 1 || ab == 0 {
                return Ok((Action::Zero, 32, 32));
            }
            let m = ab.div_ceil(32);
            // Borrowed-digit remainder scans the admitted digits and returns a
            // scalar. This exceeds its work and one-limb result reservation.
            Ok((
                Action::Mod(divisor),
                plans::mul(&[24, plans::add(&[m, 1])?])?,
                plans::mul(&[64, plans::add(&[m, 2])?])?,
            ))
        }
    }
}

fn reserve_more(bytes: u64, reserved: &mut u64, b: &mut Budget) -> Result<(), ResourceError> {
    let total = reserved.checked_add(bytes).ok_or(ResourceError::Counter)?;
    b.reserve(bytes)?;
    *reserved = total;
    Ok(())
}

/// Inputs are canonical decimal payloads from Expressions. The caller already
/// established exact committed operation authority and checked Nat operands.
/// No backend miss is a negative comparison. Every result retains the complete
/// precharged reservation until append/caller retirement, as successor does.
pub(crate) fn arithmetic(
    op: Operation,
    left: &[u8],
    right: &[u8],
    b: &mut Budget,
) -> Result<Digits, Error> {
    let (left_bytes, left_work) = parse_plan(left.len())?;
    let (right_bytes, right_work) = parse_plan(right.len())?;
    let mut reserved = 0;
    b.charge_work(plans::add(&[left_work, right_work])?)?;
    reserve_more(plans::add(&[left_bytes, right_bytes])?, &mut reserved, b)?;
    let result = (|| {
        let a = BigUint::parse_bytes(left, 10).ok_or(ResourceError::Invariant)?;
        let z = BigUint::parse_bytes(right, 10).ok_or(ResourceError::Invariant)?;
        let (action, bytes, work) = operation_plan(op, &a, &z)?;
        b.charge_work(work)?;
        reserve_more(bytes, &mut reserved, b)?;
        let value = apply(action, &a, &z);
        let bits = value.bits();
        let (bytes, work) = plans::format(bits)?;
        b.charge_work(work)?;
        reserve_more(bytes, &mut reserved, b)?;
        Ok(value.to_str_radix(10))
    })();
    // All parsed/working BigUints have dropped before releasing their capacity.
    match result {
        Ok(text) => Ok(Digits { text, reserved }),
        Err(error) => {
            b.release(reserved)?;
            Err(error)
        }
    }
}

fn apply(action: Action, a: &BigUint, z: &BigUint) -> BigUint {
    match action {
        Action::Zero => BigUint::ZERO,
        Action::One => BigUint::from(1u32),
        Action::Left => a.clone(),
        Action::Right => z.clone(),
        Action::Add => a + z,
        Action::Mul => a * z,
        Action::Pow(exponent) => a.pow(exponent),
        Action::Sub => a - z,
        Action::Div(divisor) => a.clone() / divisor,
        Action::Mod(divisor) => a % divisor,
        Action::GeneralDiv => a / z,
        Action::GeneralMod => a % z,
        Action::Gcd => {
            let (mut x, mut y) = (a.clone(), z.clone());
            while y != BigUint::ZERO {
                let next = &x % &y;
                x = y;
                y = next;
            }
            x
        }
        Action::Land => a & z,
        Action::Lor => a | z,
        Action::Xor => a ^ z,
        Action::ShiftLeft(n) => a << n,
        Action::ShiftRight(n) => a >> n,
    }
}

// A value in a single value-kernel graph. All large values are normalized
// magnitudes greater than u64::MAX, so a mixed pair cannot compare equal.
#[derive(Clone)]
pub(crate) struct BinaryNat(Magnitude);

#[derive(Clone)]
enum Magnitude {
    Small(u64),
    Big(BigUint),
    Packed { limbs: usize, words: Vec<u32> },
}

impl BinaryNat {
    pub(crate) fn small(value: u64) -> Self {
        Self(Magnitude::Small(value))
    }
    pub(crate) fn as_small(&self) -> Option<u64> {
        match self.0 {
            Magnitude::Small(n) => Some(n),
            _ => None,
        }
    }

    fn operand(
        &self,
        budget: &mut Budget,
        scratch: &mut u64,
    ) -> Result<std::borrow::Cow<'_, BigUint>, ResourceError> {
        use std::borrow::Cow;
        Ok(match &self.0 {
            Magnitude::Small(n) => Cow::Owned(BigUint::from(*n)),
            Magnitude::Big(n) => Cow::Borrowed(n),
            Magnitude::Packed { limbs, words } => {
                let length = *limbs as u64;
                budget.charge_work(32 * (length + 4))?;
                reserve_more(32 * (length + 4), scratch, budget)?;
                let mut digits = Vec::new();
                digits
                    .try_reserve_exact(*limbs)
                    .map_err(|_| ResourceError::Allocation)?;
                let mut data = words.as_slice();
                while digits.len() < *limbs {
                    let (&mask, rest) = data.split_first().ok_or(ResourceError::Invariant)?;
                    let width = 32.min(*limbs - digits.len());
                    let (block, next) = rest
                        .split_at_checked(mask.count_ones() as usize)
                        .ok_or(ResourceError::Invariant)?;
                    data = next;
                    let start = digits.len();
                    if mask == u32::MAX && width == 32 {
                        digits.extend_from_slice(block);
                    } else {
                        digits.resize(start + width, 0);
                        let mut bits = mask;
                        for &word in block {
                            let index = bits.trailing_zeros() as usize;
                            *digits
                                .get_mut(start + index)
                                .ok_or(ResourceError::Invariant)? = word;
                            bits &= bits - 1;
                        }
                    }
                }
                if !data.is_empty() {
                    return Err(ResourceError::Invariant);
                }
                Cow::Owned(BigUint::new(digits))
            }
        })
    }

    pub(crate) fn compare(
        &self,
        rhs: &Self,
        budget: &mut Budget,
    ) -> Result<std::cmp::Ordering, ResourceError> {
        use std::cmp::Ordering;
        match (&self.0, &rhs.0) {
            (Magnitude::Small(a), Magnitude::Small(b)) => return Ok(a.cmp(b)),
            (Magnitude::Small(_), _) => return Ok(Ordering::Less),
            (_, Magnitude::Small(_)) => return Ok(Ordering::Greater),
            _ => {}
        }
        let mut scratch = 0;
        let result = (|| {
            let a = self.operand(budget, &mut scratch)?;
            let b = rhs.operand(budget, &mut scratch)?;
            budget.charge_work(a.bits().min(b.bits()).div_ceil(32) + 1)?;
            Ok(a.cmp(&b))
        })();
        budget.release(scratch)?;
        result
    }
}

fn keep_binary(result: &BigUint, b: &mut Budget, retained: &mut u64) -> Result<BinaryNat, Error> {
    if let Ok(small) = u64::try_from(result) {
        return Ok(BinaryNat::small(small));
    }
    // Clone the normalized digits, not the possibly larger scratch capacity.
    // The portable envelope covers the minimum allocation and rounding to a
    // machine digit on both targets.
    let limbs = result.bits().div_ceil(32);
    if limbs > 256 {
        b.charge_work(32 * (limbs + 4))?;
        let count = result.iter_u32_digits().filter(|&digit| digit != 0).count() as u64
            + limbs.div_ceil(32);
        if count <= limbs - limbs.div_ceil(8) {
            reserve_more(4 * count, retained, b)?;
            let mut words = Vec::new();
            words
                .try_reserve_exact(usize::try_from(count).map_err(|_| ResourceError::Storage)?)
                .map_err(|_| ResourceError::Allocation)?;
            let mut digits = result.iter_u32_digits();
            while digits.len() != 0 {
                let mask_at = words.len();
                words.push(0);
                let mut mask = 0;
                for (bit, digit) in digits.by_ref().take(32).enumerate() {
                    if digit != 0 {
                        mask |= 1 << bit;
                        words.push(digit);
                    }
                }
                words[mask_at] = mask;
            }
            return Ok(BinaryNat(Magnitude::Packed {
                limbs: usize::try_from(limbs).map_err(|_| ResourceError::Storage)?,
                words,
            }));
        }
    }
    b.charge_work(limbs + 1)?;
    reserve_more(plans::mul(&[8, limbs + 4])?, retained, b)?;
    Ok(BinaryNat(Magnitude::Big(result.clone())))
}

pub(crate) fn parse_binary(
    bytes: &[u8],
    b: &mut Budget,
    retained: &mut u64,
) -> Result<BinaryNat, Error> {
    let (space, work) = parse_plan(bytes.len())?;
    b.charge_work(work)?;
    b.reserve(space)?;
    let result = BigUint::parse_bytes(bytes, 10)
        .ok_or(ResourceError::Invariant.into())
        .and_then(|n| keep_binary(&n, b, retained));
    b.release(space)?;
    result
}

pub(crate) fn binary_arithmetic(
    op: Operation,
    left: &BinaryNat,
    right: &BinaryNat,
    b: &mut Budget,
    retained: &mut u64,
) -> Result<BinaryNat, Error> {
    // Both potential u64-to-BigUint temporaries remain covered until drop.
    let mut scratch = 0;
    reserve_more(64, &mut scratch, b)?;
    let result = (|| {
        let a = left.operand(b, &mut scratch)?;
        let z = right.operand(b, &mut scratch)?;
        let (ab, bb) = (a.bits(), z.bits());
        let product_bits = ab.checked_mul(u64::try_from(z.as_ref()).unwrap_or(u64::MAX));
        let value = if op == Operation::Pow
            && ab > 1
            && ab <= 32
            && product_bits.is_some_and(|n| n > SCALAR_FORMAT_BITS)
            && !operation_plan(op, &a, &z).is_ok_and(|(_, space, work)| {
                b.has_work_headroom(work) && b.has_storage_headroom(space)
            })
            && let Ok(exponent) = u32::try_from(z.as_ref())
        {
            // A fixed scalar multiply is linear in the current width. The final
            // bound dominates every iteration of this pinned backend operation.
            let limbs = (ab * u64::from(exponent)).div_ceil(32);
            b.charge_work(plans::mul(&[64, limbs + 4, u64::from(exponent) + 1])?)?;
            reserve_more(plans::mul(&[64, limbs + 4])?, &mut scratch, b)?;
            let mut value = BigUint::from(1u32);
            let factor = u32::try_from(a.as_ref()).map_err(|_| ResourceError::Invariant)?;
            for _ in 0..exponent {
                value *= factor;
            }
            value
        } else {
            let (action, space, work) = if op == Operation::Mul
                && ab.min(bb) > 0
                && ab.min(bb) <= 1024
                && ab.max(bb) > SCALAR_FORMAT_BITS
            {
                // The shorter operand has at most 32 portable digits. This
                // selects a schoolbook leaf even for an asymmetric wide pair.
                let s = plans::add(&[ab.div_ceil(32), bb.div_ceil(32)])?;
                let work = plans::add(&[
                    plans::mul(&[128, ab.min(bb).div_ceil(32) + 2, s + 4])?,
                    plans::mul(&[1024, s + 16])?,
                ])?;
                (Action::Mul, plans::mul(&[576, s + 16])?, work)
            } else {
                operation_plan(op, &a, &z)?
            };
            b.charge_work(work)?;
            reserve_more(space, &mut scratch, b)?;
            apply(action, &a, &z)
        };
        keep_binary(&value, b, retained)
    })();
    b.release(scratch)?;
    result
}
