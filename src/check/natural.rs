//! Budget-admitted owned BigUint successor/predecessor; gives the bounds.
//! Input is canonical decimal storage from Expressions, never raw JSON text.
use crate::resource::{Budget, ResourceError};
use num_bigint::BigUint;

mod arithmetic;
mod plans;
pub(crate) use arithmetic::{Operation, arithmetic};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Error {
    Resource(ResourceError),
    Unsupported,
}
impl From<ResourceError> for Error {
    fn from(value: ResourceError) -> Self {
        Self::Resource(value)
    }
}

pub(crate) struct Digits {
    text: String,
    reserved: u64,
}
const _: () = assert!(core::mem::size_of::<Digits>() == 32);
const _: () = assert!(core::mem::size_of::<BigUint>() == 24);

impl Digits {
    pub(crate) fn as_bytes(&self) -> &[u8] {
        self.text.as_bytes()
    }
    pub(crate) fn retire(self, budget: &mut Budget) -> Result<(), ResourceError> {
        let reserved = self.reserved;
        drop(self);
        budget.release(reserved)
    }
}

const SCALAR_FORMAT_BITS: u64 = 2016;

fn plan(d: usize) -> Result<(u64, u64), Error> {
    let d = u64::try_from(d).map_err(|_| ResourceError::Counter)?;
    if d == 0 {
        return Err(ResourceError::Invariant.into());
    }
    // Canonical nonzero d-digit numbers have at least 3(d-1)+1 bits.
    // Preserve the existing small plan; larger calls compose the same parser,
    // mutation and formatter envelopes under the unchanged run budgets.
    if d > 672 {
        let (parse_bytes, parse_work) = plans::parse(d)?;
        let bits = plans::add(&[plans::mul(&[4, d])?, 1])?;
        let limbs = plans::add(&[bits.div_ceil(32), 2])?;
        return Ok((
            plans::add(&[parse_bytes, plans::mul(&[64, limbs])?])?,
            plans::add(&[parse_work, plans::mul(&[32, limbs])?])?,
        ));
    }
    let bits = d.checked_mul(4).ok_or(ResourceError::Counter)?;
    let l = bits.div_ceil(32) + 1;
    let c = (2 * (l + 1)).max(4);
    let f = (bits + 1).div_ceil(32);
    let digits = (bits + 1).div_ceil(3) + 1;
    let storage = d + 24 * l.max(4) + 24 * c + 8 * c + 16 * f + 3 * digits.max(8);
    let work = 32 * (d + 1) * (l + 1) + 32 * (digits + 1) * (f + 1) + 32 * (l + 1);
    Ok((storage, work))
}

pub(crate) fn successor(bytes: &[u8], budget: &mut Budget) -> Result<Digits, Error> {
    step(bytes, true, budget)
}

/// Called only for a positive canonical literal selected by Nat major exposure.
pub(crate) fn predecessor(bytes: &[u8], budget: &mut Budget) -> Result<Digits, Error> {
    step(bytes, false, budget)
}

fn step(bytes: &[u8], increment: bool, budget: &mut Budget) -> Result<Digits, Error> {
    let (mut reserved, work) = plan(bytes.len())?;
    budget.charge_work(work)?;
    budget.reserve(reserved)?;
    let result = (|| {
        // Expressions guarantees digits only, canonical leading zero, and ASCII.
        // The crate parser is more permissive; it is not an input validator.
        let mut value = BigUint::parse_bytes(bytes, 10).ok_or(ResourceError::Invariant)?;
        if increment {
            value += 1u32;
        } else {
            if value.bits() == 0 {
                return Err(ResourceError::Invariant.into());
            }
            value -= 1u32;
        }
        if value.bits() > SCALAR_FORMAT_BITS {
            // Admit formatting at its actual result size, as arithmetic does.
            // This avoids assuming the floor-sqrt quotient-count envelope is
            // monotone when composed with an overestimate of parsed bit size.
            let (extra, work) = plans::format(value.bits())?;
            budget.charge_work(work)?;
            let total = reserved.checked_add(extra).ok_or(ResourceError::Counter)?;
            budget.reserve(extra)?;
            reserved = total;
        }
        Ok(value.to_str_radix(10))
    })();
    match result {
        Ok(text) => Ok(Digits { text, reserved }),
        Err(error) => {
            budget.release(reserved)?;
            Err(error)
        }
    }
}
