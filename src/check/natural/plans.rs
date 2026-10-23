//! Coarse requested-layout/work envelopes resource ledger.
//! These plan whole backend calls; there is no per-digit budget bookkeeping.
use super::*;

pub(super) fn add(values: &[u64]) -> Result<u64, Error> {
    values.iter().try_fold(0u64, |a, b| {
        a.checked_add(*b).ok_or(ResourceError::Counter.into())
    })
}

pub(super) fn mul(values: &[u64]) -> Result<u64, Error> {
    values.iter().try_fold(1u64, |a, b| {
        a.checked_mul(*b).ok_or(ResourceError::Counter.into())
    })
}

pub(super) fn parse(d: u64) -> Result<(u64, u64), Error> {
    if d == 0 {
        return Err(ResourceError::Invariant.into());
    }
    let m = add(&[mul(&[4, d])?.div_ceil(32), 1])?;
    Ok((
        add(&[d, mul(&[24, m.max(4)])?])?,
        mul(&[32, add(&[d, 1])?, add(&[m, 1])?])?,
    ))
}

pub(super) fn multiply(s: u64) -> Result<(u64, u64), Error> {
    let q = s.saturating_sub(6).max(1);
    let r = add(&[s, 16])?;
    let h = 2 * u64::from(u64::BITS - q.leading_zeros()) + 1;
    // The reviewed bound distinguishes local helper work from borrowed
    // ancestor-output tails; tiny leaves are covered by the linear term.
    let nodes = add(&[1, mul(&[5, mul(&[q, q])? / 400])?])?;
    Ok((
        mul(&[576, r])?,
        add(&[mul(&[1024, h, r, r])?, mul(&[1024, r, nodes])?])?,
    ))
}

pub(super) fn format(bits: u64) -> Result<(u64, u64), Error> {
    let n = bits.div_ceil(32);
    if bits <= SCALAR_FORMAT_BITS {
        let digits = add(&[bits.div_ceil(3), 1])?;
        return Ok((
            add(&[mul(&[16, n])?, mul(&[3, digits.max(8)])?])?,
            mul(&[32, add(&[digits, 1])?, add(&[n, 1])?])?,
        ));
    }
    // The general formatter's source-derived composition applies at N>=64.
    let t = n.isqrt();
    let m = add(&[mul(&[2, t])?, 4])?;
    let p = add(&[mul(&[4, t])?, 4])?;
    let digits = add(&[bits, 1])?;
    let square_bound = mul(&[128, add(&[t, 1])?])?;
    let j = u64::from(u64::BITS - square_bound.leading_zeros());
    let denominator = n.div_ceil(2).isqrt() - 1;
    let l = n.div_ceil(denominator);
    let division_size = add(&[n, m, 6])?;
    let (multiply_bytes, multiply_work) = multiply(p)?;
    let bytes = add(&[
        mul(&[8, add(&[n, 2, mul(&[3, m])?])?])?,
        mul(&[3, digits])?,
        multiply_bytes.max(mul(&[128, division_size])?),
    ])?;
    let v = add(&[
        mul(&[add(&[n, 4])?, add(&[mul(&[64, m])?, 128])?])?,
        mul(&[256, division_size])?,
        256,
    ])?;
    let work = add(&[
        mul(&[j, multiply_work])?,
        mul(&[l, v])?,
        mul(&[32, add(&[digits, 1])?, add(&[n, 1])?])?,
        mul(&[256, add(&[digits, n, m, 64])?])?,
    ])?;
    Ok((bytes, work))
}
