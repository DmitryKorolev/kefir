//! Iota result spines without transient application syntax.
use super::*;

pub(super) fn after_iota(
    scratch: &mut Scratch,
    frame: Iota,
    rhs: ExprId,
    fields: usize,
    b: &mut Budget,
) -> Result<(), ResourceError> {
    let old_len = scratch.applications.len();
    let prefix = frame.layout()?.0 as usize;
    let prefix_start = old_len
        .checked_sub(prefix)
        .ok_or(ResourceError::Invariant)?;
    let start = prefix_start
        .checked_sub(frame.layout()?.1 as usize)
        .and_then(|n| n.checked_sub(1))
        .ok_or(ResourceError::Invariant)?;
    if old_len != frame.end as usize
        || start < scratch.base()
        || fields > scratch.constructor_arguments.len()
    {
        return Err(ResourceError::Invariant);
    }
    let prefix_destination = start.checked_add(fields).ok_or(ResourceError::Counter)?;
    let new_len = prefix_destination
        .checked_add(prefix)
        .ok_or(ResourceError::Counter)?;
    b.charge_work(
        u64::try_from(
            prefix
                .checked_add(fields)
                .and_then(|n| n.checked_add(1))
                .ok_or(ResourceError::Counter)?,
        )
        .map_err(|_| ResourceError::Counter)?,
    )?;
    let added = new_len.saturating_sub(old_len);
    b.reserve_frames(added)?;
    if let Err(error) = b.grow_vec(&mut scratch.applications, new_len) {
        b.release_frames(added)?;
        return Err(error);
    }
    let marker = Application {
        original: rhs,
        function: rhs,
        argument: rhs,
    };
    // No fallible construction remains: preserve every outer application and
    // suspension boundary, then publish the new suffix in argument-pop order.
    if new_len > old_len {
        scratch.applications.resize(new_len, marker);
    }
    scratch
        .applications
        .copy_within(prefix_start..old_len, prefix_destination);
    for (slot, &argument) in scratch.applications[start..prefix_destination]
        .iter_mut()
        .zip(&scratch.constructor_arguments[..fields])
    {
        *slot = Application { argument, ..marker };
    }
    for slot in &mut scratch.applications[prefix_destination..new_len] {
        slot.original = rhs;
        slot.function = rhs;
    }
    scratch.applications.truncate(new_len);
    b.release_frames(old_len.saturating_sub(new_len))?;
    scratch.constructor_arguments.clear();
    Ok(())
}
