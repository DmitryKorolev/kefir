//! Structural prefix composition; no display-name concatenation or public names.
use super::*;
use crate::syntax::names::NameError;
fn append(prefix: NameId, part: Component<'_>, work: &mut Working<'_>) -> Result<NameId, Stop> {
    work.names
        .append(prefix, part, work.budget)
        .map_err(|e| match e {
            NameError::Resource(e) => Stop::Resource(e),
            _ => Stop::Resource(ResourceError::Invariant),
        })
}
fn compose(
    prefix: NameId,
    name: NameId,
    stop: NameId,
    work: &mut Working<'_>,
) -> Result<NameId, Stop> {
    let mut path = Vec::new();
    let mut data = Vec::new();
    let result = (|| {
        let mut n = name;
        while !same(work.names, n, stop, work.budget)? {
            let Some((p, _)) = work.names.view(n, work.budget)? else {
                return Err(ResourceError::Invariant.into());
            };
            push_frame(&mut path, n, work.budget)?;
            n = p;
        }
        let mut out = prefix;
        while let Some(n) = pop_frame(&mut path, work.budget)? {
            let (_, part) = work
                .names
                .view(n, work.budget)?
                .ok_or(ResourceError::Invariant)?;
            let (numeric, payload) = match part {
                Component::Number(s) => (true, s),
                Component::String(s) => (false, s.as_bytes()),
            };
            data.clear();
            work.budget.grow_vec(&mut data, payload.len())?;
            data.extend_from_slice(payload);
            let part = if numeric {
                Component::Number(&data)
            } else {
                Component::String(std::str::from_utf8(&data).map_err(|_| ResourceError::Invariant)?)
            };
            out = append(out, part, work)?;
        }
        Ok(out)
    })();
    let a = release_stack(path, work.budget);
    let b = release(data, work.budget);
    a?;
    b?;
    result
}
pub(super) fn fresh(
    prior: NameId,
    next: &mut u32,
    env: &Environment,
    before: usize,
    work: &mut Working<'_>,
) -> Result<NameId, Stop> {
    // Raw final-component suffixing is not macro-scope-preserving. Keep the
    // unsupported boundary explicit until exact appendIndexAfter is implemented.
    // Conservatively recognize reserved scope-marker components anywhere.
    let mut component = prior;
    while let Some((parent, part)) = work.names.view(component, work.budget)? {
        if matches!(part, Component::String("_@" | "_hyg" | "_hygCtx")) {
            return Err(Stop::Unsupported);
        }
        component = parent;
    }
    let prefix = append(NameId::ANONYMOUS, Component::String("_nested"), work)?;
    let base = compose(prefix, prior, NameId::ANONYMOUS, work)?;
    let mut data = Vec::new();
    let result = (|| {
        loop {
            let count = *next;
            *next = next.checked_add(1).ok_or(ResourceError::Counter)?;
            let mut digits = [0u8; 10];
            let mut at = 10;
            let mut n = count;
            loop {
                at -= 1;
                digits[at] = b'0' + (n % 10) as u8;
                n /= 10;
                if n == 0 {
                    break;
                }
            }
            let (parent, part) = work
                .names
                .view(base, work.budget)?
                .ok_or(ResourceError::Invariant)?;
            let parent = if let Component::String(s) = part {
                data.clear();
                work.budget.grow_vec(&mut data, s.len() + 1 + 10)?;
                data.extend_from_slice(s.as_bytes());
                parent
            } else {
                data.clear();
                work.budget.grow_vec(&mut data, 11)?;
                base
            };
            data.push(b'_');
            data.extend_from_slice(&digits[at..]);
            let candidate = append(
                parent,
                Component::String(
                    std::str::from_utf8(&data).map_err(|_| ResourceError::Invariant)?,
                ),
                work,
            )?;
            if env
                .lookup(candidate, before, work.names, work.budget)?
                .is_none()
            {
                return Ok(candidate);
            }
        }
    })();
    release(data, work.budget)?;
    result
}
pub(super) fn constructor(
    name: NameId,
    prior: NameId,
    helper: NameId,
    work: &mut Working<'_>,
) -> Result<NameId, Stop> {
    compose(helper, name, prior, work)
}

/// The structural root prefix is reserved, including occurrences hidden in a
/// projection type identity. Binder display names are deliberately irrelevant.
pub(super) fn public_name(mut name: NameId, work: &mut Working<'_>) -> Result<(), Stop> {
    while let Some((parent, part)) = work.names.view(name, work.budget)? {
        if parent == NameId::ANONYMOUS && matches!(part, Component::String("_nested")) {
            return Err(Stop::Unsupported);
        }
        name = parent;
    }
    Ok(())
}
