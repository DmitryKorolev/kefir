//! One demanded, uncached expansion using the committed whole String manifest.
use super::*;
use std::io::Write;

#[allow(clippy::too_many_arguments)]
pub(super) fn expand(
    root: ExprId,
    incoming: ReductionPath,
    scope: Scope<'_>,
    environment: &Environment,
    expressions: &mut Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Head, HeadError> {
    let symbols = environment
        .string_symbols(
            scope.before,
            scope.formation,
            scope.expression_end,
            expressions,
            levels,
            budget,
        )?
        .ok_or(HeadError::Unsupported)?;
    expand_symbols(root, incoming, symbols, expressions, levels, names, budget)
}

// Caller supplies the exact committed certificate symbols; tests exercise only
// this construction/retirement protocol, not semantic certificate admission.
fn expand_symbols(
    root: ExprId,
    incoming: ReductionPath,
    symbols: [NameId; 5],
    expressions: &mut Expressions,
    levels: &Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<Head, HeadError> {
    let ExprKind::String(bytes) =
        expressions
            .get(root, budget)?
            .kind(expressions, levels, budget)?
    else {
        return Err(HeadError::Unsupported);
    };
    let completed_path = incoming.after_reduction()?;
    // Count only after paying for UTF-8 validation and scalar counting. The remaining
    // precharge covers copying, reverse traversal and bounded scalar formatting.
    let length = u64::try_from(bytes.len()).map_err(|_| ResourceError::Counter)?;
    budget.charge_work(length.checked_mul(2).ok_or(ResourceError::Counter)?)?;
    let text = std::str::from_utf8(bytes).map_err(|_| ResourceError::Invariant)?;
    let count = text.chars().count();
    let work = u64::try_from(count)
        .ok()
        .and_then(|c| c.checked_add(1))
        .and_then(|c| c.checked_mul(32))
        .and_then(|c| length.checked_mul(2).and_then(|n| n.checked_add(c)))
        .ok_or(ResourceError::Counter)?;
    budget.charge_work(work)?;
    let mut copy = Vec::new();
    budget.grow_vec(&mut copy, bytes.len())?;
    copy.extend_from_slice(bytes);
    let mark = expressions.watermark();
    let result = construct(
        &copy,
        count,
        symbols,
        completed_path,
        expressions,
        levels,
        names,
        budget,
    );
    let capacity = copy.capacity() as u64;
    drop(copy);
    let release = budget.release(capacity);
    // No child owner, cache, or context ever sees the private suffix. On failed
    // rollback the caller's poisoned declaration owner still owns all syntax.
    if result.is_err() || release.is_err() {
        expressions.discard_since(mark, budget)?;
    }
    release?;
    if result.is_ok() {
        budget.observe(Event::Reductions, 1);
    }
    result
}

#[allow(clippy::too_many_arguments)]
fn construct(
    bytes: &[u8],
    count: usize,
    symbols: [NameId; 5],
    incoming: ReductionPath,
    e: &mut Expressions,
    l: &Levels,
    n: &Names,
    b: &mut Budget,
) -> Result<Head, HeadError> {
    // Pre-reservation invariant: the only emitted forms below are constants
    // with zero/one universe arguments, applications and natural literals.
    // Their third descriptor word is 0/1, so the compact expression store needs
    // no escaped-operand allocation after reserve_string_expansion succeeds.
    e.reserve_string_expansion(count, b)?;
    let [char_name, of_nat_name, nil_name, cons_name, of_list_name] = symbols;
    let char_ty = e.append(ExprKind::Constant(char_name, &[]), l, n, b)?;
    let of_nat = e.append(ExprKind::Constant(of_nat_name, &[]), l, n, b)?;
    let nil = e.append(ExprKind::Constant(nil_name, &[LevelId::ZERO]), l, n, b)?;
    let cons = e.append(ExprKind::Constant(cons_name, &[LevelId::ZERO]), l, n, b)?;
    let of_list = e.append(ExprKind::Constant(of_list_name, &[]), l, n, b)?;
    let mut tail = e.append(ExprKind::App(nil, char_ty), l, n, b)?;
    let cons_char = e.append(ExprKind::App(cons, char_ty), l, n, b)?;
    let text = std::str::from_utf8(bytes).map_err(|_| ResourceError::Invariant)?;
    for scalar in text.chars().rev() {
        let mut decimal = [0u8; 7];
        let used = {
            let mut output = &mut decimal[..];
            write!(&mut output, "{}", u32::from(scalar)).map_err(|_| ResourceError::Invariant)?;
            7 - output.len()
        };
        let value = e.append(ExprKind::Natural(&decimal[..used]), l, n, b)?;
        let character = e.append(ExprKind::App(of_nat, value), l, n, b)?;
        let head = e.append(ExprKind::App(cons_char, character), l, n, b)?;
        tail = e.append(ExprKind::App(head, tail), l, n, b)?;
    }
    let expression = e.append(ExprKind::App(of_list, tail), l, n, b)?;
    Ok(Head {
        expression,
        path: incoming,
    })
}
