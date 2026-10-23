//! Compile-time canonical descriptor checks; no production traversal or state.
use super::manifest::*;

const fn term(id: u32, before: usize) -> bool {
    id != 0 && (id as usize) < before
}
const fn name(id: u32) -> bool {
    id as usize <= NAMES.len()
}
const fn sequence(id: u32) -> bool {
    id != 0 && id as usize <= SEQUENCES.len()
}
const fn canonical() -> bool {
    let mut i = 0;
    while i < NAMES.len() {
        let [parent, tag, a, b] = NAMES[i];
        if parent as usize > i || tag > 1 {
            return false;
        }
        if tag == 0 && a as usize + b as usize > UTF8_BYTES.len() {
            return false;
        }
        i += 1;
    }
    i = 0;
    while i < LEVELS.len() {
        let [tag, a, b] = LEVELS[i];
        if !match tag {
            0 => a == 0 && b == 0,
            1 => a != 0 && a as usize <= i && b == 0,
            2 => name(a) && a != 0 && b == 0,
            3 | 4 => a != 0 && a as usize <= i && b != 0 && b as usize <= i,
            _ => false,
        } {
            return false;
        }
        i += 1;
    }
    i = 0;
    while i < SEQUENCES.len() {
        let [start, len] = SEQUENCES[i];
        if start as usize + len as usize > SEQUENCE_WORDS.len() {
            return false;
        }
        i += 1;
    }
    i = 0;
    while i < EXPRESSIONS.len() {
        let [tag, a, b, c] = EXPRESSIONS[i];
        let before = i + 1;
        let valid = match tag {
            0 => b == 0 && c == 0,
            1 => a != 0 && a as usize <= LEVELS.len() && b == 0 && c == 0,
            2..=4 => term(a, before) && term(b, before) && c == 0,
            5 => name(a) && a != 0 && sequence(b) && c == 0,
            6 => name(a) && a != 0 && term(c, before),
            7 | 9 => a as usize + b as usize <= UTF8_BYTES.len() && c == 0,
            8 => {
                if a == 0 || a as usize > LET_PAYLOADS.len() || b != 0 || c != 0 {
                    return false;
                }
                let [binder, ty, value, body, flags] = LET_PAYLOADS[a as usize - 1];
                name(binder)
                    && term(ty, before)
                    && term(value, before)
                    && term(body, before)
                    && flags <= 1
            }
            _ => false,
        };
        if !valid {
            return false;
        }
        i += 1;
    }
    i = 0;
    while i < DECLARATIONS.len() {
        let [
            n,
            kind,
            parameters,
            ty,
            value,
            all,
            constructors,
            rules,
            metadata,
            inductive,
            dependencies,
            group,
        ] = DECLARATIONS[i];
        if !name(n)
            || n == 0
            || kind > 4
            || !sequence(parameters)
            || !term(ty, EXPRESSIONS.len() + 1)
            || (value != 0 && !term(value, EXPRESSIONS.len() + 1))
            || !sequence(all)
            || !sequence(constructors)
            || !sequence(rules)
            || !sequence(metadata)
            || !name(inductive)
            || dependencies == 0
            || dependencies as usize > DEPENDENCY_MASKS.len()
            || group as usize > GROUPS.len()
        {
            return false;
        }
        i += 1;
    }
    true
}
const _: () = assert!(canonical());
