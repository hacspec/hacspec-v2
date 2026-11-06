//! @off: fstar, lean, coq, ssprove, legacy-lean
//!
//! Control flow ProVerif has no direct form for: early returns, `while` and
//! `loop`, `break` and `continue` in a `for`, nested loops, `let … else` and
//! `if let` chains.
#![allow(dead_code)]

fn early_return(x: u8) -> u8 {
    if x == 0 {
        return 1;
    }
    x
}

fn return_in_match(x: Option<u8>) -> u8 {
    let v = match x {
        Some(v) => v,
        None => return 0,
    };
    v
}

fn let_else(x: Option<u8>) -> u8 {
    let Some(v) = x else { return 0 };
    v
}

fn question_mark_option(x: Option<u8>, y: Option<u8>) -> Option<u8> {
    let a = x?;
    let b = y?;
    Some(a ^ b)
}

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn if_let_chain(x: Option<u8>, y: Option<u8>) -> u8 {
    if let Some(a) = x
        && let Some(b) = y
    {
        a ^ b
    } else {
        0
    }
}

fn nested_for(xs: [u8; 2], ys: [u8; 2]) -> u8 {
    let mut acc = 0;
    for x in xs {
        for y in ys {
            acc = acc ^ x ^ y;
        }
    }
    acc
}

fn for_break(xs: [u8; 3]) -> u8 {
    let mut acc = 0;
    for x in xs {
        if x == 0 {
            break;
        }
        acc = acc ^ x;
    }
    acc
}

/// @fail(extraction): proverif(HAX0001)
fn for_return(xs: [u8; 3]) -> u8 {
    for x in xs {
        if x == 0 {
            return 1;
        }
    }
    0
}

/// @fail(extraction): proverif(HAX0001)
fn while_loop(mut x: u8) -> u8 {
    while x > 0 {
        x = x - 1;
    }
    x
}

/// @fail(extraction): proverif(HAX0001)
fn loop_break_value(x: u8) -> u8 {
    loop {
        break x;
    }
}

const A: Option<u8> = Some(1);

// A constant whose body cannot be translated is marked.
/// @fail(extraction): proverif(HAX0001, HAX0001)
const CHAINED: u8 = if let Some(a) = A
    && let Some(b) = A
{
    a ^ b
} else {
    0
};
