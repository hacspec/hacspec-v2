//! @off: fstar, lean, coq, ssprove, legacy-lean
//!
//! A library function without a model is declared as an abstract `fun`,
//! whose value no pattern matches, as the lowering of a `&mut` argument and a
//! `match` need: every such function is warned of.

fn take_option(mut o: Option<u8>) -> Option<u8> {
    o.take()
}

fn replace_value(mut x: u8) -> u8 {
    core::mem::replace(&mut x, 1)
}

fn pop_last(mut v: Vec<u8>) -> Option<u8> {
    v.pop()
}

fn match_unmodelled(v: Vec<u8>) -> u8 {
    match v.first() {
        Some(x) => *x,
        None => 0,
    }
}

// A value destructured after a crate function returns it.

fn head(v: &[u8]) -> Option<&u8> {
    v.first()
}

fn through_helper(v: &[u8]) -> u8 {
    match head(v) {
        Some(x) => *x,
        None => 0,
    }
}

// A crate function taking a `&mut` is extracted, so it is not warned of.

fn bump(x: &mut u8) -> u8 {
    *x += 1;
    *x
}

fn call_bump(mut x: u8) -> u8 {
    bump(&mut x)
}

// A `pv_extern` function and an opaque constant, whose values match no
// pattern.

#[hax_lib::pv_extern]
fn lookup(x: u8) -> Option<u8> {
    Some(x)
}

fn match_extern(x: u8) -> u8 {
    match lookup(x) {
        Some(v) => v,
        None => 0,
    }
}

#[hax_lib::opaque]
const DEFAULT: Option<u8> = Some(1);

fn match_opaque_const() -> u8 {
    match DEFAULT {
        Some(v) => v,
        None => 0,
    }
}
