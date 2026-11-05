//! @off: fstar, lean, coq, ssprove, legacy-lean
//!
//! A conversion the library models as the identity is warned of when its
//! types are represented differently, or when it narrows an integer.

#[hax_lib::proverif::before("event Recorded(bitstring).")]
#[hax_lib::proverif::replace_body("event Recorded(${x}); ${x}")]
fn record(x: u8) -> u8 {
    x
}

fn into_option(x: u8) -> u8 {
    let o: Option<u8> = x.into();
    match o {
        Some(v) => record(v),
        None => 0,
    }
}

fn bool_into(b: bool) -> u8 {
    let n: u8 = b.into();
    record(n)
}

fn widening(x: u8) -> u32 {
    x.into()
}

fn from_bytes() -> u8 {
    let n = u32::from_be_bytes([0, 0, 0, 1]);
    if n == 1 { record(1) } else { 0 }
}

fn str_as_bytes(s: &str) -> usize {
    s.as_bytes().len()
}

fn try_into_option(x: u8) -> u8 {
    let o: Option<u8> = x.try_into().unwrap();
    match o {
        Some(v) => record(v),
        None => 0,
    }
}

// A conversion of a branch, inside a branch.

fn converted_branch(c: bool, x: u8) -> Option<u8> {
    if c {
        Option::from(if x == 1 { 2 } else { 3 })
    } else {
        record(0);
        None
    }
}

// Same representations: not warned of.

fn transposed(x: Option<Result<u8, u8>>) -> Result<Option<u8>, u8> {
    x.transpose()
}

fn string_from(s: &str) -> String {
    String::from(s)
}

fn vec_from(a: [u8; 2]) -> Vec<u8> {
    Vec::from(a)
}
