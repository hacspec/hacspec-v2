//! @off: fstar, lean, coq, ssprove, legacy-lean
//! @cli: into proverif --result-errors
//!
//! Under `--result-errors`, `unwrap` and `transpose` have models of their own,
//! not the identity, so they are neither dropped nor warned of.

#[hax_lib::proverif::before("event Recorded(bitstring).")]
#[hax_lib::proverif::replace_body("event Recorded(${x}); ${x}")]
fn record(x: u8) -> u8 {
    x
}

fn check(x: u8) -> Result<u8, u8> {
    if x == 0 { Err(0) } else { Ok(x) }
}

fn unwrap_compared(x: u8) -> u8 {
    let v = check(x).unwrap();
    if v == 5 { record(1) } else { 0 }
}
