//! @off: fstar, lean, coq, ssprove, legacy-lean
//!
//! A diverging expression, such as a panic with a message or a call of a
//! function returning `!`, is evaluated before the trace ends.

#[hax_lib::proverif::before("event Recorded(bitstring).")]
#[hax_lib::proverif::replace_body("event Recorded(${x}); ${x}")]
fn record(x: u8) -> u8 {
    x
}

fn panic_arg(x: u8) -> u8 {
    if x == 0 {
        panic!("bad {}", record(1))
    }
    x
}

fn alert(x: u8) -> ! {
    record(x);
    panic!()
}

fn diverging_call(o: Option<u8>) -> u8 {
    match o {
        Some(v) => v,
        None => alert(9),
    }
}
