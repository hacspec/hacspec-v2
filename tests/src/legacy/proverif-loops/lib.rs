//! @off: fstar, lean, coq, ssprove, legacy-lean
//!
//! The ProVerif model unrolls a `for` loop over a list a bounded number of
//! times, and runs no iteration over an iterator that is not a list. A loop
//! that updates variables, or whose body may be observable, is rejected.

#[hax_lib::proverif::before("event Recorded(bitstring).")]
#[hax_lib::proverif::replace_body("event Recorded(${x}); ${x}")]
fn record(x: u8) -> u8 {
    x
}

// Observable bodies, over a list, a range with a variable bound and an
// adapter.

/// @fail(extraction): proverif(HAX0001)
fn observable_list(v: [u8; 5]) -> u8 {
    let mut s = 0;
    for x in v {
        s = record(x);
    }
    s
}

/// @fail(extraction): proverif(HAX0001)
fn observable_range(n: u8) {
    for i in 0..n {
        record(i);
    }
}

/// @fail(extraction): proverif(HAX0001)
fn observable_enumerate(v: &[u8]) -> u8 {
    let mut s = 0;
    for (_, x) in v.iter().enumerate() {
        s = record(*x);
    }
    s
}

/// @fail(extraction): proverif(HAX0001)
fn observable_map(v: &[u8]) -> Vec<u8> {
    v.iter().map(|x| record(*x)).collect()
}

// Loops that update variables, which the model would lose past the bound.

#[derive(PartialEq)]
enum State {
    Start,
    Done,
}

/// @fail(extraction): proverif(HAX0001)
fn state_past_bound() -> u8 {
    let mut s = State::Start;
    for _ in [0u8, 0, 0, 0] {
        s = State::Done;
    }
    match s {
        State::Done => record(3),
        State::Start => 0,
    }
}

/// @fail(extraction): proverif(HAX0001)
fn quiet_accumulator(v: &[u8]) -> u8 {
    let mut s = 0;
    for x in v {
        s ^= *x;
    }
    s
}

// A loop that updates nothing, with a quiet body, does nothing in the model.

fn quiet_stateless(v: &[u8]) -> u8 {
    for x in v {
        let _ = *x;
    }
    record(0)
}

// A loop that updates a variable, around a rejected loop.

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn around_rejected(v: [u8; 2]) -> u8 {
    let mut s = 0;
    for x in v {
        for _ in v {
            record(x);
        }
        s = x;
    }
    s
}
