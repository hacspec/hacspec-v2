//! @fail(tc): legacy-lean(2)
//! A `return` in a closure exits only the closure.

#![allow(dead_code)]

/// @fail(extraction): coq(HAX0001, HAX0001), ssprove(HAX0001), proverif(HAX0008)
fn in_while_condition(n: u8) -> u8 {
    let mut i = 0u8;
    while {
        let c = |x: u8| -> bool {
            if x == 3 {
                return false;
            }
            true
        };
        c(i) && i < n
    } {
        i += 1;
    }
    i
}

/// @fail(extraction): coq(HAX0001, HAX0001), ssprove(HAX0001), proverif(HAX0008)
fn in_loop_body(n: u8) -> u8 {
    let mut i = 0u8;
    while i < n {
        let c = |x: u8| -> bool {
            if x == 3 {
                return false;
            }
            true
        };
        if c(i) {
            i += 1;
        } else {
            i += 2;
        }
    }
    i
}

/// @fail(extraction): proverif(HAX0008)
fn nested(i: u8) -> u8 {
    let c = |x: u8| -> u8 {
        let d = |y: u8| -> u8 {
            if y == 0 {
                return 7;
            }
            y
        };
        if x == 3 {
            return d(x);
        }
        x + 1
    };
    for j in 0..i {
        if c(j) == 9 {
            return 4;
        }
    }
    c(i)
}
