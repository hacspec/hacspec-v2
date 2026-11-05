#![allow(dead_code)]

/// @fail(extraction): proverif(HAX0001)
pub fn f(n: u8) -> u8 {
    if n == 0 {
        0
    } else {
        n + f(n - 1)
    }
}
