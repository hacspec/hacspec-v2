#![allow(dead_code)]
#![allow(unused_variables)]

/// @fail(extraction): proverif(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001)
fn test() -> u32 {
    let f_1 = |_: u32| 9;
    let f_2 = |x: u32, y: u32| x + y;
    let f_2_tuple = |(x, y): (u32, u32)| x + y;
    f_1(0) + f_2(1, 2) + f_2_tuple((1, 2))
}
