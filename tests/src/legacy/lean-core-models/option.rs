// Tests for core models in lean
#![allow(dead_code)]
#![allow(unused_variables)]

struct S {
    f1: u32,
}

enum E {
    C(u32),
}

impl Default for S {
    fn default() -> Self {
        S { f1: 42 }
    }
}

/// @fail(extraction): proverif(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001)
fn test() {
    let o1 = Option::Some(4);
    let o2: Option<i32> = None;

    let o3 = o1.clone().is_some_and(|x| x == 0);
    let o3 = o1.clone().is_none_or(|x| x == 0);

    let o4 = Some(0).unwrap();
    let o5 = Some(0).unwrap_or(9);
    let o6 = Some(0).unwrap_or_else(|| 9);
    let o7 = Option::None::<S>.unwrap_or_default();

    // maps
    let o8 = Some(0).map(|x| x + 1);
    let o9 = Some(1).map_or(9, |x| x + 1);
    let o10 = Some(2).map_or_else(|| 9, |x| x + 1);

    // options and  results
    let o11 = Some(3).ok_or(E::C(0));
    let o12 = Some(1).ok_or_else(|| E::C(1));

    let o13 = None.and_then(|x: u32| Some(x));
    let o14 = Some(S { f1: 9 }).take();

    // tests
    let o15 = Some(1).is_some();
    let o16 = Some(2).is_none();
    let o17 = Some(3).expect("Should be Some");
    let o18 = Some(4).unwrap();
}
