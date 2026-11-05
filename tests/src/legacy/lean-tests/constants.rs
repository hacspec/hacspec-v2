// Tests on constants
#![allow(dead_code)]
#![allow(unused_variables)]

const C1: u32 = 5678;
const C2: u32 = C1 + 1;
const C3: u32 = if true { 890 } else { 9 / 0 };

const fn computation(x: u32) -> u32 {
    x + x + 1
}

const C4: u32 = computation(C1) + C2;
const C5: (u32, u32) = (0 + 0, 0);
const C6: [u32; 1] = [0];

fn test() {
    let x = C1 + 1;
    let y = C2 + C3;
    let z = C4 - C3;
}

mod const_parameters {

    /// Function with const parameter
/// @fail(extraction): proverif(HAX0001)
    fn f<const N: usize>() -> usize {
        N
    }

    const N0: usize = 1;
    const N1: usize = 10;

    fn test() {
        let _ = f::<9>() + f::<N1>();
    }

    /// Trait definition
    trait T<const N_TRAIT: usize> {
        fn f<const N_FIELD: usize>(&self) -> usize;
    }

    /// Struct definition
    struct S<const N: usize>(u32);

/// @fail(extraction): proverif(HAX0001, HAX0001)
    impl<const N_TRAIT: usize> T<N_TRAIT> for S<N_TRAIT> {
        fn f<const N_FIELD: usize>(&self) -> usize {
            N_TRAIT - N_FIELD
        }
    }

/// @fail(extraction): proverif(HAX0001, HAX0001)
    fn test2<const N2: usize, A: T<N2>>(x: A) -> usize {
        let s = S::<N1>(9);
        let _ = s.f::<1>() + x.f::<{ 1 + N1 }>();
        let s = S::<{ 1 + 2 }>(9);
        x.f::<{ 2 + 2 }>()
    }
}
