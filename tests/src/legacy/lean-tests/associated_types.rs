mod basic {
    trait Iterable {
        type Item;
        fn first(&self) -> Self::Item;
    }

/// @fail(extraction): proverif(HAX0001)
    fn just_the_first<I: Iterable>(iter: I) -> I::Item {
        iter.first()
    }

/// @fail(extraction): proverif(HAX0001)
    fn first_plus_1<I: Iterable<Item = i32>>(iter: I) -> i32 {
        iter.first() + 1
    }

    impl Iterable for bool {
        type Item = i32;
        fn first(&self) -> i32 {
            3
        }
    }

    fn a() {
        first_plus_1(true);
    }
}

mod projection {
    trait T1 {
        type A1;
    }

    trait T2 {
        type A2: T1;
        fn f() -> <Self::A2 as T1>::A1;
    }
}

mod multiple_associated_types {
    trait Pair {
        type First;
        type Second;
        fn first(&self) -> Self::First;
        fn second(&self) -> Self::Second;
    }

/// @fail(extraction): proverif(HAX0001, HAX0001)
    fn get_both<P: Pair>(pair: P) -> (P::First, P::Second) {
        (pair.first(), pair.second())
    }

/// @fail(extraction): ssprove(HAX0001)
    impl Pair for (i32, bool) {
        type First = i32;
        type Second = bool;
        fn first(&self) -> i32 {
            self.0
        }
        fn second(&self) -> bool {
            self.1
        }
    }

    fn b() {
        let pair = (42, true);
        let both = get_both(pair);
    }

/// @fail(extraction): proverif(HAX0001)
    fn get_first_as_i32<P: Pair<First = i32>>(pair: P) -> i32 {
        pair.first()
    }
}

mod multiple_projections {
    trait FnOnce<T> {
        type Output;
    }

    pub fn func<T, U, D, F>(d: D, f: F, u: U)
    where
        F: FnOnce<T, Output = U>,
        D: FnOnce<T, Output = U>,
    {
    }
}
