//! @fail(tc): legacy-lean(1)
#![allow(dead_code)]

fn no_dependency_1() {}

fn g() -> Bar {
    Bar(f(32))
}

fn no_dependency_2() {}

fn f(_: u32) -> Foo {
    Foo::A
}

struct Bar(Foo);
enum Foo {
    A,
    B,
}

mod mut_rec {
/// @fail(extraction): proverif(HAX0001)
    fn f() {
        g()
    }

    fn f_2() {
        f()
    }

/// @fail(extraction): proverif(HAX0001)
    fn g() {
        f()
    }
}

mod independent_cycles {
/// @fail(extraction): proverif(HAX0001)
    fn a() {
        c()
    }
/// @fail(extraction): proverif(HAX0001)
    fn b() {
        d()
    }
/// @fail(extraction): proverif(HAX0001)
    fn c() {
        a()
    }
/// @fail(extraction): proverif(HAX0001)
    fn d() {
        b()
    }
}
