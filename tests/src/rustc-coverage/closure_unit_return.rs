#![feature(coverage_attribute)]
//@ edition: 2021

// Regression test for an inconsistency between functions that return the value
// of their trailing expression, and functions that implicitly return `()`.

/// @fail(extraction): proverif(HAX0001)
fn explicit_unit() {
    let closure = || {
        ();
    };

    drop(closure);
    () // explicit return of trailing value
}

/// @fail(extraction): proverif(HAX0001)
fn implicit_unit() {
    let closure = || {
        ();
    };

    drop(closure);
    // implicit return of `()`
}

#[coverage(off)]
fn main() {
    explicit_unit();
    implicit_unit();
}
