//! @fail(extraction): proverif(HAX0001)
//! @off: fstar, lean, coq, ssprove, legacy-lean
//!
//! The ProVerif model evaluates operands, record fields and the operands of
//! `&&` and `||` in Rust order, so the events of hand-written models keep
//! their order. Code whose order the model cannot keep is rejected.

#[derive(PartialEq)]
enum Error {
    Invalid,
    Other,
}

#[hax_lib::proverif::before("event Recorded(bitstring).")]
#[hax_lib::proverif::replace_body("event Recorded(${x}); ${x}")]
fn record(x: u8) -> u8 {
    x
}

fn check(x: u8) -> Result<u8, Error> {
    if x == 0 { Err(Error::Invalid) } else { Ok(x) }
}

// Observable operands, which the model evaluates in Rust order.

fn two_records(a: u8, b: u8) -> u8 {
    a + b
}

fn reordered_operands() -> u8 {
    two_records(record(1), {
        let y = record(2);
        y
    })
}

// Fields written out of declaration order, which the model evaluates in
// Rust order.

struct Pair {
    a: u8,
    b: u8,
}

fn reordered_fields() -> Result<u8, Pair> {
    Err(Pair {
        b: record(2),
        a: record(1),
    })
}

fn ordered_fields() -> (Pair, (u8, u8)) {
    (
        Pair {
            a: record(1),
            b: record(2),
        },
        (record(3), record(4)),
    )
}

// Operands that hoisting would move above observable ones: a `?`, an
// assignment; the second operand of `&&`; and the base of a struct update.

fn question_mark_operand() -> Result<u8, Error> {
    Ok(two_records(record(1), check(record(2))?))
}

fn assign_operand(c: bool) -> u8 {
    let mut n = 0;
    two_records(
        record(1),
        if c {
            n = record(2);
            n
        } else {
            0
        },
    )
}

fn lazy_and(x: u8) -> bool {
    x == 0 && {
        let y = record(2);
        y == 0
    }
}

struct Triple {
    a: u8,
    b: u8,
    c: u8,
}

fn make_triple() -> Triple {
    Triple {
        a: record(5),
        b: 0,
        c: 0,
    }
}

fn update_base() -> Triple {
    Triple {
        a: record(1),
        ..make_triple()
    }
}

// A call taking a `&mut`, with a `?` in another argument.

fn bump(x: &mut u8, y: u8) -> u8 {
    *x += y;
    *x
}

/// @fail(extraction): proverif(HAX0001)
fn mut_temporary_operand() -> Result<u8, Error> {
    Ok(bump(&mut record(1), check(record(2))?))
}

// Observable calls in a place that is assigned or borrowed mutably.

/// @fail(extraction): proverif(HAX0001)
fn observable_index_assign() -> u8 {
    let mut v = [0u8; 2];
    v[record(1) as usize] = record(2);
    v[0]
}

/// @fail(extraction): proverif(HAX0001)
fn observable_index_borrow() -> u8 {
    let mut v = [0u8; 2];
    bump(&mut v[record(1) as usize], 0)
}

// A tuple struct with its fields named out of order.

struct Tup(u8, u8);

fn tuple_named_out_of_order() -> Tup {
    Tup {
        1: record(2),
        0: record(1),
    }
}

// A closure before a hoisted operand.

#[hax_lib::pv_inline]
fn apply_inline(f: fn(u8) -> u8, x: u8) -> u8 {
    f(x)
}

fn closure_before_hoisted() -> Result<u8, Error> {
    Ok(apply_inline(|y| record(y), check(record(2))?))
}

// A struct-update base whose fields are all overwritten, and an unused read
// of a constant whose model is observable.

fn make_pair() -> Pair {
    Pair {
        a: record(3),
        b: 0,
    }
}

fn overwritten_base() -> Result<u8, Pair> {
    Err(Pair {
        a: 0,
        b: 0,
        ..make_pair()
    })
}

#[hax_lib::proverif::replace(
    "event Const_read. letfun ${READ_CONST}() = event Const_read; nat_0."
)]
const READ_CONST: u8 = 0;

fn unused_constant_read() -> Result<u8, Error> {
    let _unused = READ_CONST;
    Err(Error::Invalid)
}

// Calls taking a `&mut`, which the model lowers to a `let` that updates the
// place.

fn record_mut(x: &mut u8) -> u8 {
    *x = record(*x);
    *x
}

fn mut_call_operand() -> u8 {
    let mut n = 2;
    two_records(record(1), record_mut(&mut n))
}

fn mut_call_lazy(x: u8) -> bool {
    let mut n = 2;
    x == 0 && record_mut(&mut n) == 0
}

fn mut_place_operand() -> Result<u8, Error> {
    let mut t = 1;
    Ok(bump(&mut t, check(record(2))?))
}

// A constant passed to an inlined function that uses it twice.

#[hax_lib::pv_inline]
fn twice(x: u8) -> u8 {
    x + x
}

fn inline_constant() -> u8 {
    twice(READ_CONST)
}

// Calls taking a `&mut` in a branch of an operand, after a borrowed element,
// and in an unchecked function.

fn bump3(x: &mut u8, y: &u8, z: u8) -> u8 {
    *x += *y + z;
    *x
}

fn mut_call_in_branch(c: bool) -> u8 {
    let mut n = 2;
    two_records(record(1), if c { record_mut(&mut n) } else { 0 })
}

fn mut_call_in_nested_lazy(x: u8, c: bool) -> bool {
    let mut n = 2;
    x == 0 && (c || record_mut(&mut n) == 0)
}

/// @fail(extraction): proverif(HAX0001)
fn mut_call_after_borrowed_element() -> u8 {
    let mut n = 0;
    let mut m = 2;
    let v = [0u8; 2];
    bump3(&mut n, &v[record(1) as usize], record_mut(&mut m))
}

/// @fail(extraction): proverif(HAX0001)
#[hax_lib::pv_unchecked_results]
fn unchecked_mut_order() -> Result<u8, Error> {
    let mut t = 1;
    Ok(bump3(&mut t, &record(1), check(record(2))?))
}

// An index computed by a trait impl of the crate.

struct IndexTag;

impl From<IndexTag> for usize {
    fn from(_: IndexTag) -> usize {
        record(0) as usize
    }
}

/// @fail(extraction): proverif(HAX0001)
fn index_through_trait() -> u8 {
    let mut a = [0u8; 2];
    bump(&mut a[usize::from(IndexTag)], 1)
}

// Operands holding a loop, before a `?` and before a call taking a `&mut`.

/// @fail(extraction): proverif(HAX0001)
fn loop_block_before_question(c: u8) -> Result<u8, Error> {
    let mut t = 1;
    Ok(bump3(
        &mut t,
        &{
            for _ in 0..1 {}
            record(1)
        },
        check(c)?,
    ))
}

fn loop_block_before_mut_call() -> u8 {
    let mut n = 2;
    two_records(
        {
            for _ in 0..1 {}
            record(1)
        },
        record_mut(&mut n),
    )
}

// A compound assignment whose value mutates the assigned variable.

struct Counter {
    c: u8,
}

impl Counter {
    fn step(&mut self) -> u8 {
        self.c = record(self.c);
        1
    }
}

/// @fail(extraction): proverif(HAX0001)
fn compound_with_mut_call(mut s: Counter) -> u8 {
    s.c += s.step();
    s.c
}

// A struct update whose field mutates the base, an assignment whose value
// mutates the index, a call taking a `&mut` in a guard, and an iterator
// computed once for `any`.

struct St {
    id: u8,
    n: u8,
}

impl St {
    fn fresh(&mut self) -> u8 {
        self.n = record(self.n);
        self.n
    }
}

fn update_mutating_base(mut st: St) -> St {
    St {
        id: st.fresh(),
        ..st
    }
}

fn set_index(i: &mut usize) -> u8 {
    *i = 1;
    0
}

/// @fail(extraction): proverif(HAX0001)
fn assign_mutating_index() -> u8 {
    let mut a = [0u8; 2];
    let mut i = 0;
    a[i] = set_index(&mut i);
    a[1]
}

fn take(n: &mut u8) -> bool {
    *n = record(*n);
    true
}

/// @fail(extraction): proverif(HAX0001)
fn mut_call_in_guard(o: Option<u8>) -> u8 {
    let mut n = 0;
    match o {
        Some(_) if take(&mut n) => 1,
        _ => 0,
    }
}

fn make_items(m: u8) -> [u8; 2] {
    [record(m), 0]
}

fn any_on_computed(m: u8) -> bool {
    make_items(m).into_iter().any(|x| x == 1)
}

// Assignments whose value assigns a variable of the place.

/// @fail(extraction): proverif(HAX0001)
fn assign_value_assigns_index() -> u8 {
    let mut a = [1u8; 2];
    let mut i = 0;
    a[i] = {
        i = 1;
        0
    };
    record(a[1])
}

/// @fail(extraction): proverif(HAX0001)
fn compound_value_assigns(mut x: u8) -> u8 {
    x += {
        x = 2;
        1
    };
    x
}

// Reads before a later operand writes the variable.

fn step_mut(x: &mut u8) -> Result<u8, Error> {
    *x = record(*x);
    check(*x)
}

fn read_before_write(mut x: u8) -> Result<u8, Error> {
    Ok(two_records(x, step_mut(&mut x)?))
}

fn update_reads_before_write(mut st: St) -> St {
    St {
        n: st.n,
        id: st.fresh(),
    }
}

/// @fail(extraction): proverif(HAX0001)
fn index_written_by_argument() -> u8 {
    let mut a = [0u8; 2];
    let mut i = 0;
    let r = bump(&mut a[i], set_index(&mut i));
    r
}

// An index that updates the indexed array, which Rust reads after the index.

fn next_index(a: &mut [u8; 2]) -> usize {
    a[0] = record(1);
    0
}

/// @fail(extraction): proverif(HAX0001)
fn index_after_update() -> u8 {
    let mut a = [0u8; 2];
    a[next_index(&mut a)]
}

fn index_bound_first() -> u8 {
    let mut a = [0u8; 2];
    let i = next_index(&mut a);
    a[i]
}

// Writes through a reference and through `self`, which a later operand makes.

fn write_through(p: &mut u8) -> u8 {
    two_records(*p, {
        *p = record(3);
        4
    })
}

impl St {
    fn write_field(&mut self) -> u8 {
        two_records(self.n, {
            self.n = record(1);
            2
        })
    }
}

// A value that Rust evaluates before an index that may fail.

/// @fail(extraction): proverif(HAX0001)
fn value_before_failing_index(mut v: [u8; 2], o: Option<usize>) -> [u8; 2] {
    v[o.unwrap()] = record(1);
    v
}

fn index_bound_before_value(mut v: [u8; 2], o: Option<usize>) -> [u8; 2] {
    let i = o.unwrap();
    v[i] = record(1);
    v
}

// An index that may fail, which Rust evaluates after an earlier argument, a
// struct-update base that may fail, which Rust evaluates after the fields,
// and an index that updates a variable the value reads.

fn set_at(x: u8, slot: &mut u8) -> u8 {
    *slot = x;
    x
}

/// @fail(extraction): proverif(HAX0001)
fn mut_index_after_event(mut a: [u8; 2], o: Option<usize>) -> u8 {
    set_at(record(1), &mut a[o.unwrap()])
}

fn update_failing_base(o: Option<Pair>) -> Pair {
    Pair {
        a: record(1),
        ..o.unwrap()
    }
}

/// @fail(extraction): proverif(HAX0001)
fn index_replaces_value(mut a: [u8; 2], mut i: usize) -> [u8; 2] {
    a[core::mem::replace(&mut i, 1)] = i as u8;
    a
}

// `&mut` temporaries, which the lowering of `&mut` does not write back.

fn mk(x: u8) -> u8 {
    x
}

fn set2(_x: &mut u8, slot: &mut u8) {
    *slot = 1;
}

/// @fail(extraction): proverif(HAX0001)
fn temporary_before_failing_index(mut a: [u8; 2], o: Option<usize>) -> [u8; 2] {
    set2(&mut mk(record(1)), &mut a[o.unwrap()]);
    a
}

fn temporary_before_variable(mut a: u8) -> u8 {
    set2(&mut mk(7), &mut a);
    a
}

fn temporary_bound(mut a: u8) -> u8 {
    let mut t = mk(7);
    set2(&mut t, &mut a);
    a
}

// An unsized temporary, and a function returning `((),)`, with a temporary.

fn set_from(_x: &mut [u8], slot: &mut u8) {
    *slot = 1;
}

fn unsized_temporary(mut a: u8) -> u8 {
    set_from(&mut [7u8], &mut a);
    a
}

fn set_tuple(_x: &mut u8, slot: &mut u8) -> ((),) {
    *slot = 1;
    ((),)
}

fn tuple_unit_temporary(mut a: u8) -> u8 {
    set_tuple(&mut mk(7), &mut a);
    a
}

// A generic return type instantiated with `()`.

fn pass<T>(slot: &mut u8, t: T) -> T {
    *slot = 1;
    t
}

/// @fail(extraction): proverif(HAX0001)
fn unit_instance(mut a: u8) -> u8 {
    pass(&mut a, ());
    a
}

// A library call returning `()` with a `&mut` temporary.

fn build_vec() -> Vec<u8> {
    vec![5]
}

fn append_temporary() -> Vec<u8> {
    let mut v = Vec::new();
    v.append(&mut build_vec());
    v
}
