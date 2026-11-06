//! @off: fstar, lean, coq, ssprove, legacy-lean
//! @cli: into proverif --keep-trait-calls **::Kept::**
//!
//! The default Result model: a `Result` is its `Ok` payload, producing an
//! `Err` ends the trace, and arms that need an `Err` are dropped. Code that
//! goes on after an `Err` is rejected, and so is a `Result` that is not
//! returned or consumed at once, even if it is propagated later.
//! `proverif-result-errors` extracts the same items with `--result-errors`.

#[derive(PartialEq)]
enum Error {
    Invalid,
    Other,
}

fn check(x: u8) -> Result<u8, Error> {
    if x == 0 { Err(Error::Invalid) } else { Ok(x) }
}

fn question_mark(x: u8) -> Result<u8, Error> {
    let y = check(x)?;
    Ok(y)
}

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn err_arms_first(r: Result<u8, Error>) -> u8 {
    match r {
        Err(Error::Invalid) => 1,
        Err(_) => 2,
        Ok(v) => v,
    }
}

/// @fail(extraction): proverif(HAX0001)
fn nested_err(o: Option<Result<u8, Error>>) -> u8 {
    match o {
        Some(Err(_)) => 0,
        Some(Ok(v)) => v,
        None => 1,
    }
}

/// @fail(extraction): proverif(HAX0001)
fn is_ok(r: Result<u8, Error>) -> bool {
    r.is_ok()
}

fn map_err(r: Result<u8, u8>) -> Result<u8, u16> {
    r.map_err(|e| e as u16)
}

// `transpose` swaps the `Option` and the `Result`.
fn transpose(x: Option<Result<u8, u8>>) -> Result<Option<u8>, u8> {
    x.transpose()
}

// Going on after an `Err`.

/// @fail(extraction): proverif(HAX0001)
fn if_let_else(r: Result<u8, Error>) -> u8 {
    if let Ok(v) = r { v } else { 0 }
}

/// @fail(extraction): proverif(HAX0001)
fn wildcard_arm(r: Result<u8, Error>) -> u8 {
    match r {
        Ok(v) => v,
        _ => 0,
    }
}

/// @fail(extraction): proverif(HAX0001)
fn discarded(x: u8) -> u8 {
    let _ = check(x);
    x
}

fn unused_param(_r: Result<u8, Error>, x: u8) -> u8 {
    x
}

/// @fail(extraction): proverif(HAX0001)
fn used_on_one_path(c: bool, x: u8) -> Result<u8, Error> {
    let r = check(x);
    if c { r } else { Ok(0) }
}

// Propagating an `Err`.

fn propagating_arms(r: Result<u8, Error>) -> Result<u8, Error> {
    match r {
        Ok(v) => Ok(v + 1),
        Err(e) => Err(e),
    }
}

fn panicking_arm(r: Result<u8, Error>) -> u8 {
    match r {
        Ok(v) => v,
        Err(_) => panic!(),
    }
}

fn wildcard_err(r: Result<u8, Error>) -> Result<u8, Error> {
    match r {
        Ok(v) => Ok(v),
        _ => Err(Error::Other),
    }
}

// A `Result` bound, stored or passed before it is consumed.

/// @fail(extraction): proverif(HAX0001)
fn bound_then_propagated(x: u8) -> Result<u8, Error> {
    let r = check(x);
    let v = r?;
    Ok(v)
}

/// @fail(extraction): proverif(HAX0001)
fn in_tuple(x: u8) -> (u8, Result<u8, Error>) {
    (x, check(x))
}

/// @fail(extraction): proverif(HAX0001)
fn from_tuple(x: u8) -> Result<u8, Error> {
    let (y, r) = in_tuple(x);
    let v = r?;
    Ok(y + v)
}

/// @fail(extraction): proverif(HAX0001)
fn passed(x: u8) -> Result<u8, Error> {
    question_mark_of(check(x))
}

fn question_mark_of(r: Result<u8, Error>) -> Result<u8, Error> {
    let v = r?;
    Ok(v)
}

// Errors of hand-written models.

#[hax_lib::proverif::replace_body("hax_result_ok(x)")]
fn modelled(x: u8) -> Result<u8, Error> {
    check(x)
}

/// @fail(extraction): proverif(HAX0001)
fn match_any(x: u8) -> u8 {
    match modelled(x) {
        Ok(v) => v,
        Err(_) => 0,
    }
}

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn match_variant(x: u8) -> u8 {
    match modelled(x) {
        Ok(v) => v,
        Err(Error::Invalid) => 1,
        Err(_) => 2,
    }
}

fn forwarded(x: u8) -> Result<u8, Error> {
    let v = modelled(x)?;
    Ok(v)
}

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn match_forwarded(x: u8) -> u8 {
    match forwarded(x) {
        Ok(v) => v,
        Err(Error::Invalid) => 1,
        Err(Error::Other) => 2,
    }
}

fn error_code(e: Error) -> u8 {
    match e {
        Error::Invalid => 1,
        Error::Other => 2,
    }
}

/// @fail(extraction): proverif(HAX0001)
fn inspected(x: u8) -> u8 {
    match modelled(x) {
        Ok(v) => v,
        Err(e) => error_code(e),
    }
}

#[hax_lib::opaque]
fn opaque_result(x: u8) -> Result<u8, Error> {
    check(x)
}

fn use_opaque(x: u8) -> Result<u8, Error> {
    let v = opaque_result(x)?;
    Ok(v)
}

#[hax_lib::pv_constructor]
fn encode(x: u8) -> u8 {
    x
}

#[hax_lib::pv_inverse_of(encode)]
fn decode(b: u8) -> Result<u8, Error> {
    check(b)
}

fn round_trip(x: u8) -> Result<u8, Error> {
    decode(encode(x))
}

/// @fail(extraction): proverif(HAX0001)
fn decode_or_zero(b: u8) -> u8 {
    match decode(b) {
        Ok(v) => v,
        Err(_) => 0,
    }
}

// Observable calls while an `Err` is pending.

#[hax_lib::proverif::before("event Recorded(bitstring).")]
#[hax_lib::proverif::replace_body("event Recorded(${x}); ${x}")]
fn record(x: u8) -> u8 {
    x
}

/// @fail(extraction): proverif(HAX0001)
fn err_arm_effect(r: Result<u8, Error>) -> Result<u8, Error> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => {
            record(0);
            Err(e)
        }
    }
}

/// @fail(extraction): proverif(HAX0001)
fn effect_before_propagation(x: u8) -> Result<u8, Error> {
    let r = check(x);
    record(x);
    let v = r?;
    Ok(v)
}

/// @fail(extraction): proverif(HAX0001)
fn effect_after_result(x: u8) -> (Result<u8, Error>, u8) {
    (check(x), record(x))
}

fn effect_after_propagation(x: u8) -> Result<u8, Error> {
    let v = check(x)?;
    Ok(record(v))
}

struct Out {
    n: u8,
    r: Result<u8, Error>,
}

/// @fail(extraction): proverif(HAX0001)
fn produce(x: u8) -> Out {
    Out { n: x, r: check(x) }
}

/// @fail(extraction): proverif(HAX0001)
fn rest_pattern(x: u8) -> u8 {
    let Out { n, .. } = produce(x);
    n
}

/// @fail(extraction): proverif(HAX0001)
fn all_fields(x: u8) -> Result<u8, Error> {
    let Out { n, r } = produce(x);
    let v = r?;
    Ok(n + v)
}

// Error values of hand-written models, kept through other values.

/// @fail(extraction): proverif(HAX0001)
fn equal_err(x: u8) -> u8 {
    if modelled(x) == Err(Error::Invalid) { 1 } else { 0 }
}

/// @fail(extraction): proverif(HAX0001, HAX0001, HAX0001, HAX0001)
fn repacked(x: u8) -> u8 {
    let swapped: Result<Error, ()> = match modelled(x) {
        Ok(_) => Err(()),
        Err(e) => Ok(e),
    };
    match swapped {
        Ok(Error::Invalid) => 1,
        Ok(Error::Other) => 2,
        Err(_) => 3,
    }
}

#[hax_lib::pv_extern]
fn derive(k: u8) -> Result<u8, Error> {
    check(k)
}

fn use_derive(k: u8) -> Result<u8, Error> {
    let v = derive(k)?;
    Ok(v)
}

#[hax_lib::proverif::replace_body("crypto__hash(x)")]
fn hashed(x: u8) -> Result<u8, Error> {
    check(x)
}

fn use_hashed(x: u8) -> Result<u8, Error> {
    let v = hashed(x)?;
    Ok(v)
}

enum Wrapped {
    E(Error),
}

fn map_err_constructor(x: u8) -> Result<u8, Wrapped> {
    let v = check(x).map_err(Wrapped::E)?;
    Ok(v)
}

#[hax_lib::proverif::replace_body("e")]
fn make_error(e: Error) -> Error {
    e
}

fn err_payload_effect(x: u8) -> Result<u8, Error> {
    if x == 0 { Err(make_error(Error::Invalid)) } else { Ok(x) }
}

/// @fail(extraction): proverif(HAX0001, HAX0001, HAX0001)
fn nested_unwrap(x: u8) -> u8 {
    let outer: Result<Result<u8, Error>, ()> = Ok(modelled(x));
    match outer.unwrap() {
        Ok(v) => v,
        Err(Error::Invalid) => 1,
        Err(Error::Other) => 2,
    }
}

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn nested_ok(x: u8) -> u8 {
    let outer: Result<Result<u8, Error>, ()> = Ok(modelled(x));
    match outer.ok() {
        Some(Ok(v)) => v,
        Some(Err(Error::Invalid)) => 1,
        _ => 2,
    }
}

fn identity<T>(x: T) -> T {
    x
}

/// @fail(extraction): proverif(HAX0001, HAX0001, HAX0001)
fn through_generic(x: u8) -> u8 {
    match identity(modelled(x)) {
        Ok(v) => v,
        Err(Error::Invalid) => 1,
        Err(Error::Other) => 2,
    }
}

// Guards and arms that see an `Err`.

/// @fail(extraction): proverif(HAX0001)
fn guard_falls_through(o: Option<u8>) -> u8 {
    match o {
        Some(v) if let Ok(y) = check(v) => y,
        _ => 0,
    }
}

fn err_taken_first(x: u8) -> Result<u8, Error> {
    if let Err(e) = check(x) {
        return Err(e);
    }
    Ok(x)
}

fn err_arm_then_catch_all(x: u8) -> u8 {
    match check(x) {
        Err(_) => panic!(),
        Ok(1) => 1,
        _ => 2,
    }
}

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn two_pending(x: u8, y: u8) -> Result<u8, Error> {
    let a = check(x);
    let b = check(y);
    let u = a?;
    let v = b?;
    Ok(u + v)
}

/// @fail(extraction): proverif(HAX0001)
fn early_return_before_use(c: bool, x: u8) -> Result<u8, Error> {
    let r = check(x);
    if c {
        return Err(Error::Other);
    }
    r
}

/// @fail(extraction): proverif(HAX0001)
fn pure_loop_before_use(x: u8) -> Result<u8, Error> {
    let r = check(x);
    let mut n = 0;
    for i in 0..x {
        n += i;
    }
    let v = r?;
    Ok(v + n)
}

// Error values kept in other values.

/// @fail(extraction): proverif(HAX0001, HAX0001, HAX0001)
fn ok_or_repacked(x: u8) -> u8 {
    let opt = match modelled(x) {
        Err(e) => Some(e),
        Ok(_) => None,
    };
    let swapped: Result<Error, ()> = opt.ok_or(());
    match swapped {
        Ok(Error::Invalid) => 1,
        Ok(Error::Other) => 2,
        Err(_) => 3,
    }
}

#[hax_lib::proverif::replace(
    "letfun ${MODELLED_CONST}() = hax_result_err(rust_primitives__hax__Tuple0__Tuple0)."
)]
const MODELLED_CONST: Result<u8, Error> = Err(Error::Invalid);

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn match_const() -> u8 {
    match MODELLED_CONST {
        Ok(v) => v,
        Err(Error::Invalid) => 1,
        Err(Error::Other) => 2,
    }
}

/// @fail(extraction): proverif(HAX0001)
fn reused_name(x: u8) -> u8 {
    let y = match modelled(x) {
        Ok(v) => v,
        Err(e) => {
            let _ = e;
            0
        }
    };
    let e = y + 1;
    if e == 3 { 1 } else { 0 }
}

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn spliced(x: u8) -> u8 {
    let r = modelled(x);
    hax_lib::proverif!("${r}");
    0
}

// A `Result` passed to a generic parameter.

trait Tag {
    fn tag(&self) -> u8;
}

impl<T> Tag for T {
    fn tag(&self) -> u8 {
        3
    }
}

/// @fail(extraction): proverif(HAX0001)
fn generic_self(x: u8) -> u8 {
    check(x).tag()
}

// Models that build the `Result` themselves, or apply a bare term after a
// `let`.

#[hax_lib::proverif::replace_body("hax_result_err(rust_primitives__hax__Tuple0__Tuple0)")]
fn always_err(_x: u8) -> Result<u8, ()> {
    Err(())
}

/// @fail(extraction): proverif(HAX0001)
fn recover_always_err(x: u8) -> u8 {
    match always_err(x) {
        Ok(v) => v,
        Err(_) => 0,
    }
}

#[hax_lib::proverif::replace_body("let k2 = crypto__hash(${k}) in crypto__aead_dec(k2, ${c}, empty)")]
fn dec_let(k: u8, c: u8) -> Result<u8, ()> {
    if k == c { Ok(k) } else { Err(()) }
}

fn use_dec_let(k: u8, c: u8) -> Result<u8, ()> {
    let v = dec_let(k, c)?;
    Ok(v)
}

#[hax_lib::pv_inverse_of(encode)]
fn decode_unchecked(b: u8) -> u8 {
    b
}

// Observable through a table, or through another model.

#[hax_lib::proverif::before("table Recorded_table(bitstring).")]
#[hax_lib::proverif::replace_body("insert Recorded_table(${x}); ${x}")]
fn record_in_table(x: u8) -> u8 {
    x
}

/// @fail(extraction): proverif(HAX0001)
fn err_arm_table(r: Result<u8, Error>) -> Result<u8, Error> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => {
            record_in_table(0);
            Err(e)
        }
    }
}

#[hax_lib::proverif::replace_body("${record}(${x})")]
fn indirect_record(x: u8) -> u8 {
    record(x)
}

/// @fail(extraction): proverif(HAX0001)
fn err_arm_indirect(r: Result<u8, Error>) -> Result<u8, Error> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => {
            indirect_record(0);
            Err(e)
        }
    }
}

// Propagation that returns another `Err`, or converts the `Result`.

/// @fail(extraction): proverif(HAX0001)
fn returns_other_err(x: u8) -> Result<u8, Error> {
    let _r = check(x);
    Err(Error::Other)
}

/// @fail(extraction): proverif(HAX0001)
fn converted(x: u8) -> Result<u8, Error> {
    let r: Result<u8, Error> = From::from(check(x));
    r
}

// Guards with observable or falling-through `Err`s.

/// @fail(extraction): proverif(HAX0001)
fn guard_effect(o: Option<u8>) -> Result<u8, Error> {
    match o {
        Some(v) if let Err(_) = check(record(v)) => Err(Error::Other),
        _ => Ok(1),
    }
}

/// @fail(extraction): proverif(HAX0001)
fn guard_falls_to_err(o: Option<u8>) -> Result<u8, Error> {
    match o {
        Some(v) if let Ok(y) = check(v) => Ok(y),
        _ => Err(Error::Other),
    }
}

// Models whose observable behaviour is not in their own text.

#[hax_lib::proverif::before(
    "event Logged(bitstring). letfun log_it(x: bitstring) = event Logged(x); x."
)]
#[hax_lib::proverif::replace_body("log_it(${x})")]
fn log(x: u8) -> u8 {
    x
}

/// @fail(extraction): proverif(HAX0001)
fn err_arm_log(r: Result<u8, Error>) -> Result<u8, Error> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => {
            log(0);
            Err(e)
        }
    }
}

#[hax_lib::proverif::replace("event Read. letfun ${OBSERVED}() = event Read; nat_0.")]
const OBSERVED: u8 = 0;

/// @fail(extraction): proverif(HAX0001)
fn err_arm_constant(r: Result<u8, Error>) -> Result<u8, Error> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => {
            let _k = OBSERVED;
            Err(e)
        }
    }
}

// Models of `&mut` functions, and of values holding a `Result`.

#[hax_lib::proverif::replace_body("crypto__aead_dec(${k}, ${c}, empty)")]
fn dec_mut(st: &mut u8, k: u8, c: u8) -> Result<u8, ()> {
    *st += 1;
    if k == c { Ok(k) } else { Err(()) }
}

fn use_dec_mut(k: u8, c: u8) -> Result<u8, ()> {
    let mut st = 0;
    let v = dec_mut(&mut st, k, c)?;
    Ok(v + st)
}

#[hax_lib::proverif::replace_body(
    "rust_primitives__hax__Tuple2__Tuple2(${k}, crypto__aead_dec(${k}, ${c}, empty))"
)]
fn dec_pair(k: u8, c: u8) -> (u8, Result<u8, ()>) {
    (k, if k == c { Ok(k) } else { Err(()) })
}

// A `Result` used on some paths, then on every path; pure verbatim ProVerif
// before a use.

fn check_u8(x: u8) -> Result<u8, u8> {
    if x == 0 { Err(0) } else { Ok(x) }
}

/// @fail(extraction): proverif(HAX0001)
fn used_on_one_branch(x: u8) -> Result<u8, u8> {
    let r = check_u8(x);
    let y = if x > 1 { r? } else { 1 };
    let z = r?;
    Ok(y + z)
}

/// @fail(extraction): proverif(HAX0001)
fn pure_quote_before_use(x: u8) -> Result<u8, u8> {
    let r = check_u8(x);
    hax_lib::proverif!("nat_0");
    let v = r?;
    Ok(v)
}

// Models observable through a nullary `letfun`, or a constant the crate does
// not define.

#[hax_lib::proverif::before(
    "event Nullary_seen. letfun log_nullary() = event Nullary_seen; nat_0."
)]
#[hax_lib::proverif::replace_body("log_nullary")]
fn nullary() -> u8 {
    0
}

/// @fail(extraction): proverif(HAX0001)
fn err_arm_nullary(r: Result<u8, Error>) -> Result<u8, Error> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => {
            nullary();
            Err(e)
        }
    }
}

trait HasConst {
    const C: u8;
}

/// @fail(extraction): proverif(HAX0001)
fn err_arm_trait_const<T: HasConst>(r: Result<u8, Error>) -> Result<u8, Error> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => {
            let _c = T::C;
            Err(e)
        }
    }
}

// An or-pattern binding an error on one side.

#[hax_lib::proverif::replace_body("crypto__hash(${x})")]
fn modelled_both(x: u8) -> Result<Error, Error> {
    if x == 0 { Err(Error::Other) } else { Ok(Error::Invalid) }
}

/// @fail(extraction): proverif(HAX0001)
fn or_pattern_taint(x: u8) -> u8 {
    let e = match modelled_both(x) {
        Err(e) | Ok(e) => e,
    };
    match e {
        Error::Invalid => 1,
        Error::Other => 2,
    }
}

// A library function returning a `Result`, without a model.

fn missing_model(b: [u8; 1]) -> Result<u8, Error> {
    match core::str::from_utf8(&b) {
        Ok(_) => Ok(1),
        Err(_) => Err(Error::Invalid),
    }
}

// A recovery the user takes responsibility for.

#[hax_lib::pv_unchecked_results]
fn unchecked_recovery(x: u8) -> u8 {
    match check(x) {
        Ok(v) => v,
        Err(_) => 0,
    }
}

// Calls on an `Err` path: a function calling no model, or a conversion
// through an impl calling one.

fn wrap(e: Error) -> Wrapped {
    Wrapped::E(e)
}

fn err_arm_pure_helper(x: u8) -> Result<u8, Wrapped> {
    match check(x) {
        Ok(v) => Ok(v),
        Err(e) => Err(wrap(e)),
    }
}

enum Logged {
    E(Error),
}

impl From<Error> for Logged {
    fn from(e: Error) -> Self {
        record(0);
        Logged::E(e)
    }
}

/// @fail(extraction): proverif(HAX0001)
fn noisy_conversion(x: u8) -> Result<u8, Logged> {
    let v = check(x)?;
    Ok(v)
}

// Mapping the error of a hand-written model.

fn map_err_ignoring(x: u8) -> Result<u8, u8> {
    modelled(x).map_err(|_| 1)
}

fn map_err_reading(x: u8) -> Result<u8, u8> {
    modelled(x).map_err(|e| error_code(e))
}

// A function returning a `Result`, applied by `Option::map`.

fn option_map_closure(o: Option<u8>) -> Result<Option<u8>, Error> {
    let v = o.map(|x| check(x)).transpose()?;
    Ok(v)
}

/// @fail(extraction): proverif(HAX0001)
fn option_map_fn(o: Option<u8>) -> Result<Option<u8>, Error> {
    o.map(modelled).transpose()
}

/// @fail(extraction): proverif(HAX0001)
fn option_map_kept(o: Option<u8>) -> Option<Result<u8, Error>> {
    let r = o.map(modelled);
    r
}

// A function value applied on an `Err` path, a checked caller of an
// unchecked function, and a conversion of a `Result` by an impl.

/// @fail(extraction): proverif(HAX0001)
fn err_arm_fn_value(r: Result<u8, Error>, o: Option<u8>) -> Result<u8, Error> {
    let f: fn(u8) -> u8 = record;
    match r {
        Ok(v) => Ok(v),
        Err(e) => {
            let _ = o.map(f);
            Err(e)
        }
    }
}

#[hax_lib::pv_unchecked_results]
fn unchecked_forward(x: u8) -> Result<u8, Error> {
    modelled(x)
}

/// @fail(extraction): proverif(HAX0001)
fn inspect_unchecked(x: u8) -> u8 {
    match unchecked_forward(x) {
        Ok(v) => v,
        Err(e) => error_code(e),
    }
}

struct WithResult {
    r: Result<u8, Error>,
    code: u8,
}

/// @fail(extraction): proverif(HAX0001, HAX0001, HAX0001)
impl From<Result<u8, Error>> for WithResult {
    fn from(r: Result<u8, Error>) -> Self {
        match r {
            Ok(v) => WithResult { r: Ok(v), code: 0 },
            Err(e) => WithResult {
                r: Ok(0),
                code: error_code(e),
            },
        }
    }
}

/// @fail(extraction): proverif(HAX0001)
fn converted_model(x: u8) -> WithResult {
    modelled(x).into()
}

// Arms that leave on an `Err` without returning one.

/// @fail(extraction): proverif(HAX0001)
fn return_ok_on_err(x: u8) -> Result<u8, Error> {
    match check(x) {
        Ok(v) => Ok(v),
        Err(_) => return Ok(0),
    }
}

/// @fail(extraction): proverif(HAX0001)
fn continue_on_err(xs: [u8; 2]) -> Result<u8, Error> {
    let mut n = 0;
    for x in xs {
        let v = match check(x) {
            Ok(v) => v,
            Err(_) => continue,
        };
        n = v;
    }
    Ok(n)
}

/// @fail(extraction): proverif(HAX0001)
fn nested_leave_on_err(x: u8, c: bool) -> Result<u8, Error> {
    match check(x) {
        Ok(v) => Ok(v),
        Err(_) => match c {
            true => return Ok(1),
            false => panic!(),
        },
    }
}

// The error of a hand-written model, passed on through a `match`, then read.

fn rematched(x: u8) -> Result<u8, Error> {
    let v = match modelled(x) {
        Ok(v) => Ok(v),
        Err(e) => Err(e),
    }?;
    Ok(v)
}

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn inspect_rematched(x: u8) -> u8 {
    match rematched(x) {
        Ok(v) => v,
        Err(Error::Invalid) => 1,
        Err(Error::Other) => 2,
    }
}

// Trait methods: an extracted impl, and a hand-written one.

trait Decode {
    fn decode(&self) -> Result<u8, Error>;
}

impl Decode for u8 {
    fn decode(&self) -> Result<u8, Error> {
        check(*self)
    }
}

struct Modelled(u8);

impl Decode for Modelled {
    #[hax_lib::proverif::replace_body("hax_result_ok(self)")]
    fn decode(&self) -> Result<u8, Error> {
        check(self.0)
    }
}

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn inspect_decoded(x: u8) -> u8 {
    match x.decode() {
        Ok(v) => v,
        Err(Error::Invalid) => 1,
        Err(Error::Other) => 2,
    }
}

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn inspect_modelled_decoded(x: Modelled) -> u8 {
    match x.decode() {
        Ok(v) => v,
        Err(Error::Invalid) => 1,
        Err(Error::Other) => 2,
    }
}

// The error of a hand-written model inside an `Ok` payload.

#[hax_lib::proverif::replace_body("hax_result_ok(hax_result_err(x))")]
fn nested_model(x: u8) -> Result<Result<u8, Error>, Error> {
    Ok(check(x))
}

/// @fail(extraction): proverif(HAX0001)
fn inspect_nested_ok(x: u8) -> u8 {
    match nested_model(x).ok() {
        Some(Err(Error::Invalid)) => 1,
        Some(Err(Error::Other)) => 2,
        Some(Ok(v)) => v,
        None => 3,
    }
}

// An argument evaluated after the `Result` its call consumes.

fn checked_failure() -> Result<u8, u8> {
    record(1);
    Err(0)
}

/// @fail(extraction): proverif(HAX0001)
fn observable_expect_arg() -> u8 {
    checked_failure().expect({
        record(2);
        "error"
    })
}

// Leaving an arm that sees an `Err` from inside an expression.

/// @fail(extraction): proverif(HAX0001)
fn return_in_err_payload(x: u8, recover: bool) -> Result<u8, Error> {
    match check(x) {
        Ok(v) => Ok(v),
        Err(_) => Err({
            if recover {
                return Ok(1);
            }
            Error::Invalid
        }),
    }
}

/// @fail(extraction): proverif(HAX0001)
fn return_in_err_arm_let(x: u8, c: bool) -> Result<u8, Error> {
    match check(x) {
        Ok(v) => Ok(v),
        Err(e) => {
            let _y: u8 = if c { return Ok(7) } else { 0 };
            Err(e)
        }
    }
}

// A library function calling an observable impl of the crate.

#[derive(PartialEq, Eq, PartialOrd)]
struct Po(u8);

impl Ord for Po {
    fn cmp(&self, o: &Self) -> core::cmp::Ordering {
        record(self.0).cmp(&o.0)
    }
}

/// @fail(extraction): proverif(HAX0001)
fn library_calls_impl(x: u8, a: Po, b: Po) -> Result<u8, Error> {
    match check(x) {
        Ok(v) => Ok(v),
        Err(e) => {
            let _m = core::cmp::max(a, b);
            Err(e)
        }
    }
}

// A library function calling an observable impl of a supertrait.

#[derive(PartialEq, Eq)]
struct Pk(u8);

impl PartialOrd for Pk {
    fn partial_cmp(&self, o: &Self) -> Option<core::cmp::Ordering> {
        Some(record(self.0).cmp(&o.0))
    }
}

impl Ord for Pk {
    fn cmp(&self, o: &Self) -> core::cmp::Ordering {
        self.0.cmp(&o.0)
    }
}

/// @fail(extraction): proverif(HAX0001)
fn library_calls_supertrait(x: u8, a: Pk, b: Pk) -> Result<u8, Error> {
    match check(x) {
        Ok(v) => Ok(v),
        Err(e) => {
            let _m = core::cmp::max(a, b);
            Err(e)
        }
    }
}

// Replacing the error of a hand-written model whose `Ok` payload holds
// another of its errors.

/// @fail(extraction): proverif(HAX0001)
fn nested_map_err(x: u8) -> u8 {
    match nested_model(x).map_err(|_| Error::Other) {
        Ok(Err(Error::Invalid)) => 1,
        _ => 0,
    }
}

// A `Result` inside the `Ok` of a hand-written model, bound and returned after
// an event.

/// @fail(extraction): proverif(HAX0001)
fn nested_ok_payload(x: u8) -> Result<u8, Error> {
    match nested_model(x) {
        Ok(inner) => {
            record(1);
            inner
        }
        Err(e) => Err(e),
    }
}

// An unchecked function that would be inlined.

#[hax_lib::pv_unchecked_results]
fn with_fallback(f: fn(u8) -> u8, x: u8) -> u8 {
    match check(x) {
        Ok(v) => f(v),
        Err(_) => 0,
    }
}

fn uses_fallback(x: u8) -> u8 {
    with_fallback(|v| v, x)
}

// A generic function whose model is a verbatim term.

trait Make {
    fn make(x: u8) -> Self;
}

impl Make for Result<u8, Error> {
    fn make(x: u8) -> Self {
        check(x)
    }
}

#[hax_lib::proverif::replace_body("hax_result_ok(x)")]
fn make<T: Make>(x: u8) -> T {
    T::make(x)
}

/// @fail(extraction): proverif(HAX0001)
fn use_make(x: u8) -> Result<u8, Error> {
    let v: u8 = make::<Result<u8, Error>>(x)?;
    Ok(v)
}

// A `?` in a closure given to `Option::map`.

/// @fail(extraction): proverif(HAX0001)
fn map_closure_question(o: Option<u8>) -> u8 {
    match o
        .map(|c| {
            let v = modelled(c)?;
            Ok(v)
        })
        .transpose()
    {
        Ok(_) => 0,
        Err(e) => error_code(e),
    }
}

// A `Result` method that hax's libraries do not model.

/// @fail(extraction): proverif(HAX0001)
fn unmodelled_transpose() -> u8 {
    match Err::<Option<u8>, Error>(Error::Invalid).transpose() {
        Some(Err(Error::Invalid)) => record(9),
        _ => 0,
    }
}

// A `Result` given to a library function that hax's libraries do not model.

struct NoResult;

impl Default for NoResult {
    fn default() -> Self {
        record(0);
        NoResult
    }
}

/// @fail(extraction): proverif(HAX0001)
fn unmodelled_consumer() -> u8 {
    let _ = Err::<NoResult, Error>(Error::Invalid).unwrap_or_default();
    0
}

// A generic function instantiated with a `Result`.

struct GenTag;

impl From<GenTag> for Result<u8, Error> {
    fn from(_: GenTag) -> Self {
        Err(Error::Invalid)
    }
}

fn convert<T, U: From<T>>(x: T) -> U {
    U::from(x)
}

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn generic_result_instance() -> u8 {
    if let Err(Error::Invalid) = convert::<GenTag, Result<u8, Error>>(GenTag) {
        record(4)
    } else {
        0
    }
}

// An associated type holding a `Result`.

struct ResultItems;

/// @fail(extraction): proverif(HAX0001)
impl Iterator for ResultItems {
    type Item = Result<u8, Error>;
    fn next(&mut self) -> Option<Self::Item> {
        Some(Err(Error::Invalid))
    }
}

fn next_generic<I: Iterator>(it: &mut I) -> Option<I::Item> {
    it.next()
}

/// @fail(extraction): proverif(HAX0001)
fn generic_associated_result() -> u8 {
    match next_generic(&mut ResultItems) {
        Some(Err(Error::Invalid)) => record(1),
        _ => 0,
    }
}

// An associated type of a reference impl, holding a `Result`.

struct RefItems;

/// @fail(extraction): proverif(HAX0001)
impl Iterator for &RefItems {
    type Item = Result<u8, Error>;
    fn next(&mut self) -> Option<Self::Item> {
        Some(Err(Error::Invalid))
    }
}

// An impl with no method, whose associated type holds a `Result`.

struct OutResult(Result<u8, Error>);

/// @fail(extraction): proverif(HAX0001)
impl Default for OutResult {
    fn default() -> Self {
        OutResult(Err(Error::Invalid))
    }
}

trait HasOutput {
    type Output: Default;
}

impl HasOutput for u8 {
    type Output = OutResult;
}

fn make_output<T: HasOutput>() -> T::Output {
    Default::default()
}

/// @fail(extraction): proverif(HAX0001)
fn use_output() -> u8 {
    match make_output::<u8>() {
        OutResult(Err(_)) => record(1),
        OutResult(Ok(v)) => v,
    }
}

// Kept trait calls, which call the hand-written model of the trait item.

trait Kept {
    fn dec(&self, x: u8) -> Result<u8, Error>;
    fn kept_tag(&self) -> u8;
}

struct Plain;

impl Kept for Plain {
    fn dec(&self, x: u8) -> Result<u8, Error> {
        check(x)
    }
    fn kept_tag(&self) -> u8 {
        0
    }
}

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn kept_err_read(x: u8) -> u8 {
    match Plain.dec(x) {
        Ok(v) => v,
        Err(Error::Invalid) => record(1),
        Err(Error::Other) => record(2),
    }
}

/// @fail(extraction): proverif(HAX0001)
fn kept_on_err_path(r: Result<u8, Error>) -> Result<u8, Error> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => {
            let _ = Plain.kept_tag();
            Err(e)
        }
    }
}

// A library function given by path to `map_err`, which runs an observable
// conversion of the crate.

/// @fail(extraction): proverif(HAX0001)
fn map_err_by_path(x: u8) -> Result<u8, Logged> {
    check(x).map_err(Logged::from)
}

// A trait method of the crate given by path to `map_err`.

trait Convert {
    fn conv(e: Error) -> Self;
}

impl Convert for Logged {
    fn conv(e: Error) -> Logged {
        Logged::from(e)
    }
}

/// @fail(extraction): proverif(HAX0001)
fn map_err_by_trait_path(x: u8) -> Result<u8, Logged> {
    check(x).map_err(Logged::conv)
}

// A `pv_inline` function given by path to `map_err`.

#[hax_lib::pv_inline]
fn log_inline(e: Error) -> Logged {
    Logged::from(e)
}

/// @fail(extraction): proverif(HAX0001)
fn map_err_by_inline_path(x: u8) -> Result<u8, Logged> {
    check(x).map_err(log_inline)
}

// A trait method of the crate given by reference to `map_err`.

/// @fail(extraction): proverif(HAX0001)
fn map_err_by_reference(x: u8) -> Result<u8, Logged> {
    check(x).map_err(&Logged::conv)
}

// A method of a generic impl, called while an `Err` is pending.

trait Note {
    fn note(&self) -> u8;
}

struct Quietly<T>(T);

impl<T: Clone> Note for Quietly<T> {
    fn note(&self) -> u8 {
        1
    }
}

struct Loudly<T>(T);

impl<T: Clone> Note for Loudly<T> {
    fn note(&self) -> u8 {
        record(1)
    }
}

fn err_arm_quiet_generic(r: Result<u8, Error>, n: Quietly<u8>) -> Result<u8, Error> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => {
            n.note();
            Err(e)
        }
    }
}

/// @fail(extraction): proverif(HAX0001)
fn err_arm_noisy_generic(r: Result<u8, Error>, n: Loudly<u8>) -> Result<u8, Error> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => {
            n.note();
            Err(e)
        }
    }
}
