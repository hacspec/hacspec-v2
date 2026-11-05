//! @off: fstar, lean, coq, ssprove, legacy-lean
//!
//! Rust may call impls of the crate that the ProVerif model does not call:
//! those that formatting, iteration, dereferencing and library functions use
//! implicitly. Such impls are rejected when they may be observable, and so are
//! hand-written impls of the traits that the model compares, clones or hashes
//! structurally.

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

// An observable `Deref` impl.

struct Wrapped8(u8);

/// @fail(extraction): proverif(HAX0001)
impl core::ops::Deref for Wrapped8 {
    type Target = u8;
    fn deref(&self) -> &u8 {
        record(0);
        &self.0
    }
}

// An observable impl of a derivable trait.

struct NoisyClone(u8);

/// @fail(extraction): proverif(HAX0001)
impl Clone for NoisyClone {
    fn clone(&self) -> Self {
        NoisyClone(record(self.0))
    }
}

// An observable `Iterator` impl.

struct RecordingIter(u8);

/// @fail(extraction): proverif(HAX0001)
impl Iterator for RecordingIter {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        if self.0 == 0 {
            None
        } else {
            self.0 = record(self.0 - 1);
            Some(self.0)
        }
    }
}

// An observable `Display` impl, a hand-written `PartialEq`, and a crate
// iterator.

struct Shown;

/// @fail(extraction): proverif(HAX0001)
impl core::fmt::Display for Shown {
    fn fmt(&self, _f: &mut core::fmt::Formatter) -> core::fmt::Result {
        record(0);
        Ok(())
    }
}

struct Loose(u8);

/// @fail(extraction): proverif(HAX0001)
impl PartialEq for Loose {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

struct Count(u8);

impl Iterator for Count {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        if self.0 == 0 {
            None
        } else {
            self.0 -= 1;
            Some(self.0)
        }
    }
}

/// @fail(extraction): proverif(HAX0001, HAX0001)
fn loop_over_crate_iterator() -> u8 {
    let mut last = 0;
    for x in Count(2) {
        last = record(x);
    }
    last
}

struct Parsed(u8);

impl TryFrom<u8> for Parsed {
    type Error = Error;
    fn try_from(x: u8) -> Result<Parsed, Error> {
        Ok(Parsed(record(x)))
    }
}

/// @fail(extraction): proverif(HAX0001)
fn noisy_try_into(x: u8) -> Result<Parsed, Error> {
    x.try_into()
}

impl core::str::FromStr for Parsed {
    type Err = Error;
    fn from_str(_: &str) -> Result<Parsed, Error> {
        Ok(Parsed(record(0)))
    }
}

/// @fail(extraction): proverif(HAX0001)
fn noisy_parse(s: &str) -> Result<Parsed, Error> {
    s.parse()
}

/// @fail(extraction): proverif(HAX0001)
fn lazy_filter_map(v: &[u8]) -> Option<u8> {
    v.iter().filter_map(|x| Some(record(*x))).next()
}

// A library trait method called through the bound of a generic function.

/// @fail(extraction): proverif(HAX0001)
fn conv<T: TryFrom<u8>>(x: u8) -> Result<T, T::Error> {
    T::try_from(x)
}

// An observable `Drop` impl, and an implicit call in an unchecked function.

struct Guard(u8);

/// @fail(extraction): proverif(HAX0001)
impl Drop for Guard {
    fn drop(&mut self) {
        record(self.0);
    }
}

fn dropped_guard() -> u8 {
    let _g = Guard(1);
    0
}

/// @fail(extraction): proverif(HAX0001)
#[hax_lib::pv_unchecked_results]
fn unchecked_parse(s: &str) -> Result<Parsed, Error> {
    s.parse()
}

// An observable `Hasher` impl, which `Hash` impls call.

struct Recorder(u8);

/// @fail(extraction): proverif(HAX0001)
impl core::hash::Hasher for Recorder {
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, b: &[u8]) {
        self.0 = record(b[0]);
    }
}

fn hash_into(x: u8, mut h: Recorder) -> u8 {
    core::hash::Hash::hash(&x, &mut h);
    h.0
}

// A generic conversion through the library's blanket `Into` impl, and a
// supertrait bound.

struct Noisy(u8);

impl From<u8> for Noisy {
    fn from(x: u8) -> Noisy {
        Noisy(record(x))
    }
}

/// @fail(extraction): proverif(HAX0001)
fn conv_into<T: Into<Noisy>>(x: T) -> Noisy {
    x.into()
}

fn into_concrete(x: u8) -> Noisy {
    x.into()
}

trait Shows: core::fmt::Display {}

/// @fail(extraction): proverif(HAX0001)
fn show_super<T: Shows>(x: &T) -> String {
    format!("{x}")
}
