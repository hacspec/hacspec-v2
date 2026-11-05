//! @off: fstar, lean, coq, ssprove, legacy-lean
//!
//! The library derives `Into`, `TryFrom` and `TryInto` from a `From` impl of
//! the crate, which the model does not call through a generic bound.

#[hax_lib::proverif::before("event Recorded(bitstring).")]
#[hax_lib::proverif::replace_body("event Recorded(${x}); ${x}")]
fn record(x: u8) -> u8 {
    x
}

struct Noisy(u8);

impl From<u8> for Noisy {
    fn from(x: u8) -> Noisy {
        Noisy(record(x))
    }
}

/// @fail(extraction): proverif(HAX0001)
fn try_from_bound<T: TryFrom<u8>>(x: u8) -> Result<T, T::Error> {
    T::try_from(x)
}

/// @fail(extraction): proverif(HAX0001)
fn try_into_bound<T>(x: u8) -> Result<T, <u8 as TryInto<T>>::Error>
where
    u8: TryInto<T>,
{
    x.try_into()
}

fn concrete(x: u8) -> Noisy {
    Noisy::from(x)
}
