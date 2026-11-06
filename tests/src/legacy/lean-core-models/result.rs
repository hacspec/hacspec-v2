// Tests for core models in lean
#![allow(dead_code)]
#![allow(unused_variables)]

#[derive(Clone)]
enum E1 {
    C1,
    C2(u32),
}

enum E2 {
    C1,
    C2(u32),
}

/// @fail(extraction): proverif(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001)
fn tests() -> Result<u32, E1> {
    // Constructors
    let v1 = Result::<u32, E1>::Ok(1);
    let v2 = Result::<u32, _>::Err(E1::C1);

    let f = |x: u32| x + 1;

    // map
    let v5 = Ok::<_, E1>(1).map(|v| v + 1);
    let v6 = Ok::<_, E1>(1).map_or(9, f);
    let v7 = Ok::<_, E1>(1).map_or_else(|_| 10, f);
    let v8 = Ok(0).map_err(|e: E1| match e {
        E1::C1 => E2::C1,
        E1::C2(x) => E2::C2(x + 1),
    });

    let v9 = v1.is_ok();
    let v10 = v1.is_err();
    let v11 = v1.clone().and_then(|x| Ok::<_, E1>(x + 1));

    let v12 = Ok::<u32, u32>(0).clone().unwrap();
    let v13 = Ok::<u32, u32>(0).clone().expect("Should be Ok");

    // ? notation
    let v3 = v1.map(f)? + v2?;

    Ok(v3)
}
