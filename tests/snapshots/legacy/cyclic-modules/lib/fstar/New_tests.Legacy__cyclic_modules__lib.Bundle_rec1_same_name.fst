module New_tests.Legacy__cyclic_modules__lib.Bundle_rec1_same_name
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): proverif(HAX0001)
let rec f (x: i32) : i32 =
  if x >. mk_i32 0 then f__from__rec1_same_name (x -! mk_i32 1 <: i32) else mk_i32 0

/// @fail(extraction): proverif(HAX0001)
and f__from__rec1_same_name (x: i32) : i32 = f x
