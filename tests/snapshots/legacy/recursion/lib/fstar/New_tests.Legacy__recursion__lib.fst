module New_tests.Legacy__recursion__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): proverif(HAX0001)
let rec f (n: u8) : u8 = if n =. mk_u8 0 then mk_u8 0 else n +! (f (n -! mk_u8 1 <: u8) <: u8)
