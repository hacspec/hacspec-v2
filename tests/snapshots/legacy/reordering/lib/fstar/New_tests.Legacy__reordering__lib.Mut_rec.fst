module New_tests.Legacy__reordering__lib.Mut_rec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): proverif(HAX0001)
let rec g (_: Prims.unit) : Prims.unit = f ()

/// @fail(extraction): proverif(HAX0001)
and f (_: Prims.unit) : Prims.unit = g ()

let ff_2_ (_: Prims.unit) : Prims.unit = f ()
