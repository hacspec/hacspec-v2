module New_tests.Legacy__reordering__lib.Independent_cycles
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): proverif(HAX0001)
let rec c (_: Prims.unit) : Prims.unit = a ()

/// @fail(extraction): proverif(HAX0001)
and a (_: Prims.unit) : Prims.unit = c ()

/// @fail(extraction): proverif(HAX0001)
let rec d (_: Prims.unit) : Prims.unit = b ()

/// @fail(extraction): proverif(HAX0001)
and b (_: Prims.unit) : Prims.unit = d ()
