module New_tests.Rustc_coverage__no_spans
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): proverif(HAX0001)
let affected_function (_: Prims.unit) :  Prims.unit -> Prims.unit =
  fun temp_0_ ->
    let _:Prims.unit = temp_0_ in
    () <: Prims.unit

/// @fail(extraction): proverif(HAX0001)
let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit =
    Core_models.Ops.Function.f_call #(Prims.unit -> Prims.unit)
      #Prims.unit
      #FStar.Tactics.Typeclasses.solve
      (affected_function () <: Prims.unit -> Prims.unit)
      (() <: Prims.unit)
  in
  ()
