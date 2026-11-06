module New_tests.Rustc_coverage__closure_unit_return
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): proverif(HAX0001)
let explicit_unit (_: Prims.unit) : Prims.unit =
  let closure: Prims.unit -> Prims.unit =
    fun temp_0_ ->
      let _:Prims.unit = temp_0_ in
      let _:Prims.unit = () <: Prims.unit in
      ()
  in
  let _:Prims.unit = Core_models.Mem.drop #(Prims.unit -> Prims.unit) closure in
  () <: Prims.unit

/// @fail(extraction): proverif(HAX0001)
let implicit_unit (_: Prims.unit) : Prims.unit =
  let closure: Prims.unit -> Prims.unit =
    fun temp_0_ ->
      let _:Prims.unit = temp_0_ in
      let _:Prims.unit = () <: Prims.unit in
      ()
  in
  let _:Prims.unit = Core_models.Mem.drop #(Prims.unit -> Prims.unit) closure in
  ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = explicit_unit () in
  let _:Prims.unit = implicit_unit () in
  ()
