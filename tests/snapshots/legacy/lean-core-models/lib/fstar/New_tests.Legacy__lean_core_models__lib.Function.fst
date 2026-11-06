module New_tests.Legacy__lean_core_models__lib.Function
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): proverif(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001)
let test (_: Prims.unit) : u32 =
  let ff_1_: u32 -> u32 =
    fun temp_0_ ->
      let _:u32 = temp_0_ in
      mk_u32 9
  in
  let ff_2_: u32 -> u32 -> u32 =
    fun x y ->
      let x:u32 = x in
      let y:u32 = y in
      x +! y
  in
  let ff_2_tuple: (u32 & u32) -> u32 =
    fun temp_0_ ->
      let (x: u32), (y: u32) = temp_0_ in
      x +! y
  in
  ((Core_models.Ops.Function.f_call #(u32 -> u32)
        #u32
        #FStar.Tactics.Typeclasses.solve
        ff_1_
        (mk_u32 0 <: u32)
      <:
      u32) +!
    (Core_models.Ops.Function.f_call #(u32 -> u32 -> u32)
        #(u32 & u32)
        #FStar.Tactics.Typeclasses.solve
        ff_2_
        (mk_u32 1, mk_u32 2 <: (u32 & u32))
      <:
      u32)
    <:
    u32) +!
  (Core_models.Ops.Function.f_call #((u32 & u32) -> u32)
      #(u32 & u32)
      #FStar.Tactics.Typeclasses.solve
      ff_2_tuple
      ((mk_u32 1, mk_u32 2 <: (u32 & u32)) <: (u32 & u32))
    <:
    u32)
