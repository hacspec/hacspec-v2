module New_tests.Rustc_coverage__closure_bug
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Std.Env in
  ()

/// @fail(extraction): proverif(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001)
let main (_: Prims.unit) : Prims.unit =
  let truthy:bool =
    (Core_models.Iter.Traits.Exact_size.f_len #Std.Env.t_Args
        #FStar.Tactics.Typeclasses.solve
        (Std.Env.args () <: Std.Env.t_Args)
      <:
      usize) =.
    mk_usize 1
  in
  let a: Prims.unit -> bool =
    fun temp_0_ ->
      let _:Prims.unit = temp_0_ in
      if truthy then true else false
  in
  let _:bool =
    Core_models.Ops.Function.f_call #(Prims.unit -> bool)
      #Prims.unit
      #FStar.Tactics.Typeclasses.solve
      a
      (() <: Prims.unit)
  in
  let _:Prims.unit =
    if truthy
    then
      let _:bool =
        Core_models.Ops.Function.f_call #(Prims.unit -> bool)
          #Prims.unit
          #FStar.Tactics.Typeclasses.solve
          a
          (() <: Prims.unit)
      in
      ()
  in
  let b: Prims.unit -> bool =
    fun temp_0_ ->
      let _:Prims.unit = temp_0_ in
      if truthy then true else false
  in
  let _:bool =
    Core_models.Ops.Function.f_call #(Prims.unit -> bool)
      #Prims.unit
      #FStar.Tactics.Typeclasses.solve
      b
      (() <: Prims.unit)
  in
  let _:Prims.unit =
    if truthy
    then
      let _:bool =
        Core_models.Ops.Function.f_call #(Prims.unit -> bool)
          #Prims.unit
          #FStar.Tactics.Typeclasses.solve
          b
          (() <: Prims.unit)
      in
      ()
  in
  let c: Prims.unit -> bool =
    fun temp_0_ ->
      let _:Prims.unit = temp_0_ in
      if truthy then true else false
  in
  let _:bool =
    Core_models.Ops.Function.f_call #(Prims.unit -> bool)
      #Prims.unit
      #FStar.Tactics.Typeclasses.solve
      c
      (() <: Prims.unit)
  in
  let _:Prims.unit =
    if truthy
    then
      let _:bool =
        Core_models.Ops.Function.f_call #(Prims.unit -> bool)
          #Prims.unit
          #FStar.Tactics.Typeclasses.solve
          c
          (() <: Prims.unit)
      in
      ()
  in
  let d: Prims.unit -> bool =
    fun temp_0_ ->
      let _:Prims.unit = temp_0_ in
      if truthy then true else false
  in
  let _:bool =
    Core_models.Ops.Function.f_call #(Prims.unit -> bool)
      #Prims.unit
      #FStar.Tactics.Typeclasses.solve
      d
      (() <: Prims.unit)
  in
  if truthy
  then
    let _:bool =
      Core_models.Ops.Function.f_call #(Prims.unit -> bool)
        #Prims.unit
        #FStar.Tactics.Typeclasses.solve
        d
        (() <: Prims.unit)
    in
    ()
