module New_tests.Legacy__closure_return__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): coq(HAX0001, HAX0001), ssprove(HAX0001), proverif(HAX0008)
let in_while_condition (n: u8) : u8 =
  let i:u8 = mk_u8 0 in
  let i:u8 =
    Rust_primitives.Hax.while_loop (fun i ->
          let i:u8 = i in
          true)
      (fun i ->
          let i:u8 = i in
          let c: u8 -> bool =
            fun x ->
              let x:u8 = x in
              if x =. mk_u8 3 then false else true
          in
          Core_models.Ops.Function.f_call #(u8 -> bool)
            #u8
            #FStar.Tactics.Typeclasses.solve
            c
            (i <: u8) &&
          i <. n)
      (fun i ->
          let i:u8 = i in
          Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
      i
      (fun i ->
          let i:u8 = i in
          let i:u8 = i +! mk_u8 1 in
          i)
  in
  i

/// @fail(extraction): coq(HAX0001, HAX0001), ssprove(HAX0001), proverif(HAX0008)
let in_loop_body (n: u8) : u8 =
  let i:u8 = mk_u8 0 in
  let i:u8 =
    Rust_primitives.Hax.while_loop (fun i ->
          let i:u8 = i in
          true)
      (fun i ->
          let i:u8 = i in
          i <. n <: bool)
      (fun i ->
          let i:u8 = i in
          Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
      i
      (fun i ->
          let i:u8 = i in
          let c: u8 -> bool =
            fun x ->
              let x:u8 = x in
              if x =. mk_u8 3 then false else true
          in
          if
            Core_models.Ops.Function.f_call #(u8 -> bool)
              #u8
              #FStar.Tactics.Typeclasses.solve
              c
              (i <: u8)
          then
            let i:u8 = i +! mk_u8 1 in
            i
          else
            let i:u8 = i +! mk_u8 2 in
            i)
  in
  i

/// @fail(extraction): proverif(HAX0008)
let nested (i: u8) : u8 =
  let c: u8 -> u8 =
    fun x ->
      let x:u8 = x in
      let d: u8 -> u8 =
        fun y ->
          let y:u8 = y in
          if y =. mk_u8 0 then mk_u8 7 else y
      in
      if x =. mk_u8 3
      then
        Core_models.Ops.Function.f_call #(u8 -> u8) #u8 #FStar.Tactics.Typeclasses.solve d (x <: u8)
      else x +! mk_u8 1
  in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_u8 0)
      i
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:u8 = temp_1_ in
          true)
      ()
      (fun temp_0_ j ->
          let _:Prims.unit = temp_0_ in
          let j:u8 = j in
          if
            (Core_models.Ops.Function.f_call #(u8 -> u8)
                #u8
                #FStar.Tactics.Typeclasses.solve
                c
                (j <: u8)
              <:
              u8) =.
            mk_u8 9
            <:
            bool
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break (mk_u8 4)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow u8 (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow u8 (Prims.unit & Prims.unit)) Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow u8 (Prims.unit & Prims.unit)) Prims.unit)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow u8 Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
    Core_models.Ops.Function.f_call #(u8 -> u8) #u8 #FStar.Tactics.Typeclasses.solve c (i <: u8)
