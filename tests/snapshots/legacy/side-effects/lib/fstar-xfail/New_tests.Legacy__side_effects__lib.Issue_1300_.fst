module New_tests.Legacy__side_effects__lib.Issue_1300_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): proverif(HAX0001)
let v_fun (_: Prims.unit) : Core_models.Result.t_Result Prims.unit u8 =
  match
    Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
          (Core_models.Slice.Iter.t_Iter u8)
          (u8 -> Core_models.Result.t_Result (u8 & t_Array u8 (mk_usize 32)) u8))
      #FStar.Tactics.Typeclasses.solve
      #(Core_models.Result.t_Result
          (Alloc.Vec.t_Vec (u8 & t_Array u8 (mk_usize 32)) Alloc.Alloc.t_Global) u8)
      (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter u8)
          #FStar.Tactics.Typeclasses.solve
          #(Core_models.Result.t_Result (u8 & t_Array u8 (mk_usize 32)) u8)
          #(u8 -> Core_models.Result.t_Result (u8 & t_Array u8 (mk_usize 32)) u8)
          (Core_models.Slice.impl__iter #u8
              (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 5) <: t_Slice u8)
            <:
            Core_models.Slice.Iter.t_Iter u8)
          (fun prev ->
              let prev:u8 = prev in
              match
                Core_models.Result.Result_Ok
                (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) <: t_Array u8 (mk_usize 32))
                <:
                Core_models.Result.t_Result (t_Array u8 (mk_usize 32)) u8
              with
              | Core_models.Result.Result_Ok hoist45 ->
                Core_models.Result.Result_Ok (prev, hoist45 <: (u8 & t_Array u8 (mk_usize 32)))
                <:
                Core_models.Result.t_Result (u8 & t_Array u8 (mk_usize 32)) u8
              | Core_models.Result.Result_Err err ->
                Core_models.Result.Result_Err err
                <:
                Core_models.Result.t_Result (u8 & t_Array u8 (mk_usize 32)) u8)
        <:
        Core_models.Iter.Adapters.Map.t_Map (Core_models.Slice.Iter.t_Iter u8)
          (u8 -> Core_models.Result.t_Result (u8 & t_Array u8 (mk_usize 32)) u8))
    <:
    Core_models.Result.t_Result
      (Alloc.Vec.t_Vec (u8 & t_Array u8 (mk_usize 32)) Alloc.Alloc.t_Global) u8
  with
  | Core_models.Result.Result_Ok v_val ->
    Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit u8
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit u8
