module New_tests.Legacy__lean_core_models__lib.Result
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_E1 =
  | E1_C1 : t_E1
  | E1_C2 : u32 -> t_E1

let impl: Core_models.Clone.t_Clone t_E1 =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

type t_E2 =
  | E2_C1 : t_E2
  | E2_C2 : u32 -> t_E2

/// @fail(extraction): proverif(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001)
let tests (_: Prims.unit) : Core_models.Result.t_Result u32 t_E1 =
  let v1:Core_models.Result.t_Result u32 t_E1 =
    Core_models.Result.Result_Ok (mk_u32 1) <: Core_models.Result.t_Result u32 t_E1
  in
  let v2:Core_models.Result.t_Result u32 t_E1 =
    Core_models.Result.Result_Err (E1_C1 <: t_E1) <: Core_models.Result.t_Result u32 t_E1
  in
  let f: u32 -> u32 =
    fun x ->
      let x:u32 = x in
      x +! mk_u32 1
  in
  let v5:Core_models.Result.t_Result i32 t_E1 =
    Core_models.Result.impl__map #i32
      #t_E1
      #i32
      #(i32 -> i32)
      (Core_models.Result.Result_Ok (mk_i32 1) <: Core_models.Result.t_Result i32 t_E1)
      (fun v ->
          let v:i32 = v in
          v +! mk_i32 1 <: i32)
  in
  let v6:u32 =
    Core_models.Result.impl__map_or #u32
      #t_E1
      #u32
      #(u32 -> u32)
      (Core_models.Result.Result_Ok (mk_u32 1) <: Core_models.Result.t_Result u32 t_E1)
      (mk_u32 9)
      f
  in
  let v7:u32 =
    Core_models.Result.impl__map_or_else #u32
      #t_E1
      #u32
      #(t_E1 -> u32)
      #(u32 -> u32)
      (Core_models.Result.Result_Ok (mk_u32 1) <: Core_models.Result.t_Result u32 t_E1)
      (fun temp_0_ ->
          let _:t_E1 = temp_0_ in
          mk_u32 10)
      f
  in
  let v8:Core_models.Result.t_Result i32 t_E2 =
    Core_models.Result.impl__map_err #i32
      #t_E1
      #t_E2
      #(t_E1 -> t_E2)
      (Core_models.Result.Result_Ok (mk_i32 0) <: Core_models.Result.t_Result i32 t_E1)
      (fun e ->
          let e:t_E1 = e in
          match e <: t_E1 with
          | E1_C1  -> E2_C1 <: t_E2
          | E1_C2 x -> E2_C2 (x +! mk_u32 1 <: u32) <: t_E2)
  in
  let v9:bool = Core_models.Result.impl__is_ok #u32 #t_E1 v1 in
  let v10:bool = Core_models.Result.impl__is_err #u32 #t_E1 v1 in
  let v11:Core_models.Result.t_Result u32 t_E1 =
    Core_models.Result.impl__and_then #u32
      #t_E1
      #u32
      #(u32 -> Core_models.Result.t_Result u32 t_E1)
      (Core_models.Clone.f_clone #(Core_models.Result.t_Result u32 t_E1)
          #FStar.Tactics.Typeclasses.solve
          v1
        <:
        Core_models.Result.t_Result u32 t_E1)
      (fun x ->
          let x:u32 = x in
          Core_models.Result.Result_Ok (x +! mk_u32 1 <: u32)
          <:
          Core_models.Result.t_Result u32 t_E1)
  in
  let v12:u32 =
    Core_models.Result.impl__unwrap #u32
      #u32
      (Core_models.Clone.f_clone #(Core_models.Result.t_Result u32 u32)
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Result.Result_Ok (mk_u32 0) <: Core_models.Result.t_Result u32 u32)
        <:
        Core_models.Result.t_Result u32 u32)
  in
  let v13:u32 =
    Core_models.Result.impl__expect #u32
      #u32
      (Core_models.Clone.f_clone #(Core_models.Result.t_Result u32 u32)
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Result.Result_Ok (mk_u32 0) <: Core_models.Result.t_Result u32 u32)
        <:
        Core_models.Result.t_Result u32 u32)
      "Should be Ok"
  in
  match
    Core_models.Result.impl__map #u32 #t_E1 #u32 #(u32 -> u32) v1 f
    <:
    Core_models.Result.t_Result u32 t_E1
  with
  | Core_models.Result.Result_Ok hoist2 ->
    (match v2 <: Core_models.Result.t_Result u32 t_E1 with
      | Core_models.Result.Result_Ok hoist1 ->
        let v3:u32 = hoist2 +! hoist1 in
        Core_models.Result.Result_Ok v3 <: Core_models.Result.t_Result u32 t_E1
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err <: Core_models.Result.t_Result u32 t_E1)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result u32 t_E1
