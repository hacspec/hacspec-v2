module New_tests.Legacy__lean_core_models__lib.Option
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_S = { f_f1:u32 }

type t_E = | E_C : u32 -> t_E

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core_models.Default.t_Default t_S =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_S) -> true);
    f_default = fun (_: Prims.unit) -> { f_f1 = mk_u32 42 } <: t_S
  }

/// @fail(extraction): proverif(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001)
let test (_: Prims.unit) : Prims.unit =
  let o1:Core_models.Option.t_Option i32 =
    Core_models.Option.Option_Some (mk_i32 4) <: Core_models.Option.t_Option i32
  in
  let (o2: Core_models.Option.t_Option i32):Core_models.Option.t_Option i32 =
    Core_models.Option.Option_None <: Core_models.Option.t_Option i32
  in
  let o3:bool =
    Core_models.Option.impl__is_some_and #i32
      #(i32 -> bool)
      (Core_models.Clone.f_clone #(Core_models.Option.t_Option i32)
          #FStar.Tactics.Typeclasses.solve
          o1
        <:
        Core_models.Option.t_Option i32)
      (fun x ->
          let x:i32 = x in
          x =. mk_i32 0 <: bool)
  in
  let o3:bool =
    Core_models.Option.impl__is_none_or #i32
      #(i32 -> bool)
      (Core_models.Clone.f_clone #(Core_models.Option.t_Option i32)
          #FStar.Tactics.Typeclasses.solve
          o1
        <:
        Core_models.Option.t_Option i32)
      (fun x ->
          let x:i32 = x in
          x =. mk_i32 0 <: bool)
  in
  let o4:i32 =
    Core_models.Option.impl__unwrap #i32
      (Core_models.Option.Option_Some (mk_i32 0) <: Core_models.Option.t_Option i32)
  in
  let o5:i32 =
    Core_models.Option.impl__unwrap_or #i32
      (Core_models.Option.Option_Some (mk_i32 0) <: Core_models.Option.t_Option i32)
      (mk_i32 9)
  in
  let o6:i32 =
    Core_models.Option.impl__unwrap_or_else #i32
      #(Prims.unit -> i32)
      (Core_models.Option.Option_Some (mk_i32 0) <: Core_models.Option.t_Option i32)
      (fun temp_0_ ->
          let _:Prims.unit = temp_0_ in
          mk_i32 9)
  in
  let o7:t_S =
    Core_models.Option.impl__unwrap_or_default #t_S
      (Core_models.Option.Option_None <: Core_models.Option.t_Option t_S)
  in
  let o8:Core_models.Option.t_Option i32 =
    Core_models.Option.impl__map #i32
      #i32
      #(i32 -> i32)
      (Core_models.Option.Option_Some (mk_i32 0) <: Core_models.Option.t_Option i32)
      (fun x ->
          let x:i32 = x in
          x +! mk_i32 1 <: i32)
  in
  let o9:i32 =
    Core_models.Option.impl__map_or #i32
      #i32
      #(i32 -> i32)
      (Core_models.Option.Option_Some (mk_i32 1) <: Core_models.Option.t_Option i32)
      (mk_i32 9)
      (fun x ->
          let x:i32 = x in
          x +! mk_i32 1 <: i32)
  in
  let o10:i32 =
    Core_models.Option.impl__map_or_else #i32
      #i32
      #(Prims.unit -> i32)
      #(i32 -> i32)
      (Core_models.Option.Option_Some (mk_i32 2) <: Core_models.Option.t_Option i32)
      (fun temp_0_ ->
          let _:Prims.unit = temp_0_ in
          mk_i32 9)
      (fun x ->
          let x:i32 = x in
          x +! mk_i32 1 <: i32)
  in
  let o11:Core_models.Result.t_Result i32 t_E =
    Core_models.Option.impl__ok_or #i32
      #t_E
      (Core_models.Option.Option_Some (mk_i32 3) <: Core_models.Option.t_Option i32)
      (E_C (mk_u32 0) <: t_E)
  in
  let o12:Core_models.Result.t_Result i32 t_E =
    Core_models.Option.impl__ok_or_else #i32
      #t_E
      #(Prims.unit -> t_E)
      (Core_models.Option.Option_Some (mk_i32 1) <: Core_models.Option.t_Option i32)
      (fun temp_0_ ->
          let _:Prims.unit = temp_0_ in
          E_C (mk_u32 1) <: t_E)
  in
  let o13:Core_models.Option.t_Option u32 =
    Core_models.Option.impl__and_then #u32
      #u32
      #(u32 -> Core_models.Option.t_Option u32)
      (Core_models.Option.Option_None <: Core_models.Option.t_Option u32)
      (fun x ->
          let x:u32 = x in
          Core_models.Option.Option_Some x <: Core_models.Option.t_Option u32)
  in
  let (_: Core_models.Option.t_Option t_S), (out: Core_models.Option.t_Option t_S) =
    Core_models.Option.impl__take #t_S
      (Core_models.Option.Option_Some ({ f_f1 = mk_u32 9 } <: t_S)
        <:
        Core_models.Option.t_Option t_S)
  in
  let o14:Core_models.Option.t_Option t_S = out in
  let o15:bool =
    Core_models.Option.impl__is_some #i32
      (Core_models.Option.Option_Some (mk_i32 1) <: Core_models.Option.t_Option i32)
  in
  let o16:bool =
    Core_models.Option.impl__is_none #i32
      (Core_models.Option.Option_Some (mk_i32 2) <: Core_models.Option.t_Option i32)
  in
  let o17:i32 =
    Core_models.Option.impl__expect #i32
      (Core_models.Option.Option_Some (mk_i32 3) <: Core_models.Option.t_Option i32)
      "Should be Some"
  in
  let o18:i32 =
    Core_models.Option.impl__unwrap #i32
      (Core_models.Option.Option_Some (mk_i32 4) <: Core_models.Option.t_Option i32)
  in
  ()
