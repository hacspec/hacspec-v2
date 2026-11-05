module New_tests.Legacy__traits__lib.Implicit_explicit_calling_conventions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Type (v_TypeArg: Type0) (v_ConstArg: usize) = { f_field:t_Array v_TypeArg v_ConstArg }

class t_Trait (v_Self: Type0) (v_TypeArg: Type0) (v_ConstArg: usize) = {
  f_method_pre:
      #v_MethodTypeArg: Type0 ->
      v_MethodConstArg: usize ->
      v_Self ->
      v_TypeArg ->
      t_Type v_TypeArg v_ConstArg
    -> Type0;
  f_method_post:
      #v_MethodTypeArg: Type0 ->
      v_MethodConstArg: usize ->
      v_Self ->
      v_TypeArg ->
      t_Type v_TypeArg v_ConstArg ->
      Prims.unit
    -> Type0;
  f_method:
      #v_MethodTypeArg: Type0 ->
      v_MethodConstArg: usize ->
      x0: v_Self ->
      x1: v_TypeArg ->
      x2: t_Type v_TypeArg v_ConstArg
    -> Prims.Pure Prims.unit
        (f_method_pre #v_MethodTypeArg v_MethodConstArg x0 x1 x2)
        (fun result -> f_method_post #v_MethodTypeArg v_MethodConstArg x0 x1 x2 result);
  f_associated_function_pre:
      #v_MethodTypeArg: Type0 ->
      v_MethodConstArg: usize ->
      v_Self ->
      v_TypeArg ->
      t_Type v_TypeArg v_ConstArg
    -> Type0;
  f_associated_function_post:
      #v_MethodTypeArg: Type0 ->
      v_MethodConstArg: usize ->
      v_Self ->
      v_TypeArg ->
      t_Type v_TypeArg v_ConstArg ->
      Prims.unit
    -> Type0;
  f_associated_function:
      #v_MethodTypeArg: Type0 ->
      v_MethodConstArg: usize ->
      x0: v_Self ->
      x1: v_TypeArg ->
      x2: t_Type v_TypeArg v_ConstArg
    -> Prims.Pure Prims.unit
        (f_associated_function_pre #v_MethodTypeArg v_MethodConstArg x0 x1 x2)
        (fun result -> f_associated_function_post #v_MethodTypeArg v_MethodConstArg x0 x1 x2 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_TypeArg: Type0) (v_ConstArg: usize) : t_Trait Prims.unit v_TypeArg v_ConstArg =
  {
    f_method_pre
    =
    (fun
        (#v_MethodTypeArg: Type0)
        (v_MethodConstArg: usize)
        (self: Prims.unit)
        (value_TypeArg: v_TypeArg)
        (value_Type: t_Type v_TypeArg v_ConstArg)
        ->
        true);
    f_method_post
    =
    (fun
        (#v_MethodTypeArg: Type0)
        (v_MethodConstArg: usize)
        (self: Prims.unit)
        (value_TypeArg: v_TypeArg)
        (value_Type: t_Type v_TypeArg v_ConstArg)
        (out: Prims.unit)
        ->
        true);
    f_method
    =
    (fun
        (#v_MethodTypeArg: Type0)
        (v_MethodConstArg: usize)
        (self: Prims.unit)
        (value_TypeArg: v_TypeArg)
        (value_Type: t_Type v_TypeArg v_ConstArg)
        ->
        ());
    f_associated_function_pre
    =
    (fun
        (#v_MethodTypeArg: Type0)
        (v_MethodConstArg: usize)
        (e_self: Prims.unit)
        (value_TypeArg: v_TypeArg)
        (value_Type: t_Type v_TypeArg v_ConstArg)
        ->
        true);
    f_associated_function_post
    =
    (fun
        (#v_MethodTypeArg: Type0)
        (v_MethodConstArg: usize)
        (e_self: Prims.unit)
        (value_TypeArg: v_TypeArg)
        (value_Type: t_Type v_TypeArg v_ConstArg)
        (out: Prims.unit)
        ->
        true);
    f_associated_function
    =
    fun
      (#v_MethodTypeArg: Type0)
      (v_MethodConstArg: usize)
      (e_self: Prims.unit)
      (value_TypeArg: v_TypeArg)
      (value_Type: t_Type v_TypeArg v_ConstArg)
      ->
      ()
  }

/// @fail(extraction): proverif(HAX0001)
let method_caller
      (#v_MethodTypeArg #v_TypeArg: Type0)
      (v_ConstArg v_MethodConstArg: usize)
      (#v_ImplTrait: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Trait v_ImplTrait v_TypeArg v_ConstArg)
      (x: v_ImplTrait)
      (value_TypeArg: v_TypeArg)
      (value_Type: t_Type v_TypeArg v_ConstArg)
    : Prims.unit =
  let _:Prims.unit =
    f_method #v_ImplTrait
      #v_TypeArg
      #v_ConstArg
      #FStar.Tactics.Typeclasses.solve
      #v_MethodTypeArg
      v_MethodConstArg
      x
      value_TypeArg
      value_Type
  in
  ()

/// @fail(extraction): proverif(HAX0001)
let associated_function_caller
      (#v_MethodTypeArg #v_TypeArg: Type0)
      (v_ConstArg v_MethodConstArg: usize)
      (#v_ImplTrait: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Trait v_ImplTrait v_TypeArg v_ConstArg)
      (x: v_ImplTrait)
      (value_TypeArg: v_TypeArg)
      (value_Type: t_Type v_TypeArg v_ConstArg)
    : Prims.unit =
  let _:Prims.unit =
    f_associated_function #v_ImplTrait
      #v_TypeArg
      #v_ConstArg
      #FStar.Tactics.Typeclasses.solve
      #v_MethodTypeArg
      v_MethodConstArg
      x
      value_TypeArg
      value_Type
  in
  ()

class t_SubTrait (v_Self: Type0) (v_TypeArg: Type0) (v_ConstArg: usize) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Trait v_Self v_TypeArg v_ConstArg;
  [@@@ FStar.Tactics.Typeclasses.no_method]f_AssocType:Type0;
  f_AssocType_i0:t_Trait f_AssocType v_TypeArg v_ConstArg
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_TypeArg:Type0) (v_ConstArg:usize) {|i: t_SubTrait v_Self v_TypeArg v_ConstArg|} -> i._super_i0
