module New_tests.Legacy__attributes__lib.Pre_post_on_traits_and_impls
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_ViaAdd = | ViaAdd : t_ViaAdd

type t_ViaMul = | ViaMul : t_ViaMul

class t_Operation (v_Self: Type0) = {
  f_double_pre:x: u8
    -> pred:
      Type0
        { (Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) <=
          (127 <: Hax_lib.Int.t_Int) ==>
          pred };
  f_double_post:x: u8 -> result: u8
    -> pred:
      Type0
        { pred ==>
          ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) * (2 <: Hax_lib.Int.t_Int)
            <:
            Hax_lib.Int.t_Int) =
          (Rust_primitives.Hax.Int.from_machine result <: Hax_lib.Int.t_Int) };
  f_double:x0: u8 -> Prims.Pure u8 (f_double_pre x0) (fun result -> f_double_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Operation t_ViaAdd =
  {
    f_double_pre
    =
    (fun (x: u8) ->
        (Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) <= (127 <: Hax_lib.Int.t_Int));
    f_double_post
    =
    (fun (x: u8) (result: u8) ->
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) * (2 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) =
        (Rust_primitives.Hax.Int.from_machine result <: Hax_lib.Int.t_Int));
    f_double = fun (x: u8) -> x +! x
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Operation_for_ViaMul: t_Operation t_ViaMul =
  {
    f_double_pre
    =
    (fun (x: u8) ->
        (Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) <= (127 <: Hax_lib.Int.t_Int));
    f_double_post
    =
    (fun (x: u8) (result: u8) ->
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) * (2 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) =
        (Rust_primitives.Hax.Int.from_machine result <: Hax_lib.Int.t_Int));
    f_double = fun (x: u8) -> x *! mk_u8 2
  }

class t_TraitWithRequiresAndEnsures (v_Self: Type0) = {
  f_method_pre:self_: v_Self -> x: u8 -> pred: Type0{x <. mk_u8 100 ==> pred};
  f_method_post:self_: v_Self -> x: u8 -> r: u8 -> pred: Type0{pred ==> r >. mk_u8 88};
  f_method:x0: v_Self -> x1: u8
    -> Prims.Pure u8 (f_method_pre x0 x1) (fun result -> f_method_post x0 x1 result)
}

/// @fail(extraction): proverif(HAX0001)
let test
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_TraitWithRequiresAndEnsures v_T)
      (x: v_T)
    : u8 = (f_method #v_T #FStar.Tactics.Typeclasses.solve x (mk_u8 99) <: u8) -! mk_u8 88
