module New_tests.Legacy__side_effects__lib.Issue_1083_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_MyFrom (v_Self: Type0) (v_T: Type0) = {
  f_my_from_pre:v_T -> Type0;
  f_my_from_post:v_T -> v_Self -> Type0;
  f_my_from:x0: v_T -> Prims.Pure v_Self (f_my_from_pre x0) (fun result -> f_my_from_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_MyFrom u16 u8 =
  {
    f_my_from_pre = (fun (x: u8) -> true);
    f_my_from_post = (fun (x: u8) (out: u16) -> true);
    f_my_from = fun (x: u8) -> cast (x <: u8) <: u16
  }

/// @fail(extraction): proverif(HAX0001, HAX0001)
let f (x: u8) : Core_models.Result.t_Result u16 u16 =
  match
    Core_models.Ops.Try_trait.f_branch #(Core_models.Result.t_Result Rust_primitives.Hax.t_Never u8)
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Result.Result_Err (mk_u8 1)
        <:
        Core_models.Result.t_Result Rust_primitives.Hax.t_Never u8)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result Core_models.Convert.t_Infallible u8) Rust_primitives.Hax.t_Never
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break residual ->
    Core_models.Ops.Try_trait.f_from_residual #(Core_models.Result.t_Result u16 u16)
      #(Core_models.Result.t_Result Core_models.Convert.t_Infallible u8)
      #FStar.Tactics.Typeclasses.solve
      residual
  | Core_models.Ops.Control_flow.ControlFlow_Continue v_val ->
    let _:Rust_primitives.Hax.t_Never = v_val in
    Core_models.Result.Result_Ok (f_my_from #u16 #u8 #FStar.Tactics.Typeclasses.solve x)
    <:
    Core_models.Result.t_Result u16 u16
