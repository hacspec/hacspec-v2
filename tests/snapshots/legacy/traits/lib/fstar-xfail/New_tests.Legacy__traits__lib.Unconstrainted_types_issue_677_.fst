module New_tests.Legacy__traits__lib.Unconstrainted_types_issue_677_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_PolyOp (v_Self: Type0) = {
  f_op_pre:u32 -> u32 -> Type0;
  f_op_post:u32 -> u32 -> u32 -> Type0;
  f_op:x0: u32 -> x1: u32 -> Prims.Pure u32 (f_op_pre x0 x1) (fun result -> f_op_post x0 x1 result)
}

type t_Plus = | Plus : t_Plus

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_PolyOp t_Plus =
  {
    f_op_pre = (fun (x: u32) (y: u32) -> true);
    f_op_post = (fun (x: u32) (y: u32) (out: u32) -> true);
    f_op = fun (x: u32) (y: u32) -> x +! y
  }

type t_Times = | Times : t_Times

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_PolyOp_for_Times: t_PolyOp t_Times =
  {
    f_op_pre = (fun (x: u32) (y: u32) -> true);
    f_op_post = (fun (x: u32) (y: u32) (out: u32) -> true);
    f_op = fun (x: u32) (y: u32) -> x *! y
  }

/// @fail(extraction): proverif(HAX0001)
let twice (#v_OP: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PolyOp v_OP) (x: u32)
    : u32 = f_op #v_OP #FStar.Tactics.Typeclasses.solve x x

let both (x: u32) : (u32 & u32) = twice #t_Plus x, twice #t_Times x <: (u32 & u32)
