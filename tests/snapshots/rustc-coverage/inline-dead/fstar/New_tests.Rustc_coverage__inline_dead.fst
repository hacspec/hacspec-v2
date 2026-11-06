module New_tests.Rustc_coverage__inline_dead
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let dead (_: Prims.unit) : u32 = mk_u32 42

/// @fail(extraction): proverif(HAX0001)
let live (v_B: bool) (_: Prims.unit) : u32 = if v_B then dead () else mk_u32 0

/// @fail(extraction): ssprove(HAX0001)
/// @fail(extraction): proverif(HAX0001, HAX0001)
let main (_: Prims.unit) : Prims.unit =
  let args:u32 = live false () <: u32 in
  let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
    let list = [Core_models.Fmt.Rt.impl__new_display #u32 args] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list 1 list
  in
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
          (mk_usize 1)
          (let list = [""; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list)
          args
        <:
        Core_models.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  let f: bool -> Prims.unit =
    fun x ->
      let x:bool = x in
      let _:Prims.unit =
        if true
        then
          let _:Prims.unit = Hax_lib.v_assert x in
          ()
      in
      ()
  in
  let _:Prims.unit =
    Core_models.Ops.Function.f_call #(bool -> Prims.unit)
      #bool
      #FStar.Tactics.Typeclasses.solve
      f
      (false <: bool)
  in
  ()
