module New_tests.Rustc_coverage__attr__nested
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let do_stuff (_: Prims.unit) : Prims.unit = ()

let outer_fn (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = do_stuff () in
  ()

let outer_fn__middle_fn (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = do_stuff () in
  ()

let outer_fn__middle_fn__inner_fn (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = do_stuff () in
  ()

type t_MyOuter = | MyOuter : t_MyOuter

let impl_MyOuter__outer_method (self: t_MyOuter) : Prims.unit =
  let _:Prims.unit = do_stuff () in
  ()

type impl_MyOuter__outer_method__t_MyMiddle =
  | C_impl_MyOuter__outer_method__MyMiddle : impl_MyOuter__outer_method__t_MyMiddle

let impl_MyOuter__outer_method__impl__middle_method (self: impl_MyOuter__outer_method__t_MyMiddle)
    : Prims.unit =
  let _:Prims.unit = do_stuff () in
  ()

type impl_MyOuter__outer_method__impl__middle_method__t_MyInner =
  | C_impl_MyOuter__outer_method__impl__middle_method__MyInner : impl_MyOuter__outer_method__impl__middle_method__t_MyInner

let impl_MyOuter__outer_method__impl__middle_method__impl__inner_method
      (self: impl_MyOuter__outer_method__impl__middle_method__t_MyInner)
    : Prims.unit =
  let _:Prims.unit = do_stuff () in
  ()

class t_MyTrait (v_Self: Type0) = {
  f_trait_method_pre:v_Self -> Type0;
  f_trait_method_post:v_Self -> Prims.unit -> Type0;
  f_trait_method:x0: v_Self
    -> Prims.Pure Prims.unit (f_trait_method_pre x0) (fun result -> f_trait_method_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_MyTrait_for_MyOuter: t_MyTrait t_MyOuter =
  {
    f_trait_method_pre = (fun (self: t_MyOuter) -> true);
    f_trait_method_post = (fun (self: t_MyOuter) (out: Prims.unit) -> true);
    f_trait_method
    =
    fun (self: t_MyOuter) ->
      let _:Prims.unit = do_stuff () in
      ()
  }

type f_trait_method__impl_MyTrait_for_MyOuter__t_MyMiddle =
  | C_f_trait_method__impl_MyTrait_for_MyOuter__MyMiddle : f_trait_method__impl_MyTrait_for_MyOuter__t_MyMiddle

[@@ FStar.Tactics.Typeclasses.tcinstance]
let f_trait_method__impl_MyTrait_for_MyOuter__impl: t_MyTrait
f_trait_method__impl_MyTrait_for_MyOuter__t_MyMiddle =
  {
    f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method_pre
    =
    (fun (self: f_trait_method__impl_MyTrait_for_MyOuter__t_MyMiddle) -> true);
    f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method_post
    =
    (fun (self: f_trait_method__impl_MyTrait_for_MyOuter__t_MyMiddle) (out: Prims.unit) -> true);
    f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method
    =
    fun (self: f_trait_method__impl_MyTrait_for_MyOuter__t_MyMiddle) ->
      let _:Prims.unit = do_stuff () in
      ()
  }

type f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method__impl__t_MyInner =
  | C_f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method__impl__MyInner : f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method__impl__t_MyInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
let f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method__impl__impl: t_MyTrait
f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method__impl__t_MyInner =
  {
    f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method__impl__f_trait_method_pre
    =
    (fun (self: f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method__impl__t_MyInner) -> true);
    f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method__impl__f_trait_method_post
    =
    (fun
        (self: f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method__impl__t_MyInner)
        (out: Prims.unit)
        ->
        true);
    f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method__impl__f_trait_method
    =
    fun (self: f_trait_method__impl_MyTrait_for_MyOuter__f_trait_method__impl__t_MyInner) ->
      let _:Prims.unit = do_stuff () in
      ()
  }

/// @fail(extraction): proverif(HAX0001)
let cclosure_expr (_: Prims.unit) : Prims.unit =
  let e_outer: Prims.unit -> Prims.unit =
    fun temp_0_ ->
      let _:Prims.unit = temp_0_ in
      let e_middle: Prims.unit -> Prims.unit =
        fun temp_0_ ->
          let _:Prims.unit = temp_0_ in
          let e_inner: Prims.unit -> Prims.unit =
            fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              let _:Prims.unit = do_stuff () in
              ()
          in
          let _:Prims.unit = do_stuff () in
          ()
      in
      let _:Prims.unit = do_stuff () in
      ()
  in
  let _:Prims.unit = do_stuff () in
  ()

/// @fail(extraction): proverif(HAX0001)
let cclosure_tail (_: Prims.unit) : Prims.unit =
  let e_outer: Prims.unit -> Prims.unit =
    fun temp_0_ ->
      let _:Prims.unit = temp_0_ in
      let e_middle: Prims.unit -> Prims.unit =
        fun temp_0_ ->
          let _:Prims.unit = temp_0_ in
          let e_inner: Prims.unit -> Prims.unit =
            fun temp_0_ ->
              let _:Prims.unit = temp_0_ in
              let _:Prims.unit = do_stuff () in
              ()
          in
          let _:Prims.unit = do_stuff () in
          ()
      in
      let _:Prims.unit = do_stuff () in
      ()
  in
  let _:Prims.unit = do_stuff () in
  ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = outer_fn () in
  let _:Prims.unit = impl_MyOuter__outer_method (MyOuter <: t_MyOuter) in
  let _:Prims.unit =
    f_trait_method #t_MyOuter #FStar.Tactics.Typeclasses.solve (MyOuter <: t_MyOuter)
  in
  let _:Prims.unit = cclosure_expr () in
  let _:Prims.unit = cclosure_tail () in
  ()
