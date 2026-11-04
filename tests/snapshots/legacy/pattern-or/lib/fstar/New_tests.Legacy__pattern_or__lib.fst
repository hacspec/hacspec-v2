module New_tests.Legacy__pattern_or__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_E =
  | E_A : t_E
  | E_B : t_E

let t_E_cast_to_repr (x: t_E) : isize =
  match x <: t_E with
  | E_A  -> mk_isize 0
  | E_B  -> mk_isize 1

let bar (x: t_E) : Prims.unit = match x <: t_E with | E_A  | E_B  -> () <: Prims.unit

let nested (x: Core_models.Option.t_Option i32) : i32 =
  match x <: Core_models.Option.t_Option i32 with
  | Core_models.Option.Option_Some (Rust_primitives.Integers.MkInt 1)
  | Core_models.Option.Option_Some (Rust_primitives.Integers.MkInt 2) -> mk_i32 1
  | Core_models.Option.Option_Some x -> x
  | Core_models.Option.Option_None  -> mk_i32 0

let deep (x: (i32 & Core_models.Option.t_Option i32)) : i32 =
  match x <: (i32 & Core_models.Option.t_Option i32) with
  | Rust_primitives.Integers.MkInt 1,
  Core_models.Option.Option_Some (Rust_primitives.Integers.MkInt 3)
  | Rust_primitives.Integers.MkInt 1,
  Core_models.Option.Option_Some (Rust_primitives.Integers.MkInt 4)
  | Rust_primitives.Integers.MkInt 2,
  Core_models.Option.Option_Some (Rust_primitives.Integers.MkInt 3)
  | Rust_primitives.Integers.MkInt 2,
  Core_models.Option.Option_Some (Rust_primitives.Integers.MkInt 4) ->
    mk_i32 0
  | x, _ -> x

let equivalent (x: (i32 & Core_models.Option.t_Option i32)) : i32 =
  match x <: (i32 & Core_models.Option.t_Option i32) with
  | Rust_primitives.Integers.MkInt 1,
  Core_models.Option.Option_Some (Rust_primitives.Integers.MkInt 3)
  | Rust_primitives.Integers.MkInt 1,
  Core_models.Option.Option_Some (Rust_primitives.Integers.MkInt 4)
  | Rust_primitives.Integers.MkInt 2,
  Core_models.Option.Option_Some (Rust_primitives.Integers.MkInt 3)
  | Rust_primitives.Integers.MkInt 2,
  Core_models.Option.Option_Some (Rust_primitives.Integers.MkInt 4) ->
    mk_i32 0
  | x, _ -> x

/// @fail(extraction): proverif(HAX0001, HAX0001)
let deep_capture (x: Core_models.Result.t_Result (i32 & i32) (i32 & i32)) : i32 =
  match x <: Core_models.Result.t_Result (i32 & i32) (i32 & i32) with
  | Core_models.Result.Result_Ok (Rust_primitives.Integers.MkInt 1, x)
  | Core_models.Result.Result_Ok (Rust_primitives.Integers.MkInt 2, x)
  | Core_models.Result.Result_Err (Rust_primitives.Integers.MkInt 3, x)
  | Core_models.Result.Result_Err (Rust_primitives.Integers.MkInt 4, x) -> x
  | Core_models.Result.Result_Ok (x, _) | Core_models.Result.Result_Err (x, _) -> x
