module New_tests.Legacy__cyclic_modules__lib.Rec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_T =
  | T_t1 : t_T
  | T_t2 : t_T

let t_T_cast_to_repr (x: t_T) : isize =
  match x <: t_T with
  | T_t1  -> mk_isize 0
  | T_t2  -> mk_isize 1

/// @fail(extraction): proverif(HAX0001)
let rec hf (x: t_T) : t_T =
  match x <: t_T with
  | T_t1  -> hf (T_t2 <: t_T)
  | T_t2  -> x

/// @fail(extraction): proverif(HAX0001)
let rec g2 (x: t_T) : t_T =
  match x <: t_T with
  | T_t1  -> g1 x
  | T_t2  -> hf x

/// @fail(extraction): proverif(HAX0001)
and g1 (x: t_T) : t_T =
  match x <: t_T with
  | T_t1  -> g2 x
  | T_t2  -> T_t1 <: t_T
