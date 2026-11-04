module New_tests.Legacy__hoisting__lib.Short_circuit_panic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let index (v: t_Slice u8) (i: usize) : bool =
  i >=. (Core_models.Slice.impl__len #u8 v <: usize) || (v.[ i ] <: u8) >. mk_u8 0

let division (a b: u8) : bool = b =. mk_u8 0 || (a /! b <: u8) >. mk_u8 1

let overflow (a b: u8) : bool = a >. mk_u8 200 || (a +! b <: u8) >. mk_u8 3

let nested (a: bool) (v: t_Slice u8) (i: usize) : bool =
  a && (i >=. (Core_models.Slice.impl__len #u8 v <: usize) || (v.[ i ] <: u8) >. mk_u8 0)

/// @fail(extraction): coq(HAX0001, HAX0001), ssprove(HAX0001), proverif(HAX0008)
let while_condition (n m: u8) : u8 =
  let i:u8 = mk_u8 0 in
  let j:u8 = mk_u8 0 in
  let (i: u8), (j: u8) =
    Rust_primitives.Hax.while_loop (fun temp_0_ ->
          let (i: u8), (j: u8) = temp_0_ in
          true)
      (fun temp_0_ ->
          let (i: u8), (j: u8) = temp_0_ in
          (i <. n <: bool) && (j <. m <: bool) && (~.(i =. mk_u8 3 <: bool) <: bool))
      (fun temp_0_ ->
          let (i: u8), (j: u8) = temp_0_ in
          Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
      (i, j <: (u8 & u8))
      (fun temp_0_ ->
          let (i: u8), (j: u8) = temp_0_ in
          let i:u8 = i +! mk_u8 1 in
          let j:u8 = j +! mk_u8 1 in
          i, j <: (u8 & u8))
  in
  i

/// @fail(extraction): coq(HAX0001, HAX0001), ssprove(HAX0001), proverif(HAX0008)
let while_condition_len (v: t_Slice u8) (n: usize) : usize =
  let i:usize = mk_usize 0 in
  let i:usize =
    Rust_primitives.Hax.while_loop (fun i ->
          let i:usize = i in
          true)
      (fun i ->
          let i:usize = i in
          (i <. n <: bool) && (i <. (Core_models.Slice.impl__len #u8 v <: usize) <: bool))
      (fun i ->
          let i:usize = i in
          Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
      i
      (fun i ->
          let i:usize = i in
          let i:usize = i +! mk_usize 1 in
          i)
  in
  i
