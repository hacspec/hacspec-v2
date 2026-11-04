module New_tests.Legacy__hoisting__lib.Control_flow_capture
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let fallible (_: Prims.unit) : Core_models.Result.t_Result bool u8 =
  Core_models.Result.Result_Ok true <: Core_models.Result.t_Result bool u8

let or_ok (b: bool) : Core_models.Result.t_Result bool u8 =
  let ok:bool = false in
  if b
  then
    let r:bool = true in
    Core_models.Result.Result_Ok (ok && r) <: Core_models.Result.t_Result bool u8
  else
    match fallible () <: Core_models.Result.t_Result bool u8 with
    | Core_models.Result.Result_Ok ok_1_ ->
      let r:bool = ok_1_ in
      Core_models.Result.Result_Ok (ok && r) <: Core_models.Result.t_Result bool u8
    | Core_models.Result.Result_Err err ->
      Core_models.Result.Result_Err err <: Core_models.Result.t_Result bool u8

let if_ok (b: bool) : Core_models.Result.t_Result bool u8 =
  let ok:bool = false in
  if b
  then
    let r:bool = true in
    Core_models.Result.Result_Ok (ok && r) <: Core_models.Result.t_Result bool u8
  else
    match fallible () <: Core_models.Result.t_Result bool u8 with
    | Core_models.Result.Result_Ok ok_1_ ->
      let r:bool = ok_1_ in
      Core_models.Result.Result_Ok (ok && r) <: Core_models.Result.t_Result bool u8
    | Core_models.Result.Result_Err err ->
      Core_models.Result.Result_Err err <: Core_models.Result.t_Result bool u8

let or_some (b: bool) (o: Core_models.Option.t_Option bool) : Core_models.Option.t_Option bool =
  let some:bool = false in
  if b
  then
    let r:bool = true in
    Core_models.Option.Option_Some (some && r) <: Core_models.Option.t_Option bool
  else
    match o <: Core_models.Option.t_Option bool with
    | Core_models.Option.Option_Some some_1_ ->
      let r:bool = some_1_ in
      Core_models.Option.Option_Some (some && r) <: Core_models.Option.t_Option bool
    | Core_models.Option.Option_None  ->
      Core_models.Option.Option_None <: Core_models.Option.t_Option bool

let fresh_name_taken (b: bool) : Core_models.Result.t_Result bool u8 =
  let ok:bool = false in
  let ok_1_:bool = true in
  if b
  then
    let r:bool = true in
    Core_models.Result.Result_Ok (ok && r && ok_1_) <: Core_models.Result.t_Result bool u8
  else
    match fallible () <: Core_models.Result.t_Result bool u8 with
    | Core_models.Result.Result_Ok ok_2_ ->
      let r:bool = ok_2_ in
      Core_models.Result.Result_Ok (ok && r && ok_1_) <: Core_models.Result.t_Result bool u8
    | Core_models.Result.Result_Err err ->
      Core_models.Result.Result_Err err <: Core_models.Result.t_Result bool u8

let fb (x: u8) : Core_models.Result.t_Result u8 u8 =
  Core_models.Result.Result_Ok x <: Core_models.Result.t_Result u8 u8

let mutated_ok (b: bool) : Core_models.Result.t_Result u8 u8 =
  let ok:u8 = mk_u8 0 in
  if b
  then
    let ok:u8 = mk_u8 1 in
    match fb (mk_u8 5) <: Core_models.Result.t_Result u8 u8 with
    | Core_models.Result.Result_Ok ok_1_ ->
      let (ok: u8), (r: u8) = ok, ok_1_ <: (u8 & u8) in
      Core_models.Result.Result_Ok (Core_models.Num.impl_u8__wrapping_add ok r)
      <:
      Core_models.Result.t_Result u8 u8
    | Core_models.Result.Result_Err err ->
      Core_models.Result.Result_Err err <: Core_models.Result.t_Result u8 u8
  else
    let (ok: u8), (r: u8) = ok, mk_u8 0 <: (u8 & u8) in
    Core_models.Result.Result_Ok (Core_models.Num.impl_u8__wrapping_add ok r)
    <:
    Core_models.Result.t_Result u8 u8

let bump (v: u8) : (u8 & u8) =
  let v:u8 = Core_models.Num.impl_u8__wrapping_add v (mk_u8 1) in
  let hax_temp_output:u8 = v in
  v, hax_temp_output <: (u8 & u8)

let add (a b: u8) : u8 = Core_models.Num.impl_u8__wrapping_add a b

let mutated_tmp0 (b: bool) (y: u8) : u8 =
  let tmp0:u8 = mk_u8 0 in
  let ((tmp0: u8), (y: u8)), (r: u8) =
    if b
    then
      let tmp0:u8 = mk_u8 1 in
      let (tmp0_1_: u8), (out: u8) = bump y in
      let y:u8 = tmp0_1_ in
      (tmp0, y <: (u8 & u8)), out <: ((u8 & u8) & u8)
    else (tmp0, y <: (u8 & u8)), mk_u8 0 <: ((u8 & u8) & u8)
  in
  add (add tmp0 r <: u8) y

let mutated_hoist (b: bool) (y: u8) : u8 =
  let hoist1:u8 = mk_u8 0 in
  let hoist2:u8 = mk_u8 0 in
  let ((hoist1: u8), (hoist2: u8), (y: u8)), (r: u8) =
    if b
    then
      let hoist1:u8 = mk_u8 1 in
      let hoist2:u8 = mk_u8 1 in
      let (tmp0: u8), (out: u8) = bump y in
      let y:u8 = tmp0 in
      let hoist16:u8 = out in
      let (tmp0: u8), (out: u8) = bump y in
      let y:u8 = tmp0 in
      (hoist1, hoist2, y <: (u8 & u8 & u8)), add hoist16 out <: ((u8 & u8 & u8) & u8)
    else (hoist1, hoist2, y <: (u8 & u8 & u8)), mk_u8 0 <: ((u8 & u8 & u8) & u8)
  in
  add (add hoist1 hoist2 <: u8) r

let shadowing_let (b: bool) : Core_models.Result.t_Result u8 u8 =
  let x:u8 = mk_u8 5 in
  if b
  then
    let x_1_:u8 = x +! mk_u8 1 in
    match fallible () <: Core_models.Result.t_Result bool u8 with
    | Core_models.Result.Result_Ok hoist17 ->
      if hoist17
      then Core_models.Result.Result_Ok x_1_ <: Core_models.Result.t_Result u8 u8
      else
        let r:u8 = x_1_ in
        Core_models.Result.Result_Ok (x +! r) <: Core_models.Result.t_Result u8 u8
    | Core_models.Result.Result_Err err ->
      Core_models.Result.Result_Err err <: Core_models.Result.t_Result u8 u8
  else
    let r:u8 = mk_u8 2 in
    Core_models.Result.Result_Ok (x +! r) <: Core_models.Result.t_Result u8 u8
