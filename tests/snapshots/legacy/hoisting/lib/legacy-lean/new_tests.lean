
-- Legacy lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/legacy-lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace new_tests.legacy__hoisting__lib.issue_2336

@[spec]
def change (value : Bool) : RustM (rust_primitives.hax.Tuple2 Bool Bool) := do
  let value : Bool := true;
  let hax_temp_output : Bool := false;
  (pure (rust_primitives.hax.Tuple2.mk value hax_temp_output))

@[spec]
def or_mut_ref (first : Bool) (value : Bool) :
    RustM (rust_primitives.hax.Tuple2 Bool Bool) := do
  let ⟨value, hax_temp_output⟩ ←
    if first then do
      (pure (rust_primitives.hax.Tuple2.mk value true))
    else do
      let ⟨tmp0, out⟩ ← (change value);
      let value : Bool := tmp0;
      (pure (rust_primitives.hax.Tuple2.mk value out));
  (pure (rust_primitives.hax.Tuple2.mk value hax_temp_output))

@[spec]
def and_mut_ref (first : Bool) (value : Bool) :
    RustM (rust_primitives.hax.Tuple2 Bool Bool) := do
  let ⟨value, hax_temp_output⟩ ←
    if first then do
      let ⟨tmp0, out⟩ ← (change value);
      let value : Bool := tmp0;
      (pure (rust_primitives.hax.Tuple2.mk value out))
    else do
      (pure (rust_primitives.hax.Tuple2.mk value false));
  (pure (rust_primitives.hax.Tuple2.mk value hax_temp_output))

@[spec]
def or_assign (first : Bool) : RustM u8 := do
  let x : u8 := (0 : u8);
  let x : u8 ←
    if first then do (pure x) else do let x : u8 := (1 : u8); (pure x);
  (pure x)

@[spec]
def fallible (b : Bool) : RustM (core_models.result.Result Bool u8) := do
  if b then do
    (pure (core_models.result.Result.Ok true))
  else do
    (pure (core_models.result.Result.Err (1 : u8)))

@[spec]
def or_question_mark (first : Bool) :
    RustM (core_models.result.Result Bool u8) := do
  if first then do
    (pure (core_models.result.Result.Ok true))
  else do
    match (← (fallible false)) with
      | (core_models.result.Result.Ok  ok) => do
        (pure (core_models.result.Result.Ok ok))
      | (core_models.result.Result.Err  err) => do
        (pure (core_models.result.Result.Err err))

@[spec]
def or_return (first : Bool) : RustM u8 := do
  if first then do let _ := true; (pure (0 : u8)) else do (pure (1 : u8))

@[spec]
def and_local_let (i : usize) (v : (RustSlice u8)) (value : Bool) :
    RustM (rust_primitives.hax.Tuple2 Bool Bool) := do
  let ⟨value, hax_temp_output⟩ ←
    if (← (i <? (← (core_models.slice.Impl.len u8 v)))) then do
      let x : u8 ← v[i]_?;
      if (← (x >? (0 : u8))) then do
        (pure (rust_primitives.hax.Tuple2.mk value true))
      else do
        let ⟨tmp0, out⟩ ← (change value);
        let value : Bool := tmp0;
        (pure (rust_primitives.hax.Tuple2.mk value out))
    else do
      (pure (rust_primitives.hax.Tuple2.mk value false));
  (pure (rust_primitives.hax.Tuple2.mk value hax_temp_output))

@[spec]
def if_condition (first : Bool) (value : Bool) :
    RustM (rust_primitives.hax.Tuple2 Bool u8) := do
  let ⟨value, hoist3⟩ ←
    if first then do
      (pure (rust_primitives.hax.Tuple2.mk value true))
    else do
      let ⟨tmp0, out⟩ ← (change value);
      let value : Bool := tmp0;
      (pure (rust_primitives.hax.Tuple2.mk value out));
  let hax_temp_output : u8 ←
    if hoist3 then do (pure (1 : u8)) else do (pure (0 : u8));
  (pure (rust_primitives.hax.Tuple2.mk value hax_temp_output))

--  @fail(extraction): proverif(HAX0008)
@[spec]
def match_guard (o : (core_models.option.Option u8)) (value : Bool) :
    RustM (rust_primitives.hax.Tuple2 Bool u8) := do
  let ⟨value, hoist5⟩ ←
    match o with
      | (core_models.option.Option.Some  x) => do
        let ⟨value, hoist4⟩ ←
          if (← (x >? (3 : u8))) then do
            (pure (rust_primitives.hax.Tuple2.mk value true))
          else do
            let ⟨tmp0, out⟩ ← (change value);
            let value : Bool := tmp0;
            (pure (rust_primitives.hax.Tuple2.mk value out));
        match hoist4 with
          | true => do
            (pure (rust_primitives.hax.Tuple2.mk
              value
              (core_models.option.Option.Some x)))
          | _ => do
            (pure (rust_primitives.hax.Tuple2.mk
              value
              core_models.option.Option.None))
      | _ => do
        (pure (rust_primitives.hax.Tuple2.mk
          value
          core_models.option.Option.None));
  let hax_temp_output : u8 ←
    match hoist5 with
      | (core_models.option.Option.Some  x) => do (pure x)
      | (core_models.option.Option.None ) => do (pure (0 : u8));
  (pure (rust_primitives.hax.Tuple2.mk value hax_temp_output))

@[spec]
def pure_operands (a : Bool) (b : Bool) (c : u8) : RustM Bool := do
  (a &&? (← (b ||? (← (c >? (3 : u8))))))

@[spec]
def left_mut_ref (second : Bool) (value : Bool) :
    RustM (rust_primitives.hax.Tuple2 Bool Bool) := do
  let ⟨tmp0, out⟩ ← (change value);
  let value : Bool := tmp0;
  let hax_temp_output : Bool ← (out ||? second);
  (pure (rust_primitives.hax.Tuple2.mk value hax_temp_output))

@[spec]
def both_mut_refs (a : Bool) (b : Bool) :
    RustM (rust_primitives.hax.Tuple3 Bool Bool Bool) := do
  let ⟨tmp0, out⟩ ← (change a);
  let a : Bool := tmp0;
  let ⟨b, hax_temp_output⟩ ←
    if out then do
      let ⟨tmp0, out⟩ ← (change b);
      let b : Bool := tmp0;
      (pure (rust_primitives.hax.Tuple2.mk b out))
    else do
      (pure (rust_primitives.hax.Tuple2.mk b false));
  (pure (rust_primitives.hax.Tuple3.mk a b hax_temp_output))

@[spec]
def chained (first : Bool) (second : Bool) (value : Bool) :
    RustM (rust_primitives.hax.Tuple2 Bool Bool) := do
  let ⟨value, hax_temp_output⟩ ←
    if (← (first ||? second)) then do
      (pure (rust_primitives.hax.Tuple2.mk value true))
    else do
      let ⟨tmp0, out⟩ ← (change value);
      let value : Bool := tmp0;
      (pure (rust_primitives.hax.Tuple2.mk value out));
  (pure (rust_primitives.hax.Tuple2.mk value hax_temp_output))

end new_tests.legacy__hoisting__lib.issue_2336


namespace new_tests.legacy__hoisting__lib.while_condition

--  @fail(extraction): coq(HAX0001, HAX0001), ssprove(HAX0001), proverif(HAX0008)
@[spec]
def local_let (_ : rust_primitives.hax.Tuple0) : RustM u8 := do
  let n : u8 := (0 : u8);
  let n : u8 ←
    (rust_primitives.hax.while_loop
      (fun n => (do (pure true) : RustM Bool))
      (fun n =>
        (do
        let y : u8 ← (core_models.num.Impl_6.wrapping_add n (1 : u8));
        (y <? (4 : u8)) :
        RustM Bool))
      (fun n =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      n
      (fun n => (do let n : u8 ← (n +? (1 : u8)); (pure n) : RustM u8)));
  (pure n)

--  @fail(extraction): coq(HAX0001, HAX0001), ssprove(HAX0001), proverif(HAX0008)
@[spec]
def local_mut (_ : rust_primitives.hax.Tuple0) : RustM u8 := do
  let n : u8 := (0 : u8);
  let n : u8 ←
    (rust_primitives.hax.while_loop
      (fun n => (do (pure true) : RustM Bool))
      (fun n =>
        (do
        let y : u8 := n;
        let y : u8 ← (core_models.num.Impl_6.wrapping_add y (1 : u8));
        (y <? (4 : u8)) :
        RustM Bool))
      (fun n =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      n
      (fun n => (do let n : u8 ← (n +? (1 : u8)); (pure n) : RustM u8)));
  (pure n)

--  @fail(extraction): coq(HAX0001, HAX0001, HAX0008), ssprove(HAX0008, HAX0001), proverif(HAX0008, HAX0008)
opaque inner_loop (n : u8) : RustM u8

@[spec]
def dec (x : u8) : RustM (rust_primitives.hax.Tuple2 u8 Bool) := do
  let ⟨x, hax_temp_output⟩ ←
    if (← (x ==? (0 : u8))) then do
      (pure (rust_primitives.hax.Tuple2.mk x false))
    else do
      let x : u8 ← (x -? (1 : u8));
      (pure (rust_primitives.hax.Tuple2.mk x true));
  (pure (rust_primitives.hax.Tuple2.mk x hax_temp_output))

@[spec]
def fallible (b : Bool) : RustM (core_models.result.Result Bool u8) := do
  if b then do
    (pure (core_models.result.Result.Ok true))
  else do
    (pure (core_models.result.Result.Err (1 : u8)))

end new_tests.legacy__hoisting__lib.while_condition


namespace new_tests.legacy__hoisting__lib.evaluation_order

@[spec]
def add (a : u8) (b : u8) : RustM u8 := do
  (core_models.num.Impl_6.wrapping_add a b)

@[spec]
def bump (v : u8) : RustM (rust_primitives.hax.Tuple2 u8 u8) := do
  let v : u8 ← (core_models.num.Impl_6.wrapping_add v (1 : u8));
  let hax_temp_output : u8 := (1 : u8);
  (pure (rust_primitives.hax.Tuple2.mk v hax_temp_output))

@[spec]
def set (v : u8) : RustM (rust_primitives.hax.Tuple2 u8 u8) := do
  let v : u8 := (7 : u8);
  let hax_temp_output : u8 := (2 : u8);
  (pure (rust_primitives.hax.Tuple2.mk v hax_temp_output))

@[spec]
def read_then_assign (_ : rust_primitives.hax.Tuple0) : RustM u8 := do
  let v : u8 := (0 : u8);
  let hoist9 : u8 := v;
  let v : u8 := (5 : u8);
  (add hoist9 (1 : u8))

@[spec]
def read_then_mut_ref (v : u8) : RustM (rust_primitives.hax.Tuple2 u8 u8) := do
  let hoist11 : u8 := v;
  let ⟨tmp0, out⟩ ← (bump v);
  let v : u8 := tmp0;
  let hax_temp_output : u8 ← (add hoist11 out);
  (pure (rust_primitives.hax.Tuple2.mk v hax_temp_output))

@[spec]
def two_mut_refs (a : u8) (b : u8) :
    RustM (rust_primitives.hax.Tuple3 u8 u8 u8) := do
  let ⟨tmp0, out⟩ ← (bump a);
  let a : u8 := tmp0;
  let hoist13 : u8 := out;
  let ⟨tmp0, out⟩ ← (set b);
  let b : u8 := tmp0;
  let hax_temp_output : u8 ← (add hoist13 out);
  (pure (rust_primitives.hax.Tuple3.mk a b hax_temp_output))

end new_tests.legacy__hoisting__lib.evaluation_order


namespace new_tests.legacy__hoisting__lib.issue_1734

@[spec]
def hoisted_let (x : u8) : RustM u8 := do
  let x_1 : i32 := (9 : i32);
  ((0 : u8) +? x)

@[spec]
def hoisted_let_rhs (x : u8) : RustM u8 := do
  let x_1 : u8 ← (core_models.num.Impl_6.wrapping_add x (1 : u8));
  let y : u8 ← (core_models.num.Impl_6.wrapping_mul x_1 (2 : u8));
  (core_models.num.Impl_6.wrapping_add y x)

@[spec]
def add (a : u8) (b : u8) : RustM u8 := do
  (core_models.num.Impl_6.wrapping_add a b)

@[spec]
def two_hoisted_lets (x : u8) : RustM u8 := do
  let x_2 : u8 := (1 : u8);
  let x_1 : u8 := (2 : u8);
  (add (← (add x_2 x_1)) x)

end new_tests.legacy__hoisting__lib.issue_1734


namespace new_tests.legacy__hoisting__lib.control_flow_capture

@[spec]
def fallible (_ : rust_primitives.hax.Tuple0) :
    RustM (core_models.result.Result Bool u8) := do
  (pure (core_models.result.Result.Ok true))

@[spec]
def or_ok (b : Bool) : RustM (core_models.result.Result Bool u8) := do
  let ok : Bool := false;
  if b then do
    let r : Bool := true;
    (pure (core_models.result.Result.Ok (← (ok &&? r))))
  else do
    match (← (fallible rust_primitives.hax.Tuple0.mk)) with
      | (core_models.result.Result.Ok  ok_1) => do
        let r : Bool := ok_1;
        (pure (core_models.result.Result.Ok (← (ok &&? r))))
      | (core_models.result.Result.Err  err) => do
        (pure (core_models.result.Result.Err err))

@[spec]
def if_ok (b : Bool) : RustM (core_models.result.Result Bool u8) := do
  let ok : Bool := false;
  if b then do
    let r : Bool := true;
    (pure (core_models.result.Result.Ok (← (ok &&? r))))
  else do
    match (← (fallible rust_primitives.hax.Tuple0.mk)) with
      | (core_models.result.Result.Ok  ok_1) => do
        let r : Bool := ok_1;
        (pure (core_models.result.Result.Ok (← (ok &&? r))))
      | (core_models.result.Result.Err  err) => do
        (pure (core_models.result.Result.Err err))

@[spec]
def or_some (b : Bool) (o : (core_models.option.Option Bool)) :
    RustM (core_models.option.Option Bool) := do
  let some : Bool := false;
  if b then do
    let r : Bool := true;
    (pure (core_models.option.Option.Some (← (some &&? r))))
  else do
    match o with
      | (core_models.option.Option.Some  some_1) => do
        let r : Bool := some_1;
        (pure (core_models.option.Option.Some (← (some &&? r))))
      | (core_models.option.Option.None ) => do
        (pure core_models.option.Option.None)

@[spec]
def fresh_name_taken (b : Bool) :
    RustM (core_models.result.Result Bool u8) := do
  let ok : Bool := false;
  let ok_1 : Bool := true;
  if b then do
    let r : Bool := true;
    (pure (core_models.result.Result.Ok (← ((← (ok &&? r)) &&? ok_1))))
  else do
    match (← (fallible rust_primitives.hax.Tuple0.mk)) with
      | (core_models.result.Result.Ok  ok_2) => do
        let r : Bool := ok_2;
        (pure (core_models.result.Result.Ok (← ((← (ok &&? r)) &&? ok_1))))
      | (core_models.result.Result.Err  err) => do
        (pure (core_models.result.Result.Err err))

@[spec]
def fb (x : u8) : RustM (core_models.result.Result u8 u8) := do
  (pure (core_models.result.Result.Ok x))

@[spec]
def mutated_ok (b : Bool) : RustM (core_models.result.Result u8 u8) := do
  let ok : u8 := (0 : u8);
  if b then do
    let ok : u8 := (1 : u8);
    match (← (fb (5 : u8))) with
      | (core_models.result.Result.Ok  ok_1) => do
        let ⟨ok, r⟩ := (rust_primitives.hax.Tuple2.mk ok ok_1);
        (pure (core_models.result.Result.Ok
          (← (core_models.num.Impl_6.wrapping_add ok r))))
      | (core_models.result.Result.Err  err) => do
        (pure (core_models.result.Result.Err err))
  else do
    let ⟨ok, r⟩ := (rust_primitives.hax.Tuple2.mk ok (0 : u8));
    (pure (core_models.result.Result.Ok
      (← (core_models.num.Impl_6.wrapping_add ok r))))

@[spec]
def bump (v : u8) : RustM (rust_primitives.hax.Tuple2 u8 u8) := do
  let v : u8 ← (core_models.num.Impl_6.wrapping_add v (1 : u8));
  let hax_temp_output : u8 := v;
  (pure (rust_primitives.hax.Tuple2.mk v hax_temp_output))

@[spec]
def add (a : u8) (b : u8) : RustM u8 := do
  (core_models.num.Impl_6.wrapping_add a b)

@[spec]
def mutated_tmp0 (b : Bool) (y : u8) : RustM u8 := do
  let tmp0 : u8 := (0 : u8);
  let ⟨⟨tmp0, y⟩, r⟩ ←
    if b then do
      let tmp0 : u8 := (1 : u8);
      let ⟨tmp0_1, out⟩ ← (bump y);
      let y : u8 := tmp0_1;
      (pure (rust_primitives.hax.Tuple2.mk
        (rust_primitives.hax.Tuple2.mk tmp0 y)
        out))
    else do
      (pure (rust_primitives.hax.Tuple2.mk
        (rust_primitives.hax.Tuple2.mk tmp0 y)
        (0 : u8)));
  (add (← (add tmp0 r)) y)

@[spec]
def mutated_hoist (b : Bool) (y : u8) : RustM u8 := do
  let hoist1 : u8 := (0 : u8);
  let hoist2 : u8 := (0 : u8);
  let ⟨⟨hoist1, hoist2, y⟩, r⟩ ←
    if b then do
      let hoist1 : u8 := (1 : u8);
      let hoist2 : u8 := (1 : u8);
      let ⟨tmp0, out⟩ ← (bump y);
      let y : u8 := tmp0;
      let hoist15 : u8 := out;
      let ⟨tmp0, out⟩ ← (bump y);
      let y : u8 := tmp0;
      (pure (rust_primitives.hax.Tuple2.mk
        (rust_primitives.hax.Tuple3.mk hoist1 hoist2 y)
        (← (add hoist15 out))))
    else do
      (pure (rust_primitives.hax.Tuple2.mk
        (rust_primitives.hax.Tuple3.mk hoist1 hoist2 y)
        (0 : u8)));
  (add (← (add hoist1 hoist2)) r)

@[spec]
def shadowing_let (b : Bool) : RustM (core_models.result.Result u8 u8) := do
  let x : u8 := (5 : u8);
  if b then do
    let x_1 : u8 ← (x +? (1 : u8));
    match (← (fallible rust_primitives.hax.Tuple0.mk)) with
      | (core_models.result.Result.Ok  hoist16) => do
        if hoist16 then do
          (pure (core_models.result.Result.Ok x_1))
        else do
          let r : u8 := x_1;
          (pure (core_models.result.Result.Ok (← (x +? r))))
      | (core_models.result.Result.Err  err) => do
        (pure (core_models.result.Result.Err err))
  else do
    let r : u8 := (2 : u8);
    (pure (core_models.result.Result.Ok (← (x +? r))))

end new_tests.legacy__hoisting__lib.control_flow_capture

