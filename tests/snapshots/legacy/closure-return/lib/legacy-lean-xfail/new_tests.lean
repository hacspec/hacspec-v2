
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


namespace new_tests.legacy__closure_return__lib

--  @fail(extraction): coq(HAX0001, HAX0001), ssprove(HAX0001), proverif(HAX0008)
@[spec]
def in_while_condition (n : u8) : RustM u8 := do
  let i : u8 := (0 : u8);
  let i : u8 ←
    (rust_primitives.hax.while_loop
      (fun i => (do (pure true) : RustM Bool))
      (fun i =>
        (do
        let c : (u8 -> RustM Bool) :=
          (fun x =>
            (do
            if (← (x ==? (3 : u8))) then do (pure false) else do (pure true) :
            RustM Bool));
        ((← (core_models.ops.function.Fn.call
            (u8 -> RustM Bool)
            (rust_primitives.hax.Tuple1 u8)
            c
            (rust_primitives.hax.Tuple1.mk i)))
          &&? (← (i <? n))) :
        RustM Bool))
      (fun i =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      i
      (fun i => (do let i : u8 ← (i +? (1 : u8)); (pure i) : RustM u8)));
  (pure i)

--  @fail(extraction): coq(HAX0001, HAX0001), ssprove(HAX0001), proverif(HAX0008)
@[spec]
def in_loop_body (n : u8) : RustM u8 := do
  let i : u8 := (0 : u8);
  let i : u8 ←
    (rust_primitives.hax.while_loop
      (fun i => (do (pure true) : RustM Bool))
      (fun i => (do (i <? n) : RustM Bool))
      (fun i =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      i
      (fun i =>
        (do
        let c : (u8 -> RustM Bool) :=
          (fun x =>
            (do
            if (← (x ==? (3 : u8))) then do (pure false) else do (pure true) :
            RustM Bool));
        if
        (← (core_models.ops.function.Fn.call
          (u8 -> RustM Bool)
          (rust_primitives.hax.Tuple1 u8) c (rust_primitives.hax.Tuple1.mk i)))
        then do
          let i : u8 ← (i +? (1 : u8));
          (pure i)
        else do
          let i : u8 ← (i +? (2 : u8));
          (pure i) :
        RustM u8)));
  (pure i)

--  @fail(extraction): proverif(HAX0008)
@[spec]
def nested (i : u8) : RustM u8 := do
  let c : (u8 -> RustM u8) :=
    (fun x =>
      (do
      let d : (u8 -> RustM u8) :=
        (fun y =>
          (do
          if (← (y ==? (0 : u8))) then do (pure (7 : u8)) else do (pure y) :
          RustM u8));
      if (← (x ==? (3 : u8))) then do
        (core_models.ops.function.Fn.call
          (u8 -> RustM u8)
          (rust_primitives.hax.Tuple1 u8) d (rust_primitives.hax.Tuple1.mk x))
      else do
        (x +? (1 : u8)) :
      RustM u8));
  match
    (← (rust_primitives.hax.folds.fold_range_return
      (0 : u8)
      i
      (fun _ _ => (do (pure true) : RustM Bool))
      rust_primitives.hax.Tuple0.mk
      (fun _ j =>
        (do
        if
        (← ((← (core_models.ops.function.Fn.call
            (u8 -> RustM u8)
            (rust_primitives.hax.Tuple1 u8)
            c
            (rust_primitives.hax.Tuple1.mk j)))
          ==? (9 : u8))) then do
          (pure (core_models.ops.control_flow.ControlFlow.Break
            (core_models.ops.control_flow.ControlFlow.Break (4 : u8))))
        else do
          (pure (core_models.ops.control_flow.ControlFlow.Continue
            rust_primitives.hax.Tuple0.mk)) :
        RustM
        (core_models.ops.control_flow.ControlFlow
          (core_models.ops.control_flow.ControlFlow
            u8
            (rust_primitives.hax.Tuple2
              rust_primitives.hax.Tuple0
              rust_primitives.hax.Tuple0))
          rust_primitives.hax.Tuple0)))))
  with
    | (core_models.ops.control_flow.ControlFlow.Break  ret) => do (pure ret)
    | (core_models.ops.control_flow.ControlFlow.Continue  _) => do
      (core_models.ops.function.Fn.call
        (u8 -> RustM u8)
        (rust_primitives.hax.Tuple1 u8) c (rust_primitives.hax.Tuple1.mk i))

end new_tests.legacy__closure_return__lib

