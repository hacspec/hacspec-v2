
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


namespace new_tests.rustc_coverage__mcdc__nested_if

@[spec]
def say (message : String) : RustM rust_primitives.hax.Tuple0 := do
  let _ ← (core_models.hint.black_box String message);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def nested_if_in_condition (a : Bool) (b : Bool) (c : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if
  (← (rust_primitives.hax.logical_op.and_then
    a
    (do if (← (b ||? c)) then do (pure true) else do (pure false)))) then do
    let _ ← (say "yes");
    (pure rust_primitives.hax.Tuple0.mk)
  else do
    let _ ← (say "no");
    (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def doubly_nested_if_in_condition (a : Bool) (b : Bool) (c : Bool) (d : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if
  (← (rust_primitives.hax.logical_op.and_then
    a
    (do
    if
    (← (rust_primitives.hax.logical_op.or_else
      b
      (do if (← (c &&? d)) then do (pure true) else do (pure false)))) then do
      (pure false)
    else do
      (pure true)))) then do
    let _ ← (say "yes");
    (pure rust_primitives.hax.Tuple0.mk)
  else do
    let _ ← (say "no");
    (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def nested_single_condition_decision (a : Bool) (b : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if
  (← (rust_primitives.hax.logical_op.and_then
    a
    (do if b then do (pure false) else do (pure true)))) then do
    let _ ← (say "yes");
    (pure rust_primitives.hax.Tuple0.mk)
  else do
    let _ ← (say "no");
    (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def nested_in_then_block_in_condition
    (a : Bool)
    (b : Bool)
    (c : Bool)
    (d : Bool)
    (e : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if
  (← (rust_primitives.hax.logical_op.and_then
    a
    (do
    if (← (b ||? c)) then do
      if (← (d &&? e)) then do (pure true) else do (pure false)
    else do
      (pure false)))) then do
    let _ ← (say "yes");
    (pure rust_primitives.hax.Tuple0.mk)
  else do
    let _ ← (say "no");
    (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (nested_if_in_condition true false false);
  let _ ← (nested_if_in_condition true true true);
  let _ ← (nested_if_in_condition true false true);
  let _ ← (nested_if_in_condition false true true);
  let _ ← (doubly_nested_if_in_condition true false false true);
  let _ ← (doubly_nested_if_in_condition true true true true);
  let _ ← (doubly_nested_if_in_condition true false true true);
  let _ ← (doubly_nested_if_in_condition false true true true);
  let _ ← (nested_single_condition_decision true true);
  let _ ← (nested_single_condition_decision true false);
  let _ ← (nested_single_condition_decision false false);
  let _ ← (nested_in_then_block_in_condition false false false false false);
  let _ ← (nested_in_then_block_in_condition true false false false false);
  let _ ← (nested_in_then_block_in_condition true true false false false);
  let _ ← (nested_in_then_block_in_condition true false true false false);
  let _ ← (nested_in_then_block_in_condition true false true true false);
  let _ ← (nested_in_then_block_in_condition true false true false true);
  let _ ← (nested_in_then_block_in_condition true false true true true);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__mcdc__nested_if

