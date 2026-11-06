
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


namespace new_tests.legacy__pattern_or__lib

inductive E : Type
| A : E
| B : E

@[spec]
def E_cast_to_repr (x : E) : RustM isize := do
  match x with
    | (E.A ) => do (pure (0 : isize))
    | (E.B ) => do (pure (1 : isize))

@[spec]
def bar (x : E) : RustM rust_primitives.hax.Tuple0 := do
  match x with | (E.A ) | (E.B ) => do (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def nested (x : (core_models.option.Option i32)) : RustM i32 := do
  match x with
    | (core_models.option.Option.Some  1) | (core_models.option.Option.Some  2)
      => do
      (pure (1 : i32))
    | (core_models.option.Option.Some  x) => do (pure x)
    | (core_models.option.Option.None ) => do (pure (0 : i32))

@[spec]
def deep
    (x : (rust_primitives.hax.Tuple2 i32 (core_models.option.Option i32))) :
    RustM i32 := do
  match x with
    | ⟨1, (core_models.option.Option.Some  3)⟩ | ⟨1,
                                                  (core_models.option.Option.Some
                                                     4)⟩ | ⟨2,
                                                            (core_models.option.Option.Some
                                                               3)⟩ | ⟨2,
                                                                      (core_models.option.Option.Some
                                                                         4)⟩ =>
      do
      (pure (0 : i32))
    | ⟨x, _⟩ => do (pure x)

@[spec]
def equivalent
    (x : (rust_primitives.hax.Tuple2 i32 (core_models.option.Option i32))) :
    RustM i32 := do
  match x with
    | ⟨1, (core_models.option.Option.Some  3)⟩ | ⟨1,
                                                  (core_models.option.Option.Some
                                                     4)⟩ | ⟨2,
                                                            (core_models.option.Option.Some
                                                               3)⟩ | ⟨2,
                                                                      (core_models.option.Option.Some
                                                                         4)⟩ =>
      do
      (pure (0 : i32))
    | ⟨x, _⟩ => do (pure x)

--  @fail(extraction): proverif(HAX0001, HAX0001)
@[spec]
def deep_capture
    (x :
    (core_models.result.Result
      (rust_primitives.hax.Tuple2 i32 i32)
      (rust_primitives.hax.Tuple2 i32 i32))) :
    RustM i32 := do
  match x with
    | (core_models.result.Result.Ok  ⟨1, x⟩) | (core_models.result.Result.Ok
         ⟨2, x⟩) | (core_models.result.Result.Err  ⟨3, x⟩) |
      (core_models.result.Result.Err  ⟨4, x⟩) => do
      (pure x)
    | (core_models.result.Result.Ok  ⟨x, _⟩) | (core_models.result.Result.Err
         ⟨x, _⟩) => do
      (pure x)

end new_tests.legacy__pattern_or__lib

