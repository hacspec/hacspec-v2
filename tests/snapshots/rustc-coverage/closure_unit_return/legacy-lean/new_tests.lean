
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


namespace new_tests.rustc_coverage__closure_unit_return

--  @fail(extraction): proverif(HAX0001)
@[spec]
def explicit_unit (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let
    closure : (rust_primitives.hax.Tuple0 ->
    RustM rust_primitives.hax.Tuple0) :=
    (fun _ =>
      (do
      let _ := rust_primitives.hax.Tuple0.mk;
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0));
  let _ ←
    (core_models.mem.drop
      (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0) closure);
  (pure rust_primitives.hax.Tuple0.mk)

--  @fail(extraction): proverif(HAX0001)
@[spec]
def implicit_unit (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let
    closure : (rust_primitives.hax.Tuple0 ->
    RustM rust_primitives.hax.Tuple0) :=
    (fun _ =>
      (do
      let _ := rust_primitives.hax.Tuple0.mk;
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0));
  let _ ←
    (core_models.mem.drop
      (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0) closure);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (explicit_unit rust_primitives.hax.Tuple0.mk);
  let _ ← (implicit_unit rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__closure_unit_return

