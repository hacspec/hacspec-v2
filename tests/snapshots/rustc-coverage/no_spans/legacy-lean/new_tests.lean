
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


namespace new_tests.rustc_coverage__no_spans

--  @fail(extraction): proverif(HAX0001)
@[spec]
def affected_function (_ : rust_primitives.hax.Tuple0) :
    RustM (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0) := do
  (pure (fun _ =>
    (do
    (pure rust_primitives.hax.Tuple0.mk) : RustM rust_primitives.hax.Tuple0)))

--  @fail(extraction): proverif(HAX0001)
@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (core_models.ops.function.Fn.call
      (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0)
      rust_primitives.hax.Tuple0
      (← (affected_function rust_primitives.hax.Tuple0.mk))
      rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__no_spans

