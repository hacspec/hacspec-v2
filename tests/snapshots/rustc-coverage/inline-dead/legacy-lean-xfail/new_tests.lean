
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


namespace new_tests.rustc_coverage__inline_dead

@[spec]
def dead (_ : rust_primitives.hax.Tuple0) : RustM u32 := do (pure (42 : u32))

--  @fail(extraction): proverif(HAX0001)
@[spec]
def live (B : Bool) (_ : rust_primitives.hax.Tuple0) : RustM u32 := do
  if B then do (dead rust_primitives.hax.Tuple0.mk) else do (pure (0 : u32))

--  @fail(extraction): ssprove(HAX0001)
--  @fail(extraction): proverif(HAX0001, HAX0001)
@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let args : (rust_primitives.hax.Tuple1 u32) :=
    (rust_primitives.hax.Tuple1.mk
      (← (live (false) rust_primitives.hax.Tuple0.mk)));
  let args : (RustArray core_models.fmt.rt.Argument 1) :=
    (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display u32
                            (rust_primitives.hax.Tuple1._0 args)))]);
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
        (RustArray.ofVec #v["", "\n"])
        args)));
  let _ := rust_primitives.hax.Tuple0.mk;
  let f : (Bool -> RustM rust_primitives.hax.Tuple0) :=
    (fun x =>
      (do
      let _ ←
        if true then do
          let _ ← (hax_lib.assert x);
          (pure rust_primitives.hax.Tuple0.mk)
        else do
          (pure rust_primitives.hax.Tuple0.mk);
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0));
  let _ ←
    (core_models.ops.function.Fn.call
      (Bool -> RustM rust_primitives.hax.Tuple0)
      (rust_primitives.hax.Tuple1 Bool)
      f
      (rust_primitives.hax.Tuple1.mk false));
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__inline_dead

