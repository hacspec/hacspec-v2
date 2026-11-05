
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


namespace new_tests.rustc_coverage__holes

--  @fail(extraction): coq(HAX0001), legacy-lean(HAX0001), ssprove(HAX0001), fstar(HAX0001)
--  @fail(extraction): proverif(HAX0001)
@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure sorry)

def main.MY_STATIC : rust_primitives.hax.Tuple0 :=
  RustM.of_isOk (do (pure rust_primitives.hax.Tuple0.mk)) (by rfl)

def main.MY_CONST : rust_primitives.hax.Tuple0 :=
  RustM.of_isOk (do (pure rust_primitives.hax.Tuple0.mk)) (by rfl)

@[spec]
def main._unused_fn (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

structure main.MyStruct where
  _x : u32
  _y : u32

@[spec]
def main.Impl._method (self : main.MyStruct) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

class main.MyTrait.AssociatedTypes (Self : Type) where

class main.MyTrait (Self : Type)
  [associatedTypes : outParam (main.MyTrait.AssociatedTypes (Self : Type))]
  where

@[reducible] instance main.Impl_1.AssociatedTypes :
  main.MyTrait.AssociatedTypes main.MyStruct
  where

instance main.Impl_1 : main.MyTrait main.MyStruct where

end new_tests.rustc_coverage__holes

