
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


namespace new_tests.rustc_coverage__attr__nested

@[spec]
def do_stuff (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def outer_fn (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def outer_fn.middle_fn (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def outer_fn.middle_fn.inner_fn (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

structure MyOuter where
  -- no fields

@[spec]
def Impl.outer_method (self : MyOuter) : RustM rust_primitives.hax.Tuple0 := do
  let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

structure Impl.outer_method.MyMiddle where
  -- no fields

@[spec]
def Impl.outer_method.Impl.middle_method (self : Impl.outer_method.MyMiddle) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

structure Impl.outer_method.Impl.middle_method.MyInner where
  -- no fields

@[spec]
def Impl.outer_method.Impl.middle_method.Impl.inner_method
    (self : Impl.outer_method.Impl.middle_method.MyInner) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

class MyTrait.AssociatedTypes (Self : Type) where

class MyTrait (Self : Type)
  [associatedTypes : outParam (MyTrait.AssociatedTypes (Self : Type))]
  where
  trait_method (Self) : (Self -> RustM rust_primitives.hax.Tuple0)

@[spec]
def Impl_1.trait_method_hoisted (self : MyOuter) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[reducible] instance Impl_1.AssociatedTypes :
  MyTrait.AssociatedTypes MyOuter
  where

instance Impl_1 : MyTrait MyOuter where
  trait_method := (Impl_1.trait_method_hoisted)

structure Impl_1.trait_method.MyMiddle where
  -- no fields

@[spec]
def Impl_1.trait_method.Impl.trait_method_hoisted
    (self : Impl_1.trait_method.MyMiddle) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[reducible] instance Impl_1.trait_method.Impl.AssociatedTypes :
  MyTrait.AssociatedTypes Impl_1.trait_method.MyMiddle
  where

instance Impl_1.trait_method.Impl : MyTrait Impl_1.trait_method.MyMiddle where
  trait_method := (Impl_1.trait_method.Impl.trait_method_hoisted)

structure Impl_1.trait_method.Impl.trait_method.MyInner where
  -- no fields

@[spec]
def Impl_1.trait_method.Impl.trait_method.Impl.trait_method_hoisted
    (self : Impl_1.trait_method.Impl.trait_method.MyInner) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[reducible] instance Impl_1.trait_method.Impl.trait_method.Impl.AssociatedTypes
  :
  MyTrait.AssociatedTypes Impl_1.trait_method.Impl.trait_method.MyInner
  where

instance Impl_1.trait_method.Impl.trait_method.Impl :
  MyTrait Impl_1.trait_method.Impl.trait_method.MyInner
  where
  trait_method :=
  (Impl_1.trait_method.Impl.trait_method.Impl.trait_method_hoisted)

--  @fail(extraction): proverif(HAX0001)
@[spec]
def closure_expr (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let
    _outer : (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0) :=
    (fun _ =>
      (do
      let
        _middle : (rust_primitives.hax.Tuple0 ->
        RustM rust_primitives.hax.Tuple0) :=
        (fun _ =>
          (do
          let
            _inner : (rust_primitives.hax.Tuple0 ->
            RustM rust_primitives.hax.Tuple0) :=
            (fun _ =>
              (do
              let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
              (pure rust_primitives.hax.Tuple0.mk) :
              RustM rust_primitives.hax.Tuple0));
          let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
          (pure rust_primitives.hax.Tuple0.mk) :
          RustM rust_primitives.hax.Tuple0));
      let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0));
  let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

--  @fail(extraction): proverif(HAX0001)
@[spec]
def closure_tail (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let
    _outer : (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0) :=
    (fun _ =>
      (do
      let
        _middle : (rust_primitives.hax.Tuple0 ->
        RustM rust_primitives.hax.Tuple0) :=
        (fun _ =>
          (do
          let
            _inner : (rust_primitives.hax.Tuple0 ->
            RustM rust_primitives.hax.Tuple0) :=
            (fun _ =>
              (do
              let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
              (pure rust_primitives.hax.Tuple0.mk) :
              RustM rust_primitives.hax.Tuple0));
          let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
          (pure rust_primitives.hax.Tuple0.mk) :
          RustM rust_primitives.hax.Tuple0));
      let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0));
  let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (outer_fn rust_primitives.hax.Tuple0.mk);
  let _ ← (Impl.outer_method MyOuter.mk);
  let _ ← (MyTrait.trait_method MyOuter MyOuter.mk);
  let _ ← (closure_expr rust_primitives.hax.Tuple0.mk);
  let _ ← (closure_tail rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__attr__nested

