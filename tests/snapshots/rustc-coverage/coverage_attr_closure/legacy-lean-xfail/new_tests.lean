
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


namespace new_tests.rustc_coverage__coverage_attr_closure

--  @fail(extraction): ssprove(HAX0001)
--  @fail(extraction): proverif(HAX0001)
def GLOBAL_CLOSURE_ON : (String -> RustM rust_primitives.hax.Tuple0) :=
  RustM.of_isOk
    (do
    (pure (fun input =>
      (do
      let args : (rust_primitives.hax.Tuple1 String) :=
        (rust_primitives.hax.Tuple1.mk input);
      let args : (RustArray core_models.fmt.rt.Argument 1) :=
        (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display String
                                (rust_primitives.hax.Tuple1._0 args)))]);
      let _ ←
        (std.io.stdio._print
          (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
            (RustArray.ofVec #v["", "\n"])
            args)));
      let _ := rust_primitives.hax.Tuple0.mk;
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0))))
    (by rfl)

--  @fail(extraction): ssprove(HAX0001)
--  @fail(extraction): proverif(HAX0001)
def GLOBAL_CLOSURE_OFF : (String -> RustM rust_primitives.hax.Tuple0) :=
  RustM.of_isOk
    (do
    (pure (fun input =>
      (do
      let args : (rust_primitives.hax.Tuple1 String) :=
        (rust_primitives.hax.Tuple1.mk input);
      let args : (RustArray core_models.fmt.rt.Argument 1) :=
        (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display String
                                (rust_primitives.hax.Tuple1._0 args)))]);
      let _ ←
        (std.io.stdio._print
          (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
            (RustArray.ofVec #v["", "\n"])
            args)));
      let _ := rust_primitives.hax.Tuple0.mk;
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0))))
    (by rfl)

--  @fail(extraction): ssprove(HAX0001)
--  @fail(extraction): proverif(HAX0001, HAX0001)
@[spec]
def contains_closures_on (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _local_closure_on : (String -> RustM rust_primitives.hax.Tuple0) :=
    (fun input =>
      (do
      let args : (rust_primitives.hax.Tuple1 String) :=
        (rust_primitives.hax.Tuple1.mk input);
      let args : (RustArray core_models.fmt.rt.Argument 1) :=
        (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display String
                                (rust_primitives.hax.Tuple1._0 args)))]);
      let _ ←
        (std.io.stdio._print
          (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
            (RustArray.ofVec #v["", "\n"])
            args)));
      let _ := rust_primitives.hax.Tuple0.mk;
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0));
  let _local_closure_off : (String -> RustM rust_primitives.hax.Tuple0) :=
    (fun input =>
      (do
      let args : (rust_primitives.hax.Tuple1 String) :=
        (rust_primitives.hax.Tuple1.mk input);
      let args : (RustArray core_models.fmt.rt.Argument 1) :=
        (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display String
                                (rust_primitives.hax.Tuple1._0 args)))]);
      let _ ←
        (std.io.stdio._print
          (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
            (RustArray.ofVec #v["", "\n"])
            args)));
      let _ := rust_primitives.hax.Tuple0.mk;
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0));
  (pure rust_primitives.hax.Tuple0.mk)

--  @fail(extraction): ssprove(HAX0001)
--  @fail(extraction): proverif(HAX0001, HAX0001)
@[spec]
def contains_closures_off (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _local_closure_on : (String -> RustM rust_primitives.hax.Tuple0) :=
    (fun input =>
      (do
      let args : (rust_primitives.hax.Tuple1 String) :=
        (rust_primitives.hax.Tuple1.mk input);
      let args : (RustArray core_models.fmt.rt.Argument 1) :=
        (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display String
                                (rust_primitives.hax.Tuple1._0 args)))]);
      let _ ←
        (std.io.stdio._print
          (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
            (RustArray.ofVec #v["", "\n"])
            args)));
      let _ := rust_primitives.hax.Tuple0.mk;
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0));
  let _local_closure_off : (String -> RustM rust_primitives.hax.Tuple0) :=
    (fun input =>
      (do
      let args : (rust_primitives.hax.Tuple1 String) :=
        (rust_primitives.hax.Tuple1.mk input);
      let args : (RustArray core_models.fmt.rt.Argument 1) :=
        (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display String
                                (rust_primitives.hax.Tuple1._0 args)))]);
      let _ ←
        (std.io.stdio._print
          (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
            (RustArray.ofVec #v["", "\n"])
            args)));
      let _ := rust_primitives.hax.Tuple0.mk;
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0));
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (contains_closures_on rust_primitives.hax.Tuple0.mk);
  let _ ← (contains_closures_off rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__coverage_attr_closure

