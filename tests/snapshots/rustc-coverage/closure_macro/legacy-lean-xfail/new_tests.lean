
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


namespace new_tests.rustc_coverage__closure_macro

@[spec]
def load_configuration_files (_ : rust_primitives.hax.Tuple0) :
    RustM
    (core_models.result.Result alloc.string.String alloc.string.String)
    := do
  (pure (core_models.result.Result.Ok
    (← (core_models.convert.From._from alloc.string.String String "config"))))

--  @fail(extraction): ssprove(HAX0001)
--  @fail(extraction): proverif(HAX0001)
@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM
    (core_models.result.Result rust_primitives.hax.Tuple0 alloc.string.String)
    := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
        (RustArray.ofVec #v["Starting service\n"]))));
  let _ := rust_primitives.hax.Tuple0.mk;
  match
    (← (core_models.result.Impl.or_else
      alloc.string.String
      alloc.string.String
      alloc.string.String
      (alloc.string.String ->
      RustM (core_models.result.Result alloc.string.String alloc.string.String))
      (← (load_configuration_files rust_primitives.hax.Tuple0.mk))
      (fun e =>
        (do
        let args : (rust_primitives.hax.Tuple1 alloc.string.String) :=
          (rust_primitives.hax.Tuple1.mk e);
        let args : (RustArray core_models.fmt.rt.Argument 1) :=
          (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display
                                  alloc.string.String
                                  (rust_primitives.hax.Tuple1._0 args)))]);
        let message : alloc.string.String ←
          (core_models.hint.must_use alloc.string.String
            (← (alloc.fmt.format
              (← (core_models.fmt.rt.Impl_1.new_v1 ((1 : usize)) ((1 : usize))
                (RustArray.ofVec #v["Error loading configs: "])
                args)))));
        if (← ((← (alloc.string.Impl.len message)) >? (0 : usize))) then do
          let args : (rust_primitives.hax.Tuple1 alloc.string.String) :=
            (rust_primitives.hax.Tuple1.mk message);
          let args : (RustArray core_models.fmt.rt.Argument 1) :=
            (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display
                                    alloc.string.String
                                    (rust_primitives.hax.Tuple1._0 args)))]);
          let _ ←
            (std.io.stdio._print
              (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
                (RustArray.ofVec #v["", "\n"])
                args)));
          let _ := rust_primitives.hax.Tuple0.mk;
          (pure (core_models.result.Result.Ok
            (← (core_models.convert.From._from
              alloc.string.String
              String "ok"))))
        else do
          let _ ←
            if
            (← ((← (core_models.str.Impl.len "error")) >? (0 : usize))) then do
              let _ ←
                (std.io.stdio._print
                  (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                    (RustArray.ofVec #v["no msg\n"]))));
              let _ := rust_primitives.hax.Tuple0.mk;
              (pure rust_primitives.hax.Tuple0.mk)
            else do
              let _ ←
                (std.io.stdio._print
                  (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                    (RustArray.ofVec #v["error\n"]))));
              let _ := rust_primitives.hax.Tuple0.mk;
              (pure rust_primitives.hax.Tuple0.mk);
          (pure (core_models.result.Result.Err
            (← (core_models.convert.From._from
              alloc.string.String
              String "error")))) :
        RustM
        (core_models.result.Result alloc.string.String alloc.string.String)))))
  with
    | (core_models.result.Result.Ok  config) => do
      let startup_delay_duration : alloc.string.String ←
        (core_models.convert.From._from alloc.string.String String "arg");
      let _ := (rust_primitives.hax.Tuple2.mk config startup_delay_duration);
      (pure (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

end new_tests.rustc_coverage__closure_macro

