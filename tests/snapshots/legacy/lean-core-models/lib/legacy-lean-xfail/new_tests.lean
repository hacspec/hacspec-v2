
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


namespace new_tests.legacy__lean_core_models__lib.default.structs

structure S where
  f1 : usize

@[spec]
def Impl.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM S := do
  (pure (S.mk (f1 := (0 : usize))))

@[reducible] instance Impl.AssociatedTypes :
  core_models.default.Default.AssociatedTypes S
  where

instance Impl : core_models.default.Default S where
  default := (Impl.default_hoisted)

@[spec]
def test (_ : rust_primitives.hax.Tuple0) : RustM S := do
  (core_models.default.Default.default S rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__lean_core_models__lib.default.structs


namespace new_tests.legacy__lean_core_models__lib.default.enums

inductive E (T : Type) : Type
| C1 : u32 -> E (T : Type)
| C2 : T -> E (T : Type)

@[spec]
def Impl.default_hoisted
    (T : Type)
    [trait_constr_default_hoisted_associated_type_i0 :
      core_models.default.Default.AssociatedTypes
      T]
    [trait_constr_default_hoisted_i0 : core_models.default.Default T ]
    (_ : rust_primitives.hax.Tuple0) :
    RustM (E T) := do
  (pure (E.C2
    (← (core_models.default.Default.default T rust_primitives.hax.Tuple0.mk))))

@[reducible] instance Impl.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_associated_type_i0 :
    core_models.default.Default.AssociatedTypes
    T]
  [trait_constr_Impl_i0 : core_models.default.Default T ] :
  core_models.default.Default.AssociatedTypes (E T)
  where

instance Impl
  (T : Type)
  [trait_constr_Impl_associated_type_i0 :
    core_models.default.Default.AssociatedTypes
    T]
  [trait_constr_Impl_i0 : core_models.default.Default T ] :
  core_models.default.Default (E T)
  where
  default := (Impl.default_hoisted T)

end new_tests.legacy__lean_core_models__lib.default.enums


namespace new_tests.legacy__lean_core_models__lib.function

--  @fail(extraction): proverif(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001)
@[spec]
def test (_ : rust_primitives.hax.Tuple0) : RustM u32 := do
  let f_1 : (u32 -> RustM u32) := (fun _ => (do (pure (9 : u32)) : RustM u32));
  let f_2 : (u32 -> u32 -> RustM u32) := (fun x y => (do (x +? y) : RustM u32));
  let f_2_tuple : ((rust_primitives.hax.Tuple2 u32 u32) -> RustM u32) :=
    (fun ⟨x, y⟩ => (do (x +? y) : RustM u32));
  ((← ((← (core_models.ops.function.Fn.call
        (u32 -> RustM u32)
        (rust_primitives.hax.Tuple1 u32)
        f_1
        (rust_primitives.hax.Tuple1.mk (0 : u32))))
      +? (← (core_models.ops.function.Fn.call
        (u32 -> u32 -> RustM u32)
        (rust_primitives.hax.Tuple2 u32 u32)
        f_2
        (rust_primitives.hax.Tuple2.mk (1 : u32) (2 : u32))))))
    +? (← (core_models.ops.function.Fn.call
      ((rust_primitives.hax.Tuple2 u32 u32) -> RustM u32)
      (rust_primitives.hax.Tuple1 (rust_primitives.hax.Tuple2 u32 u32))
      f_2_tuple
      (rust_primitives.hax.Tuple1.mk
        (rust_primitives.hax.Tuple2.mk (1 : u32) (2 : u32))))))

end new_tests.legacy__lean_core_models__lib.function


namespace new_tests.legacy__lean_core_models__lib.option

structure S where
  f1 : u32

inductive E : Type
| C : u32 -> E

@[spec]
def Impl.default_hoisted (_ : rust_primitives.hax.Tuple0) : RustM S := do
  (pure (S.mk (f1 := (42 : u32))))

@[reducible] instance Impl.AssociatedTypes :
  core_models.default.Default.AssociatedTypes S
  where

instance Impl : core_models.default.Default S where
  default := (Impl.default_hoisted)

--  @fail(extraction): proverif(HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001, HAX0001)
@[spec]
def test (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let o1 : (core_models.option.Option i32) :=
    (core_models.option.Option.Some (4 : i32));
  let o2 : (core_models.option.Option i32) := core_models.option.Option.None;
  let o3 : Bool ←
    (core_models.option.Impl.is_some_and i32 (i32 -> RustM Bool)
      (← (core_models.clone.Clone.clone (core_models.option.Option i32) o1))
      (fun x => (do (x ==? (0 : i32)) : RustM Bool)));
  let o3 : Bool ←
    (core_models.option.Impl.is_none_or i32 (i32 -> RustM Bool)
      (← (core_models.clone.Clone.clone (core_models.option.Option i32) o1))
      (fun x => (do (x ==? (0 : i32)) : RustM Bool)));
  let o4 : i32 ←
    (core_models.option.Impl.unwrap i32
      (core_models.option.Option.Some (0 : i32)));
  let o5 : i32 ←
    (core_models.option.Impl.unwrap_or i32
      (core_models.option.Option.Some (0 : i32))
      (9 : i32));
  let o6 : i32 ←
    (core_models.option.Impl.unwrap_or_else
      i32
      (rust_primitives.hax.Tuple0 -> RustM i32)
      (core_models.option.Option.Some (0 : i32))
      (fun _ => (do (pure (9 : i32)) : RustM i32)));
  let o7 : S ←
    (core_models.option.Impl.unwrap_or_default S
      core_models.option.Option.None);
  let o8 : (core_models.option.Option i32) ←
    (core_models.option.Impl.map i32 i32 (i32 -> RustM i32)
      (core_models.option.Option.Some (0 : i32))
      (fun x => (do (x +? (1 : i32)) : RustM i32)));
  let o9 : i32 ←
    (core_models.option.Impl.map_or i32 i32 (i32 -> RustM i32)
      (core_models.option.Option.Some (1 : i32))
      (9 : i32)
      (fun x => (do (x +? (1 : i32)) : RustM i32)));
  let o10 : i32 ←
    (core_models.option.Impl.map_or_else
      i32
      i32
      (rust_primitives.hax.Tuple0 -> RustM i32)
      (i32 -> RustM i32)
      (core_models.option.Option.Some (2 : i32))
      (fun _ => (do (pure (9 : i32)) : RustM i32))
      (fun x => (do (x +? (1 : i32)) : RustM i32)));
  let o11 : (core_models.result.Result i32 E) ←
    (core_models.option.Impl.ok_or i32 E
      (core_models.option.Option.Some (3 : i32))
      (E.C (0 : u32)));
  let o12 : (core_models.result.Result i32 E) ←
    (core_models.option.Impl.ok_or_else
      i32
      E
      (rust_primitives.hax.Tuple0 -> RustM E)
      (core_models.option.Option.Some (1 : i32))
      (fun _ => (do (pure (E.C (1 : u32))) : RustM E)));
  let o13 : (core_models.option.Option u32) ←
    (core_models.option.Impl.and_then
      u32
      u32
      (u32 -> RustM (core_models.option.Option u32))
      core_models.option.Option.None
      (fun x =>
        (do
        (pure (core_models.option.Option.Some x)) :
        RustM (core_models.option.Option u32))));
  let ⟨_, out⟩ ←
    (core_models.option.Impl.take S
      (core_models.option.Option.Some (S.mk (f1 := (9 : u32)))));
  let o14 : (core_models.option.Option S) := out;
  let o15 : Bool ←
    (core_models.option.Impl.is_some i32
      (core_models.option.Option.Some (1 : i32)));
  let o16 : Bool ←
    (core_models.option.Impl.is_none i32
      (core_models.option.Option.Some (2 : i32)));
  let o17 : i32 ←
    (core_models.option.Impl.expect i32
      (core_models.option.Option.Some (3 : i32))
      "Should be Some");
  let o18 : i32 ←
    (core_models.option.Impl.unwrap i32
      (core_models.option.Option.Some (4 : i32)));
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__lean_core_models__lib.option


namespace new_tests.legacy__lean_core_models__lib.phantom

class Foo.AssociatedTypes (Self : Type) where

class Foo (Self : Type)
  [associatedTypes : outParam (Foo.AssociatedTypes (Self : Type))]
  where

structure Bar
  (F : Type)
  [trait_constr_Bar_associated_type_i0 : Foo.AssociatedTypes F]
  [trait_constr_Bar_i0 : Foo F ]
  where
  _phantom : (core_models.marker.PhantomData F)

@[spec]
def Impl.new
    (F : Type)
    [trait_constr_new_associated_type_i0 : Foo.AssociatedTypes F]
    [trait_constr_new_i0 : Foo F ]
    (_ : rust_primitives.hax.Tuple0) :
    RustM (Bar F) := do
  (pure (Bar.mk (_phantom := core_models.marker.PhantomData.mk)))

end new_tests.legacy__lean_core_models__lib.phantom


namespace new_tests.legacy__lean_core_models__lib.result

inductive E1 : Type
| C1 : E1
| C2 : u32 -> E1

@[instance] opaque Impl.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes E1 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl :
  core_models.clone.Clone E1 :=
  by constructor <;> exact Inhabited.default

inductive E2 : Type
| C1 : E2
| C2 : u32 -> E2

--  @fail(extraction): proverif(HAX0001, HAX0001, HAX0001, HAX0001)
@[spec]
def tests (_ : rust_primitives.hax.Tuple0) :
    RustM (core_models.result.Result u32 E1) := do
  let v1 : (core_models.result.Result u32 E1) :=
    (core_models.result.Result.Ok (1 : u32));
  let v2 : (core_models.result.Result u32 E1) :=
    (core_models.result.Result.Err E1.C1);
  let f : (u32 -> RustM u32) := (fun x => (do (x +? (1 : u32)) : RustM u32));
  let v5 : (core_models.result.Result i32 E1) ←
    (core_models.result.Impl.map i32 E1 i32 (i32 -> RustM i32)
      (core_models.result.Result.Ok (1 : i32))
      (fun v => (do (v +? (1 : i32)) : RustM i32)));
  let v6 : u32 ←
    (core_models.result.Impl.map_or u32 E1 u32 (u32 -> RustM u32)
      (core_models.result.Result.Ok (1 : u32))
      (9 : u32)
      f);
  let v7 : u32 ←
    (core_models.result.Impl.map_or_else
      u32
      E1
      u32
      (E1 -> RustM u32)
      (u32 -> RustM u32)
      (core_models.result.Result.Ok (1 : u32))
      (fun _ => (do (pure (10 : u32)) : RustM u32))
      f);
  let v8 : (core_models.result.Result i32 E2) ←
    (core_models.result.Impl.map_err i32 E1 E2 (E1 -> RustM E2)
      (core_models.result.Result.Ok (0 : i32))
      (fun e =>
        (do
        match e with
          | (E1.C1 ) => do (pure E2.C1)
          | (E1.C2  x) => do (pure (E2.C2 (← (x +? (1 : u32))))) :
        RustM E2)));
  let v9 : Bool ← (core_models.result.Impl.is_ok u32 E1 v1);
  let v10 : Bool ← (core_models.result.Impl.is_err u32 E1 v1);
  let v11 : (core_models.result.Result u32 E1) ←
    (core_models.result.Impl.and_then
      u32
      E1
      u32
      (u32 -> RustM (core_models.result.Result u32 E1))
      (← (core_models.clone.Clone.clone (core_models.result.Result u32 E1) v1))
      (fun x =>
        (do
        (pure (core_models.result.Result.Ok (← (x +? (1 : u32))))) :
        RustM (core_models.result.Result u32 E1))));
  let v12 : u32 ←
    (core_models.result.Impl.unwrap u32 u32
      (← (core_models.clone.Clone.clone
        (core_models.result.Result u32 u32)
        (core_models.result.Result.Ok (0 : u32)))));
  let v13 : u32 ←
    (core_models.result.Impl.expect u32 u32
      (← (core_models.clone.Clone.clone
        (core_models.result.Result u32 u32)
        (core_models.result.Result.Ok (0 : u32))))
      "Should be Ok");
  match
    (← (core_models.result.Impl.map u32 E1 u32 (u32 -> RustM u32) v1 f))
  with
    | (core_models.result.Result.Ok  hoist2) => do
      match v2 with
        | (core_models.result.Result.Ok  hoist1) => do
          let v3 : u32 ← (hoist2 +? hoist1);
          (pure (core_models.result.Result.Ok v3))
        | (core_models.result.Result.Err  err) => do
          (pure (core_models.result.Result.Err err))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

end new_tests.legacy__lean_core_models__lib.result

