
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


namespace new_tests.legacy__cyclic_modules__lib.typ_b

inductive T1 : Type
| T1 : T1

end new_tests.legacy__cyclic_modules__lib.typ_b


namespace new_tests.legacy__cyclic_modules__lib.typ_a

inductive T : Type
| T : new_tests.legacy__cyclic_modules__lib.typ_b.T1 -> T

end new_tests.legacy__cyclic_modules__lib.typ_a


namespace new_tests.legacy__cyclic_modules__lib.typ_b

@[spec]
def T1_cast_to_repr (x : T1) : RustM isize := do
  match x with | (T1.T1 ) => do (pure (0 : isize))

inductive T2 : Type
| T2 : new_tests.legacy__cyclic_modules__lib.typ_a.T -> T2

end new_tests.legacy__cyclic_modules__lib.typ_b


namespace new_tests.legacy__cyclic_modules__lib

@[spec]
def f (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib


namespace new_tests.legacy__cyclic_modules__lib.b

@[spec]
def g (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (new_tests.legacy__cyclic_modules__lib.f rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.b


namespace new_tests.legacy__cyclic_modules__lib.c

@[spec]
def i (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.c


namespace new_tests.legacy__cyclic_modules__lib

@[spec]
def h (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (new_tests.legacy__cyclic_modules__lib.b.g rust_primitives.hax.Tuple0.mk);
  (new_tests.legacy__cyclic_modules__lib.c.i rust_primitives.hax.Tuple0.mk)

@[spec]
def h2 (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (new_tests.legacy__cyclic_modules__lib.c.i rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib


namespace new_tests.legacy__cyclic_modules__lib.d

@[spec]
def d1 (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.d


namespace new_tests.legacy__cyclic_modules__lib.e

@[spec]
def e1 (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (new_tests.legacy__cyclic_modules__lib.d.d1 rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.e


namespace new_tests.legacy__cyclic_modules__lib.de

@[spec]
def de1 (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (new_tests.legacy__cyclic_modules__lib.e.e1 rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.de


namespace new_tests.legacy__cyclic_modules__lib.d

@[spec]
def d2 (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (new_tests.legacy__cyclic_modules__lib.de.de1 rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.d


namespace new_tests.legacy__cyclic_modules__lib.rec

inductive T : Type
| t1 : T
| t2 : T

@[spec]
def T_cast_to_repr (x : T) : RustM isize := do
  match x with
    | (T.t1 ) => do (pure (0 : isize))
    | (T.t2 ) => do (pure (1 : isize))

end new_tests.legacy__cyclic_modules__lib.rec


namespace new_tests.legacy__cyclic_modules__lib.m2

@[spec]
def d (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def c (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.m2


namespace new_tests.legacy__cyclic_modules__lib.m1

@[spec]
def a (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (new_tests.legacy__cyclic_modules__lib.m2.c rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.m1


namespace new_tests.legacy__cyclic_modules__lib.m2

@[spec]
def b (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (new_tests.legacy__cyclic_modules__lib.m1.a rust_primitives.hax.Tuple0.mk);
  (d rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.m2


namespace new_tests.legacy__cyclic_modules__lib.disjoint_cycle_a

@[spec]
def g (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.disjoint_cycle_a


namespace new_tests.legacy__cyclic_modules__lib.disjoint_cycle_b

@[spec]
def h (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.disjoint_cycle_b


namespace new_tests.legacy__cyclic_modules__lib.disjoint_cycle_a

@[spec]
def f (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (new_tests.legacy__cyclic_modules__lib.disjoint_cycle_b.h
    rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.disjoint_cycle_a


namespace new_tests.legacy__cyclic_modules__lib.disjoint_cycle_b

@[spec]
def i (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (new_tests.legacy__cyclic_modules__lib.disjoint_cycle_a.g
    rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.disjoint_cycle_b


namespace new_tests.legacy__cyclic_modules__lib.variant_constructor_a

inductive Context : Type
| A : i32 -> Context
| B : i32 -> Context

@[spec]
def Impl.test (x : (core_models.option.Option i32)) :
    RustM (core_models.option.Option Context) := do
  (core_models.option.Impl.map i32 Context (i32 -> RustM Context) x Context.A)

end new_tests.legacy__cyclic_modules__lib.variant_constructor_a


namespace new_tests.legacy__cyclic_modules__lib.variant_constructor_b

@[spec]
def h (_ : rust_primitives.hax.Tuple0) :
    RustM
    new_tests.legacy__cyclic_modules__lib.variant_constructor_a.Context
    := do
  (pure (new_tests.legacy__cyclic_modules__lib.variant_constructor_a.Context.A
    (1 : i32)))

end new_tests.legacy__cyclic_modules__lib.variant_constructor_b


namespace new_tests.legacy__cyclic_modules__lib.variant_constructor_a

@[spec]
def f (_ : rust_primitives.hax.Tuple0) : RustM Context := do
  (new_tests.legacy__cyclic_modules__lib.variant_constructor_b.h
    rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.variant_constructor_a


namespace new_tests.legacy__cyclic_modules__lib.issue_1823.first_example.a

structure A where
  -- no fields

end new_tests.legacy__cyclic_modules__lib.issue_1823.first_example.a


namespace new_tests.legacy__cyclic_modules__lib.issue_1823.first_example.b

structure B where
  -- no fields

end new_tests.legacy__cyclic_modules__lib.issue_1823.first_example.b


namespace new_tests.legacy__cyclic_modules__lib.issue_1823.first_example.a

@[spec]
def Impl.mkb (self : A) :
    RustM
    new_tests.legacy__cyclic_modules__lib.issue_1823.first_example.b.B
    := do
  (pure new_tests.legacy__cyclic_modules__lib.issue_1823.first_example.b.B.mk)

end new_tests.legacy__cyclic_modules__lib.issue_1823.first_example.a


namespace new_tests.legacy__cyclic_modules__lib.issue_1823.first_example.b

@[spec]
def Impl.mka (self : B) :
    RustM
    new_tests.legacy__cyclic_modules__lib.issue_1823.first_example.a.A
    := do
  (pure new_tests.legacy__cyclic_modules__lib.issue_1823.first_example.a.A.mk)

end new_tests.legacy__cyclic_modules__lib.issue_1823.first_example.b


namespace new_tests.legacy__cyclic_modules__lib.issue_1823.second_example.a

@[spec]
def a (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.issue_1823.second_example.a


namespace new_tests.legacy__cyclic_modules__lib.issue_1823.second_example.b

@[spec]
def call_a (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (new_tests.legacy__cyclic_modules__lib.issue_1823.second_example.a.a
    rust_primitives.hax.Tuple0.mk)

@[spec]
def b (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.issue_1823.second_example.b


namespace new_tests.legacy__cyclic_modules__lib.issue_1823.second_example.a

@[spec]
def call_b (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (new_tests.legacy__cyclic_modules__lib.issue_1823.second_example.b.b
    rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.issue_1823.second_example.a


namespace new_tests.legacy__cyclic_modules__lib.typ_b

inductive T2Rec : Type
| T2 : new_tests.legacy__cyclic_modules__lib.typ_a.TRec -> T2Rec

inductive T1Rec : Type
| T1 : T2Rec -> T1Rec

end new_tests.legacy__cyclic_modules__lib.typ_b


namespace new_tests.legacy__cyclic_modules__lib.typ_a

inductive TRec : Type
| T : new_tests.legacy__cyclic_modules__lib.typ_b.T1Rec -> TRec
| Empty : TRec

end new_tests.legacy__cyclic_modules__lib.typ_a


namespace new_tests.legacy__cyclic_modules__lib.rec

--  @fail(extraction): proverif(HAX0001)
@[spec]
def hf (x : T) : RustM T := do
  match x with | (T.t1 ) => do (hf T.t2) | (T.t2 ) => do (pure x)
partial_fixpoint

end new_tests.legacy__cyclic_modules__lib.rec


namespace new_tests.legacy__cyclic_modules__lib.rec2_same_name

--  @fail(extraction): proverif(HAX0001)
@[spec]
def f (x : i32) : RustM i32 := do
  if (← (x >? (0 : i32))) then do
    (new_tests.legacy__cyclic_modules__lib.rec1_same_name.f
      (← (x -? (1 : i32))))
  else do
    (pure (0 : i32))

end new_tests.legacy__cyclic_modules__lib.rec2_same_name


namespace new_tests.legacy__cyclic_modules__lib.rec1_same_name

--  @fail(extraction): proverif(HAX0001)
@[spec]
def f (x : i32) : RustM i32 := do
  (new_tests.legacy__cyclic_modules__lib.rec2_same_name.f x)

end new_tests.legacy__cyclic_modules__lib.rec1_same_name


namespace new_tests.legacy__cyclic_modules__lib.late_skip_b

--  @fail(extraction): proverif(HAX0001)
def f (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (new_tests.legacy__cyclic_modules__lib.late_skip_a.f
    rust_primitives.hax.Tuple0.mk)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def f.spec (_ : rust_primitives.hax.Tuple0) :
    Spec (requires := do (pure true)) (ensures := fun _ => pure True) (f ⟨⟩) :=
{
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [f] <;> bv_decide
}

end new_tests.legacy__cyclic_modules__lib.late_skip_b


namespace new_tests.legacy__cyclic_modules__lib.late_skip_a

--  @fail(extraction): proverif(HAX0001)
@[spec]
def f (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (new_tests.legacy__cyclic_modules__lib.late_skip_b.f
    rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cyclic_modules__lib.late_skip_a


namespace new_tests.legacy__cyclic_modules__lib.enums_b

inductive U : Type
| A : U
| B : U
| C : (alloc.vec.Vec
      new_tests.legacy__cyclic_modules__lib.enums_a.T
      alloc.alloc.Global) -> U

inductive T : Type
| A : T
| B : T
| C : (alloc.vec.Vec
      new_tests.legacy__cyclic_modules__lib.enums_a.T
      alloc.alloc.Global) -> T

end new_tests.legacy__cyclic_modules__lib.enums_b


namespace new_tests.legacy__cyclic_modules__lib.enums_a

inductive T : Type
| A : T
| B : T
| C : (alloc.vec.Vec
      new_tests.legacy__cyclic_modules__lib.enums_b.U
      alloc.alloc.Global) -> T
| D : (alloc.vec.Vec
      new_tests.legacy__cyclic_modules__lib.enums_b.T
      alloc.alloc.Global) -> T

end new_tests.legacy__cyclic_modules__lib.enums_a


namespace new_tests.legacy__cyclic_modules__lib.enums_b

@[spec]
def f (_ : rust_primitives.hax.Tuple0) : RustM T := do (pure T.A)

end new_tests.legacy__cyclic_modules__lib.enums_b


namespace new_tests.legacy__cyclic_modules__lib.rec

--  @fail(extraction): proverif(HAX0001)
@[spec]
def g2 (x : T) : RustM T := do
  match x with | (T.t1 ) => do (g1 x) | (T.t2 ) => do (hf x)

--  @fail(extraction): proverif(HAX0001)
@[spec]
def g1 (x : T) : RustM T := do
  match x with | (T.t1 ) => do (g2 x) | (T.t2 ) => do (pure T.t1)

end new_tests.legacy__cyclic_modules__lib.rec

