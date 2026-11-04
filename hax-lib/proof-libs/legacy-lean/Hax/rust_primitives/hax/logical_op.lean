import Hax.Tactic.Init
import Hax.rust_primitives.RustM

/-
  Logic predicates introduced by Hax (in pre/post conditions)
-/
namespace rust_primitives.hax.logical_op

/-- Boolean conjunction. Cannot panic (always returns .ok ) -/
@[simp, spec, hax_bv_decide]
def and (a b: Bool) : RustM Bool := pure (a && b)

/-- Boolean disjunction. Cannot panic (always returns .ok )-/
@[simp, spec, hax_bv_decide]
def or (a b: Bool) : RustM Bool := pure (a || b)

/-- Boolean exclusive disjunction. Cannot panic (always returns .ok )-/
@[simp, spec, hax_bv_decide]
def xor (a b: Bool) : RustM Bool := pure (a ^^ b)

/-- Boolean negation. Cannot panic (always returns .ok )-/
@[simp, spec, hax_bv_decide]
def not (a :Bool) : RustM Bool := pure (!a)

/-- Boolean conjunction that runs `b` only when `a` holds -/
def and_then (a : Bool) (b : RustM Bool) : RustM Bool := if a then b else pure false

/-- Boolean disjunction that runs `b` only when `a` does not hold -/
def or_else (a : Bool) (b : RustM Bool) : RustM Bool := if a then pure true else b

open Std.Do in
/-- Requires `b` to succeed even when it is not run, as the `&&?` it replaces,
so that it yields a single verification condition -/
@[spec]
theorem and_then.spec {a : Bool} {b : RustM Bool}
    {Q : PostCond Bool (.except Error (.except PUnit .pure))} :
    ⦃wp⟦b⟧ (fun r => Q.1 (a && r), ExceptConds.false)⦄ and_then a b ⦃Q⦄ := by
  cases a
  · simp only [and_then, Bool.false_and, Triple]
    rcases b with _ | _ | r
    all_goals simp [wp, ExceptT.run, ExceptConds.false, OptionT.run, Id.run, pure,
      ExceptT.pure, ExceptT.mk]
  · simp only [and_then, Bool.true_and, if_true, Triple]
    exact (wp b).mono _ _ ⟨fun r => .rfl, ExceptConds.entails_false⟩

open Std.Do in
/-- Requires `b` to succeed even when it is not run, as the `||?` it replaces,
so that it yields a single verification condition -/
@[spec]
theorem or_else.spec {a : Bool} {b : RustM Bool}
    {Q : PostCond Bool (.except Error (.except PUnit .pure))} :
    ⦃wp⟦b⟧ (fun r => Q.1 (a || r), ExceptConds.false)⦄ or_else a b ⦃Q⦄ := by
  cases a
  · simp only [or_else, Bool.false_or, Triple]
    exact (wp b).mono _ _ ⟨fun r => .rfl, ExceptConds.entails_false⟩
  · simp only [or_else, Bool.true_or, if_true, Triple]
    rcases b with _ | _ | r
    all_goals simp [wp, ExceptT.run, ExceptConds.false, OptionT.run, Id.run, pure,
      ExceptT.pure, ExceptT.mk]

@[inherit_doc] infixl:35 " &&? " => and
@[inherit_doc] infixl:30 " ||? " => or
@[inherit_doc] infixl:30 " ^^? " => xor
@[inherit_doc] notation:max "!?" b:40 => not b

end rust_primitives.hax.logical_op

namespace rust_primitives.hax

@[spec] def logical_op_or (x y : Bool) : RustM Bool := pure (x || y)
@[spec] def logical_op_and (x y : Bool) : RustM Bool := pure (x && y)

end rust_primitives.hax
