module New_tests.Legacy__attributes__lib.Props
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): proverif(HAX0001, HAX0001)
let f (x: Hax_lib.Prop.t_Prop) (y: bool) : Hax_lib.Prop.t_Prop =
  let (xprop: Hax_lib.Prop.t_Prop):Hax_lib.Prop.t_Prop = b2t y in
  let p:Hax_lib.Prop.t_Prop = b2t y /\ xprop /\ b2t y /\ b2t y in
  ~(p \/ b2t y ==>
    (forall (x: u8). b2t (x <=. Core_models.Num.impl_u8__MAX <: bool)) /\
    (exists (x: u16). b2t (x >. mk_u16 300 <: bool)))
