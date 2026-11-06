
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


namespace new_tests.legacy__recursion__lib

--  @fail(extraction): proverif(HAX0001)
@[spec]
def f (n : u8) : RustM u8 := do
  if (← (n ==? (0 : u8))) then do
    (pure (0 : u8))
  else do
    (n +? (← (f (← (n -? (1 : u8))))))
partial_fixpoint

end new_tests.legacy__recursion__lib

