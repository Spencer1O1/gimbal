/-
  Early Milestone 7 fixtures: intrinsic elaboration round-trips.
-/

import Gimbal.Equality.Elaborate
import Gimbal.Fixtures

namespace Gimbal.Equality.Fixtures

open Gimbal Gimbal.Fixtures Gimbal.Equality

example : (ofMorphism two).erase = two.term :=
  ofMorphism_erase two

example : (ofMorphism pairThenAdd).erase = pairThenAdd.term :=
  ofMorphism_erase pairThenAdd

example : (ofMorphism curryAdd).erase = curryAdd.term :=
  ofMorphism_erase curryAdd

example : (ofMorphism two).toMorphism = two :=
  ofMorphism_toMorphism two

/-- Ill-typed terms do not elaborate. -/
example : elaborate (sig := NumSig) illTypedComposeTerm = none :=
  rfl

/-- Well-typed generator elaborates to the matching intrinsic constructor. -/
example :
    elaborate (sig := NumSig) two.term =
      some ⟨.unit, Number, .generator ⟨0, by decide⟩⟩ :=
  rfl

end Gimbal.Equality.Fixtures
