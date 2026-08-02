/-
  Early Milestone 7 fixtures: intrinsic elaboration and translation.
-/

import Gimbal.Equality.Translate
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

/-- Identity translates to the source variable. -/
example :
    translate (sig := NumSig) (.id Number) = .var .here :=
  rfl

/-- Discard translates to unit. -/
example :
    translate (sig := NumSig) (.discard Number) = .unit :=
  rfl

/-- `first` translates to `fst x`. -/
example :
    translate (sig := NumSig) (.first Number Number) = .fst (.var .here) :=
  rfl

/-- Generator `two` translates to application of the rigid generator variable. -/
example :
    translateMorphism two =
      .app (.var (.there (genVar NumSig ⟨0, by decide⟩))) (.var .here) :=
  rfl

end Gimbal.Equality.Fixtures
