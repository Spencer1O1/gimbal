/-
  Early Milestone 7 fixtures: elaboration, translation, polarization, focusing.
-/

import Gimbal.Equality.Focus
import Gimbal.Equality.Translate
import Gimbal.Fixtures

namespace Gimbal.Equality.Fixtures

open Gimbal Gimbal.Fixtures Gimbal.Equality

example : (ofMorphism two).erase = two.term :=
  ofMorphism_erase two

example : elaborate (sig := NumSig) illTypedComposeTerm = none :=
  rfl

example :
    translate (sig := NumSig) (.id Number) = .var .here :=
  rfl

example :
    translate (sig := NumSig) (.discard Number) = .unit :=
  rfl

example :
    translateMorphism two =
      .app (.var (.there (genVar NumSig ⟨0, by decide⟩))) (.var .here) :=
  rfl

/-- Fixed polarity assignment. -/
example : objectPolarity (Number : Object 1) = .pos := rfl
example : objectPolarity (.unit : Object 1) = .neg := rfl
example : objectPolarity (.prod Number Number) = .neg := rfl
example : objectPolarity (.coprod Number Number) = .pos := rfl
example : objectPolarity (.exp Number Number) = .neg := rfl

/-- Minimal shifts erase. -/
example : (asPos (Number : Object 1)).erase = Number :=
  erase_asPos _
example : (asNeg (.unit : Object 1)).erase = .unit :=
  erase_asNeg _

/-- Focusing succeeds on representative translated terms (mutual defs; use native). -/
example : (focus! (sig := NumSig) (translate (.id Number))).isSome = true := by
  native_decide

example : (focus! (sig := NumSig) (translate (.discard Number))).isSome = true := by
  native_decide

example : (focus! (sig := NumSig) (translate (.first Number Number))).isSome = true := by
  native_decide

example : (focus! (sig := NumSig) (translateMorphism two)).isSome = true := by
  native_decide

end Gimbal.Equality.Fixtures
