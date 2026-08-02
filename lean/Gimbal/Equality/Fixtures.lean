/-
  Early Milestone 7 fixtures: elaboration, translation, polarization, focusing.
  Includes a short pre-reachability hardening pass.
-/

import Gimbal.Equality.Focus
import Gimbal.Equality.Translate
import Gimbal.Equality.Reachability
import Gimbal.Equality.Saturation
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

/-! ### Hardening helpers -/

private def isUnitInv {Γ : Ctx NumSig} : InvTm Γ .unit → Bool
  | .unit => true
  | _ => false

private def isIdFocused : InvTm (translateCtx (sig := NumSig) Number) Number → Bool
  | .foc (.pos (.done (.neu (.var .here)))) => true
  | _ => false

private def isFirstFocused :
    InvTm (translateCtx (sig := NumSig) (.prod Number Number)) Number → Bool
  | .foc (.pos (.done (.neu (.fst (.var .here))))) => true
  | _ => false

private def isLeftFocused :
    InvTm (translateCtx (sig := NumSig) Number) (.coprod Number Number) → Bool
  | .foc (.pos (.done (.inl (.neu (.var .here))))) => true
  | _ => false

private def isCaseUnit :
    InvTm (translateCtx (sig := NumSig) (.coprod Number Number)) .unit → Bool
  | .case (.var .here) .unit .unit => true
  | _ => false

private def isAbsurdFocused :
    InvTm (translateCtx (sig := NumSig) .never) Number → Bool
  | .abort (.var .here) => true
  | _ => false

/-! ### Hardening checks -/

def focusDiscardIsUnit : Bool :=
  match focus! (translate (sig := NumSig) (.discard Number)) with
  | some t => isUnitInv t
  | none => false

example : focusDiscardIsUnit = true := by native_decide

def focusIdIsVar : Bool :=
  match focus! (translate (sig := NumSig) (.id Number)) with
  | some t => isIdFocused t
  | none => false

example : focusIdIsVar = true := by native_decide

def focusFirstIsFst : Bool :=
  match focus! (translate (sig := NumSig) (.first Number Number)) with
  | some t => isFirstFocused t
  | none => false

example : focusFirstIsFst = true := by native_decide

def focusLeftIsInl : Bool :=
  match focus! (translate (sig := NumSig) (.left Number Number)) with
  | some t => isLeftFocused t
  | none => false

example : focusLeftIsInl = true := by native_decide

example : (focus! (translateMorphism two)).isSome = true := by
  native_decide

example : (focus! (translateMorphism curryAdd)).isSome = true := by
  native_decide

def caseDiscard : IntrinsicMorphism NumSig (.coprod Number Number) .unit :=
  IntrinsicMorphism.case (sig := NumSig)
    (.discard (sig := NumSig) Number)
    (.discard (sig := NumSig) Number)

def focusCaseIsCase : Bool :=
  match focus! (translate caseDiscard) with
  | some t => isCaseUnit t
  | none => false

example : focusCaseIsCase = true := by native_decide

def focusAbsurdIsAbort : Bool :=
  match focus! (translate (sig := NumSig) (.absurd Number)) with
  | some t => isAbsurdFocused t
  | none => false

example : focusAbsurdIsAbort = true := by native_decide

example :
    (focus! (translate (sig := NumSig) (.eval Number Number))).isSome = true := by
  native_decide

example : (focus! (translateMorphism pairThenAdd)).isSome = true := by
  native_decide

/-! ### Reachability spike gates -/

/-- `x : X, s : X → X` — type universe stays finite (no neutral explosion). -/
def cycleCtx : ReachCtx 1 where
  hyps := #[(.base 0 : Object 1), .exp (.base 0) (.base 0)]
  newFrom := 0

def cycleGoal : Object 1 := .base 0

def cycleState : ReachState 1 :=
  runReachability cycleCtx cycleGoal

/-- Subformula closure is tiny: X and X→X only. -/
example : (subformulaClosure (cycleCtx.roots cycleGoal)).size = 2 := by
  native_decide

/-- X is retrievable from the context variable. -/
example : isRetrievable cycleState (.base 0) = true := by
  native_decide

/-- Applying `s` does not enlarge the type universe. -/
example : (pendingWitnesses cycleState).size = 0 := by
  native_decide

/-- Inconsistent context: `x : 0` makes never simply deducible. -/
def neverCtx : ReachCtx 1 where
  hyps := #[(.never : Object 1)]
  newFrom := 0

example : (runReachability neverCtx (.base 0)).inconsistent = true := by
  native_decide

/--
New fragment: old has `s : X → Y`, new has `x : X`.
Then `Y` becomes simply deducible via app, not yet retrievable.
-/
def appCtx : ReachCtx 2 where
  hyps := #[
    .exp (.base 0) (.base 1), -- s : X → Y  (old)
    .base 0                    -- x : X      (new)
  ]
  newFrom := 1

def appState : ReachState 2 :=
  runReachability appCtx (.base 1)

example : isSimplyDeducible appState (.base 1) = true := by
  native_decide

example : isRetrievable appState (.base 1) = false := by
  native_decide

example : (pendingWitnesses appState).size = 1 := by
  native_decide

/-- Pending `Y` uses the new hypothesis `x`. -/
example : usesNew appState (.base 1) = true := by
  native_decide

/-- Schedule contains exactly that pending witness. -/
example : (buildSchedule appState).size = 1 := by
  native_decide

/-- Product projection: `p : X × Y` makes both components deducible. -/
def prodCtx : ReachCtx 2 where
  hyps := #[.prod (.base 0) (.base 1)]
  newFrom := 0

def prodState : ReachState 2 :=
  runReachability prodCtx (.base 0)

example : isSimplyDeducible prodState (.base 0) = true := by
  native_decide

example : isSimplyDeducible prodState (.base 1) = true := by
  native_decide

/-- Old-only deduction: `Y` reachable without `Γnew` is not scheduled. -/
def oldOnlyCtx : ReachCtx 2 where
  hyps := #[
    .exp (.base 0) (.base 1),
    .base 0
  ]
  newFrom := 2  -- everything is old

example : (buildSchedule (runReachability oldOnlyCtx (.base 1))).size = 0 := by
  native_decide

example : isSimplyDeducible (runReachability oldOnlyCtx (.base 1)) (.base 1) = true := by
  native_decide

/-! ### Saturation schedule scaffolding -/

def satUnitEraseOk : Bool :=
  let s := saturate (sig := NumSig) neverCtx (.unit : Object 1)
    (InvTm.unit (Γ := Ctx.empty (sig := NumSig)))
  match s with
  | .mk sched cont =>
    sched.size == 0 &&
      match cont with
      | .unit => true
      | _ => false

example : satUnitEraseOk = true := by native_decide

end Gimbal.Equality.Fixtures
