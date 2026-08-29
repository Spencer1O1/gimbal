/-
  Boundary counterexample for unrestricted consistency-query splicing.

  A query below `CPos.shift` is interpreted after `resetRound`. Its finite
  normal form therefore cannot see which variables belonged to the enclosing
  round. Two derivations of the same exact child query can consequently have
  different use under the enclosing current mask. Replacing one by the other
  does not, in general, preserve the enclosing `CQuery` index.
-/

import Gimbal.Equality.Scherer.ConsistencyTransport

namespace Gimbal.Equality.Scherer
namespace ConsistencySpliceBoundary

open FrameContractionFixtures ScopeTransportFixtures

/-! ### A mixed-round duplicate frame -/

/-- Reset after the first duplicate, then add the second duplicate. -/
theorem mixedHd : cst1.resetRound.depth < 2 := by decide

def mixedState : ResolvedState Uc O1 2 :=
  cst1.resetRound.pushResolved mixedHd USc {o}

theorem mixedRealizes : CtxRealizes mixedState CΓ2 cenv2 := by
  simpa [mixedState, ResolvedState.pushResolved, CΓ2, cenv2, USc] using
    CtxRealizes.push crealizes1.resetRound mixedHd USc {o}

/-- Neither duplicate is outer-new. -/
def mixedInput : RealizedFrameInput mixedState := ⟨fun _ => false⟩

/-- The older duplicate is not current; the newest duplicate is current. -/
def mixed : ConsistencyScope Uc O1 2 CΓ2 where
  state := mixedState
  env := cenv2
  frameInput := mixedInput
  outer := FrameRealizes.outerMask mixedRealizes mixedInput
  current := FrameRealizes.currentMask mixedRealizes
  realizes := FrameRealizes.canonical mixedRealizes mixedInput
  coverage := ∅

def oldVar : StableVar CΓ2 S := .there .here
def newVar : StableVar CΓ2 S := .here

theorem mixed_masks :
    mixed.outer S oldVar = false ∧ mixed.outer S newVar = false ∧
      mixed.current S oldVar = false ∧ mixed.current S newVar = true := by
  native_decide

theorem reset_masks :
    mixed.resetRound.outer S oldVar = false ∧
      mixed.resetRound.outer S newVar = false ∧
      mixed.resetRound.current S oldVar = false ∧
      mixed.resetRound.current S newVar = false := by
  native_decide

/-! ### Same exact reset query, different enclosing use -/

def zeroTarget : Obligation Uc O1 := ⟨⟨.zero, by simp [Uc]⟩, {o}⟩
def resetUse : UseSig := ⟨false, false⟩

def oldNeutral : SNegNeu CΓ2 (.shift .zero) := .var oldVar
def newNeutral : SNegNeu CΓ2 (.shift .zero) := .var newVar

def oldQuery : CQuery mixed.resetRound zeroTarget resetUse oldNeutral :=
  .intro (.var oldVar) (by native_decide) (by native_decide)

def newQuery : CQuery mixed.resetRound zeroTarget resetUse newNeutral :=
  .intro (.var newVar) (by native_decide) (by native_decide)

theorem zeroRequest : ZeroRequest mixed.resetRound {o} resetUse where
  zero_mem := by simp [Uc]

def oldSat : CSat (Old := CΓ2) (New := .empty) mixed.resetRound
    (P := (.zero : Pos 0))
    (Sat.inconsistent (Old := CΓ2) (New := .empty) oldNeutral) :=
  .inconsistent zeroRequest oldQuery

def newSat : CSat (Old := CΓ2) (New := .empty) mixed.resetRound
    (P := (.zero : Pos 0))
    (Sat.inconsistent (Old := CΓ2) (New := .empty) newNeutral) :=
  .inconsistent zeroRequest newQuery

def oldPos : SPosNeu CΓ2 (.shift (.shift (.zero : Pos 0))) :=
  .shift (.satShift (.inconsistent oldNeutral))

def newPos : SPosNeu CΓ2 (.shift (.shift (.zero : Pos 0))) :=
  .shift (.satShift (.inconsistent newNeutral))

def oldPosGenerated : CPos mixed oldPos :=
  .shift (.satShift oldSat)

def newPosGenerated : CPos mixed newPos :=
  .shift (.satShift newSat)

/-- The two replaceable children inhabit literally the same intrinsic query,
not merely equal normalized keys. -/
theorem child_query_identical :
    (mixed.resetRound.query zeroTarget resetUse).normalize =
      (mixed.resetRound.query zeroTarget resetUse).normalize := rfl

/-- Both children have the exact same result, support, UseSig, generation, and
freshness data required by `CQuery`. -/
theorem both_children_generated :
    Nonempty (CQuery mixed.resetRound zeroTarget resetUse oldNeutral) ∧
      Nonempty (CQuery mixed.resetRound zeroTarget resetUse newNeutral) ∧
      oldNeutral.resolvedSupport mixed.resetRound.env =
        newNeutral.resolvedSupport mixed.resetRound.env ∧
      oldNeutral.useSig mixed.resetRound.outer mixed.resetRound.current =
        newNeutral.useSig mixed.resetRound.outer mixed.resetRound.current := by
  exact ⟨⟨oldQuery⟩, ⟨newQuery⟩, by native_decide, by native_decide⟩

/-- Nevertheless the enclosing pre-reset current mask distinguishes the two
generated positive terms. -/
theorem enclosing_current_distinguishes :
    oldPos.uses mixed.current = false ∧
      newPos.uses mixed.current = true := by
  native_decide

/-- Therefore an unrestricted one-hole replacement theorem cannot promise
preservation of the enclosing current-use bit from only the child query index,
normalized equality, headroom, and target split evidence. -/
theorem identical_child_query_does_not_preserve_enclosing_use :
    oldNeutral.useSig mixed.resetRound.outer mixed.resetRound.current =
        newNeutral.useSig mixed.resetRound.outer mixed.resetRound.current ∧
      oldPos.uses mixed.current ≠ newPos.uses mixed.current := by
  exact ⟨by native_decide, by native_decide⟩

end ConsistencySpliceBoundary
end Gimbal.Equality.Scherer
