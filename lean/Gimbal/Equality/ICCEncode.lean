/-
  Encoding soundness and rigidity obligations for ordered-phase codes (8F/E).

  Primary target: `ICCEq t u ↔ encodeICC ε t = encodeICC ε u`.
  This file accumulates lemmas toward `EncodeIccInvariantGoal` and
  `IccEqIffEncodeEqGoal`. Termination of encode is by worklist/goal formula
  weight (candidate `encodeMeasure`), not by output AST size.
-/

import Gimbal.Equality.ICCCode

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Right-introduction encoding -/

theorem encodeICCGo_unit_nil (fuel : Nat) {Γ : Ctx sig} (ε : OriginEnv Γ) :
    encodeICCGo (fuel + 1) ([] : List (PosEntry sig)) ε (.unit (Γ := Γ)) =
      some .unit := rfl

theorem encodeICC_unit_of_nilWorklist {Γ : Ctx sig} (ε : OriginEnv Γ)
    (hws : OriginEnv.posWorklist ε = []) :
    encodeICC ε (.unit (Γ := Γ)) = some .unit := by
  unfold encodeICC
  rw [hws]
  have hpos : 0 < objectWeight (.unit : Object sig.nBases) := objectWeight_pos _
  have : 0 < encodeMeasure ([] : List (PosEntry sig)) (.unit : Object sig.nBases) := by
    simpa [encodeMeasure, worklistWeight] using hpos
  match hm : encodeMeasure ([] : List (PosEntry sig)) (.unit : Object sig.nBases) with
  | 0 =>
      simp only [encodeMeasure, worklistWeight, List.foldl, objectWeight] at hm
      omega
  | fuel + 1 =>
      exact encodeICCGo_unit_nil fuel ε

/-- Trivial direction of generator invariance. -/
theorem encodeICC_eq_refl {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (t : InvTm Γ A) :
    encodeICC ε t = encodeICC ε t := rfl

/-! ### Open obligations (design E remaining work)

Tracked as goal Props in `Completeness.lean`:

1. `OriginCollisionFree` — replace `Origin.obs 0` and λ `.split (.hyp 0) false`
2. ~~Peel soundness (`peelCaseOuter_icc`)~~ **Done**
3. `EncodeIccInvariant` / rigidity / `ICCCompleteness`
4. `EncodeTotal` — measure adequacy; no proof-critical fuel exhaustion
5. `ReferenceCompareTotal` + iff — total comparator; **no `2048` decidability**
6. Wire code equality into the total `referenceCompare`; resume 8G
-/

end Equality
end Gimbal
