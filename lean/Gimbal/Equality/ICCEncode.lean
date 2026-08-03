/-
  Encoding soundness and rigidity obligations for ordered-phase codes (8F/E).

  Primary target: `ICCEq t u ↔ encodeICC ε t = encodeICC ε u`.
  This file accumulates lemmas toward `EncodeIccInvariantGoal` and
  `IccEqIffEncodeEqGoal`. Termination of encode is by worklist/goal formula
  weight (candidate `encodeMeasure`), not by output AST size.
-/

import Gimbal.Equality.ICCCode
import Gimbal.Equality.ICCPeel

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Right-introduction encoding -/

theorem encodeICCGo_unit_nil (fuel : Nat) {Γ : Ctx sig} (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) :
    encodeICCGo (fuel + 1) ([] : List (PosEntry sig)) ε domNest obsSlot
      (.unit (Γ := Γ)) = some .unit := rfl

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
      exact encodeICCGo_unit_nil fuel ε 0 0

/-- Trivial direction of generator invariance. -/
theorem encodeICC_eq_refl {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (t : InvTm Γ A) :
    encodeICC ε t = encodeICC ε t := rfl

/-! ### Forced-rule unfolds -/

theorem forcedRule_cons_coprod (e : PosEntry sig) (ws : List (PosEntry sig))
    {L R : Object sig.nBases} (hty : e.ty = .coprod L R)
    (goal : Object sig.nBases) :
    forcedRule (e :: ws) goal = .leftCoprod e L R := by
  simp [forcedRule, hty]

/-! ### `case_pair` preserves codes under a forced outer coprod -/

theorem encodeICCGo_case_pair {Γ : Ctx sig} {A B C D : Object sig.nBases}
    (fuel : Nat) (e : PosEntry sig) (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (x : Var Γ (.coprod A B))
    (t₁ : InvTm (Γ ▻ A) C) (t₂ : InvTm (Γ ▻ B) C)
    (u₁ : InvTm (Γ ▻ A) D) (u₂ : InvTm (Γ ▻ B) D)
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin) :
    encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot
        (.case (.var x) (.pair t₁ u₁) (.pair t₂ u₂)) =
      encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot
        (.pair (.case (.var x) t₁ t₂) (.case (.var x) u₁ u₂)) := by
  have hforce := forcedRule_cons_coprod e ws hty (.prod C D)
  have hpeel := peelCaseOuter_case_pair ε e.origin x t₁ t₂ u₁ u₂ hit
  -- Both peels yield the same outer case; encode follows that shared peel.
  simp [encodeICCGo, hforce, hpeel.1, hpeel.2]

/-! ### Open obligations (design E remaining work)

Tracked as goal Props in `Completeness.lean`:

1. ~~`OriginCollisionFree` API~~ **Done** (`Origin.dom`, `obsSlot`/`domNest`)
2. ~~Peel soundness (`peelCaseOuter_icc`)~~ **Done**
3. `EncodeIccInvariant` / rigidity / `ICCCompleteness` (guarded by `isSome`)
4. `EncodeTotal` — measure adequacy; no proof-critical fuel exhaustion
5. `ReferenceCompareTotal` + iff — total comparator; **no `2048` decidability**
6. Wire code equality into the total `referenceCompare`; resume 8G
-/

end Equality
end Gimbal
