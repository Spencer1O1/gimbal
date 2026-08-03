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

theorem encodeICCGo_case_lam {Γ : Ctx sig} {A B Arg Ret : Object sig.nBases}
    (fuel : Nat) (e : PosEntry sig) (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (x : Var Γ (.coprod A B))
    (t : InvTm (Γ ▻ A ▻ Arg) Ret) (u : InvTm (Γ ▻ B ▻ Arg) Ret)
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin) :
    encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot
        (.case (.var x) (.lam t) (.lam u)) =
      encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot
        (.lam (.case (NegNeu.weaken (B := Arg) (.var x))
          (InvTm.rename Rename.exchange t)
          (InvTm.rename Rename.exchange u))) := by
  have hforce := forcedRule_cons_coprod e ws hty (.exp Arg Ret)
  have hpeel := peelCaseOuter_case_lam ε e.origin x t u hit
  simp [encodeICCGo, hforce, hpeel.1, hpeel.2]

private theorem List.foldl_add_nat {α : Type _} (ws : List α) (f : α → Nat) (a : Nat) :
    ws.foldl (fun acc x => acc + f x) a =
      a + ws.foldl (fun acc x => acc + f x) 0 := by
  induction ws generalizing a with
  | nil => rfl
  | cons x xs ih =>
      have hx :
          (x :: xs).foldl (fun acc y => acc + f y) 0 =
            f x + xs.foldl (fun acc y => acc + f y) 0 := by
        simpa [List.foldl, Nat.zero_add] using ih (f x)
      change xs.foldl (fun acc y => acc + f y) (a + f x) =
        a + (x :: xs).foldl (fun acc y => acc + f y) 0
      rw [ih (a + f x), hx]
      omega

private theorem worklistWeight_cons (e : PosEntry sig) (ws : List (PosEntry sig)) :
    worklistWeight (e :: ws) = objectWeight e.ty + worklistWeight ws := by
  simp only [worklistWeight, List.foldl]
  have h := List.foldl_add_nat ws (fun e => objectWeight e.ty) (objectWeight e.ty)
  simpa [Nat.zero_add] using h

private theorem encodeMeasure_cons_pos (e : PosEntry sig) (ws : List (PosEntry sig))
    (goal : Object sig.nBases) :
    0 < encodeMeasure (e :: ws) goal := by
  have he : 0 < objectWeight e.ty := objectWeight_pos _
  have hg : 0 < objectWeight goal := objectWeight_pos _
  rw [encodeMeasure, worklistWeight_cons]
  omega

/-- `ICCEq.case_pair` preserves `encodeICC` when the worklist head is that coprod. -/
theorem encodeICC_case_pair {Γ : Ctx sig} {A B C D : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (x : Var Γ (.coprod A B))
    (t₁ : InvTm (Γ ▻ A) C) (t₂ : InvTm (Γ ▻ B) C)
    (u₁ : InvTm (Γ ▻ A) D) (u₂ : InvTm (Γ ▻ B) D)
    (hws : OriginEnv.posWorklist ε = e :: ws)
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin) :
    encodeICC ε (.case (.var x) (.pair t₁ u₁) (.pair t₂ u₂)) =
      encodeICC ε (.pair (.case (.var x) t₁ t₂) (.case (.var x) u₁ u₂)) := by
  unfold encodeICC
  rw [hws]
  have hpos := encodeMeasure_cons_pos e ws (.prod C D)
  obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  simpa [hm] using
    encodeICCGo_case_pair fuel e ws ε 0 0 x t₁ t₂ u₁ u₂ hty hit

/-- `ICCEq.case_lam` preserves `encodeICC` when the worklist head is that coprod. -/
theorem encodeICC_case_lam {Γ : Ctx sig} {A B Arg Ret : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (x : Var Γ (.coprod A B))
    (t : InvTm (Γ ▻ A ▻ Arg) Ret) (u : InvTm (Γ ▻ B ▻ Arg) Ret)
    (hws : OriginEnv.posWorklist ε = e :: ws)
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin) :
    encodeICC ε (.case (.var x) (.lam t) (.lam u)) =
      encodeICC ε
        (.lam (.case (NegNeu.weaken (B := Arg) (.var x))
          (InvTm.rename Rename.exchange t)
          (InvTm.rename Rename.exchange u))) := by
  unfold encodeICC
  rw [hws]
  have hpos := encodeMeasure_cons_pos e ws (.exp Arg Ret)
  obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  simpa [hm] using
    encodeICCGo_case_lam fuel e ws ε 0 0 x t u hty hit

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
