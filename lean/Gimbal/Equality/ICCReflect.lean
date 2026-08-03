/-
  Reflection / common-code soundness for ordered-phase codes (design E rigidity).

  Invariance:     ICCEq t u → EncodeIccStep ε t u
  Reflection:     encodeICC ε t = some c → encodeICC ε u = some c → ICCEq t u

  “Rigidity” means the second theorem (or an equivalent reify-and-relate
  package). Peel soundness (`peelCaseOuter_icc`) supports showing each
  encodable term is ICC-equivalent to the ordered phase its code denotes.
-/

import Gimbal.Equality.ICC
import Gimbal.Equality.ICCEncode
import Gimbal.Equality.ICCPeel
import Gimbal.Equality.ICCTotal

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Peel supports ordered-phase reflection -/

/--
Peel soundness: a successful outer peel is an ICC step toward the ordered
left-coprod form that encode continues under `encodeLeftCoprodBranches`.
-/
theorem peelCaseOuter_icc_of_some {Γ : Ctx sig} {C : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) (t : InvTm Γ C)
    {A B : Object sig.nBases} {n : NegNeu Γ (.coprod A B)}
    {tL : InvTm (Γ ▻ A) C} {tR : InvTm (Γ ▻ B) C}
    (h : peelCaseOuter ε o t = some ⟨A, B, n, tL, tR⟩) :
    ICCEq t (.case n tL tR) :=
  peelCaseOuter_icc ε o t h

/-! ### Reflection base cases -/

/-- Under forced `leftNever`, a successful encode forces an abort code. -/
private theorem encodeICCGo_leftNever_eq_abort {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (e : PosEntry sig) (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat) (t : InvTm Γ A)
    (hty : e.ty = .never) {c : ICCCode Γ A}
    (h : encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot t = some c) :
    ∃ n, t = .abort n ∧ c = .abort e.origin := by
  cases t with
  | abort n =>
      have hab :=
        encodeICCGo_abort_leftNever (A := A) fuel e ws ε domNest obsSlot n hty
      refine ⟨n, rfl, Option.some.inj (h.symm.trans hab)⟩
  | unit =>
      simp [encodeICCGo, forcedRule_cons_never e ws hty _] at h
  | pair t₁ t₂ =>
      simp [encodeICCGo, forcedRule_cons_never e ws hty _] at h
  | lam body =>
      simp [encodeICCGo, forcedRule_cons_never e ws hty _] at h
  | case n tL tR =>
      simp [encodeICCGo, forcedRule_cons_never e ws hty _] at h
  | foc f =>
      simp [encodeICCGo, forcedRule_cons_never e ws hty _] at h

/-- Under forced `leftNever`, any two successful encodes are `abort_eq`. -/
theorem encode_reflect_abort_leftNever {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (hws : OriginEnv.posWorklist ε = e :: ws) (hty : e.ty = .never)
    {t u : InvTm Γ A} {c : ICCCode Γ A}
    (ht : encodeICC ε t = some c) (hu : encodeICC ε u = some c) :
    ICCEq t u := by
  unfold encodeICC at ht hu
  rw [hws] at ht hu
  have hpos := encodeMeasure_cons_pos e ws A
  obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  simp only [hm] at ht hu
  obtain ⟨n, rfl, _⟩ := encodeICCGo_leftNever_eq_abort fuel e ws ε 0 0 t hty ht
  obtain ⟨m, rfl, _⟩ := encodeICCGo_leftNever_eq_abort fuel e ws ε 0 0 u hty hu
  exact ICCEq.abort_eq n m

/-- Nil-worklist unit: successful encode forces `.unit`. -/
private theorem encodeICCGo_rightUnit_eq_unit {Γ : Ctx sig}
    (fuel : Nat) (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (t : InvTm Γ .unit) {c : ICCCode Γ .unit}
    (h : encodeICCGo (fuel + 1) ([] : List (PosEntry sig)) ε domNest obsSlot t =
      some c) :
    t = .unit ∧ c = .unit := by
  cases t with
  | unit =>
      have hu := encodeICCGo_unit_nil fuel ε domNest obsSlot
      exact ⟨rfl, Option.some.inj (h.symm.trans hu)⟩
  | case _ _ _ =>
      simp [encodeICCGo, forcedRule, peelUnit] at h
  | abort _ =>
      simp [encodeICCGo, forcedRule, peelUnit] at h
  | foc _ =>
      simp [encodeICCGo, forcedRule, peelUnit] at h

theorem encode_reflect_unit_nil {Γ : Ctx sig} (ε : OriginEnv Γ)
    (hws : OriginEnv.posWorklist ε = [])
    {t u : InvTm Γ .unit} {c : ICCCode Γ .unit}
    (ht : encodeICC ε t = some c) (hu : encodeICC ε u = some c) :
    ICCEq t u := by
  unfold encodeICC at ht hu
  rw [hws] at ht hu
  have hpos : 0 < encodeMeasure ([] : List (PosEntry sig)) (.unit : Object sig.nBases) := by
    have := objectWeight_pos (.unit : Object sig.nBases)
    simpa [encodeMeasure, worklistWeight] using this
  obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  simp only [hm] at ht hu
  obtain ⟨rfl, rfl⟩ := encodeICCGo_rightUnit_eq_unit fuel ε 0 0 t ht
  obtain ⟨rfl, _⟩ := encodeICCGo_rightUnit_eq_unit fuel ε 0 0 u hu
  exact ICCEq.refl _

/-! ### Packaging toward `EncodeIccReflectGoal` -/

/--
Common-code soundness from a reify-and-relate argument:

each successful encode yields a term ICC-equivalent to the ordered phase its
code denotes; identical codes then give `ICCEq` by transitivity.

Base cases above discharge atom codes (`unit`, `abort`). Peel soundness
(`peelCaseOuter_icc_of_some`) is the left-coprod step of that induction.
Full discharge is `EncodeIccReflectGoal` in `ICCCode` / `Completeness`.
-/
abbrev EncodeIccReflectFromReifyGoal : Prop :=
  EncodeIccReflectGoal (sig := sig)

end Equality
end Gimbal
