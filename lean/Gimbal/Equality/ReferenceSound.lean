/-
  Soundness of the reference comparator.

  If the reference pipeline answers `.equal` then the two inputs have the same
  meaning. Each stage contributes one lemma: schedule application preserves
  meaning (`tmEq_applyPairObs`), ICC canonicalization preserves meaning
  (`tmEq_canonicalize`), and the lockstep structural comparison only ever
  reports `.equal` on terms it can prove equal — typed structural equality at
  the leaves, congruence at the nodes.
-/

import Gimbal.Equality.ICCCanon
import Gimbal.Equality.Reference
import Gimbal.Equality.SatPreserve

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- Both halves of a conjunctive answer must be `.equal`. -/
theorem CandidateResult.and_eq_equal {r₁ r₂ : CandidateResult}
    (h : r₁.and r₂ = .equal) : r₁ = .equal ∧ r₂ = .equal := by
  cases r₁ <;> cases r₂ <;> simp_all [CandidateResult.and]

theorem InvTm.tmEq_of_castCtx {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (h : Γ = Δ) {t u : InvTm Δ A}
    (H : TmEq (InvTm.castCtx h.symm t).erase (InvTm.castCtx h.symm u).erase) :
    TmEq t.erase u.erase := by
  cases h
  exact H

/-- A successful typed comparison of canonical forms means equal meanings. -/
theorem tmEq_of_referenceStructEq {Γ : Ctx sig} {A : Object sig.nBases}
    {t u : InvTm Γ A} (h : referenceStructEq t u = true) :
    TmEq t.erase u.erase := by
  rw [referenceStructEq] at h
  have := InvTm.eq_of_beq _ _ h
  exact (tmEq_canonicalize t).symm.trans (.trans (.of_eq (congrArg _ this))
    (tmEq_canonicalize u))

/-- The reference pipeline only answers `.equal` on terms with equal meanings. -/
theorem tmEq_reference : ∀ fuel : Nat,
    (∀ (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases)
        {A : Object sig.nBases} {t u : InvTm (Ctx.ofHyps Γ.hyps) A},
        referenceSatRec fuel Γ goal t u = .equal → TmEq t.erase u.erase) ∧
    (∀ (hyps : Array (Object sig.nBases)) (goal : Object sig.nBases)
        {A : Object sig.nBases} {t u : InvTm (Ctx.ofHyps hyps) A},
        referenceInvRec fuel hyps goal t u = .equal → TmEq t.erase u.erase)
  | 0 => by
      constructor <;> intros <;>
        simp_all [referenceSatRec, referenceInvRec]
  | fuel + 1 => by
      obtain ⟨ihSat, ihInv⟩ := tmEq_reference fuel
      constructor
      · intro Γ goal A t u h
        rw [referenceSatRec.eq_def] at h
        dsimp only at h
        by_cases hinv : (!checkOldInvariant Γ.oldPrefix goal) = true
        · rw [if_pos hinv] at h; exact absurd h (by simp)
        · rw [if_neg hinv] at h
          cases hp : pairObs Γ goal t u with
          | invariantFailure => rw [hp] at h; exact absurd h (by simp)
          | ok entries σ =>
            rw [hp] at h
            dsimp only at h
            cases hT : applyPairObs (saturationBudget fuel entries.size) σ Γ.hyps entries t with
            | exhausted => rw [hT] at h; exact absurd h (by simp)
            | invariantFailure =>
                rw [hT] at h
                cases hU : applyPairObs (saturationBudget fuel entries.size) σ Γ.hyps entries u with
                | exhausted => rw [hU] at h; exact absurd h (by simp)
                | invariantFailure => rw [hU] at h; exact absurd h (by simp)
                | ok u' => rw [hU] at h; exact absurd h (by simp)
            | ok t' =>
              rw [hT] at h
              cases hU : applyPairObs (saturationBudget fuel entries.size) σ Γ.hyps entries u with
              | exhausted => rw [hU] at h; exact absurd h (by simp)
              | invariantFailure => rw [hU] at h; exact absurd h (by simp)
              | ok u' =>
                rw [hU] at h
                exact (tmEq_applyPairObs _ _ _ _ hT).symm.trans
                  ((tmEq_canonicalize _).symm.trans
                    ((ihInv _ _ h).trans
                      ((tmEq_canonicalize _).trans (tmEq_applyPairObs _ _ _ _ hU))))
      · intro hyps goal A t u h
        rw [referenceInvRec.eq_def] at h
        dsimp only at h
        split at h
        case h_1 => exact .refl _
        case h_2 n _ => exact TmEq.of_never n.erase _ _
        case h_3 t₁ t₂ u₁ u₂ =>
            obtain ⟨h₁, h₂⟩ := CandidateResult.and_eq_equal h
            simp only [InvTm.erase]
            exact TmEq.pair (ihInv _ _ h₁) (ihInv _ _ h₂)
        case h_4 =>
            rename_i t₁ u₁
            simp only [InvTm.erase]
            exact TmEq.lam
              (InvTm.tmEq_of_castCtx (t := t₁) (u := u₁)
                (Ctx.ofHyps_push hyps _) (ihSat _ _ h))
        case h_5 =>
            rename_i _L _R n _L' _R' m t₁ t₂ u₁ u₂
            split at h
            · exact absurd h (by simp)
            · rename_i hbeq
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hbeq
              obtain ⟨hty, hnm⟩ := NegNeu.eq_of_beq n m hbeq
              injection hty with hL hR
              subst hL; subst hR
              cases eq_of_heq hnm
              split at h
              · split at h
                · dsimp only at h
                  obtain ⟨h₁, h₂⟩ := CandidateResult.and_eq_equal h
                  simp only [InvTm.erase]
                  exact TmEq.case (.refl _)
                    (InvTm.tmEq_of_castCtx (t := t₁) (u := u₁)
                      (Ctx.ofHyps_push hyps _) (ihSat _ _ h₁))
                    (InvTm.tmEq_of_castCtx (t := t₂) (u := u₂)
                      (Ctx.ofHyps_push hyps _) (ihSat _ _ h₂))
                · exact absurd h (by simp)
              · exact absurd h (by simp)
        case h_6 =>
            rename_i _P n _P' m t₁ u₁
            split at h
            · exact absurd h (by simp)
            · rename_i hbeq
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hbeq
              obtain ⟨hty, hnm⟩ := NegNeu.eq_of_beq n m hbeq
              subst hty
              cases eq_of_heq hnm
              split at h
              · dsimp only at h
                simp only [InvTm.erase, FocTm.erase]
                exact TmEq.subst0_congr
                  (InvTm.tmEq_of_castCtx (t := t₁) (u := u₁)
                    (Ctx.ofHyps_push hyps _) (ihSat _ _ h)) (.refl _)
              · exact absurd h (by simp)
        case h_7 =>
            rename_i p q
            split at h
            · rename_i hpq
              obtain rfl := PosNeu.eq_of_beq p q hpq
              exact .refl _
            · exact absurd h (by simp)
        case h_8 =>
            rename_i n m
            split at h
            · rename_i hnm
              cases eq_of_heq (NegNeu.eq_of_beq n m hnm).2
              exact .refl _
            · exact absurd h (by simp)
        case h_9 =>
            rename_i t₁ u₁
            simp only [InvTm.erase, FocTm.erase, SatTm.erase]
            exact ihInv _ _ h
        all_goals
          first
          | exact .refl _
          | (split at h
             · exact tmEq_of_referenceStructEq (by assumption)
             · exact absurd h (by simp))

/-! ### Soundness of the entry points -/

theorem tmEq_of_referenceCompareInv {A : Object sig.nBases}
    {Γ : ReachCtx sig.nBases} {goal : Object sig.nBases}
    {t u : InvTm (Ctx.ofHyps Γ.hyps) A} {fuel : Nat}
    (h : referenceCompareInv Γ goal t u fuel = .equal) :
    TmEq t.erase u.erase :=
  (tmEq_reference fuel).1 _ _ h

theorem tmEq_of_referenceCompareUnder {Γ : Ctx sig} {A : Object sig.nBases}
    {goal : Object sig.nBases} {t u : InvTm Γ A} {fuel : Nat}
    (h : referenceCompareUnder Γ goal t u fuel = .equal) :
    TmEq t.erase u.erase :=
  InvTm.tmEq_of_castCtx (Ctx.ofHyps_toReachCtx Γ) ((tmEq_reference fuel).1 _ _ h)

/-- A successful reference comparison of ordinary terms means they are equal. -/
theorem tmEq_of_referenceCompareTm {Γ : Ctx sig} {A : Object sig.nBases}
    {goal : Object sig.nBases} {t u : Tm Γ A} {fuel : Nat}
    (h : referenceCompareTm goal t u fuel = .equal) : TmEq t u :=
  (focus_tmEq t).symm.trans
    ((tmEq_of_referenceCompareUnder h).trans (focus_tmEq u))

/--
Soundness of the reference comparator: an `.equal` answer is a proof of
definitional equality of the input morphisms.
-/
theorem defEq_of_referenceCompare {X Y : Object sig.nBases}
    {f g : IntrinsicMorphism sig X Y} {fuel : Nat}
    (h : referenceCompare f g fuel = .equal) : IntrinsicDefEq f g :=
  ((interpret_translate f).symm.trans
      ((tmEq_of_referenceCompareTm h).intrinsicDefEq (rootEnv X))).trans
    (interpret_translate g)

end Equality
end Gimbal
