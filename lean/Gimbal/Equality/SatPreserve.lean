/-
  Applying a schedule preserves meaning.

  An observation is applied by abstracting it out of the continuation and then
  either binding it with `letPos` (atoms) or splitting on it (coproducts). The
  first is erasure-preserving on the nose (`erase_letPos_abstr`); the second is
  strong sum η (`TmEq.sum_eta`), which applies because both branches are the
  *same* abstracted body with the fresh binder committed to each injection.
  Everything else in the schedule loop is congruence.
-/

import Gimbal.Equality.Saturation

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Context casts are invisible to erasure -/

theorem InvTm.tmEq_castCtx_left {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (h : Γ = Δ) {t : InvTm Γ A} {u : InvTm Δ A}
    (H : TmEq t.erase (InvTm.castCtx h.symm u).erase) :
    TmEq (InvTm.castCtx h t).erase u.erase := by
  cases h
  exact H

/-! ### Committing a binder to an injection -/

/-- Substituting `inl x` under an inserted binder is the left injection cut. -/
theorem subst0_skip1_inl {Γ : Ctx sig} {L R Z : Object sig.nBases}
    (w : Tm (Γ ▻ .coprod L R) Z) :
    subst0 (rename (Rename.skip1 (B := L)) w) (.inl (.var .here)) =
      subst Subst.injLeft w := by
  rw [subst0, subst_rename]
  refine subst_eq_of_pointwise ?_ w
  intro C x
  cases x <;> rfl

/-- Substituting `inr y` under an inserted binder is the right injection cut. -/
theorem subst0_skip1_inr {Γ : Ctx sig} {L R Z : Object sig.nBases}
    (w : Tm (Γ ▻ .coprod L R) Z) :
    subst0 (rename (Rename.skip1 (B := R)) w) (.inr (.var .here)) =
      subst Subst.injRight w := by
  rw [subst0, subst_rename]
  refine subst_eq_of_pointwise ?_ w
  intro C x
  cases x <;> rfl

/-- The branch built by saturation erases to the corresponding injection cut. -/
theorem tmEq_branch_inl {Γ : Ctx sig} {L R A : Object sig.nBases}
    (body : InvTm (Γ ▻ .coprod L R) A) :
    TmEq (hsubstInv (InvTm.rename Rename.skip1 body) (InvTm.etaInl L R)).erase
      (subst Subst.injLeft body.erase) := by
  refine .trans (tmEq_hsubstInv _ _)
    (.trans (TmEq.subst0_congr (.refl _) (tmEq_etaInl L R)) (.of_eq ?_))
  show subst0 (InvTm.rename (Rename.skip1 (B := L)) body).erase
      (Tm.inl (Tm.var .here)) = _
  rw [InvTm.erase_rename, subst0_skip1_inl]

theorem tmEq_branch_inr {Γ : Ctx sig} {L R A : Object sig.nBases}
    (body : InvTm (Γ ▻ .coprod L R) A) :
    TmEq (hsubstInv (InvTm.rename Rename.skip1 body) (InvTm.etaInr L R)).erase
      (subst Subst.injRight body.erase) := by
  refine .trans (tmEq_hsubstInv _ _)
    (.trans (TmEq.subst0_congr (.refl _) (tmEq_etaInr L R)) (.of_eq ?_))
  show subst0 (InvTm.rename (Rename.skip1 (B := R)) body).erase
      (Tm.inr (Tm.var .here)) = _
  rw [InvTm.erase_rename, subst0_skip1_inr]

/-- Splitting on a coproduct observation preserves meaning. -/
theorem tmEq_case_abstr {Γ : Ctx sig} {L R A : Object sig.nBases}
    (m : NegNeu Γ (.coprod L R)) (cont : InvTm Γ A) :
    TmEq
      (Tm.case m.erase
        (hsubstInv (InvTm.rename Rename.skip1
          (InvTm.abstr .here (NegNeu.weaken m) (InvTm.weaken cont)))
          (InvTm.etaInl L R)).erase
        (hsubstInv (InvTm.rename Rename.skip1
          (InvTm.abstr .here (NegNeu.weaken m) (InvTm.weaken cont)))
          (InvTm.etaInr L R)).erase)
      cont.erase := by
  have hbody := erase_letPos_abstr m cont
  refine .trans (TmEq.case (.refl _) (tmEq_branch_inl _) (tmEq_branch_inr _)) ?_
  exact .trans (TmEq.sum_eta _ _) (.of_eq hbody)

/-! ### Schedule application preserves meaning -/

/--
Applying one observation, and applying a whole schedule, both return a term
with the same meaning as the continuation they were given.
-/
theorem tmEq_applySchedule : ∀ fuel : Nat,
    (∀ {σ : ReachState sig.nBases} (cert : ReachRankCert σ)
        (hyps : Array (Object sig.nBases))
        (P : Object sig.nBases) (nP : NegNeu (Ctx.ofHyps hyps) P)
        (rest : List (PairEntry sig hyps)) {A : Object sig.nBases}
        {cont t' : InvTm (Ctx.ofHyps hyps) A},
        applyObsNeu fuel cert hyps P nP rest cont = .ok t' →
        TmEq t'.erase cont.erase) ∧
    (∀ {σ : ReachState sig.nBases} (cert : ReachRankCert σ)
        (hyps : Array (Object sig.nBases))
        (entries : List (PairEntry sig hyps)) {A : Object sig.nBases}
        {cont t' : InvTm (Ctx.ofHyps hyps) A},
        applyPairObsGo fuel cert hyps entries cont = .ok t' →
        TmEq t'.erase cont.erase)
  | 0 => by
      constructor <;> intros <;> simp_all [applyObsNeu, applyPairObsGo]
  | fuel + 1 => by
      obtain ⟨ihObs, ihGo⟩ := tmEq_applySchedule fuel
      constructor
      · intro σ cert hyps P nP rest A cont t' h
        rw [applyObsNeu] at h
        dsimp only at h
        split at h
        · -- the observation is a proof of `never`: everything is equal
          rename_i hNever
          cases h
          exact TmEq.of_never (NegNeu.cast hNever nP).erase _ _
        · split at h
          · -- coproduct: split on the observation
            split at h
            case h_1 =>
              rename_i _bodyL _bodyR heqL heqR
              cases h
              refine .trans (TmEq.case (.refl _)
                (InvTm.tmEq_castCtx_left _ (ihGo _ _ _ heqL))
                (InvTm.tmEq_castCtx_left _ (ihGo _ _ _ heqR))) ?_
              exact tmEq_case_abstr _ cont
            all_goals exact absurd h (by simp)
          · -- atom: bind the observation with `letPos`
            split at h
            case h_1 =>
              rename_i _body heqB
              cases h
              show TmEq (subst0 (InvTm.castCtx _ _).erase (NegNeu.erase nP)) cont.erase
              refine .trans (TmEq.subst0_congr
                (InvTm.tmEq_castCtx_left _ (ihGo _ _ _ heqB)) (.refl _)) ?_
              exact .of_eq (erase_letPos_abstr nP cont)
            all_goals exact absurd h (by simp)
      · intro σ cert hyps entries A cont t' h
        rw [applyPairObsGo.eq_def] at h
        dsimp only at h
        split at h
        · cases h
          exact .refl _
        · split at h
          · split at h
            · exact absurd h (by simp)
            · split at h
              · exact absurd h (by simp)
              · split at h
                · exact ihObs _ _ _ _ _ h
                · exact absurd h (by simp)
          · exact ihObs _ _ _ _ _ h

/-- Top-level schedule application preserves meaning. -/
theorem tmEq_applyPairObs (fuel : Nat) {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ)
    (hyps : Array (Object sig.nBases)) (entries : Array (PairEntry sig hyps))
    {A : Object sig.nBases} {cont t' : InvTm (Ctx.ofHyps hyps) A}
    (h : applyPairObs fuel cert hyps entries cont = .ok t') :
    TmEq t'.erase cont.erase := by
  rw [applyPairObs] at h
  split at h
  · -- an inconsistent context collapses to the absurd branch
    split at h
    next n _ =>
      cases h
      exact TmEq.of_never n.erase _ _
    next => exact absurd h (by simp)
  · exact (tmEq_applySchedule fuel).2 _ _ _ h

end Equality
end Gimbal
