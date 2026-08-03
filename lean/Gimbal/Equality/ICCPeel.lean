/-
  Soundness of forced-rule peeling for ordered-phase codes (8F/E).

  When `peelCaseOuter` succeeds, the source term is ICC-equivalent to an outer
  `case` on a scrutinee of the requested origin.
-/

import Gimbal.Equality.ICCCanon
import Gimbal.Equality.ICCCode

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Distribution is an ICC step -/

theorem distCaseOut_icc {Γ : Ctx sig} {A B C : Object sig.nBases}
    (n : NegNeu Γ (.coprod A B))
    (t : InvTm (Γ ▻ A) C) (u : InvTm (Γ ▻ B) C) {t' : InvTm Γ C}
    (h : distCaseOut n t u = some t') :
    ICCEq (.case n t u) t' := by
  unfold distCaseOut at h
  split at h
  · next t₁ u₁ t₂ u₂ => cases h; exact .case_pair n t₁ t₂ u₁ u₂
  · next t₁ u₁ => cases h; exact .case_lam n t₁ u₁
  · cases h; exact .case_unit n
  · nomatch h

/-! ### Pointwise rename congruence + id / comp -/

private theorem rename_ext_pointwise_eq {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ τ : Rename sig Γ Δ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B), ρ x = τ x)
    {B : Object sig.nBases} (x : Var (Γ ▻ A) B) :
    Rename.ext ρ x = Rename.ext τ x := by
  cases x <;> first | rfl | exact congrArg Var.there (h _)

mutual
theorem NegNeu.rename_eq_of_pointwise {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ τ : Rename sig Γ Δ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B), ρ x = τ x) :
    (n : NegNeu Γ A) → NegNeu.rename ρ n = NegNeu.rename τ n
  | .var x => congrArg NegNeu.var (h x)
  | .app f a => by
      simp only [NegNeu.rename]
      rw [NegNeu.rename_eq_of_pointwise h f, InvTm.rename_eq_of_pointwise h a]
  | .fst f => by simp only [NegNeu.rename]; rw [NegNeu.rename_eq_of_pointwise h f]
  | .snd f => by simp only [NegNeu.rename]; rw [NegNeu.rename_eq_of_pointwise h f]

theorem PosNeu.rename_eq_of_pointwise {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ τ : Rename sig Γ Δ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B), ρ x = τ x) :
    (p : PosNeu Γ A) → PosNeu.rename ρ p = PosNeu.rename τ p
  | .neu n => by simp only [PosNeu.rename]; rw [NegNeu.rename_eq_of_pointwise h n]
  | .inl p => by simp only [PosNeu.rename]; rw [PosNeu.rename_eq_of_pointwise h p]
  | .inr p => by simp only [PosNeu.rename]; rw [PosNeu.rename_eq_of_pointwise h p]
  | .val t => by simp only [PosNeu.rename]; rw [InvTm.rename_eq_of_pointwise h t]

theorem InvTm.rename_eq_of_pointwise {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ τ : Rename sig Γ Δ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B), ρ x = τ x) :
    (t : InvTm Γ A) → InvTm.rename ρ t = InvTm.rename τ t
  | .unit => rfl
  | .pair t u => by
      simp only [InvTm.rename]
      rw [InvTm.rename_eq_of_pointwise h t, InvTm.rename_eq_of_pointwise h u]
  | .lam t => by
      simp only [InvTm.rename]
      refine congrArg InvTm.lam (InvTm.rename_eq_of_pointwise ?_ t)
      intro B x; exact rename_ext_pointwise_eq h x
  | .case n t u => by
      simp only [InvTm.rename]
      rw [NegNeu.rename_eq_of_pointwise h n]
      refine congrArg₂ (InvTm.case _) ?_ ?_
      · exact InvTm.rename_eq_of_pointwise (fun x => rename_ext_pointwise_eq h x) t
      · exact InvTm.rename_eq_of_pointwise (fun x => rename_ext_pointwise_eq h x) u
  | .abort n => by simp only [InvTm.rename]; rw [NegNeu.rename_eq_of_pointwise h n]
  | .foc f => by simp only [InvTm.rename]; rw [FocTm.rename_eq_of_pointwise h f]

theorem FocTm.rename_eq_of_pointwise {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ τ : Rename sig Γ Δ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B), ρ x = τ x) :
    (f : FocTm Γ A) → FocTm.rename ρ f = FocTm.rename τ f
  | .pos (.done p) => by
      simp only [FocTm.rename, PosIntro.rename]
      exact congrArg FocTm.pos (congrArg PosIntro.done (PosNeu.rename_eq_of_pointwise h p))
  | .neg (.done n) => by
      simp only [FocTm.rename, NegElim.rename]
      exact congrArg FocTm.neg (congrArg NegElim.done (NegNeu.rename_eq_of_pointwise h n))
  | .letPos n t => by
      simp only [FocTm.rename]
      refine congrArg₂ FocTm.letPos (NegNeu.rename_eq_of_pointwise h n) ?_
      exact InvTm.rename_eq_of_pointwise (fun x => rename_ext_pointwise_eq h x) t
  | .sat (.mk s t) => by
      simp only [FocTm.rename, SatTm.rename]
      exact congrArg FocTm.sat (congrArg (SatTm.mk s) (InvTm.rename_eq_of_pointwise h t))
end

mutual
theorem NegNeu.rename_id {Γ : Ctx sig} {A : Object sig.nBases} :
    (n : NegNeu Γ A) → NegNeu.rename (Rename.id (Γ := Γ)) n = n
  | .var _ => rfl
  | .app f a => by simp [NegNeu.rename, NegNeu.rename_id f, InvTm.rename_id a]
  | .fst f => by simp [NegNeu.rename, NegNeu.rename_id f]
  | .snd f => by simp [NegNeu.rename, NegNeu.rename_id f]

theorem PosNeu.rename_id {Γ : Ctx sig} {A : Object sig.nBases} :
    (p : PosNeu Γ A) → PosNeu.rename (Rename.id (Γ := Γ)) p = p
  | .neu n => by simp [PosNeu.rename, NegNeu.rename_id n]
  | .inl p => by simp [PosNeu.rename, PosNeu.rename_id p]
  | .inr p => by simp [PosNeu.rename, PosNeu.rename_id p]
  | .val t => by simp [PosNeu.rename, InvTm.rename_id t]

theorem InvTm.rename_id {Γ : Ctx sig} {A : Object sig.nBases} :
    (t : InvTm Γ A) → InvTm.rename (Rename.id (Γ := Γ)) t = t
  | .unit => rfl
  | .pair t u => by simp [InvTm.rename, InvTm.rename_id t, InvTm.rename_id u]
  | .lam t => by
      simp only [InvTm.rename]
      have h := InvTm.rename_eq_of_pointwise (ρ := Rename.ext (Rename.id (Γ := Γ)))
        (τ := Rename.id (Γ := _)) (fun {B} x => Rename.ext_id_apply x) t
      rw [h, InvTm.rename_id t]
  | .case n t u => by
      simp only [InvTm.rename, NegNeu.rename_id n]
      have ht := InvTm.rename_eq_of_pointwise (ρ := Rename.ext (Rename.id (Γ := Γ)))
        (τ := Rename.id) (fun {B} x => Rename.ext_id_apply x) t
      have hu := InvTm.rename_eq_of_pointwise (ρ := Rename.ext (Rename.id (Γ := Γ)))
        (τ := Rename.id) (fun {B} x => Rename.ext_id_apply x) u
      rw [ht, InvTm.rename_id t, hu, InvTm.rename_id u]
  | .abort n => by simp [InvTm.rename, NegNeu.rename_id n]
  | .foc f => by simp [InvTm.rename, FocTm.rename_id f]

theorem FocTm.rename_id {Γ : Ctx sig} {A : Object sig.nBases} :
    (f : FocTm Γ A) → FocTm.rename (Rename.id (Γ := Γ)) f = f
  | .pos (.done p) => by simp [FocTm.rename, PosIntro.rename, PosNeu.rename_id p]
  | .neg (.done n) => by simp [FocTm.rename, NegElim.rename, NegNeu.rename_id n]
  | .letPos n t => by
      simp only [FocTm.rename, NegNeu.rename_id n]
      have h := InvTm.rename_eq_of_pointwise (ρ := Rename.ext (Rename.id (Γ := Γ)))
        (τ := Rename.id) (fun {B} x => Rename.ext_id_apply x) t
      rw [h, InvTm.rename_id t]
  | .sat (.mk _ t) => by simp [FocTm.rename, SatTm.rename, InvTm.rename_id t]
end

mutual
theorem NegNeu.rename_comp {Γ Δ Ε : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) :
    (n : NegNeu Γ A) →
      NegNeu.rename ρ (NegNeu.rename τ n) = NegNeu.rename (Rename.comp ρ τ) n
  | .var _ => rfl
  | .app f a => by simp [NegNeu.rename, NegNeu.rename_comp ρ τ f, InvTm.rename_comp ρ τ a]
  | .fst f => by simp [NegNeu.rename, NegNeu.rename_comp ρ τ f]
  | .snd f => by simp [NegNeu.rename, NegNeu.rename_comp ρ τ f]

theorem PosNeu.rename_comp {Γ Δ Ε : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) :
    (p : PosNeu Γ A) →
      PosNeu.rename ρ (PosNeu.rename τ p) = PosNeu.rename (Rename.comp ρ τ) p
  | .neu n => by simp [PosNeu.rename, NegNeu.rename_comp ρ τ n]
  | .inl p => by simp [PosNeu.rename, PosNeu.rename_comp ρ τ p]
  | .inr p => by simp [PosNeu.rename, PosNeu.rename_comp ρ τ p]
  | .val t => by simp [PosNeu.rename, InvTm.rename_comp ρ τ t]

theorem InvTm.rename_comp {Γ Δ Ε : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) :
    (t : InvTm Γ A) →
      InvTm.rename ρ (InvTm.rename τ t) = InvTm.rename (Rename.comp ρ τ) t
  | .unit => rfl
  | .pair t u => by simp [InvTm.rename, InvTm.rename_comp ρ τ t, InvTm.rename_comp ρ τ u]
  | .lam t => by
      simp only [InvTm.rename]
      rw [InvTm.rename_comp (Rename.ext ρ) (Rename.ext τ) t]
      refine congrArg InvTm.lam (InvTm.rename_eq_of_pointwise ?_ t)
      intro B x; exact (Rename.ext_comp_apply ρ τ x).symm
  | .case n t u => by
      simp only [InvTm.rename, NegNeu.rename_comp ρ τ n]
      rw [InvTm.rename_comp (Rename.ext ρ) (Rename.ext τ) t,
          InvTm.rename_comp (Rename.ext ρ) (Rename.ext τ) u]
      refine congrArg₂ (InvTm.case _) ?_ ?_
      · exact InvTm.rename_eq_of_pointwise (fun x => (Rename.ext_comp_apply ρ τ x).symm) t
      · exact InvTm.rename_eq_of_pointwise (fun x => (Rename.ext_comp_apply ρ τ x).symm) u
  | .abort n => by simp [InvTm.rename, NegNeu.rename_comp ρ τ n]
  | .foc f => by simp [InvTm.rename, FocTm.rename_comp ρ τ f]

theorem FocTm.rename_comp {Γ Δ Ε : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) :
    (f : FocTm Γ A) →
      FocTm.rename ρ (FocTm.rename τ f) = FocTm.rename (Rename.comp ρ τ) f
  | .pos (.done p) => by simp [FocTm.rename, PosIntro.rename, PosNeu.rename_comp ρ τ p]
  | .neg (.done n) => by simp [FocTm.rename, NegElim.rename, NegNeu.rename_comp ρ τ n]
  | .letPos n t => by
      simp only [FocTm.rename, NegNeu.rename_comp ρ τ n]
      rw [InvTm.rename_comp (Rename.ext ρ) (Rename.ext τ) t]
      refine congrArg₂ FocTm.letPos rfl (InvTm.rename_eq_of_pointwise ?_ t)
      intro B x; exact (Rename.ext_comp_apply ρ τ x).symm
  | .sat (.mk _ t) => by simp [FocTm.rename, SatTm.rename, InvTm.rename_comp ρ τ t]
end

theorem InvTm.rename_exchange_exchange {Γ : Ctx sig} {A B C : Object sig.nBases}
    (t : InvTm (Γ ▻ A ▻ B) C) :
    InvTm.rename (Rename.exchange (A := B) (B := A))
      (InvTm.rename (Rename.exchange (A := A) (B := B)) t) = t := by
  rw [InvTm.rename_comp]
  refine Eq.trans (InvTm.rename_eq_of_pointwise ?_ t) (InvTm.rename_id t)
  intro D x; exact OriginEnv.exchange_exchange_var x


/-! ### Cross-context unweaken for variables -/

theorem NegNeu.eq_weaken_of_beq_unweaken_var {Γ : Ctx sig}
    {A B P : Object sig.nBases}
    (y : Var Γ P) (n₂ : NegNeu (Γ ▻ B) P)
    (hbeq : NegNeu.beq (NegNeu.weaken (B := A) (.var y)) n₂ = true) :
    n₂ = NegNeu.weaken (B := B) (.var y) := by
  cases n₂ with
  | var z =>
      cases z with
      | here =>
          simp [NegNeu.beq, NegNeu.weaken, NegNeu.rename, Rename.weaken,
            Var.toRawIdx, beq_iff_eq] at hbeq
      | there z =>
          simp only [NegNeu.beq, NegNeu.weaken, NegNeu.rename, Rename.weaken,
            Var.toRawIdx, beq_iff_eq, Nat.add_right_cancel_iff] at hbeq
          obtain ⟨_, hxy⟩ := Var.eq_of_toRawIdx y z hbeq
          cases eq_of_heq hxy
          rfl
  | app _ _ => simp [NegNeu.beq, NegNeu.weaken, NegNeu.rename] at hbeq
  | fst _ => simp [NegNeu.beq, NegNeu.weaken, NegNeu.rename] at hbeq
  | snd _ => simp [NegNeu.beq, NegNeu.weaken, NegNeu.rename] at hbeq

theorem NegNeu.var_of_originOfVar {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (n : NegNeu Γ A) {o : Origin sig}
    (h : originOfVar ε n = some o) :
    ∃ x : Var Γ A, n = .var x ∧ ε x = o := by
  cases n with
  | var x =>
      simp only [originOfVar, Option.some.injEq] at h
      exact ⟨x, rfl, h⟩
  | app _ _ | fst _ | snd _ =>
      simp [originOfVar] at h

private theorem peel_result_eq {Γ : Ctx sig} {C : Object sig.nBases}
    {A₁ B₁ A B : Object sig.nBases}
    {n₁ : NegNeu Γ (.coprod A₁ B₁)} {n : NegNeu Γ (.coprod A B)}
    {l₁ : InvTm (Γ ▻ A₁) C} {r₁ : InvTm (Γ ▻ B₁) C}
    {tL : InvTm (Γ ▻ A) C} {tR : InvTm (Γ ▻ B) C}
    (h : (⟨A₁, B₁, n₁, l₁, r₁⟩ :
        (A B : Object sig.nBases) × NegNeu Γ (.coprod A B) ×
          InvTm (Γ ▻ A) C × InvTm (Γ ▻ B) C) =
      ⟨A, B, n, tL, tR⟩) :
    A₁ = A ∧ B₁ = B ∧ HEq n₁ n ∧ HEq l₁ tL ∧ HEq r₁ tR := by
  cases h
  exact ⟨rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

/-! ### Peel soundness -/

theorem peelCaseOuterGo_icc {Γ : Ctx sig} {C : Object sig.nBases}
    (fuel : Nat) (ε : OriginEnv Γ) (o : Origin sig) :
    ∀ (t : InvTm Γ C) {A B : Object sig.nBases} {n : NegNeu Γ (.coprod A B)}
      {tL : InvTm (Γ ▻ A) C} {tR : InvTm (Γ ▻ B) C},
      peelCaseOuterGo fuel ε o t = some ⟨A, B, n, tL, tR⟩ →
        ICCEq t (.case n tL tR) := by
  induction fuel generalizing Γ C ε with
  | zero =>
      intro t A B n tL tR h
      simp [peelCaseOuterGo] at h
  | succ fuel ih =>
      intro t A B n tL tR h
      cases t with
      | unit | abort _ | foc _ => simp [peelCaseOuterGo] at h
      | pair t₁ t₂ =>
          simp only [peelCaseOuterGo] at h
          cases h1 : peelCaseOuterGo fuel ε o t₁ with
          | none => simp [h1] at h
          | some r1 =>
              cases h2 : peelCaseOuterGo fuel ε o t₂ with
              | none => simp [h1, h2] at h
              | some r2 =>
                  simp only [h1, h2] at h
                  rcases r1 with ⟨A₁, B₁, n₁, l₁, r₁⟩
                  rcases r2 with ⟨A₂, B₂, n₂, l₂, r₂⟩
                  split at h
                  · rename_i hA
                    split at h
                    · rename_i hB
                      split at h
                      · rename_i hbeq
                        simp only [Option.some.injEq] at h
                        obtain ⟨rfl, rfl, hn, hl, hr⟩ := peel_result_eq h
                        cases eq_of_heq hn
                        cases eq_of_heq hl
                        cases eq_of_heq hr
                        -- `hA`/`hB` equate the two peel component types; apply before beq.
                        cases hA; cases hB
                        obtain ⟨_, hneq⟩ := NegNeu.eq_of_beq n₁ n₂ hbeq
                        cases eq_of_heq hneq
                        refine .trans (.pair_cong (ih ε t₁ h1) (ih ε t₂ h2)) ?_
                        exact .symm (.case_pair n₁ l₁ r₁ l₂ r₂)
                      · nomatch h
                    · nomatch h
                  · nomatch h
      | lam body =>
          simp only [peelCaseOuterGo] at h
          cases hb : peelCaseOuterGo fuel
              (OriginEnv.weaken (A := _) ε (.dom 0)) o body with
          | none => simp [hb] at h
          | some r =>
              simp only [hb] at h
              rcases r with ⟨A₁, B₁, n₁, tL₁, tR₁⟩
              split at h
              · rename_i n0 hunw
                simp only [Option.some.injEq] at h
                obtain ⟨rfl, rfl, hn, hl, hr⟩ := peel_result_eq h
                cases eq_of_heq hn; cases eq_of_heq hl; cases eq_of_heq hr
                have hn₁ : n₁ = NegNeu.weaken (B := _) n0 :=
                  NegNeu.eq_weaken_of_unweaken? n₁ n0 hunw
                have ihb := ih _ body hb
                have ihb' :
                    ICCEq body (.case (NegNeu.weaken (B := _) n0) tL₁ tR₁) := by
                  convert ihb; exact hn₁.symm
                refine .trans (.lam_cong ihb') ?_
                have hstep :=
                  ICCEq.symm (.case_lam n0
                    (InvTm.rename Rename.exchange tL₁)
                    (InvTm.rename Rename.exchange tR₁))
                convert hstep using 1
                refine congrArg InvTm.lam (congrArg₂
                  (fun a b => InvTm.case (NegNeu.weaken n0) a b) ?_ ?_)
                · exact (InvTm.rename_exchange_exchange tL₁).symm
                · exact (InvTm.rename_exchange_exchange tR₁).symm
              · nomatch h
      | case scr tL₀ tR₀ =>
          cases scr with
          | app _ _ | fst _ | snd _ => simp [peelCaseOuterGo] at h
          | var x =>
              simp only [peelCaseOuterGo] at h
              split at h
              · simp only [Option.some.injEq] at h
                obtain ⟨rfl, rfl, hn, hl, hr⟩ := peel_result_eq h
                cases eq_of_heq hn; cases eq_of_heq hl; cases eq_of_heq hr
                exact .refl _
              · cases hL : peelCaseOuterGo fuel
                    (OriginEnv.weaken (A := _) ε (.split (ε x) false)) o tL₀ with
                | none =>
                    simp only [hL] at h
                    cases hD : distCaseOut (.var x) tL₀ tR₀ with
                    | none => simp [hD] at h
                    | some t' =>
                        simp only [hD] at h
                        exact .trans (distCaseOut_icc (.var x) tL₀ tR₀ hD)
                          (ih ε t' h)
                | some rL =>
                    cases hR : peelCaseOuterGo fuel
                        (OriginEnv.weaken (A := _) ε (.split (ε x) true)) o tR₀ with
                    | none =>
                        simp only [hL, hR] at h
                        cases hD : distCaseOut (.var x) tL₀ tR₀ with
                        | none => simp [hD] at h
                        | some t' =>
                            simp only [hD] at h
                            exact .trans (distCaseOut_icc (.var x) tL₀ tR₀ hD)
                              (ih ε t' h)
                    | some rR =>
                        simp only [hL, hR] at h
                        rcases rL with ⟨C₁, D₁, n₁, a₁, b₁⟩
                        rcases rR with ⟨C₂, D₂, n₂, a₂, b₂⟩
                        split at h
                        · rename_i hC
                          split at h
                          · rename_i hDty
                            split at h
                            · rename_i hbeq
                              split at h
                              · rename_i m hunw
                                split at h
                                · rename_i om horig
                                  split at h
                                  · rename_i _hom
                                    simp only [Option.some.injEq] at h
                                    obtain ⟨rfl, rfl, hn, hl, hr⟩ :=
                                      peel_result_eq h
                                    cases eq_of_heq hn
                                    cases eq_of_heq hl
                                    cases eq_of_heq hr
                                    cases hC; cases hDty
                                    have hn₁ :
                                        n₁ = NegNeu.weaken (B := _) m :=
                                      NegNeu.eq_weaken_of_unweaken? n₁ m hunw
                                    obtain ⟨y, rfl, _⟩ :=
                                      NegNeu.var_of_originOfVar ε m horig
                                    have hn₂ :
                                        n₂ = NegNeu.weaken (B := _) (.var y) :=
                                      NegNeu.eq_weaken_of_beq_unweaken_var
                                        (A := _) y n₂ (by simpa [hn₁] using hbeq)
                                    have ihL := ih _ tL₀ hL
                                    have ihR := ih _ tR₀ hR
                                    have ihL' :
                                        ICCEq tL₀
                                          (.case (NegNeu.weaken (B := _) (.var y))
                                            a₁ b₁) := by
                                      simpa [hn₁] using ihL
                                    have ihR' :
                                        ICCEq tR₀
                                          (.case (NegNeu.weaken (B := _) (.var y))
                                            a₂ b₂) := by
                                      simpa [hn₂] using ihR
                                    exact .trans (.case_cong ihL' ihR')
                                      (.case_case (.var x) (.var y) a₁ b₁ a₂ b₂)
                                  · nomatch h
                                · nomatch h
                              · nomatch h
                            · nomatch h
                          · nomatch h
                        · nomatch h

theorem peelCaseOuter_icc {Γ : Ctx sig} {C : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) (t : InvTm Γ C)
    {A B : Object sig.nBases} {n : NegNeu Γ (.coprod A B)}
    {tL : InvTm (Γ ▻ A) C} {tR : InvTm (Γ ▻ B) C}
    (h : peelCaseOuter ε o t = some ⟨A, B, n, tL, tR⟩) :
    ICCEq t (.case n tL tR) :=
  peelCaseOuterGo_icc _ ε o t h

/-! ### Peel agreement for ICC `case_pair` -/

theorem NegNeu.beq_var_self {Γ : Ctx sig} {A : Object sig.nBases} (x : Var Γ A) :
    NegNeu.beq (.var x) (.var x) = true := by
  simp [NegNeu.beq]

theorem peelCaseOuterGo_case_var_hit {Γ : Ctx sig} {A B C : Object sig.nBases}
    (fuel : Nat) (ε : OriginEnv Γ) (o : Origin sig)
    (x : Var Γ (.coprod A B))
    (tL : InvTm (Γ ▻ A) C) (tR : InvTm (Γ ▻ B) C)
    (hit : ε x = o) :
    peelCaseOuterGo (fuel + 1) ε o (.case (.var x) tL tR) =
      some ⟨A, B, .var x, tL, tR⟩ := by
  simp [peelCaseOuterGo, hit]

private theorem size_case_var_pos {Γ : Ctx sig} {A B C : Object sig.nBases}
    (x : Var Γ (.coprod A B)) (tL : InvTm (Γ ▻ A) C) (tR : InvTm (Γ ▻ B) C) :
    0 < InvTm.size (.case (.var x) tL tR : InvTm Γ C) := by
  simp only [InvTm.size]; omega

theorem peelCaseOuter_case_var_hit {Γ : Ctx sig} {A B C : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig)
    (x : Var Γ (.coprod A B))
    (tL : InvTm (Γ ▻ A) C) (tR : InvTm (Γ ▻ B) C)
    (hit : ε x = o) :
    peelCaseOuter ε o (.case (.var x) tL tR) =
      some ⟨A, B, .var x, tL, tR⟩ := by
  unfold peelCaseOuter
  have hpos := size_case_var_pos x tL tR
  obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  simpa [hm] using peelCaseOuterGo_case_var_hit fuel ε o x tL tR hit

theorem peelCaseOuterGo_pair_cases {Γ : Ctx sig} {A B C D : Object sig.nBases}
    (fuel : Nat) (ε : OriginEnv Γ) (o : Origin sig)
    (x : Var Γ (.coprod A B))
    (t₁ : InvTm (Γ ▻ A) C) (t₂ : InvTm (Γ ▻ B) C)
    (u₁ : InvTm (Γ ▻ A) D) (u₂ : InvTm (Γ ▻ B) D)
    (hit : ε x = o)
    (hLsz : InvTm.size (.case (.var x) t₁ t₂) ≤ fuel)
    (hRsz : InvTm.size (.case (.var x) u₁ u₂) ≤ fuel) :
    peelCaseOuterGo (fuel + 1) ε o
        (.pair (.case (.var x) t₁ t₂) (.case (.var x) u₁ u₂)) =
      some ⟨A, B, .var x, .pair t₁ u₁, .pair t₂ u₂⟩ := by
  have hL :
      peelCaseOuterGo fuel ε o (.case (.var x) t₁ t₂) =
        some ⟨A, B, .var x, t₁, t₂⟩ := by
    have hpos := size_case_var_pos x t₁ t₂
    have hfuel_pos : 0 < fuel := Nat.lt_of_lt_of_le hpos hLsz
    obtain ⟨fuel', hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hfuel_pos)
    subst hm
    exact peelCaseOuterGo_case_var_hit fuel' ε o x t₁ t₂ hit
  have hR :
      peelCaseOuterGo fuel ε o (.case (.var x) u₁ u₂) =
        some ⟨A, B, .var x, u₁, u₂⟩ := by
    have hpos := size_case_var_pos x u₁ u₂
    have hfuel_pos : 0 < fuel := Nat.lt_of_lt_of_le hpos hRsz
    obtain ⟨fuel', hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hfuel_pos)
    subst hm
    exact peelCaseOuterGo_case_var_hit fuel' ε o x u₁ u₂ hit
  simp [peelCaseOuterGo, hL, hR, NegNeu.beq_var_self x]

theorem peelCaseOuter_pair_cases {Γ : Ctx sig} {A B C D : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig)
    (x : Var Γ (.coprod A B))
    (t₁ : InvTm (Γ ▻ A) C) (t₂ : InvTm (Γ ▻ B) C)
    (u₁ : InvTm (Γ ▻ A) D) (u₂ : InvTm (Γ ▻ B) D)
    (hit : ε x = o) :
    peelCaseOuter ε o
        (.pair (.case (.var x) t₁ t₂) (.case (.var x) u₁ u₂)) =
      some ⟨A, B, .var x, .pair t₁ u₁, .pair t₂ u₂⟩ := by
  unfold peelCaseOuter
  set t :=
    (.pair (.case (.var x) t₁ t₂) (.case (.var x) u₁ u₂) : InvTm Γ (.prod C D))
  have hsz :
      InvTm.size t =
        InvTm.size (.case (.var x) t₁ t₂) +
          InvTm.size (.case (.var x) u₁ u₂) + 1 := by
    simp [t, InvTm.size]
  have hpos : 0 < InvTm.size t := by
    have := size_case_var_pos x t₁ t₂
    omega
  obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  have hLsz : InvTm.size (.case (.var x) t₁ t₂) ≤ fuel := by
    have := size_case_var_pos x u₁ u₂
    omega
  have hRsz : InvTm.size (.case (.var x) u₁ u₂) ≤ fuel := by
    have := size_case_var_pos x t₁ t₂
    omega
  simpa [t, hm] using
    peelCaseOuterGo_pair_cases fuel ε o x t₁ t₂ u₁ u₂ hit hLsz hRsz

/-- Both sides of `ICCEq.case_pair` peel to the same outer case. -/
theorem peelCaseOuter_case_pair {Γ : Ctx sig} {A B C D : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig)
    (x : Var Γ (.coprod A B))
    (t₁ : InvTm (Γ ▻ A) C) (t₂ : InvTm (Γ ▻ B) C)
    (u₁ : InvTm (Γ ▻ A) D) (u₂ : InvTm (Γ ▻ B) D)
    (hit : ε x = o) :
    peelCaseOuter ε o (.case (.var x) (.pair t₁ u₁) (.pair t₂ u₂)) =
      peelCaseOuter ε o (.pair (.case (.var x) t₁ t₂) (.case (.var x) u₁ u₂)) ∧
    peelCaseOuter ε o (.case (.var x) (.pair t₁ u₁) (.pair t₂ u₂)) =
      some ⟨A, B, .var x, .pair t₁ u₁, .pair t₂ u₂⟩ :=
  ⟨by rw [peelCaseOuter_case_var_hit ε o x (.pair t₁ u₁) (.pair t₂ u₂) hit,
          peelCaseOuter_pair_cases ε o x t₁ t₂ u₁ u₂ hit],
    peelCaseOuter_case_var_hit ε o x (.pair t₁ u₁) (.pair t₂ u₂) hit⟩

end Equality
end Gimbal
