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
      | unit | abort _ => simp [peelCaseOuterGo] at h
      | foc f =>
          cases f with
          | pos _ | neg _ => simp [peelCaseOuterGo] at h
          | sat s =>
              cases s with
              | mk _sched body =>
                  simp only [peelCaseOuterGo] at h
                  exact .trans (.sat_body _sched body) (ih ε body h)
          | letPos n body =>
              simp only [peelCaseOuterGo] at h
              cases hb : peelCaseOuterGo fuel
                  (OriginEnv.weaken (A := _) ε (.dom 0)) o body with
              | none => simp [hb] at h
              | some r =>
                  simp only [hb] at h
                  rcases r with ⟨A₁, B₁, n₁, tL₁, tR₁⟩
                  split at h
                  · rename_i m0 hunw
                    simp only [Option.some.injEq] at h
                    obtain ⟨rfl, rfl, hn, hl, hr⟩ := peel_result_eq h
                    cases eq_of_heq hn; cases eq_of_heq hl; cases eq_of_heq hr
                    have hn₁ : n₁ = NegNeu.weaken (B := _) m0 :=
                      NegNeu.eq_weaken_of_unweaken? n₁ m0 hunw
                    have ihb := ih _ body hb
                    have ihb' :
                        ICCEq body (.case (NegNeu.weaken (B := _) m0) tL₁ tR₁) := by
                      convert ihb; exact hn₁.symm
                    exact .trans (.foc_cong (.letPos_cong ihb'))
                      (.case_letPos m0 n tL₁ tR₁)
                  · nomatch h
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

/-! ### Peel size / budget accounts (for encode fuel adequacy) -/

private theorem InvTm.size_cast_eq {Γ : Ctx sig} {A B : Object sig.nBases}
    (h : A = B) (t : InvTm Γ A) :
    InvTm.size (h ▸ t) = InvTm.size t := by
  cases h; rfl

private theorem InvTm.posPushBudget_cast_eq {Γ : Ctx sig} {A B : Object sig.nBases}
    (h : A = B) (t : InvTm Γ A) :
    InvTm.posPushBudget (h ▸ t) = InvTm.posPushBudget t := by
  cases h; rfl

/--
Successful peel produces branches strictly smaller than the source, with budgets
bounded by the source. Used to show left-coprod branch fuel is below the parent
`encodeFuel`, including redistribution / exchange paths.
-/
theorem peelCaseOuterGo_size_budget {Γ : Ctx sig} {C : Object sig.nBases}
    (fuel : Nat) (ε : OriginEnv Γ) (o : Origin sig) :
    ∀ (t : InvTm Γ C) {A B : Object sig.nBases} {n : NegNeu Γ (.coprod A B)}
      {tL : InvTm (Γ ▻ A) C} {tR : InvTm (Γ ▻ B) C},
      peelCaseOuterGo fuel ε o t = some ⟨A, B, n, tL, tR⟩ →
        InvTm.size tL < InvTm.size t ∧
        InvTm.size tR < InvTm.size t ∧
        InvTm.posPushBudget tL ≤ InvTm.posPushBudget t ∧
        InvTm.posPushBudget tR ≤ InvTm.posPushBudget t := by
  induction fuel using Nat.strongRecOn generalizing Γ C ε with
  | ind fuel ih =>
      intro t A B n tL tR h
      cases fuel with
      | zero => simp [peelCaseOuterGo] at h
      | succ fuel =>
          cases t with
          | unit | abort _ => simp [peelCaseOuterGo] at h
          | foc f =>
              cases f with
              | pos _ | neg _ => simp [peelCaseOuterGo] at h
              | sat s =>
                  cases s with
                  | mk _sched body =>
                      simp only [peelCaseOuterGo] at h
                      have ihb := ih fuel (Nat.lt_succ_self _) ε body h
                      simp only [InvTm.size, FocTm.size, InvTm.posPushBudget,
                        FocTm.posPushBudget] at ihb ⊢
                      omega
              | letPos n body =>
                  simp only [peelCaseOuterGo] at h
                  cases hb : peelCaseOuterGo fuel
                      (OriginEnv.weaken (A := _) ε (.dom 0)) o body with
                  | none => simp [hb] at h
                  | some r =>
                      simp only [hb] at h
                      rcases r with ⟨A₁, B₁, n₁, tL₁, tR₁⟩
                      split at h
                      · rename_i m0 hunw
                        simp only [Option.some.injEq] at h
                        obtain ⟨rfl, rfl, hn, hl, hr⟩ := peel_result_eq h
                        cases eq_of_heq hn; cases eq_of_heq hl; cases eq_of_heq hr
                        have ihb := ih fuel (Nat.lt_succ_self _) _ body hb
                        have hnsz : NegNeu.size (NegNeu.weaken (B := A₁) n) =
                            NegNeu.size n :=
                          NegNeu.size_rename _ n
                        have hnsz' : NegNeu.size (NegNeu.weaken (B := B₁) n) =
                            NegNeu.size n :=
                          NegNeu.size_rename _ n
                        simp only [InvTm.size, FocTm.size, InvTm.size_rename,
                          InvTm.posPushBudget, FocTm.posPushBudget,
                          InvTm.posPushBudget_rename, hnsz, hnsz'] at ihb ⊢
                        omega
                      · nomatch h
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
                            cases hA; cases hB
                            obtain ⟨_, hneq⟩ := NegNeu.eq_of_beq n₁ n₂ hbeq
                            cases eq_of_heq hneq
                            have ih1 := ih fuel (Nat.lt_succ_self _) ε t₁ h1
                            have ih2 := ih fuel (Nat.lt_succ_self _) ε t₂ h2
                            simp only [InvTm.size, InvTm.posPushBudget] at ih1 ih2 ⊢
                            omega
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
                    have ihb := ih fuel (Nat.lt_succ_self _) _ body hb
                    simp only [InvTm.size, InvTm.size_rename, InvTm.posPushBudget,
                      InvTm.posPushBudget_rename] at ihb ⊢
                    omega
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
                    simp only [InvTm.size, NegNeu.size, InvTm.posPushBudget]
                    omega
                  · cases hL : peelCaseOuterGo fuel
                        (OriginEnv.weaken (A := _) ε (.split (ε x) false)) o tL₀ with
                    | none =>
                        simp only [hL] at h
                        cases hD : distCaseOut (.var x) tL₀ tR₀ with
                        | none => simp [hD] at h
                        | some t' =>
                            simp only [hD] at h
                            cases tL₀ with
                            | pair t₁ u₁ =>
                                cases tR₀ with
                                | pair t₂ u₂ =>
                                    unfold distCaseOut at hD; cases hD
                                    -- Dist pair peel uses `fuel`; unfold when `fuel = succ`.
                                    cases fuel with
                                    | zero => simp [peelCaseOuterGo] at h
                                    | succ fuel =>
                                        simp only [peelCaseOuterGo] at h
                                        cases h1 : peelCaseOuterGo fuel ε o
                                            (.case (.var x) t₁ t₂) with
                                        | none => simp [h1] at h
                                        | some r1 =>
                                            cases h2 : peelCaseOuterGo fuel ε o
                                                (.case (.var x) u₁ u₂) with
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
                                                      obtain ⟨rfl, rfl, hn, hl, hr⟩ :=
                                                        peel_result_eq h
                                                      cases eq_of_heq hn
                                                      cases eq_of_heq hl
                                                      cases eq_of_heq hr
                                                      cases hA; cases hB
                                                      obtain ⟨_, hneq⟩ :=
                                                        NegNeu.eq_of_beq n₁ n₂ hbeq
                                                      cases eq_of_heq hneq
                                                      have ih1 :=
                                                        ih fuel (by omega) ε _ h1
                                                      have ih2 :=
                                                        ih fuel (by omega) ε _ h2
                                                      simp only [InvTm.size,
                                                        InvTm.posPushBudget, NegNeu.size]
                                                        at ih1 ih2 ⊢
                                                      omega
                                                    · nomatch h
                                                  · nomatch h
                                                · nomatch h
                                | abort _ | foc _ | case _ _ _ =>
                                    unfold distCaseOut at hD; nomatch hD
                            | lam t₁ =>
                                cases tR₀ with
                                | lam u₁ =>
                                    unfold distCaseOut at hD; cases hD
                                    have ih' :=
                                      ih fuel (Nat.lt_succ_self _) ε _ h
                                    simp only [InvTm.size, NegNeu.size, NegNeu.weaken,
                                      NegNeu.rename, InvTm.size_rename,
                                      InvTm.posPushBudget, InvTm.posPushBudget_rename]
                                      at ih' ⊢
                                    omega
                                | abort _ | foc _ | case _ _ _ =>
                                    unfold distCaseOut at hD; nomatch hD
                            | unit =>
                                cases tR₀ with
                                | unit =>
                                    unfold distCaseOut at hD; cases hD
                                    cases fuel <;> simp [peelCaseOuterGo] at h
                                | abort _ | foc _ | case _ _ _ =>
                                    unfold distCaseOut at hD; nomatch hD
                            | abort _ | foc _ | case _ _ _ =>
                                unfold distCaseOut at hD; nomatch hD
                    | some rL =>
                        cases hR : peelCaseOuterGo fuel
                            (OriginEnv.weaken (A := _) ε (.split (ε x) true)) o tR₀ with
                        | none =>
                            simp only [hL, hR] at h
                            cases hD : distCaseOut (.var x) tL₀ tR₀ with
                            | none => simp [hD] at h
                            | some t' =>
                                simp only [hD] at h
                                cases tL₀ with
                                | pair t₁ u₁ =>
                                    cases tR₀ with
                                    | pair t₂ u₂ =>
                                        unfold distCaseOut at hD; cases hD
                                        cases fuel with
                                        | zero => simp [peelCaseOuterGo] at h
                                        | succ fuel =>
                                            simp only [peelCaseOuterGo] at h
                                            cases h1 : peelCaseOuterGo fuel ε o
                                                (.case (.var x) t₁ t₂) with
                                            | none => simp [h1] at h
                                            | some r1 =>
                                                cases h2 : peelCaseOuterGo fuel ε o
                                                    (.case (.var x) u₁ u₂) with
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
                                                          obtain ⟨rfl, rfl, hn, hl, hr⟩ :=
                                                            peel_result_eq h
                                                          cases eq_of_heq hn
                                                          cases eq_of_heq hl
                                                          cases eq_of_heq hr
                                                          cases hA; cases hB
                                                          obtain ⟨_, hneq⟩ :=
                                                            NegNeu.eq_of_beq n₁ n₂ hbeq
                                                          cases eq_of_heq hneq
                                                          have ih1 :=
                                                            ih fuel (by omega) ε _ h1
                                                          have ih2 :=
                                                            ih fuel (by omega) ε _ h2
                                                          simp only [InvTm.size,
                                                            InvTm.posPushBudget, NegNeu.size]
                                                            at ih1 ih2 ⊢
                                                          omega
                                                        · nomatch h
                                                      · nomatch h
                                                    · nomatch h
                                    | abort _ | foc _ | case _ _ _ =>
                                        unfold distCaseOut at hD; nomatch hD
                                | lam t₁ =>
                                    cases tR₀ with
                                    | lam u₁ =>
                                        unfold distCaseOut at hD; cases hD
                                        have ih' :=
                                          ih fuel (Nat.lt_succ_self _) ε _ h
                                        simp only [InvTm.size, NegNeu.size, NegNeu.weaken,
                                          NegNeu.rename, InvTm.size_rename,
                                          InvTm.posPushBudget, InvTm.posPushBudget_rename]
                                          at ih' ⊢
                                        omega
                                    | abort _ | foc _ | case _ _ _ =>
                                        unfold distCaseOut at hD; nomatch hD
                                | unit =>
                                    cases tR₀ with
                                    | unit =>
                                        unfold distCaseOut at hD; cases hD
                                        cases fuel <;> simp [peelCaseOuterGo] at h
                                    | abort _ | foc _ | case _ _ _ =>
                                        unfold distCaseOut at hD; nomatch hD
                                | abort _ | foc _ | case _ _ _ =>
                                    unfold distCaseOut at hD; nomatch hD
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
                                        have ihL :=
                                          ih fuel (Nat.lt_succ_self _) _ tL₀ hL
                                        have ihR :=
                                          ih fuel (Nat.lt_succ_self _) _ tR₀ hR
                                        simp only [InvTm.size, NegNeu.size,
                                          NegNeu.weaken, NegNeu.rename,
                                          InvTm.size_rename, InvTm.size_cast_eq,
                                          InvTm.posPushBudget,
                                          InvTm.posPushBudget_rename,
                                          InvTm.posPushBudget_cast_eq] at ihL ihR ⊢
                                        omega
                                      · nomatch h
                                    · nomatch h
                                  · nomatch h
                                · nomatch h
                              · nomatch h
                            · nomatch h

theorem peelCaseOuter_size_budget {Γ : Ctx sig} {C : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) (t : InvTm Γ C)
    {A B : Object sig.nBases} {n : NegNeu Γ (.coprod A B)}
    {tL : InvTm (Γ ▻ A) C} {tR : InvTm (Γ ▻ B) C}
    (h : peelCaseOuter ε o t = some ⟨A, B, n, tL, tR⟩) :
    InvTm.size tL < InvTm.size t ∧
    InvTm.size tR < InvTm.size t ∧
    InvTm.posPushBudget tL ≤ InvTm.posPushBudget t ∧
    InvTm.posPushBudget tR ≤ InvTm.posPushBudget t :=
  peelCaseOuterGo_size_budget _ ε o t h

/--
Left-coprod branch fuel is strictly below the parent after a successful peel.
-/
theorem encodeFuelBranches_lt_of_peel {Γ : Ctx sig} {C L R : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig))
    (hty : e.ty = .coprod L R)
    (ε : OriginEnv Γ) (t : InvTm Γ C)
    (n : NegNeu Γ (.coprod L R))
    (tL : InvTm (Γ ▻ L) C) (tR : InvTm (Γ ▻ R) C)
    (h : peelCaseOuter ε e.origin t = some ⟨L, R, n, tL, tR⟩) :
    encodeFuelBranches (e :: ws) e tL tR < encodeFuel (e :: ws) t := by
  obtain ⟨hsL, hsR, hbL, hbR⟩ := peelCaseOuter_size_budget ε e.origin t h
  have hpushL := worklistWeight_pushPos_le ws (.split e.origin false) L
  have hpushR := worklistWeight_pushPos_le ws (.split e.origin true) R
  have hRpos := objectWeight_pos R
  have hLpos := objectWeight_pos L
  have hLfuel :
      encodeFuel (pushPos ws (.split e.origin false) L) tL <
        encodeFuel (e :: ws) t := by
    simp only [encodeFuel, encodeMeasure, worklistWeight_cons, hty, objectWeight]
      at hsL hbL hpushL ⊢
    omega
  have hRfuel :
      encodeFuel (pushPos ws (.split e.origin true) R) tR <
        encodeFuel (e :: ws) t := by
    simp only [encodeFuel, encodeMeasure, worklistWeight_cons, hty, objectWeight]
      at hsR hbR hpushR ⊢
    omega
  simp only [encodeFuelBranches, List.tail_cons]
  exact (Nat.max_lt).mpr ⟨hLfuel, hRfuel⟩

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

/-! ### Peel agreement for ICC `case_lam` -/

theorem NegNeu.unweaken_weaken_var {Γ : Ctx sig} {Arg A : Object sig.nBases}
    (x : Var Γ A) :
    NegNeu.unweaken? (B := Arg) (NegNeu.weaken (.var x)) = some (.var x) := by
  simp [NegNeu.unweaken?, NegNeu.weaken, NegNeu.rename, Rename.weaken]

private theorem peelCaseOuterGo_lam_eq {Γ : Ctx sig} {Arg Ret : Object sig.nBases}
    (fuel : Nat) (ε : OriginEnv Γ) (o : Origin sig)
    (body : InvTm (Γ ▻ Arg) Ret) :
    peelCaseOuterGo (fuel + 1) ε o (.lam body) =
      match peelCaseOuterGo fuel (OriginEnv.weaken (A := Arg) ε (.dom 0)) o body with
      | some ⟨A, B, n, tL, tR⟩ =>
          match NegNeu.unweaken? n with
          | some n0 =>
              some ⟨A, B, n0,
                .lam (InvTm.rename Rename.exchange tL),
                .lam (InvTm.rename Rename.exchange tR)⟩
          | none => none
      | none => none :=
  rfl

theorem peelCaseOuterGo_lam_cases {Γ : Ctx sig} {A B Arg Ret : Object sig.nBases}
    (fuel : Nat) (ε : OriginEnv Γ) (o : Origin sig)
    (x : Var Γ (.coprod A B))
    (t : InvTm (Γ ▻ A ▻ Arg) Ret) (u : InvTm (Γ ▻ B ▻ Arg) Ret)
    (hit : ε x = o)
    (hfuel : InvTm.size (.case (NegNeu.weaken (B := Arg) (.var x))
        (InvTm.rename Rename.exchange t)
        (InvTm.rename Rename.exchange u)) ≤ fuel) :
    peelCaseOuterGo (fuel + 1) ε o
        (.lam (.case (NegNeu.weaken (B := Arg) (.var x))
          (InvTm.rename Rename.exchange t)
          (InvTm.rename Rename.exchange u))) =
      some ⟨A, B, .var x,
        .lam (InvTm.rename Rename.exchange (InvTm.rename Rename.exchange t)),
        .lam (InvTm.rename Rename.exchange (InvTm.rename Rename.exchange u))⟩ := by
  have hit' : OriginEnv.weaken (A := Arg) ε (.dom 0) (.there x) = o := by
    simpa [OriginEnv.weaken, OriginEnv.snoc] using hit
  have hpos : 0 < InvTm.size
      (.case (NegNeu.weaken (B := Arg) (.var x))
        (InvTm.rename Rename.exchange t)
        (InvTm.rename Rename.exchange u) : InvTm (Γ ▻ Arg) Ret) := by
    simp only [InvTm.size]; omega
  have hfuel_pos : 0 < fuel := Nat.lt_of_lt_of_le hpos hfuel
  obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hfuel_pos)
  have hbody :
      peelCaseOuterGo (fuel' + 1) (OriginEnv.weaken (A := Arg) ε (.dom 0)) o
          (.case (.var (.there x))
            (InvTm.rename Rename.exchange t)
            (InvTm.rename Rename.exchange u)) =
        some ⟨A, B, .var (.there x),
          InvTm.rename Rename.exchange t,
          InvTm.rename Rename.exchange u⟩ :=
    peelCaseOuterGo_case_var_hit fuel'
      (OriginEnv.weaken (A := Arg) ε (.dom 0)) o (.there x)
      (InvTm.rename Rename.exchange t) (InvTm.rename Rename.exchange u) hit'
  rw [peelCaseOuterGo_lam_eq]
  have hbody' :
      peelCaseOuterGo (fuel' + 1) (OriginEnv.weaken (A := Arg) ε (.dom 0)) o
          (.case (NegNeu.weaken (B := Arg) (.var x))
            (InvTm.rename Rename.exchange t)
            (InvTm.rename Rename.exchange u)) =
        some ⟨A, B, .var (.there x),
          InvTm.rename Rename.exchange t,
          InvTm.rename Rename.exchange u⟩ := by
    simpa [NegNeu.weaken, NegNeu.rename, Rename.weaken] using hbody
  rw [hbody']
  simp [NegNeu.unweaken?]

theorem peelCaseOuter_lam_cases {Γ : Ctx sig} {A B Arg Ret : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig)
    (x : Var Γ (.coprod A B))
    (t : InvTm (Γ ▻ A ▻ Arg) Ret) (u : InvTm (Γ ▻ B ▻ Arg) Ret)
    (hit : ε x = o) :
    peelCaseOuter ε o
        (.lam (.case (NegNeu.weaken (B := Arg) (.var x))
          (InvTm.rename Rename.exchange t)
          (InvTm.rename Rename.exchange u))) =
      some ⟨A, B, .var x, .lam t, .lam u⟩ := by
  unfold peelCaseOuter
  set body :=
    (.case (NegNeu.weaken (B := Arg) (.var x))
      (InvTm.rename Rename.exchange t)
      (InvTm.rename Rename.exchange u) : InvTm (Γ ▻ Arg) Ret)
  set tm := (.lam body : InvTm Γ (.exp Arg Ret))
  have hsz : InvTm.size tm = InvTm.size body + 1 := by simp [tm, body, InvTm.size]
  have hpos : 0 < InvTm.size tm := by
    have : 0 < InvTm.size body := by simp only [body, InvTm.size]; omega
    omega
  obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  have hfuel : InvTm.size body ≤ fuel := by omega
  have hgo := peelCaseOuterGo_lam_cases fuel ε o x t u hit (by simpa [body] using hfuel)
  have ht : InvTm.rename Rename.exchange (InvTm.rename Rename.exchange t) = t :=
    InvTm.rename_exchange_exchange t
  have hu : InvTm.rename Rename.exchange (InvTm.rename Rename.exchange u) = u :=
    InvTm.rename_exchange_exchange u
  simpa [tm, body, hm, ht, hu] using hgo

/-- Both sides of `ICCEq.case_lam` peel to the same outer case. -/
theorem peelCaseOuter_case_lam {Γ : Ctx sig} {A B Arg Ret : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig)
    (x : Var Γ (.coprod A B))
    (t : InvTm (Γ ▻ A ▻ Arg) Ret) (u : InvTm (Γ ▻ B ▻ Arg) Ret)
    (hit : ε x = o) :
    peelCaseOuter ε o (.case (.var x) (.lam t) (.lam u)) =
      peelCaseOuter ε o
        (.lam (.case (NegNeu.weaken (B := Arg) (.var x))
          (InvTm.rename Rename.exchange t)
          (InvTm.rename Rename.exchange u))) ∧
    peelCaseOuter ε o (.case (.var x) (.lam t) (.lam u)) =
      some ⟨A, B, .var x, .lam t, .lam u⟩ :=
  ⟨by rw [peelCaseOuter_case_var_hit ε o x (.lam t) (.lam u) hit,
          peelCaseOuter_lam_cases ε o x t u hit],
    peelCaseOuter_case_var_hit ε o x (.lam t) (.lam u) hit⟩

/-! ### Peel agreement for ICC `case_case` -/

theorem NegNeu.beq_weaken_var_self {Γ : Ctx sig} {A B : Object sig.nBases}
    (x : Var Γ A) :
    NegNeu.beq (NegNeu.weaken (B := B) (.var x))
      (NegNeu.weaken (B := B) (.var x)) = true := by
  simp [NegNeu.beq, NegNeu.weaken, NegNeu.rename, Rename.weaken]

/-- Weakening the same variable under different binders preserves raw-index equality. -/
theorem NegNeu.beq_weaken_var_cross {Γ : Ctx sig} {P L R : Object sig.nBases}
    (x : Var Γ P) :
    NegNeu.beq (NegNeu.weaken (B := L) (.var x))
      (NegNeu.weaken (B := R) (.var x)) = true := by
  simp [NegNeu.beq, NegNeu.weaken, NegNeu.rename, Rename.weaken, Var.toRawIdx]

theorem originOfVar_var {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (x : Var Γ A) :
    originOfVar ε (.var x) = some (ε x) := rfl

/--
When the outer scrutinee misses the forced origin but both branches expose the
same weakened variable of that origin, peel reconstructs the exchanged outer case.
-/
theorem peelCaseOuterGo_case_miss_var {Γ : Ctx sig}
    {A B C D E : Object sig.nBases}
    (fuel : Nat) (ε : OriginEnv Γ) (o : Origin sig)
    (xt : Var Γ (.coprod C D)) (xs : Var Γ (.coprod A B))
    (a₁ : InvTm (Γ ▻ C ▻ A) E) (b₁ : InvTm (Γ ▻ C ▻ B) E)
    (a₂ : InvTm (Γ ▻ D ▻ A) E) (b₂ : InvTm (Γ ▻ D ▻ B) E)
    (miss : (ε xt == o) = false) (hit : ε xs = o)
    (hL :
      peelCaseOuterGo fuel
          (OriginEnv.weaken (A := C) ε (.split (ε xt) false)) o
          (.case (NegNeu.weaken (B := C) (.var xs)) a₁ b₁) =
        some ⟨A, B, NegNeu.weaken (B := C) (.var xs), a₁, b₁⟩)
    (hR :
      peelCaseOuterGo fuel
          (OriginEnv.weaken (A := D) ε (.split (ε xt) true)) o
          (.case (NegNeu.weaken (B := D) (.var xs)) a₂ b₂) =
        some ⟨A, B, NegNeu.weaken (B := D) (.var xs), a₂, b₂⟩) :
    peelCaseOuterGo (fuel + 1) ε o
        (.case (.var xt)
          (.case (NegNeu.weaken (B := C) (.var xs)) a₁ b₁)
          (.case (NegNeu.weaken (B := D) (.var xs)) a₂ b₂)) =
      some ⟨A, B, .var xs,
        .case (NegNeu.weaken (B := A) (.var xt))
          (InvTm.rename Rename.exchange a₁)
          (InvTm.rename Rename.exchange a₂),
        .case (NegNeu.weaken (B := B) (.var xt))
          (InvTm.rename Rename.exchange b₁)
          (InvTm.rename Rename.exchange b₂)⟩ := by
  simp only [peelCaseOuterGo, miss, Bool.false_eq_true, ↓reduceIte, hL, hR]
  simp [NegNeu.beq_weaken_var_cross (L := C) (R := D) xs,
    NegNeu.unweaken_weaken_var (Arg := C) xs, originOfVar_var, hit]

/-- Both sides of `ICCEq.case_case` peel to the same outer case on `xs`. -/
theorem peelCaseOuter_case_case {Γ : Ctx sig}
    {A B C D E : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig)
    (xs : Var Γ (.coprod A B)) (xt : Var Γ (.coprod C D))
    (t₁ : InvTm (Γ ▻ A ▻ C) E) (t₂ : InvTm (Γ ▻ A ▻ D) E)
    (u₁ : InvTm (Γ ▻ B ▻ C) E) (u₂ : InvTm (Γ ▻ B ▻ D) E)
    (hit : ε xs = o) (miss : (ε xt == o) = false) :
    peelCaseOuter ε o
        (.case (.var xs)
          (.case (NegNeu.weaken (B := A) (.var xt)) t₁ t₂)
          (.case (NegNeu.weaken (B := B) (.var xt)) u₁ u₂)) =
      peelCaseOuter ε o
        (.case (.var xt)
          (.case (NegNeu.weaken (B := C) (.var xs))
            (InvTm.rename Rename.exchange t₁)
            (InvTm.rename Rename.exchange u₁))
          (.case (NegNeu.weaken (B := D) (.var xs))
            (InvTm.rename Rename.exchange t₂)
            (InvTm.rename Rename.exchange u₂))) ∧
    peelCaseOuter ε o
        (.case (.var xs)
          (.case (NegNeu.weaken (B := A) (.var xt)) t₁ t₂)
          (.case (NegNeu.weaken (B := B) (.var xt)) u₁ u₂)) =
      some ⟨A, B, .var xs,
        .case (NegNeu.weaken (B := A) (.var xt)) t₁ t₂,
        .case (NegNeu.weaken (B := B) (.var xt)) u₁ u₂⟩ := by
  have hX := peelCaseOuter_case_var_hit ε o xs
    (.case (NegNeu.weaken (B := A) (.var xt)) t₁ t₂)
    (.case (NegNeu.weaken (B := B) (.var xt)) u₁ u₂) hit
  refine ⟨?agree, hX⟩
  rw [hX]
  unfold peelCaseOuter
  set tY :=
    (.case (.var xt)
      (.case (NegNeu.weaken (B := C) (.var xs))
        (InvTm.rename Rename.exchange t₁)
        (InvTm.rename Rename.exchange u₁))
      (.case (NegNeu.weaken (B := D) (.var xs))
        (InvTm.rename Rename.exchange t₂)
        (InvTm.rename Rename.exchange u₂)) : InvTm Γ E)
  have hsz :
      InvTm.size tY =
        NegNeu.size (.var xt) +
          InvTm.size (.case (NegNeu.weaken (B := C) (.var xs))
            (InvTm.rename Rename.exchange t₁)
            (InvTm.rename Rename.exchange u₁)) +
          InvTm.size (.case (NegNeu.weaken (B := D) (.var xs))
            (InvTm.rename Rename.exchange t₂)
            (InvTm.rename Rename.exchange u₂)) + 1 := by
    simp [tY, InvTm.size]
  have hpos : 0 < InvTm.size tY := by simp only [hsz, NegNeu.size]; omega
  obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  have hLsz :
      InvTm.size (.case (NegNeu.weaken (B := C) (.var xs))
        (InvTm.rename Rename.exchange t₁)
        (InvTm.rename Rename.exchange u₁)) ≤ fuel := by
    simp only [hsz, NegNeu.size] at hm; omega
  have hRsz :
      InvTm.size (.case (NegNeu.weaken (B := D) (.var xs))
        (InvTm.rename Rename.exchange t₂)
        (InvTm.rename Rename.exchange u₂)) ≤ fuel := by
    simp only [hsz, NegNeu.size] at hm; omega
  have hitL :
      OriginEnv.weaken (A := C) ε (.split (ε xt) false) (.there xs) = o := by
    simpa [OriginEnv.weaken, OriginEnv.snoc] using hit
  have hitR :
      OriginEnv.weaken (A := D) ε (.split (ε xt) true) (.there xs) = o := by
    simpa [OriginEnv.weaken, OriginEnv.snoc] using hit
  have hLpos := size_case_var_pos (Γ := Γ ▻ C) (.there xs)
    (InvTm.rename Rename.exchange t₁) (InvTm.rename Rename.exchange u₁)
  have hRpos := size_case_var_pos (Γ := Γ ▻ D) (.there xs)
    (InvTm.rename Rename.exchange t₂) (InvTm.rename Rename.exchange u₂)
  have hL :
      peelCaseOuterGo fuel
          (OriginEnv.weaken (A := C) ε (.split (ε xt) false)) o
          (.case (NegNeu.weaken (B := C) (.var xs))
            (InvTm.rename Rename.exchange t₁)
            (InvTm.rename Rename.exchange u₁)) =
        some ⟨A, B, NegNeu.weaken (B := C) (.var xs),
          InvTm.rename Rename.exchange t₁,
          InvTm.rename Rename.exchange u₁⟩ := by
    have hfuel_pos : 0 < fuel := Nat.lt_of_lt_of_le hLpos hLsz
    obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hfuel_pos)
    simpa [NegNeu.weaken, NegNeu.rename, Rename.weaken] using
      peelCaseOuterGo_case_var_hit fuel'
        (OriginEnv.weaken (A := C) ε (.split (ε xt) false)) o (.there xs)
        (InvTm.rename Rename.exchange t₁) (InvTm.rename Rename.exchange u₁) hitL
  have hR :
      peelCaseOuterGo fuel
          (OriginEnv.weaken (A := D) ε (.split (ε xt) true)) o
          (.case (NegNeu.weaken (B := D) (.var xs))
            (InvTm.rename Rename.exchange t₂)
            (InvTm.rename Rename.exchange u₂)) =
        some ⟨A, B, NegNeu.weaken (B := D) (.var xs),
          InvTm.rename Rename.exchange t₂,
          InvTm.rename Rename.exchange u₂⟩ := by
    have hfuel_pos : 0 < fuel := Nat.lt_of_lt_of_le hRpos hRsz
    obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hfuel_pos)
    simpa [NegNeu.weaken, NegNeu.rename, Rename.weaken] using
      peelCaseOuterGo_case_var_hit fuel'
        (OriginEnv.weaken (A := D) ε (.split (ε xt) true)) o (.there xs)
        (InvTm.rename Rename.exchange t₂) (InvTm.rename Rename.exchange u₂) hitR
  have hgo :=
    peelCaseOuterGo_case_miss_var fuel ε o xt xs
      (InvTm.rename Rename.exchange t₁) (InvTm.rename Rename.exchange u₁)
      (InvTm.rename Rename.exchange t₂) (InvTm.rename Rename.exchange u₂)
      miss hit hL hR
  -- Exchange involution recovers the original leaves.
  have hgo' :
      peelCaseOuterGo (fuel + 1) ε o tY =
        some ⟨A, B, .var xs,
          .case (NegNeu.weaken (B := A) (.var xt)) t₁ t₂,
          .case (NegNeu.weaken (B := B) (.var xt)) u₁ u₂⟩ := by
    simpa [tY, InvTm.rename_exchange_exchange] using hgo
  simpa [tY, hm] using hgo'.symm

/-! ### Peel stable under `rekeyHypToObs`

LetPos dig uses `.dom 0` (fixed by rekey; same as λ dig), so dig-under-foc
commutes with newest-hyp→obs rekey. Nested case-miss needs the same
`weaken_rekey` / `originOfVar` / `beq` substrate.
-/

theorem originOfVar_rekeyHypToObs {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (hypIdx k : Nat) (n : NegNeu Γ A) :
    originOfVar (fun {_B} x => Origin.rekeyHypToObs hypIdx k (ε x)) n =
      (originOfVar ε n).map (Origin.rekeyHypToObs hypIdx k) := by
  cases n with
  | var x => rfl
  | app _ _ | fst _ | snd _ => rfl

/-- Rekey of a found origin preserves the hit/miss test (`=` form). -/
theorem originOfVar_rekey_hit_iff {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (hypIdx k : Nat) (n : NegNeu Γ A) (o : Origin sig)
    {β : Type} (r : β) :
    (match (originOfVar ε n).map (Origin.rekeyHypToObs hypIdx k) with
      | some om => if om = Origin.rekeyHypToObs hypIdx k o then some r else none
      | none => none) =
    (match originOfVar ε n with
      | some om => if om = o then some r else none
      | none => none) := by
  cases originOfVar ε n with
  | none => rfl
  | some om =>
      change
          (if Origin.rekeyHypToObs hypIdx k om =
                Origin.rekeyHypToObs hypIdx k o then some r else none) =
            (if om = o then some r else none)
      by_cases h : om = o
      · subst h; simp
      · have hne : Origin.rekeyHypToObs hypIdx k om ≠
            Origin.rekeyHypToObs hypIdx k o := fun hr =>
          h (Origin.rekeyHypToObs_inj hr)
        simp [h, hne]

/-- Same as `originOfVar_rekey_hit_iff`, for the `BEq` tests in `peelCaseOuterGo`. -/
theorem originOfVar_rekey_beq_hit_iff {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (hypIdx k : Nat) (n : NegNeu Γ A) (o : Origin sig)
    {β : Type} (r : β) :
    (match (originOfVar ε n).map (Origin.rekeyHypToObs hypIdx k) with
      | some om => if om == Origin.rekeyHypToObs hypIdx k o then some r else none
      | none => none) =
    (match originOfVar ε n with
      | some om => if om == o then some r else none
      | none => none) := by
  cases originOfVar ε n with
  | none => rfl
  | some om =>
      change
          (if Origin.rekeyHypToObs hypIdx k om ==
                Origin.rekeyHypToObs hypIdx k o then some r else none) =
            (if om == o then some r else none)
      rw [Origin.beq_rekeyHypToObs]

theorem originOfVar_env_eq {Γ : Ctx sig} {A : Object sig.nBases}
    {ε ε' : OriginEnv Γ} (n : NegNeu Γ A)
    (hε : ∀ {B} (x : Var Γ B), ε x = ε' x) :
    originOfVar ε n = originOfVar ε' n := by
  cases n with
  | var x => exact congrArg some (hε x)
  | app _ _ | fst _ | snd _ => rfl

/-- Pointwise env equality preserves peel. -/
theorem peelCaseOuterGo_env_eq {Γ : Ctx sig} {C : Object sig.nBases}
    (fuel : Nat) {ε ε' : OriginEnv Γ} {o o' : Origin sig} (t : InvTm Γ C)
    (hε : ∀ {B} (x : Var Γ B), ε x = ε' x) (ho : o = o') :
    peelCaseOuterGo fuel ε o t = peelCaseOuterGo fuel ε' o' t := by
  subst ho
  induction fuel generalizing Γ C ε ε' with
  | zero => rfl
  | succ fuel ih =>
      cases t with
      | unit | abort _ => rfl
      | foc f =>
          cases f with
          | pos _ | neg _ => rfl
          | sat s =>
              cases s with
              | mk _ body =>
                  simp only [peelCaseOuterGo]
                  exact ih (ε := ε) (ε' := ε') body hε
          | letPos _n body =>
              rename_i P
              simp only [peelCaseOuterGo]
              have hεw : ∀ {B} (x : Var (Γ ▻ P) B),
                  OriginEnv.weaken (A := P) ε (.dom 0) x =
                    OriginEnv.weaken (A := P) ε' (.dom 0) x := by
                intro B x; cases x with
                | here => rfl
                | there y => exact hε y
              rw [ih (ε := OriginEnv.weaken (A := P) ε (.dom 0))
                (ε' := OriginEnv.weaken (A := P) ε' (.dom 0)) body hεw]
      | pair t₁ t₂ =>
          simp only [peelCaseOuterGo]
          rw [ih (ε := ε) (ε' := ε') t₁ hε, ih (ε := ε) (ε' := ε') t₂ hε]
      | lam body =>
          rename_i Arg _Ret
          simp only [peelCaseOuterGo]
          have hεw : ∀ {B} (x : Var (Γ ▻ Arg) B),
              OriginEnv.weaken (A := Arg) ε (.dom 0) x =
                OriginEnv.weaken (A := Arg) ε' (.dom 0) x := by
            intro B x; cases x with
            | here => rfl
            | there y => exact hε y
          rw [ih (ε := OriginEnv.weaken (A := Arg) ε (.dom 0))
            (ε' := OriginEnv.weaken (A := Arg) ε' (.dom 0)) body hεw]
      | case scr tL tR =>
          rename_i A B
          cases scr with
          | app _ _ | fst _ | snd _ => rfl
          | var x =>
              simp only [peelCaseOuterGo]
              have hhit : (ε x == o) = (ε' x == o) := by rw [hε x]
              rw [hhit]
              split
              · rfl
              · have hx : ε x = ε' x := hε x
                have hεL : ∀ {C} (y : Var (Γ ▻ A) C),
                    OriginEnv.weaken (A := A) ε (.split (ε x) false) y =
                      OriginEnv.weaken (A := A) ε' (.split (ε' x) false) y := by
                  intro C y; cases y with
                  | here => simp [OriginEnv.weaken, hx]
                  | there z => exact hε z
                have hεR : ∀ {C} (y : Var (Γ ▻ B) C),
                    OriginEnv.weaken (A := B) ε (.split (ε x) true) y =
                      OriginEnv.weaken (A := B) ε' (.split (ε' x) true) y := by
                  intro C y; cases y with
                  | here => simp [OriginEnv.weaken, hx]
                  | there z => exact hε z
                rw [ih (ε := OriginEnv.weaken (A := A) ε (.split (ε x) false))
                  (ε' := OriginEnv.weaken (A := A) ε' (.split (ε' x) false))
                  tL hεL]
                rw [ih (ε := OriginEnv.weaken (A := B) ε (.split (ε x) true))
                  (ε' := OriginEnv.weaken (A := B) ε' (.split (ε' x) true))
                  tR hεR]
                cases peelCaseOuterGo fuel
                    (OriginEnv.weaken (A := A) ε' (.split (ε' x) false)) o tL with
                | none =>
                    cases distCaseOut (.var x) tL tR with
                    | none => rfl
                    | some t' => exact ih (ε := ε) (ε' := ε') t' hε
                | some rL =>
                    cases peelCaseOuterGo fuel
                        (OriginEnv.weaken (A := B) ε' (.split (ε' x) true)) o tR with
                    | none =>
                        cases distCaseOut (.var x) tL tR with
                        | none => rfl
                        | some t' => exact ih (ε := ε) (ε' := ε') t' hε
                    | some rR =>
                        rcases rL with ⟨C₁, D₁, n₁, a₁, b₁⟩
                        rcases rR with ⟨C₂, D₂, n₂, a₂, b₂⟩
                        -- Only `originOfVar` differs (ε vs ε'); rewrite it under the shared spine.
                        simp_rw [originOfVar_env_eq (hε := hε)]

/--
Simultaneous rekey of the origin environment and forced query leaves
`peelCaseOuterGo` unchanged (returned neutrals/terms carry no origin tags).
-/
theorem peelCaseOuterGo_rekeyHypToObs {Γ : Ctx sig} {C : Object sig.nBases}
    (fuel : Nat) (ε : OriginEnv Γ) (hypIdx k : Nat) (o : Origin sig)
    (t : InvTm Γ C) :
    peelCaseOuterGo fuel
        (fun {_B} x => Origin.rekeyHypToObs hypIdx k (ε x))
        (Origin.rekeyHypToObs hypIdx k o) t =
      peelCaseOuterGo fuel ε o t := by
  induction fuel generalizing Γ C ε with
  | zero => rfl
  | succ fuel ih =>
      cases t with
      | unit | abort _ => rfl
      | foc f =>
          cases f with
          | pos _ | neg _ => rfl
          | sat s =>
              cases s with
              | mk _ body =>
                  simp only [peelCaseOuterGo]
                  exact ih ε body
          | letPos _n body =>
              rename_i P
              simp only [peelCaseOuterGo]
              have hεw : ∀ {B} (x : Var (Γ ▻ P) B),
                  Origin.rekeyHypToObs hypIdx k
                    (OriginEnv.weaken (A := P) ε (.dom 0) x) =
                    OriginEnv.weaken (A := P)
                      (fun {_C} y => Origin.rekeyHypToObs hypIdx k (ε y))
                      (.dom 0) x := by
                intro B x
                simpa [Origin.rekeyHypToObs_dom] using
                  OriginEnv.weaken_rekeyHypToObs ε (.dom 0) hypIdx k x
              have hdig :=
                peelCaseOuterGo_env_eq (o := Origin.rekeyHypToObs hypIdx k o)
                  (o' := Origin.rekeyHypToObs hypIdx k o) fuel body hεw rfl
              have hmain :
                  peelCaseOuterGo fuel
                      (OriginEnv.weaken (A := P)
                        (fun {_C} y => Origin.rekeyHypToObs hypIdx k (ε y))
                        (.dom 0))
                      (Origin.rekeyHypToObs hypIdx k o) body =
                    peelCaseOuterGo fuel
                      (OriginEnv.weaken (A := P) ε (.dom 0)) o body :=
                hdig.symm.trans (ih (OriginEnv.weaken (A := P) ε (.dom 0)) body)
              rw [hmain]
      | pair t₁ t₂ =>
          simp only [peelCaseOuterGo]
          rw [ih ε t₁, ih ε t₂]
      | lam body =>
          rename_i Arg _Ret
          simp only [peelCaseOuterGo]
          have hεw : ∀ {B} (x : Var (Γ ▻ Arg) B),
              Origin.rekeyHypToObs hypIdx k
                (OriginEnv.weaken (A := Arg) ε (.dom 0) x) =
                OriginEnv.weaken (A := Arg)
                  (fun {_C} y => Origin.rekeyHypToObs hypIdx k (ε y))
                  (.dom 0) x := by
            intro B x
            simpa [Origin.rekeyHypToObs_dom] using
              OriginEnv.weaken_rekeyHypToObs ε (.dom 0) hypIdx k x
          have hdig :=
            peelCaseOuterGo_env_eq (o := Origin.rekeyHypToObs hypIdx k o)
              (o' := Origin.rekeyHypToObs hypIdx k o) fuel body hεw rfl
          have hmain :
              peelCaseOuterGo fuel
                  (OriginEnv.weaken (A := Arg)
                    (fun {_C} y => Origin.rekeyHypToObs hypIdx k (ε y))
                    (.dom 0))
                  (Origin.rekeyHypToObs hypIdx k o) body =
                peelCaseOuterGo fuel
                  (OriginEnv.weaken (A := Arg) ε (.dom 0)) o body :=
            hdig.symm.trans (ih (OriginEnv.weaken (A := Arg) ε (.dom 0)) body)
          rw [hmain]
      | case scr tL tR =>
          rename_i A B
          cases scr with
          | app _ _ | fst _ | snd _ => rfl
          | var x =>
              simp only [peelCaseOuterGo]
              have hhit :
                  ((fun {_B} y => Origin.rekeyHypToObs hypIdx k (ε y)) x ==
                    Origin.rekeyHypToObs hypIdx k o) =
                    (ε x == o) :=
                Origin.beq_rekeyHypToObs hypIdx k (ε x) o
              rw [hhit]
              split
              · rfl
              · have hεL : ∀ {C} (y : Var (Γ ▻ A) C),
                    Origin.rekeyHypToObs hypIdx k
                      (OriginEnv.weaken (A := A) ε (.split (ε x) false) y) =
                      OriginEnv.weaken (A := A)
                        (fun {_C} z => Origin.rekeyHypToObs hypIdx k (ε z))
                        (.split (Origin.rekeyHypToObs hypIdx k (ε x)) false) y := by
                  intro C y
                  simpa [Origin.rekeyHypToObs_split] using
                    OriginEnv.weaken_rekeyHypToObs ε (.split (ε x) false) hypIdx k y
                have hεR : ∀ {C} (y : Var (Γ ▻ B) C),
                    Origin.rekeyHypToObs hypIdx k
                      (OriginEnv.weaken (A := B) ε (.split (ε x) true) y) =
                      OriginEnv.weaken (A := B)
                        (fun {_C} z => Origin.rekeyHypToObs hypIdx k (ε z))
                        (.split (Origin.rekeyHypToObs hypIdx k (ε x)) true) y := by
                  intro C y
                  simpa [Origin.rekeyHypToObs_split] using
                    OriginEnv.weaken_rekeyHypToObs ε (.split (ε x) true) hypIdx k y
                have hL :=
                  (peelCaseOuterGo_env_eq
                    (o := Origin.rekeyHypToObs hypIdx k o)
                    (o' := Origin.rekeyHypToObs hypIdx k o) fuel tL hεL rfl).symm.trans
                    (ih (OriginEnv.weaken (A := A) ε (.split (ε x) false)) tL)
                have hR :=
                  (peelCaseOuterGo_env_eq
                    (o := Origin.rekeyHypToObs hypIdx k o)
                    (o' := Origin.rekeyHypToObs hypIdx k o) fuel tR hεR rfl).symm.trans
                    (ih (OriginEnv.weaken (A := B) ε (.split (ε x) true)) tR)
                rw [hL, hR]
                cases peelCaseOuterGo fuel
                    (OriginEnv.weaken (A := A) ε (.split (ε x) false)) o tL with
                | none =>
                    cases distCaseOut (.var x) tL tR with
                    | none => rfl
                    | some t' => exact ih ε t'
                | some rL =>
                    cases peelCaseOuterGo fuel
                        (OriginEnv.weaken (A := B) ε (.split (ε x) true)) o tR with
                    | none =>
                        cases distCaseOut (.var x) tL tR with
                        | none => rfl
                        | some t' => exact ih ε t'
                    | some rR =>
                        rcases rL with ⟨C₁, D₁, n₁, a₁, b₁⟩
                        rcases rR with ⟨C₂, D₂, n₂, a₂, b₂⟩
                        -- Shared peel spine; only originOfVar / == query differ.
                        by_cases hC : C₁ = C₂
                        · by_cases hD : D₁ = D₂
                          · by_cases hbeq :
                                NegNeu.beq n₁ (hD ▸ hC ▸ n₂) = true
                            · cases hunw : NegNeu.unweaken? n₁ with
                              | none =>
                                  simp [hC, hD, hbeq, hunw]
                              | some m =>
                                  simp only [hC, hD, hbeq, hunw, ↓reduceDIte,
                                    ↓reduceIte]
                                  rw [originOfVar_rekeyHypToObs ε hypIdx k m]
                                  exact originOfVar_rekey_beq_hit_iff
                                    ε hypIdx k m o _
                            · simp [hC, hD, hbeq]
                          · simp [hC, hD]
                        · simp [hC]

/-- Top-level peel is stable under simultaneous env/query rekey. -/
theorem peelCaseOuter_rekeyHypToObs {Γ : Ctx sig} {C : Object sig.nBases}
    (ε : OriginEnv Γ) (hypIdx k : Nat) (o : Origin sig) (t : InvTm Γ C) :
    peelCaseOuter
        (fun {_B} x => Origin.rekeyHypToObs hypIdx k (ε x))
        (Origin.rekeyHypToObs hypIdx k o) t =
      peelCaseOuter ε o t :=
  peelCaseOuterGo_rekeyHypToObs (InvTm.size t) ε hypIdx k o t

theorem peelCaseOuter_env_eq {Γ : Ctx sig} {C : Object sig.nBases}
    {ε ε' : OriginEnv Γ} {o o' : Origin sig} (t : InvTm Γ C)
    (hε : ∀ {B} (x : Var Γ B), ε x = ε' x) (ho : o = o') :
    peelCaseOuter ε o t = peelCaseOuter ε' o' t :=
  peelCaseOuterGo_env_eq (InvTm.size t) t hε ho

end Equality
end Gimbal
