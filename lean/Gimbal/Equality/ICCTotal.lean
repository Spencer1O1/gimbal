/-
  Totality of ordered-phase encoding on the valid fragment (Milestone 8F/E).

  Successful-result fuel monotonicity: if encode returns `some c` at fuel `f`,
  it returns the same `c` at every `g ≥ f`. Failure need not be monotonic.
-/

import Gimbal.Equality.ICCEncode
import Gimbal.Equality.ICCFragment

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Successful encode unfolds -/

theorem encodeICCGo_foc_pos {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (p : PosNeu Γ A)
    (hforce : forcedRule ws A = .focus) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.foc (.pos (.done p))) =
      some (.foc (.pos p)) := by
  simp [encodeICCGo, hforce, encodeFocGo]

theorem encodeICCGo_foc_neg {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (n : NegNeu Γ A)
    (hforce : forcedRule ws A = .focus) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.foc (.neg (.done n))) =
      some (.foc (.neg n)) := by
  simp [encodeICCGo, hforce, encodeFocGo]

theorem forcedRule_cons_base_moveStable (e : PosEntry sig) (ws : List (PosEntry sig))
    {b : Fin sig.nBases} (hty : e.ty = .base b) (goal : Object sig.nBases) :
    forcedRule (e :: ws) goal = .moveStable e := by
  simp [forcedRule, hty]

theorem encodeICCGo_pair_rightProd {Γ : Ctx sig} {L R : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (t : InvTm Γ L) (u : InvTm Γ R)
    (hforce : forcedRule ws (.prod L R) = .rightProd L R) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.pair t u) =
      match encodeICCGo fuel ws ε domNest obsSlot t,
            encodeICCGo fuel ws ε domNest obsSlot u with
      | some c₁, some c₂ => some (.pair c₁ c₂)
      | _, _ => none := by
  simp [encodeICCGo, hforce, peelPair]
  rfl

theorem encodeICCGo_moveStable_eq {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (t : InvTm Γ A) (e : PosEntry sig)
    (hforce : forcedRule ws A = .moveStable e) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot t =
      encodeICCGo fuel ws.tail ε domNest obsSlot t := by
  cases t <;> simp [encodeICCGo, hforce]

theorem encodeICCGo_focus_eq {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (f : FocTm Γ A)
    (hforce : forcedRule ws A = .focus) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.foc f) =
      encodeFocGo fuel ws ε domNest obsSlot f := by
  simp [encodeICCGo, hforce]

theorem encodeICCGo_leftNever_abort {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (n : NegNeu Γ .never) (e : PosEntry sig)
    (hforce : forcedRule ws A = .leftNever e) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.abort (A := A) n) =
      some (.abort e.origin) := by
  simp [encodeICCGo, hforce]

theorem encodeICCGo_rightUnit_unit {Γ : Ctx sig}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat)
    (hforce : forcedRule ws (.unit : Object sig.nBases) = .rightUnit) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.unit (Γ := Γ)) =
      some (.unit) := by
  simp [encodeICCGo, hforce, peelUnit]

theorem encodeICCGo_lam_rightExp {Γ : Ctx sig} {Arg Ret : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (body : InvTm (Γ ▻ Arg) Ret)
    (hforce : forcedRule ws (.exp Arg Ret) = .rightExp Arg Ret) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.lam body) =
      match encodeICCGo fuel (pushPos ws (.dom (sig := sig) domNest) Arg)
            (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) domNest))
            (domNest + 1) obsSlot body with
      | some c => some (.lam c)
      | none => none := by
  simp [encodeICCGo, hforce, peelLam]
  rfl

theorem encodeICCGo_foc_rightProd {Γ : Ctx sig} {L R : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (f : FocTm Γ (.prod L R))
    (hforce : forcedRule ws (.prod L R) = .rightProd L R) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.foc f) =
      match encodeFocGo fuel ws ε domNest obsSlot f with
      | some c => some c
      | none => none := by
  simp [encodeICCGo, hforce, peelPair]
  rfl

theorem encodeICCGo_foc_rightExp {Γ : Ctx sig} {Arg Ret : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (f : FocTm Γ (.exp Arg Ret))
    (hforce : forcedRule ws (.exp Arg Ret) = .rightExp Arg Ret) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.foc f) =
      match encodeFocGo fuel ws ε domNest obsSlot f with
      | some c => some c
      | none => none := by
  simp [encodeICCGo, hforce, peelLam]
  rfl

theorem encodeLeftCoprodBranches_unfold {Γ : Ctx sig} {L R A : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (e : PosEntry sig)
    (tL : InvTm (Γ ▻ L) A) (tR : InvTm (Γ ▻ R) A) :
    encodeLeftCoprodBranches fuel ws ε domNest obsSlot e tL tR =
      match encodeICCGo fuel
              (pushPos ws.tail (.split e.origin false) L)
              (OriginEnv.weaken (A := L) ε (.split e.origin false))
              domNest obsSlot tL,
            encodeICCGo fuel
              (pushPos ws.tail (.split e.origin true) R)
              (OriginEnv.weaken (A := R) ε (.split e.origin true))
              domNest obsSlot tR with
      | some cL, some cR => some (.case e.origin cL cR)
      | _, _ => none := by
  simp [encodeLeftCoprodBranches]
  rfl

/-! ### Successful-result fuel monotonicity -/

/--
Mutual successful-result fuel mono: a successful encode at fuel `fuel₁` is
stable at every larger fuel. Failure need not be monotonic.
-/
theorem encode_successful_fuel_mono (fuel₁ : Nat) :
    (∀ {Γ : Ctx sig} {A : Object sig.nBases} (fuel₂ : Nat)
      (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
      (domNest obsSlot : Nat) (t : InvTm Γ A) (c : ICCCode Γ A),
      fuel₁ ≤ fuel₂ →
        encodeICCGo fuel₁ ws ε domNest obsSlot t = some c →
          encodeICCGo fuel₂ ws ε domNest obsSlot t = some c) ∧
    (∀ {Γ : Ctx sig} {A : Object sig.nBases} (fuel₂ : Nat)
      (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
      (domNest obsSlot : Nat) (f : FocTm Γ A) (c : ICCCode Γ A),
      fuel₁ ≤ fuel₂ →
        encodeFocGo fuel₁ ws ε domNest obsSlot f = some c →
          encodeFocGo fuel₂ ws ε domNest obsSlot f = some c) ∧
    (∀ {Γ : Ctx sig} {A L R : Object sig.nBases} (fuel₂ : Nat)
      (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
      (domNest obsSlot : Nat) (e : PosEntry sig)
      (tL : InvTm (Γ ▻ L) A) (tR : InvTm (Γ ▻ R) A) (c : ICCCode Γ A),
      fuel₁ ≤ fuel₂ →
        encodeLeftCoprodBranches fuel₁ ws ε domNest obsSlot e tL tR = some c →
          encodeLeftCoprodBranches fuel₂ ws ε domNest obsSlot e tL tR = some c) := by
  induction fuel₁ with
  | zero =>
      refine ⟨?go0, ?foc0, ?cop0⟩
      · intro Γ A fuel₂ ws ε domNest obsSlot t c hle h
        simp [encodeICCGo] at h
      · intro Γ A fuel₂ ws ε domNest obsSlot f c hle h
        cases f with
        | pos p =>
            cases p with
            | done p => simpa [encodeFocGo] using h
        | neg n =>
            cases n with
            | done n => simpa [encodeFocGo] using h
        | letPos n t => simp [encodeFocGo] at h
        | sat s =>
            cases s with
            | mk _ t => simp [encodeFocGo] at h
      · intro Γ A L R fuel₂ ws ε domNest obsSlot e tL tR c hle h
        rw [encodeLeftCoprodBranches_unfold] at h
        simp [encodeICCGo] at h
  | succ fuel₁ ih =>
      rcases ih with ⟨ihGo, ihFoc, ihCop⟩
      -- Name Go mono at this fuel so Coprod (same fuel) can use it.
      have goMono :
          ∀ {Γ : Ctx sig} {A : Object sig.nBases} (fuel₂ : Nat)
            (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
            (domNest obsSlot : Nat) (t : InvTm Γ A) (c : ICCCode Γ A),
            fuel₁ + 1 ≤ fuel₂ →
              encodeICCGo (fuel₁ + 1) ws ε domNest obsSlot t = some c →
                encodeICCGo fuel₂ ws ε domNest obsSlot t = some c := by
        intro Γ A fuel₂ ws ε domNest obsSlot t c hle h
        cases fuel₂ with
        | zero => exact (Nat.not_succ_le_zero _ hle).elim
        | succ fuel₂ =>
            have hle' : fuel₁ ≤ fuel₂ := Nat.le_of_succ_le_succ hle
            cases hfr : forcedRule ws A with
            | moveStable e =>
                rw [encodeICCGo_moveStable_eq fuel₁ ws ε domNest obsSlot t e hfr] at h
                rw [encodeICCGo_moveStable_eq fuel₂ ws ε domNest obsSlot t e hfr]
                exact ihGo fuel₂ ws.tail ε domNest obsSlot t c hle' h
            | leftNever e =>
                cases t with
                | abort n =>
                    rw [encodeICCGo_leftNever_abort fuel₁ ws ε domNest obsSlot n e hfr] at h
                    rw [encodeICCGo_leftNever_abort fuel₂ ws ε domNest obsSlot n e hfr]
                    exact h
                | unit => simp [encodeICCGo, hfr] at h
                | pair _ _ => simp [encodeICCGo, hfr] at h
                | lam _ => simp [encodeICCGo, hfr] at h
                | case _ _ _ => simp [encodeICCGo, hfr] at h
                | foc _ => simp [encodeICCGo, hfr] at h
            | rightUnit =>
                if hA : A = (.unit : Object sig.nBases) then
                  subst A
                  cases t with
                  | unit =>
                      rw [encodeICCGo_rightUnit_unit fuel₁ ws ε domNest obsSlot hfr] at h
                      rw [encodeICCGo_rightUnit_unit fuel₂ ws ε domNest obsSlot hfr]
                      exact h
                  | case _ _ _ => simp [encodeICCGo, hfr, peelUnit] at h
                  | abort _ => simp [encodeICCGo, hfr, peelUnit] at h
                  | foc _ => simp [encodeICCGo, hfr, peelUnit] at h
                else
                  cases t with
                  | unit => exact (hA rfl).elim
                  | pair _ _ => simp [encodeICCGo, hfr] at h
                  | lam _ => simp [encodeICCGo, hfr] at h
                  | case _ _ _ =>
                      simp [encodeICCGo, hfr] at h
                      exact (hA h.1).elim
                  | abort _ =>
                      simp [encodeICCGo, hfr] at h
                      exact (hA h.1).elim
                  | foc _ =>
                      simp [encodeICCGo, hfr] at h
                      exact (hA h.1).elim
            | rightProd L R =>
                if hA : A = (.prod L R : Object sig.nBases) then
                  subst A
                  cases t with
                  | pair t₁ t₂ =>
                      rw [encodeICCGo_pair_rightProd fuel₁ ws ε domNest obsSlot t₁ t₂ hfr] at h
                      rw [encodeICCGo_pair_rightProd fuel₂ ws ε domNest obsSlot t₁ t₂ hfr]
                      cases ht₁ : encodeICCGo fuel₁ ws ε domNest obsSlot t₁ with
                      | some c₁ =>
                          cases ht₂ : encodeICCGo fuel₁ ws ε domNest obsSlot t₂ with
                          | some c₂ =>
                              simp only [ht₁, ht₂] at h
                              cases h
                              simp [ihGo fuel₂ ws ε domNest obsSlot t₁ c₁ hle' ht₁,
                                ihGo fuel₂ ws ε domNest obsSlot t₂ c₂ hle' ht₂]
                          | none => simp [ht₁, ht₂] at h
                      | none =>
                          cases encodeICCGo fuel₁ ws ε domNest obsSlot t₂ <;>
                            simp [ht₁] at h
                  | foc f =>
                      rw [encodeICCGo_foc_rightProd fuel₁ ws ε domNest obsSlot f hfr] at h
                      rw [encodeICCGo_foc_rightProd fuel₂ ws ε domNest obsSlot f hfr]
                      cases hf : encodeFocGo fuel₁ ws ε domNest obsSlot f with
                      | some c' =>
                          simp only [hf] at h
                          have hmono :=
                            ihFoc fuel₂ ws ε domNest obsSlot f c' hle' hf
                          simp only [hmono]
                          exact h
                      | none => simp [hf] at h
                  | case _ _ _ => simp [encodeICCGo, hfr, peelPair] at h
                  | abort _ => simp [encodeICCGo, hfr, peelPair] at h
                else
                  cases t with
                  | unit => simp [encodeICCGo, hfr] at h
                  | pair _ _ =>
                      simp [encodeICCGo, hfr] at h
                      exact (hA (congrArg₂ Object.prod h.1.1 h.1.2)).elim
                  | lam _ => simp [encodeICCGo, hfr] at h
                  | case _ _ _ =>
                      simp [encodeICCGo, hfr] at h
                      exact (hA h.1).elim
                  | abort _ =>
                      simp [encodeICCGo, hfr] at h
                      exact (hA h.1).elim
                  | foc _ =>
                      simp [encodeICCGo, hfr] at h
                      exact (hA h.1).elim
            | rightExp Arg Ret =>
                if hA : A = (.exp Arg Ret : Object sig.nBases) then
                  subst A
                  cases t with
                  | lam body =>
                      rw [encodeICCGo_lam_rightExp fuel₁ ws ε domNest obsSlot body hfr] at h
                      rw [encodeICCGo_lam_rightExp fuel₂ ws ε domNest obsSlot body hfr]
                      cases hb : encodeICCGo fuel₁
                          (pushPos ws (.dom (sig := sig) domNest) Arg)
                          (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) domNest))
                          (domNest + 1) obsSlot body with
                      | some c' =>
                          simp only [hb] at h
                          have hmono :=
                            ihGo fuel₂ _ _ (domNest + 1) obsSlot body c' hle' hb
                          simp only [hmono]
                          exact h
                      | none => simp [hb] at h
                  | foc f =>
                      rw [encodeICCGo_foc_rightExp fuel₁ ws ε domNest obsSlot f hfr] at h
                      rw [encodeICCGo_foc_rightExp fuel₂ ws ε domNest obsSlot f hfr]
                      cases hf : encodeFocGo fuel₁ ws ε domNest obsSlot f with
                      | some c' =>
                          simp only [hf] at h
                          have hmono :=
                            ihFoc fuel₂ ws ε domNest obsSlot f c' hle' hf
                          simp only [hmono]
                          exact h
                      | none => simp [hf] at h
                  | case _ _ _ => simp [encodeICCGo, hfr, peelLam] at h
                  | abort _ => simp [encodeICCGo, hfr, peelLam] at h
                else
                  cases t with
                  | unit => simp [encodeICCGo, hfr] at h
                  | pair _ _ => simp [encodeICCGo, hfr] at h
                  | lam _ =>
                      simp [encodeICCGo, hfr] at h
                      exact (hA (congrArg₂ Object.exp h.1.1 h.1.2)).elim
                  | case _ _ _ =>
                      simp [encodeICCGo, hfr] at h
                      exact (hA h.1).elim
                  | abort _ =>
                      simp [encodeICCGo, hfr] at h
                      exact (hA h.1).elim
                  | foc _ =>
                      simp [encodeICCGo, hfr] at h
                      exact (hA h.1).elim
            | leftCoprod e L R =>
                unfold encodeICCGo at h ⊢
                simp only [hfr] at h ⊢
                split at h
                · next L' R' n tL tR hpeel =>
                    split at h
                    · next hL =>
                        split at h
                        · next hR =>
                            simp only [hL, hR]
                            exact ihCop (L := L) (R := R) fuel₂ ws ε
                              domNest obsSlot e (hL ▸ tL) (hR ▸ tR) c hle' h
                        · contradiction
                    · contradiction
                · next =>
                    split at h
                    · next =>
                        split at h
                        · next ty x hfind =>
                            split at h
                            · next hty =>
                                split at h
                                · next hit =>
                                    simp only [hty, hit]
                                    exact ihCop (L := L) (R := R) fuel₂ ws ε
                                      domNest obsSlot e (.unit) (.unit) c hle' h
                                · contradiction
                            · contradiction
                        · contradiction
                    · contradiction
            | focus =>
                cases t with
                | foc f =>
                    rw [encodeICCGo_focus_eq fuel₁ ws ε domNest obsSlot f hfr] at h
                    rw [encodeICCGo_focus_eq fuel₂ ws ε domNest obsSlot f hfr]
                    exact ihFoc fuel₂ ws ε domNest obsSlot f c hle' h
                | unit => simp [encodeICCGo, hfr] at h
                | pair _ _ => simp [encodeICCGo, hfr] at h
                | lam _ => simp [encodeICCGo, hfr] at h
                | case _ _ _ => simp [encodeICCGo, hfr] at h
                | abort _ => simp [encodeICCGo, hfr] at h
      have focMono :
          ∀ {Γ : Ctx sig} {A : Object sig.nBases} (fuel₂ : Nat)
            (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
            (domNest obsSlot : Nat) (f : FocTm Γ A) (c : ICCCode Γ A),
            fuel₁ + 1 ≤ fuel₂ →
              encodeFocGo (fuel₁ + 1) ws ε domNest obsSlot f = some c →
                encodeFocGo fuel₂ ws ε domNest obsSlot f = some c := by
        intro Γ A fuel₂ ws ε domNest obsSlot f c hle h
        cases f with
        | pos p =>
            cases p with
            | done p => simpa [encodeFocGo] using h
        | neg n =>
            cases n with
            | done n => simpa [encodeFocGo] using h
        | letPos n t =>
            cases fuel₂ with
            | zero => exact (Nat.not_succ_le_zero _ hle).elim
            | succ fuel₂ =>
                have hle' : fuel₁ ≤ fuel₂ := Nat.le_of_succ_le_succ hle
                simp [encodeFocGo] at h ⊢
                split at h
                · next c' hc' =>
                    cases h
                    rw [ihGo fuel₂ _ _ domNest (obsSlot + 1) t c' hle' hc']
                · contradiction
        | sat s =>
            cases s with
            | mk _sched t =>
                cases fuel₂ with
                | zero => exact (Nat.not_succ_le_zero _ hle).elim
                | succ fuel₂ =>
                    have hle' : fuel₁ ≤ fuel₂ := Nat.le_of_succ_le_succ hle
                    simp [encodeFocGo] at h ⊢
                    split at h
                    · next c' hc' =>
                        cases h
                        rw [ihGo fuel₂ ws ε domNest obsSlot t c' hle' hc']
                    · contradiction
      have copMono :
          ∀ {Γ : Ctx sig} {A L R : Object sig.nBases} (fuel₂ : Nat)
            (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
            (domNest obsSlot : Nat) (e : PosEntry sig)
            (tL : InvTm (Γ ▻ L) A) (tR : InvTm (Γ ▻ R) A) (c : ICCCode Γ A),
            fuel₁ + 1 ≤ fuel₂ →
              encodeLeftCoprodBranches (fuel₁ + 1) ws ε domNest obsSlot e tL tR =
                some c →
                encodeLeftCoprodBranches fuel₂ ws ε domNest obsSlot e tL tR =
                  some c := by
        intro Γ A L R fuel₂ ws ε domNest obsSlot e tL tR c hle h
        rw [encodeLeftCoprodBranches_unfold] at h ⊢
        split at h
        · next cL cR hcL hcR =>
            cases h
            have hL := goMono fuel₂ _ _ domNest obsSlot tL cL hle hcL
            have hR := goMono fuel₂ _ _ domNest obsSlot tR cR hle hcR
            simp [hL, hR]
        · contradiction
      exact ⟨goMono, focMono, copMono⟩

/-- Successful `encodeICCGo` is stable under increasing fuel. -/
theorem encodeICCGo_le {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel fuel' : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (t : InvTm Γ A) (c : ICCCode Γ A)
    (hle : fuel ≤ fuel')
    (h : encodeICCGo fuel ws ε domNest obsSlot t = some c) :
    encodeICCGo fuel' ws ε domNest obsSlot t = some c :=
  (encode_successful_fuel_mono fuel).1 fuel' ws ε domNest obsSlot t c hle h

/-- Successful `encodeFocGo` is stable under increasing fuel. -/
theorem encodeFocGo_le {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel fuel' : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (f : FocTm Γ A) (c : ICCCode Γ A)
    (hle : fuel ≤ fuel')
    (h : encodeFocGo fuel ws ε domNest obsSlot f = some c) :
    encodeFocGo fuel' ws ε domNest obsSlot f = some c :=
  (encode_successful_fuel_mono fuel).2.1 fuel' ws ε domNest obsSlot f c hle h

/--
Full mutual fuel monotonicity: successful `encodeICCGo` is stable under
increasing fuel.
-/
def EncodeFuelMonoGoal : Prop :=
  ∀ {Γ : Ctx sig} {A : Object sig.nBases} (fuel fuel' : Nat)
    (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (t : InvTm Γ A) (c : ICCCode Γ A),
    fuel ≤ fuel' →
      encodeICCGo fuel ws ε domNest obsSlot t = some c →
        encodeICCGo fuel' ws ε domNest obsSlot t = some c

theorem EncodeFuelMonoGoal_holds : EncodeFuelMonoGoal (sig := sig) :=
  fun fuel fuel' ws ε domNest obsSlot t c hle h =>
    encodeICCGo_le fuel fuel' ws ε domNest obsSlot t c hle h

/-! ### Computational adequacy (fuel independence / stabilization)

Distinct from semantic totality (`EncodeTotal` on `ValidEncodeFragment`):

* **Computational:** for any term, once fuel is at least the derived bound,
  the `Option` result is stable (including stable structural `none`).
* **Semantic:** valid reference-produced terms return `some code`.

Proved from recursive-call decrease lemmas + the mutual encoder structure.
-/

theorem encodeFuelBranches_lt_case {Γ : Ctx sig} {L R A : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig))
    (hty : e.ty = .coprod L R)
    (n : NegNeu Γ (.coprod L R))
    (tL : InvTm (Γ ▻ L) A) (tR : InvTm (Γ ▻ R) A) :
    encodeFuelBranches (e :: ws) e tL tR <
      encodeFuel (e :: ws) (.case n tL tR) := by
  have hL := encodeFuel_leftCoprod_lt e ws (.split e.origin false) hty n tL tR
  have hR := encodeFuel_leftCoprod_right_lt e ws (.split e.origin true) hty n tL tR
  simp only [encodeFuelBranches, List.tail_cons]
  exact (Nat.max_lt).mpr ⟨hL, hR⟩

theorem encodeFuelBranches_le_unit_eta {Γ : Ctx sig} {L R : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig))
    (hty : e.ty = .coprod L R)
    {n : Nat} (hle : encodeFuel (e :: ws) (.unit (Γ := Γ)) ≤ n + 1) :
    encodeFuelBranches (e :: ws) e
      (.unit : InvTm (Γ ▻ L) .unit)
      (.unit : InvTm (Γ ▻ R) .unit) ≤ n := by
  have hpushL := worklistWeight_pushPos_le ws (.split e.origin false) L
  have hpushR := worklistWeight_pushPos_le ws (.split e.origin true) R
  have hLp := objectWeight_pos L
  have hRp := objectWeight_pos R
  simp only [encodeFuelBranches, List.tail_cons, encodeFuel, encodeMeasure,
    InvTm.size, InvTm.posPushBudget, worklistWeight_cons, hty, objectWeight] at *
  omega

/--
Forced-rule head equality from a `leftCoprod` result.
-/
theorem forcedRule_leftCoprod_ty {e : PosEntry sig} {ws : List (PosEntry sig)}
    {A L R : Object sig.nBases}
    (h : forcedRule (e :: ws) A = .leftCoprod e L R) :
    e.ty = .coprod L R := by
  simp [forcedRule] at h
  split at h <;> try contradiction
  next L0 R0 heq =>
    injection h with _ hL hR
    subst hL; subst hR
    exact heq

theorem forcedRule_leftCoprod_entry {e e' : PosEntry sig} {ws : List (PosEntry sig)}
    {A L R : Object sig.nBases}
    (h : forcedRule (e' :: ws) A = .leftCoprod e L R) :
    e = e' := by
  simp [forcedRule] at h
  split at h <;> try contradiction
  next L0 R0 =>
    injection h with he _ _
    exact he.symm

theorem forcedRule_nil_not_moveStable {A : Object sig.nBases} {e : PosEntry sig}
    (h : forcedRule ([] : List (PosEntry sig)) A = .moveStable e) : False := by
  simp [forcedRule] at h
  split at h <;> cases h

theorem forcedRule_nil_not_leftCoprod {A L R : Object sig.nBases} {e : PosEntry sig}
    (h : forcedRule ([] : List (PosEntry sig)) A = .leftCoprod e L R) : False := by
  simp [forcedRule] at h
  split at h <;> cases h

theorem forcedRule_rightUnit_ty {ws : List (PosEntry sig)} {A : Object sig.nBases}
    (h : forcedRule ws A = .rightUnit) : A = .unit := by
  cases ws with
  | nil =>
      simp [forcedRule] at h
      split at h <;> try (cases h)
      rfl
  | cons e ws' =>
      simp [forcedRule] at h
      split at h <;> cases h

theorem forcedRule_rightProd_ty {ws : List (PosEntry sig)} {A L R : Object sig.nBases}
    (h : forcedRule ws A = .rightProd L R) : A = .prod L R := by
  cases ws with
  | nil =>
      simp [forcedRule] at h
      split at h <;> (try cases h); try rfl
  | cons e ws' =>
      simp [forcedRule] at h
      split at h <;> cases h

theorem forcedRule_rightExp_ty {ws : List (PosEntry sig)} {A Arg Ret : Object sig.nBases}
    (h : forcedRule ws A = .rightExp Arg Ret) : A = .exp Arg Ret := by
  cases ws with
  | nil =>
      simp [forcedRule] at h
      split at h <;> (try cases h); try rfl
  | cons e ws' =>
      simp [forcedRule] at h
      split at h <;> cases h

/--
Step-irrelevance: one extra fuel unit is a no-op once the derived bound is met.
-/
theorem encode_step_irrelevance (n : Nat) :
    (∀ {Γ : Ctx sig} {A : Object sig.nBases}
      (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
      (domNest obsSlot : Nat) (t : InvTm Γ A),
      encodeFuel ws t ≤ n →
        encodeICCGo (n + 1) ws ε domNest obsSlot t =
          encodeICCGo n ws ε domNest obsSlot t) ∧
    (∀ {Γ : Ctx sig} {A : Object sig.nBases}
      (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
      (domNest obsSlot : Nat) (f : FocTm Γ A),
      encodeFuelFoc ws f + 1 ≤ n →
        encodeFocGo (n + 1) ws ε domNest obsSlot f =
          encodeFocGo n ws ε domNest obsSlot f) ∧
    (∀ {Γ : Ctx sig} {A L R : Object sig.nBases}
      (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
      (domNest obsSlot : Nat) (e : PosEntry sig)
      (tL : InvTm (Γ ▻ L) A) (tR : InvTm (Γ ▻ R) A),
      encodeFuelBranches (ws := ws) e tL tR ≤ n →
        encodeLeftCoprodBranches (n + 1) ws ε domNest obsSlot e tL tR =
          encodeLeftCoprodBranches n ws ε domNest obsSlot e tL tR) := by
  induction n with
  | zero =>
      refine ⟨?go0, ?foc0, ?cop0⟩
      · intro Γ A ws ε domNest obsSlot t hle
        exact absurd hle (Nat.not_le_of_gt (encodeFuel_pos ws t))
      · intro Γ A ws ε domNest obsSlot f hle
        have hpos : 0 < encodeFuelFoc ws f + 1 := by
          cases f with
          | pos p =>
              cases p with
              | done p =>
                  simp only [encodeFuelFoc, FocTm.posPushBudget, FocTm.size]
                  have : 0 < PosNeu.size p + 1 := Nat.succ_pos _
                  omega
          | neg n =>
              cases n with
              | done n =>
                  simp only [encodeFuelFoc, FocTm.posPushBudget, FocTm.size]
                  have : 0 < NegNeu.size n + 1 := Nat.succ_pos _
                  omega
          | letPos n t =>
              simp only [encodeFuelFoc, FocTm.posPushBudget, FocTm.size]
              omega
          | sat s =>
              cases s with
              | mk _ t =>
                  simp only [encodeFuelFoc, FocTm.posPushBudget, FocTm.size]
                  have := encodeFuel_pos ws t
                  simp only [encodeFuel] at this
                  omega
        exact absurd hle (Nat.not_le_of_gt hpos)
      · intro Γ A L R ws ε domNest obsSlot e tL tR hle
        simp only [encodeFuelBranches] at hle
        have hL := encodeFuel_pos (pushPos ws.tail (.split e.origin false) L) tL
        exact absurd hle (Nat.not_le_of_gt (Nat.lt_of_lt_of_le hL (Nat.le_max_left _ _)))
  | succ n ih =>
      rcases ih with ⟨ihGo, ihFoc, ihCop⟩
      -- Prove `go` first so `foc`/`cop` can reuse it at bound `n+1`
      -- (branch children are only known ≤ `n+1`, not necessarily ≤ `n`).
      have go : ∀ {Γ : Ctx sig} {A : Object sig.nBases}
          (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
          (domNest obsSlot : Nat) (t : InvTm Γ A),
          encodeFuel ws t ≤ n + 1 →
            encodeICCGo (n + 1 + 1) ws ε domNest obsSlot t =
              encodeICCGo (n + 1) ws ε domNest obsSlot t := by
        intro Γ A ws ε domNest obsSlot t hle
        cases hfr : forcedRule ws A with
        | moveStable e =>
            cases ws with
            | nil => exact (forcedRule_nil_not_moveStable hfr).elim
            | cons e' ws' =>
                have he : e = e' := by
                  simp [forcedRule] at hfr
                  split at hfr <;> try contradiction
                  · cases hfr; rfl
                  · cases hfr; rfl
                subst he
                have hle' : encodeFuel ws' t ≤ n :=
                  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
                    (encodeFuel_moveStable_lt e ws' t) hle)
                rw [encodeICCGo_moveStable_eq (n+1) _ ε domNest obsSlot t e hfr]
                rw [encodeICCGo_moveStable_eq n _ ε domNest obsSlot t e hfr]
                exact ihGo ws' ε domNest obsSlot t hle'
        | leftNever e =>
            cases t with
            | abort n' =>
                rw [encodeICCGo_leftNever_abort (n+1) ws ε domNest obsSlot n' e hfr,
                  encodeICCGo_leftNever_abort n ws ε domNest obsSlot n' e hfr]
            | unit => unfold encodeICCGo; simp only [hfr]
            | pair _ _ => unfold encodeICCGo; simp only [hfr]
            | lam _ => unfold encodeICCGo; simp only [hfr]
            | case _ _ _ => unfold encodeICCGo; simp only [hfr]
            | foc _ => unfold encodeICCGo; simp only [hfr]
        | rightUnit =>
            have hA := forcedRule_rightUnit_ty hfr
            subst A
            cases t with
            | unit =>
                rw [encodeICCGo_rightUnit_unit (n+1) ws ε domNest obsSlot hfr,
                  encodeICCGo_rightUnit_unit n ws ε domNest obsSlot hfr]
            | case _ _ _ => unfold encodeICCGo; simp only [hfr, peelUnit]
            | abort _ => unfold encodeICCGo; simp only [hfr, peelUnit]
            | foc _ => unfold encodeICCGo; simp only [hfr, peelUnit]
        | rightProd L R =>
            have hA := forcedRule_rightProd_ty hfr
            subst A
            cases t with
            | pair t₁ t₂ =>
                have hle1 : encodeFuel ws t₁ ≤ n :=
                  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
                    (encodeFuel_pair_fst_lt ws t₁ t₂) hle)
                have hle2 : encodeFuel ws t₂ ≤ n :=
                  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
                    (encodeFuel_pair_snd_lt ws t₁ t₂) hle)
                rw [encodeICCGo_pair_rightProd (n+1) ws ε domNest obsSlot t₁ t₂ hfr,
                  encodeICCGo_pair_rightProd n ws ε domNest obsSlot t₁ t₂ hfr,
                  ihGo ws ε domNest obsSlot t₁ hle1,
                  ihGo ws ε domNest obsSlot t₂ hle2]
            | foc f =>
                have hFoc : encodeFuelFoc ws f + 1 ≤ n := by
                  have := encodeFuel_focus_eq ws f
                  simp only [encodeFuel] at hle this; omega
                rw [encodeICCGo_foc_rightProd (n+1) ws ε domNest obsSlot f hfr,
                  encodeICCGo_foc_rightProd n ws ε domNest obsSlot f hfr,
                  ihFoc ws ε domNest obsSlot f hFoc]
            | case _ _ _ => unfold encodeICCGo; simp only [hfr, peelPair]
            | abort _ => unfold encodeICCGo; simp only [hfr, peelPair]
        | rightExp Arg Ret =>
            have hA := forcedRule_rightExp_ty hfr
            subst A
            cases t with
            | lam body =>
                have hle' : encodeFuel (pushPos ws (.dom (sig := sig) domNest) Arg)
                    body ≤ n :=
                  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
                    (encodeFuel_lam_lt ws (.dom (sig := sig) domNest) body) hle)
                rw [encodeICCGo_lam_rightExp (n+1) ws ε domNest obsSlot body hfr,
                  encodeICCGo_lam_rightExp n ws ε domNest obsSlot body hfr,
                  ihGo _ _ (domNest+1) obsSlot body hle']
            | foc f =>
                have hFoc : encodeFuelFoc ws f + 1 ≤ n := by
                  have := encodeFuel_focus_eq ws f
                  simp only [encodeFuel] at hle this; omega
                rw [encodeICCGo_foc_rightExp (n+1) ws ε domNest obsSlot f hfr,
                  encodeICCGo_foc_rightExp n ws ε domNest obsSlot f hfr,
                  ihFoc ws ε domNest obsSlot f hFoc]
            | case _ _ _ => unfold encodeICCGo; simp only [hfr, peelLam]
            | abort _ => unfold encodeICCGo; simp only [hfr, peelLam]
        | leftCoprod e L R =>
            cases ws with
            | nil => exact (forcedRule_nil_not_leftCoprod hfr).elim
            | cons e' ws' =>
                have he := forcedRule_leftCoprod_entry hfr
                subst he
                have hty := forcedRule_leftCoprod_ty hfr
                -- Shared peel; discharge via Branches IH when bound ≤ n
                unfold encodeICCGo
                simp only [hfr]
                split
                · next L' R' n' tL tR hpeel =>
                    split
                    · next hL =>
                        split
                        · next hR =>
                            have hBr : encodeFuelBranches (e :: ws') e
                                (hL ▸ tL) (hR ▸ tR) ≤ n := by
                              have hpeelCast :
                                  peelCaseOuter ε e.origin t =
                                    some ⟨L, R, hR ▸ hL ▸ n', hL ▸ tL, hR ▸ tR⟩ := by
                                cases hL; cases hR; exact hpeel
                              have hlt := encodeFuelBranches_lt_of_peel e ws' hty ε t
                                (hR ▸ hL ▸ n') (hL ▸ tL) (hR ▸ tR) hpeelCast
                              exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hle)
                            exact ihCop (e :: ws') ε domNest obsSlot e
                              (hL ▸ tL) (hR ▸ tR) hBr
                        · rfl
                    · rfl
                · next =>
                    split
                    · next =>
                        -- unit left-η
                        split
                        · next ty x hfind =>
                            split
                            · next hty' =>
                                split
                                · next hit =>
                                    have hBr := encodeFuelBranches_le_unit_eta e ws' hty hle
                                    exact ihCop (e :: ws') ε domNest obsSlot e
                                      .unit .unit hBr
                                · rfl
                            · rfl
                        · rfl
                    · rfl
        | focus =>
            cases t with
            | foc f =>
                have hFoc : encodeFuelFoc ws f + 1 ≤ n := by
                  have := encodeFuel_focus_eq ws f
                  simp only [encodeFuel] at hle this; omega
                rw [encodeICCGo_focus_eq (n+1) ws ε domNest obsSlot f hfr,
                  encodeICCGo_focus_eq n ws ε domNest obsSlot f hfr]
                exact ihFoc ws ε domNest obsSlot f hFoc
            | unit => unfold encodeICCGo; simp only [hfr]
            | pair _ _ => unfold encodeICCGo; simp only [hfr]
            | lam _ => unfold encodeICCGo; simp only [hfr]
            | case _ _ _ => unfold encodeICCGo; simp only [hfr]
            | abort _ => unfold encodeICCGo; simp only [hfr]
      have foc : ∀ {Γ : Ctx sig} {A : Object sig.nBases}
          (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
          (domNest obsSlot : Nat) (f : FocTm Γ A),
          encodeFuelFoc ws f + 1 ≤ n + 1 →
            encodeFocGo (n + 1 + 1) ws ε domNest obsSlot f =
              encodeFocGo (n + 1) ws ε domNest obsSlot f := by
        intro Γ A ws ε domNest obsSlot f hle
        cases f with
        | pos p => cases p with | done p => simp [encodeFocGo]
        | neg n' => cases n' with | done n' => simp [encodeFocGo]
        | letPos n' t =>
            rename_i P
            -- `encodeFocGo (n+2)` calls `encodeICCGo (n+1)`; need IH at bound `n`.
            have hChild : encodeFuel (pushPos ws (.obs (sig := sig) obsSlot) P) t ≤ n := by
              have hlePos := encodeFuel_letPos_le ws (.obs (sig := sig) obsSlot) n' t
              simp only [encodeFuelFoc, FocTm.posPushBudget, FocTm.size,
                encodeFuel, InvTm.size, InvTm.posPushBudget] at hle hlePos ⊢
              omega
            simp [encodeFocGo]
            rw [ihGo _ _ domNest (obsSlot + 1) t hChild]
        | sat s =>
            cases s with
            | mk sched t =>
                have hChild : encodeFuel ws t ≤ n := by
                  have hsat := encodeFuel_sat_le ws sched t
                  simp only [encodeFuelFoc, FocTm.posPushBudget, FocTm.size,
                    encodeFuel, InvTm.size, InvTm.posPushBudget] at hle hsat ⊢
                  omega
                simp [encodeFocGo]
                rw [ihGo ws ε domNest obsSlot t hChild]
      have cop : ∀ {Γ : Ctx sig} {A L R : Object sig.nBases}
          (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
          (domNest obsSlot : Nat) (e : PosEntry sig)
          (tL : InvTm (Γ ▻ L) A) (tR : InvTm (Γ ▻ R) A),
          encodeFuelBranches (ws := ws) e tL tR ≤ n + 1 →
            encodeLeftCoprodBranches (n + 1 + 1) ws ε domNest obsSlot e tL tR =
              encodeLeftCoprodBranches (n + 1) ws ε domNest obsSlot e tL tR := by
        intro Γ A L R ws ε domNest obsSlot e tL tR hle
        rw [encodeLeftCoprodBranches_unfold,
          encodeLeftCoprodBranches_unfold (fuel := n + 1)]
        have hL : encodeFuel (pushPos ws.tail (.split e.origin false) L) tL ≤ n + 1 := by
          simp only [encodeFuelBranches] at hle; omega
        have hR : encodeFuel (pushPos ws.tail (.split e.origin true) R) tR ≤ n + 1 := by
          simp only [encodeFuelBranches] at hle; omega
        rw [go _ _ domNest obsSlot tL hL, go _ _ domNest obsSlot tR hR]
      exact ⟨go, foc, cop⟩

/-- Telescope step-irrelevance to full independence above the derived bound. -/
theorem encodeICCGo_independent {Γ : Ctx sig} {A : Object sig.nBases}
    (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (t : InvTm Γ A) (g : Nat)
    (hle : encodeFuel ws t ≤ g) :
    encodeICCGo g ws ε domNest obsSlot t =
      encodeICCGo (encodeFuel ws t) ws ε domNest obsSlot t := by
  induction hle with
  | refl => rfl
  | step h ih =>
      have := (encode_step_irrelevance _).1 ws ε domNest obsSlot t h
      exact this.trans ih

theorem encodeFocGo_independent {Γ : Ctx sig} {A : Object sig.nBases}
    (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (f : FocTm Γ A) (g : Nat)
    (hle : encodeFuelFoc ws f + 1 ≤ g) :
    encodeFocGo g ws ε domNest obsSlot f =
      encodeFocGo (encodeFuelFoc ws f + 1) ws ε domNest obsSlot f := by
  induction hle with
  | refl => rfl
  | step h ih =>
      have := (encode_step_irrelevance _).2.1 ws ε domNest obsSlot f h
      exact this.trans ih

theorem encodeLeftCoprodBranches_independent {Γ : Ctx sig} {A L R : Object sig.nBases}
    (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (e : PosEntry sig)
    (tL : InvTm (Γ ▻ L) A) (tR : InvTm (Γ ▻ R) A) (g : Nat)
    (hle : encodeFuelBranches (ws := ws) e tL tR ≤ g) :
    encodeLeftCoprodBranches g ws ε domNest obsSlot e tL tR =
      encodeLeftCoprodBranches (encodeFuelBranches (ws := ws) e tL tR)
        ws ε domNest obsSlot e tL tR := by
  induction hle with
  | refl => rfl
  | step h ih =>
      have := (encode_step_irrelevance _).2.2 ws ε domNest obsSlot e tL tR h
      exact this.trans ih

/--
Full `Option` equality of top-level encodes from fuel-independent Go agreement,
via stabilization at `F := max (encodeFuel t) (encodeFuel u)`.
-/
theorem encodeICC_eq_of_go_eq {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (ws : List (PosEntry sig))
    (hws : OriginEnv.posWorklist ε = ws)
    (t u : InvTm Γ A)
    (hgo : ∀ fuel, encodeICCGo fuel ws ε 0 0 t =
      encodeICCGo fuel ws ε 0 0 u) :
    encodeICC ε t = encodeICC ε u := by
  unfold encodeICC
  rw [hws]
  let ft := encodeFuel ws t
  let fu := encodeFuel ws u
  let F := max ft fu
  have ht : encodeICCGo ft ws ε 0 0 t = encodeICCGo F ws ε 0 0 t :=
    (encodeICCGo_independent ws ε 0 0 t F (Nat.le_max_left _ _)).symm
  have hu : encodeICCGo fu ws ε 0 0 u = encodeICCGo F ws ε 0 0 u :=
    (encodeICCGo_independent ws ε 0 0 u F (Nat.le_max_right _ _)).symm
  exact ht.trans ((hgo F).trans hu.symm)

/-- `EncodeIccStep` from Go agreement alone (domain from stabilization). -/
theorem EncodeIccStep.of_go_eq {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (ws : List (PosEntry sig))
    (hws : OriginEnv.posWorklist ε = ws)
    (t u : InvTm Γ A)
    (hgo : ∀ fuel, encodeICCGo fuel ws ε 0 0 t =
      encodeICCGo fuel ws ε 0 0 u) :
    EncodeIccStep ε t u :=
  EncodeIccStep.of_option_eq ε (encodeICC_eq_of_go_eq ε ws hws t u hgo)

/-! ### Max-fuel lift from Go agreement -/

/--
When both sides encode successfully, fuel-independent Go agreement implies
equal codes. Lift each result to `F := max (encodeFuel t) (encodeFuel u)`,
agree there, then conclude `c = d`.
-/
theorem encodeICC_code_eq_of_go_eq {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (ws : List (PosEntry sig))
    (hws : OriginEnv.posWorklist ε = ws)
    (t u : InvTm Γ A) (c d : ICCCode Γ A)
    (ht : encodeICC ε t = some c)
    (hu : encodeICC ε u = some d)
    (hgo : ∀ fuel, encodeICCGo fuel ws ε 0 0 t =
      encodeICCGo fuel ws ε 0 0 u) :
    c = d := by
  unfold encodeICC at ht hu
  rw [hws] at ht hu
  let ft := encodeFuel ws t
  let fu := encodeFuel ws u
  let F := max ft fu
  have hcF := encodeICCGo_le ft F ws ε 0 0 t c (Nat.le_max_left _ _) ht
  have hdF := encodeICCGo_le fu F ws ε 0 0 u d (Nat.le_max_right _ _) hu
  have hEq : encodeICCGo F ws ε 0 0 t = encodeICCGo F ws ε 0 0 u := hgo F
  exact Option.some.inj (hcF.symm.trans (hEq.trans hdF))

/--
`EncodeIccStep` from Go agreement when encodability is already synchronized
(e.g. both sides of a `ValidEncodeFragment` obligation, or an explicit domain
proof). Codes agree whenever `t` encodes, by lifting to the common max fuel.
-/
theorem EncodeIccStep.of_go_eq_of_domain {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (ws : List (PosEntry sig))
    (hws : OriginEnv.posWorklist ε = ws)
    (t u : InvTm Γ A)
    (hdom : EncodableICC ε t ↔ EncodableICC ε u)
    (hgo : ∀ fuel, encodeICCGo fuel ws ε 0 0 t =
      encodeICCGo fuel ws ε 0 0 u) :
    EncodeIccStep ε t u := by
  refine ⟨hdom, fun ht => ?_⟩
  obtain ⟨c, hc⟩ := EncodableICC.exists ht
  have hu : EncodableICC ε u := hdom.mp ht
  obtain ⟨d, hd⟩ := EncodableICC.exists hu
  have hcd := encodeICC_code_eq_of_go_eq ε ws hws t u c d hc hd hgo
  exact hc.trans (hcd ▸ hd.symm)

/--
One-sided domain transfer along Go agreement when `encodeFuel t ≤ encodeFuel u`.
-/
theorem EncodableICC.of_go_eq_of_fuel_le {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (ws : List (PosEntry sig))
    (hws : OriginEnv.posWorklist ε = ws)
    (t u : InvTm Γ A)
    (hle : encodeFuel ws t ≤ encodeFuel ws u)
    (hgo : ∀ fuel, encodeICCGo fuel ws ε 0 0 t =
      encodeICCGo fuel ws ε 0 0 u)
    (ht : EncodableICC ε t) :
    EncodableICC ε u := by
  obtain ⟨c, hc⟩ := EncodableICC.exists ht
  unfold encodeICC at hc
  rw [hws] at hc
  have hc' := encodeICCGo_le (encodeFuel ws t) (encodeFuel ws u) ws ε 0 0 t c hle hc
  have hu : encodeICCGo (encodeFuel ws u) ws ε 0 0 u = some c :=
    (hgo (encodeFuel ws u)) ▸ hc'
  exact EncodableICC.of_eq_some (by unfold encodeICC; rw [hws]; exact hu)

/-! ### Commute-rule `EncodeIccStep` packaging (Go agreement + max fuel) -/

theorem encodeIccStep_case_pair {Γ : Ctx sig} {A B C D : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (x : Var Γ (.coprod A B))
    (t₁ : InvTm (Γ ▻ A) C) (t₂ : InvTm (Γ ▻ B) C)
    (u₁ : InvTm (Γ ▻ A) D) (u₂ : InvTm (Γ ▻ B) D)
    (hws : OriginEnv.posWorklist ε = e :: ws)
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin) :
    EncodeIccStep ε
      (.case (.var x) (.pair t₁ u₁) (.pair t₂ u₂))
      (.pair (.case (.var x) t₁ t₂) (.case (.var x) u₁ u₂)) :=
  EncodeIccStep.of_go_eq ε (e :: ws) hws _ _
    (fun fuel => encodeICCGo_case_pair_any fuel e ws ε 0 0 x t₁ t₂ u₁ u₂ hty hit)

theorem encodeIccStep_case_lam {Γ : Ctx sig} {A B Arg Ret : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (x : Var Γ (.coprod A B))
    (t : InvTm (Γ ▻ A ▻ Arg) Ret) (u : InvTm (Γ ▻ B ▻ Arg) Ret)
    (hws : OriginEnv.posWorklist ε = e :: ws)
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin) :
    EncodeIccStep ε
      (.case (.var x) (.lam t) (.lam u))
      (.lam (.case (NegNeu.weaken (B := Arg) (.var x))
        (InvTm.rename Rename.exchange t)
        (InvTm.rename Rename.exchange u))) :=
  EncodeIccStep.of_go_eq ε (e :: ws) hws _ _
    (fun fuel => encodeICCGo_case_lam_any fuel e ws ε 0 0 x t u hty hit)

theorem encodeIccStep_case_case {Γ : Ctx sig} {A B C D E : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (xs : Var Γ (.coprod A B)) (xt : Var Γ (.coprod C D))
    (t₁ : InvTm (Γ ▻ A ▻ C) E) (t₂ : InvTm (Γ ▻ A ▻ D) E)
    (u₁ : InvTm (Γ ▻ B ▻ C) E) (u₂ : InvTm (Γ ▻ B ▻ D) E)
    (hws : OriginEnv.posWorklist ε = e :: ws)
    (hty : e.ty = .coprod A B) (hit : ε xs = e.origin)
    (miss : (ε xt == e.origin) = false) :
    EncodeIccStep ε
      (.case (.var xs)
        (.case (NegNeu.weaken (B := A) (.var xt)) t₁ t₂)
        (.case (NegNeu.weaken (B := B) (.var xt)) u₁ u₂))
      (.case (.var xt)
        (.case (NegNeu.weaken (B := C) (.var xs))
          (InvTm.rename Rename.exchange t₁)
          (InvTm.rename Rename.exchange u₁))
        (.case (NegNeu.weaken (B := D) (.var xs))
          (InvTm.rename Rename.exchange t₂)
          (InvTm.rename Rename.exchange u₂))) :=
  EncodeIccStep.of_go_eq ε (e :: ws) hws _ _
    (fun fuel =>
      encodeICCGo_case_case_any fuel e ws ε 0 0 xs xt t₁ t₂ u₁ u₂ hty hit miss)

theorem encodeIccStep_case_unit {Γ : Ctx sig} {A B : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (x : Var Γ (.coprod A B))
    (hws : OriginEnv.posWorklist ε = e :: ws)
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin)
    (hfind : OriginEnv.find? ε e.origin = some ⟨.coprod A B, x⟩) :
    EncodeIccStep ε (.case (.var x) .unit .unit) (.unit (Γ := Γ)) :=
  EncodeIccStep.of_go_eq ε (e :: ws) hws _ _
    (fun fuel =>
      encodeICCGo_case_unit_any fuel e ws ε 0 0 x hty hit hfind)

/-! ### `case_letPos` / `sat_body` packaging (invariance substrate)

`ICCEq.sat_body` unwraps `.foc (.sat _)` to the body. Encode of sat under
`forcedRule = .focus` yields `.foc (.body c)` while encode of the body yields
`c`, so codes are **not** equal: `EncodeIccStep` does **not** hold for
`sat_body` whenever the body encodes (proved below). Bridging via
`ICCEq.sat_body` alone cannot repair this without changing encode (sticky:
drop the `.foc (.body _)` shell) or weakening `EncodeIccStep`.

`ICCEq.case_letPos` peel agreement and Go/`EncodeIccStep` packaging are landed
below (`encodeIccStep_case_letPos`).
-/

theorem encodeIccStep_case_letPos {Γ : Ctx sig} {A B P C : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (x : Var Γ (.coprod A B)) (n : NegNeu Γ P)
    (tL : InvTm (Γ ▻ P ▻ A) C) (tR : InvTm (Γ ▻ P ▻ B) C)
    (hws : OriginEnv.posWorklist ε = e :: ws)
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin) :
    EncodeIccStep ε
      (.foc (.letPos n (.case (NegNeu.weaken (B := P) (.var x)) tL tR)))
      (.case (.var x)
        (.foc (.letPos (NegNeu.weaken (B := A) n)
          (InvTm.rename Rename.exchange tL)))
        (.foc (.letPos (NegNeu.weaken (B := B) n)
          (InvTm.rename Rename.exchange tR)))) :=
  EncodeIccStep.of_go_eq ε (e :: ws) hws _ _
    (fun fuel => encodeICCGo_case_letPos_any fuel e ws ε 0 0 x n tL tR hty hit)

/-- Sat unwrap at the Go level under `focus` (fuel shifted by the sat shell). -/
theorem encodeICCGo_foc_sat_eq {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (s : Schedule sig.nBases) (t : InvTm Γ A)
    (hfr : forcedRule ws A = .focus) :
    encodeICCGo (fuel + 2) ws ε domNest obsSlot (.foc (.sat (.mk s t))) =
      match encodeICCGo fuel ws ε domNest obsSlot t with
      | some c => some (.foc (.body c))
      | none => none :=
  encodeICCGo_foc_sat fuel ws ε domNest obsSlot s t hfr

/--
Code relationship for `ICCEq.sat_body` under `focus`: sat encodes to
`.foc (.body c)` when the body encodes to `c`. Not an `EncodeIccStep`
(wrapper mismatch).
-/
theorem encodeICCGo_sat_body_codes {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (s : Schedule sig.nBases) (t : InvTm Γ A)
    (hfr : forcedRule ws A = .focus) :
    encodeICCGo (fuel + 2) ws ε domNest obsSlot (.foc (.sat (.mk s t))) =
      (encodeICCGo fuel ws ε domNest obsSlot t).map fun c => .foc (.body c) := by
  rw [encodeICCGo_foc_sat_eq fuel ws ε domNest obsSlot s t hfr]
  cases encodeICCGo fuel ws ε domNest obsSlot t <;> rfl

/-!
`EncodeIccStep` for `ICCEq.sat_body` is **blocked** under the current encoder:
`encodeICCGo_sat_body_codes` shows sat maps to `.foc (.body c)` while the body
maps to `c`. Packaging as `EncodeIccStep` would require sticky encode erasure
(return `c` for sat) or a weaker step relation. Not claimed.
-/

/-! ### EncodeTotal base witnesses -/

theorem encode_unit_nilWorklist {Γ : Ctx sig} (ε : OriginEnv Γ)
    (hws : OriginEnv.posWorklist ε = []) :
    ∃ c, encodeICC ε (.unit (Γ := Γ)) = some c :=
  ⟨.unit, encodeICC_unit_of_nilWorklist ε hws⟩

theorem encode_abort_leftNever {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (n : NegNeu Γ .never)
    (hws : OriginEnv.posWorklist ε = e :: ws) (hty : e.ty = .never) :
    ∃ c, encodeICC ε (.abort (A := A) n) = some c :=
  ⟨.abort e.origin, encodeICC_abort_leftNever ε e ws n hws hty⟩

theorem encodable_unit_nilWorklist {Γ : Ctx sig} (ε : OriginEnv Γ)
    (hws : OriginEnv.posWorklist ε = []) :
    EncodableICC ε (.unit (Γ := Γ)) :=
  EncodableICC.of_eq_some (encodeICC_unit_of_nilWorklist ε hws)

theorem encodable_abort_leftNever {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (n : NegNeu Γ .never)
    (hws : OriginEnv.posWorklist ε = e :: ws) (hty : e.ty = .never) :
    EncodableICC ε (.abort (A := A) n) :=
  EncodableICC.of_eq_some (encodeICC_abort_leftNever ε e ws n hws hty)

/-! ### EncodeReady: syntactic totality precondition

`WellInv` alone is not enough: unique-order encode can return structural `none`
when the term is not aligned with `forcedRule` (e.g. `abort` under empty
worklist, or an unprocessed coprod head that `peelCaseOuter` cannot expose).

`EncodeReady` is the stronger alignment predicate. Totality on
`ValidEncodeFragment` reduces to inhabiting `EncodeReady` for
`OriginEnv.ofHyps` (and its weakenings under `pushPos`).
-/

/-! ### EncodeReady (defined in `ICCCode`)

`EncodeReady` / `EncodeReadyFoc` live next to `encodeICC` so the valid-fragment
certificate can mention readiness without an import cycle.
-/

private theorem peelCaseOuter_unit_eq_none {Γ : Ctx sig}
    (ε : OriginEnv Γ) (o : Origin sig) :
    peelCaseOuter ε o (.unit (Γ := Γ)) = none := by
  simp [peelCaseOuter, InvTm.size, peelCaseOuterGo]

/-- Successful Go under `EncodeReady`, at the derived fuel bound. -/
theorem encodeReady_go_some {Γ : Ctx sig} {A : Object sig.nBases}
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {domNest obsSlot : Nat} {t : InvTm Γ A}
    (h : EncodeReady ws ε domNest obsSlot t) :
    ∃ c, encodeICCGo (encodeFuel ws t) ws ε domNest obsSlot t = some c := by
  revert A ws ε domNest obsSlot t
  refine EncodeReady.rec
    (motive_1 := fun {Γ} ws ε domNest obsSlot {A} t _ =>
      ∃ c, encodeICCGo (encodeFuel ws t) ws ε domNest obsSlot t = some c)
    (motive_2 := fun {Γ} ws ε domNest obsSlot {A} f _ =>
      ∃ c, encodeFocGo (encodeFuelFoc ws f + 1) ws ε domNest obsSlot f = some c)
    ?moveStable ?leftNever ?rightUnit ?rightProd_pair ?rightProd_foc
    ?rightExp_lam ?rightExp_foc ?leftCoprod_peel ?leftCoprod_unitEta ?focus
    ?pos ?neg ?letPos ?sat
  case moveStable =>
    intro Γ A e ws ε domNest obsSlot t hfr _ ih
    obtain ⟨c, hc⟩ := ih
    have hpos := encodeFuel_pos (e :: ws) t
    obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hle : encodeFuel ws t ≤ fuel := by
      have := encodeFuel_moveStable_lt e ws t; omega
    have hc' := encodeICCGo_le (encodeFuel ws t) fuel ws ε domNest obsSlot t c hle hc
    refine ⟨c, ?_⟩
    simp only [hm]
    rw [encodeICCGo_moveStable_eq fuel (e :: ws) ε domNest obsSlot t e hfr]
    simpa [List.tail_cons] using hc'
  case leftNever =>
    intro Γ A e ws ε domNest obsSlot n hty
    have hpos := encodeFuel_pos (e :: ws) (.abort (A := A) n)
    obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    refine ⟨.abort e.origin, ?_⟩
    simp only [hm]
    exact encodeICCGo_abort_leftNever fuel e ws ε domNest obsSlot n hty
  case rightUnit =>
    intro Γ ws ε domNest obsSlot hfr
    have hpos := encodeFuel_pos ws (.unit (Γ := Γ))
    obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    refine ⟨.unit, ?_⟩
    simp only [hm]
    exact encodeICCGo_rightUnit_unit fuel ws ε domNest obsSlot hfr
  case rightProd_pair =>
    intro Γ L R ws ε domNest obsSlot t u hfr _ _ iht ihu
    obtain ⟨c₁, hc₁⟩ := iht
    obtain ⟨c₂, hc₂⟩ := ihu
    have hpos := encodeFuel_pos ws (.pair t u)
    obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hle1 : encodeFuel ws t ≤ fuel := by
      have := encodeFuel_pair_fst_lt ws t u; omega
    have hle2 : encodeFuel ws u ≤ fuel := by
      have := encodeFuel_pair_snd_lt ws t u; omega
    have hc₁' := encodeICCGo_le _ fuel ws ε domNest obsSlot t c₁ hle1 hc₁
    have hc₂' := encodeICCGo_le _ fuel ws ε domNest obsSlot u c₂ hle2 hc₂
    refine ⟨.pair c₁ c₂, ?_⟩
    simp only [hm]
    rw [encodeICCGo_pair_rightProd fuel ws ε domNest obsSlot t u hfr, hc₁', hc₂']
  case rightProd_foc =>
    intro Γ L R ws ε domNest obsSlot f hfr _ ihf
    obtain ⟨c, hc⟩ := ihf
    have hpos := encodeFuel_pos ws (.foc f)
    obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hEq := encodeFuel_focus_eq ws f
    have hFoc : encodeFuelFoc ws f + 1 ≤ fuel := by omega
    have hc' := encodeFocGo_le _ fuel ws ε domNest obsSlot f c hFoc hc
    refine ⟨c, ?_⟩
    simp only [hm]
    rw [encodeICCGo_foc_rightProd fuel ws ε domNest obsSlot f hfr]
    simp only [hc']
  case rightExp_lam =>
    intro Γ Arg Ret ws ε domNest obsSlot body hfr _ ihb
    obtain ⟨c, hc⟩ := ihb
    have hpos := encodeFuel_pos ws (.lam body)
    obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hle : encodeFuel (pushPos ws (.dom (sig := sig) domNest) Arg) body ≤ fuel := by
      have := encodeFuel_lam_lt ws (.dom (sig := sig) domNest) body; omega
    have hc' := encodeICCGo_le _ fuel _ _ (domNest + 1) obsSlot body c hle hc
    refine ⟨.lam c, ?_⟩
    simp only [hm]
    rw [encodeICCGo_lam_rightExp fuel ws ε domNest obsSlot body hfr, hc']
  case rightExp_foc =>
    intro Γ Arg Ret ws ε domNest obsSlot f hfr _ ihf
    obtain ⟨c, hc⟩ := ihf
    have hpos := encodeFuel_pos ws (.foc f)
    obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hEq := encodeFuel_focus_eq ws f
    have hFoc : encodeFuelFoc ws f + 1 ≤ fuel := by omega
    have hc' := encodeFocGo_le _ fuel ws ε domNest obsSlot f c hFoc hc
    refine ⟨c, ?_⟩
    simp only [hm]
    rw [encodeICCGo_foc_rightExp fuel ws ε domNest obsSlot f hfr]
    simp only [hc']
  case leftCoprod_peel =>
    intro Γ A L R e ws ε domNest obsSlot n tL tR t hfr hpeel _ _ ihL ihR
    obtain ⟨cL, hcL⟩ := ihL
    obtain ⟨cR, hcR⟩ := ihR
    have hty := forcedRule_leftCoprod_ty hfr
    have hpos := encodeFuel_pos (e :: ws) t
    obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hBrlt := encodeFuelBranches_lt_of_peel e ws hty ε t n tL tR hpeel
    have hLle : encodeFuel (pushPos ws (.split e.origin false) L) tL ≤ fuel := by
      simp only [encodeFuelBranches, List.tail_cons] at hBrlt; omega
    have hRle : encodeFuel (pushPos ws (.split e.origin true) R) tR ≤ fuel := by
      simp only [encodeFuelBranches, List.tail_cons] at hBrlt; omega
    have hcL' := encodeICCGo_le _ fuel _ _ domNest obsSlot tL cL hLle hcL
    have hcR' := encodeICCGo_le _ fuel _ _ domNest obsSlot tR cR hRle hcR
    refine ⟨.case e.origin cL cR, ?_⟩
    simp only [hm]
    have hgo :
        encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot t =
          encodeLeftCoprodBranches fuel (e :: ws) ε domNest obsSlot e tL tR := by
      unfold encodeICCGo
      simp only [hfr, hpeel, dite_eq_ite, ite_true]
    rw [hgo, encodeLeftCoprodBranches_unfold]
    simp only [List.tail_cons, hcL', hcR']
  case leftCoprod_unitEta =>
    intro Γ L R e ws ε domNest obsSlot x hfr hfind hit _ _ ihL ihR
    obtain ⟨cL, hcL⟩ := ihL
    obtain ⟨cR, hcR⟩ := ihR
    have hty := forcedRule_leftCoprod_ty hfr
    have hpos := encodeFuel_pos (e :: ws) (.unit (Γ := Γ))
    obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hBr : encodeFuelBranches (e :: ws) e
        (.unit : InvTm (Γ ▻ L) .unit)
        (.unit : InvTm (Γ ▻ R) .unit) ≤ fuel := by
      have hle : encodeFuel (e :: ws) (.unit (Γ := Γ)) ≤ fuel + 1 := by
        simp only [hm]; exact Nat.le_refl _
      exact encodeFuelBranches_le_unit_eta e ws hty hle
    have hLle : encodeFuel (pushPos ws (.split e.origin false) L)
        (.unit : InvTm (Γ ▻ L) .unit) ≤ fuel := by
      simp only [encodeFuelBranches, List.tail_cons] at hBr; omega
    have hRle : encodeFuel (pushPos ws (.split e.origin true) R)
        (.unit : InvTm (Γ ▻ R) .unit) ≤ fuel := by
      simp only [encodeFuelBranches, List.tail_cons] at hBr; omega
    have hcL' := encodeICCGo_le _ fuel _ _ domNest obsSlot _ cL hLle hcL
    have hcR' := encodeICCGo_le _ fuel _ _ domNest obsSlot _ cR hRle hcR
    refine ⟨.case e.origin cL cR, ?_⟩
    simp only [hm]
    have hgo :
        encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot (.unit (Γ := Γ)) =
          encodeLeftCoprodBranches fuel (e :: ws) ε domNest obsSlot e
            (.unit : InvTm (Γ ▻ L) .unit)
            (.unit : InvTm (Γ ▻ R) .unit) := by
      unfold encodeICCGo
      simp only [hfr, peelCaseOuter_unit_eq_none, hfind, dite_eq_ite, ite_true, hit]
    rw [hgo, encodeLeftCoprodBranches_unfold]
    simp only [List.tail_cons, hcL', hcR']
  case focus =>
    intro Γ A ws ε domNest obsSlot f hfr _ ihf
    obtain ⟨c, hc⟩ := ihf
    have hpos := encodeFuel_pos ws (.foc f)
    obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hEq := encodeFuel_focus_eq ws f
    have hFoc : encodeFuelFoc ws f + 1 ≤ fuel := by omega
    have hc' := encodeFocGo_le _ fuel ws ε domNest obsSlot f c hFoc hc
    refine ⟨c, ?_⟩
    simp only [hm]
    rw [encodeICCGo_focus_eq fuel ws ε domNest obsSlot f hfr]
    exact hc'
  case pos =>
    intro Γ A ws ε domNest obsSlot p
    exact ⟨.foc (.pos p), by simp [encodeFocGo]⟩
  case neg =>
    intro Γ A ws ε domNest obsSlot n
    exact ⟨.foc (.neg n), by simp [encodeFocGo]⟩
  case letPos =>
    intro Γ P A ws ε domNest obsSlot n t _ iht
    obtain ⟨c, hc⟩ := iht
    obtain ⟨fuel, hm⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (Nat.pos_iff_ne_zero.mp (Nat.succ_pos (encodeFuelFoc ws (.letPos n t))))
    have hFuel : encodeFuelFoc ws (.letPos n t) = fuel := by
      have : encodeFuelFoc ws (.letPos n t) + 1 = fuel + 1 := hm
      exact Nat.succ.inj this
    have hle : encodeFuel (pushPos ws (.obs (sig := sig) obsSlot) P) t ≤ fuel := by
      have h1 := encodeFuel_letPos_le ws (.obs (sig := sig) obsSlot) n t
      have h2 := encodeFuel_focus_eq ws (.letPos n t)
      omega
    have hc' := encodeICCGo_le _ fuel _ _ domNest (obsSlot + 1) t c hle hc
    refine ⟨.foc (.letPos (.obs (sig := sig) obsSlot) n c), ?_⟩
    have hgoal :
        encodeFocGo (fuel + 1) ws ε domNest obsSlot (.letPos n t) =
          some (.foc (.letPos (.obs (sig := sig) obsSlot) n c)) := by
      simp [encodeFocGo, hc']
    convert hgoal
  case sat =>
    intro Γ A ws ε domNest obsSlot s t _ iht
    obtain ⟨c, hc⟩ := iht
    obtain ⟨fuel, hm⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (Nat.pos_iff_ne_zero.mp (Nat.succ_pos (encodeFuelFoc ws (.sat (.mk s t)))))
    have hFuel : encodeFuelFoc ws (.sat (.mk s t)) = fuel := by
      have : encodeFuelFoc ws (.sat (.mk s t)) + 1 = fuel + 1 := hm
      exact Nat.succ.inj this
    have hle : encodeFuel ws t ≤ fuel := by
      have h1 := encodeFuel_sat_le ws s t
      have h2 := encodeFuel_focus_eq ws (.sat (.mk s t))
      omega
    have hc' := encodeICCGo_le _ fuel ws ε domNest obsSlot t c hle hc
    refine ⟨.foc (.body c), ?_⟩
    have hgoal :
        encodeFocGo (fuel + 1) ws ε domNest obsSlot (.sat (.mk s t)) =
          some (.foc (.body c)) := by
      simp [encodeFocGo, hc']
    convert hgoal

/-- `EncodeReady` at phase-entry counters implies `EncodableICC`. -/
theorem EncodableICC.of_encodeReady {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (ws : List (PosEntry sig))
    (hws : OriginEnv.posWorklist ε = ws)
    {t : InvTm Γ A}
    (h : EncodeReady ws ε 0 0 t) :
    EncodableICC ε t := by
  obtain ⟨c, hc⟩ := encodeReady_go_some h
  exact EncodableICC.of_eq_some (by
    unfold encodeICC
    rw [hws]
    exact hc)

/-- Concrete code witness from `EncodeReady`. -/
theorem encode_of_encodeReady {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (ws : List (PosEntry sig))
    (hws : OriginEnv.posWorklist ε = ws)
    {t : InvTm Γ A}
    (h : EncodeReady ws ε 0 0 t) :
    ∃ c, encodeICC ε t = some c :=
  EncodableICC.exists (EncodableICC.of_encodeReady ε ws hws h)

/-! ### EncodeReady base introductions -/

theorem encodeReady_unit_nil {Γ : Ctx sig} (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) :
    EncodeReady ([] : List (PosEntry sig)) ε domNest obsSlot (.unit (Γ := Γ)) :=
  .rightUnit rfl

theorem encodeReady_abort_leftNever {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (domNest obsSlot : Nat) (n : NegNeu Γ .never) (hty : e.ty = .never) :
    EncodeReady (e :: ws) ε domNest obsSlot (.abort (A := A) n) :=
  .leftNever hty

theorem encodeReady_foc_pos_nil {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (domNest obsSlot : Nat) (p : PosNeu Γ A)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    EncodeReady ([] : List (PosEntry sig)) ε domNest obsSlot
      (.foc (.pos (.done p))) :=
  .focus hfr (.pos)

theorem encodeReady_foc_neg_nil {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (domNest obsSlot : Nat) (n : NegNeu Γ A)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    EncodeReady ([] : List (PosEntry sig)) ε domNest obsSlot
      (.foc (.neg (.done n))) :=
  .focus hfr (.neg)

/-! ### EncodeIccInvariant packaging (generator fragments) -/

theorem encodeIccStep_refl {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (t : InvTm Γ A) :
    EncodeIccStep ε t t :=
  EncodeIccStep.refl ε t

theorem encodeIccStep_symm {Γ : Ctx sig} {A : Object sig.nBases}
    {ε : OriginEnv Γ} {t u : InvTm Γ A}
    (h : EncodeIccStep ε t u) : EncodeIccStep ε u t :=
  EncodeIccStep.symm h

theorem encodeIccStep_trans {Γ : Ctx sig} {A : Object sig.nBases}
    {ε : OriginEnv Γ} {t u v : InvTm Γ A}
    (htu : EncodeIccStep ε t u) (huv : EncodeIccStep ε u v) :
    EncodeIccStep ε t v :=
  EncodeIccStep.trans htu huv

/-- Pair congruence as `EncodeIccStep` when Go children agree under `rightProd`. -/
theorem encodeIccStep_pair_cong {Γ : Ctx sig} {L R : Object sig.nBases}
    (ε : OriginEnv Γ) (ws : List (PosEntry sig))
    (hws : OriginEnv.posWorklist ε = ws)
    (hfr : forcedRule ws (.prod L R) = .rightProd L R)
    {t₁ t₂ : InvTm Γ L} {u₁ u₂ : InvTm Γ R}
    (ht : ∀ fuel, encodeICCGo fuel ws ε 0 0 t₁ =
      encodeICCGo fuel ws ε 0 0 t₂)
    (hu : ∀ fuel, encodeICCGo fuel ws ε 0 0 u₁ =
      encodeICCGo fuel ws ε 0 0 u₂) :
    EncodeIccStep ε (.pair t₁ u₁) (.pair t₂ u₂) :=
  EncodeIccStep.of_go_eq ε ws hws _ _ fun fuel => by
    cases fuel with
    | zero => simp [encodeICCGo]
    | succ fuel =>
        exact encodeICCGo_pair_cong fuel ws ε 0 0 hfr (ht fuel) (hu fuel)

/-- λ congruence as `EncodeIccStep` when bodies agree under the pushed env. -/
theorem encodeIccStep_lam_cong {Γ : Ctx sig} {Arg Ret : Object sig.nBases}
    (ε : OriginEnv Γ) (ws : List (PosEntry sig))
    (hws : OriginEnv.posWorklist ε = ws)
    (hfr : forcedRule ws (.exp Arg Ret) = .rightExp Arg Ret)
    {t u : InvTm (Γ ▻ Arg) Ret}
    (hbody : ∀ fuel,
      encodeICCGo fuel
        (pushPos ws (.dom (sig := sig) 0) Arg)
        (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) 0))
        1 0 t =
      encodeICCGo fuel
        (pushPos ws (.dom (sig := sig) 0) Arg)
        (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) 0))
        1 0 u) :
    EncodeIccStep ε (.lam t) (.lam u) :=
  EncodeIccStep.of_go_eq ε ws hws _ _ fun fuel => by
    cases fuel with
    | zero => simp [encodeICCGo]
    | succ fuel =>
        exact encodeICCGo_lam_cong fuel ws ε 0 0 hfr (hbody fuel)

/-! ### ValidEncodeFragment → EncodeReady → EncodeTotal -/

/-- Projection: provisional fragment still stashes phase-entry readiness. -/
theorem encodeReady_of_validEncodeFragment {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps) A}
    (h : ValidEncodeFragment t) :
    EncodeReady (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))
      (OriginEnv.ofHyps hyps) 0 0 t :=
  h.ready

/-- Forced-rule classification for a nonempty worklist head. -/
theorem forcedRule_cons_cases (e : PosEntry sig) (ws : List (PosEntry sig))
    (goal : Object sig.nBases) :
    (∃ L R, e.ty = .coprod L R ∧ forcedRule (e :: ws) goal = .leftCoprod e L R) ∨
    (e.ty = .never ∧ forcedRule (e :: ws) goal = .leftNever e) ∨
    forcedRule (e :: ws) goal = .moveStable e := by
  cases hty : e.ty <;> simp [forcedRule, hty]

/-! ### Rekey `hyp ↦ obs` preserves EncodeReady

`Origin.rekeyHypToObs hypIdx 0` turns the newest hyp tag into `obs 0` and
shifts every existing observation up by one. When every hyp index in the
worklist/env is `≤ hypIdx`, this preserves `Origin.cmp`, so `pushPos` and
`mergeSort` commute with mapping. Observation-slot counters bump by one.
-/

@[simp] theorem PosEntry.rekeyHypToObs_ty (hypIdx k : Nat) (e : PosEntry sig) :
    (PosEntry.rekeyHypToObs hypIdx k e).ty = e.ty := rfl

@[simp] theorem PosEntry.rekeyHypToObs_origin (hypIdx k : Nat) (e : PosEntry sig) :
    (PosEntry.rekeyHypToObs hypIdx k e).origin =
      Origin.rekeyHypToObs hypIdx k e.origin := rfl

theorem forcedRule_rekey_cons_moveStable (hypIdx k : Nat)
    (e : PosEntry sig) (ws : List (PosEntry sig)) {A : Object sig.nBases}
    (h : forcedRule (e :: ws) A = .moveStable e) :
    forcedRule
        (PosEntry.rekeyHypToObs hypIdx k e ::
          ws.map (PosEntry.rekeyHypToObs hypIdx k)) A =
      .moveStable (PosEntry.rekeyHypToObs hypIdx k e) := by
  simp only [forcedRule] at h ⊢
  cases hty : e.ty <;> simp [hty, PosEntry.rekeyHypToObs] at h ⊢

theorem forcedRule_rekey_cons_leftNever (hypIdx k : Nat)
    (e : PosEntry sig) (ws : List (PosEntry sig)) {A : Object sig.nBases}
    (hty : e.ty = .never) :
    forcedRule
        (PosEntry.rekeyHypToObs hypIdx k e ::
          ws.map (PosEntry.rekeyHypToObs hypIdx k)) A =
      .leftNever (PosEntry.rekeyHypToObs hypIdx k e) := by
  simp [forcedRule, hty, PosEntry.rekeyHypToObs]

theorem forcedRule_rekey_rightUnit (hypIdx k : Nat)
    (ws : List (PosEntry sig))
    (h : forcedRule ws (.unit : Object sig.nBases) = .rightUnit) :
    forcedRule (ws.map (PosEntry.rekeyHypToObs hypIdx k))
      (.unit : Object sig.nBases) = .rightUnit := by
  match ws with
  | [] => simpa [forcedRule] using h
  | e :: _ =>
      simp only [forcedRule] at h
      cases hty : e.ty <;> simp [hty] at h

theorem forcedRule_rekey_rightProd (hypIdx k : Nat)
    (ws : List (PosEntry sig)) {L R : Object sig.nBases}
    (h : forcedRule ws (.prod L R) = .rightProd L R) :
    forcedRule (ws.map (PosEntry.rekeyHypToObs hypIdx k)) (.prod L R) =
      .rightProd L R := by
  match ws with
  | [] => simpa [forcedRule] using h
  | e :: _ =>
      simp only [forcedRule] at h
      cases hty : e.ty <;> simp [hty] at h

theorem forcedRule_rekey_rightExp (hypIdx k : Nat)
    (ws : List (PosEntry sig)) {Arg Ret : Object sig.nBases}
    (h : forcedRule ws (.exp Arg Ret) = .rightExp Arg Ret) :
    forcedRule (ws.map (PosEntry.rekeyHypToObs hypIdx k)) (.exp Arg Ret) =
      .rightExp Arg Ret := by
  match ws with
  | [] => simpa [forcedRule] using h
  | e :: _ =>
      simp only [forcedRule] at h
      cases hty : e.ty <;> simp [hty] at h

theorem forcedRule_rekey_focus (hypIdx k : Nat)
    (ws : List (PosEntry sig)) {A : Object sig.nBases}
    (h : forcedRule ws A = .focus) :
    forcedRule (ws.map (PosEntry.rekeyHypToObs hypIdx k)) A = .focus := by
  match ws with
  | [] =>
      simp only [forcedRule] at h ⊢
      cases A <;> simp at h ⊢
  | e :: _ =>
      simp only [forcedRule] at h
      cases hty : e.ty <;> simp [hty] at h

theorem forcedRule_rekey_cons_leftCoprod (hypIdx k : Nat)
    (e : PosEntry sig) (ws : List (PosEntry sig)) {A L R : Object sig.nBases}
    (h : forcedRule (e :: ws) A = .leftCoprod e L R) :
    forcedRule
        (PosEntry.rekeyHypToObs hypIdx k e ::
          ws.map (PosEntry.rekeyHypToObs hypIdx k)) A =
      .leftCoprod (PosEntry.rekeyHypToObs hypIdx k e) L R := by
  have hty := forcedRule_leftCoprod_ty h
  simp [forcedRule, hty, PosEntry.rekeyHypToObs]

/-- `pushPos` commutes with `rekeyHypToObs _ 0` when hyp indices are bounded. -/
theorem pushPos_map_rekeyHypToObs_zero (hypIdx : Nat)
    (ws : List (PosEntry sig)) (o : Origin sig) (ty : Object sig.nBases)
    (hws : ∀ e ∈ ws, Origin.hypIdxLe e.origin hypIdx)
    (ho : Origin.hypIdxLe o hypIdx) :
    (pushPos ws o ty).map (PosEntry.rekeyHypToObs hypIdx 0) =
      pushPos (ws.map (PosEntry.rekeyHypToObs hypIdx 0))
        (Origin.rekeyHypToObs hypIdx 0 o) ty := by
  dsimp only [pushPos]
  cases hpol : objectPolarity ty == Polarity.pos
  · rfl
  · change
      ((({ origin := o, ty := ty } :: ws).mergeSort
            fun a b => Origin.ble a.origin b.origin).map
          (PosEntry.rekeyHypToObs hypIdx 0)) =
        (({ origin := Origin.rekeyHypToObs hypIdx 0 o, ty := ty } ::
            ws.map (PosEntry.rekeyHypToObs hypIdx 0)).mergeSort
          fun a b => Origin.ble a.origin b.origin)
    have hl :
        ∀ a ∈ { origin := o, ty := ty } :: ws,
          ∀ b ∈ { origin := o, ty := ty } :: ws,
            Origin.ble a.origin b.origin =
              Origin.ble
                (PosEntry.rekeyHypToObs hypIdx 0 a).origin
                (PosEntry.rekeyHypToObs hypIdx 0 b).origin := by
      intro a ha b hb
      have ha' : Origin.hypIdxLe a.origin hypIdx := by
        cases ha with
        | head => exact ho
        | tail _ hmem => exact hws a hmem
      have hb' : Origin.hypIdxLe b.origin hypIdx := by
        cases hb with
        | head => exact ho
        | tail _ hmem => exact hws b hmem
      simp only [PosEntry.rekeyHypToObs_origin]
      exact (Origin.ble_rekeyHypToObs_zero_of_hypIdxLe hypIdx ha' hb').symm
    have hmap :=
      List.map_mergeSort (r := fun a b => Origin.ble a.origin b.origin)
        (s := fun a b => Origin.ble a.origin b.origin)
        (f := PosEntry.rekeyHypToObs hypIdx 0) hl
    simpa [PosEntry.rekeyHypToObs, List.map_cons] using hmap

/-! ### Rekey EncodeReady

Transport along `Origin.rekeyHypToObs hypIdx 0` (bumps `obsSlot`). Peel / unit-η
use `peelCaseOuter_rekeyHypToObs` / `OriginEnv.find?_rekeyHypToObs`.
-/

def worklistHypIdxLe (ws : List (PosEntry sig)) (bound : Nat) : Prop :=
  ∀ e ∈ ws, Origin.hypIdxLe e.origin bound

theorem hypIdxLe_of_mem_pushPos (ws : List (PosEntry sig)) (o : Origin sig)
    (ty : Object sig.nBases) (bound : Nat)
    (hws : worklistHypIdxLe ws bound) (ho : Origin.hypIdxLe o bound) :
    worklistHypIdxLe (pushPos ws o ty) bound := by
  intro e he
  simp only [pushPos] at he
  cases hpol : objectPolarity ty == Polarity.pos
  · exact hws e (by simpa [hpol] using he)
  · have he' : e ∈ ({ origin := o, ty := ty } :: ws).mergeSort
        fun a b => Origin.ble a.origin b.origin := by simpa [hpol] using he
    have he'' : e ∈ { origin := o, ty := ty } :: ws := List.mem_mergeSort.mp he'
    cases he'' with
    | head => exact ho
    | tail _ hmem => exact hws e hmem

theorem encodeReadyNoPeel_env_eq {Γ : Ctx sig} {A : Object sig.nBases}
    {ws : List (PosEntry sig)} {ε ε' : OriginEnv Γ}
    {domNest obsSlot : Nat} {t : InvTm Γ A}
    (hε : ∀ {B} (x : Var Γ B), ε x = ε' x)
    (h : EncodeReadyNoPeel ws ε domNest obsSlot t) :
    EncodeReadyNoPeel ws ε' domNest obsSlot t := by
  refine
    (EncodeReadyNoPeel.rec
      (motive_1 := fun {Γ} ws ε d o {A} t _ =>
        ∀ ε' : OriginEnv Γ, (∀ {B} (x : Var Γ B), ε x = ε' x) →
          EncodeReadyNoPeel ws ε' d o t)
      (motive_2 := fun {Γ} ws ε d o {A} f _ =>
        ∀ ε' : OriginEnv Γ, (∀ {B} (x : Var Γ B), ε x = ε' x) →
          EncodeReadyFocNoPeel ws ε' d o f)
      ?ms ?ln ?ru ?rp ?rpf ?re ?ref ?fo ?pos ?neg ?lp ?sat h) ε' hε
  case ms =>
    intro Γ A e ws ε d o t hfr _ ih ε' hε'
    exact .moveStable hfr (ih ε' hε')
  case ln =>
    intros; exact .leftNever ‹_›
  case ru =>
    intros; exact .rightUnit ‹_›
  case rp =>
    intro Γ L R ws ε d o t u hfr _ _ iht ihu ε' hε'
    exact .rightProd_pair hfr (iht ε' hε') (ihu ε' hε')
  case rpf =>
    intro Γ L R ws ε d o f hfr _ ihf ε' hε'
    exact .rightProd_foc hfr (ihf ε' hε')
  case re =>
    intro Γ Arg Ret ws ε d o body hfr _ ihb ε' hε'
    refine .rightExp_lam hfr (ihb (OriginEnv.weaken (A := Arg) ε' (.dom (sig := sig) d)) ?_)
    intro B x
    cases x with
    | here => rfl
    | there y => exact hε' y
  case ref =>
    intro Γ Arg Ret ws ε d o f hfr _ ihf ε' hε'
    exact .rightExp_foc hfr (ihf ε' hε')
  case fo =>
    intro Γ A ws ε d o f hfr _ ihf ε' hε'
    exact .focus hfr (ihf ε' hε')
  case pos => intros; exact .pos
  case neg => intros; exact .neg
  case lp =>
    intro Γ P A ws ε d o n t _ iht ε' hε'
    refine .letPos (iht (OriginEnv.weaken (A := P) ε' (.obs (sig := sig) o)) ?_)
    intro B x
    cases x with
    | here => rfl
    | there y => exact hε' y
  case sat =>
    intro Γ A ws ε d o s t _ iht ε' hε'
    exact .sat (iht ε' hε')

theorem encodeReadyFocNoPeel_env_eq {Γ : Ctx sig} {A : Object sig.nBases}
    {ws : List (PosEntry sig)} {ε ε' : OriginEnv Γ}
    {domNest obsSlot : Nat} {f : FocTm Γ A}
    (hε : ∀ {B} (x : Var Γ B), ε x = ε' x)
    (h : EncodeReadyFocNoPeel ws ε domNest obsSlot f) :
    EncodeReadyFocNoPeel ws ε' domNest obsSlot f := by
  refine
    (EncodeReadyFocNoPeel.rec
      (motive_1 := fun {Γ} ws ε d o {A} t _ =>
        ∀ ε' : OriginEnv Γ, (∀ {B} (x : Var Γ B), ε x = ε' x) →
          EncodeReadyNoPeel ws ε' d o t)
      (motive_2 := fun {Γ} ws ε d o {A} f _ =>
        ∀ ε' : OriginEnv Γ, (∀ {B} (x : Var Γ B), ε x = ε' x) →
          EncodeReadyFocNoPeel ws ε' d o f)
      ?ms ?ln ?ru ?rp ?rpf ?re ?ref ?fo ?pos ?neg ?lp ?sat h) ε' hε
  case ms =>
    intro Γ A e ws ε d o t hfr _ ih ε' hε'
    exact .moveStable hfr (ih ε' hε')
  case ln => intros; exact .leftNever ‹_›
  case ru => intros; exact .rightUnit ‹_›
  case rp =>
    intro Γ L R ws ε d o t u hfr _ _ iht ihu ε' hε'
    exact .rightProd_pair hfr (iht ε' hε') (ihu ε' hε')
  case rpf =>
    intro Γ L R ws ε d o f hfr _ ihf ε' hε'
    exact .rightProd_foc hfr (ihf ε' hε')
  case re =>
    intro Γ Arg Ret ws ε d o body hfr _ ihb ε' hε'
    refine .rightExp_lam hfr (ihb (OriginEnv.weaken (A := Arg) ε' (.dom (sig := sig) d)) ?_)
    intro B x; cases x with | here => rfl | there y => exact hε' y
  case ref =>
    intro Γ Arg Ret ws ε d o f hfr _ ihf ε' hε'
    exact .rightExp_foc hfr (ihf ε' hε')
  case fo =>
    intro Γ A ws ε d o f hfr _ ihf ε' hε'
    exact .focus hfr (ihf ε' hε')
  case pos => intros; exact .pos
  case neg => intros; exact .neg
  case lp =>
    intro Γ P A ws ε d o n t _ iht ε' hε'
    refine .letPos (iht (OriginEnv.weaken (A := P) ε' (.obs (sig := sig) o)) ?_)
    intro B x; cases x with | here => rfl | there y => exact hε' y
  case sat =>
    intro Γ A ws ε d o s t _ iht ε' hε'
    exact .sat (iht ε' hε')

theorem encodeReady_rekeyHypToObs_noPeel {Γ : Ctx sig} {A : Object sig.nBases}
    (hypIdx : Nat)
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {domNest obsSlot : Nat} {t : InvTm Γ A}
    (hws : worklistHypIdxLe ws hypIdx)
    (hε : ∀ {B} (x : Var Γ B), Origin.hypIdxLe (ε x) hypIdx)
    (h : EncodeReadyNoPeel ws ε domNest obsSlot t) :
    EncodeReadyNoPeel
      (ws.map (PosEntry.rekeyHypToObs hypIdx 0))
      (fun {B} x => Origin.rekeyHypToObs hypIdx 0 (ε x))
      domNest (obsSlot + 1) t := by
  refine
    (EncodeReadyNoPeel.rec
      (motive_1 := fun {Γ} ws ε d o {A} t _ =>
        worklistHypIdxLe ws hypIdx →
        (∀ {B} (x : Var Γ B), Origin.hypIdxLe (ε x) hypIdx) →
        EncodeReadyNoPeel (ws.map (PosEntry.rekeyHypToObs hypIdx 0))
          (fun {B} x => Origin.rekeyHypToObs hypIdx 0 (ε x)) d (o + 1) t)
      (motive_2 := fun {Γ} ws ε d o {A} f _ =>
        worklistHypIdxLe ws hypIdx →
        (∀ {B} (x : Var Γ B), Origin.hypIdxLe (ε x) hypIdx) →
        EncodeReadyFocNoPeel (ws.map (PosEntry.rekeyHypToObs hypIdx 0))
          (fun {B} x => Origin.rekeyHypToObs hypIdx 0 (ε x)) d (o + 1) f)
      ?ms ?ln ?ru ?rp ?rpf ?re ?ref ?fo ?pos ?neg ?lp ?sat h) hws hε
  case ms =>
    intro Γ A e ws ε d o t hfr _ ih hws hε
    have hfr' := forcedRule_rekey_cons_moveStable hypIdx 0 e ws hfr
    refine .moveStable hfr' (ih ?_ hε)
    intro e' he'
    exact hws e' (List.Mem.tail _ he')
  case ln =>
    intro Γ A e ws ε d o n hty hws hε
    exact .leftNever (by simpa [PosEntry.rekeyHypToObs] using hty)
  case ru =>
    intro Γ ws ε d o hfr hws hε
    exact .rightUnit (forcedRule_rekey_rightUnit hypIdx 0 ws hfr)
  case rp =>
    intro Γ L R ws ε d o t u hfr _ _ iht ihu hws hε
    exact .rightProd_pair (forcedRule_rekey_rightProd hypIdx 0 ws hfr)
      (iht hws hε) (ihu hws hε)
  case rpf =>
    intro Γ L R ws ε d o f hfr _ ihf hws hε
    exact .rightProd_foc (forcedRule_rekey_rightProd hypIdx 0 ws hfr) (ihf hws hε)
  case re =>
    intro Γ Arg Ret ws ε d o body hfr _ ihb hws hε
    have hpush := pushPos_map_rekeyHypToObs_zero hypIdx ws (.dom (sig := sig) d) Arg
      hws (by simp [Origin.hypIdxLe])
    have hεw : ∀ {B} (x : Var (Γ ▻ Arg) B),
        Origin.hypIdxLe (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) d) x) hypIdx := by
      intro B x; cases x with
      | here => simp [OriginEnv.weaken, Origin.hypIdxLe]
      | there y => exact hε y
    have hb := ihb (hypIdxLe_of_mem_pushPos ws _ Arg hypIdx hws (by simp [Origin.hypIdxLe])) hεw
    refine .rightExp_lam (forcedRule_rekey_rightExp hypIdx 0 ws hfr) ?_
    refine encodeReadyNoPeel_env_eq ?_ (by
      simpa [hpush, Origin.rekeyHypToObs_dom] using hb)
    intro B x
    simpa [OriginEnv.weaken_rekeyHypToObs] using rfl
  case ref =>
    intro Γ Arg Ret ws ε d o f hfr _ ihf hws hε
    exact .rightExp_foc (forcedRule_rekey_rightExp hypIdx 0 ws hfr) (ihf hws hε)
  case fo =>
    intro Γ A ws ε d o f hfr _ ihf hws hε
    exact .focus (forcedRule_rekey_focus hypIdx 0 ws hfr) (ihf hws hε)
  case pos => intros; exact .pos
  case neg => intros; exact .neg
  case lp =>
    intro Γ P A ws ε d o n t _ iht hws hε
    have hpush := pushPos_map_rekeyHypToObs_zero hypIdx ws (.obs (sig := sig) o) P
      hws (by simp [Origin.hypIdxLe])
    have hεw : ∀ {B} (x : Var (Γ ▻ P) B),
        Origin.hypIdxLe (OriginEnv.weaken (A := P) ε (.obs (sig := sig) o) x) hypIdx := by
      intro B x; cases x with
      | here => simp [OriginEnv.weaken, Origin.hypIdxLe]
      | there y => exact hε y
    have ht := iht (hypIdxLe_of_mem_pushPos ws _ P hypIdx hws (by simp [Origin.hypIdxLe])) hεw
    refine .letPos ?_
    refine encodeReadyNoPeel_env_eq
      (fun {B} x => by
        simpa [Origin.rekeyHypToObs_obs] using
          OriginEnv.weaken_rekeyHypToObs ε (.obs (sig := sig) o) hypIdx 0 x)
      (by simpa [hpush, Origin.rekeyHypToObs_obs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ht)
  case sat =>
    intro Γ A ws ε d o s t _ iht hws hε
    exact .sat (iht hws hε)

theorem encodeReadyFoc_rekeyHypToObs_noPeel {Γ : Ctx sig} {A : Object sig.nBases}
    (hypIdx : Nat)
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {domNest obsSlot : Nat} {f : FocTm Γ A}
    (hws : worklistHypIdxLe ws hypIdx)
    (hε : ∀ {B} (x : Var Γ B), Origin.hypIdxLe (ε x) hypIdx)
    (h : EncodeReadyFocNoPeel ws ε domNest obsSlot f) :
    EncodeReadyFocNoPeel
      (ws.map (PosEntry.rekeyHypToObs hypIdx 0))
      (fun {B} x => Origin.rekeyHypToObs hypIdx 0 (ε x))
      domNest (obsSlot + 1) f := by
  refine
    (EncodeReadyFocNoPeel.rec
      (motive_1 := fun {Γ} ws ε d o {A} t _ =>
        worklistHypIdxLe ws hypIdx →
        (∀ {B} (x : Var Γ B), Origin.hypIdxLe (ε x) hypIdx) →
        EncodeReadyNoPeel (ws.map (PosEntry.rekeyHypToObs hypIdx 0))
          (fun {B} x => Origin.rekeyHypToObs hypIdx 0 (ε x)) d (o + 1) t)
      (motive_2 := fun {Γ} ws ε d o {A} f _ =>
        worklistHypIdxLe ws hypIdx →
        (∀ {B} (x : Var Γ B), Origin.hypIdxLe (ε x) hypIdx) →
        EncodeReadyFocNoPeel (ws.map (PosEntry.rekeyHypToObs hypIdx 0))
          (fun {B} x => Origin.rekeyHypToObs hypIdx 0 (ε x)) d (o + 1) f)
      ?ms ?ln ?ru ?rp ?rpf ?re ?ref ?fo ?pos ?neg ?lp ?sat h) hws hε
  case ms =>
    intro Γ A e ws ε d o t hfr _ ih hws hε
    exact .moveStable (forcedRule_rekey_cons_moveStable hypIdx 0 e ws hfr)
      (ih (fun e' he => hws e' (List.Mem.tail _ he)) hε)
  case ln =>
    intro Γ A e ws ε d o n hty hws hε
    exact .leftNever (by simpa [PosEntry.rekeyHypToObs] using hty)
  case ru =>
    intro Γ ws ε d o hfr hws hε
    exact .rightUnit (forcedRule_rekey_rightUnit hypIdx 0 ws hfr)
  case rp =>
    intro Γ L R ws ε d o t u hfr _ _ iht ihu hws hε
    exact .rightProd_pair (forcedRule_rekey_rightProd hypIdx 0 ws hfr)
      (iht hws hε) (ihu hws hε)
  case rpf =>
    intro Γ L R ws ε d o f hfr _ ihf hws hε
    exact .rightProd_foc (forcedRule_rekey_rightProd hypIdx 0 ws hfr) (ihf hws hε)
  case re =>
    intro Γ Arg Ret ws ε d o body hfr _ ihb hws hε
    have hpush := pushPos_map_rekeyHypToObs_zero hypIdx ws (.dom (sig := sig) d) Arg
      hws (by simp [Origin.hypIdxLe])
    have hεw : ∀ {B} (x : Var (Γ ▻ Arg) B),
        Origin.hypIdxLe (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) d) x) hypIdx := by
      intro B x; cases x with
      | here => simp [OriginEnv.weaken, Origin.hypIdxLe]
      | there y => exact hε y
    have hb := ihb (hypIdxLe_of_mem_pushPos ws _ Arg hypIdx hws (by simp [Origin.hypIdxLe])) hεw
    refine .rightExp_lam (forcedRule_rekey_rightExp hypIdx 0 ws hfr) ?_
    refine encodeReadyNoPeel_env_eq ?_ (by simpa [hpush, Origin.rekeyHypToObs_dom] using hb)
    intro B x; simpa [OriginEnv.weaken_rekeyHypToObs] using rfl
  case ref =>
    intro Γ Arg Ret ws ε d o f hfr _ ihf hws hε
    exact .rightExp_foc (forcedRule_rekey_rightExp hypIdx 0 ws hfr) (ihf hws hε)
  case fo =>
    intro Γ A ws ε d o f hfr _ ihf hws hε
    exact .focus (forcedRule_rekey_focus hypIdx 0 ws hfr) (ihf hws hε)
  case pos => intros; exact .pos
  case neg => intros; exact .neg
  case lp =>
    intro Γ P A ws ε d o n t _ iht hws hε
    have hpush := pushPos_map_rekeyHypToObs_zero hypIdx ws (.obs (sig := sig) o) P
      hws (by simp [Origin.hypIdxLe])
    have hεw : ∀ {B} (x : Var (Γ ▻ P) B),
        Origin.hypIdxLe (OriginEnv.weaken (A := P) ε (.obs (sig := sig) o) x) hypIdx := by
      intro B x; cases x with
      | here => simp [OriginEnv.weaken, Origin.hypIdxLe]
      | there y => exact hε y
    have ht := iht (hypIdxLe_of_mem_pushPos ws _ P hypIdx hws (by simp [Origin.hypIdxLe])) hεw
    refine .letPos ?_
    refine encodeReadyNoPeel_env_eq
      (fun {B} x => by
        simpa [Origin.rekeyHypToObs_obs] using
          OriginEnv.weaken_rekeyHypToObs ε (.obs (sig := sig) o) hypIdx 0 x)
      (by simpa [hpush, Origin.rekeyHypToObs_obs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ht)
  case sat =>
    intro Γ A ws ε d o s t _ iht hws hε
    exact .sat (iht hws hε)

/-- Pointwise env equality for full `EncodeReady` (incl. peel / unit-η). -/
theorem encodeReady_env_eq {Γ : Ctx sig} {A : Object sig.nBases}
    {ws : List (PosEntry sig)} {ε ε' : OriginEnv Γ}
    {domNest obsSlot : Nat} {t : InvTm Γ A}
    (hε : ∀ {B} (x : Var Γ B), ε x = ε' x)
    (h : EncodeReady ws ε domNest obsSlot t) :
    EncodeReady ws ε' domNest obsSlot t := by
  refine
    (EncodeReady.rec
      (motive_1 := fun {Γ} ws ε d o {A} t _ =>
        ∀ ε' : OriginEnv Γ, (∀ {B} (x : Var Γ B), ε x = ε' x) →
          EncodeReady ws ε' d o t)
      (motive_2 := fun {Γ} ws ε d o {A} f _ =>
        ∀ ε' : OriginEnv Γ, (∀ {B} (x : Var Γ B), ε x = ε' x) →
          EncodeReadyFoc ws ε' d o f)
      ?ms ?ln ?ru ?rp ?rpf ?re ?ref ?lp ?lu ?fo ?pos ?neg ?letp ?sat h) ε' hε
  case ms =>
    intro Γ A e ws ε d o t hfr _ ih ε' hε'
    exact .moveStable hfr (ih ε' hε')
  case ln => intros; exact .leftNever ‹_›
  case ru => intros; exact .rightUnit ‹_›
  case rp =>
    intro Γ L R ws ε d o t u hfr _ _ iht ihu ε' hε'
    exact .rightProd_pair hfr (iht ε' hε') (ihu ε' hε')
  case rpf =>
    intro Γ L R ws ε d o f hfr _ ihf ε' hε'
    exact .rightProd_foc hfr (ihf ε' hε')
  case re =>
    intro Γ Arg Ret ws ε d o body hfr _ ihb ε' hε'
    refine .rightExp_lam hfr (ihb (OriginEnv.weaken (A := Arg) ε' (.dom (sig := sig) d)) ?_)
    intro B x; cases x <;> [rfl; exact hε' _]
  case ref =>
    intro Γ Arg Ret ws ε d o f hfr _ ihf ε' hε'
    exact .rightExp_foc hfr (ihf ε' hε')
  case lp =>
    intro Γ A L R e ws ε d o n tL tR t hfr hpeel _ _ ihL ihR ε' hε'
    have hpeel' : peelCaseOuter ε' e.origin t = some ⟨L, R, n, tL, tR⟩ :=
      (peelCaseOuter_env_eq t hε' rfl).symm ▸ hpeel
    refine .leftCoprod_peel hfr hpeel'
      (ihL (OriginEnv.weaken (A := L) ε' (.split e.origin false)) ?_)
      (ihR (OriginEnv.weaken (A := R) ε' (.split e.origin true)) ?_)
    · intro B x; cases x with
      | here => simp [OriginEnv.weaken, hε']
      | there y => exact hε' y
    · intro B x; cases x with
      | here => simp [OriginEnv.weaken, hε']
      | there y => exact hε' y
  case lu =>
    intro Γ L R e ws ε d o x hfr hfind hit _ _ ihL ihR ε' hε'
    have hit' : (ε' x == e.origin) = true := by simpa [hε' x] using hit
    refine .leftCoprod_unitEta hfr
      ((OriginEnv.find?_env_eq e.origin hε').symm ▸ hfind) hit'
      (ihL (OriginEnv.weaken (A := L) ε' (.split e.origin false)) ?_)
      (ihR (OriginEnv.weaken (A := R) ε' (.split e.origin true)) ?_)
    · intro B y; cases y with
      | here => simp [OriginEnv.weaken, hε']
      | there z => exact hε' z
    · intro B y; cases y with
      | here => simp [OriginEnv.weaken, hε']
      | there z => exact hε' z
  case fo =>
    intro Γ A ws ε d o f hfr _ ihf ε' hε'
    exact .focus hfr (ihf ε' hε')
  case pos => intros; exact .pos
  case neg => intros; exact .neg
  case letp =>
    intro Γ P A ws ε d o n t _ iht ε' hε'
    refine .letPos (iht (OriginEnv.weaken (A := P) ε' (.obs (sig := sig) o)) ?_)
    intro B x; cases x <;> [rfl; exact hε' _]
  case sat =>
    intro Γ A ws ε d o s t _ iht ε' hε'
    exact .sat (iht ε' hε')

/--
Full `EncodeReady` transport under `rekeyHypToObs hypIdx 0` (bumps `obsSlot`).
Peel / unit-η use `peelCaseOuter_rekeyHypToObs` / `find?_rekeyHypToObs`.
-/
theorem encodeReady_rekeyHypToObs {Γ : Ctx sig} {A : Object sig.nBases}
    (hypIdx : Nat)
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {domNest obsSlot : Nat} {t : InvTm Γ A}
    (hws : worklistHypIdxLe ws hypIdx)
    (hε : ∀ {B} (x : Var Γ B), Origin.hypIdxLe (ε x) hypIdx)
    (h : EncodeReady ws ε domNest obsSlot t) :
    EncodeReady
      (ws.map (PosEntry.rekeyHypToObs hypIdx 0))
      (fun {B} x => Origin.rekeyHypToObs hypIdx 0 (ε x))
      domNest (obsSlot + 1) t := by
  refine
    (EncodeReady.rec
      (motive_1 := fun {Γ} ws ε d o {A} t _ =>
        worklistHypIdxLe ws hypIdx →
        (∀ {B} (x : Var Γ B), Origin.hypIdxLe (ε x) hypIdx) →
        EncodeReady (ws.map (PosEntry.rekeyHypToObs hypIdx 0))
          (fun {B} x => Origin.rekeyHypToObs hypIdx 0 (ε x)) d (o + 1) t)
      (motive_2 := fun {Γ} ws ε d o {A} f _ =>
        worklistHypIdxLe ws hypIdx →
        (∀ {B} (x : Var Γ B), Origin.hypIdxLe (ε x) hypIdx) →
        EncodeReadyFoc (ws.map (PosEntry.rekeyHypToObs hypIdx 0))
          (fun {B} x => Origin.rekeyHypToObs hypIdx 0 (ε x)) d (o + 1) f)
      ?ms ?ln ?ru ?rp ?rpf ?re ?ref ?lp ?lu ?fo ?pos ?neg ?letp ?sat h) hws hε
  case ms =>
    intro Γ A e ws ε d o t hfr _ ih hws hε
    exact .moveStable (forcedRule_rekey_cons_moveStable hypIdx 0 e ws hfr)
      (ih (fun e' he => hws e' (List.Mem.tail _ he)) hε)
  case ln =>
    intro Γ A e ws ε d o n hty hws hε
    exact .leftNever (by simpa [PosEntry.rekeyHypToObs] using hty)
  case ru =>
    intro Γ ws ε d o hfr hws hε
    exact .rightUnit (forcedRule_rekey_rightUnit hypIdx 0 ws hfr)
  case rp =>
    intro Γ L R ws ε d o t u hfr _ _ iht ihu hws hε
    exact .rightProd_pair (forcedRule_rekey_rightProd hypIdx 0 ws hfr)
      (iht hws hε) (ihu hws hε)
  case rpf =>
    intro Γ L R ws ε d o f hfr _ ihf hws hε
    exact .rightProd_foc (forcedRule_rekey_rightProd hypIdx 0 ws hfr) (ihf hws hε)
  case re =>
    intro Γ Arg Ret ws ε d o body hfr _ ihb hws hε
    have hpush := pushPos_map_rekeyHypToObs_zero hypIdx ws (.dom (sig := sig) d) Arg
      hws (by simp [Origin.hypIdxLe])
    have hεw : ∀ {B} (x : Var (Γ ▻ Arg) B),
        Origin.hypIdxLe (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) d) x) hypIdx := by
      intro B x; cases x with
      | here => simp [OriginEnv.weaken, Origin.hypIdxLe]
      | there y => exact hε y
    have hb := ihb (hypIdxLe_of_mem_pushPos ws _ Arg hypIdx hws (by simp [Origin.hypIdxLe])) hεw
    refine .rightExp_lam (forcedRule_rekey_rightExp hypIdx 0 ws hfr) ?_
    refine encodeReady_env_eq ?_ (by
      simpa [hpush, Origin.rekeyHypToObs_dom] using hb)
    intro B x
    simpa [OriginEnv.weaken_rekeyHypToObs] using rfl
  case ref =>
    intro Γ Arg Ret ws ε d o f hfr _ ihf hws hε
    exact .rightExp_foc (forcedRule_rekey_rightExp hypIdx 0 ws hfr) (ihf hws hε)
  case lp =>
    intro Γ A L R e ws ε d o n tL tR t hfr hpeel _ _ ihL ihR hws hε
    have hfr' := forcedRule_rekey_cons_leftCoprod hypIdx 0 e ws hfr
    have hpeel' :
        peelCaseOuter
            (fun {_B} x => Origin.rekeyHypToObs hypIdx 0 (ε x))
            (Origin.rekeyHypToObs hypIdx 0 e.origin) t =
          some ⟨L, R, n, tL, tR⟩ := by
      rw [peelCaseOuter_rekeyHypToObs]; exact hpeel
    have he : Origin.hypIdxLe e.origin hypIdx := hws e (List.Mem.head _)
    have hws' : worklistHypIdxLe ws hypIdx :=
      fun e' he' => hws e' (List.Mem.tail _ he')
    have hεL : ∀ {B} (x : Var (Γ ▻ L) B),
        Origin.hypIdxLe
          (OriginEnv.weaken (A := L) ε (.split e.origin false) x) hypIdx := by
      intro B x; cases x with
      | here => simpa [OriginEnv.weaken, Origin.hypIdxLe] using he
      | there y => exact hε y
    have hεR : ∀ {B} (x : Var (Γ ▻ R) B),
        Origin.hypIdxLe
          (OriginEnv.weaken (A := R) ε (.split e.origin true) x) hypIdx := by
      intro B x; cases x with
      | here => simpa [OriginEnv.weaken, Origin.hypIdxLe] using he
      | there y => exact hε y
    have hpushL := pushPos_map_rekeyHypToObs_zero hypIdx ws (.split e.origin false) L
      hws' (by simpa [Origin.hypIdxLe] using he)
    have hpushR := pushPos_map_rekeyHypToObs_zero hypIdx ws (.split e.origin true) R
      hws' (by simpa [Origin.hypIdxLe] using he)
    have hL := ihL
      (hypIdxLe_of_mem_pushPos ws _ L hypIdx hws'
        (by simpa [Origin.hypIdxLe] using he)) hεL
    have hR := ihR
      (hypIdxLe_of_mem_pushPos ws _ R hypIdx hws'
        (by simpa [Origin.hypIdxLe] using he)) hεR
    refine .leftCoprod_peel hfr' hpeel' ?_ ?_
    · refine encodeReady_env_eq ?_ (by
        simpa [hpushL, Origin.rekeyHypToObs_split, List.map_cons,
          PosEntry.rekeyHypToObs] using hL)
      intro B x
      simpa [Origin.rekeyHypToObs_split] using
        OriginEnv.weaken_rekeyHypToObs ε (.split e.origin false) hypIdx 0 x
    · refine encodeReady_env_eq ?_ (by
        simpa [hpushR, Origin.rekeyHypToObs_split, List.map_cons,
          PosEntry.rekeyHypToObs] using hR)
      intro B x
      simpa [Origin.rekeyHypToObs_split] using
        OriginEnv.weaken_rekeyHypToObs ε (.split e.origin true) hypIdx 0 x
  case lu =>
    intro Γ L R e ws ε d o x hfr hfind hit _ _ ihL ihR hws hε
    have hfr' := forcedRule_rekey_cons_leftCoprod hypIdx 0 e ws hfr
    have hfind' :
        OriginEnv.find?
            (fun {_B} y => Origin.rekeyHypToObs hypIdx 0 (ε y))
            (Origin.rekeyHypToObs hypIdx 0 e.origin) =
          some ⟨.coprod L R, x⟩ := by
      rw [OriginEnv.find?_rekeyHypToObs]; exact hfind
    have hit' :
        ((fun {_B} y => Origin.rekeyHypToObs hypIdx 0 (ε y)) x ==
          Origin.rekeyHypToObs hypIdx 0 e.origin) = true := by
      rw [Origin.beq_rekeyHypToObs]; exact hit
    have he : Origin.hypIdxLe e.origin hypIdx := hws e (List.Mem.head _)
    have hws' : worklistHypIdxLe ws hypIdx :=
      fun e' he' => hws e' (List.Mem.tail _ he')
    have hεL : ∀ {B} (y : Var (Γ ▻ L) B),
        Origin.hypIdxLe
          (OriginEnv.weaken (A := L) ε (.split e.origin false) y) hypIdx := by
      intro B y; cases y with
      | here => simpa [OriginEnv.weaken, Origin.hypIdxLe] using he
      | there z => exact hε z
    have hεR : ∀ {B} (y : Var (Γ ▻ R) B),
        Origin.hypIdxLe
          (OriginEnv.weaken (A := R) ε (.split e.origin true) y) hypIdx := by
      intro B y; cases y with
      | here => simpa [OriginEnv.weaken, Origin.hypIdxLe] using he
      | there z => exact hε z
    have hpushL := pushPos_map_rekeyHypToObs_zero hypIdx ws (.split e.origin false) L
      hws' (by simpa [Origin.hypIdxLe] using he)
    have hpushR := pushPos_map_rekeyHypToObs_zero hypIdx ws (.split e.origin true) R
      hws' (by simpa [Origin.hypIdxLe] using he)
    have hL := ihL
      (hypIdxLe_of_mem_pushPos ws _ L hypIdx hws'
        (by simpa [Origin.hypIdxLe] using he)) hεL
    have hR := ihR
      (hypIdxLe_of_mem_pushPos ws _ R hypIdx hws'
        (by simpa [Origin.hypIdxLe] using he)) hεR
    refine .leftCoprod_unitEta hfr' hfind' hit' ?_ ?_
    · refine encodeReady_env_eq ?_ (by
        simpa [hpushL, Origin.rekeyHypToObs_split, List.map_cons,
          PosEntry.rekeyHypToObs] using hL)
      intro B y
      simpa [Origin.rekeyHypToObs_split] using
        OriginEnv.weaken_rekeyHypToObs ε (.split e.origin false) hypIdx 0 y
    · refine encodeReady_env_eq ?_ (by
        simpa [hpushR, Origin.rekeyHypToObs_split, List.map_cons,
          PosEntry.rekeyHypToObs] using hR)
      intro B y
      simpa [Origin.rekeyHypToObs_split] using
        OriginEnv.weaken_rekeyHypToObs ε (.split e.origin true) hypIdx 0 y
  case fo =>
    intro Γ A ws ε d o f hfr _ ihf hws hε
    exact .focus (forcedRule_rekey_focus hypIdx 0 ws hfr) (ihf hws hε)
  case pos => intros; exact .pos
  case neg => intros; exact .neg
  case letp =>
    intro Γ P A ws ε d o n t _ iht hws hε
    have hpush := pushPos_map_rekeyHypToObs_zero hypIdx ws (.obs (sig := sig) o) P
      hws (by simp [Origin.hypIdxLe])
    have hεw : ∀ {B} (x : Var (Γ ▻ P) B),
        Origin.hypIdxLe (OriginEnv.weaken (A := P) ε (.obs (sig := sig) o) x) hypIdx := by
      intro B x; cases x with
      | here => simp [OriginEnv.weaken, Origin.hypIdxLe]
      | there y => exact hε y
    have ht := iht (hypIdxLe_of_mem_pushPos ws _ P hypIdx hws (by simp [Origin.hypIdxLe])) hεw
    refine .letPos ?_
    refine encodeReady_env_eq
      (fun {B} x => by
        simpa [Origin.rekeyHypToObs_obs] using
          OriginEnv.weaken_rekeyHypToObs ε (.obs (sig := sig) o) hypIdx 0 x)
      (by simpa [hpush, Origin.rekeyHypToObs_obs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ht)
  case sat =>
    intro Γ A ws ε d o s t _ iht hws hε
    exact .sat (iht hws hε)

theorem encodeReadyFoc_rekeyHypToObs {Γ : Ctx sig} {A : Object sig.nBases}
    (hypIdx : Nat)
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {domNest obsSlot : Nat} {f : FocTm Γ A}
    (hws : worklistHypIdxLe ws hypIdx)
    (hε : ∀ {B} (x : Var Γ B), Origin.hypIdxLe (ε x) hypIdx)
    (h : EncodeReadyFoc ws ε domNest obsSlot f) :
    EncodeReadyFoc
      (ws.map (PosEntry.rekeyHypToObs hypIdx 0))
      (fun {B} x => Origin.rekeyHypToObs hypIdx 0 (ε x))
      domNest (obsSlot + 1) f := by
  refine
    (EncodeReadyFoc.rec
      (motive_1 := fun {Γ} ws ε d o {A} t _ =>
        worklistHypIdxLe ws hypIdx →
        (∀ {B} (x : Var Γ B), Origin.hypIdxLe (ε x) hypIdx) →
        EncodeReady (ws.map (PosEntry.rekeyHypToObs hypIdx 0))
          (fun {B} x => Origin.rekeyHypToObs hypIdx 0 (ε x)) d (o + 1) t)
      (motive_2 := fun {Γ} ws ε d o {A} f _ =>
        worklistHypIdxLe ws hypIdx →
        (∀ {B} (x : Var Γ B), Origin.hypIdxLe (ε x) hypIdx) →
        EncodeReadyFoc (ws.map (PosEntry.rekeyHypToObs hypIdx 0))
          (fun {B} x => Origin.rekeyHypToObs hypIdx 0 (ε x)) d (o + 1) f)
      ?ms ?ln ?ru ?rp ?rpf ?re ?ref ?lp ?lu ?fo ?pos ?neg ?letp ?sat h) hws hε
  case ms =>
    intro Γ A e ws ε d o t hfr _ ih hws hε
    exact .moveStable (forcedRule_rekey_cons_moveStable hypIdx 0 e ws hfr)
      (ih (fun e' he => hws e' (List.Mem.tail _ he)) hε)
  case ln =>
    intro Γ A e ws ε d o n hty hws hε
    exact .leftNever (by simpa [PosEntry.rekeyHypToObs] using hty)
  case ru =>
    intro Γ ws ε d o hfr hws hε
    exact .rightUnit (forcedRule_rekey_rightUnit hypIdx 0 ws hfr)
  case rp =>
    intro Γ L R ws ε d o t u hfr _ _ iht ihu hws hε
    exact .rightProd_pair (forcedRule_rekey_rightProd hypIdx 0 ws hfr)
      (iht hws hε) (ihu hws hε)
  case rpf =>
    intro Γ L R ws ε d o f hfr _ ihf hws hε
    exact .rightProd_foc (forcedRule_rekey_rightProd hypIdx 0 ws hfr) (ihf hws hε)
  case re =>
    intro Γ Arg Ret ws ε d o body hfr _ ihb hws hε
    have hpush := pushPos_map_rekeyHypToObs_zero hypIdx ws (.dom (sig := sig) d) Arg
      hws (by simp [Origin.hypIdxLe])
    have hεw : ∀ {B} (x : Var (Γ ▻ Arg) B),
        Origin.hypIdxLe (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) d) x) hypIdx := by
      intro B x; cases x with
      | here => simp [OriginEnv.weaken, Origin.hypIdxLe]
      | there y => exact hε y
    have hb := ihb (hypIdxLe_of_mem_pushPos ws _ Arg hypIdx hws (by simp [Origin.hypIdxLe])) hεw
    refine .rightExp_lam (forcedRule_rekey_rightExp hypIdx 0 ws hfr) ?_
    refine encodeReady_env_eq ?_ (by simpa [hpush, Origin.rekeyHypToObs_dom] using hb)
    intro B x; simpa [OriginEnv.weaken_rekeyHypToObs] using rfl
  case ref =>
    intro Γ Arg Ret ws ε d o f hfr _ ihf hws hε
    exact .rightExp_foc (forcedRule_rekey_rightExp hypIdx 0 ws hfr) (ihf hws hε)
  case lp =>
    intro Γ A L R e ws ε d o n tL tR t hfr hpeel _ _ ihL ihR hws hε
    have hfr' := forcedRule_rekey_cons_leftCoprod hypIdx 0 e ws hfr
    have hpeel' :
        peelCaseOuter
            (fun {_B} x => Origin.rekeyHypToObs hypIdx 0 (ε x))
            (Origin.rekeyHypToObs hypIdx 0 e.origin) t =
          some ⟨L, R, n, tL, tR⟩ := by
      rw [peelCaseOuter_rekeyHypToObs]; exact hpeel
    have he : Origin.hypIdxLe e.origin hypIdx := hws e (List.Mem.head _)
    have hws' : worklistHypIdxLe ws hypIdx :=
      fun e' he' => hws e' (List.Mem.tail _ he')
    have hεL : ∀ {B} (x : Var (Γ ▻ L) B),
        Origin.hypIdxLe
          (OriginEnv.weaken (A := L) ε (.split e.origin false) x) hypIdx := by
      intro B x; cases x with
      | here => simpa [OriginEnv.weaken, Origin.hypIdxLe] using he
      | there y => exact hε y
    have hεR : ∀ {B} (x : Var (Γ ▻ R) B),
        Origin.hypIdxLe
          (OriginEnv.weaken (A := R) ε (.split e.origin true) x) hypIdx := by
      intro B x; cases x with
      | here => simpa [OriginEnv.weaken, Origin.hypIdxLe] using he
      | there y => exact hε y
    have hpushL := pushPos_map_rekeyHypToObs_zero hypIdx ws (.split e.origin false) L
      hws' (by simpa [Origin.hypIdxLe] using he)
    have hpushR := pushPos_map_rekeyHypToObs_zero hypIdx ws (.split e.origin true) R
      hws' (by simpa [Origin.hypIdxLe] using he)
    have hL := ihL
      (hypIdxLe_of_mem_pushPos ws _ L hypIdx hws'
        (by simpa [Origin.hypIdxLe] using he)) hεL
    have hR := ihR
      (hypIdxLe_of_mem_pushPos ws _ R hypIdx hws'
        (by simpa [Origin.hypIdxLe] using he)) hεR
    refine .leftCoprod_peel hfr' hpeel' ?_ ?_
    · refine encodeReady_env_eq ?_ (by
        simpa [hpushL, Origin.rekeyHypToObs_split, List.map_cons,
          PosEntry.rekeyHypToObs] using hL)
      intro B x
      simpa [Origin.rekeyHypToObs_split] using
        OriginEnv.weaken_rekeyHypToObs ε (.split e.origin false) hypIdx 0 x
    · refine encodeReady_env_eq ?_ (by
        simpa [hpushR, Origin.rekeyHypToObs_split, List.map_cons,
          PosEntry.rekeyHypToObs] using hR)
      intro B x
      simpa [Origin.rekeyHypToObs_split] using
        OriginEnv.weaken_rekeyHypToObs ε (.split e.origin true) hypIdx 0 x
  case lu =>
    intro Γ L R e ws ε d o x hfr hfind hit _ _ ihL ihR hws hε
    have hfr' := forcedRule_rekey_cons_leftCoprod hypIdx 0 e ws hfr
    have hfind' :
        OriginEnv.find?
            (fun {_B} y => Origin.rekeyHypToObs hypIdx 0 (ε y))
            (Origin.rekeyHypToObs hypIdx 0 e.origin) =
          some ⟨.coprod L R, x⟩ := by
      rw [OriginEnv.find?_rekeyHypToObs]; exact hfind
    have hit' :
        ((fun {_B} y => Origin.rekeyHypToObs hypIdx 0 (ε y)) x ==
          Origin.rekeyHypToObs hypIdx 0 e.origin) = true := by
      rw [Origin.beq_rekeyHypToObs]; exact hit
    have he : Origin.hypIdxLe e.origin hypIdx := hws e (List.Mem.head _)
    have hws' : worklistHypIdxLe ws hypIdx :=
      fun e' he' => hws e' (List.Mem.tail _ he')
    have hεL : ∀ {B} (y : Var (Γ ▻ L) B),
        Origin.hypIdxLe
          (OriginEnv.weaken (A := L) ε (.split e.origin false) y) hypIdx := by
      intro B y; cases y with
      | here => simpa [OriginEnv.weaken, Origin.hypIdxLe] using he
      | there z => exact hε z
    have hεR : ∀ {B} (y : Var (Γ ▻ R) B),
        Origin.hypIdxLe
          (OriginEnv.weaken (A := R) ε (.split e.origin true) y) hypIdx := by
      intro B y; cases y with
      | here => simpa [OriginEnv.weaken, Origin.hypIdxLe] using he
      | there z => exact hε z
    have hpushL := pushPos_map_rekeyHypToObs_zero hypIdx ws (.split e.origin false) L
      hws' (by simpa [Origin.hypIdxLe] using he)
    have hpushR := pushPos_map_rekeyHypToObs_zero hypIdx ws (.split e.origin true) R
      hws' (by simpa [Origin.hypIdxLe] using he)
    have hL := ihL
      (hypIdxLe_of_mem_pushPos ws _ L hypIdx hws'
        (by simpa [Origin.hypIdxLe] using he)) hεL
    have hR := ihR
      (hypIdxLe_of_mem_pushPos ws _ R hypIdx hws'
        (by simpa [Origin.hypIdxLe] using he)) hεR
    refine .leftCoprod_unitEta hfr' hfind' hit' ?_ ?_
    · refine encodeReady_env_eq ?_ (by
        simpa [hpushL, Origin.rekeyHypToObs_split, List.map_cons,
          PosEntry.rekeyHypToObs] using hL)
      intro B y
      simpa [Origin.rekeyHypToObs_split] using
        OriginEnv.weaken_rekeyHypToObs ε (.split e.origin false) hypIdx 0 y
    · refine encodeReady_env_eq ?_ (by
        simpa [hpushR, Origin.rekeyHypToObs_split, List.map_cons,
          PosEntry.rekeyHypToObs] using hR)
      intro B y
      simpa [Origin.rekeyHypToObs_split] using
        OriginEnv.weaken_rekeyHypToObs ε (.split e.origin true) hypIdx 0 y
  case fo =>
    intro Γ A ws ε d o f hfr _ ihf hws hε
    exact .focus (forcedRule_rekey_focus hypIdx 0 ws hfr) (ihf hws hε)
  case pos => intros; exact .pos
  case neg => intros; exact .neg
  case letp =>
    intro Γ P A ws ε d o n t _ iht hws hε
    have hpush := pushPos_map_rekeyHypToObs_zero hypIdx ws (.obs (sig := sig) o) P
      hws (by simp [Origin.hypIdxLe])
    have hεw : ∀ {B} (x : Var (Γ ▻ P) B),
        Origin.hypIdxLe (OriginEnv.weaken (A := P) ε (.obs (sig := sig) o) x) hypIdx := by
      intro B x; cases x with
      | here => simp [OriginEnv.weaken, Origin.hypIdxLe]
      | there y => exact hε y
    have ht := iht (hypIdxLe_of_mem_pushPos ws _ P hypIdx hws (by simp [Origin.hypIdxLe])) hεw
    refine .letPos ?_
    refine encodeReady_env_eq
      (fun {B} x => by
        simpa [Origin.rekeyHypToObs_obs] using
          OriginEnv.weaken_rekeyHypToObs ε (.obs (sig := sig) o) hypIdx 0 x)
      (by simpa [hpush, Origin.rekeyHypToObs_obs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ht)
  case sat =>
    intro Γ A ws ε d o s t _ iht hws hε
    exact .sat (iht hws hε)

/-! ### Newest-hyp → obs (peel-free) and atom bases-only -/

private theorem ble_posEntry_trans (a b c : PosEntry sig)
    (hab : Origin.ble a.origin b.origin = true)
    (hbc : Origin.ble b.origin c.origin = true) :
    Origin.ble a.origin c.origin = true :=
  Origin.ble_trans a.origin b.origin c.origin hab hbc

private theorem ble_posEntry_total (a b : PosEntry sig) :
    (Origin.ble a.origin b.origin || Origin.ble b.origin a.origin) = true :=
  Origin.ble_total a.origin b.origin

theorem mergeSort_cons_obs_of_hyps
    (ws : List (PosEntry sig)) (P : Object sig.nBases) (k : Nat)
    (hws : ∀ e ∈ ws, ∃ i, e.origin = .hyp (sig := sig) i) :
    (({ origin := .obs (sig := sig) k, ty := P } : PosEntry sig) :: ws).mergeSort
        (fun a b => Origin.ble a.origin b.origin) =
      ws.mergeSort (fun a b => Origin.ble a.origin b.origin) ++
        [{ origin := .obs (sig := sig) k, ty := P }] := by
  let e : PosEntry sig := { origin := .obs (sig := sig) k, ty := P }
  let le : PosEntry sig → PosEntry sig → Bool :=
    fun a b => Origin.ble a.origin b.origin
  obtain ⟨l₁, l₂, h₁, h₂, hl₁⟩ :=
    List.mergeSort_cons (α := PosEntry sig) (le := le)
      ble_posEntry_trans ble_posEntry_total e ws
  have hl₂ : l₂ = [] := by
    cases l₂ with
    | nil => rfl
    | cons b rest =>
        have hb_sort : b ∈ ws.mergeSort le := by
          rw [h₂]; exact List.mem_append_right _ (List.Mem.head _)
        have ⟨i, hi⟩ := hws b (List.mem_mergeSort.mp hb_sort)
        have hp := List.pairwise_mergeSort (α := PosEntry sig) (le := le)
          ble_posEntry_trans ble_posEntry_total (e :: ws)
        rw [h₁] at hp
        have hpair : List.Pairwise (fun a b => le a b = true) (e :: b :: rest) :=
          (List.pairwise_append.mp hp).2.1
        have hrel : le e b = true := by
          cases hpair with
          | cons h _ => exact h b (List.Mem.head _)
        simp only [le, e, Origin.ble, hi, Origin.cmp_obs_hyp] at hrel
        cases hrel <;> contradiction
  subst hl₂
  have h₂' : ws.mergeSort le = l₁ := by simpa using h₂
  calc
    (e :: ws).mergeSort le = l₁ ++ [e] := h₁
    _ = ws.mergeSort le ++ [e] := by rw [h₂']

theorem posCollect_origin_prop {Γ : Ctx sig} (ε : OriginEnv Γ)
    (P : Origin sig → Prop)
    (hε : ∀ {A} (x : Var Γ A), P (ε x))
    {e : PosEntry sig} (he : e ∈ OriginEnv.posCollect ε) :
    P e.origin := by
  induction Γ with
  | empty => rw [posCollect_empty] at he; cases he
  | snoc Δ A ih =>
      rw [posCollect_snoc] at he
      split at he
      · cases he with
        | head => exact hε .here
        | tail _ hmem =>
            exact ih (fun {B} x => ε (.there x)) (fun {B} x => hε (.there x)) hmem
      · exact ih (fun {B} x => ε (.there x)) (fun {B} x => hε (.there x)) he

theorem posCollect_ofHyps_origin_hyp_lt (hyps : Array (Object sig.nBases))
    {e : PosEntry sig} (he : e ∈ OriginEnv.posCollect (OriginEnv.ofHyps hyps)) :
    ∃ i < hyps.size, e.origin = .hyp (sig := sig) i :=
  posCollect_origin_prop (OriginEnv.ofHyps hyps)
    (fun o => ∃ i < hyps.size, o = .hyp (sig := sig) i)
    (fun {A} x => by
      refine ⟨hyps.size - 1 - Var.toRawIdx x, ?_, rfl⟩
      have hraw : Var.toRawIdx x < hyps.size := by
        have := Var.toRawIdx_lt_length x
        simpa [Ctx.length_ofHyps] using this
      omega)
    he

theorem map_rekey_posCollect_ofHyps (hyps : Array (Object sig.nBases)) (k : Nat) :
    (OriginEnv.posCollect (OriginEnv.ofHyps hyps)).map
        (PosEntry.rekeyHypToObs hyps.size k) =
      OriginEnv.posCollect (OriginEnv.ofHyps hyps) := by
  have h : ∀ e ∈ OriginEnv.posCollect (OriginEnv.ofHyps hyps),
      PosEntry.rekeyHypToObs hyps.size k e = e := by
    intro e he
    have ⟨i, hlt, hi⟩ := posCollect_ofHyps_origin_hyp_lt hyps he
    match e with
    | ⟨origin, ty⟩ =>
        simp only at hi
        subst hi
        simp [PosEntry.rekeyHypToObs, Origin.rekeyHypToObs, Nat.ne_of_lt hlt]
  refine List.ext_getElem ?_ ?_
  · simp
  · intro n h₁ h₂
    have he :
        (OriginEnv.posCollect (OriginEnv.ofHyps hyps))[n] ∈
          OriginEnv.posCollect (OriginEnv.ofHyps hyps) :=
      List.getElem_mem _
    simpa [List.getElem_map, h _ he]

theorem Origin.hypIdxLe_weaken_hyp (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases) {A : Object sig.nBases}
    (x : Var (Ctx.ofHyps hyps ▻ P) A) :
    Origin.hypIdxLe
      (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.hyp (sig := sig) hyps.size) x)
      hyps.size := by
  cases x with
  | here => simp [OriginEnv.weaken, Origin.hypIdxLe]
  | there y =>
      simp only [OriginEnv.weaken]
      exact Origin.hypIdxLe_ofHyps_le_size hyps y

theorem hypIdxLe_posCollect_weaken_hyp (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases)
    {e : PosEntry sig}
    (he : e ∈ OriginEnv.posCollect
      (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.hyp (sig := sig) hyps.size))) :
    Origin.hypIdxLe e.origin hyps.size :=
  posCollect_origin_prop _
    (fun o => Origin.hypIdxLe o hyps.size)
    (fun {A} x => Origin.hypIdxLe_weaken_hyp hyps P x) he

theorem posWorklist_rekey_weaken_hyp_to_obs (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases) :
    (OriginEnv.posWorklist
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size))).map
        (PosEntry.rekeyHypToObs hyps.size 0) =
      pushPos (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))
        (.obs (sig := sig) 0) P := by
  dsimp only [OriginEnv.posWorklist, pushPos]
  have hidx :
      ∀ e ∈ OriginEnv.posCollect
          (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
            (.hyp (sig := sig) hyps.size)),
        Origin.hypIdxLe e.origin hyps.size :=
    fun e he => hypIdxLe_posCollect_weaken_hyp hyps P he
  have hmap :=
    List.map_mergeSort
      (r := fun a b => Origin.ble a.origin b.origin)
      (s := fun a b => Origin.ble a.origin b.origin)
      (f := PosEntry.rekeyHypToObs hyps.size 0)
      (by
        intro a ha b hb
        dsimp only [PosEntry.rekeyHypToObs]
        exact (Origin.ble_rekeyHypToObs_zero_of_hypIdxLe hyps.size
          (hidx a ha) (hidx b hb)).symm)
  rw [hmap, posCollect_weaken_hyp]
  cases hpol : objectPolarity P == Polarity.pos
  · simp [hpol, map_rekey_posCollect_ofHyps]
  · have hws : ∀ e ∈ OriginEnv.posCollect (OriginEnv.ofHyps hyps),
        ∃ i, e.origin = .hyp (sig := sig) i :=
      fun e he =>
        match posCollect_ofHyps_origin_hyp_lt hyps he with
        | ⟨i, _, hi⟩ => ⟨i, hi⟩
    simp only [hpol, List.map_cons, PosEntry.rekeyHypToObs, Origin.rekeyHypToObs,
      BEq.rfl, ↓reduceIte, map_rekey_posCollect_ofHyps]
    have hL := mergeSort_cons_obs_of_hyps
      (OriginEnv.posCollect (OriginEnv.ofHyps hyps)) P 0 hws
    have hR := mergeSort_cons_obs_of_hyps
      ((OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort
        fun a b => Origin.ble a.origin b.origin) P 0
      (fun e he => hws e (List.mem_mergeSort.mp he))
    have hid :
        ((OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort
            fun a b => Origin.ble a.origin b.origin).mergeSort
          (fun a b => Origin.ble a.origin b.origin) =
        (OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort
          fun a b => Origin.ble a.origin b.origin :=
      List.mergeSort_of_pairwise
        (List.pairwise_mergeSort ble_posEntry_trans ble_posEntry_total _)
    rw [hL, hR, hid]



/-- Rekey newest hyp under `weaken (.hyp size)` to phase-entry obs readiness. -/
theorem encodeReady_newest_hyp_to_obs_noPeel
    (hyps : Array (Object sig.nBases)) (P : Object sig.nBases)
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps ▻ P) A}
    (h : EncodeReadyNoPeel
      (OriginEnv.posWorklist
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size)))
      (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.hyp (sig := sig) hyps.size))
      0 0 t) :
    EncodeReadyNoPeel
      (pushPos (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))
        (.obs (sig := sig) 0) P)
      (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.obs (sig := sig) 0))
      0 1 t := by
  have hws :
      worklistHypIdxLe
        (OriginEnv.posWorklist
          (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
            (.hyp (sig := sig) hyps.size)))
        hyps.size := by
    intro e he
    have he' : e ∈ OriginEnv.posCollect
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size)) := by
      simpa [OriginEnv.posWorklist, List.mem_mergeSort] using he
    exact hypIdxLe_posCollect_weaken_hyp hyps P he'
  have hε : ∀ {B} (x : Var (Ctx.ofHyps hyps ▻ P) B),
      Origin.hypIdxLe
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size) x)
        hyps.size :=
    fun {B} x => Origin.hypIdxLe_weaken_hyp hyps P x
  have hr := encodeReady_rekeyHypToObs_noPeel hyps.size hws hε h
  refine encodeReadyNoPeel_env_eq
    (fun {B} x => OriginEnv.rekey_ofHyps_weaken_to_obs hyps P 0 x) ?_
  simpa [posWorklist_rekey_weaken_hyp_to_obs] using hr

/-- Full `EncodeReady` newest-hyp → obs (includes peel / unit-η under the binder). -/
theorem encodeReady_newest_hyp_to_obs
    (hyps : Array (Object sig.nBases)) (P : Object sig.nBases)
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps ▻ P) A}
    (h : EncodeReady
      (OriginEnv.posWorklist
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size)))
      (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.hyp (sig := sig) hyps.size))
      0 0 t) :
    EncodeReady
      (pushPos (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))
        (.obs (sig := sig) 0) P)
      (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.obs (sig := sig) 0))
      0 1 t := by
  have hws :
      worklistHypIdxLe
        (OriginEnv.posWorklist
          (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
            (.hyp (sig := sig) hyps.size)))
        hyps.size := by
    intro e he
    have he' : e ∈ OriginEnv.posCollect
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size)) := by
      simpa [OriginEnv.posWorklist, List.mem_mergeSort] using he
    exact hypIdxLe_posCollect_weaken_hyp hyps P he'
  have hε : ∀ {B} (x : Var (Ctx.ofHyps hyps ▻ P) B),
      Origin.hypIdxLe
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size) x)
        hyps.size :=
    fun {B} x => Origin.hypIdxLe_weaken_hyp hyps P x
  have hr := encodeReady_rekeyHypToObs hyps.size hws hε h
  refine encodeReady_env_eq
    (fun {B} x => OriginEnv.rekey_ofHyps_weaken_to_obs hyps P 0 x) ?_
  simpa [posWorklist_rekey_weaken_hyp_to_obs] using hr

/-! ### Left-coprod branch schedules (`ofHyps.push` vs encode `ws.tail` + split)

Encode's left-coprod branches use `pushPos ws.tail (.split e.origin side) _`
(`encodeLeftCoprodBranches`). Phase-entry `ofHyps (hyps.push L)` readiness
uses `pushPos (e :: ws) (.hyp hyps.size) L` when the parent worklist is
`e :: ws`. Two gaps:

1. **Consume** — drop left-coprod head `e` from the branch worklist.
2. **Binder tag** — `rekeyHypToSplit` (newest hyp → `.split parent side`).

`Origin.rekeyHypToSplit` + `mergeSort_cons_split_of_hyps` /
`posWorklist_rekey_weaken_hyp_to_split` / `pushPos_cons_of_blt_head` close
schedule algebra to `e :: leftCoprodBranchWs`. EncodeReady transport under
rekey + drop-`e` remains open (drop is not valid for left-coprod heads).
-/

/-- Parent `ofHyps` worklist agrees with weaken-hyp after push (cast form). -/
theorem posWorklist_ofHyps_push_eq_weaken_hyp
    (hyps : Array (Object sig.nBases)) (P : Object sig.nBases) :
    OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)) =
      OriginEnv.posWorklist
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size)) :=
  posWorklist_ofHyps_push hyps P

/--
Encode branch schedule after consuming left-coprod head `e` (definitional form
of `encodeLeftCoprodBranches`'s worklist).
-/
def leftCoprodBranchWs (ws : List (PosEntry sig)) (e : PosEntry sig)
    (side : Bool) (ty : Object sig.nBases) : List (PosEntry sig) :=
  pushPos ws (.split e.origin side) ty

/-- Split insertion after a hyp-only worklist sorts to the end (like `obs`). -/
theorem mergeSort_cons_split_of_hyps
    (ws : List (PosEntry sig)) (parent : Origin sig) (side : Bool)
    (P : Object sig.nBases)
    (hws : ∀ e ∈ ws, ∃ i, e.origin = .hyp (sig := sig) i) :
    (({ origin := .split parent side, ty := P } : PosEntry sig) :: ws).mergeSort
        (fun a b => Origin.ble a.origin b.origin) =
      ws.mergeSort (fun a b => Origin.ble a.origin b.origin) ++
        [{ origin := .split parent side, ty := P }] := by
  let e : PosEntry sig := { origin := .split parent side, ty := P }
  let le : PosEntry sig → PosEntry sig → Bool :=
    fun a b => Origin.ble a.origin b.origin
  obtain ⟨l₁, l₂, h₁, h₂, hl₁⟩ :=
    List.mergeSort_cons (α := PosEntry sig) (le := le)
      ble_posEntry_trans ble_posEntry_total e ws
  have hl₂ : l₂ = [] := by
    cases l₂ with
    | nil => rfl
    | cons b rest =>
        have hb_sort : b ∈ ws.mergeSort le := by
          rw [h₂]; exact List.mem_append_right _ (List.Mem.head _)
        have ⟨i, hi⟩ := hws b (List.mem_mergeSort.mp hb_sort)
        have hp := List.pairwise_mergeSort (α := PosEntry sig) (le := le)
          ble_posEntry_trans ble_posEntry_total (e :: ws)
        rw [h₁] at hp
        have hpair : List.Pairwise (fun a b => le a b = true) (e :: b :: rest) :=
          (List.pairwise_append.mp hp).2.1
        have hrel : le e b = true := by
          cases hpair with
          | cons h _ => exact h b (List.Mem.head _)
        -- split > hyp, so ble split hyp is false
        simp only [le, e, Origin.ble, hi, Origin.cmp] at hrel
        cases hrel <;> contradiction
  subst hl₂
  have h₂' : ws.mergeSort le = l₁ := by simpa using h₂
  calc
    (e :: ws).mergeSort le = l₁ ++ [e] := h₁
    _ = ws.mergeSort le ++ [e] := by rw [h₂']

/-- Parent `ofHyps` collect is unchanged by `rekeyHypToSplit` at `hyps.size`. -/
theorem map_rekeyHypToSplit_posCollect_ofHyps
    (hyps : Array (Object sig.nBases)) (parent : Origin sig) (side : Bool) :
    (OriginEnv.posCollect (OriginEnv.ofHyps hyps)).map
        (PosEntry.rekeyHypToSplit hyps.size parent side) =
      OriginEnv.posCollect (OriginEnv.ofHyps hyps) := by
  have h : ∀ e ∈ OriginEnv.posCollect (OriginEnv.ofHyps hyps),
      PosEntry.rekeyHypToSplit hyps.size parent side e = e := by
    intro e he
    have ⟨i, hlt, hi⟩ := posCollect_ofHyps_origin_hyp_lt hyps he
    match e with
    | ⟨origin, ty⟩ =>
        simp only at hi
        subst hi
        simp [PosEntry.rekeyHypToSplit, Origin.rekeyHypToSplit, Nat.ne_of_lt hlt]
  refine List.ext_getElem ?_ ?_
  · simp
  · intro n h₁ h₂
    have he :
        (OriginEnv.posCollect (OriginEnv.ofHyps hyps))[n] ∈
          OriginEnv.posCollect (OriginEnv.ofHyps hyps) :=
      List.getElem_mem _
    simpa [List.getElem_map, h _ he]

/-- Same as `map_rekeyHypToSplit_posCollect_ofHyps` after `mergeSort`. -/
theorem map_rekeyHypToSplit_posWorklist_ofHyps
    (hyps : Array (Object sig.nBases)) (parent : Origin sig) (side : Bool) :
    (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)).map
        (PosEntry.rekeyHypToSplit hyps.size parent side) =
      OriginEnv.posWorklist (OriginEnv.ofHyps hyps) := by
  dsimp only [OriginEnv.posWorklist]
  have h : ∀ e ∈
      (OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort
        fun a b => Origin.ble a.origin b.origin,
      PosEntry.rekeyHypToSplit hyps.size parent side e = e := by
    intro e he
    have ⟨i, hlt, hi⟩ :=
      posCollect_ofHyps_origin_hyp_lt hyps (List.mem_mergeSort.mp he)
    match e with
    | ⟨origin, ty⟩ =>
        simp only at hi
        subst hi
        simp [PosEntry.rekeyHypToSplit, Origin.rekeyHypToSplit, Nat.ne_of_lt hlt]
  refine List.ext_getElem ?_ ?_
  · simp
  · intro n h₁ h₂
    have he :
        ((OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort
            fun a b => Origin.ble a.origin b.origin)[n] ∈
          (OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort
            fun a b => Origin.ble a.origin b.origin :=
      List.getElem_mem _
    simpa [List.getElem_map, h _ he]

/-- Newest hyp index sorts after every strictly-older hyp entry. -/
theorem mergeSort_cons_hyp_newest_of_hyps
    (ws : List (PosEntry sig)) (P : Object sig.nBases) (idx : Nat)
    (hws : ∀ e ∈ ws, ∃ i < idx, e.origin = .hyp (sig := sig) i) :
    (({ origin := .hyp (sig := sig) idx, ty := P } : PosEntry sig) :: ws).mergeSort
        (fun a b => Origin.ble a.origin b.origin) =
      ws.mergeSort (fun a b => Origin.ble a.origin b.origin) ++
        [{ origin := .hyp (sig := sig) idx, ty := P }] := by
  let e : PosEntry sig := { origin := .hyp (sig := sig) idx, ty := P }
  let le : PosEntry sig → PosEntry sig → Bool :=
    fun a b => Origin.ble a.origin b.origin
  obtain ⟨l₁, l₂, h₁, h₂, hl₁⟩ :=
    List.mergeSort_cons (α := PosEntry sig) (le := le)
      ble_posEntry_trans ble_posEntry_total e ws
  have hl₂ : l₂ = [] := by
    cases l₂ with
    | nil => rfl
    | cons b rest =>
        have hb_sort : b ∈ ws.mergeSort le := by
          rw [h₂]; exact List.mem_append_right _ (List.Mem.head _)
        have ⟨i, hlt, hi⟩ := hws b (List.mem_mergeSort.mp hb_sort)
        have hp := List.pairwise_mergeSort (α := PosEntry sig) (le := le)
          ble_posEntry_trans ble_posEntry_total (e :: ws)
        rw [h₁] at hp
        have hpair : List.Pairwise (fun a b => le a b = true) (e :: b :: rest) :=
          (List.pairwise_append.mp hp).2.1
        have hrel : le e b = true := by
          cases hpair with
          | cons h _ => exact h b (List.Mem.head _)
        -- hyp idx > hyp i, so ble (hyp idx) (hyp i) is false
        simp only [le, e, Origin.ble, hi, Origin.cmp_hyp_hyp] at hrel
        have hgt : compare idx i = Ordering.gt := Nat.compare_eq_gt.mpr hlt
        simp [hgt] at hrel
  subst hl₂
  have h₂' : ws.mergeSort le = l₁ := by simpa using h₂
  calc
    (e :: ws).mergeSort le = l₁ ++ [e] := h₁
    _ = ws.mergeSort le ++ [e] := by rw [h₂']

/--
Binder-tag half: rekey newest hyp under `weaken (.hyp size)` to split yields
encode's `pushPos` on the **full** parent worklist (left-coprod head still
present). Compare `posWorklist_rekey_weaken_hyp_to_obs`. Hyp→split does not
preserve `Origin.cmp` vs obs/dom, so this uses hyp-only `mergeSort_cons_*`
instead of `List.map_mergeSort`.
-/
theorem posWorklist_rekey_weaken_hyp_to_split
    (hyps : Array (Object sig.nBases)) (P : Object sig.nBases)
    (parent : Origin sig) (side : Bool) :
    (OriginEnv.posWorklist
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size))).map
        (PosEntry.rekeyHypToSplit hyps.size parent side) =
      pushPos (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))
        (.split parent side) P := by
  dsimp only [OriginEnv.posWorklist, pushPos]
  have hws : ∀ e ∈ OriginEnv.posCollect (OriginEnv.ofHyps hyps),
      ∃ i < hyps.size, e.origin = .hyp (sig := sig) i :=
    fun e he => posCollect_ofHyps_origin_hyp_lt hyps he
  have hws' : ∀ e ∈ OriginEnv.posCollect (OriginEnv.ofHyps hyps),
      ∃ i, e.origin = .hyp (sig := sig) i :=
    fun e he => match hws e he with | ⟨i, _, hi⟩ => ⟨i, hi⟩
  let le : PosEntry sig → PosEntry sig → Bool :=
    fun a b => Origin.ble a.origin b.origin
  rw [posCollect_weaken_hyp]
  split_ifs with hpol
  · -- P positive
    have hHypEnd :=
      mergeSort_cons_hyp_newest_of_hyps
        (OriginEnv.posCollect (OriginEnv.ofHyps hyps)) P hyps.size hws
    have hSplitEnd :=
      mergeSort_cons_split_of_hyps
        ((OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort le) parent side P
        (fun e he => hws' e (List.mem_mergeSort.mp he))
    have hid :
        ((OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort le).mergeSort le =
          (OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort le :=
      List.mergeSort_of_pairwise
        (List.pairwise_mergeSort ble_posEntry_trans ble_posEntry_total _)
    rw [hHypEnd, List.map_append, List.map_cons, List.map_nil]
    have hsorted := map_rekeyHypToSplit_posWorklist_ofHyps hyps parent side
    dsimp only [OriginEnv.posWorklist] at hsorted
    rw [hsorted]
    simp only [PosEntry.rekeyHypToSplit, Origin.rekeyHypToSplit, BEq.rfl, ↓reduceIte]
    rw [hSplitEnd, hid]
  · -- P not positive: both sides are the parent worklist
    exact map_rekeyHypToSplit_posWorklist_ofHyps hyps parent side

/-- Boolean split of a list by a predicate is unique. -/
private theorem list_split_bool_unique {α : Type*} {S A B A' B' : List α}
    (P : α → Bool)
    (h : S = A ++ B) (h' : S = A' ++ B')
    (hA : ∀ a ∈ A, P a = true) (hB : ∀ b ∈ B, P b = false)
    (hA' : ∀ a ∈ A', P a = true) (hB' : ∀ b ∈ B', P b = false) :
    A = A' ∧ B = B' := by
  induction A generalizing S A' B B' with
  | nil =>
      cases A' with
      | nil =>
          have : B = B' := by
            have hB0 : S = B := by simpa using h
            have hB1 : S = B' := by simpa using h'
            exact hB0.symm.trans hB1
          exact ⟨rfl, this⟩
      | cons y A'rest =>
          have hy : P y = true := hA' y (List.Mem.head _)
          have hyS : y ∈ S := by
            rw [h']; exact List.mem_append_left _ (List.Mem.head _)
          have hyB : y ∈ B := by
            simpa [h] using hyS
          have hyf : P y = false := hB y hyB
          simp [hy] at hyf
  | cons a Arest ih =>
      cases A' with
      | nil =>
          have ha : P a = true := hA a (List.Mem.head _)
          have haS : a ∈ S := by
            rw [h]; exact List.mem_append_left _ (List.Mem.head _)
          have haB' : a ∈ B' := by
            simpa [h'] using haS
          have haf : P a = false := hB' a haB'
          simp [ha] at haf
      | cons a' A'rest =>
          have haS : S = a :: (Arest ++ B) := by simpa using h
          have ha'S : S = a' :: (A'rest ++ B') := by simpa using h'
          have haa' : a = a' := by
            rw [haS] at ha'S; exact (List.cons.inj ha'S).1
          subst haa'
          have hrest : Arest ++ B = A'rest ++ B' := by
            rw [haS] at ha'S; exact (List.cons.inj ha'S).2
          have ⟨hAeq, hBeq⟩ :=
            ih (S := Arest ++ B) (A' := A'rest) (B := B) (B' := B')
              rfl hrest
              (fun x hx => hA x (List.Mem.tail _ hx))
              hB
              (fun x hx => hA' x (List.Mem.tail _ hx))
              hB'
          exact ⟨by rw [hAeq], hBeq⟩

/-- If `e` is `≤` every entry of `ws`, it sorts to the front. -/
theorem mergeSort_cons_of_ble_head
    (e : PosEntry sig) (ws : List (PosEntry sig))
    (hws : ∀ e' ∈ ws, Origin.ble e.origin e'.origin = true) :
    (e :: ws).mergeSort (fun a b => Origin.ble a.origin b.origin) =
      e :: ws.mergeSort (fun a b => Origin.ble a.origin b.origin) := by
  let le : PosEntry sig → PosEntry sig → Bool :=
    fun a b => Origin.ble a.origin b.origin
  obtain ⟨l₁, l₂, h₁, h₂, hl₁⟩ :=
    List.mergeSort_cons (α := PosEntry sig) (le := le)
      ble_posEntry_trans ble_posEntry_total e ws
  have hl₁_nil : l₁ = [] := by
    cases l₁ with
    | nil => rfl
    | cons b rest =>
        have hb_sort : b ∈ ws.mergeSort le := by
          rw [h₂]; exact List.mem_append_left _ (List.Mem.head _)
        have hble := hws b (List.mem_mergeSort.mp hb_sort)
        have h := hl₁ b (List.Mem.head _)
        -- h : (!le e b) = true contradicts hble : ble e.origin b.origin = true
        dsimp only [le] at h
        rw [hble, Bool.not_true] at h
        cases h
  subst hl₁_nil
  have h₂' : ws.mergeSort le = l₂ := by simpa using h₂
  calc
    (e :: ws).mergeSort le = e :: l₂ := by simpa using h₁
    _ = e :: ws.mergeSort le := by rw [h₂']

/--
If `e` is strictly below `o` and `≤` every entry of `ws`, then
`pushPos (e :: ws) o = e :: pushPos ws o`.
-/
theorem pushPos_cons_of_blt_head
    (e : PosEntry sig) (ws : List (PosEntry sig)) (o : Origin sig)
    (ty : Object sig.nBases)
    (hws : ∀ e' ∈ ws, Origin.ble e.origin e'.origin = true)
    (ho : Origin.blt e.origin o = true) :
    pushPos (e :: ws) o ty = e :: pushPos ws o ty := by
  dsimp only [pushPos]
  split_ifs with hpol
  · let eNew : PosEntry sig := { origin := o, ty := ty }
    let le : PosEntry sig → PosEntry sig → Bool :=
      fun a b => Origin.ble a.origin b.origin
    let P : PosEntry sig → Bool := fun b => !(le eNew b)
    have h_e_ws := mergeSort_cons_of_ble_head e ws hws
    obtain ⟨l₁, l₂, h₁, h₂, hl₁⟩ :=
      List.mergeSort_cons (α := PosEntry sig) (le := le)
        ble_posEntry_trans ble_posEntry_total eNew (e :: ws)
    obtain ⟨m₁, m₂, hm₁, hm₂, hm₁cond⟩ :=
      List.mergeSort_cons (α := PosEntry sig) (le := le)
        ble_posEntry_trans ble_posEntry_total eNew ws
    have hnot_new_e : le eNew e = false := Origin.not_ble_of_blt_symm ho
    have hl₂_le : ∀ b ∈ l₂, le eNew b = true := by
      intro b hb
      have hp := List.pairwise_mergeSort (α := PosEntry sig) (le := le)
        ble_posEntry_trans ble_posEntry_total (eNew :: e :: ws)
      rw [h₁] at hp
      have hpair := (List.pairwise_append.mp hp).2.1
      cases hpair with
      | cons hrel _ => exact hrel b hb
    have hm₂_le : ∀ b ∈ m₂, le eNew b = true := by
      intro b hb
      have hp := List.pairwise_mergeSort (α := PosEntry sig) (le := le)
        ble_posEntry_trans ble_posEntry_total (eNew :: ws)
      rw [hm₁] at hp
      have hpair := (List.pairwise_append.mp hp).2.1
      cases hpair with
      | cons hrel _ => exact hrel b hb
    have he_in_l₁ : e ∈ l₁ := by
      have he_mem : e ∈ l₁ ++ l₂ := by
        rw [← h₂, h_e_ws]; exact List.Mem.head _
      refine (List.mem_append.mp he_mem).resolve_right ?_
      intro he_l₂
      have : le eNew e = true := hl₂_le e he_l₂
      simp [hnot_new_e] at this
    have hsplit_e_ws : l₁ ++ l₂ = e :: (m₁ ++ m₂) := by
      calc
        l₁ ++ l₂ = (e :: ws).mergeSort le := h₂.symm
        _ = e :: ws.mergeSort le := h_e_ws
        _ = e :: (m₁ ++ m₂) := by rw [hm₂]
    cases List.append_eq_cons_iff.mp hsplit_e_ws with
    | inl h =>
        obtain ⟨hl₁_nil, _⟩ := h
        subst hl₁_nil; cases he_in_l₁
    | inr h =>
        obtain ⟨l₁', ⟨hl₁_eq, hrest⟩⟩ := h
        subst hl₁_eq
        have hP_l₁' : ∀ a ∈ l₁', P a = true := fun a ha => by
          have h := hl₁ a (List.Mem.tail _ ha)
          simpa [P, Bool.not_eq_eq_eq_not, Bool.not_true] using h
        have hP_l₂ : ∀ b ∈ l₂, P b = false := fun b hb => by
          have : le eNew b = true := hl₂_le b hb
          simp [P, this]
        have hP_m₁ : ∀ a ∈ m₁, P a = true := fun a ha => by
          have h := hm₁cond a ha
          simpa [P, Bool.not_eq_eq_eq_not, Bool.not_true] using h
        have hP_m₂ : ∀ b ∈ m₂, P b = false := fun b hb => by
          have : le eNew b = true := hm₂_le b hb
          simp [P, this]
        -- hrest : m₁ ++ m₂ = l₁' ++ l₂
        have ⟨hl₁'_eq, hl₂_eq⟩ :=
          list_split_bool_unique (S := m₁ ++ m₂) (A := l₁') (B := l₂)
            (A' := m₁) (B' := m₂) P hrest rfl hP_l₁' hP_l₂ hP_m₁ hP_m₂
        calc
          (eNew :: e :: ws).mergeSort le
              = (e :: l₁') ++ eNew :: l₂ := h₁
          _ = e :: (l₁' ++ eNew :: l₂) := rfl
          _ = e :: (m₁ ++ eNew :: m₂) := by rw [hl₁'_eq, hl₂_eq]
          _ = e :: (eNew :: ws).mergeSort le := by rw [← hm₁]
  · rfl

/--
With sorted parent head `e` and `e < split`,
`pushPos (e :: ws) (.split …) = e :: leftCoprodBranchWs ws e side`.
-/
theorem pushPos_cons_leftCoprod_split
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (ty : Object sig.nBases)
    (hws : ∀ e' ∈ ws, Origin.ble e.origin e'.origin = true)
    (ho : Origin.blt e.origin (.split e.origin side) = true) :
    pushPos (e :: ws) (.split e.origin side) ty =
      e :: leftCoprodBranchWs ws e side ty :=
  pushPos_cons_of_blt_head e ws (.split e.origin side) ty hws ho

/-- Head of a sorted `posWorklist` is `≤` every later entry. -/
theorem ble_tail_of_posWorklist_cons {Γ : Ctx sig}
    (ε : OriginEnv Γ) {e : PosEntry sig} {ws : List (PosEntry sig)}
    (hws : OriginEnv.posWorklist ε = e :: ws) :
    ∀ e' ∈ ws, Origin.ble e.origin e'.origin = true := by
  intro e' he'
  have hp := List.pairwise_mergeSort (α := PosEntry sig)
      (le := fun a b => Origin.ble a.origin b.origin)
      ble_posEntry_trans ble_posEntry_total (OriginEnv.posCollect ε)
  rw [← OriginEnv.posWorklist_eq_mergeSort ε, hws] at hp
  cases hp with
  | cons hrel _ => exact hrel e' he'

/-- ofHyps origins are hyps, so each is strictly below any split. -/
theorem blt_split_of_posWorklist_ofHyps_mem
    (hyps : Array (Object sig.nBases))
    {e : PosEntry sig}
    (he : e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps))
    (parent : Origin sig) (side : Bool) :
    Origin.blt e.origin (.split parent side) = true := by
  have he' : e ∈ OriginEnv.posCollect (OriginEnv.ofHyps hyps) := by
    simpa [OriginEnv.posWorklist, List.mem_mergeSort] using he
  obtain ⟨i, _, hi⟩ := posCollect_ofHyps_origin_hyp_lt hyps he'
  simp [hi]

/--
Gap statement closed for **schedule algebra**: binder rekey + `pushPos_cons` give

`ofHyps.push` ↦ `e :: leftCoprodBranchWs`

EncodeReady **consume** (drop `e`, same term) is not a rekey lemma: with
`e.ty` a left-coprod, `forcedRule (e :: _)` is `.leftCoprod`, so readiness of
that term under `e :: _` is peel/unit-η only. Branch readiness under
`leftCoprodBranchWs` must be obtained under encode's schedule (induction
motive), not by transporting `PhaseEncodeReady` on `ofHyps.push` and
dropping `e`.
-/
theorem leftCoprod_branch_schedule_gap
    (hyps : Array (Object sig.nBases)) {L : Object sig.nBases}
    {e : PosEntry sig} {ws : List (PosEntry sig)} (side : Bool)
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = e :: ws) :
    OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push L)) =
      OriginEnv.posWorklist
        (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size)) ∧
    (OriginEnv.posWorklist
        (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size))).map
        (PosEntry.rekeyHypToSplit hyps.size e.origin side) =
      e :: leftCoprodBranchWs ws e side L ∧
    leftCoprodBranchWs ws e side L =
      pushPos ws (.split e.origin side) L := by
  refine ⟨posWorklist_ofHyps_push hyps L, ?_, rfl⟩
  have hrekey := by
    simpa [hws] using
      posWorklist_rekey_weaken_hyp_to_split hyps L e.origin side
  have hcons :=
    pushPos_cons_leftCoprod_split e ws side L
      (ble_tail_of_posWorklist_cons (OriginEnv.ofHyps hyps) hws)
      (blt_split_of_posWorklist_ofHyps_mem hyps
        (by simp [hws]) e.origin side)
  exact hrekey.trans hcons

/-! ### EncodeReady under encode left-coprod branch schedules

These inhabit the premises of `EncodeReady.leftCoprod_peel` /
`encodeReady_applyObsNeu_coprod_var` directly under
`leftCoprodBranchWs` + `weaken (.split)` — matching `encodeLeftCoprodBranches`.
-/

/-- Worklist entries are all base-typed (hence `moveStable`). -/
def worklistBasesOnly (ws : List (PosEntry sig)) : Prop :=
  ∀ e ∈ ws, ∃ b : Fin sig.nBases, e.ty = .base b

theorem encodeReady_unit_basesOnly {Γ : Ctx sig}
    (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat)
    (hws : worklistBasesOnly ws) :
    EncodeReady ws ε domNest obsSlot (.unit (Γ := Γ)) := by
  induction ws with
  | nil => exact encodeReady_unit_nil ε domNest obsSlot
  | cons e ws ih =>
      have ⟨b, hb⟩ := hws e (List.Mem.head _)
      exact .moveStable
        (forcedRule_cons_base_moveStable e ws hb (.unit : Object sig.nBases))
        (ih fun e' he' => hws e' (List.Mem.tail _ he'))

theorem encodeReady_foc_pos_basesOnly {Γ : Ctx sig} {A : Object sig.nBases}
    (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (p : PosNeu Γ A)
    (hws : worklistBasesOnly ws)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    EncodeReady ws ε domNest obsSlot (.foc (.pos (.done p))) := by
  induction ws with
  | nil => exact encodeReady_foc_pos_nil ε domNest obsSlot p hfr
  | cons e ws ih =>
      have ⟨b, hb⟩ := hws e (List.Mem.head _)
      exact .moveStable (forcedRule_cons_base_moveStable e ws hb A)
        (ih fun e' he' => hws e' (List.Mem.tail _ he'))

theorem encodeReady_foc_neg_basesOnly {Γ : Ctx sig} {A : Object sig.nBases}
    (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (n : NegNeu Γ A)
    (hws : worklistBasesOnly ws)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    EncodeReady ws ε domNest obsSlot (.foc (.neg (.done n))) := by
  induction ws with
  | nil => exact encodeReady_foc_neg_nil ε domNest obsSlot n hfr
  | cons e ws ih =>
      have ⟨b, hb⟩ := hws e (List.Mem.head _)
      exact .moveStable (forcedRule_cons_base_moveStable e ws hb A)
        (ih fun e' he' => hws e' (List.Mem.tail _ he'))

/-- After stripping base heads, `.pair` is ready under `rightProd` on `[]`. -/
theorem encodeReady_pair_basesOnly {Γ : Ctx sig} {L R : Object sig.nBases}
    (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (t : InvTm Γ L) (u : InvTm Γ R)
    (hws : worklistBasesOnly ws)
    (ht : EncodeReady ([] : List (PosEntry sig)) ε domNest obsSlot t)
    (hu : EncodeReady ([] : List (PosEntry sig)) ε domNest obsSlot u) :
    EncodeReady ws ε domNest obsSlot (.pair t u) := by
  induction ws with
  | nil => exact .rightProd_pair rfl ht hu
  | cons e ws ih =>
      have ⟨b, hb⟩ := hws e (List.Mem.head _)
      exact .moveStable
        (forcedRule_cons_base_moveStable e ws hb (.prod L R))
        (ih fun e' he' => hws e' (List.Mem.tail _ he'))

/-- After stripping base heads, `.lam` is ready under `rightExp` on `[]`. -/
theorem encodeReady_lam_basesOnly {Γ : Ctx sig} {Arg Ret : Object sig.nBases}
    (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (obsSlot : Nat) (body : InvTm (Γ ▻ Arg) Ret)
    (hws : worklistBasesOnly ws)
    (hb : EncodeReady
      (pushPos ([] : List (PosEntry sig)) (.dom (sig := sig) 0) Arg)
      (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) 0))
      1 obsSlot body) :
    EncodeReady ws ε 0 obsSlot (.lam body) := by
  induction ws with
  | nil => exact .rightExp_lam rfl hb
  | cons e ws ih =>
      have ⟨b, hb'⟩ := hws e (List.Mem.head _)
      exact .moveStable
        (forcedRule_cons_base_moveStable e ws hb' (.exp Arg Ret))
        (ih fun e' he' => hws e' (List.Mem.tail _ he'))

/-- After stripping base heads, `.foc (.sat _)` is ready under `focus` on `[]`. -/
theorem encodeReady_foc_sat_basesOnly {Γ : Ctx sig} {A : Object sig.nBases}
    (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (s : Schedule sig.nBases) (t : InvTm Γ A)
    (hws : worklistBasesOnly ws)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (ht : EncodeReady ([] : List (PosEntry sig)) ε domNest obsSlot t) :
    EncodeReady ws ε domNest obsSlot (.foc (.sat (.mk s t))) := by
  induction ws with
  | nil => exact .focus hfr (.sat ht)
  | cons e ws ih =>
      have ⟨b, hb⟩ := hws e (List.Mem.head _)
      exact .moveStable (forcedRule_cons_base_moveStable e ws hb A)
        (ih fun e' he' => hws e' (List.Mem.tail _ he'))

/--
Branch worklist stays base-only when the parent tail is base-only and the
split payload is either negative (not pushed) or itself a base.
-/
theorem leftCoprodBranchWs_basesOnly
    (ws : List (PosEntry sig)) (e : PosEntry sig) (side : Bool)
    (L : Object sig.nBases)
    (hws : worklistBasesOnly ws)
    (hL : objectPolarity L ≠ Polarity.pos ∨ ∃ b : Fin sig.nBases, L = .base b) :
    worklistBasesOnly (leftCoprodBranchWs ws e side L) := by
  dsimp only [leftCoprodBranchWs, pushPos, worklistBasesOnly]
  cases hpol : objectPolarity L == Polarity.pos with
  | false =>
      intro e' he'
      exact hws e' (by simpa [hpol] using he')
  | true =>
      have hpos : objectPolarity L = Polarity.pos := by
        simpa [beq_iff_eq] using hpol
      rcases hL with hneg | ⟨b, hb⟩
      · exact absurd hpos hneg
      · intro e' he'
        have he'' :
            e' ∈ ({ origin := .split e.origin side, ty := L } :: ws).mergeSort
              fun a b => Origin.ble a.origin b.origin := by
          simpa [hpol] using he'
        have he_mem : e' ∈ { origin := .split e.origin side, ty := L } :: ws :=
          List.mem_mergeSort.mp he''
        cases he_mem with
        | head => exact ⟨b, by simp [hb]⟩
        | tail _ hmem => exact hws e' hmem

/-- `.unit` is encode-ready under a base-only left-coprod branch schedule. -/
theorem encodeReady_unit_leftCoprodBranch
    (hyps : Array (Object sig.nBases)) (L : Object sig.nBases)
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (hbr : worklistBasesOnly (leftCoprodBranchWs ws e side L)) :
    EncodeReady (leftCoprodBranchWs ws e side L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0
      (.unit : InvTm (Ctx.ofHyps hyps ▻ L) .unit) :=
  encodeReady_unit_basesOnly _ _ 0 0 hbr

theorem encodeReady_foc_pos_leftCoprodBranch
    (hyps : Array (Object sig.nBases)) {A L : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (p : PosNeu (Ctx.ofHyps hyps ▻ L) A)
    (hbr : worklistBasesOnly (leftCoprodBranchWs ws e side L))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    EncodeReady (leftCoprodBranchWs ws e side L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0
      (.foc (.pos (.done p))) :=
  encodeReady_foc_pos_basesOnly _ _ 0 0 p hbr hfr

theorem encodeReady_foc_neg_leftCoprodBranch
    (hyps : Array (Object sig.nBases)) {A L : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (n : NegNeu (Ctx.ofHyps hyps ▻ L) A)
    (hbr : worklistBasesOnly (leftCoprodBranchWs ws e side L))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    EncodeReady (leftCoprodBranchWs ws e side L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0
      (.foc (.neg (.done n))) :=
  encodeReady_foc_neg_basesOnly _ _ 0 0 n hbr hfr

/-- `.pair` under encode's left-coprod branch schedule (base-only tails). -/
theorem encodeReady_pair_leftCoprodBranch
    (hyps : Array (Object sig.nBases)) {L L' R' : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (t : InvTm (Ctx.ofHyps hyps ▻ L) L') (u : InvTm (Ctx.ofHyps hyps ▻ L) R')
    (hbr : worklistBasesOnly (leftCoprodBranchWs ws e side L))
    (ht : EncodeReady ([] : List (PosEntry sig))
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0 t)
    (hu : EncodeReady ([] : List (PosEntry sig))
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0 u) :
    EncodeReady (leftCoprodBranchWs ws e side L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0 (.pair t u) :=
  encodeReady_pair_basesOnly _ _ 0 0 t u hbr ht hu

/-- `.lam` under encode's left-coprod branch schedule (base-only tails). -/
theorem encodeReady_lam_leftCoprodBranch
    (hyps : Array (Object sig.nBases)) {L Arg Ret : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (body : InvTm (Ctx.ofHyps hyps ▻ L ▻ Arg) Ret)
    (hbr : worklistBasesOnly (leftCoprodBranchWs ws e side L))
    (hb : EncodeReady
      (pushPos ([] : List (PosEntry sig)) (.dom (sig := sig) 0) Arg)
      (OriginEnv.weaken (A := Arg)
        (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
        (.dom (sig := sig) 0))
      1 0 body) :
    EncodeReady (leftCoprodBranchWs ws e side L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0 (.lam body) :=
  encodeReady_lam_basesOnly _ _ 0 body hbr hb

/-- `.foc (.sat _)` under encode's left-coprod branch schedule (base-only tails). -/
theorem encodeReady_foc_sat_leftCoprodBranch
    (hyps : Array (Object sig.nBases)) {A L : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (s : Schedule sig.nBases) (t : InvTm (Ctx.ofHyps hyps ▻ L) A)
    (hbr : worklistBasesOnly (leftCoprodBranchWs ws e side L))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (ht : EncodeReady ([] : List (PosEntry sig))
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0 t) :
    EncodeReady (leftCoprodBranchWs ws e side L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0 (.foc (.sat (.mk s t))) :=
  encodeReady_foc_sat_basesOnly _ _ 0 0 s t hbr hfr ht

/-!
Non-base `pushPos` payloads under branch schedules: the only positive non-base
objects are `.never` and `.coprod _ _`. Negative payloads are not inserted
(schedule stays bases-only if the parent tail was). Nested coprod still needs
`leftCoprod_peel` / `leftCoprod_unitEta` under the inserted split entry.
Never payloads are discharged below via `worklistBasesOrNever`.
-/

/-- Worklist entries are bases or `never` (abort-capable after stripping bases). -/
def worklistBasesOrNever (ws : List (PosEntry sig)) : Prop :=
  ∀ e ∈ ws, (∃ b : Fin sig.nBases, e.ty = .base b) ∨ e.ty = .never

/-- Abort is encode-ready on a bases/`never` worklist that actually contains `never`. -/
theorem encodeReady_abort_basesOrNever {Γ : Ctx sig} {A : Object sig.nBases}
    (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (n : NegNeu Γ .never)
    (hws : worklistBasesOrNever ws)
    (hne : ∃ e ∈ ws, e.ty = .never) :
    EncodeReady ws ε domNest obsSlot (.abort (A := A) n) := by
  induction ws with
  | nil =>
      obtain ⟨_, he, _⟩ := hne
      cases he
  | cons e ws ih =>
      match hws e (List.Mem.head _) with
      | .inl ⟨b, hb⟩ =>
          refine .moveStable (forcedRule_cons_base_moveStable e ws hb A)
            (ih (fun e' he' => hws e' (List.Mem.tail _ he')) ?_)
          obtain ⟨e', he', hty⟩ := hne
          cases he' with
          | head =>
              cases hty ▸ hb
          | tail _ hmem =>
              exact ⟨e', hmem, hty⟩
      | .inr hnever =>
          exact .leftNever hnever

theorem leftCoprodBranchWs_basesOrNever_never
    (ws : List (PosEntry sig)) (e : PosEntry sig) (side : Bool)
    (hws : worklistBasesOnly ws) :
    worklistBasesOrNever (leftCoprodBranchWs ws e side .never) := by
  intro e' he'
  have he'' :
      e' ∈ ({ origin := .split e.origin side, ty := (.never : Object sig.nBases) } :: ws).mergeSort
        fun a b => Origin.ble a.origin b.origin := by
    simpa [leftCoprodBranchWs, pushPos, objectPolarity_never] using he'
  have he_mem :
      e' ∈ { origin := .split e.origin side, ty := (.never : Object sig.nBases) } :: ws :=
    List.mem_mergeSort.mp he''
  cases he_mem with
  | head => exact Or.inr rfl
  | tail _ hmem => exact Or.inl (hws e' hmem)

theorem mem_never_of_leftCoprodBranchWs_never
    (ws : List (PosEntry sig)) (e : PosEntry sig) (side : Bool) :
    ∃ e' ∈ leftCoprodBranchWs ws e side .never, e'.ty = .never := by
  refine ⟨⟨.split e.origin side, .never⟩, ?_, rfl⟩
  dsimp only [leftCoprodBranchWs, pushPos]
  simp only [objectPolarity_never, BEq.rfl, ↓reduceIte]
  exact List.mem_mergeSort.mpr (List.Mem.head _)

/-- Abort under a never-payload encode branch schedule (parent tail bases-only). -/
theorem encodeReady_abort_leftCoprodBranch_never
    (hyps : Array (Object sig.nBases)) {A : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (hws : worklistBasesOnly ws)
    (n : NegNeu (Ctx.ofHyps hyps ▻ .never) .never) :
    EncodeReady (leftCoprodBranchWs ws e side .never)
      (OriginEnv.weaken (A := .never) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0 (.abort (A := A) n) :=
  encodeReady_abort_basesOrNever _ _ 0 0 n
    (leftCoprodBranchWs_basesOrNever_never ws e side hws)
    (mem_never_of_leftCoprodBranchWs_never ws e side)

/-- Bases-only fails as soon as a `never` or nested `coprod` sits on the worklist. -/
theorem not_worklistBasesOnly_of_never_or_coprod
    {ws : List (PosEntry sig)}
    (hne : ∃ e ∈ ws,
      e.ty = .never ∨ ∃ L R : Object sig.nBases, e.ty = .coprod L R) :
    ¬ worklistBasesOnly ws := by
  intro hws
  obtain ⟨e, he, hty⟩ := hne
  obtain ⟨b, hb⟩ := hws e he
  cases hty with
  | inl hnever => cases hnever ▸ hb
  | inr h =>
      obtain ⟨L, R, hcoprod⟩ := h
      cases hcoprod ▸ hb

/-- Nested-coprod `pushPos` after a hyp-only tail sorts the insert to the end. -/
theorem leftCoprodBranchWs_coprod_eq_append_of_hyps
    (ws : List (PosEntry sig)) (e : PosEntry sig) (side : Bool)
    (L R : Object sig.nBases)
    (hws : ∀ e' ∈ ws, ∃ i, e'.origin = .hyp (sig := sig) i) :
    leftCoprodBranchWs ws e side (.coprod L R) =
      ws.mergeSort (fun a b => Origin.ble a.origin b.origin) ++
        [{ origin := .split e.origin side, ty := .coprod L R }] := by
  dsimp only [leftCoprodBranchWs, pushPos]
  simp only [objectPolarity_coprod, BEq.rfl, ↓reduceIte]
  exact mergeSort_cons_split_of_hyps ws e.origin side (.coprod L R) hws

/-- `.unit` under left-coprod unit-η after a bases/`moveStable` prefix. -/
theorem encodeReady_unit_leftCoprod_unitEta_of_base_prefix
    {Γ : Ctx sig} {L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    {ε : OriginEnv Γ} {domNest obsSlot : Nat}
    (x : Var Γ (.coprod L R))
    (hpref : worklistBasesOnly pref)
    (hfr : forcedRule (e :: ws) (.unit : Object sig.nBases) = .leftCoprod e L R)
    (hfind : OriginEnv.find? ε e.origin = some ⟨.coprod L R, x⟩)
    (hit : (ε x == e.origin) = true)
    (hL : EncodeReady
      (pushPos ws (.split e.origin false) L)
      (OriginEnv.weaken (A := L) ε (.split e.origin false))
      domNest obsSlot (.unit : InvTm (Γ ▻ L) .unit))
    (hR : EncodeReady
      (pushPos ws (.split e.origin true) R)
      (OriginEnv.weaken (A := R) ε (.split e.origin true))
      domNest obsSlot (.unit : InvTm (Γ ▻ R) .unit)) :
    EncodeReady (pref ++ e :: ws) ε domNest obsSlot (.unit (Γ := Γ)) := by
  induction pref with
  | nil =>
      exact .leftCoprod_unitEta hfr hfind hit hL hR
  | cons e' pref ih =>
      have ⟨b, hb⟩ := hpref e' (List.Mem.head _)
      exact .moveStable
        (forcedRule_cons_base_moveStable e' _ hb (.unit : Object sig.nBases))
        (ih fun e'' he'' => hpref e'' (List.Mem.tail _ he''))

/--
Nested-coprod payload under encode's branch schedule (hyp-only parent tail):
split insert sorts last; strip bases then `leftCoprod_unitEta` on `.here`.
Branch schedules after consuming the nested head are `pushPos [] (.split …)`.
-/
theorem encodeReady_unit_leftCoprodBranch_nested
    (hyps : Array (Object sig.nBases))
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (L R : Object sig.nBases)
    (hhyp : ∀ e' ∈ ws, ∃ i, e'.origin = .hyp (sig := sig) i)
    (hbase : worklistBasesOnly ws)
    (hL : EncodeReady
      (pushPos ([] : List (PosEntry sig)) (.split (.split e.origin side) false) L)
      (OriginEnv.weaken (A := L)
        (OriginEnv.weaken (A := .coprod L R) (OriginEnv.ofHyps hyps)
          (.split e.origin side))
        (.split (.split e.origin side) false))
      0 0 (.unit : InvTm (Ctx.ofHyps hyps ▻ .coprod L R ▻ L) .unit))
    (hR : EncodeReady
      (pushPos ([] : List (PosEntry sig)) (.split (.split e.origin side) true) R)
      (OriginEnv.weaken (A := R)
        (OriginEnv.weaken (A := .coprod L R) (OriginEnv.ofHyps hyps)
          (.split e.origin side))
        (.split (.split e.origin side) true))
      0 0 (.unit : InvTm (Ctx.ofHyps hyps ▻ .coprod L R ▻ R) .unit)) :
    EncodeReady (leftCoprodBranchWs ws e side (.coprod L R))
      (OriginEnv.weaken (A := .coprod L R) (OriginEnv.ofHyps hyps)
        (.split e.origin side))
      0 0
      (.unit : InvTm (Ctx.ofHyps hyps ▻ .coprod L R) .unit) := by
  let eIns : PosEntry sig :=
    { origin := .split e.origin side, ty := .coprod L R }
  have hwsEq :
      leftCoprodBranchWs ws e side (.coprod L R) =
        ws.mergeSort (fun a b => Origin.ble a.origin b.origin) ++ [eIns] :=
    leftCoprodBranchWs_coprod_eq_append_of_hyps ws e side L R hhyp
  have hpref :
      worklistBasesOnly
        (ws.mergeSort fun a b => Origin.ble a.origin b.origin) :=
    fun e' he' => hbase e' (List.mem_mergeSort.mp he')
  have hfr :
      forcedRule (eIns :: ([] : List (PosEntry sig)))
        (.unit : Object sig.nBases) = .leftCoprod eIns L R :=
    forcedRule_cons_coprod eIns [] rfl _
  have hfind :
      OriginEnv.find?
        (OriginEnv.weaken (A := .coprod L R) (OriginEnv.ofHyps hyps)
          (.split e.origin side))
        eIns.origin =
        some ⟨.coprod L R, .here⟩ := by
    simpa [eIns] using
      OriginEnv.find?_weaken_here (OriginEnv.ofHyps hyps) (.split e.origin side)
  have hit :
      ((OriginEnv.weaken (A := .coprod L R) (OriginEnv.ofHyps hyps)
          (.split e.origin side) (.here)) == eIns.origin) = true := by
    simp [OriginEnv.weaken, OriginEnv.snoc, eIns, BEq.rfl]
  rw [hwsEq]
  simpa using
    encodeReady_unit_leftCoprod_unitEta_of_base_prefix (x := .here)
      hpref hfr hfind hit hL hR

/-!
Same-term transport `EncodeReady` on `ofHyps.push` → `leftCoprodBranchWs` is
**not** available: if the parent head is left-coprod, keeping that head forces
peel/unit-η, while encode's branch schedule is `leftCoprodBranchWs` alone.
Prove branch readiness under encode's schedule (see
`encodeReady_*_leftCoprodBranch`), not by dropping the parent head.
Status name reserved: `encodeReady_ofHyps_push_to_leftCoprodBranch` (blocked).
-/

/-- `castCtx` is the identity on `.unit`. -/
theorem InvTm.castCtx_unit {Γ Δ : Ctx sig} (h : Γ = Δ) :
    InvTm.castCtx h (.unit : InvTm Γ .unit) = (.unit : InvTm Δ .unit) := by
  cases h
  rfl

theorem InvTm.castCtx_foc_pos {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (h : Γ = Δ) (p : PosNeu Γ A) :
    InvTm.castCtx h (.foc (.pos (.done p))) =
      .foc (.pos (.done (h ▸ p))) := by
  cases h
  rfl

theorem InvTm.castCtx_foc_neg {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (h : Γ = Δ) (n : NegNeu Γ A) :
    InvTm.castCtx h (.foc (.neg (.done n))) =
      .foc (.neg (.done (h ▸ n))) := by
  cases h
  rfl

theorem InvTm.castCtx_foc_sat {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (h : Γ = Δ) (s : Schedule sig.nBases) (t : InvTm Γ A) :
    InvTm.castCtx h (.foc (.sat (.mk s t))) =
      .foc (.sat (.mk s (InvTm.castCtx h t))) := by
  cases h
  rfl

theorem InvTm.castCtx_foc_letPos {Γ Δ : Ctx sig} {P A : Object sig.nBases}
    (h : Γ = Δ) (n : NegNeu Γ P) (t : InvTm (Γ ▻ P) A) :
    InvTm.castCtx h (.foc (.letPos n t)) =
      .foc (.letPos (h ▸ n) (congrArg (fun Γ => Γ ▻ P) h ▸ t)) := by
  cases h
  rfl

/-- Cast `ofHyps.push` unit onto the encode branch schedule (base-only). -/
theorem encodeReady_unit_leftCoprodBranch_cast
    (hyps : Array (Object sig.nBases)) (L : Object sig.nBases)
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (hbr : worklistBasesOnly (leftCoprodBranchWs ws e side L)) :
    EncodeReady (leftCoprodBranchWs ws e side L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0
      (InvTm.castCtx (Ctx.ofHyps_push hyps L)
        (.unit : InvTm (Ctx.ofHyps (hyps.push L)) .unit)) := by
  rw [InvTm.castCtx_unit]
  exact encodeReady_unit_leftCoprodBranch hyps L e ws side hbr

/-- Cast `ofHyps.push` foc-pos onto the encode branch schedule (base-only). -/
theorem encodeReady_foc_pos_leftCoprodBranch_cast
    (hyps : Array (Object sig.nBases)) {A L : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (p : PosNeu (Ctx.ofHyps (hyps.push L)) A)
    (hbr : worklistBasesOnly (leftCoprodBranchWs ws e side L))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    EncodeReady (leftCoprodBranchWs ws e side L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0
      (InvTm.castCtx (Ctx.ofHyps_push hyps L) (.foc (.pos (.done p)))) := by
  rw [InvTm.castCtx_foc_pos]
  exact encodeReady_foc_pos_leftCoprodBranch hyps e ws side
    ((Ctx.ofHyps_push hyps L) ▸ p) hbr hfr

/-- Cast `ofHyps.push` foc-neg onto the encode branch schedule (base-only). -/
theorem encodeReady_foc_neg_leftCoprodBranch_cast
    (hyps : Array (Object sig.nBases)) {A L : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (n : NegNeu (Ctx.ofHyps (hyps.push L)) A)
    (hbr : worklistBasesOnly (leftCoprodBranchWs ws e side L))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    EncodeReady (leftCoprodBranchWs ws e side L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0
      (InvTm.castCtx (Ctx.ofHyps_push hyps L) (.foc (.neg (.done n)))) := by
  rw [InvTm.castCtx_foc_neg]
  exact encodeReady_foc_neg_leftCoprodBranch hyps e ws side
    ((Ctx.ofHyps_push hyps L) ▸ n) hbr hfr

/-- Cast `ofHyps.push` sat-of-foc-pos onto the encode branch schedule. -/
theorem encodeReady_foc_sat_focPos_leftCoprodBranch_cast
    (hyps : Array (Object sig.nBases)) {A L : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (s : Schedule sig.nBases) (p : PosNeu (Ctx.ofHyps (hyps.push L)) A)
    (hbr : worklistBasesOnly (leftCoprodBranchWs ws e side L))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    EncodeReady (leftCoprodBranchWs ws e side L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0
      (InvTm.castCtx (Ctx.ofHyps_push hyps L)
        (.foc (.sat (.mk s (.foc (.pos (.done p))))))) := by
  rw [InvTm.castCtx_foc_sat, InvTm.castCtx_foc_pos]
  have ht :
      EncodeReady ([] : List (PosEntry sig))
        (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin side))
        0 0
        (.foc (.pos (.done ((Ctx.ofHyps_push hyps L) ▸ p)))) :=
    encodeReady_foc_pos_nil _ 0 0 _ hfr
  exact encodeReady_foc_sat_leftCoprodBranch hyps e ws side s _ hbr hfr ht

/-- Empty phase worklist: `.unit` is phase-encode-ready. -/
theorem phaseEncodeReady_unit_nil_worklist
    {hyps : Array (Object sig.nBases)}
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = []) :
    PhaseEncodeReady (.unit (Γ := Ctx.ofHyps hyps)) := by
  simpa [PhaseEncodeReady, hws] using
    encodeReady_unit_nil (OriginEnv.ofHyps hyps) 0 0

/-- Base-only (or empty) worklist + `focus`: done positive focus is ready. -/
theorem phaseEncodeReady_foc_pos_bases_focus
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (p : PosNeu (Ctx.ofHyps hyps) A)
    (hws : ∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    PhaseEncodeReady (.foc (.pos (.done p))) := by
  refine encodeReady_of_noPeel ?_
  -- reuse moveStable stripping from `encodeReady_foc_letPos_basesOnly_noPeel` pattern
  have go :
      ∀ ws,
        (∀ e ∈ ws, ∃ b : Fin sig.nBases, e.ty = .base b) →
        EncodeReadyNoPeel ws (OriginEnv.ofHyps hyps) 0 0
          (.foc (.pos (.done p))) := by
    intro ws hws'
    induction ws with
    | nil => exact .focus hfr .pos
    | cons e ws ih =>
        have ⟨b, hb⟩ := hws' e (List.Mem.head _)
        exact .moveStable (forcedRule_cons_base_moveStable e ws hb A)
          (ih fun e' he' => hws' e' (List.Mem.tail _ he'))
  simpa [PhaseEncodeReady] using go _ hws

theorem phaseEncodeReady_foc_neg_bases_focus
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (n : NegNeu (Ctx.ofHyps hyps) A)
    (hws : ∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    PhaseEncodeReady (.foc (.neg (.done n))) := by
  refine encodeReady_of_noPeel ?_
  have go :
      ∀ ws,
        (∀ e ∈ ws, ∃ b : Fin sig.nBases, e.ty = .base b) →
        EncodeReadyNoPeel ws (OriginEnv.ofHyps hyps) 0 0
          (.foc (.neg (.done n))) := by
    intro ws hws'
    induction ws with
    | nil => exact .focus hfr .neg
    | cons e ws ih =>
        have ⟨b, hb⟩ := hws' e (List.Mem.head _)
        exact .moveStable (forcedRule_cons_base_moveStable e ws hb A)
          (ih fun e' he' => hws' e' (List.Mem.tail _ he'))
  simpa [PhaseEncodeReady] using go _ hws

/-! ### WellInv → PhaseEncodeReady under bases-only (empty-schedule substrate)

Empty `applyPairObs` returns the continuation unchanged. Raw already has
`WellInv` of that continuation; under a bases-only ofHyps worklist the
intro/focus shapes below are PhaseEncodeReady with no ready stash.
-/

/-- Bases-only + WellInv `.unit` ⇒ phase ready. -/
theorem phaseEncodeReady_of_wellInv_unit_bases
    {hyps : Array (Object sig.nBases)}
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (_hw : WellInv (.unit : InvTm (Ctx.ofHyps hyps) .unit)) :
    PhaseEncodeReady (.unit : InvTm (Ctx.ofHyps hyps) .unit) :=
  encodeReady_unit_basesOnly _
    (OriginEnv.ofHyps hyps) 0 0 hws

/-- Bases-only + focus + WellFoc.pos ⇒ phase ready. -/
theorem phaseEncodeReady_of_wellInv_foc_pos_bases
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (p : PosNeu (Ctx.ofHyps hyps) A)
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hw : WellInv (.foc (.pos (.done p)) : InvTm (Ctx.ofHyps hyps) A)) :
    PhaseEncodeReady (.foc (.pos (.done p))) := by
  cases hw with
  | foc hf =>
      cases hf with
      | pos _ _ => exact phaseEncodeReady_foc_pos_bases_focus p hws hfr

/-- Bases-only + `rightProd` + WellFoc.neg ⇒ phase ready. -/
theorem phaseEncodeReady_of_wellInv_foc_neg_prod_bases
    {hyps : Array (Object sig.nBases)} {L R : Object sig.nBases}
    (n : NegNeu (Ctx.ofHyps hyps) (.prod L R))
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hw : WellInv
      (.foc (.neg (.done n)) : InvTm (Ctx.ofHyps hyps) (.prod L R))) :
    PhaseEncodeReady (.foc (.neg (.done n))) := by
  cases hw with
  | foc hf =>
      cases hf with
      | neg _ _ =>
          refine encodeReady_of_noPeel ?_
          have go :
              ∀ ws,
                worklistBasesOnly ws →
                EncodeReadyNoPeel ws (OriginEnv.ofHyps hyps) 0 0
                  (.foc (.neg (.done n)) :
                    InvTm (Ctx.ofHyps hyps) (.prod L R)) := by
            intro ws hws'
            induction ws with
            | nil => exact .rightProd_foc rfl .neg
            | cons e ws ih =>
                have ⟨b, hb⟩ := hws' e (List.Mem.head _)
                exact .moveStable
                  (forcedRule_cons_base_moveStable e ws hb (.prod L R))
                  (ih fun e' he' => hws' e' (List.Mem.tail _ he'))
          simpa [PhaseEncodeReady] using go _ hws

/-- Bases-only + `rightExp` + WellFoc.neg ⇒ phase ready. -/
theorem phaseEncodeReady_of_wellInv_foc_neg_exp_bases
    {hyps : Array (Object sig.nBases)} {Arg Ret : Object sig.nBases}
    (n : NegNeu (Ctx.ofHyps hyps) (.exp Arg Ret))
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hw : WellInv
      (.foc (.neg (.done n)) : InvTm (Ctx.ofHyps hyps) (.exp Arg Ret))) :
    PhaseEncodeReady (.foc (.neg (.done n))) := by
  cases hw with
  | foc hf =>
      cases hf with
      | neg _ _ =>
          refine encodeReady_of_noPeel ?_
          have go :
              ∀ ws,
                worklistBasesOnly ws →
                EncodeReadyNoPeel ws (OriginEnv.ofHyps hyps) 0 0
                  (.foc (.neg (.done n)) :
                    InvTm (Ctx.ofHyps hyps) (.exp Arg Ret)) := by
            intro ws hws'
            induction ws with
            | nil => exact .rightExp_foc rfl .neg
            | cons e ws ih =>
                have ⟨b, hb⟩ := hws' e (List.Mem.head _)
                exact .moveStable
                  (forcedRule_cons_base_moveStable e ws hb (.exp Arg Ret))
                  (ih fun e' he' => hws' e' (List.Mem.tail _ he'))
          simpa [PhaseEncodeReady] using go _ hws

/-- Bases-only + focus + sat of a focus-typed foc-pos body ⇒ phase ready. -/
theorem phaseEncodeReady_of_wellInv_foc_sat_focPos_bases
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (s : Schedule sig.nBases) (p : PosNeu (Ctx.ofHyps hyps) A)
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (_hw : WellInv
      (.foc (.sat (.mk s (.foc (.pos (.done p))))) :
        InvTm (Ctx.ofHyps hyps) A)) :
    PhaseEncodeReady
      (.foc (.sat (.mk s (.foc (.pos (.done p)))))) := by
  have hbody :
      EncodeReady ([] : List (PosEntry sig)) (OriginEnv.ofHyps hyps) 0 0
        (.foc (.pos (.done p))) :=
    encodeReady_foc_pos_nil (OriginEnv.ofHyps hyps) 0 0 p hfr
  exact encodeReady_foc_sat_basesOnly _
    (OriginEnv.ofHyps hyps) 0 0 s _ hws hfr hbody

/-- Invert `moveStable` when the worklist head is a base. -/
theorem encodeReadyNoPeel_tail_of_base_head
    {Γ : Ctx sig} {A : Object sig.nBases}
    {e : PosEntry sig} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {domNest obsSlot : Nat} {t : InvTm Γ A}
    (hty : ∃ b : Fin sig.nBases, e.ty = .base b)
    (h : EncodeReadyNoPeel (e :: ws) ε domNest obsSlot t) :
    EncodeReadyNoPeel ws ε domNest obsSlot t := by
  have ⟨b, hb⟩ := hty
  have hfr0 : forcedRule (e :: ws) A = .moveStable e :=
    forcedRule_cons_base_moveStable e ws hb A
  refine
    (EncodeReadyNoPeel.rec
      (motive_1 := fun {Γ} ws' ε' d o {A} t' _ =>
        ∀ (e' : PosEntry sig) (wsTail : List (PosEntry sig))
          (_hws : ws' = e' :: wsTail)
          (_hty : ∃ b : Fin sig.nBases, e'.ty = .base b),
          EncodeReadyNoPeel wsTail ε' d o t')
      (motive_2 := fun {Γ} ws' ε' d o {A} f _ =>
        ∀ (_e' : PosEntry sig) (_wsTail : List (PosEntry sig))
          (_hws : ws' = _e' :: _wsTail)
          (_hty : ∃ b : Fin sig.nBases, _e'.ty = .base b),
          True)
      ?ms ?ln ?ru ?rp ?rpf ?re ?ref ?fo ?pos ?neg ?lp ?sat h) e ws rfl hty
  case ms =>
    intro Γ A e' ws' ε d o t hfr _ ih e'' wsTail hws hty'
    cases hws
    exact ‹EncodeReadyNoPeel ws' ε d o t›
  case ln =>
    intro Γ A e' ws' ε d o n hty' e'' wsTail hws ⟨b, hb⟩
    cases hws
    simp [hb] at hty'
  case ru =>
    intro Γ ws' ε d o hfr e'' wsTail hws ⟨b, hb⟩
    cases hws
    simp [forcedRule, hb] at hfr
  case rp =>
    intro Γ L R ws' ε d o t u hfr _ _ _ _ e'' wsTail hws ⟨b, hb⟩
    cases hws
    simp [forcedRule, hb] at hfr
  case rpf =>
    intro Γ L R ws' ε d o f hfr _ _ e'' wsTail hws ⟨b, hb⟩
    cases hws
    simp [forcedRule, hb] at hfr
  case re =>
    intro Γ Arg Ret ws' ε d o body hfr _ _ e'' wsTail hws ⟨b, hb⟩
    cases hws
    simp [forcedRule, hb] at hfr
  case ref =>
    intro Γ Arg Ret ws' ε d o f hfr _ _ e'' wsTail hws ⟨b, hb⟩
    cases hws
    simp [forcedRule, hb] at hfr
  case fo =>
    intro Γ A ws' ε d o f hfr _ _ e'' wsTail hws ⟨b, hb⟩
    cases hws
    simp [forcedRule, hb] at hfr
  case pos => intros; trivial
  case neg => intros; trivial
  case lp => intros; trivial
  case sat => intros; trivial

theorem encodeReadyNoPeel_of_base_prefix
    {Γ : Ctx sig} {A : Object sig.nBases}
    {pref ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {domNest obsSlot : Nat} {t : InvTm Γ A}
    (hpref : ∀ e ∈ pref, ∃ b : Fin sig.nBases, e.ty = .base b)
    (h : EncodeReadyNoPeel (pref ++ ws) ε domNest obsSlot t) :
    EncodeReadyNoPeel ws ε domNest obsSlot t := by
  induction pref with
  | nil => exact h
  | cons e pref ih =>
      exact ih (fun e' he' => hpref e' (List.Mem.tail _ he'))
        (encodeReadyNoPeel_tail_of_base_head
          (hpref e (List.Mem.head _)) h)

/-- Invert `moveStable` when the worklist head is a base (`EncodeReady`). -/
theorem encodeReady_tail_of_base_head
    {Γ : Ctx sig} {A : Object sig.nBases}
    {e : PosEntry sig} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {domNest obsSlot : Nat} {t : InvTm Γ A}
    (hty : ∃ b : Fin sig.nBases, e.ty = .base b)
    (h : EncodeReady (e :: ws) ε domNest obsSlot t) :
    EncodeReady ws ε domNest obsSlot t := by
  have ⟨b, hb⟩ := hty
  refine
    (EncodeReady.rec
      (motive_1 := fun {Γ} ws' ε' d o {A} t' _ =>
        ∀ (e' : PosEntry sig) (wsTail : List (PosEntry sig))
          (_hws : ws' = e' :: wsTail)
          (_hty : ∃ b : Fin sig.nBases, e'.ty = .base b),
          EncodeReady wsTail ε' d o t')
      (motive_2 := fun {Γ} ws' ε' d o {A} f _ =>
        ∀ (_e' : PosEntry sig) (_wsTail : List (PosEntry sig))
          (_hws : ws' = _e' :: _wsTail)
          (_hty : ∃ b : Fin sig.nBases, _e'.ty = .base b),
          True)
      ?ms ?ln ?ru ?rp ?rpf ?re ?ref ?lp ?lu ?fo ?pos ?neg ?letp ?sat h)
      e ws rfl hty
  case ms =>
    intro Γ A e' ws' ε d o t hfr _ ih e'' wsTail hws hty'
    cases hws
    exact ‹EncodeReady ws' ε d o t›
  case ln =>
    intro Γ A e' ws' ε d o n hty' e'' wsTail hws ⟨b, hb⟩
    cases hws; simp [hb] at hty'
  case ru =>
    intro Γ ws' ε d o hfr e'' wsTail hws ⟨b, hb⟩
    cases hws; simp [forcedRule, hb] at hfr
  case rp =>
    intro Γ L R ws' ε d o t u hfr _ _ _ _ e'' wsTail hws ⟨b, hb⟩
    cases hws; simp [forcedRule, hb] at hfr
  case rpf =>
    intro Γ L R ws' ε d o f hfr _ _ e'' wsTail hws ⟨b, hb⟩
    cases hws; simp [forcedRule, hb] at hfr
  case re =>
    intro Γ Arg Ret ws' ε d o body hfr _ _ e'' wsTail hws ⟨b, hb⟩
    cases hws; simp [forcedRule, hb] at hfr
  case ref =>
    intro Γ Arg Ret ws' ε d o f hfr _ _ e'' wsTail hws ⟨b, hb⟩
    cases hws; simp [forcedRule, hb] at hfr
  case lp =>
    intro Γ A L R e' ws' ε d o n tL tR t hfr hpeel _ _ _ _ e'' wsTail hws ⟨b, hb⟩
    cases hws; simp [forcedRule, hb] at hfr
  case lu =>
    intro Γ L R e' ws' ε d o x hfr hfind hit _ _ _ _ e'' wsTail hws ⟨b, hb⟩
    cases hws; simp [forcedRule, hb] at hfr
  case fo =>
    intro Γ A ws' ε d o f hfr _ _ e'' wsTail hws ⟨b, hb⟩
    cases hws; simp [forcedRule, hb] at hfr
  case pos => intros; trivial
  case neg => intros; trivial
  case letp => intros; trivial
  case sat => intros; trivial

theorem encodeReady_of_base_prefix
    {Γ : Ctx sig} {A : Object sig.nBases}
    {pref ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {domNest obsSlot : Nat} {t : InvTm Γ A}
    (hpref : ∀ e ∈ pref, ∃ b : Fin sig.nBases, e.ty = .base b)
    (h : EncodeReady (pref ++ ws) ε domNest obsSlot t) :
    EncodeReady ws ε domNest obsSlot t := by
  induction pref with
  | nil => exact h
  | cons e pref ih =>
      exact ih (fun e' he' => hpref e' (List.Mem.tail _ he'))
        (encodeReady_tail_of_base_head (hpref e (List.Mem.head _)) h)

/--
Base-only outer worklist: after stripping `moveStable` bases, `focus` + `letPos`
with body ready under `pushPos [] (.obs 0)` (empty remaining worklist).
Combined with `encodeReady_newest_hyp_to_obs_noPeel` + base-prefix inversion
when the rekeyed push worklist is `bases ++ [obs]`.
-/
theorem encodeReady_foc_letPos_basesOnly_noPeel
    {Γ : Ctx sig} {A P : Object sig.nBases}
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {n : NegNeu Γ P} {body : InvTm (Γ ▻ P) A}
    (hws : ∀ e ∈ ws, ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hbody : EncodeReadyNoPeel
      (pushPos ([] : List (PosEntry sig)) (.obs (sig := sig) 0) P)
      (OriginEnv.weaken (A := P) ε (.obs (sig := sig) 0))
      0 1 body) :
    EncodeReadyNoPeel ws ε 0 0 (.foc (.letPos n body)) := by
  induction ws with
  | nil =>
      exact .focus hfr (.letPos hbody)
  | cons e ws ih =>
      have ⟨b, hb⟩ := hws e (List.Mem.head _)
      exact .moveStable (forcedRule_cons_base_moveStable e ws hb A)
        (ih fun e' he' => hws e' (List.Mem.tail _ he'))

/-- Full `EncodeReady` form: body may use peel / unit-η (e.g. left-coprod under obs). -/
theorem encodeReady_foc_letPos_basesOnly
    {Γ : Ctx sig} {A P : Object sig.nBases}
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {n : NegNeu Γ P} {body : InvTm (Γ ▻ P) A}
    (hws : ∀ e ∈ ws, ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hbody : EncodeReady
      (pushPos ([] : List (PosEntry sig)) (.obs (sig := sig) 0) P)
      (OriginEnv.weaken (A := P) ε (.obs (sig := sig) 0))
      0 1 body) :
    EncodeReady ws ε 0 0 (.foc (.letPos n body)) := by
  induction ws with
  | nil =>
      exact .focus hfr (.letPos hbody)
  | cons e ws ih =>
      have ⟨b, hb⟩ := hws e (List.Mem.head _)
      exact .moveStable (forcedRule_cons_base_moveStable e ws hb A)
        (ih fun e' he' => hws e' (List.Mem.tail _ he'))

/--
Atom-shaped result `.foc (.letPos …)` is phase-encode-ready when the phase
worklist is base-only, the goal focuses under an empty remainder, and the
binder body is peel-free ready under `pushPos [] (.obs 0)` (e.g. after
newest-hyp rekey + base-prefix inversion).
-/
theorem encodeReady_applyObsNeu_atom_basesOnly
    {hyps : Array (Object sig.nBases)} {A P : Object sig.nBases}
    {n : NegNeu (Ctx.ofHyps hyps) P}
    {body : InvTm (Ctx.ofHyps hyps ▻ P) A}
    (hws : ∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hbody : EncodeReadyNoPeel
      (pushPos ([] : List (PosEntry sig)) (.obs (sig := sig) 0) P)
      (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.obs (sig := sig) 0))
      0 1 body) :
    PhaseEncodeReady
      (.foc (.letPos n body) : InvTm (Ctx.ofHyps hyps) A) := by
  simpa [PhaseEncodeReady] using
    encodeReady_of_noPeel
      (encodeReady_foc_letPos_basesOnly_noPeel hws hfr hbody)

/-- Atom `letPos` with a full-ready body (peel allowed under the observation). -/
theorem encodeReady_applyObsNeu_atom
    {hyps : Array (Object sig.nBases)} {A P : Object sig.nBases}
    {n : NegNeu (Ctx.ofHyps hyps) P}
    {body : InvTm (Ctx.ofHyps hyps ▻ P) A}
    (hws : ∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hbody : EncodeReady
      (pushPos ([] : List (PosEntry sig)) (.obs (sig := sig) 0) P)
      (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.obs (sig := sig) 0))
      0 1 body) :
    PhaseEncodeReady
      (.foc (.letPos n body) : InvTm (Ctx.ofHyps hyps) A) :=
  encodeReady_foc_letPos_basesOnly hws hfr hbody

/-! ### `Ctx.ofHyps_push` cast transport (atom / applyObsNeu) -/

/-- Transport peel-free readiness along a context equality. -/
theorem encodeReadyNoPeel_castCtx {Γ Δ : Ctx sig} (hΓ : Γ = Δ)
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ} {ε' : OriginEnv Δ}
    {domNest obsSlot : Nat} {A : Object sig.nBases} {t : InvTm Γ A}
    (hε : ∀ {B} (x : Var Γ B), ε x = ε' (hΓ ▸ x))
    (h : EncodeReadyNoPeel ws ε domNest obsSlot t) :
    EncodeReadyNoPeel ws ε' domNest obsSlot (InvTm.castCtx hΓ t) := by
  subst hΓ
  exact encodeReadyNoPeel_env_eq (fun {B} x => hε x) h

theorem encodeReadyFocNoPeel_castCtx {Γ Δ : Ctx sig} (hΓ : Γ = Δ)
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ} {ε' : OriginEnv Δ}
    {domNest obsSlot : Nat} {A : Object sig.nBases} {f : FocTm Γ A}
    (hε : ∀ {B} (x : Var Γ B), ε x = ε' (hΓ ▸ x))
    (h : EncodeReadyFocNoPeel ws ε domNest obsSlot f) :
    EncodeReadyFocNoPeel ws ε' domNest obsSlot (hΓ ▸ f) := by
  subst hΓ
  -- reuse env transport via the mutual rec already in encodeReadyNoPeel_env_eq's foc motive
  refine
    (EncodeReadyFocNoPeel.rec
      (motive_1 := fun {Γ} ws ε d o {A} t _ =>
        ∀ ε' : OriginEnv Γ, (∀ {B} (x : Var Γ B), ε x = ε' x) →
          EncodeReadyNoPeel ws ε' d o t)
      (motive_2 := fun {Γ} ws ε d o {A} f _ =>
        ∀ ε' : OriginEnv Γ, (∀ {B} (x : Var Γ B), ε x = ε' x) →
          EncodeReadyFocNoPeel ws ε' d o f)
      ?ms ?ln ?ru ?rp ?rpf ?re ?ref ?fo ?pos ?neg ?lp ?sat h) ε' hε
  case ms =>
    intro Γ A e ws ε d o t hfr _ ih ε' hε'
    exact .moveStable hfr (ih ε' hε')
  case ln => intros; exact .leftNever ‹_›
  case ru => intros; exact .rightUnit ‹_›
  case rp =>
    intro Γ L R ws ε d o t u hfr _ _ iht ihu ε' hε'
    exact .rightProd_pair hfr (iht ε' hε') (ihu ε' hε')
  case rpf =>
    intro Γ L R ws ε d o f hfr _ ihf ε' hε'
    exact .rightProd_foc hfr (ihf ε' hε')
  case re =>
    intro Γ Arg Ret ws ε d o body hfr _ ihb ε' hε'
    refine .rightExp_lam hfr (ihb (OriginEnv.weaken (A := Arg) ε' (.dom (sig := sig) d)) ?_)
    intro B x; cases x with | here => rfl | there y => exact hε' y
  case ref =>
    intro Γ Arg Ret ws ε d o f hfr _ ihf ε' hε'
    exact .rightExp_foc hfr (ihf ε' hε')
  case fo =>
    intro Γ A ws ε d o f hfr _ ihf ε' hε'
    exact .focus hfr (ihf ε' hε')
  case pos => intros; exact .pos
  case neg => intros; exact .neg
  case lp =>
    intro Γ P A ws ε d o n t _ iht ε' hε'
    refine .letPos (iht (OriginEnv.weaken (A := P) ε' (.obs (sig := sig) o)) ?_)
    intro B x; cases x with | here => rfl | there y => exact hε' y
  case sat =>
    intro Γ A ws ε d o s t _ iht ε' hε'
    exact .sat (iht ε' hε')

/--
Cast recursive `ofHyps (hyps.push P)` readiness onto the weaken-hyp snoc
environment used by newest-hyp → obs rekey.
-/
theorem encodeReadyNoPeel_ofHyps_push
    (hyps : Array (Object sig.nBases)) (P : Object sig.nBases)
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps (hyps.push P)) A}
    (h : EncodeReadyNoPeel
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
      (OriginEnv.ofHyps (hyps.push P)) 0 0 t) :
    EncodeReadyNoPeel
      (OriginEnv.posWorklist
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size)))
      (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.hyp (sig := sig) hyps.size))
      0 0
      (InvTm.castCtx (Ctx.ofHyps_push hyps P) t) := by
  have hctx := Ctx.ofHyps_push hyps P
  have hws := posWorklist_ofHyps_push (sig := sig) hyps P
  have h' :
      EncodeReadyNoPeel
        (OriginEnv.posWorklist
          (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
            (.hyp (sig := sig) hyps.size)))
        (OriginEnv.ofHyps (hyps.push P)) 0 0 t := by
    simpa [hws] using h
  exact encodeReadyNoPeel_castCtx hctx
    (fun {B} y => OriginEnv.ofHyps_eq_weaken_hyp_cast hyps P y) h'

/-- Push-body readiness → obs-side readiness under `pushPos (ofHyps) (.obs 0)`. -/
theorem encodeReadyNoPeel_ofHyps_push_to_obs
    (hyps : Array (Object sig.nBases)) (P : Object sig.nBases)
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps (hyps.push P)) A}
    (h : EncodeReadyNoPeel
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
      (OriginEnv.ofHyps (hyps.push P)) 0 0 t) :
    EncodeReadyNoPeel
      (pushPos (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))
        (.obs (sig := sig) 0) P)
      (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.obs (sig := sig) 0))
      0 1
      (InvTm.castCtx (Ctx.ofHyps_push hyps P) t) :=
  encodeReady_newest_hyp_to_obs_noPeel hyps P
    (encodeReadyNoPeel_ofHyps_push hyps P h)

/-- Transport full `EncodeReady` along a context equality. -/
theorem encodeReady_castCtx {Γ Δ : Ctx sig} (hΓ : Γ = Δ)
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ} {ε' : OriginEnv Δ}
    {domNest obsSlot : Nat} {A : Object sig.nBases} {t : InvTm Γ A}
    (hε : ∀ {B} (x : Var Γ B), ε x = ε' (hΓ ▸ x))
    (h : EncodeReady ws ε domNest obsSlot t) :
    EncodeReady ws ε' domNest obsSlot (InvTm.castCtx hΓ t) := by
  subst hΓ
  exact encodeReady_env_eq (fun {B} x => hε x) h

theorem encodeReady_ofHyps_push
    (hyps : Array (Object sig.nBases)) (P : Object sig.nBases)
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps (hyps.push P)) A}
    (h : EncodeReady
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
      (OriginEnv.ofHyps (hyps.push P)) 0 0 t) :
    EncodeReady
      (OriginEnv.posWorklist
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size)))
      (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.hyp (sig := sig) hyps.size))
      0 0
      (InvTm.castCtx (Ctx.ofHyps_push hyps P) t) := by
  have hctx := Ctx.ofHyps_push hyps P
  have hws := posWorklist_ofHyps_push (sig := sig) hyps P
  have h' :
      EncodeReady
        (OriginEnv.posWorklist
          (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
            (.hyp (sig := sig) hyps.size)))
        (OriginEnv.ofHyps (hyps.push P)) 0 0 t := by
    simpa [hws] using h
  exact encodeReady_castCtx hctx
    (fun {B} y => OriginEnv.ofHyps_eq_weaken_hyp_cast hyps P y) h'

/-- Push-body full readiness → obs-side readiness (peel allowed under the binder). -/
theorem encodeReady_ofHyps_push_to_obs
    (hyps : Array (Object sig.nBases)) (P : Object sig.nBases)
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps (hyps.push P)) A}
    (h : EncodeReady
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
      (OriginEnv.ofHyps (hyps.push P)) 0 0 t) :
    EncodeReady
      (pushPos (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))
        (.obs (sig := sig) 0) P)
      (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.obs (sig := sig) 0))
      0 1
      (InvTm.castCtx (Ctx.ofHyps_push hyps P) t) :=
  encodeReady_newest_hyp_to_obs hyps P (encodeReady_ofHyps_push hyps P h)

/--
Observing under `ofHyps` appends the new obs after all hyp entries (hyp < obs).
-/
theorem pushPos_obs_ofHyps_eq_append (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases) (k : Nat) :
    pushPos (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))
        (.obs (sig := sig) k) P =
      OriginEnv.posWorklist (OriginEnv.ofHyps hyps) ++
        pushPos ([] : List (PosEntry sig)) (.obs (sig := sig) k) P := by
  dsimp only [pushPos]
  cases hpol : objectPolarity P == Polarity.pos
  · simp [hpol]
  · have hws : ∀ e ∈ OriginEnv.posCollect (OriginEnv.ofHyps hyps),
        ∃ i, e.origin = .hyp (sig := sig) i :=
      fun e he =>
        match posCollect_ofHyps_origin_hyp_lt hyps he with
        | ⟨i, _, hi⟩ => ⟨i, hi⟩
    let le : PosEntry sig → PosEntry sig → Bool :=
      fun a b => Origin.ble a.origin b.origin
    have hR := mergeSort_cons_obs_of_hyps
      ((OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort le) P k
      (fun e he => hws e (List.mem_mergeSort.mp he))
    have hid :
        ((OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort le).mergeSort le =
          (OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort le :=
      List.mergeSort_of_pairwise
        (List.pairwise_mergeSort ble_posEntry_trans ble_posEntry_total _)
    simp only [OriginEnv.posWorklist, hpol, ↓reduceIte]
    -- LHS: mergeSort (obs :: collect.mergeSort); RHS: collect.mergeSort ++ mergeSort [obs]
    change
      (({ origin := .obs (sig := sig) k, ty := P } ::
          (OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort le).mergeSort le) =
        (OriginEnv.posCollect (OriginEnv.ofHyps hyps)).mergeSort le ++
          ([{ origin := .obs (sig := sig) k, ty := P }] : List (PosEntry sig)).mergeSort le
    have hsingle :
        ([{ origin := .obs (sig := sig) k, ty := P }] : List (PosEntry sig)).mergeSort le =
          [{ origin := .obs (sig := sig) k, ty := P }] := by
      simp [le, List.mergeSort]
    rw [hR, hid, hsingle]

/--
Atom `applyObsNeu` wrap: recursive readiness on `ofHyps (hyps.push P)` casts
across `Ctx.ofHyps_push`, rekeys newest hyp → `.obs 0`, strips base prefix, and
packages outer `focus` + `letPos`.
-/
theorem encodeReady_applyObsNeu_atom_of_push_body
    {hyps : Array (Object sig.nBases)} {A P : Object sig.nBases}
    {n : NegNeu (Ctx.ofHyps hyps) P}
    {body : InvTm (Ctx.ofHyps (hyps.push P)) A}
    (hws : ∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hbody : EncodeReadyNoPeel
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
      (OriginEnv.ofHyps (hyps.push P)) 0 0 body) :
    PhaseEncodeReady
      (.foc (.letPos n (InvTm.castCtx (Ctx.ofHyps_push hyps P) body)) :
        InvTm (Ctx.ofHyps hyps) A) := by
  have hobs := encodeReadyNoPeel_ofHyps_push_to_obs hyps P hbody
  have happen := pushPos_obs_ofHyps_eq_append hyps P 0
  have hbody' :
      EncodeReadyNoPeel
        (pushPos ([] : List (PosEntry sig)) (.obs (sig := sig) 0) P)
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.obs (sig := sig) 0))
        0 1
        (InvTm.castCtx (Ctx.ofHyps_push hyps P) body) := by
    refine encodeReadyNoPeel_of_base_prefix hws ?_
    simpa [happen] using hobs
  exact encodeReady_applyObsNeu_atom_basesOnly hws hfr hbody'

/--
Full-ready push body (peel / left-coprod allowed under the new hyp): cast, rekey
newest hyp → `.obs 0`, strip base prefix, wrap outer `focus` + `letPos`.
This is the left-coprod-under-outer-`letPos` transport after peel dig readiness
on the extended hyp context.
-/
theorem encodeReady_applyObsNeu_atom_of_push_body_ready
    {hyps : Array (Object sig.nBases)} {A P : Object sig.nBases}
    {n : NegNeu (Ctx.ofHyps hyps) P}
    {body : InvTm (Ctx.ofHyps (hyps.push P)) A}
    (hws : ∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hbody : EncodeReady
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
      (OriginEnv.ofHyps (hyps.push P)) 0 0 body) :
    PhaseEncodeReady
      (.foc (.letPos n (InvTm.castCtx (Ctx.ofHyps_push hyps P) body)) :
        InvTm (Ctx.ofHyps hyps) A) := by
  have hobs := encodeReady_ofHyps_push_to_obs hyps P hbody
  have happen := pushPos_obs_ofHyps_eq_append hyps P 0
  have hbody' :
      EncodeReady
        (pushPos ([] : List (PosEntry sig)) (.obs (sig := sig) 0) P)
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.obs (sig := sig) 0))
        0 1
        (InvTm.castCtx (Ctx.ofHyps_push hyps P) body) := by
    refine encodeReady_of_base_prefix hws ?_
    simpa [happen] using hobs
  exact encodeReady_applyObsNeu_atom hws hfr hbody'

/-! ### Schedule application preserves EncodeReady -/

/-- Empty schedule: result is the continuation. -/
theorem encodeReady_applyPairObsGo_nil {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (fuel : Nat) (σ : ReachState sig.nBases)
    (cont : InvTm (Ctx.ofHyps hyps) A)
    (hcont : PhaseEncodeReady cont)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyPairObsGo (fuel + 1) σ hyps [] cont = .ok t') :
    PhaseEncodeReady t' := by
  simp only [applyPairObsGo] at hok
  cases hok
  exact hcont

/--
If the phase worklist is a `moveStable` (base) prefix followed by a `never`
head, an abort is phase-encode-ready.
-/
theorem encodeReady_abort_of_posWorklist_never {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (n : NegNeu (Ctx.ofHyps hyps) .never)
    {pref : List (PosEntry sig)} {e : PosEntry sig} {suf : List (PosEntry sig)}
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hty : e.ty = .never) :
    PhaseEncodeReady (.abort (A := A) n) := by
  have go :
      ∀ pref' : List (PosEntry sig),
        (∀ e' ∈ pref', ∃ b : Fin sig.nBases, e'.ty = .base b) →
        EncodeReady (pref' ++ e :: suf) (OriginEnv.ofHyps hyps) 0 0
          (.abort (A := A) n) := by
    intro pref' hpref'
    induction pref' with
    | nil =>
        exact .leftNever hty
    | cons e' pref' ih =>
        have ⟨b, hb⟩ := hpref' e' (List.Mem.head _)
        have hfr : forcedRule (e' :: (pref' ++ e :: suf)) A = .moveStable e' :=
          forcedRule_cons_base_moveStable e' _ hb A
        exact .moveStable hfr (ih fun e'' he'' => hpref' e'' (List.Mem.tail _ he''))
  simpa [PhaseEncodeReady, hws] using go pref hpref

/--
Top-level inconsistent `applyPairObs` returns abort. Ready when the phase
worklist has a never hyp (possibly after base/`moveStable` heads).
-/
theorem encodeReady_applyPairObs_inconsistent {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (fuel : Nat) (σ : ReachState sig.nBases)
    (entries : Array (PairEntry sig hyps))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    (hincons : σ.inconsistent = true)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyPairObs fuel σ hyps entries cont = .ok t')
    {pref : List (PosEntry sig)} {e : PosEntry sig} {suf : List (PosEntry sig)}
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hty : e.ty = .never) :
    PhaseEncodeReady t' := by
  simp only [applyPairObs, hincons, ↓reduceIte] at hok
  split at hok
  · cases hok
    exact encodeReady_abort_of_posWorklist_never _ hws hpref hty
  · exact absurd hok (by simp)

/--
Consistent `applyPairObs` with an empty schedule returns the continuation.
-/
theorem encodeReady_applyPairObs_emptyEntries {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (fuel : Nat) (σ : ReachState sig.nBases)
    (entries : Array (PairEntry sig hyps))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    (hcons : σ.inconsistent = false)
    (hempty : entries.toList = [])
    (hcont : PhaseEncodeReady cont)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyPairObs fuel σ hyps entries cont = .ok t') :
    PhaseEncodeReady t' := by
  simp only [applyPairObs, hcons, ↓reduceIte] at hok
  match fuel with
  | 0 => simp [applyPairObsGo] at hok
  | fuel + 1 =>
      simp only [hempty] at hok
      exact encodeReady_applyPairObsGo_nil fuel σ cont hcont hok

/--
Empty schedule: `applyPairObs` returns the continuation. Ready when the ofHyps
worklist is bases-only and the continuation is a WellInv intro/focus shape
below — discharges empty-schedule readiness from raw's `WellInv` (no ready stash).
-/
theorem encodeReady_applyPairObs_emptyEntries_of_wellInv_intro
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (entries : Array (PairEntry sig hyps))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    (hcons : σ.inconsistent = false)
    (hempty : entries.toList = [])
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hw : WellInv cont)
    (hshape :
      (∃ hA : A = (.unit : Object sig.nBases),
          HEq cont (.unit : InvTm (Ctx.ofHyps hyps) .unit)) ∨
      (∃ p : PosNeu (Ctx.ofHyps hyps) A,
          cont = .foc (.pos (.done p)) ∧
          forcedRule ([] : List (PosEntry sig)) A = .focus) ∨
      (∃ (L R : Object sig.nBases)
          (n : NegNeu (Ctx.ofHyps hyps) (.prod L R))
          (hA : A = .prod L R),
          HEq cont
            (.foc (.neg (.done n)) :
              InvTm (Ctx.ofHyps hyps) (.prod L R))) ∨
      (∃ (Arg Ret : Object sig.nBases)
          (n : NegNeu (Ctx.ofHyps hyps) (.exp Arg Ret))
          (hA : A = .exp Arg Ret),
          HEq cont
            (.foc (.neg (.done n)) :
              InvTm (Ctx.ofHyps hyps) (.exp Arg Ret))) ∨
      (∃ (s : Schedule sig.nBases) (p : PosNeu (Ctx.ofHyps hyps) A),
          cont = .foc (.sat (.mk s (.foc (.pos (.done p))))) ∧
          forcedRule ([] : List (PosEntry sig)) A = .focus))
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyPairObs fuel σ hyps entries cont = .ok t') :
    PhaseEncodeReady t' := by
  have hcont : PhaseEncodeReady cont := by
    match hshape with
    | .inl ⟨hA, hEq⟩ =>
        cases hA
        cases hEq
        exact phaseEncodeReady_of_wellInv_unit_bases hws hw
    | .inr (.inl ⟨p, hp, hfr⟩) =>
        cases hp
        exact phaseEncodeReady_of_wellInv_foc_pos_bases p hws hfr hw
    | .inr (.inr (.inl ⟨L, R, n, hA, hc⟩)) =>
        cases hA
        cases hc
        exact phaseEncodeReady_of_wellInv_foc_neg_prod_bases n hws hw
    | .inr (.inr (.inr (.inl ⟨Arg, Ret, n, hA, hc⟩))) =>
        cases hA
        cases hc
        exact phaseEncodeReady_of_wellInv_foc_neg_exp_bases n hws hw
    | .inr (.inr (.inr (.inr ⟨s, p, hc, hfr⟩))) =>
        cases hc
        exact phaseEncodeReady_of_wellInv_foc_sat_focPos_bases s p hws hfr hw
  exact encodeReady_applyPairObs_emptyEntries fuel σ entries cont hcons hempty
    hcont hok

/--
`applyObsNeu` on `.never` returns abort. Phase-ready when the ofHyps worklist
exposes a `never` head after a bases/`moveStable` prefix.
-/
theorem encodeReady_applyObsNeu_never {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (fuel : Nat) (σ : ReachState sig.nBases)
    (nP : NegNeu (Ctx.ofHyps hyps) .never)
    (rest : List (PairEntry sig hyps))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyObsNeu (fuel + 1) σ hyps .never nP rest cont = .ok t')
    {pref : List (PosEntry sig)} {e : PosEntry sig} {suf : List (PosEntry sig)}
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hty : e.ty = .never) :
    PhaseEncodeReady t' := by
  simp [applyObsNeu] at hok
  subst t'
  exact encodeReady_abort_of_posWorklist_never nP hws hpref hty

/-- Exact `.never` schedule head: `applyPairObsGo` steps to abort packaging. -/
theorem encodeReady_applyPairObsGo_exact_never {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (fuel : Nat) (σ : ReachState sig.nBases)
    (n : NegNeu (Ctx.ofHyps hyps) .never)
    (rest : List (PairEntry sig hyps))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyPairObsGo (fuel + 1) σ hyps (.exact .never n :: rest) cont = .ok t')
    {pref : List (PosEntry sig)} {e : PosEntry sig} {suf : List (PosEntry sig)}
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hty : e.ty = .never) :
    PhaseEncodeReady t' := by
  rw [applyPairObsGo.eq_def] at hok
  dsimp only at hok
  cases fuel with
  | zero => simp [applyObsNeu] at hok
  | succ fuel =>
      exact encodeReady_applyObsNeu_never fuel σ n rest cont hok hws hpref hty

/-- Entries are exclusively exact-`.never` observations (no consistency / atoms / coprods). -/
def exactNeverEntriesOnly {hyps : Array (Object sig.nBases)}
    (entries : List (PairEntry sig hyps)) : Prop :=
  ∀ e ∈ entries, ∃ n, e = .exact (.never) n

/--
`applyPairObsGo` under an exact-never-only schedule: empty returns the ready
continuation; a never head aborts (needs never on the phase worklist).
-/
theorem encodeReady_applyPairObsGo_exactNeverOnly {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (fuel : Nat) (σ : ReachState sig.nBases)
    (entries : List (PairEntry sig hyps))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hent : exactNeverEntriesOnly entries)
    (hok : applyPairObsGo (fuel + 1) σ hyps entries cont = .ok t')
    (hempty : entries = [] → PhaseEncodeReady cont)
    (hnever : entries ≠ [] →
      ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
        OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
        (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
        e.ty = .never) :
    PhaseEncodeReady t' := by
  match entries with
  | [] =>
      exact encodeReady_applyPairObsGo_nil fuel σ cont (hempty rfl) hok
  | e :: rest =>
      obtain ⟨n, heq⟩ := hent e (List.Mem.head _)
      cases heq
      obtain ⟨pref, eNe, suf, hws, hpref, hty⟩ := hnever (by simp)
      exact encodeReady_applyPairObsGo_exact_never fuel σ n rest cont hok
        hws hpref hty

/-- Continuation pushed under `ofHyps` for an atom observation. -/
def atomPushCont {hyps : Array (Object sig.nBases)} {P A : Object sig.nBases}
    (nP : NegNeu (Ctx.ofHyps hyps) P)
    (cont : InvTm (Ctx.ofHyps hyps) A) :
    InvTm (Ctx.ofHyps (hyps.push P)) A :=
  InvTm.castCtx (Ctx.ofHyps_push hyps P).symm
    (InvTm.abstr (P := P) .here (NegNeu.weaken (B := P) nP)
      (InvTm.weaken (B := P) cont))

/-- Pushing a base hyp onto a bases-only ofHyps worklist stays bases-only. -/
theorem worklistBasesOnly_ofHyps_push_base
    (hyps : Array (Object sig.nBases)) (b : Fin sig.nBases)
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))) :
    worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push (.base b)))) := by
  intro e he
  have hpc :
      OriginEnv.posCollect
          (OriginEnv.weaken (A := .base b) (OriginEnv.ofHyps hyps)
            (.hyp (sig := sig) hyps.size)) =
        ({ origin := .hyp (sig := sig) hyps.size, ty := .base b } : PosEntry sig) ::
          OriginEnv.posCollect (OriginEnv.ofHyps hyps) := by
    simpa [objectPolarity_base] using posCollect_weaken_hyp hyps (.base b)
  have he' :
      e ∈
        ({ origin := .hyp (sig := sig) hyps.size, ty := (.base b : Object sig.nBases) } :
            PosEntry sig) ::
          OriginEnv.posCollect (OriginEnv.ofHyps hyps) := by
    have : e ∈ OriginEnv.posWorklist
        (OriginEnv.weaken (A := .base b) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size)) := by
      simpa [posWorklist_ofHyps_push] using he
    simpa [OriginEnv.posWorklist, hpc, List.mem_mergeSort] using this
  cases he' with
  | head => exact ⟨b, rfl⟩
  | tail _ hmem =>
      exact hws e (List.mem_mergeSort.mpr hmem)

theorem InvTm.abstr_unit {Γ : Ctx sig} {P : Object sig.nBases}
    (x : Var Γ P) (m : NegNeu Γ P) :
    InvTm.abstr x m (.unit : InvTm Γ .unit) = .unit := by
  rw [InvTm.abstr]

theorem InvTm.weaken_unit {Γ : Ctx sig} {B : Object sig.nBases} :
    InvTm.weaken (B := B) (.unit : InvTm Γ .unit) = .unit := by
  rfl

theorem atomPushCont_unit {hyps : Array (Object sig.nBases)}
    {P : Object sig.nBases} (nP : NegNeu (Ctx.ofHyps hyps) P) :
    atomPushCont nP (.unit : InvTm (Ctx.ofHyps hyps) .unit) =
      (.unit : InvTm (Ctx.ofHyps (hyps.push P)) .unit) := by
  simp only [atomPushCont, InvTm.weaken_unit, InvTm.abstr_unit, InvTm.castCtx_unit]

/--
Nil-rest atom push body readiness from a unit continuation (no external
`atomPushCont` hypothesis): bases-only parent + base observation ⇒ unit under
`ofHyps.push`.
-/
theorem encodeReady_atomPushCont_unit
    {hyps : Array (Object sig.nBases)} {b : Fin sig.nBases}
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))) :
    EncodeReady
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push (.base b))))
      (OriginEnv.ofHyps (hyps.push (.base b))) 0 0
      (atomPushCont nP (.unit : InvTm (Ctx.ofHyps hyps) .unit)) := by
  rw [atomPushCont_unit]
  exact encodeReady_unit_basesOnly _
    (OriginEnv.ofHyps (hyps.push (.base b))) 0 0
    (worklistBasesOnly_ofHyps_push_base hyps b hws)

/-- Atom push of foc-pos is again foc-pos (under `ofHyps.push`). -/
theorem atomPushCont_is_foc_pos {hyps : Array (Object sig.nBases)}
    {P A : Object sig.nBases} (nP : NegNeu (Ctx.ofHyps hyps) P)
    (p : PosNeu (Ctx.ofHyps hyps) A) :
    ∃ p' : PosNeu (Ctx.ofHyps (hyps.push P)) A,
      atomPushCont nP (.foc (.pos (.done p))) = .foc (.pos (.done p')) := by
  let q : PosNeu (Ctx.ofHyps hyps ▻ P) A :=
    PosNeu.abstr (P := P) .here (NegNeu.weaken (B := P) nP)
      (PosNeu.rename (Rename.weaken (A := P)) p)
  refine ⟨(Ctx.ofHyps_push hyps P).symm ▸ q, ?_⟩
  simp only [atomPushCont, InvTm.weaken]
  change
    InvTm.castCtx (Ctx.ofHyps_push hyps P).symm
        (InvTm.abstr (P := P) .here (NegNeu.weaken (B := P) nP)
          (.foc (FocTm.rename (Rename.weaken (A := P)) (.pos (.done p))))) =
      .foc (.pos (.done ((Ctx.ofHyps_push hyps P).symm ▸ q)))
  rw [FocTm.rename, PosIntro.rename, InvTm.abstr, FocTm.abstr]
  exact InvTm.castCtx_foc_pos _ _

theorem atomPushCont_is_foc_neg {hyps : Array (Object sig.nBases)}
    {P A : Object sig.nBases} (nP : NegNeu (Ctx.ofHyps hyps) P)
    (n : NegNeu (Ctx.ofHyps hyps) A) :
    ∃ n' : NegNeu (Ctx.ofHyps (hyps.push P)) A,
      atomPushCont nP (.foc (.neg (.done n))) = .foc (.neg (.done n')) := by
  let q : NegNeu (Ctx.ofHyps hyps ▻ P) A :=
    NegNeu.abstr (P := P) .here (NegNeu.weaken (B := P) nP)
      (NegNeu.rename (Rename.weaken (A := P)) n)
  refine ⟨(Ctx.ofHyps_push hyps P).symm ▸ q, ?_⟩
  simp only [atomPushCont, InvTm.weaken]
  change
    InvTm.castCtx (Ctx.ofHyps_push hyps P).symm
        (InvTm.abstr (P := P) .here (NegNeu.weaken (B := P) nP)
          (.foc (FocTm.rename (Rename.weaken (A := P)) (.neg (.done n))))) =
      .foc (.neg (.done ((Ctx.ofHyps_push hyps P).symm ▸ q)))
  rw [FocTm.rename, NegElim.rename, InvTm.abstr, FocTm.abstr]
  exact InvTm.castCtx_foc_neg _ _

/-- Push-body ready for foc-pos continuation under bases-only + focus. -/
theorem encodeReady_atomPushCont_foc_pos
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {b : Fin sig.nBases}
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (p : PosNeu (Ctx.ofHyps hyps) A)
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    EncodeReady
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push (.base b))))
      (OriginEnv.ofHyps (hyps.push (.base b))) 0 0
      (atomPushCont nP (.foc (.pos (.done p)))) := by
  obtain ⟨p', hp'⟩ := atomPushCont_is_foc_pos nP p
  rw [hp']
  exact encodeReady_foc_pos_basesOnly _
    (OriginEnv.ofHyps (hyps.push (.base b))) 0 0 p'
    (worklistBasesOnly_ofHyps_push_base hyps b hws) hfr

theorem encodeReady_atomPushCont_foc_neg
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {b : Fin sig.nBases}
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (n : NegNeu (Ctx.ofHyps hyps) A)
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    EncodeReady
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push (.base b))))
      (OriginEnv.ofHyps (hyps.push (.base b))) 0 0
      (atomPushCont nP (.foc (.neg (.done n)))) := by
  obtain ⟨n', hn'⟩ := atomPushCont_is_foc_neg nP n
  rw [hn']
  exact encodeReady_foc_neg_basesOnly _
    (OriginEnv.ofHyps (hyps.push (.base b))) 0 0 n'
    (worklistBasesOnly_ofHyps_push_base hyps b hws) hfr

/-- Atom push distributes over outer `sat`. -/
theorem atomPushCont_foc_sat {hyps : Array (Object sig.nBases)}
    {P A : Object sig.nBases} (nP : NegNeu (Ctx.ofHyps hyps) P)
    (s : Schedule sig.nBases) (t : InvTm (Ctx.ofHyps hyps) A) :
    atomPushCont nP (.foc (.sat (.mk s t))) =
      .foc (.sat (.mk s (atomPushCont nP t))) := by
  simp only [atomPushCont, InvTm.weaken]
  change
    InvTm.castCtx (Ctx.ofHyps_push hyps P).symm
        (InvTm.abstr (P := P) .here (NegNeu.weaken (B := P) nP)
          (.foc (FocTm.rename (Rename.weaken (A := P)) (.sat (.mk s t))))) =
      .foc (.sat (.mk s
        (InvTm.castCtx (Ctx.ofHyps_push hyps P).symm
          (InvTm.abstr (P := P) .here (NegNeu.weaken (B := P) nP)
            (InvTm.rename (Rename.weaken (A := P)) t)))))
  rw [FocTm.rename, SatTm.rename, InvTm.abstr, FocTm.abstr]
  exact InvTm.castCtx_foc_sat _ _ _

/-- Push-body ready for sat-of-foc-pos continuation under bases-only + focus. -/
theorem encodeReady_atomPushCont_foc_sat_focPos
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {b : Fin sig.nBases}
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (s : Schedule sig.nBases) (p : PosNeu (Ctx.ofHyps hyps) A)
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    EncodeReady
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push (.base b))))
      (OriginEnv.ofHyps (hyps.push (.base b))) 0 0
      (atomPushCont nP
        (.foc (.sat (.mk s (.foc (.pos (.done p))))))) := by
  rw [atomPushCont_foc_sat]
  obtain ⟨p', hp'⟩ := atomPushCont_is_foc_pos nP p
  rw [hp']
  have hbody :
      EncodeReady ([] : List (PosEntry sig))
        (OriginEnv.ofHyps (hyps.push (.base b))) 0 0
        (.foc (.pos (.done p'))) :=
    encodeReady_foc_pos_nil (OriginEnv.ofHyps (hyps.push (.base b))) 0 0 p' hfr
  exact encodeReady_foc_sat_basesOnly _
    (OriginEnv.ofHyps (hyps.push (.base b))) 0 0 s _
    (worklistBasesOnly_ofHyps_push_base hyps b hws) hfr hbody

/--
Atom push of `letPos` around foc-pos stays `letPos` around foc-pos under
`ofHyps.push`.
-/
theorem atomPushCont_is_foc_letPos_focPos {hyps : Array (Object sig.nBases)}
    {P Q A : Object sig.nBases} (nP : NegNeu (Ctx.ofHyps hyps) P)
    (n : NegNeu (Ctx.ofHyps hyps) Q)
    (p : PosNeu (Ctx.ofHyps hyps ▻ Q) A) :
    ∃ (n' : NegNeu (Ctx.ofHyps (hyps.push P)) Q)
      (p' : PosNeu (Ctx.ofHyps (hyps.push P) ▻ Q) A),
      atomPushCont nP (.foc (.letPos n (.foc (.pos (.done p))))) =
        .foc (.letPos n' (.foc (.pos (.done p')))) := by
  let nA : NegNeu (Ctx.ofHyps hyps ▻ P) Q :=
    NegNeu.abstr (P := P) .here (NegNeu.weaken (B := P) nP)
      (NegNeu.rename (Rename.weaken (A := P)) n)
  let pA : PosNeu (Ctx.ofHyps hyps ▻ P ▻ Q) A :=
    PosNeu.abstr (P := P) (.there .here)
      (NegNeu.weaken (B := Q) (NegNeu.weaken (B := P) nP))
      (PosNeu.rename (Rename.ext (Rename.weaken (A := P))) p)
  refine
    ⟨(Ctx.ofHyps_push hyps P).symm ▸ nA,
      (congrArg (fun Γ => Γ ▻ Q) (Ctx.ofHyps_push hyps P).symm) ▸ pA, ?_⟩
  -- Unfold push to `castCtx.symm (.foc (.letPos nA (.foc (.pos (.done pA)))))`.
  have habstr :
      InvTm.abstr (P := P) .here (NegNeu.weaken (B := P) nP)
          (InvTm.weaken (B := P)
            (.foc (.letPos n (.foc (.pos (.done p)))) :
              InvTm (Ctx.ofHyps hyps) A)) =
        .foc (.letPos nA (.foc (.pos (.done pA)))) := by
    dsimp only [InvTm.weaken, InvTm.rename, FocTm.rename, PosIntro.rename,
      nA, pA]
    rw [InvTm.abstr, FocTm.abstr, InvTm.abstr, FocTm.abstr]
  have hcast :
      InvTm.castCtx (Ctx.ofHyps_push hyps P).symm
          (.foc (.letPos nA (.foc (.pos (.done pA))))) =
        .foc (.letPos ((Ctx.ofHyps_push hyps P).symm ▸ nA)
          (.foc (.pos (.done
            ((congrArg (fun Γ => Γ ▻ Q) (Ctx.ofHyps_push hyps P).symm) ▸
              pA))))) := by
    have h1 :=
      InvTm.castCtx_foc_letPos (Ctx.ofHyps_push hyps P).symm nA
        (.foc (.pos (.done pA)))
    have h2 :=
      InvTm.castCtx_foc_pos
        (congrArg (fun Γ => Γ ▻ Q) (Ctx.ofHyps_push hyps P).symm) pA
    rw [h1]
    exact
      congrArg
        (fun (t : InvTm (Ctx.ofHyps (hyps.push P) ▻ Q) A) =>
          (InvTm.foc
              (.letPos ((Ctx.ofHyps_push hyps P).symm ▸ nA) t) :
            InvTm (Ctx.ofHyps (hyps.push P)) A))
        h2
  simp only [atomPushCont]
  rw [habstr, hcast]

/-- `pushPos [] (.obs 0)` of a base is a singleton bases-only worklist. -/
theorem worklistBasesOnly_pushPos_obs_base (b : Fin sig.nBases) :
    worklistBasesOnly
      (pushPos ([] : List (PosEntry sig)) (.obs (sig := sig) 0) (.base b)) := by
  intro e he
  have : e ∈
      ({ origin := .obs (sig := sig) 0, ty := (.base b : Object sig.nBases) } :
          PosEntry sig) ::
        ([] : List (PosEntry sig)) := by
    simpa [pushPos, objectPolarity_base, List.mem_mergeSort] using he
  cases this with
  | head => exact ⟨b, rfl⟩
  | tail _ h => cases h

/--
Push-body ready for base-binder `letPos` around foc-pos under bases-only +
focus.
-/
theorem encodeReady_atomPushCont_foc_letPos_focPos_base
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {b bQ : Fin sig.nBases}
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (n : NegNeu (Ctx.ofHyps hyps) (.base bQ))
    (p : PosNeu (Ctx.ofHyps hyps ▻ (.base bQ)) A)
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    EncodeReady
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push (.base b))))
      (OriginEnv.ofHyps (hyps.push (.base b))) 0 0
      (atomPushCont nP
        (.foc (.letPos n (.foc (.pos (.done p)))))) := by
  obtain ⟨n', p', hp'⟩ := atomPushCont_is_foc_letPos_focPos nP n p
  rw [hp']
  have hbody :
      EncodeReady
        (pushPos ([] : List (PosEntry sig)) (.obs (sig := sig) 0) (.base bQ))
        (OriginEnv.weaken (A := .base bQ)
          (OriginEnv.ofHyps (hyps.push (.base b))) (.obs (sig := sig) 0))
        0 1 (.foc (.pos (.done p'))) :=
    encodeReady_foc_pos_basesOnly _
      (OriginEnv.weaken (A := .base bQ)
        (OriginEnv.ofHyps (hyps.push (.base b))) (.obs (sig := sig) 0))
      0 1 p' (worklistBasesOnly_pushPos_obs_base bQ) hfr
  exact encodeReady_foc_letPos_basesOnly
    (worklistBasesOnly_ofHyps_push_base hyps b hws) hfr hbody

/--
Continuation shapes from which base-atom nil-rest push-body `EncodeReady` is
derived (no external `atomPushCont` hypothesis): foc-done, sat-of-foc-pos, or
base-binder `letPos` around foc-pos.
-/
def AtomDerivedContShape {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (cont : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  (∃ p : PosNeu (Ctx.ofHyps hyps) A, cont = .foc (.pos (.done p))) ∨
  (∃ n : NegNeu (Ctx.ofHyps hyps) A, cont = .foc (.neg (.done n))) ∨
  (∃ (s : Schedule sig.nBases) (p : PosNeu (Ctx.ofHyps hyps) A),
    cont = .foc (.sat (.mk s (.foc (.pos (.done p)))))) ∨
  (∃ (bQ : Fin sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base bQ))
      (p : PosNeu (Ctx.ofHyps hyps ▻ (.base bQ)) A),
    cont = .foc (.letPos n (.foc (.pos (.done p)))))

/--
Push-body readiness from derived continuation shapes (foc-done, sat-of-foc-pos,
or base-binder `letPos` around foc-pos), without an external `atomPushCont`
hypothesis.
-/
theorem encodeReady_atomPushCont_of_focDone
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {b : Fin sig.nBases}
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hshape : AtomDerivedContShape cont) :
    EncodeReady
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push (.base b))))
      (OriginEnv.ofHyps (hyps.push (.base b))) 0 0
      (atomPushCont nP cont) := by
  match hshape with
  | .inl ⟨p, hp⟩ =>
      cases hp
      exact encodeReady_atomPushCont_foc_pos nP p hws hfr
  | .inr (.inl ⟨n, hn⟩) =>
      cases hn
      exact encodeReady_atomPushCont_foc_neg nP n hws hfr
  | .inr (.inr (.inl ⟨s, p, hp⟩)) =>
      cases hp
      exact encodeReady_atomPushCont_foc_sat_focPos nP s p hws hfr
  | .inr (.inr (.inr ⟨_bQ, n, p, hp⟩)) =>
      cases hp
      exact encodeReady_atomPushCont_foc_letPos_focPos_base nP n p hws hfr

/-- From a successful atom nil-rest observation, recover the `letPos` shape and
push body (`atomPushCont`). `fuel` is the inner empty-Go fuel
(`applyObsNeu (fuel+1)`); success requires `fuel ≥ 1`. -/
theorem applyObsNeu_atom_nil_rest_ok_inv {hyps : Array (Object sig.nBases)}
    {A P : Object sig.nBases} (fuel : Nat) (σ : ReachState sig.nBases)
    (nP : NegNeu (Ctx.ofHyps hyps) P)
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hne : P ≠ (.never : Object sig.nBases))
    (hnotSum : ∀ L R, P ≠ .coprod L R)
    (hok : applyObsNeu (fuel + 1) σ hyps P nP [] cont = .ok t') :
    t' = .foc (.letPos nP
      (InvTm.castCtx (Ctx.ofHyps_push hyps P) (atomPushCont nP cont))) ∧
    applyPairObsGo fuel σ (hyps.push P) [] (atomPushCont nP cont) =
      .ok (atomPushCont nP cont) := by
  cases P with
  | never =>
      exact absurd rfl hne
  | coprod L R =>
      exact absurd rfl (hnotSum L R)
  | base b =>
      rw [applyObsNeu] at hok
      dsimp only at hok
      -- `base` is neither never nor coprod; atom path with empty rest
      simp only [List.map_nil] at hok
      cases fuel with
      | zero => simp [applyPairObsGo] at hok
      | succ fuel =>
          simp only [applyPairObsGo, atomPushCont] at hok
          cases hok
          exact ⟨rfl, by simp [applyPairObsGo, atomPushCont]⟩
  | unit =>
      rw [applyObsNeu] at hok
      dsimp only at hok
      simp only [List.map_nil] at hok
      cases fuel with
      | zero => simp [applyPairObsGo] at hok
      | succ fuel =>
          simp only [applyPairObsGo, atomPushCont] at hok
          cases hok
          exact ⟨rfl, by simp [applyPairObsGo, atomPushCont]⟩
  | prod L R =>
      rw [applyObsNeu] at hok
      dsimp only at hok
      simp only [List.map_nil] at hok
      cases fuel with
      | zero => simp [applyPairObsGo] at hok
      | succ fuel =>
          simp only [applyPairObsGo, atomPushCont] at hok
          cases hok
          exact ⟨rfl, by simp [applyPairObsGo, atomPushCont]⟩
  | exp Arg Ret =>
      rw [applyObsNeu] at hok
      dsimp only at hok
      simp only [List.map_nil] at hok
      cases fuel with
      | zero => simp [applyPairObsGo] at hok
      | succ fuel =>
          simp only [applyPairObsGo, atomPushCont] at hok
          cases hok
          exact ⟨rfl, by simp [applyPairObsGo, atomPushCont]⟩

/--
Atom nil-rest readiness from Go success **without** a prior shape hypothesis:
inversion supplies `letPos`/`atomPushCont`, then existing push-body packaging.
-/
theorem encodeReady_applyObsNeu_atom_nil_rest_of_go
    {hyps : Array (Object sig.nBases)} {A P : Object sig.nBases}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (nP : NegNeu (Ctx.ofHyps hyps) P)
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hne : P ≠ (.never : Object sig.nBases))
    (hnotSum : ∀ L R, P ≠ .coprod L R)
    (hok : applyObsNeu (fuel + 1) σ hyps P nP [] cont = .ok t')
    (hws : ∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hbody : EncodeReady
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
      (OriginEnv.ofHyps (hyps.push P)) 0 0 (atomPushCont nP cont)) :
    PhaseEncodeReady t' := by
  obtain ⟨ht, _⟩ := applyObsNeu_atom_nil_rest_ok_inv fuel σ nP cont hne hnotSum hok
  cases ht
  exact encodeReady_applyObsNeu_atom_of_push_body_ready hws hfr hbody

/-- Exact atom, empty remainder: Go inversion + push-body ready (no shape hyp). -/
theorem encodeReady_applyPairObsGo_exact_atom_nil_rest_of_go
    {hyps : Array (Object sig.nBases)} {A P : Object sig.nBases}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (n : NegNeu (Ctx.ofHyps hyps) P)
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hne : P ≠ (.never : Object sig.nBases))
    (hnotSum : ∀ L R, P ≠ .coprod L R)
    (hok : applyPairObsGo (fuel + 2) σ hyps [.exact P n] cont = .ok t')
    (hws : ∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hbody : EncodeReady
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
      (OriginEnv.ofHyps (hyps.push P)) 0 0 (atomPushCont n cont)) :
    PhaseEncodeReady t' := by
  rw [applyPairObsGo.eq_def] at hok
  dsimp only at hok
  exact encodeReady_applyObsNeu_atom_nil_rest_of_go fuel σ n cont hne hnotSum hok
    hws hfr hbody

/--
Atom nil-rest readiness deriving push-body EncodeReady from derived
continuation shapes (foc-done / sat-of-foc-pos), not an external `atomPushCont` hypothesis. Observation type is a
base (exact-schedule atom).
-/
theorem encodeReady_applyObsNeu_atom_nil_rest_of_focDone
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {b : Fin sig.nBases}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyObsNeu (fuel + 1) σ hyps (.base b) nP [] cont = .ok t')
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hshape : AtomDerivedContShape cont) :
    PhaseEncodeReady t' := by
  have hbody := encodeReady_atomPushCont_of_focDone nP cont hws hfr hshape
  exact encodeReady_applyObsNeu_atom_nil_rest_of_go fuel σ nP cont
    (by simp) (fun L R h => nomatch h) hok hws hfr hbody

theorem encodeReady_applyPairObsGo_exact_atom_nil_rest_of_focDone
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {b : Fin sig.nBases}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (n : NegNeu (Ctx.ofHyps hyps) (.base b))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyPairObsGo (fuel + 2) σ hyps [.exact (.base b) n] cont = .ok t')
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hshape : AtomDerivedContShape cont) :
    PhaseEncodeReady t' := by
  rw [applyPairObsGo.eq_def] at hok
  dsimp only at hok
  exact encodeReady_applyObsNeu_atom_nil_rest_of_focDone fuel σ n cont hok
    hws hfr hshape

/-- Left branch continuation after coprod observation (empty remainder). -/
def coprodPushContL {hyps : Array (Object sig.nBases)} {L R A : Object sig.nBases}
    (n : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A) :
    InvTm (Ctx.ofHyps (hyps.push L)) A :=
  let hL := Ctx.ofHyps_push hyps L
  let body : InvTm (Ctx.ofHyps hyps ▻ .coprod L R) A :=
    InvTm.abstr .here (NegNeu.weaken n) (InvTm.weaken cont)
  InvTm.castCtx hL.symm
    (hsubstInv (InvTm.rename Rename.skip1 body) (InvTm.etaInl L R))

/-- Right branch continuation after coprod observation (empty remainder). -/
def coprodPushContR {hyps : Array (Object sig.nBases)} {L R A : Object sig.nBases}
    (n : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A) :
    InvTm (Ctx.ofHyps (hyps.push R)) A :=
  let hR := Ctx.ofHyps_push hyps R
  let body : InvTm (Ctx.ofHyps hyps ▻ .coprod L R) A :=
    InvTm.abstr .here (NegNeu.weaken n) (InvTm.weaken cont)
  InvTm.castCtx hR.symm
    (hsubstInv (InvTm.rename Rename.skip1 body) (InvTm.etaInr L R))

theorem coprodPushContL_unit {hyps : Array (Object sig.nBases)}
    {L R : Object sig.nBases}
    (n : NegNeu (Ctx.ofHyps hyps) (.coprod L R)) :
    coprodPushContL n (.unit : InvTm (Ctx.ofHyps hyps) .unit) =
      (.unit : InvTm (Ctx.ofHyps (hyps.push L)) .unit) := by
  simp only [coprodPushContL, InvTm.weaken_unit, InvTm.abstr_unit]
  -- rename skip1 unit = unit; hsubstInv unit = unit; castCtx unit = unit
  change InvTm.castCtx _ (hsubstInv (InvTm.rename _ .unit) _) = _
  simp only [InvTm.rename, hsubstInv, InvTm.castCtx_unit]

theorem coprodPushContR_unit {hyps : Array (Object sig.nBases)}
    {L R : Object sig.nBases}
    (n : NegNeu (Ctx.ofHyps hyps) (.coprod L R)) :
    coprodPushContR n (.unit : InvTm (Ctx.ofHyps hyps) .unit) =
      (.unit : InvTm (Ctx.ofHyps (hyps.push R)) .unit) := by
  simp only [coprodPushContR, InvTm.weaken_unit, InvTm.abstr_unit]
  change InvTm.castCtx _ (hsubstInv (InvTm.rename _ .unit) _) = _
  simp only [InvTm.rename, hsubstInv, InvTm.castCtx_unit]

/-! ### Derived coprod branch shapes (non-unit beyond unit η) -/

/--
Branch bodies under `ofHyps.push` from which left-coprod `EncodeReady` follows
after cast onto `Γ ▻ Side` (parallel to `AtomDerivedContShape`).
-/
def CoprodDerivedBranchShape {hyps : Array (Object sig.nBases)}
    {Side A : Object sig.nBases}
    (body : InvTm (Ctx.ofHyps (hyps.push Side)) A) : Prop :=
  (∃ hA : A = (.unit : Object sig.nBases),
      HEq body (.unit : InvTm (Ctx.ofHyps (hyps.push Side)) .unit)) ∨
  (∃ p : PosNeu (Ctx.ofHyps (hyps.push Side)) A,
      body = .foc (.pos (.done p)) ∧
      forcedRule ([] : List (PosEntry sig)) A = .focus) ∨
  (∃ n : NegNeu (Ctx.ofHyps (hyps.push Side)) A,
      body = .foc (.neg (.done n)) ∧
      forcedRule ([] : List (PosEntry sig)) A = .focus) ∨
  (∃ (s : Schedule sig.nBases) (p : PosNeu (Ctx.ofHyps (hyps.push Side)) A),
      body = .foc (.sat (.mk s (.foc (.pos (.done p))))) ∧
      forcedRule ([] : List (PosEntry sig)) A = .focus)

/-- Cast branch body ready under encode's left-coprod schedule from shape. -/
theorem encodeReady_coprodBranch_cast_of_shape
    (hyps : Array (Object sig.nBases)) {Side A : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (body : InvTm (Ctx.ofHyps (hyps.push Side)) A)
    (hbr : worklistBasesOnly (leftCoprodBranchWs ws e side Side))
    (hshape : CoprodDerivedBranchShape body) :
    EncodeReady (leftCoprodBranchWs ws e side Side)
      (OriginEnv.weaken (A := Side) (OriginEnv.ofHyps hyps) (.split e.origin side))
      0 0
      (InvTm.castCtx (Ctx.ofHyps_push hyps Side) body) := by
  match hshape with
  | .inl ⟨hA, hEq⟩ =>
      cases hA
      cases hEq
      exact encodeReady_unit_leftCoprodBranch_cast hyps Side e ws side hbr
  | .inr (.inl ⟨p, hp, hfr⟩) =>
      cases hp
      exact encodeReady_foc_pos_leftCoprodBranch_cast hyps e ws side p hbr hfr
  | .inr (.inr (.inl ⟨n, hn, hfr⟩)) =>
      cases hn
      exact encodeReady_foc_neg_leftCoprodBranch_cast hyps e ws side n hbr hfr
  | .inr (.inr (.inr ⟨s, p, hp, hfr⟩)) =>
      cases hp
      exact encodeReady_foc_sat_focPos_leftCoprodBranch_cast hyps e ws side s p
        hbr hfr

/-! #### Parent cont → `coprodPushCont` branch shapes (base goal) -/

theorem InvTm.abstr_weaken_foc_pos {Γ : Ctx sig} {P A : Object sig.nBases}
    (m : NegNeu Γ P) (p : PosNeu Γ A) :
    InvTm.abstr (.here : Var (Γ ▻ P) P) (NegNeu.weaken (B := P) m)
      (InvTm.weaken (B := P) (.foc (.pos (.done p)))) =
      .foc (.pos (.done (PosNeu.abstr .here (NegNeu.weaken (B := P) m)
        (PosNeu.rename (Rename.weaken (A := P)) p)))) := by
  simp only [InvTm.weaken, InvTm.rename, FocTm.rename, PosIntro.rename,
    InvTm.abstr, FocTm.abstr]

theorem InvTm.abstr_weaken_foc_neg {Γ : Ctx sig} {P A : Object sig.nBases}
    (m : NegNeu Γ P) (n : NegNeu Γ A) :
    InvTm.abstr (.here : Var (Γ ▻ P) P) (NegNeu.weaken (B := P) m)
      (InvTm.weaken (B := P) (.foc (.neg (.done n)))) =
      .foc (.neg (.done (NegNeu.abstr .here (NegNeu.weaken (B := P) m)
        (NegNeu.rename (Rename.weaken (A := P)) n)))) := by
  simp only [InvTm.weaken, InvTm.rename, FocTm.rename, NegElim.rename,
    InvTm.abstr, FocTm.abstr]

theorem InvTm.abstr_weaken_foc_sat {Γ : Ctx sig} {P A : Object sig.nBases}
    (m : NegNeu Γ P) (s : Schedule sig.nBases) (t : InvTm Γ A) :
    InvTm.abstr (.here : Var (Γ ▻ P) P) (NegNeu.weaken (B := P) m)
      (InvTm.weaken (B := P) (.foc (.sat (.mk s t)))) =
      .foc (.sat (.mk s (InvTm.abstr .here (NegNeu.weaken (B := P) m)
        (InvTm.weaken (B := P) t)))) := by
  simp only [InvTm.weaken, InvTm.rename, FocTm.rename, SatTm.rename,
    InvTm.abstr, FocTm.abstr]

theorem InvTm.rename_skip1_foc_pos {Γ : Ctx sig} {A B C : Object sig.nBases}
    (p : PosNeu (Γ ▻ A) C) :
    InvTm.rename (Rename.skip1 (B := B)) (.foc (.pos (.done p))) =
      .foc (.pos (.done (PosNeu.rename (Rename.skip1 (B := B)) p))) := by
  simp only [InvTm.rename, FocTm.rename, PosIntro.rename]

theorem InvTm.rename_skip1_foc_neg {Γ : Ctx sig} {A B C : Object sig.nBases}
    (n : NegNeu (Γ ▻ A) C) :
    InvTm.rename (Rename.skip1 (B := B)) (.foc (.neg (.done n))) =
      .foc (.neg (.done (NegNeu.rename (Rename.skip1 (B := B)) n))) := by
  simp only [InvTm.rename, FocTm.rename, NegElim.rename]

theorem InvTm.rename_skip1_foc_sat {Γ : Ctx sig} {A B C : Object sig.nBases}
    (s : Schedule sig.nBases) (t : InvTm (Γ ▻ A) C) :
    InvTm.rename (Rename.skip1 (B := B)) (.foc (.sat (.mk s t))) =
      .foc (.sat (.mk s (InvTm.rename (Rename.skip1 (B := B)) t))) := by
  simp only [InvTm.rename, FocTm.rename, SatTm.rename]

theorem hsubstInv_foc_pos_eq_hsubstPos {Γ : Ctx sig} {Cut A : Object sig.nBases}
    (p : PosNeu (Γ ▻ Cut) A) (v : InvTm Γ Cut) :
    hsubstInv (.foc (.pos (.done p))) v = hsubstPos p v := by
  simp only [hsubstInv]

/-- Coproduct cut: `hsubstNeu` never returns `.val`; non-coprod results are `.neu`. -/
theorem hsubstNeu_coprod_of_ne {Γ : Ctx sig} {L R C : Object sig.nBases}
    (n : NegNeu (Γ ▻ .coprod L R) C) (v : InvTm Γ (.coprod L R))
    (hne : (.coprod L R : Object sig.nBases) ≠ C) :
    ∃ n' : NegNeu Γ C, hsubstNeu n v = .neu n' := by
  match n with
  | .var .here => exact absurd rfl hne
  | .var (.there x) =>
      refine ⟨.var x, ?_⟩; simp only [hsubstNeu]
  | .app (A := A) (B := B) m u =>
      have hne' : (.coprod L R : Object sig.nBases) ≠ .exp A B := by
        intro h; cases h
      obtain ⟨m', hm'⟩ := hsubstNeu_coprod_of_ne m v hne'
      refine ⟨.app m' (hsubstInv u v), ?_⟩
      simp only [hsubstNeu, hm']
  | .fst (A := A) (B := B) m =>
      have hne' : (.coprod L R : Object sig.nBases) ≠ .prod A B := by
        intro h; cases h
      obtain ⟨m', hm'⟩ := hsubstNeu_coprod_of_ne m v hne'
      refine ⟨.fst m', ?_⟩; simp only [hsubstNeu, hm']
  | .snd (A := A) (B := B) m =>
      have hne' : (.coprod L R : Object sig.nBases) ≠ .prod A B := by
        intro h; cases h
      obtain ⟨m', hm'⟩ := hsubstNeu_coprod_of_ne m v hne'
      refine ⟨.snd m', ?_⟩; simp only [hsubstNeu, hm']
termination_by n.size

theorem hsubstPos_neu_etaInl_base {Γ : Ctx sig} {L R : Object sig.nBases}
    {b : Fin sig.nBases}
    (n : NegNeu (Γ ▻ L ▻ .coprod L R) (.base b)) :
    ∃ p' : PosNeu (Γ ▻ L) (.base b),
      hsubstPos (.neu n) (InvTm.etaInl L R) = .foc (.pos (.done p')) := by
  have hne : (.coprod L R : Object sig.nBases) ≠ .base b := by intro h; cases h
  obtain ⟨n', hn'⟩ := hsubstNeu_coprod_of_ne n (InvTm.etaInl L R) hne
  refine ⟨.neu n', ?_⟩
  simp only [hsubstPos, hn', NegNeu.eta]

theorem hsubstPos_neu_etaInr_base {Γ : Ctx sig} {L R : Object sig.nBases}
    {b : Fin sig.nBases}
    (n : NegNeu (Γ ▻ R ▻ .coprod L R) (.base b)) :
    ∃ p' : PosNeu (Γ ▻ R) (.base b),
      hsubstPos (.neu n) (InvTm.etaInr L R) = .foc (.pos (.done p')) := by
  have hne : (.coprod L R : Object sig.nBases) ≠ .base b := by intro h; cases h
  obtain ⟨n', hn'⟩ := hsubstNeu_coprod_of_ne n (InvTm.etaInr L R) hne
  refine ⟨.neu n', ?_⟩
  simp only [hsubstPos, hn', NegNeu.eta]

/-- Base-goal foc-pos of a neu: left push body is foc-pos. -/
theorem coprodPushContL_foc_pos_neu_base {hyps : Array (Object sig.nBases)}
    {L R : Object sig.nBases} {b : Fin sig.nBases}
    (nSum : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (n : NegNeu (Ctx.ofHyps hyps) (.base b)) :
    ∃ p' : PosNeu (Ctx.ofHyps (hyps.push L)) (.base b),
      coprodPushContL nSum (.foc (.pos (.done (.neu n)))) =
        .foc (.pos (.done p')) := by
  let Γ := Ctx.ofHyps hyps
  let n1 : NegNeu (Γ ▻ L ▻ .coprod L R) (.base b) :=
    NegNeu.rename (Rename.skip1 (B := L))
      (NegNeu.abstr .here (NegNeu.weaken nSum)
        (NegNeu.rename (Rename.weaken (A := .coprod L R)) n))
  obtain ⟨pMid, hpMid⟩ := hsubstPos_neu_etaInl_base n1
  refine ⟨(Ctx.ofHyps_push hyps L).symm ▸ pMid, ?_⟩
  show InvTm.castCtx (Ctx.ofHyps_push hyps L).symm
      (hsubstInv
        (InvTm.rename (Rename.skip1 (B := L))
          (InvTm.abstr .here (NegNeu.weaken nSum)
            (InvTm.weaken (B := .coprod L R)
              (.foc (.pos (.done (.neu n)))))))
        (InvTm.etaInl L R)) =
      .foc (.pos (.done ((Ctx.ofHyps_push hyps L).symm ▸ pMid)))
  rw [InvTm.abstr_weaken_foc_pos (p := .neu n), InvTm.rename_skip1_foc_pos]
  have hpos :
      PosNeu.rename (Rename.skip1 (B := L))
          (PosNeu.abstr .here (NegNeu.weaken nSum)
            (PosNeu.rename (Rename.weaken (A := .coprod L R)) (.neu n))) =
        .neu n1 := by
    dsimp only [n1]
    simp only [PosNeu.rename, PosNeu.abstr]
  rw [hpos, hsubstInv_foc_pos_eq_hsubstPos, hpMid]
  exact InvTm.castCtx_foc_pos (Ctx.ofHyps_push hyps L).symm pMid

theorem coprodPushContR_foc_pos_neu_base {hyps : Array (Object sig.nBases)}
    {L R : Object sig.nBases} {b : Fin sig.nBases}
    (nSum : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (n : NegNeu (Ctx.ofHyps hyps) (.base b)) :
    ∃ p' : PosNeu (Ctx.ofHyps (hyps.push R)) (.base b),
      coprodPushContR nSum (.foc (.pos (.done (.neu n)))) =
        .foc (.pos (.done p')) := by
  let Γ := Ctx.ofHyps hyps
  let n1 : NegNeu (Γ ▻ R ▻ .coprod L R) (.base b) :=
    NegNeu.rename (Rename.skip1 (B := R))
      (NegNeu.abstr .here (NegNeu.weaken nSum)
        (NegNeu.rename (Rename.weaken (A := .coprod L R)) n))
  obtain ⟨pMid, hpMid⟩ := hsubstPos_neu_etaInr_base n1
  refine ⟨(Ctx.ofHyps_push hyps R).symm ▸ pMid, ?_⟩
  show InvTm.castCtx (Ctx.ofHyps_push hyps R).symm
      (hsubstInv
        (InvTm.rename (Rename.skip1 (B := R))
          (InvTm.abstr .here (NegNeu.weaken nSum)
            (InvTm.weaken (B := .coprod L R)
              (.foc (.pos (.done (.neu n)))))))
        (InvTm.etaInr L R)) =
      .foc (.pos (.done ((Ctx.ofHyps_push hyps R).symm ▸ pMid)))
  rw [InvTm.abstr_weaken_foc_pos (p := .neu n), InvTm.rename_skip1_foc_pos]
  have hpos :
      PosNeu.rename (Rename.skip1 (B := R))
          (PosNeu.abstr .here (NegNeu.weaken nSum)
            (PosNeu.rename (Rename.weaken (A := .coprod L R)) (.neu n))) =
        .neu n1 := by
    dsimp only [n1]
    simp only [PosNeu.rename, PosNeu.abstr]
  rw [hpos, hsubstInv_foc_pos_eq_hsubstPos, hpMid]
  exact InvTm.castCtx_foc_pos (Ctx.ofHyps_push hyps R).symm pMid

/-- Base-goal foc-neg: push body is foc-pos (via `NegNeu.eta`). -/
theorem coprodPushContL_foc_neg_base {hyps : Array (Object sig.nBases)}
    {L R : Object sig.nBases} {b : Fin sig.nBases}
    (nSum : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (n : NegNeu (Ctx.ofHyps hyps) (.base b)) :
    ∃ p' : PosNeu (Ctx.ofHyps (hyps.push L)) (.base b),
      coprodPushContL nSum (.foc (.neg (.done n))) =
        .foc (.pos (.done p')) := by
  let Γ := Ctx.ofHyps hyps
  let n1 : NegNeu (Γ ▻ L ▻ .coprod L R) (.base b) :=
    NegNeu.rename (Rename.skip1 (B := L))
      (NegNeu.abstr .here (NegNeu.weaken nSum)
        (NegNeu.rename (Rename.weaken (A := .coprod L R)) n))
  have hne : (.coprod L R : Object sig.nBases) ≠ .base b := by intro h; cases h
  obtain ⟨n', hn'⟩ := hsubstNeu_coprod_of_ne n1 (InvTm.etaInl L R) hne
  refine ⟨(Ctx.ofHyps_push hyps L).symm ▸ (.neu n'), ?_⟩
  show InvTm.castCtx (Ctx.ofHyps_push hyps L).symm
      (hsubstInv
        (InvTm.rename (Rename.skip1 (B := L))
          (InvTm.abstr .here (NegNeu.weaken nSum)
            (InvTm.weaken (B := .coprod L R) (.foc (.neg (.done n))))))
        (InvTm.etaInl L R)) =
      .foc (.pos (.done ((Ctx.ofHyps_push hyps L).symm ▸ (.neu n'))))
  rw [InvTm.abstr_weaken_foc_neg, InvTm.rename_skip1_foc_neg]
  have hneg :
      NegNeu.rename (Rename.skip1 (B := L))
          (NegNeu.abstr .here (NegNeu.weaken nSum)
            (NegNeu.rename (Rename.weaken (A := .coprod L R)) n)) =
        n1 := rfl
  rw [hneg]
  change InvTm.castCtx _ (hsubstInv (.foc (.neg (.done n1))) (InvTm.etaInl L R)) = _
  simp only [hsubstInv, hn', NegNeu.eta]
  exact InvTm.castCtx_foc_pos (Ctx.ofHyps_push hyps L).symm (.neu n')

theorem coprodPushContR_foc_neg_base {hyps : Array (Object sig.nBases)}
    {L R : Object sig.nBases} {b : Fin sig.nBases}
    (nSum : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (n : NegNeu (Ctx.ofHyps hyps) (.base b)) :
    ∃ p' : PosNeu (Ctx.ofHyps (hyps.push R)) (.base b),
      coprodPushContR nSum (.foc (.neg (.done n))) =
        .foc (.pos (.done p')) := by
  let Γ := Ctx.ofHyps hyps
  let n1 : NegNeu (Γ ▻ R ▻ .coprod L R) (.base b) :=
    NegNeu.rename (Rename.skip1 (B := R))
      (NegNeu.abstr .here (NegNeu.weaken nSum)
        (NegNeu.rename (Rename.weaken (A := .coprod L R)) n))
  have hne : (.coprod L R : Object sig.nBases) ≠ .base b := by intro h; cases h
  obtain ⟨n', hn'⟩ := hsubstNeu_coprod_of_ne n1 (InvTm.etaInr L R) hne
  refine ⟨(Ctx.ofHyps_push hyps R).symm ▸ (.neu n'), ?_⟩
  show InvTm.castCtx (Ctx.ofHyps_push hyps R).symm
      (hsubstInv
        (InvTm.rename (Rename.skip1 (B := R))
          (InvTm.abstr .here (NegNeu.weaken nSum)
            (InvTm.weaken (B := .coprod L R) (.foc (.neg (.done n))))))
        (InvTm.etaInr L R)) =
      .foc (.pos (.done ((Ctx.ofHyps_push hyps R).symm ▸ (.neu n'))))
  rw [InvTm.abstr_weaken_foc_neg, InvTm.rename_skip1_foc_neg]
  have hneg :
      NegNeu.rename (Rename.skip1 (B := R))
          (NegNeu.abstr .here (NegNeu.weaken nSum)
            (NegNeu.rename (Rename.weaken (A := .coprod L R)) n)) =
        n1 := rfl
  rw [hneg]
  change InvTm.castCtx _ (hsubstInv (.foc (.neg (.done n1))) (InvTm.etaInr L R)) = _
  simp only [hsubstInv, hn', NegNeu.eta]
  exact InvTm.castCtx_foc_pos (Ctx.ofHyps_push hyps R).symm (.neu n')

/-- `castCtx` cancels after `castCtx.symm`. -/
theorem InvTm.castCtx_cancel_symm {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (h : Γ = Δ) (t : InvTm Δ A) :
    InvTm.castCtx h (InvTm.castCtx h.symm t) = t := by
  cases h
  rfl

/-- Base-goal sat-of-foc-pos-neu: push body is sat-of-foc-pos. -/
theorem coprodPushContL_foc_sat_focPos_neu_base {hyps : Array (Object sig.nBases)}
    {L R : Object sig.nBases} {b : Fin sig.nBases}
    (nSum : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (s : Schedule sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base b)) :
    ∃ p' : PosNeu (Ctx.ofHyps (hyps.push L)) (.base b),
      coprodPushContL nSum
          (.foc (.sat (.mk s (.foc (.pos (.done (.neu n))))))) =
        .foc (.sat (.mk s (.foc (.pos (.done p'))))) := by
  obtain ⟨p', hp'⟩ := coprodPushContL_foc_pos_neu_base nSum n
  refine ⟨p', ?_⟩
  show InvTm.castCtx (Ctx.ofHyps_push hyps L).symm
      (hsubstInv
        (InvTm.rename (Rename.skip1 (B := L))
          (InvTm.abstr .here (NegNeu.weaken nSum)
            (InvTm.weaken (B := .coprod L R)
              (.foc (.sat (.mk s (.foc (.pos (.done (.neu n))))))))))
        (InvTm.etaInl L R)) =
      .foc (.sat (.mk s (.foc (.pos (.done p')))))
  rw [InvTm.abstr_weaken_foc_sat, InvTm.rename_skip1_foc_sat]
  change InvTm.castCtx (Ctx.ofHyps_push hyps L).symm
      (hsubstInv
        (.foc (.sat (.mk s
          (InvTm.rename (Rename.skip1 (B := L))
            (InvTm.abstr .here (NegNeu.weaken nSum)
              (InvTm.weaken (B := .coprod L R)
                (.foc (.pos (.done (.neu n))))))))))
        (InvTm.etaInl L R)) = _
  simp only [hsubstInv]
  have hp'' :
      hsubstInv
          (InvTm.rename (Rename.skip1 (B := L))
            (InvTm.abstr .here (NegNeu.weaken nSum)
              (InvTm.weaken (B := .coprod L R)
                (.foc (.pos (.done (.neu n)))))))
          (InvTm.etaInl L R) =
        InvTm.castCtx (Ctx.ofHyps_push hyps L) (.foc (.pos (.done p'))) := by
    have hpush :
        InvTm.castCtx (Ctx.ofHyps_push hyps L)
            (coprodPushContL nSum (.foc (.pos (.done (.neu n))))) =
          hsubstInv
            (InvTm.rename (Rename.skip1 (B := L))
              (InvTm.abstr .here (NegNeu.weaken nSum)
                (InvTm.weaken (B := .coprod L R)
                  (.foc (.pos (.done (.neu n)))))))
            (InvTm.etaInl L R) := by
      simp only [coprodPushContL, InvTm.castCtx_cancel_symm]
    rw [← hpush, hp']
  rw [hp'', InvTm.castCtx_foc_sat]
  simp only [InvTm.castCtx_cancel_symm]

theorem coprodPushContR_foc_sat_focPos_neu_base {hyps : Array (Object sig.nBases)}
    {L R : Object sig.nBases} {b : Fin sig.nBases}
    (nSum : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (s : Schedule sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base b)) :
    ∃ p' : PosNeu (Ctx.ofHyps (hyps.push R)) (.base b),
      coprodPushContR nSum
          (.foc (.sat (.mk s (.foc (.pos (.done (.neu n))))))) =
        .foc (.sat (.mk s (.foc (.pos (.done p'))))) := by
  obtain ⟨p', hp'⟩ := coprodPushContR_foc_pos_neu_base nSum n
  refine ⟨p', ?_⟩
  show InvTm.castCtx (Ctx.ofHyps_push hyps R).symm
      (hsubstInv
        (InvTm.rename (Rename.skip1 (B := R))
          (InvTm.abstr .here (NegNeu.weaken nSum)
            (InvTm.weaken (B := .coprod L R)
              (.foc (.sat (.mk s (.foc (.pos (.done (.neu n))))))))))
        (InvTm.etaInr L R)) =
      .foc (.sat (.mk s (.foc (.pos (.done p')))))
  rw [InvTm.abstr_weaken_foc_sat, InvTm.rename_skip1_foc_sat]
  change InvTm.castCtx (Ctx.ofHyps_push hyps R).symm
      (hsubstInv
        (.foc (.sat (.mk s
          (InvTm.rename (Rename.skip1 (B := R))
            (InvTm.abstr .here (NegNeu.weaken nSum)
              (InvTm.weaken (B := .coprod L R)
                (.foc (.pos (.done (.neu n))))))))))
        (InvTm.etaInr L R)) = _
  simp only [hsubstInv]
  have hp'' :
      hsubstInv
          (InvTm.rename (Rename.skip1 (B := R))
            (InvTm.abstr .here (NegNeu.weaken nSum)
              (InvTm.weaken (B := .coprod L R)
                (.foc (.pos (.done (.neu n)))))))
          (InvTm.etaInr L R) =
        InvTm.castCtx (Ctx.ofHyps_push hyps R) (.foc (.pos (.done p'))) := by
    have hpush :
        InvTm.castCtx (Ctx.ofHyps_push hyps R)
            (coprodPushContR nSum (.foc (.pos (.done (.neu n))))) =
          hsubstInv
            (InvTm.rename (Rename.skip1 (B := R))
              (InvTm.abstr .here (NegNeu.weaken nSum)
                (InvTm.weaken (B := .coprod L R)
                  (.foc (.pos (.done (.neu n)))))))
            (InvTm.etaInr L R) := by
      simp only [coprodPushContR, InvTm.castCtx_cancel_symm]
    rw [← hpush, hp']
  rw [hp'', InvTm.castCtx_foc_sat]
  simp only [InvTm.castCtx_cancel_symm]

/--
Parent continuation shapes that determine both `coprodPushContL/R` branch
bodies without an external branch-shape hyp: unit, or base-goal foc-done /
sat-of-foc-pos-neu (parallel to `AtomDerivedContShape`; neu foc-pos for the
coprod η/`hsubstInv` path).
-/
def CoprodDerivedContShape {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (cont : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  (∃ hA : A = (.unit : Object sig.nBases),
      HEq cont (.unit : InvTm (Ctx.ofHyps hyps) .unit)) ∨
  (∃ (b : Fin sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base b))
      (hA : A = .base b),
      cont = hA ▸ (.foc (.pos (.done (.neu n))) :
        InvTm (Ctx.ofHyps hyps) (.base b)) ∧
      forcedRule ([] : List (PosEntry sig)) (.base b) = .focus) ∨
  (∃ (b : Fin sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base b))
      (hA : A = .base b),
      cont = hA ▸ (.foc (.neg (.done n)) :
        InvTm (Ctx.ofHyps hyps) (.base b)) ∧
      forcedRule ([] : List (PosEntry sig)) (.base b) = .focus) ∨
  (∃ (b : Fin sig.nBases) (s : Schedule sig.nBases)
      (n : NegNeu (Ctx.ofHyps hyps) (.base b)) (hA : A = .base b),
      cont = hA ▸ (.foc (.sat (.mk s (.foc (.pos (.done (.neu n)))))) :
        InvTm (Ctx.ofHyps hyps) (.base b)) ∧
      forcedRule ([] : List (PosEntry sig)) (.base b) = .focus)

theorem CoprodDerivedBranchShape_coprodPushContL_unit
    {hyps : Array (Object sig.nBases)} {L R : Object sig.nBases}
    (n : NegNeu (Ctx.ofHyps hyps) (.coprod L R)) :
    CoprodDerivedBranchShape
      (coprodPushContL n (.unit : InvTm (Ctx.ofHyps hyps) .unit)) := by
  refine .inl ⟨rfl, ?_⟩
  rw [coprodPushContL_unit]

theorem CoprodDerivedBranchShape_coprodPushContR_unit
    {hyps : Array (Object sig.nBases)} {L R : Object sig.nBases}
    (n : NegNeu (Ctx.ofHyps hyps) (.coprod L R)) :
    CoprodDerivedBranchShape
      (coprodPushContR n (.unit : InvTm (Ctx.ofHyps hyps) .unit)) := by
  refine .inl ⟨rfl, ?_⟩
  rw [coprodPushContR_unit]

theorem CoprodDerivedBranchShape_of_coprodPushContL
    {hyps : Array (Object sig.nBases)} {L R A : Object sig.nBases}
    (nSum : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    (hshape : CoprodDerivedContShape cont) :
    CoprodDerivedBranchShape (coprodPushContL nSum cont) := by
  match hshape with
  | .inl ⟨hA, hEq⟩ =>
      cases hA; cases hEq
      exact CoprodDerivedBranchShape_coprodPushContL_unit nSum
  | .inr (.inl ⟨b, n, hA, hc, hfr⟩) =>
      cases hA; cases hc
      obtain ⟨p', hp'⟩ := coprodPushContL_foc_pos_neu_base nSum n
      exact .inr (.inl ⟨p', hp', hfr⟩)
  | .inr (.inr (.inl ⟨b, n, hA, hc, hfr⟩)) =>
      cases hA; cases hc
      obtain ⟨p', hp'⟩ := coprodPushContL_foc_neg_base nSum n
      exact .inr (.inl ⟨p', hp', hfr⟩)
  | .inr (.inr (.inr ⟨b, s, n, hA, hc, hfr⟩)) =>
      cases hA; cases hc
      obtain ⟨p', hp'⟩ := coprodPushContL_foc_sat_focPos_neu_base nSum s n
      exact .inr (.inr (.inr ⟨s, p', hp', hfr⟩))

theorem CoprodDerivedBranchShape_of_coprodPushContR
    {hyps : Array (Object sig.nBases)} {L R A : Object sig.nBases}
    (nSum : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    (hshape : CoprodDerivedContShape cont) :
    CoprodDerivedBranchShape (coprodPushContR nSum cont) := by
  match hshape with
  | .inl ⟨hA, hEq⟩ =>
      cases hA; cases hEq
      exact CoprodDerivedBranchShape_coprodPushContR_unit nSum
  | .inr (.inl ⟨b, n, hA, hc, hfr⟩) =>
      cases hA; cases hc
      obtain ⟨p', hp'⟩ := coprodPushContR_foc_pos_neu_base nSum n
      exact .inr (.inl ⟨p', hp', hfr⟩)
  | .inr (.inr (.inl ⟨b, n, hA, hc, hfr⟩)) =>
      cases hA; cases hc
      obtain ⟨p', hp'⟩ := coprodPushContR_foc_neg_base nSum n
      exact .inr (.inl ⟨p', hp', hfr⟩)
  | .inr (.inr (.inr ⟨b, s, n, hA, hc, hfr⟩)) =>
      cases hA; cases hc
      obtain ⟨p', hp'⟩ := coprodPushContR_foc_sat_focPos_neu_base nSum s n
      exact .inr (.inr (.inr ⟨s, p', hp', hfr⟩))

/--
Coprod `applyObsNeu` with empty remainder: recover outer `.case` and both
push bodies (`coprodPushContL/R`). Success requires `fuel ≥ 1`.
-/
theorem applyObsNeu_coprod_nil_rest_ok_inv {hyps : Array (Object sig.nBases)}
    {A L R : Object sig.nBases} (fuel : Nat) (σ : ReachState sig.nBases)
    (n : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyObsNeu (fuel + 1) σ hyps (.coprod L R) n [] cont = .ok t') :
    t' = .case n
      (InvTm.castCtx (Ctx.ofHyps_push hyps L) (coprodPushContL n cont))
      (InvTm.castCtx (Ctx.ofHyps_push hyps R) (coprodPushContR n cont)) ∧
    applyPairObsGo fuel σ (hyps.push L) [] (coprodPushContL n cont) =
      .ok (coprodPushContL n cont) ∧
    applyPairObsGo fuel σ (hyps.push R) [] (coprodPushContR n cont) =
      .ok (coprodPushContR n cont) := by
  cases fuel with
  | zero =>
      rw [applyObsNeu] at hok
      dsimp only at hok
      split at hok
      · next hNever => exact nomatch hNever
      · simp only [applyPairObsGo] at hok
        exact nomatch hok
  | succ fuel =>
      rw [applyObsNeu] at hok
      dsimp only at hok
      split at hok
      · next hNever => exact nomatch hNever
      · simp only [List.map_nil, applyPairObsGo] at hok
        cases hok
        exact ⟨rfl, by simp [applyPairObsGo, coprodPushContL],
          by simp [applyPairObsGo, coprodPushContR]⟩

/-- Exact coprod, empty remainder: recover `.case` and both push bodies. -/
theorem applyPairObsGo_exact_coprod_nil_rest_ok_inv
    {hyps : Array (Object sig.nBases)} {A L R : Object sig.nBases}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (n : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyPairObsGo (fuel + 2) σ hyps [.exact (.coprod L R) n] cont = .ok t') :
    t' = .case n
      (InvTm.castCtx (Ctx.ofHyps_push hyps L) (coprodPushContL n cont))
      (InvTm.castCtx (Ctx.ofHyps_push hyps R) (coprodPushContR n cont)) ∧
    applyPairObsGo fuel σ (hyps.push L) [] (coprodPushContL n cont) =
      .ok (coprodPushContL n cont) ∧
    applyPairObsGo fuel σ (hyps.push R) [] (coprodPushContR n cont) =
      .ok (coprodPushContR n cont) := by
  rw [applyPairObsGo.eq_def] at hok
  dsimp only at hok
  exact applyObsNeu_coprod_nil_rest_ok_inv fuel σ n cont hok

/-- Exact atom, empty remainder: recover `letPos` / `atomPushCont` (Go form). -/
theorem applyPairObsGo_exact_atom_nil_rest_ok_inv
    {hyps : Array (Object sig.nBases)} {A P : Object sig.nBases}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (n : NegNeu (Ctx.ofHyps hyps) P)
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hne : P ≠ (.never : Object sig.nBases))
    (hnotSum : ∀ L R, P ≠ .coprod L R)
    (hok : applyPairObsGo (fuel + 2) σ hyps [.exact P n] cont = .ok t') :
    t' = .foc (.letPos n
      (InvTm.castCtx (Ctx.ofHyps_push hyps P) (atomPushCont n cont))) ∧
    applyPairObsGo fuel σ (hyps.push P) [] (atomPushCont n cont) =
      .ok (atomPushCont n cont) := by
  rw [applyPairObsGo.eq_def] at hok
  dsimp only at hok
  exact applyObsNeu_atom_nil_rest_ok_inv fuel σ n cont hne hnotSum hok

/-! ### Coprod `applyObsNeu` → outer `case` (var scrutinee) -/

/--
Outer `.case (.var x) …` is encode-ready under a forced left-coprod whose
origin hits `x`, given ready branches under the split/`pushPos` contexts.
-/
theorem encodeReady_case_var_leftCoprod
    {Γ : Ctx sig} {A L R : Object sig.nBases}
    {e : PosEntry sig} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {domNest obsSlot : Nat}
    (x : Var Γ (.coprod L R))
    (tL : InvTm (Γ ▻ L) A) (tR : InvTm (Γ ▻ R) A)
    (hfr : forcedRule (e :: ws) A = .leftCoprod e L R)
    (hit : ε x = e.origin)
    (hL : EncodeReady
      (pushPos ws (.split e.origin false) L)
      (OriginEnv.weaken (A := L) ε (.split e.origin false))
      domNest obsSlot tL)
    (hR : EncodeReady
      (pushPos ws (.split e.origin true) R)
      (OriginEnv.weaken (A := R) ε (.split e.origin true))
      domNest obsSlot tR) :
    EncodeReady (e :: ws) ε domNest obsSlot (.case (.var x) tL tR) :=
  .leftCoprod_peel hfr (peelCaseOuter_case_var_hit ε e.origin x tL tR hit) hL hR

/-- Same with a `moveStable` base prefix in front of the left-coprod head. -/
theorem encodeReady_case_var_leftCoprod_of_base_prefix
    {Γ : Ctx sig} {A L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    {ε : OriginEnv Γ} {domNest obsSlot : Nat}
    (x : Var Γ (.coprod L R))
    (tL : InvTm (Γ ▻ L) A) (tR : InvTm (Γ ▻ R) A)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hfr : forcedRule (e :: ws) A = .leftCoprod e L R)
    (hit : ε x = e.origin)
    (hL : EncodeReady
      (pushPos ws (.split e.origin false) L)
      (OriginEnv.weaken (A := L) ε (.split e.origin false))
      domNest obsSlot tL)
    (hR : EncodeReady
      (pushPos ws (.split e.origin true) R)
      (OriginEnv.weaken (A := R) ε (.split e.origin true))
      domNest obsSlot tR) :
    EncodeReady (pref ++ e :: ws) ε domNest obsSlot (.case (.var x) tL tR) := by
  induction pref with
  | nil =>
      exact encodeReady_case_var_leftCoprod x tL tR hfr hit hL hR
  | cons e' pref ih =>
      have ⟨b, hb⟩ := hpref e' (List.Mem.head _)
      exact .moveStable (forcedRule_cons_base_moveStable e' _ hb A)
        (ih fun e'' he'' => hpref e'' (List.Mem.tail _ he''))

/--
Phase packaging for `applyObsNeu` on a coprod whose scrutinee is a hyp var
matching the forced left-coprod origin (exact / consistency witness shape).
Branch readiness is under split/`pushPos` (encode schedule), not `ofHyps.push`.
-/
theorem encodeReady_applyObsNeu_coprod_var
    {hyps : Array (Object sig.nBases)} {A L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    (x : Var (Ctx.ofHyps hyps) (.coprod L R))
    (tL : InvTm (Ctx.ofHyps hyps ▻ L) A)
    (tR : InvTm (Ctx.ofHyps hyps ▻ R) A)
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hfr : forcedRule (e :: ws) A = .leftCoprod e L R)
    (hit : OriginEnv.ofHyps hyps x = e.origin)
    (hL : EncodeReady
      (pushPos ws (.split e.origin false) L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin false))
      0 0 tL)
    (hR : EncodeReady
      (pushPos ws (.split e.origin true) R)
      (OriginEnv.weaken (A := R) (OriginEnv.ofHyps hyps) (.split e.origin true))
      0 0 tR) :
    PhaseEncodeReady
      (.case (.var x) tL tR : InvTm (Ctx.ofHyps hyps) A) := by
  simpa [PhaseEncodeReady, hws] using
    encodeReady_case_var_leftCoprod_of_base_prefix x tL tR hpref hfr hit hL hR

/-- Nested-coprod peel packaging: outer `.case (.var .here) …` after bases prefix. -/
theorem encodeReady_case_here_leftCoprodBranch_nested
    (hyps : Array (Object sig.nBases)) {A : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (side : Bool)
    (L R : Object sig.nBases)
    (tL : InvTm (Ctx.ofHyps hyps ▻ .coprod L R ▻ L) A)
    (tR : InvTm (Ctx.ofHyps hyps ▻ .coprod L R ▻ R) A)
    (hhyp : ∀ e' ∈ ws, ∃ i, e'.origin = .hyp (sig := sig) i)
    (hbase : worklistBasesOnly ws)
    (hL : EncodeReady
      (pushPos ([] : List (PosEntry sig)) (.split (.split e.origin side) false) L)
      (OriginEnv.weaken (A := L)
        (OriginEnv.weaken (A := .coprod L R) (OriginEnv.ofHyps hyps)
          (.split e.origin side))
        (.split (.split e.origin side) false))
      0 0 tL)
    (hR : EncodeReady
      (pushPos ([] : List (PosEntry sig)) (.split (.split e.origin side) true) R)
      (OriginEnv.weaken (A := R)
        (OriginEnv.weaken (A := .coprod L R) (OriginEnv.ofHyps hyps)
          (.split e.origin side))
        (.split (.split e.origin side) true))
      0 0 tR) :
    EncodeReady (leftCoprodBranchWs ws e side (.coprod L R))
      (OriginEnv.weaken (A := .coprod L R) (OriginEnv.ofHyps hyps)
        (.split e.origin side))
      0 0
      (.case (.var .here) tL tR) := by
  let eIns : PosEntry sig :=
    { origin := .split e.origin side, ty := .coprod L R }
  have hwsEq :
      leftCoprodBranchWs ws e side (.coprod L R) =
        ws.mergeSort (fun a b => Origin.ble a.origin b.origin) ++ [eIns] :=
    leftCoprodBranchWs_coprod_eq_append_of_hyps ws e side L R hhyp
  have hpref :
      worklistBasesOnly
        (ws.mergeSort fun a b => Origin.ble a.origin b.origin) :=
    fun e' he' => hbase e' (List.mem_mergeSort.mp he')
  have hfr :
      forcedRule (eIns :: ([] : List (PosEntry sig))) A = .leftCoprod eIns L R :=
    forcedRule_cons_coprod eIns [] rfl _
  have hit :
      OriginEnv.weaken (A := .coprod L R) (OriginEnv.ofHyps hyps)
          (.split e.origin side) (.here) = eIns.origin := by
    simp [OriginEnv.weaken, OriginEnv.snoc, eIns]
  rw [hwsEq]
  exact encodeReady_case_var_leftCoprod_of_base_prefix (x := .here) tL tR
    (fun e' he' => hpref e' he') hfr hit hL hR

/--
Cast form used by `applyObsNeu` on `.coprod`: recursive bodies live under
`ofHyps (hyps.push _)` and are cast onto `Γ ▻ L/R` before the outer case.
-/
theorem encodeReady_applyObsNeu_coprod_var_cast
    {hyps : Array (Object sig.nBases)} {A L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    (x : Var (Ctx.ofHyps hyps) (.coprod L R))
    (bodyL : InvTm (Ctx.ofHyps (hyps.push L)) A)
    (bodyR : InvTm (Ctx.ofHyps (hyps.push R)) A)
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hfr : forcedRule (e :: ws) A = .leftCoprod e L R)
    (hit : OriginEnv.ofHyps hyps x = e.origin)
    (hL : EncodeReady
      (pushPos ws (.split e.origin false) L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin false))
      0 0 (InvTm.castCtx (Ctx.ofHyps_push hyps L) bodyL))
    (hR : EncodeReady
      (pushPos ws (.split e.origin true) R)
      (OriginEnv.weaken (A := R) (OriginEnv.ofHyps hyps) (.split e.origin true))
      0 0 (InvTm.castCtx (Ctx.ofHyps_push hyps R) bodyR)) :
    PhaseEncodeReady
      (.case (.var x)
        (InvTm.castCtx (Ctx.ofHyps_push hyps L) bodyL)
        (InvTm.castCtx (Ctx.ofHyps_push hyps R) bodyR) :
        InvTm (Ctx.ofHyps hyps) A) :=
  encodeReady_applyObsNeu_coprod_var x _ _ hws hpref hfr hit hL hR

/--
`applyObsNeu` coprod packaging when both recursive bodies are `.unit` and both
branch schedules are base-only (encode schedule, not ofHyps).
-/
theorem encodeReady_applyObsNeu_coprod_var_cast_unit
    {hyps : Array (Object sig.nBases)} {L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    (x : Var (Ctx.ofHyps hyps) (.coprod L R))
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hfr : forcedRule (e :: ws) (.unit : Object sig.nBases) = .leftCoprod e L R)
    (hit : OriginEnv.ofHyps hyps x = e.origin)
    (hL : worklistBasesOnly (leftCoprodBranchWs ws e false L))
    (hR : worklistBasesOnly (leftCoprodBranchWs ws e true R)) :
    PhaseEncodeReady
      (.case (.var x)
        (InvTm.castCtx (Ctx.ofHyps_push hyps L)
          (.unit : InvTm (Ctx.ofHyps (hyps.push L)) .unit))
        (InvTm.castCtx (Ctx.ofHyps_push hyps R)
          (.unit : InvTm (Ctx.ofHyps (hyps.push R)) .unit)) :
        InvTm (Ctx.ofHyps hyps) .unit) :=
  encodeReady_applyObsNeu_coprod_var_cast x _ _
    hws hpref hfr hit
    (by
      simpa [leftCoprodBranchWs] using
        encodeReady_unit_leftCoprodBranch_cast hyps L e ws false hL)
    (by
      simpa [leftCoprodBranchWs] using
        encodeReady_unit_leftCoprodBranch_cast hyps R e ws true hR)

/--
Coprod-var nil-rest readiness from Go success **without** a prior shape
hypothesis: inversion supplies `.case` / `coprodPushContL/R`, then cast
packaging under left-coprod schedule facts.
-/
theorem encodeReady_applyObsNeu_coprod_var_nil_rest_of_go
    {hyps : Array (Object sig.nBases)} {A L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (x : Var (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyObsNeu (fuel + 1) σ hyps (.coprod L R) (.var x) [] cont = .ok t')
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hfr : forcedRule (e :: ws) A = .leftCoprod e L R)
    (hit : OriginEnv.ofHyps hyps x = e.origin)
    (hL : EncodeReady
      (pushPos ws (.split e.origin false) L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin false))
      0 0 (InvTm.castCtx (Ctx.ofHyps_push hyps L) (coprodPushContL (.var x) cont)))
    (hR : EncodeReady
      (pushPos ws (.split e.origin true) R)
      (OriginEnv.weaken (A := R) (OriginEnv.ofHyps hyps) (.split e.origin true))
      0 0 (InvTm.castCtx (Ctx.ofHyps_push hyps R) (coprodPushContR (.var x) cont))) :
    PhaseEncodeReady t' := by
  obtain ⟨ht, _, _⟩ := applyObsNeu_coprod_nil_rest_ok_inv fuel σ (.var x) cont hok
  cases ht
  exact encodeReady_applyObsNeu_coprod_var_cast x _ _ hws hpref hfr hit hL hR

/-- Exact coprod-var, empty remainder: Go inversion + cast packaging (no shape hyp). -/
theorem encodeReady_applyPairObsGo_exact_coprod_var_nil_rest_of_go
    {hyps : Array (Object sig.nBases)} {A L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (x : Var (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyPairObsGo (fuel + 2) σ hyps
      [.exact (.coprod L R) (.var x)] cont = .ok t')
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hfr : forcedRule (e :: ws) A = .leftCoprod e L R)
    (hit : OriginEnv.ofHyps hyps x = e.origin)
    (hL : EncodeReady
      (pushPos ws (.split e.origin false) L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps) (.split e.origin false))
      0 0 (InvTm.castCtx (Ctx.ofHyps_push hyps L) (coprodPushContL (.var x) cont)))
    (hR : EncodeReady
      (pushPos ws (.split e.origin true) R)
      (OriginEnv.weaken (A := R) (OriginEnv.ofHyps hyps) (.split e.origin true))
      0 0 (InvTm.castCtx (Ctx.ofHyps_push hyps R) (coprodPushContR (.var x) cont))) :
    PhaseEncodeReady t' := by
  rw [applyPairObsGo.eq_def] at hok
  dsimp only at hok
  exact encodeReady_applyObsNeu_coprod_var_nil_rest_of_go fuel σ x cont hok
    hws hpref hfr hit hL hR

/--
Coprod-var nil-rest with unit continuation: branch bodies reduce to `.unit`;
readiness from branch `worklistBasesOnly` (no external push-cont EncodeReady).
-/
theorem encodeReady_applyObsNeu_coprod_var_nil_rest_of_unit
    {hyps : Array (Object sig.nBases)} {L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (x : Var (Ctx.ofHyps hyps) (.coprod L R))
    {t' : InvTm (Ctx.ofHyps hyps) .unit}
    (hok : applyObsNeu (fuel + 1) σ hyps (.coprod L R) (.var x) []
      (.unit : InvTm (Ctx.ofHyps hyps) .unit) = .ok t')
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hfr : forcedRule (e :: ws) (.unit : Object sig.nBases) = .leftCoprod e L R)
    (hit : OriginEnv.ofHyps hyps x = e.origin)
    (hL : worklistBasesOnly (leftCoprodBranchWs ws e false L))
    (hR : worklistBasesOnly (leftCoprodBranchWs ws e true R)) :
    PhaseEncodeReady t' := by
  obtain ⟨ht, _, _⟩ :=
    applyObsNeu_coprod_nil_rest_ok_inv fuel σ (.var x)
      (.unit : InvTm (Ctx.ofHyps hyps) .unit) hok
  cases ht
  simp only [coprodPushContL_unit, coprodPushContR_unit]
  exact encodeReady_applyObsNeu_coprod_var_cast_unit x hws hpref hfr hit hL hR

theorem encodeReady_applyPairObsGo_exact_coprod_var_nil_rest_of_unit
    {hyps : Array (Object sig.nBases)} {L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (x : Var (Ctx.ofHyps hyps) (.coprod L R))
    {t' : InvTm (Ctx.ofHyps hyps) .unit}
    (hok : applyPairObsGo (fuel + 2) σ hyps
      [.exact (.coprod L R) (.var x)]
      (.unit : InvTm (Ctx.ofHyps hyps) .unit) = .ok t')
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hfr : forcedRule (e :: ws) (.unit : Object sig.nBases) = .leftCoprod e L R)
    (hit : OriginEnv.ofHyps hyps x = e.origin)
    (hL : worklistBasesOnly (leftCoprodBranchWs ws e false L))
    (hR : worklistBasesOnly (leftCoprodBranchWs ws e true R)) :
    PhaseEncodeReady t' := by
  rw [applyPairObsGo.eq_def] at hok
  dsimp only at hok
  exact encodeReady_applyObsNeu_coprod_var_nil_rest_of_unit fuel σ x hok
    hws hpref hfr hit hL hR

/--
Coprod-var nil-rest from **derived branch shapes** under `ofHyps.push`
(`CoprodDerivedBranchShape`): unit / foc-done / sat-of-foc-pos after push,
cast onto encode's `leftCoprodBranchWs` — no external branch EncodeReady stash.
-/
theorem encodeReady_applyObsNeu_coprod_var_nil_rest_of_branchShape
    {hyps : Array (Object sig.nBases)} {A L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (x : Var (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyObsNeu (fuel + 1) σ hyps (.coprod L R) (.var x) [] cont = .ok t')
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hfr : forcedRule (e :: ws) A = .leftCoprod e L R)
    (hit : OriginEnv.ofHyps hyps x = e.origin)
    (hL : worklistBasesOnly (leftCoprodBranchWs ws e false L))
    (hR : worklistBasesOnly (leftCoprodBranchWs ws e true R))
    (hshapeL : CoprodDerivedBranchShape (coprodPushContL (.var x) cont))
    (hshapeR : CoprodDerivedBranchShape (coprodPushContR (.var x) cont)) :
    PhaseEncodeReady t' := by
  obtain ⟨ht, _, _⟩ := applyObsNeu_coprod_nil_rest_ok_inv fuel σ (.var x) cont hok
  cases ht
  exact encodeReady_applyObsNeu_coprod_var_cast x _ _ hws hpref hfr hit
    (by
      simpa [leftCoprodBranchWs] using
        encodeReady_coprodBranch_cast_of_shape hyps e ws false
          (coprodPushContL (.var x) cont) hL hshapeL)
    (by
      simpa [leftCoprodBranchWs] using
        encodeReady_coprodBranch_cast_of_shape hyps e ws true
          (coprodPushContR (.var x) cont) hR hshapeR)

theorem encodeReady_applyPairObsGo_exact_coprod_var_nil_rest_of_branchShape
    {hyps : Array (Object sig.nBases)} {A L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (x : Var (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyPairObsGo (fuel + 2) σ hyps
      [.exact (.coprod L R) (.var x)] cont = .ok t')
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hfr : forcedRule (e :: ws) A = .leftCoprod e L R)
    (hit : OriginEnv.ofHyps hyps x = e.origin)
    (hL : worklistBasesOnly (leftCoprodBranchWs ws e false L))
    (hR : worklistBasesOnly (leftCoprodBranchWs ws e true R))
    (hshapeL : CoprodDerivedBranchShape (coprodPushContL (.var x) cont))
    (hshapeR : CoprodDerivedBranchShape (coprodPushContR (.var x) cont)) :
    PhaseEncodeReady t' := by
  rw [applyPairObsGo.eq_def] at hok
  dsimp only at hok
  exact encodeReady_applyObsNeu_coprod_var_nil_rest_of_branchShape fuel σ x cont
    hok hws hpref hfr hit hL hR hshapeL hshapeR

/-- Coprod-var nil-rest from **parent** `CoprodDerivedContShape` (derives branch
shapes via `coprodPushCont`). -/
theorem encodeReady_applyObsNeu_coprod_var_nil_rest_of_contShape
    {hyps : Array (Object sig.nBases)} {A L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (x : Var (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyObsNeu (fuel + 1) σ hyps (.coprod L R) (.var x) [] cont = .ok t')
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hfr : forcedRule (e :: ws) A = .leftCoprod e L R)
    (hit : OriginEnv.ofHyps hyps x = e.origin)
    (hL : worklistBasesOnly (leftCoprodBranchWs ws e false L))
    (hR : worklistBasesOnly (leftCoprodBranchWs ws e true R))
    (hshape : CoprodDerivedContShape cont) :
    PhaseEncodeReady t' :=
  encodeReady_applyObsNeu_coprod_var_nil_rest_of_branchShape fuel σ x cont
    hok hws hpref hfr hit hL hR
    (CoprodDerivedBranchShape_of_coprodPushContL (.var x) cont hshape)
    (CoprodDerivedBranchShape_of_coprodPushContR (.var x) cont hshape)

theorem encodeReady_applyPairObsGo_exact_coprod_var_nil_rest_of_contShape
    {hyps : Array (Object sig.nBases)} {A L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (x : Var (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyPairObsGo (fuel + 2) σ hyps
      [.exact (.coprod L R) (.var x)] cont = .ok t')
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hfr : forcedRule (e :: ws) A = .leftCoprod e L R)
    (hit : OriginEnv.ofHyps hyps x = e.origin)
    (hL : worklistBasesOnly (leftCoprodBranchWs ws e false L))
    (hR : worklistBasesOnly (leftCoprodBranchWs ws e true R))
    (hshape : CoprodDerivedContShape cont) :
    PhaseEncodeReady t' := by
  rw [applyPairObsGo.eq_def] at hok
  dsimp only at hok
  exact encodeReady_applyObsNeu_coprod_var_nil_rest_of_contShape fuel σ x cont
    hok hws hpref hfr hit hL hR hshape

/-- Unit cont is the special case of branch-shape packaging. -/
theorem encodeReady_applyObsNeu_coprod_var_nil_rest_of_unit_via_shape
    {hyps : Array (Object sig.nBases)} {L R : Object sig.nBases}
    {pref : List (PosEntry sig)} {e : PosEntry sig} {ws : List (PosEntry sig)}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (x : Var (Ctx.ofHyps hyps) (.coprod L R))
    {t' : InvTm (Ctx.ofHyps hyps) .unit}
    (hok : applyObsNeu (fuel + 1) σ hyps (.coprod L R) (.var x) []
      (.unit : InvTm (Ctx.ofHyps hyps) .unit) = .ok t')
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws)
    (hpref : ∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b)
    (hfr : forcedRule (e :: ws) (.unit : Object sig.nBases) = .leftCoprod e L R)
    (hit : OriginEnv.ofHyps hyps x = e.origin)
    (hL : worklistBasesOnly (leftCoprodBranchWs ws e false L))
    (hR : worklistBasesOnly (leftCoprodBranchWs ws e true R)) :
    PhaseEncodeReady t' :=
  encodeReady_applyObsNeu_coprod_var_nil_rest_of_branchShape fuel σ x _
    hok hws hpref hfr hit hL hR
    (CoprodDerivedBranchShape_coprodPushContL_unit (.var x))
    (CoprodDerivedBranchShape_coprodPushContR_unit (.var x))

/--
`applyPairObsGo` under the **empty / exact-never-only / single exact atom
nil-rest / single exact coprod-var nil-rest** discipline.
-/
theorem encodeReady_applyPairObsGo_emptyNeverOrNilRestObs
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (entries : List (PairEntry sig hyps))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyPairObsGo (fuel + 1) σ hyps entries cont = .ok t')
    (hdisc :
      (exactNeverEntriesOnly entries ∧
        (entries = [] → PhaseEncodeReady cont) ∧
        (entries ≠ [] →
          ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
            OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
            (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
            e.ty = .never)) ∨
      (∃ (P : Object sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) P),
        entries = [.exact P n] ∧
        P ≠ (.never : Object sig.nBases) ∧
        (∀ L R, P ≠ .coprod L R) ∧
        (∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
          ∃ b : Fin sig.nBases, e.ty = .base b) ∧
        forcedRule ([] : List (PosEntry sig)) A = .focus ∧
        EncodeReady
          (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
          (OriginEnv.ofHyps (hyps.push P)) 0 0 (atomPushCont n cont)) ∨
      (∃ (L R : Object sig.nBases)
          (pref : List (PosEntry sig)) (e : PosEntry sig) (ws : List (PosEntry sig))
          (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
        entries = [.exact (.coprod L R) (.var x)] ∧
        OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
        (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
        forcedRule (e :: ws) A = .leftCoprod e L R ∧
        OriginEnv.ofHyps hyps x = e.origin ∧
        EncodeReady
          (pushPos ws (.split e.origin false) L)
          (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps)
            (.split e.origin false)) 0 0
          (InvTm.castCtx (Ctx.ofHyps_push hyps L)
            (coprodPushContL (.var x) cont)) ∧
        EncodeReady
          (pushPos ws (.split e.origin true) R)
          (OriginEnv.weaken (A := R) (OriginEnv.ofHyps hyps)
            (.split e.origin true)) 0 0
          (InvTm.castCtx (Ctx.ofHyps_push hyps R)
            (coprodPushContR (.var x) cont)))) :
    PhaseEncodeReady t' := by
  cases hdisc with
  | inl h =>
      obtain ⟨hent, hempty, hnever⟩ := h
      exact encodeReady_applyPairObsGo_exactNeverOnly fuel σ entries cont hent hok
        hempty hnever
  | inr h =>
      cases h with
      | inl h =>
          obtain ⟨P, n, heq, hne, hnotSum, hws, hfr, hbody⟩ := h
          cases heq
          cases fuel with
          | zero =>
              simp [applyPairObsGo, applyObsNeu] at hok
          | succ fuel =>
              exact encodeReady_applyPairObsGo_exact_atom_nil_rest_of_go fuel σ n cont
                hne hnotSum hok hws hfr hbody
      | inr h =>
          obtain ⟨L, R, pref, e, ws, x, heq, hws, hpref, hfr, hit, hL, hR⟩ := h
          cases heq
          cases fuel with
          | zero =>
              simp [applyPairObsGo, applyObsNeu] at hok
          | succ fuel =>
              exact encodeReady_applyPairObsGo_exact_coprod_var_nil_rest_of_go
                fuel σ x cont hok hws hpref hfr hit hL hR

/--
Go readiness when atom/coprod push-body facts are **derived** from shapes
rather than assumed: empty ∪ exact-never-only ∪ single exact base atom with
`AtomDerivedContShape` ∪ single exact coprod-var with
`CoprodDerivedContShape` on the parent continuation (unit / base foc-done /
sat-of-foc-pos-neu; branch shapes via `coprodPushCont`).
-/
theorem encodeReady_applyPairObsGo_emptyNeverOrDerivedNilRest
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (fuel : Nat) (σ : ReachState sig.nBases)
    (entries : List (PairEntry sig hyps))
    (cont : InvTm (Ctx.ofHyps hyps) A)
    {t' : InvTm (Ctx.ofHyps hyps) A}
    (hok : applyPairObsGo (fuel + 1) σ hyps entries cont = .ok t')
    (hdisc :
      (exactNeverEntriesOnly entries ∧
        (entries = [] → PhaseEncodeReady cont) ∧
        (entries ≠ [] →
          ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
            OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
            (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
            e.ty = .never)) ∨
      (∃ (b : Fin sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base b)),
        entries = [.exact (.base b) n] ∧
        worklistBasesOnly (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)) ∧
        forcedRule ([] : List (PosEntry sig)) A = .focus ∧
        AtomDerivedContShape cont) ∨
      (∃ (L R : Object sig.nBases)
          (pref : List (PosEntry sig)) (e : PosEntry sig) (ws : List (PosEntry sig))
          (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
        entries = [.exact (.coprod L R) (.var x)] ∧
        OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
        (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
        forcedRule (e :: ws) A = .leftCoprod e L R ∧
        OriginEnv.ofHyps hyps x = e.origin ∧
        worklistBasesOnly (leftCoprodBranchWs ws e false L) ∧
        worklistBasesOnly (leftCoprodBranchWs ws e true R) ∧
        CoprodDerivedContShape cont)) :
    PhaseEncodeReady t' := by
  cases hdisc with
  | inl h =>
      obtain ⟨hent, hempty, hnever⟩ := h
      exact encodeReady_applyPairObsGo_exactNeverOnly fuel σ entries cont hent hok
        hempty hnever
  | inr h =>
      cases h with
      | inl h =>
          obtain ⟨b, n, heq, hws, hfr, hshape⟩ := h
          cases heq
          cases fuel with
          | zero =>
              simp [applyPairObsGo, applyObsNeu] at hok
          | succ fuel =>
              exact encodeReady_applyPairObsGo_exact_atom_nil_rest_of_focDone
                fuel σ n cont hok hws hfr hshape
      | inr h =>
          obtain ⟨L, R, pref, e, ws, x, heq, hws, hpref, hfr, hit, hL, hR,
            hshape⟩ := h
          cases heq
          cases fuel with
          | zero =>
              simp [applyPairObsGo, applyObsNeu] at hok
          | succ fuel =>
              exact encodeReady_applyPairObsGo_exact_coprod_var_nil_rest_of_contShape
                fuel σ x cont hok hws hpref hfr hit hL hR hshape

/-! ### Gaps (RawReferenceProduced → PhaseEncodeReady)

Required: `encodeReady_of_rawReferenceProduced` /
`certifyReferenceProduced : RawReferenceProduced t → CertifiedReferenceProduced t`.
Until then `ValidEncodeFragment.ready` is a provisional stash and
`EncodeTotal_holds_provisional` is not semantic totality.

* ~~`peelCaseOuter_rekeyHypToObs`~~ **Landed**
* ~~`encodeReady_rekeyHypToObs` (full, peel/unit-η)~~ **Landed**;
  `encodeReady_newest_hyp_to_obs` / `encodeReady_ofHyps_push_to_obs` /
  `encodeReady_applyObsNeu_atom_of_push_body_ready` package left-coprod-under-
  outer-`letPos` after peel-ready bodies on `ofHyps.push`.
* ~~`Ctx.ofHyps_push` cast~~ **Landed**
* ~~Coprod observation → outer `case` (var hit) + ready split branches~~
  **Landed** as packaging (`encodeReady_applyObsNeu_coprod_var`); schedule
  algebra closed (`pushPos_cons_of_blt_head`, `leftCoprod_branch_schedule_gap`
  → `e :: leftCoprodBranchWs`). Branch EncodeReady: bases-only shapes +
  never-payload abort (`encodeReady_abort_leftCoprodBranch_never`); nested
  coprod unit-η / peel (`encodeReady_unit_leftCoprodBranch_nested`,
  `encodeReady_case_here_leftCoprodBranch_nested`). Same-term
  `encodeReady_ofHyps_push_to_leftCoprodBranch` blocked.
* Empty / inconsistent / exact-never / exact-never-only / atom+coprod
  nil-rest Go packaging + inversion landed
  (`applyObsNeu_*_nil_rest_ok_inv`, `applyPairObsGo_exact_*_nil_rest_ok_inv`,
  `encodeReady_applyPairObsGo_exact_atom/coprod_var_nil_rest_of_go`,
  `encodeReady_applyPairObsGo_emptyNeverOrNilRestObs`). Push-body /
  branch readiness **derived** for `AtomDerivedContShape` (foc-done /
  sat-of-foc-pos / base-binder letPos around foc-pos; `*_of_focDone`) and
  `CoprodDerivedContShape` on parent conts (unit / base foc-done /
  sat-of-foc-pos-neu → `CoprodDerivedBranchShape` via `coprodPushCont`;
  `*_of_contShape`) via
  `encodeReady_applyPairObsGo_emptyNeverOrDerivedNilRest`. Empty schedule:
  `WellInv` intro/focus shapes under bases-only discharge cont readiness
  (`phaseEncodeReady_of_wellInv_*`,
  `encodeReady_applyPairObs_emptyEntries_of_wellInv_intro`) — no ready stash.
  See `EncodeReadyRawCase`. Coprod: parent `CoprodDerivedContShape` covers
  unit + base foc-done/sat; residual base-letPos parent through push,
  general PosNeu foc-pos, pair/lam / abort-never branches.
* Restricted Raw→ready:
  `EncodeReadyOfRawGoal_emptyOrExactNever_holds`,
  `EncodeReadyOfRawGoal_emptyNeverOrNilRestObs_holds` (assumes push/branch
  ready), `EncodeReadyOfRawGoal_emptyNeverOrDerivedNilRest_holds`, and
  `EncodeReadyOfRawGoal_emptyWellInvIntroOrDerived_holds` (empty + WellInv
  intro shapes, or derived nil-rest). Unrestricted `EncodeReadyOfRawGoal`
  open. Residual: base-binder letPos parent through `coprodPushCont`;
  general PosNeu (non-neu) foc-pos; pair/lam / abort-never branch bodies;
  consistency / mixed multi-entry; general WellInv→ready /
  letPos bodies beyond foc-pos; `encodeReady_ofHyps_push_to_leftCoprodBranch`
  blocked.
* `sat_body`: Go codes landed (`encodeICCGo_sat_body_codes`); `EncodeIccStep`
  packaging blocked (sticky encode would need to drop `.foc (.body _)`).
-/

/--
Named fragment of phase-ready case data toward `EncodeReadyOfRawGoal`: empty
schedule + ready cont, inconsistent never, base-only atom `letPos`,
coprod-var with split-ready branches, or bases-only unit cast branches.
Does **not** alone imply the case data from raw production.
-/
def EncodeReadyRawCase {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  (∃ (fuel : Nat) (σ : ReachState sig.nBases)
      (entries : Array (PairEntry sig hyps))
      (cont : InvTm (Ctx.ofHyps hyps) A),
    PhaseEncodeReady cont ∧
    entries.toList = [] ∧
    σ.inconsistent = false ∧
    (applyPairObs fuel σ hyps entries cont = .ok t)) ∨
  (∃ (fuel : Nat) (σ : ReachState sig.nBases)
      (entries : Array (PairEntry sig hyps))
      (cont : InvTm (Ctx.ofHyps hyps) A)
      (pref : List (PosEntry sig)) (e : PosEntry sig)
      (suf : List (PosEntry sig)),
    σ.inconsistent = true ∧
    OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
    (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
    e.ty = .never ∧
    applyPairObs fuel σ hyps entries cont = .ok t) ∨
  (∃ (P : Object sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) P)
      (body : InvTm (Ctx.ofHyps (hyps.push P)) A),
    (∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b) ∧
    forcedRule ([] : List (PosEntry sig)) A = .focus ∧
    EncodeReady
      (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
      (OriginEnv.ofHyps (hyps.push P)) 0 0 body ∧
    t = .foc (.letPos n (InvTm.castCtx (Ctx.ofHyps_push hyps P) body))) ∨
  (∃ (L R : Object sig.nBases)
      (pref : List (PosEntry sig)) (e : PosEntry sig)
      (ws : List (PosEntry sig))
      (x : Var (Ctx.ofHyps hyps) (.coprod L R))
      (tL : InvTm (Ctx.ofHyps hyps ▻ L) A)
      (tR : InvTm (Ctx.ofHyps hyps ▻ R) A),
    OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
    (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
    forcedRule (e :: ws) A = .leftCoprod e L R ∧
    OriginEnv.ofHyps hyps x = e.origin ∧
    EncodeReady
      (pushPos ws (.split e.origin false) L)
      (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps)
        (.split e.origin false)) 0 0 tL ∧
    EncodeReady
      (pushPos ws (.split e.origin true) R)
      (OriginEnv.weaken (A := R) (OriginEnv.ofHyps hyps)
        (.split e.origin true)) 0 0 tR ∧
    t = .case (.var x) tL tR) ∨
  (∃ (L R : Object sig.nBases)
      (pref : List (PosEntry sig)) (e : PosEntry sig)
      (ws : List (PosEntry sig))
      (x : Var (Ctx.ofHyps hyps) (.coprod L R))
      (t' : InvTm (Ctx.ofHyps hyps) .unit)
      (hA : A = .unit),
    OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
    (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
    forcedRule (e :: ws) (.unit : Object sig.nBases) = .leftCoprod e L R ∧
    OriginEnv.ofHyps hyps x = e.origin ∧
    worklistBasesOnly (leftCoprodBranchWs ws e false L) ∧
    worklistBasesOnly (leftCoprodBranchWs ws e true R) ∧
    t' = .case (.var x)
      (InvTm.castCtx (Ctx.ofHyps_push hyps L)
        (.unit : InvTm (Ctx.ofHyps (hyps.push L)) .unit))
      (InvTm.castCtx (Ctx.ofHyps_push hyps R)
        (.unit : InvTm (Ctx.ofHyps (hyps.push R)) .unit)) ∧
    t = hA ▸ t')

/--
Partial readiness from `EncodeReadyRawCase` (extra case data, not from raw alone).
-/
theorem phaseEncodeReady_of_applyPairObs_partial
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {t : InvTm (Ctx.ofHyps hyps) A}
    (hcase : EncodeReadyRawCase t) :
    PhaseEncodeReady t := by
  cases hcase with
  | inl h =>
      obtain ⟨fuel, σ, entries, cont, hcont, hempty, hcons, hok⟩ := h
      exact encodeReady_applyPairObs_emptyEntries fuel σ entries cont hcons hempty
        hcont hok
  | inr h =>
      cases h with
      | inl h =>
          obtain ⟨fuel, σ, entries, cont, pref, e, suf, hincons, hws, hpref, hty, hok⟩ := h
          exact encodeReady_applyPairObs_inconsistent fuel σ entries cont hincons hok
            hws hpref hty
      | inr h =>
          cases h with
          | inl h =>
              obtain ⟨P, n, body, hws, hfr, hbody, rfl⟩ := h
              exact encodeReady_applyObsNeu_atom_of_push_body_ready hws hfr hbody
          | inr h =>
              cases h with
              | inl h =>
                  obtain ⟨L, R, pref, e, ws, x, tL, tR, hws, hpref, hfr, hit, hL, hR, rfl⟩ := h
                  exact encodeReady_applyObsNeu_coprod_var x tL tR hws hpref hfr hit hL hR
              | inr h =>
                  obtain ⟨L, R, pref, e, ws, x, t', hA, hws, hpref, hfr, hit, hL, hR, rfl, ht⟩ := h
                  cases hA
                  cases ht
                  exact encodeReady_applyObsNeu_coprod_var_cast_unit
                    x hws hpref hfr hit hL hR

/-- Raw + `EncodeReadyRawCase` ⇒ certified (fragment certify, not full Raw→ready). -/
theorem certifyReferenceProduced_of_EncodeReadyRawCase
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {t : InvTm (Ctx.ofHyps hyps) A}
    (hraw : RawReferenceProduced t)
    (hcase : EncodeReadyRawCase t) :
    CertifiedReferenceProduced t :=
  ⟨hraw, phaseEncodeReady_of_applyPairObs_partial hcase⟩

/-- Partial certify when readiness is already known. -/
theorem certifyReferenceProduced_of_partial
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {t : InvTm (Ctx.ofHyps hyps) A}
    (hraw : RawReferenceProduced t)
    (hready : PhaseEncodeReady t) :
    CertifiedReferenceProduced t :=
  ⟨hraw, hready⟩

/--
Narrow `EncodeReadyOfRawGoal` slice: empty phase worklist + raw-produced `.unit`.
Readiness follows from the schedule shape; raw is the production witness.
-/
theorem encodeReady_of_rawReferenceProduced_unit_nil
    {hyps : Array (Object sig.nBases)}
    (hws : OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = [])
    (_hr : RawReferenceProduced (.unit : InvTm (Ctx.ofHyps hyps) .unit)) :
    PhaseEncodeReady (.unit : InvTm (Ctx.ofHyps hyps) .unit) :=
  phaseEncodeReady_unit_nil_worklist hws

/--
Narrow `EncodeReadyOfRawGoal` slice: base-only phase worklist + focus + raw
`.foc (.pos (.done _))`.
-/
theorem encodeReady_of_rawReferenceProduced_foc_pos_bases
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (p : PosNeu (Ctx.ofHyps hyps) A)
    (hws : ∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (_hr : RawReferenceProduced (.foc (.pos (.done p)))) :
    PhaseEncodeReady (.foc (.pos (.done p))) :=
  phaseEncodeReady_foc_pos_bases_focus p hws hfr

/-- Goal Prop: raw operational production implies phase encode readiness. -/
def EncodeReadyOfRawGoal : Prop :=
  ∀ {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A),
    RawReferenceProduced t → PhaseEncodeReady t

/-- Goal Prop: raw → certified. -/
def CertifyReferenceProducedGoal : Prop :=
  ∀ {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A),
    RawReferenceProduced t → CertifiedReferenceProduced t

theorem CertifyReferenceProducedGoal_of_ready (h : EncodeReadyOfRawGoal (sig := sig)) :
    CertifyReferenceProducedGoal (sig := sig) :=
  fun {_hyps} {_A} t hr => ⟨hr, h t hr⟩

/--
Restricted Raw→ready for **empty or exact-`.never`-only** schedules (no atom /
coprod entries). Empty needs a ready continuation; non-empty needs never on the
phase worklist. Unrestricted `EncodeReadyOfRawGoal` remains open.
-/
theorem encodeReady_of_rawReferenceProduced_emptyOrExactNever
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {t : InvTm (Ctx.ofHyps hyps) A}
    {newFrom : Nat} {goal : Object sig.nBases} {fuel : Nat}
    {entries : Array (PairEntry sig hyps)} {σ : ReachState sig.nBases}
    {t₀ u₀ : InvTm (Ctx.ofHyps hyps) A}
    (hold : checkOldInvariant (ReachCtx.oldPrefix ⟨hyps, newFrom⟩) goal = true)
    (ht₀ : WellInv t₀) (hu₀ : WellInv u₀)
    (hobs : pairObs ⟨hyps, newFrom⟩ goal t₀ u₀ = .ok entries σ)
    (hent : exactNeverEntriesOnly entries.toList)
    (hcons : σ.inconsistent = false)
    (hok : applyPairObs (saturationBudget fuel entries.size) σ hyps entries t₀ = .ok t ∨
      applyPairObs (saturationBudget fuel entries.size) σ hyps entries u₀ = .ok t)
    (hempty : entries.toList = [] → PhaseEncodeReady t₀ ∧ PhaseEncodeReady u₀)
    (hnever : entries.toList ≠ [] →
      ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
        OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
        (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
        e.ty = .never) :
    PhaseEncodeReady t := by
  cases hok with
  | inl h =>
      simp only [applyPairObs, hcons, ↓reduceIte] at h
      match hfuel : saturationBudget fuel entries.size with
      | 0 =>
          rw [hfuel] at h
          simp [applyPairObsGo] at h
      | fuel' + 1 =>
          have hgo :
              applyPairObsGo (fuel' + 1) σ hyps entries.toList t₀ = .ok t := by
            simpa [hfuel] using h
          exact encodeReady_applyPairObsGo_exactNeverOnly fuel' σ entries.toList t₀
            hent hgo (fun hem => (hempty (by simpa using hem)).1) hnever
  | inr h =>
      simp only [applyPairObs, hcons, ↓reduceIte] at h
      match hfuel : saturationBudget fuel entries.size with
      | 0 =>
          rw [hfuel] at h
          simp [applyPairObsGo] at h
      | fuel' + 1 =>
          have hgo :
              applyPairObsGo (fuel' + 1) σ hyps entries.toList u₀ = .ok t := by
            simpa [hfuel] using h
          exact encodeReady_applyPairObsGo_exactNeverOnly fuel' σ entries.toList u₀
            hent hgo (fun hem => (hempty (by simpa using hem)).2) hnever

/-- Goal Prop for the empty/exact-never restricted fragment. -/
def EncodeReadyOfRawGoal_emptyOrExactNever : Prop :=
  ∀ {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A),
    RawReferenceProduced t →
    (∃ (newFrom : Nat) (goal : Object sig.nBases) (fuel : Nat)
        (entries : Array (PairEntry sig hyps)) (σ : ReachState sig.nBases)
        (t₀ u₀ : InvTm (Ctx.ofHyps hyps) A),
      checkOldInvariant (ReachCtx.oldPrefix ⟨hyps, newFrom⟩) goal = true ∧
        WellInv t₀ ∧ WellInv u₀ ∧
        pairObs ⟨hyps, newFrom⟩ goal t₀ u₀ = .ok entries σ ∧
        exactNeverEntriesOnly entries.toList ∧
        σ.inconsistent = false ∧
        (applyPairObs (saturationBudget fuel entries.size) σ hyps entries t₀ = .ok t ∨
          applyPairObs (saturationBudget fuel entries.size) σ hyps entries u₀ = .ok t) ∧
        (entries.toList = [] → PhaseEncodeReady t₀ ∧ PhaseEncodeReady u₀) ∧
        (entries.toList ≠ [] →
          ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
            OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
            (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
            e.ty = .never)) →
    PhaseEncodeReady t

theorem EncodeReadyOfRawGoal_emptyOrExactNever_holds :
    EncodeReadyOfRawGoal_emptyOrExactNever (sig := sig) := by
  intro hyps A t _hr hex
  obtain ⟨newFrom, goal, fuel, entries, σ, t₀, u₀,
    hold, ht₀, hu₀, hobs, hent, hcons, hok, hempty, hnever⟩ := hex
  exact encodeReady_of_rawReferenceProduced_emptyOrExactNever
    hold ht₀ hu₀ hobs hent hcons hok hempty hnever

/--
Restricted Raw→ready for **empty / exact-`.never`-only / single exact atom
nil-rest / single exact coprod-var nil-rest** schedules
(`emptyNeverOrNilRestObs`). Atom needs `atomPushCont` ready; coprod-var needs
cast branch EncodeReady under the left-coprod schedule. Unrestricted
`EncodeReadyOfRawGoal` remains open.
-/
theorem encodeReady_of_rawReferenceProduced_emptyNeverOrNilRestObs
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {t : InvTm (Ctx.ofHyps hyps) A}
    {newFrom : Nat} {goal : Object sig.nBases} {fuel : Nat}
    {entries : Array (PairEntry sig hyps)} {σ : ReachState sig.nBases}
    {t₀ u₀ : InvTm (Ctx.ofHyps hyps) A}
    (_hold : checkOldInvariant (ReachCtx.oldPrefix ⟨hyps, newFrom⟩) goal = true)
    (_ht₀ : WellInv t₀) (_hu₀ : WellInv u₀)
    (_hobs : pairObs ⟨hyps, newFrom⟩ goal t₀ u₀ = .ok entries σ)
    (hcons : σ.inconsistent = false)
    (hok : applyPairObs (saturationBudget fuel entries.size) σ hyps entries t₀ = .ok t ∨
      applyPairObs (saturationBudget fuel entries.size) σ hyps entries u₀ = .ok t)
    (hdisc_t₀ :
      (exactNeverEntriesOnly entries.toList ∧
        (entries.toList = [] → PhaseEncodeReady t₀) ∧
        (entries.toList ≠ [] →
          ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
            OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
            (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
            e.ty = .never)) ∨
      (∃ (P : Object sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) P),
        entries.toList = [.exact P n] ∧
        P ≠ (.never : Object sig.nBases) ∧
        (∀ L R, P ≠ .coprod L R) ∧
        (∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
          ∃ b : Fin sig.nBases, e.ty = .base b) ∧
        forcedRule ([] : List (PosEntry sig)) A = .focus ∧
        EncodeReady
          (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
          (OriginEnv.ofHyps (hyps.push P)) 0 0 (atomPushCont n t₀)) ∨
      (∃ (L R : Object sig.nBases)
          (pref : List (PosEntry sig)) (e : PosEntry sig) (ws : List (PosEntry sig))
          (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
        entries.toList = [.exact (.coprod L R) (.var x)] ∧
        OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
        (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
        forcedRule (e :: ws) A = .leftCoprod e L R ∧
        OriginEnv.ofHyps hyps x = e.origin ∧
        EncodeReady
          (pushPos ws (.split e.origin false) L)
          (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps)
            (.split e.origin false)) 0 0
          (InvTm.castCtx (Ctx.ofHyps_push hyps L)
            (coprodPushContL (.var x) t₀)) ∧
        EncodeReady
          (pushPos ws (.split e.origin true) R)
          (OriginEnv.weaken (A := R) (OriginEnv.ofHyps hyps)
            (.split e.origin true)) 0 0
          (InvTm.castCtx (Ctx.ofHyps_push hyps R)
            (coprodPushContR (.var x) t₀))))
    (hdisc_u₀ :
      (exactNeverEntriesOnly entries.toList ∧
        (entries.toList = [] → PhaseEncodeReady u₀) ∧
        (entries.toList ≠ [] →
          ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
            OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
            (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
            e.ty = .never)) ∨
      (∃ (P : Object sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) P),
        entries.toList = [.exact P n] ∧
        P ≠ (.never : Object sig.nBases) ∧
        (∀ L R, P ≠ .coprod L R) ∧
        (∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
          ∃ b : Fin sig.nBases, e.ty = .base b) ∧
        forcedRule ([] : List (PosEntry sig)) A = .focus ∧
        EncodeReady
          (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
          (OriginEnv.ofHyps (hyps.push P)) 0 0 (atomPushCont n u₀)) ∨
      (∃ (L R : Object sig.nBases)
          (pref : List (PosEntry sig)) (e : PosEntry sig) (ws : List (PosEntry sig))
          (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
        entries.toList = [.exact (.coprod L R) (.var x)] ∧
        OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
        (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
        forcedRule (e :: ws) A = .leftCoprod e L R ∧
        OriginEnv.ofHyps hyps x = e.origin ∧
        EncodeReady
          (pushPos ws (.split e.origin false) L)
          (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps)
            (.split e.origin false)) 0 0
          (InvTm.castCtx (Ctx.ofHyps_push hyps L)
            (coprodPushContL (.var x) u₀)) ∧
        EncodeReady
          (pushPos ws (.split e.origin true) R)
          (OriginEnv.weaken (A := R) (OriginEnv.ofHyps hyps)
            (.split e.origin true)) 0 0
          (InvTm.castCtx (Ctx.ofHyps_push hyps R)
            (coprodPushContR (.var x) u₀)))) :
    PhaseEncodeReady t := by
  cases hok with
  | inl h =>
      simp only [applyPairObs, hcons] at h
      match hfuel : saturationBudget fuel entries.size with
      | 0 =>
          rw [hfuel] at h
          simp [applyPairObsGo] at h
      | fuel' + 1 =>
          have hgo :
              applyPairObsGo (fuel' + 1) σ hyps entries.toList t₀ = .ok t := by
            simpa [hfuel] using h
          exact encodeReady_applyPairObsGo_emptyNeverOrNilRestObs fuel' σ
            entries.toList t₀ hgo hdisc_t₀
  | inr h =>
      simp only [applyPairObs, hcons] at h
      match hfuel : saturationBudget fuel entries.size with
      | 0 =>
          rw [hfuel] at h
          simp [applyPairObsGo] at h
      | fuel' + 1 =>
          have hgo :
              applyPairObsGo (fuel' + 1) σ hyps entries.toList u₀ = .ok t := by
            simpa [hfuel] using h
          exact encodeReady_applyPairObsGo_emptyNeverOrNilRestObs fuel' σ
            entries.toList u₀ hgo hdisc_u₀

/-- Goal Prop for the empty/never/nil-rest-obs restricted fragment. -/
def EncodeReadyOfRawGoal_emptyNeverOrNilRestObs : Prop :=
  ∀ {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A),
    RawReferenceProduced t →
    (∃ (newFrom : Nat) (goal : Object sig.nBases) (fuel : Nat)
        (entries : Array (PairEntry sig hyps)) (σ : ReachState sig.nBases)
        (t₀ u₀ : InvTm (Ctx.ofHyps hyps) A),
      checkOldInvariant (ReachCtx.oldPrefix ⟨hyps, newFrom⟩) goal = true ∧
        WellInv t₀ ∧ WellInv u₀ ∧
        pairObs ⟨hyps, newFrom⟩ goal t₀ u₀ = .ok entries σ ∧
        σ.inconsistent = false ∧
        (applyPairObs (saturationBudget fuel entries.size) σ hyps entries t₀ = .ok t ∨
          applyPairObs (saturationBudget fuel entries.size) σ hyps entries u₀ = .ok t) ∧
        ((exactNeverEntriesOnly entries.toList ∧
            (entries.toList = [] → PhaseEncodeReady t₀) ∧
            (entries.toList ≠ [] →
              ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
                OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
                (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
                e.ty = .never)) ∨
          (∃ (P : Object sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) P),
            entries.toList = [.exact P n] ∧
            P ≠ (.never : Object sig.nBases) ∧
            (∀ L R, P ≠ .coprod L R) ∧
            (∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
              ∃ b : Fin sig.nBases, e.ty = .base b) ∧
            forcedRule ([] : List (PosEntry sig)) A = .focus ∧
            EncodeReady
              (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
              (OriginEnv.ofHyps (hyps.push P)) 0 0 (atomPushCont n t₀)) ∨
          (∃ (L R : Object sig.nBases)
              (pref : List (PosEntry sig)) (e : PosEntry sig) (ws : List (PosEntry sig))
              (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
            entries.toList = [.exact (.coprod L R) (.var x)] ∧
            OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
            (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
            forcedRule (e :: ws) A = .leftCoprod e L R ∧
            OriginEnv.ofHyps hyps x = e.origin ∧
            EncodeReady
              (pushPos ws (.split e.origin false) L)
              (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps)
                (.split e.origin false)) 0 0
              (InvTm.castCtx (Ctx.ofHyps_push hyps L)
                (coprodPushContL (.var x) t₀)) ∧
            EncodeReady
              (pushPos ws (.split e.origin true) R)
              (OriginEnv.weaken (A := R) (OriginEnv.ofHyps hyps)
                (.split e.origin true)) 0 0
              (InvTm.castCtx (Ctx.ofHyps_push hyps R)
                (coprodPushContR (.var x) t₀)))) ∧
        ((exactNeverEntriesOnly entries.toList ∧
            (entries.toList = [] → PhaseEncodeReady u₀) ∧
            (entries.toList ≠ [] →
              ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
                OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
                (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
                e.ty = .never)) ∨
          (∃ (P : Object sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) P),
            entries.toList = [.exact P n] ∧
            P ≠ (.never : Object sig.nBases) ∧
            (∀ L R, P ≠ .coprod L R) ∧
            (∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
              ∃ b : Fin sig.nBases, e.ty = .base b) ∧
            forcedRule ([] : List (PosEntry sig)) A = .focus ∧
            EncodeReady
              (OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)))
              (OriginEnv.ofHyps (hyps.push P)) 0 0 (atomPushCont n u₀)) ∨
          (∃ (L R : Object sig.nBases)
              (pref : List (PosEntry sig)) (e : PosEntry sig) (ws : List (PosEntry sig))
              (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
            entries.toList = [.exact (.coprod L R) (.var x)] ∧
            OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
            (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
            forcedRule (e :: ws) A = .leftCoprod e L R ∧
            OriginEnv.ofHyps hyps x = e.origin ∧
            EncodeReady
              (pushPos ws (.split e.origin false) L)
              (OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps)
                (.split e.origin false)) 0 0
              (InvTm.castCtx (Ctx.ofHyps_push hyps L)
                (coprodPushContL (.var x) u₀)) ∧
            EncodeReady
              (pushPos ws (.split e.origin true) R)
              (OriginEnv.weaken (A := R) (OriginEnv.ofHyps hyps)
                (.split e.origin true)) 0 0
              (InvTm.castCtx (Ctx.ofHyps_push hyps R)
                (coprodPushContR (.var x) u₀))))) →
    PhaseEncodeReady t

theorem EncodeReadyOfRawGoal_emptyNeverOrNilRestObs_holds :
    EncodeReadyOfRawGoal_emptyNeverOrNilRestObs (sig := sig) := by
  intro hyps A t _hr hex
  obtain ⟨newFrom, goal, fuel, entries, σ, t₀, u₀,
    hold, ht₀, hu₀, hobs, hcons, hok, hdisc_t₀, hdisc_u₀⟩ := hex
  exact encodeReady_of_rawReferenceProduced_emptyNeverOrNilRestObs
    hold ht₀ hu₀ hobs hcons hok hdisc_t₀ hdisc_u₀

/--
Restricted Raw→ready where atom/coprod push-body facts are derived from
continuation shape (`emptyNeverOrDerivedNilRest` / `AtomDerivedContShape`):
foc-done / sat-of-foc-pos / base-binder letPos around foc-pos for base atom;
unit + bases-only branches for coprod-var. Unrestricted goal remains open.
-/
theorem encodeReady_of_rawReferenceProduced_emptyNeverOrDerivedNilRest
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {t : InvTm (Ctx.ofHyps hyps) A}
    {newFrom : Nat} {goal : Object sig.nBases} {fuel : Nat}
    {entries : Array (PairEntry sig hyps)} {σ : ReachState sig.nBases}
    {t₀ u₀ : InvTm (Ctx.ofHyps hyps) A}
    (_hold : checkOldInvariant (ReachCtx.oldPrefix ⟨hyps, newFrom⟩) goal = true)
    (_ht₀ : WellInv t₀) (_hu₀ : WellInv u₀)
    (_hobs : pairObs ⟨hyps, newFrom⟩ goal t₀ u₀ = .ok entries σ)
    (hcons : σ.inconsistent = false)
    (hok : applyPairObs (saturationBudget fuel entries.size) σ hyps entries t₀ = .ok t ∨
      applyPairObs (saturationBudget fuel entries.size) σ hyps entries u₀ = .ok t)
    (hdisc_t₀ :
      (exactNeverEntriesOnly entries.toList ∧
        (entries.toList = [] → PhaseEncodeReady t₀) ∧
        (entries.toList ≠ [] →
          ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
            OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
            (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
            e.ty = .never)) ∨
      (∃ (b : Fin sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base b)),
        entries.toList = [.exact (.base b) n] ∧
        worklistBasesOnly (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)) ∧
        forcedRule ([] : List (PosEntry sig)) A = .focus ∧
        AtomDerivedContShape t₀) ∨
      (∃ (L R : Object sig.nBases)
          (pref : List (PosEntry sig)) (e : PosEntry sig) (ws : List (PosEntry sig))
          (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
        entries.toList = [.exact (.coprod L R) (.var x)] ∧
        OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
        (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
        forcedRule (e :: ws) A = .leftCoprod e L R ∧
        OriginEnv.ofHyps hyps x = e.origin ∧
        worklistBasesOnly (leftCoprodBranchWs ws e false L) ∧
        worklistBasesOnly (leftCoprodBranchWs ws e true R) ∧
        CoprodDerivedContShape t₀))
    (hdisc_u₀ :
      (exactNeverEntriesOnly entries.toList ∧
        (entries.toList = [] → PhaseEncodeReady u₀) ∧
        (entries.toList ≠ [] →
          ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
            OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
            (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
            e.ty = .never)) ∨
      (∃ (b : Fin sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base b)),
        entries.toList = [.exact (.base b) n] ∧
        worklistBasesOnly (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)) ∧
        forcedRule ([] : List (PosEntry sig)) A = .focus ∧
        AtomDerivedContShape u₀) ∨
      (∃ (L R : Object sig.nBases)
          (pref : List (PosEntry sig)) (e : PosEntry sig) (ws : List (PosEntry sig))
          (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
        entries.toList = [.exact (.coprod L R) (.var x)] ∧
        OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
        (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
        forcedRule (e :: ws) A = .leftCoprod e L R ∧
        OriginEnv.ofHyps hyps x = e.origin ∧
        worklistBasesOnly (leftCoprodBranchWs ws e false L) ∧
        worklistBasesOnly (leftCoprodBranchWs ws e true R) ∧
        CoprodDerivedContShape u₀)) :
    PhaseEncodeReady t := by
  cases hok with
  | inl h =>
      simp only [applyPairObs, hcons] at h
      match hfuel : saturationBudget fuel entries.size with
      | 0 =>
          rw [hfuel] at h
          simp [applyPairObsGo] at h
      | fuel' + 1 =>
          have hgo :
              applyPairObsGo (fuel' + 1) σ hyps entries.toList t₀ = .ok t := by
            simpa [hfuel] using h
          exact encodeReady_applyPairObsGo_emptyNeverOrDerivedNilRest fuel' σ
            entries.toList t₀ hgo hdisc_t₀
  | inr h =>
      simp only [applyPairObs, hcons] at h
      match hfuel : saturationBudget fuel entries.size with
      | 0 =>
          rw [hfuel] at h
          simp [applyPairObsGo] at h
      | fuel' + 1 =>
          have hgo :
              applyPairObsGo (fuel' + 1) σ hyps entries.toList u₀ = .ok t := by
            simpa [hfuel] using h
          exact encodeReady_applyPairObsGo_emptyNeverOrDerivedNilRest fuel' σ
            entries.toList u₀ hgo hdisc_u₀

def EncodeReadyOfRawGoal_emptyNeverOrDerivedNilRest : Prop :=
  ∀ {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A),
    RawReferenceProduced t →
    (∃ (newFrom : Nat) (goal : Object sig.nBases) (fuel : Nat)
        (entries : Array (PairEntry sig hyps)) (σ : ReachState sig.nBases)
        (t₀ u₀ : InvTm (Ctx.ofHyps hyps) A),
      checkOldInvariant (ReachCtx.oldPrefix ⟨hyps, newFrom⟩) goal = true ∧
        WellInv t₀ ∧ WellInv u₀ ∧
        pairObs ⟨hyps, newFrom⟩ goal t₀ u₀ = .ok entries σ ∧
        σ.inconsistent = false ∧
        (applyPairObs (saturationBudget fuel entries.size) σ hyps entries t₀ = .ok t ∨
          applyPairObs (saturationBudget fuel entries.size) σ hyps entries u₀ = .ok t) ∧
        ((exactNeverEntriesOnly entries.toList ∧
            (entries.toList = [] → PhaseEncodeReady t₀) ∧
            (entries.toList ≠ [] →
              ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
                OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
                (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
                e.ty = .never)) ∨
          (∃ (b : Fin sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base b)),
            entries.toList = [.exact (.base b) n] ∧
            worklistBasesOnly (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)) ∧
            forcedRule ([] : List (PosEntry sig)) A = .focus ∧
            AtomDerivedContShape t₀) ∨
          (∃ (L R : Object sig.nBases)
              (pref : List (PosEntry sig)) (e : PosEntry sig) (ws : List (PosEntry sig))
              (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
            entries.toList = [.exact (.coprod L R) (.var x)] ∧
            OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
            (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
            forcedRule (e :: ws) A = .leftCoprod e L R ∧
            OriginEnv.ofHyps hyps x = e.origin ∧
            worklistBasesOnly (leftCoprodBranchWs ws e false L) ∧
            worklistBasesOnly (leftCoprodBranchWs ws e true R) ∧
            CoprodDerivedContShape t₀)) ∧
        ((exactNeverEntriesOnly entries.toList ∧
            (entries.toList = [] → PhaseEncodeReady u₀) ∧
            (entries.toList ≠ [] →
              ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
                OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
                (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
                e.ty = .never)) ∨
          (∃ (b : Fin sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base b)),
            entries.toList = [.exact (.base b) n] ∧
            worklistBasesOnly (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)) ∧
            forcedRule ([] : List (PosEntry sig)) A = .focus ∧
            AtomDerivedContShape u₀) ∨
          (∃ (L R : Object sig.nBases)
              (pref : List (PosEntry sig)) (e : PosEntry sig) (ws : List (PosEntry sig))
              (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
            entries.toList = [.exact (.coprod L R) (.var x)] ∧
            OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
            (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
            forcedRule (e :: ws) A = .leftCoprod e L R ∧
            OriginEnv.ofHyps hyps x = e.origin ∧
            worklistBasesOnly (leftCoprodBranchWs ws e false L) ∧
            worklistBasesOnly (leftCoprodBranchWs ws e true R) ∧
            CoprodDerivedContShape u₀))) →
    PhaseEncodeReady t

theorem EncodeReadyOfRawGoal_emptyNeverOrDerivedNilRest_holds :
    EncodeReadyOfRawGoal_emptyNeverOrDerivedNilRest (sig := sig) := by
  intro hyps A t _hr hex
  obtain ⟨newFrom, goal, fuel, entries, σ, t₀, u₀,
    hold, ht₀, hu₀, hobs, hcons, hok, hdisc_t₀, hdisc_u₀⟩ := hex
  exact encodeReady_of_rawReferenceProduced_emptyNeverOrDerivedNilRest
    hold ht₀ hu₀ hobs hcons hok hdisc_t₀ hdisc_u₀

/-- Continuation shape for empty-schedule WellInv→ready (no ready stash). -/
def WellInvIntroContShape {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (cont : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  (∃ hA : A = (.unit : Object sig.nBases),
      HEq cont (.unit : InvTm (Ctx.ofHyps hyps) .unit)) ∨
  (∃ p : PosNeu (Ctx.ofHyps hyps) A,
      cont = .foc (.pos (.done p)) ∧
      forcedRule ([] : List (PosEntry sig)) A = .focus) ∨
  (∃ (L R : Object sig.nBases)
      (n : NegNeu (Ctx.ofHyps hyps) (.prod L R))
      (hA : A = .prod L R),
      HEq cont
        (.foc (.neg (.done n)) :
          InvTm (Ctx.ofHyps hyps) (.prod L R))) ∨
  (∃ (Arg Ret : Object sig.nBases)
      (n : NegNeu (Ctx.ofHyps hyps) (.exp Arg Ret))
      (hA : A = .exp Arg Ret),
      HEq cont
        (.foc (.neg (.done n)) :
          InvTm (Ctx.ofHyps hyps) (.exp Arg Ret))) ∨
  (∃ (s : Schedule sig.nBases) (p : PosNeu (Ctx.ofHyps hyps) A),
      cont = .foc (.sat (.mk s (.foc (.pos (.done p))))) ∧
      forcedRule ([] : List (PosEntry sig)) A = .focus)

/--
Restricted Raw→ready: **empty schedule + bases-only + WellInv intro shape**
(no cont ready stash) **or** `emptyNeverOrDerivedNilRest` discipline.
-/
theorem encodeReady_of_rawReferenceProduced_emptyWellInvIntroOrDerived
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {t : InvTm (Ctx.ofHyps hyps) A}
    {newFrom : Nat} {goal : Object sig.nBases} {fuel : Nat}
    {entries : Array (PairEntry sig hyps)} {σ : ReachState sig.nBases}
    {t₀ u₀ : InvTm (Ctx.ofHyps hyps) A}
    (hold : checkOldInvariant (ReachCtx.oldPrefix ⟨hyps, newFrom⟩) goal = true)
    (ht₀ : WellInv t₀) (hu₀ : WellInv u₀)
    (hobs : pairObs ⟨hyps, newFrom⟩ goal t₀ u₀ = .ok entries σ)
    (hcons : σ.inconsistent = false)
    (hok : applyPairObs (saturationBudget fuel entries.size) σ hyps entries t₀ = .ok t ∨
      applyPairObs (saturationBudget fuel entries.size) σ hyps entries u₀ = .ok t)
    (hdisc :
      (entries.toList = [] ∧
        worklistBasesOnly (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)) ∧
        WellInvIntroContShape t₀ ∧ WellInvIntroContShape u₀) ∨
      ((exactNeverEntriesOnly entries.toList ∧
          (entries.toList = [] → PhaseEncodeReady t₀) ∧
          (entries.toList ≠ [] →
            ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
              OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
              (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
              e.ty = .never)) ∨
        (∃ (b : Fin sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base b)),
          entries.toList = [.exact (.base b) n] ∧
          worklistBasesOnly (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)) ∧
          forcedRule ([] : List (PosEntry sig)) A = .focus ∧
          AtomDerivedContShape t₀) ∨
        (∃ (L R : Object sig.nBases)
            (pref : List (PosEntry sig)) (e : PosEntry sig) (ws : List (PosEntry sig))
            (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
          entries.toList = [.exact (.coprod L R) (.var x)] ∧
          OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
          (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
          forcedRule (e :: ws) A = .leftCoprod e L R ∧
          OriginEnv.ofHyps hyps x = e.origin ∧
          worklistBasesOnly (leftCoprodBranchWs ws e false L) ∧
          worklistBasesOnly (leftCoprodBranchWs ws e true R) ∧
          CoprodDerivedContShape t₀)) ∧
      ((exactNeverEntriesOnly entries.toList ∧
          (entries.toList = [] → PhaseEncodeReady u₀) ∧
          (entries.toList ≠ [] →
            ∃ (pref : List (PosEntry sig)) (e : PosEntry sig) (suf : List (PosEntry sig)),
              OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: suf ∧
              (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
              e.ty = .never)) ∨
        (∃ (b : Fin sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base b)),
          entries.toList = [.exact (.base b) n] ∧
          worklistBasesOnly (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)) ∧
          forcedRule ([] : List (PosEntry sig)) A = .focus ∧
          AtomDerivedContShape u₀) ∨
        (∃ (L R : Object sig.nBases)
            (pref : List (PosEntry sig)) (e : PosEntry sig) (ws : List (PosEntry sig))
            (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
          entries.toList = [.exact (.coprod L R) (.var x)] ∧
          OriginEnv.posWorklist (OriginEnv.ofHyps hyps) = pref ++ e :: ws ∧
          (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
          forcedRule (e :: ws) A = .leftCoprod e L R ∧
          OriginEnv.ofHyps hyps x = e.origin ∧
          worklistBasesOnly (leftCoprodBranchWs ws e false L) ∧
          worklistBasesOnly (leftCoprodBranchWs ws e true R) ∧
          CoprodDerivedContShape u₀))) :
    PhaseEncodeReady t := by
  cases hdisc with
  | inl h =>
      obtain ⟨hempty, hws, hshape₀, hshape₁⟩ := h
      cases hok with
      | inl hok =>
          exact encodeReady_applyPairObs_emptyEntries_of_wellInv_intro
            (saturationBudget fuel entries.size) σ entries t₀ hcons hempty hws ht₀
            hshape₀ hok
      | inr hok =>
          exact encodeReady_applyPairObs_emptyEntries_of_wellInv_intro
            (saturationBudget fuel entries.size) σ entries u₀ hcons hempty hws hu₀
            hshape₁ hok
  | inr h =>
      obtain ⟨hdisc_t₀, hdisc_u₀⟩ := h
      exact encodeReady_of_rawReferenceProduced_emptyNeverOrDerivedNilRest
        hold ht₀ hu₀ hobs hcons hok hdisc_t₀ hdisc_u₀

def EncodeReadyOfRawGoal_emptyWellInvIntroOrDerived : Prop :=
  ∀ {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A),
    RawReferenceProduced t →
    (∃ (newFrom : Nat) (goal : Object sig.nBases) (fuel : Nat)
        (entries : Array (PairEntry sig hyps)) (σ : ReachState sig.nBases)
        (t₀ u₀ : InvTm (Ctx.ofHyps hyps) A),
      checkOldInvariant (ReachCtx.oldPrefix ⟨hyps, newFrom⟩) goal = true ∧
        WellInv t₀ ∧ WellInv u₀ ∧
        pairObs ⟨hyps, newFrom⟩ goal t₀ u₀ = .ok entries σ ∧
        σ.inconsistent = false ∧
        (applyPairObs (saturationBudget fuel entries.size) σ hyps entries t₀ = .ok t ∨
          applyPairObs (saturationBudget fuel entries.size) σ hyps entries u₀ = .ok t) ∧
        ((entries.toList = [] ∧
            worklistBasesOnly (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)) ∧
            WellInvIntroContShape t₀ ∧ WellInvIntroContShape u₀) ∨
          (((exactNeverEntriesOnly entries.toList ∧
                (entries.toList = [] → PhaseEncodeReady t₀) ∧
                (entries.toList ≠ [] →
                  ∃ (pref : List (PosEntry sig)) (e : PosEntry sig)
                      (suf : List (PosEntry sig)),
                    OriginEnv.posWorklist (OriginEnv.ofHyps hyps) =
                      pref ++ e :: suf ∧
                    (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
                    e.ty = .never)) ∨
              (∃ (b : Fin sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base b)),
                entries.toList = [.exact (.base b) n] ∧
                worklistBasesOnly
                  (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)) ∧
                forcedRule ([] : List (PosEntry sig)) A = .focus ∧
                AtomDerivedContShape t₀) ∨
              (∃ (L R : Object sig.nBases)
                  (pref : List (PosEntry sig)) (e : PosEntry sig)
                  (ws : List (PosEntry sig))
                  (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
                entries.toList = [.exact (.coprod L R) (.var x)] ∧
                OriginEnv.posWorklist (OriginEnv.ofHyps hyps) =
                  pref ++ e :: ws ∧
                (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
                forcedRule (e :: ws) A =
                  .leftCoprod e L R ∧
                OriginEnv.ofHyps hyps x = e.origin ∧
                worklistBasesOnly (leftCoprodBranchWs ws e false L) ∧
                worklistBasesOnly (leftCoprodBranchWs ws e true R) ∧
                CoprodDerivedContShape t₀)) ∧
            ((exactNeverEntriesOnly entries.toList ∧
                (entries.toList = [] → PhaseEncodeReady u₀) ∧
                (entries.toList ≠ [] →
                  ∃ (pref : List (PosEntry sig)) (e : PosEntry sig)
                      (suf : List (PosEntry sig)),
                    OriginEnv.posWorklist (OriginEnv.ofHyps hyps) =
                      pref ++ e :: suf ∧
                    (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
                    e.ty = .never)) ∨
              (∃ (b : Fin sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) (.base b)),
                entries.toList = [.exact (.base b) n] ∧
                worklistBasesOnly
                  (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)) ∧
                forcedRule ([] : List (PosEntry sig)) A = .focus ∧
                AtomDerivedContShape u₀) ∨
              (∃ (L R : Object sig.nBases)
                  (pref : List (PosEntry sig)) (e : PosEntry sig)
                  (ws : List (PosEntry sig))
                  (x : Var (Ctx.ofHyps hyps) (.coprod L R)),
                entries.toList = [.exact (.coprod L R) (.var x)] ∧
                OriginEnv.posWorklist (OriginEnv.ofHyps hyps) =
                  pref ++ e :: ws ∧
                (∀ e' ∈ pref, ∃ b : Fin sig.nBases, e'.ty = .base b) ∧
                forcedRule (e :: ws) A =
                  .leftCoprod e L R ∧
                OriginEnv.ofHyps hyps x = e.origin ∧
                worklistBasesOnly (leftCoprodBranchWs ws e false L) ∧
                worklistBasesOnly (leftCoprodBranchWs ws e true R) ∧
                CoprodDerivedContShape u₀))))) →
    PhaseEncodeReady t

theorem EncodeReadyOfRawGoal_emptyWellInvIntroOrDerived_holds :
    EncodeReadyOfRawGoal_emptyWellInvIntroOrDerived (sig := sig) := by
  intro hyps A t _hr hex
  obtain ⟨newFrom, goal, fuel, entries, σ, t₀, u₀,
    hold, ht₀, hu₀, hobs, hcons, hok, hdisc⟩ := hex
  exact encodeReady_of_rawReferenceProduced_emptyWellInvIntroOrDerived
    hold ht₀ hu₀ hobs hcons hok hdisc

end Equality
end Gimbal
