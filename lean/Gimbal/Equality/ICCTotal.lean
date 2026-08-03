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

/-- Projection: the fragment certificate stores phase-entry readiness. -/
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

theorem OriginEnv.weaken_rekeyHypToObs {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) (hypIdx k : Nat)
    {B : Object sig.nBases} (x : Var (Γ ▻ A) B) :
    Origin.rekeyHypToObs hypIdx k (OriginEnv.weaken (A := A) ε o x) =
      OriginEnv.weaken (A := A)
        (fun {C} y => Origin.rekeyHypToObs hypIdx k (ε y))
        (Origin.rekeyHypToObs hypIdx k o) x := by
  cases x <;> rfl

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

/-! ### Rekey EncodeReady (peel-free)

Transport `EncodeReadyNoPeel` along `Origin.rekeyHypToObs hypIdx 0` (bumps
`obsSlot`). Omits peel / unit-η (those need `find?` / `peelCaseOuter` rekey).
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

/-! ### Gaps (peel / full produced)

* `leftCoprod_peel` / `leftCoprod_unitEta` rekey needs `find?` / `peelCaseOuter`
  under `rekeyHypToObs` (temp dig `.obs 0` ≠ shifted obs slots).
* Closing `applyObsNeu` still needs `EncodeReady` cast along `Ctx.ofHyps_push`
  so `encodeReady_newest_hyp_to_obs_noPeel` + `encodeReadyNoPeel_of_base_prefix`
  feed `encodeReady_applyObsNeu_atom_basesOnly` (body under `pushPos [] (.obs 0)`).
* Full `phaseEncodeReady_of_produced` still open beyond empty schedule and
  inconsistent abort-with-never.
* Fragment still stores `ready` — not derived for all `ReferenceProduced`.
-/

/-- Partial: empty schedule or inconsistent abort with never-on-worklist. -/
theorem phaseEncodeReady_of_produced_partial
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {t : InvTm (Ctx.ofHyps hyps) A}
    (_h : ReferenceProduced t)
    (hcase :
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
        applyPairObs fuel σ hyps entries cont = .ok t)) :
    PhaseEncodeReady t := by
  cases hcase with
  | inl h =>
      obtain ⟨fuel, σ, entries, cont, hcont, hempty, hcons, hok⟩ := h
      exact encodeReady_applyPairObs_emptyEntries fuel σ entries cont hcons hempty
        hcont hok
  | inr h =>
      obtain ⟨fuel, σ, entries, cont, pref, e, suf, hincons, hws, hpref, hty, hok⟩ := h
      exact encodeReady_applyPairObs_inconsistent fuel σ entries cont hincons hok
        hws hpref hty


end Equality
end Gimbal
