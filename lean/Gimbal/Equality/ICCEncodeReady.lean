/-
  EncodeReady operational core (Cleanup A extract from `ICCTotal`).

  KEEP / MOVE inventory:
  * KEEP here: EncodeReady↔encode operational lemmas used by Completeness /
    EncodeIx (`encodeReady_go_some`, `EncodableICC.of_encodeReady`,
    `encode_of_encodeReady`, `encodeReady_of_validEncodeFragment`), EncodeIccStep
    packaging, fuel-mono / Go unfolds those depend on, and base intros
    (`encodeReady_unit_nil`, `encodeReady_abort_leftNever`,
    `encodeReady_foc_pos_nil`, `encodeReady_foc_neg_nil`).
  * DELETED from Total (Cleanup A): `CoprodDerived*` / `AtomDerived*` / nil-rest
    Raw→Ready exact-schedule shape chains; entire `ICCReadyCert` and legacy
    `ICCEncodeSchedule` modules.

  EncodeIx imports this module (not `ICCTotal`).
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

theorem encodeICCGo_abort_focus {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (n : NegNeu Γ .never)
    (hforce : forcedRule ws A = .focus) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.abort (A := A) n) =
      some (.abort (.obs (sig := sig) obsSlot)) := by
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
                | abort n =>
                    rw [encodeICCGo_abort_focus fuel₁ ws ε domNest obsSlot n hfr] at h
                    rw [encodeICCGo_abort_focus fuel₂ ws ε domNest obsSlot n hfr]
                    exact h
                | unit => simp [encodeICCGo, hfr] at h
                | pair _ _ => simp [encodeICCGo, hfr] at h
                | lam _ => simp [encodeICCGo, hfr] at h
                | case _ _ _ => simp [encodeICCGo, hfr] at h
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
            | abort n' =>
                rw [encodeICCGo_abort_focus (n+1) ws ε domNest obsSlot n' hfr,
                  encodeICCGo_abort_focus n ws ε domNest obsSlot n' hfr]
            | unit => unfold encodeICCGo; simp only [hfr]
            | pair _ _ => unfold encodeICCGo; simp only [hfr]
            | lam _ => unfold encodeICCGo; simp only [hfr]
            | case _ _ _ => unfold encodeICCGo; simp only [hfr]
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
    ?moveStable ?leftNever ?abortFocus ?rightUnit ?rightProd_pair ?rightProd_foc
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
  case abortFocus =>
    intro Γ A ws ε domNest obsSlot n hfr
    have hpos := encodeFuel_pos ws (.abort (A := A) n)
    obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    refine ⟨.abort (.obs (sig := sig) obsSlot), ?_⟩
    simp only [hm]
    exact encodeICCGo_abort_focus fuel ws ε domNest obsSlot n hfr
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

theorem encodeReady_abort_focus {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (ws : List (PosEntry sig)) (domNest obsSlot : Nat)
    (n : NegNeu Γ .never) (hfr : forcedRule ws A = .focus) :
    EncodeReady ws ε domNest obsSlot (.abort (A := A) n) :=
  .abortFocus hfr

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

end Equality
end Gimbal
