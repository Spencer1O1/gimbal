/-
  Totality of ordered-phase encoding on the valid fragment (Milestone 8F/E).

  `EncodeTotal` asks for a concrete code witness on every `ValidEncodeFragment`
  term under `OriginEnv.ofHyps`. Fuel monotonicity for the full mutual encoder
  and measure adequacy on every recursive path remain the path to discharging
  that Prop.
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

/-! ### Fuel monotonicity (closed + compositional layers) -/

theorem encodeFocGo_le_pos {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel fuel' : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (p : PosNeu Γ A) (c : ICCCode Γ A)
    (_hle : fuel ≤ fuel')
    (h : encodeFocGo fuel ws ε domNest obsSlot (.pos (.done p)) = some c) :
    encodeFocGo fuel' ws ε domNest obsSlot (.pos (.done p)) = some c := by
  simpa [encodeFocGo] using h

theorem encodeFocGo_le_neg {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel fuel' : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (n : NegNeu Γ A) (c : ICCCode Γ A)
    (_hle : fuel ≤ fuel')
    (h : encodeFocGo fuel ws ε domNest obsSlot (.neg (.done n)) = some c) :
    encodeFocGo fuel' ws ε domNest obsSlot (.neg (.done n)) = some c := by
  simpa [encodeFocGo] using h

/-- Forced `leftNever` abort succeeds at every larger fuel. -/
theorem encodeICCGo_le_leftNever {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel₁ fuel₂ : Nat) (e : PosEntry sig) (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat) (n : NegNeu Γ .never)
    (hty : e.ty = .never) (hle : fuel₁ ≤ fuel₂) {c : ICCCode Γ A}
    (h : encodeICCGo fuel₁ (e :: ws) ε domNest obsSlot (.abort (A := A) n) = some c) :
    encodeICCGo fuel₂ (e :: ws) ε domNest obsSlot (.abort (A := A) n) = some c := by
  cases fuel₁ with
  | zero => simp [encodeICCGo] at h
  | succ fuel₁ =>
      have hc : c = .abort e.origin := by
        simpa [encodeICCGo_abort_leftNever fuel₁ e ws ε domNest obsSlot n hty] using h.symm
      subst c
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      subst fuel₂
      have : fuel₁ + 1 + k = fuel₁ + k + 1 := by omega
      rw [this]
      exact encodeICCGo_abort_leftNever (fuel₁ + k) e ws ε domNest obsSlot n hty

/-- Nil-worklist right-unit succeeds at every larger fuel. -/
theorem encodeICCGo_le_rightUnit {Γ : Ctx sig}
    (fuel₁ fuel₂ : Nat) (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (hle : fuel₁ ≤ fuel₂) {c : ICCCode Γ .unit}
    (h : encodeICCGo fuel₁ ([] : List (PosEntry sig)) ε domNest obsSlot
      (.unit (Γ := Γ)) = some c) :
    encodeICCGo fuel₂ ([] : List (PosEntry sig)) ε domNest obsSlot
      (.unit (Γ := Γ)) = some c := by
  cases fuel₁ with
  | zero => simp [encodeICCGo] at h
  | succ fuel₁ =>
      have hc : c = .unit := by
        simpa [encodeICCGo_unit_nil fuel₁ ε domNest obsSlot] using h.symm
      subst c
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      subst fuel₂
      have : fuel₁ + 1 + k = fuel₁ + k + 1 := by omega
      rw [this]
      exact encodeICCGo_unit_nil (fuel₁ + k) ε domNest obsSlot

/-- Focused positive residue succeeds at every larger outer fuel. -/
theorem encodeICCGo_le_focus_pos {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel₁ fuel₂ : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (p : PosNeu Γ A)
    (hforce : forcedRule ws A = .focus) (hle : fuel₁ ≤ fuel₂) {c : ICCCode Γ A}
    (h : encodeICCGo fuel₁ ws ε domNest obsSlot (.foc (.pos (.done p))) = some c) :
    encodeICCGo fuel₂ ws ε domNest obsSlot (.foc (.pos (.done p))) = some c := by
  cases fuel₁ with
  | zero => simp [encodeICCGo] at h
  | succ fuel₁ =>
      have hc : c = .foc (.pos p) := by
        simpa [encodeICCGo_foc_pos fuel₁ ws ε domNest obsSlot p hforce] using h.symm
      subst c
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      subst fuel₂
      have : fuel₁ + 1 + k = fuel₁ + k + 1 := by omega
      rw [this]
      exact encodeICCGo_foc_pos (fuel₁ + k) ws ε domNest obsSlot p hforce

/-- Focused negative residue succeeds at every larger outer fuel. -/
theorem encodeICCGo_le_focus_neg {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel₁ fuel₂ : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (n : NegNeu Γ A)
    (hforce : forcedRule ws A = .focus) (hle : fuel₁ ≤ fuel₂) {c : ICCCode Γ A}
    (h : encodeICCGo fuel₁ ws ε domNest obsSlot (.foc (.neg (.done n))) = some c) :
    encodeICCGo fuel₂ ws ε domNest obsSlot (.foc (.neg (.done n))) = some c := by
  cases fuel₁ with
  | zero => simp [encodeICCGo] at h
  | succ fuel₁ =>
      have hc : c = .foc (.neg n) := by
        simpa [encodeICCGo_foc_neg fuel₁ ws ε domNest obsSlot n hforce] using h.symm
      subst c
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      subst fuel₂
      have : fuel₁ + 1 + k = fuel₁ + k + 1 := by omega
      rw [this]
      exact encodeICCGo_foc_neg (fuel₁ + k) ws ε domNest obsSlot n hforce

/--
One `moveStable` layer: compositional fuel mono once the recursive call is
stable. Stated as an implication chain to avoid unfolding `encodeICCGo` under
an `OriginEnv` (dependent function — broad `simp` hits `function expected ε`).
-/
theorem encodeICCGo_le_moveStable {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel₁ fuel₂ : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (t : InvTm Γ A) (_e : PosEntry sig)
    (_hforce : forcedRule ws A = .moveStable _e) {c : ICCCode Γ A}
    (hunfold₁ :
      encodeICCGo (fuel₁ + 1) ws ε domNest obsSlot t =
        encodeICCGo fuel₁ ws.tail ε domNest obsSlot t)
    (hunfold₂ :
      encodeICCGo (fuel₂ + 1) ws ε domNest obsSlot t =
        encodeICCGo fuel₂ ws.tail ε domNest obsSlot t)
    (ih : encodeICCGo fuel₁ ws.tail ε domNest obsSlot t = some c →
      encodeICCGo fuel₂ ws.tail ε domNest obsSlot t = some c)
    (h : encodeICCGo (fuel₁ + 1) ws ε domNest obsSlot t = some c) :
    encodeICCGo (fuel₂ + 1) ws ε domNest obsSlot t = some c := by
  rw [hunfold₁] at h
  rw [hunfold₂]
  exact ih h

/--
One right-product layer preserves fuel monotonicity when both component
recursive calls do.
-/
theorem encodeICCGo_le_rightProd_pair {Γ : Ctx sig} {L R : Object sig.nBases}
    (fuel₁ fuel₂ : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (t : InvTm Γ L) (u : InvTm Γ R)
    (hforce : forcedRule ws (.prod L R) = .rightProd L R)
    (ht : ∀ c, encodeICCGo fuel₁ ws ε domNest obsSlot t = some c →
      encodeICCGo fuel₂ ws ε domNest obsSlot t = some c)
    (hu : ∀ c, encodeICCGo fuel₁ ws ε domNest obsSlot u = some c →
      encodeICCGo fuel₂ ws ε domNest obsSlot u = some c)
    {c : ICCCode Γ (.prod L R)}
    (h : encodeICCGo (fuel₁ + 1) ws ε domNest obsSlot (.pair t u) = some c) :
    encodeICCGo (fuel₂ + 1) ws ε domNest obsSlot (.pair t u) = some c := by
  rw [encodeICCGo_pair_rightProd fuel₁ ws ε domNest obsSlot t u hforce] at h
  rw [encodeICCGo_pair_rightProd fuel₂ ws ε domNest obsSlot t u hforce]
  split at h
  next c₁ c₂ hc₁ hc₂ =>
    cases h
    rw [ht c₁ hc₁, hu c₂ hc₂]
  all_goals simp_all

/--
Full mutual fuel monotonicity: successful `encodeICCGo` is stable under
increasing fuel. Closed cases and compositional layers above; remaining
recursive rules (`leftCoprod`, `rightExp`, `letPos`, `sat`) join the same
pattern once their IHs are available.
-/
def EncodeFuelMonoGoal : Prop :=
  ∀ {Γ : Ctx sig} {A : Object sig.nBases} (fuel fuel' : Nat)
    (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (t : InvTm Γ A) (c : ICCCode Γ A),
    fuel ≤ fuel' →
      encodeICCGo fuel ws ε domNest obsSlot t = some c →
        encodeICCGo fuel' ws ε domNest obsSlot t = some c

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

end Equality
end Gimbal
