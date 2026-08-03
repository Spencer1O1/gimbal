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
      (.unit (Γ := Γ)) = some .unit := by
  simp [encodeICCGo, forcedRule, peelUnit]

theorem encodeICC_unit_of_nilWorklist {Γ : Ctx sig} (ε : OriginEnv Γ)
    (hws : OriginEnv.posWorklist ε = []) :
    encodeICC ε (.unit (Γ := Γ)) = some .unit := by
  unfold encodeICC
  rw [hws]
  have hpos := encodeFuel_pos ([] : List (PosEntry sig)) (.unit (Γ := Γ))
  obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  simpa [hm] using encodeICCGo_unit_nil fuel ε 0 0

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

/-- `ICCEq.case_pair` preserves codes at every common fuel (Go level). -/
theorem encodeICCGo_case_pair_any {Γ : Ctx sig} {A B C D : Object sig.nBases}
    (fuel : Nat) (e : PosEntry sig) (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (x : Var Γ (.coprod A B))
    (t₁ : InvTm (Γ ▻ A) C) (t₂ : InvTm (Γ ▻ B) C)
    (u₁ : InvTm (Γ ▻ A) D) (u₂ : InvTm (Γ ▻ B) D)
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin) :
    encodeICCGo fuel (e :: ws) ε domNest obsSlot
        (.case (.var x) (.pair t₁ u₁) (.pair t₂ u₂)) =
      encodeICCGo fuel (e :: ws) ε domNest obsSlot
        (.pair (.case (.var x) t₁ t₂) (.case (.var x) u₁ u₂)) := by
  match fuel with
  | 0 => simp [encodeICCGo]
  | fuel + 1 => exact encodeICCGo_case_pair fuel e ws ε domNest obsSlot x t₁ t₂ u₁ u₂ hty hit

/-- Top-level `case_pair` packaging: see `encodeIccStep_case_pair` in `ICCTotal`
(after successful-result fuel mono + max-fuel lift). -/
theorem encodeICC_case_pair {Γ : Ctx sig} {A B C D : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (x : Var Γ (.coprod A B))
    (t₁ : InvTm (Γ ▻ A) C) (t₂ : InvTm (Γ ▻ B) C)
    (u₁ : InvTm (Γ ▻ A) D) (u₂ : InvTm (Γ ▻ B) D)
    (hws : OriginEnv.posWorklist ε = e :: ws)
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin) :
    encodeICCGo (encodeFuel (e :: ws)
        (.case (.var x) (.pair t₁ u₁) (.pair t₂ u₂)))
        (e :: ws) ε 0 0
        (.case (.var x) (.pair t₁ u₁) (.pair t₂ u₂)) =
      encodeICCGo (encodeFuel (e :: ws)
        (.case (.var x) (.pair t₁ u₁) (.pair t₂ u₂)))
        (e :: ws) ε 0 0
        (.pair (.case (.var x) t₁ t₂) (.case (.var x) u₁ u₂)) :=
  encodeICCGo_case_pair_any _ e ws ε 0 0 x t₁ t₂ u₁ u₂ hty hit

/-- `ICCEq.case_lam` preserves codes at every common fuel (Go level). -/
theorem encodeICCGo_case_lam_any {Γ : Ctx sig} {A B Arg Ret : Object sig.nBases}
    (fuel : Nat) (e : PosEntry sig) (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (x : Var Γ (.coprod A B))
    (t : InvTm (Γ ▻ A ▻ Arg) Ret) (u : InvTm (Γ ▻ B ▻ Arg) Ret)
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin) :
    encodeICCGo fuel (e :: ws) ε domNest obsSlot
        (.case (.var x) (.lam t) (.lam u)) =
      encodeICCGo fuel (e :: ws) ε domNest obsSlot
        (.lam (.case (NegNeu.weaken (B := Arg) (.var x))
          (InvTm.rename Rename.exchange t)
          (InvTm.rename Rename.exchange u))) := by
  match fuel with
  | 0 => simp [encodeICCGo]
  | fuel + 1 => exact encodeICCGo_case_lam fuel e ws ε domNest obsSlot x t u hty hit

/-- `ICCEq.case_case` at a successor fuel. -/
theorem encodeICCGo_case_case {Γ : Ctx sig} {A B C D E : Object sig.nBases}
    (fuel : Nat) (e : PosEntry sig) (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (xs : Var Γ (.coprod A B)) (xt : Var Γ (.coprod C D))
    (t₁ : InvTm (Γ ▻ A ▻ C) E) (t₂ : InvTm (Γ ▻ A ▻ D) E)
    (u₁ : InvTm (Γ ▻ B ▻ C) E) (u₂ : InvTm (Γ ▻ B ▻ D) E)
    (hty : e.ty = .coprod A B) (hit : ε xs = e.origin)
    (miss : (ε xt == e.origin) = false) :
    encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot
        (.case (.var xs)
          (.case (NegNeu.weaken (B := A) (.var xt)) t₁ t₂)
          (.case (NegNeu.weaken (B := B) (.var xt)) u₁ u₂)) =
      encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot
        (.case (.var xt)
          (.case (NegNeu.weaken (B := C) (.var xs))
            (InvTm.rename Rename.exchange t₁)
            (InvTm.rename Rename.exchange u₁))
          (.case (NegNeu.weaken (B := D) (.var xs))
            (InvTm.rename Rename.exchange t₂)
            (InvTm.rename Rename.exchange u₂))) := by
  have hforce := forcedRule_cons_coprod e ws hty E
  have hpeel := peelCaseOuter_case_case ε e.origin xs xt t₁ t₂ u₁ u₂ hit miss
  simp [encodeICCGo, hforce, hpeel.1, hpeel.2]

/-- `ICCEq.case_case` preserves codes at every common fuel (Go level). -/
theorem encodeICCGo_case_case_any {Γ : Ctx sig} {A B C D E : Object sig.nBases}
    (fuel : Nat) (e : PosEntry sig) (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (xs : Var Γ (.coprod A B)) (xt : Var Γ (.coprod C D))
    (t₁ : InvTm (Γ ▻ A ▻ C) E) (t₂ : InvTm (Γ ▻ A ▻ D) E)
    (u₁ : InvTm (Γ ▻ B ▻ C) E) (u₂ : InvTm (Γ ▻ B ▻ D) E)
    (hty : e.ty = .coprod A B) (hit : ε xs = e.origin)
    (miss : (ε xt == e.origin) = false) :
    encodeICCGo fuel (e :: ws) ε domNest obsSlot
        (.case (.var xs)
          (.case (NegNeu.weaken (B := A) (.var xt)) t₁ t₂)
          (.case (NegNeu.weaken (B := B) (.var xt)) u₁ u₂)) =
      encodeICCGo fuel (e :: ws) ε domNest obsSlot
        (.case (.var xt)
          (.case (NegNeu.weaken (B := C) (.var xs))
            (InvTm.rename Rename.exchange t₁)
            (InvTm.rename Rename.exchange u₁))
          (.case (NegNeu.weaken (B := D) (.var xs))
            (InvTm.rename Rename.exchange t₂)
            (InvTm.rename Rename.exchange u₂))) := by
  match fuel with
  | 0 => simp [encodeICCGo]
  | fuel + 1 =>
      exact encodeICCGo_case_case fuel e ws ε domNest obsSlot xs xt t₁ t₂ u₁ u₂ hty hit miss

/-! ### `case_unit` via left-η; `EncodeIccStep` packaging lives in `ICCTotal` -/

theorem peelCaseOuter_unit_none {Γ : Ctx sig} (ε : OriginEnv Γ) (o : Origin sig) :
    peelCaseOuter ε o (.unit (Γ := Γ)) = none := by
  unfold peelCaseOuter
  cases InvTm.size (.unit (Γ := Γ) : InvTm Γ .unit)
  · rfl
  · simp [peelCaseOuterGo]

/-!
`case_unit` left-η is implemented via `encodeLeftCoprodBranches` (same
continuation as a successful peel).
-/

theorem encodeICCGo_case_unit {Γ : Ctx sig} {A B : Object sig.nBases}
    (fuel : Nat) (e : PosEntry sig) (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (x : Var Γ (.coprod A B))
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin)
    (hfind : OriginEnv.find? ε e.origin = some ⟨.coprod A B, x⟩) :
    encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot
        (.case (.var x) .unit .unit) =
      encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot .unit := by
  have hforce := forcedRule_cons_coprod e ws hty (.unit : Object sig.nBases)
  have hpeelX := peelCaseOuter_case_var_hit ε e.origin x
    (.unit : InvTm (Γ ▻ A) .unit) (.unit) hit
  have hpeelU := peelCaseOuter_unit_none ε e.origin
  simp only [encodeICCGo, hforce, hpeelX, hpeelU, hfind, hit, beq_self_eq_true,
    ↓reduceDIte, ↓reduceIte, eq_rec_constant]

theorem encodeICCGo_case_unit_any {Γ : Ctx sig} {A B : Object sig.nBases}
    (fuel : Nat) (e : PosEntry sig) (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (x : Var Γ (.coprod A B))
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin)
    (hfind : OriginEnv.find? ε e.origin = some ⟨.coprod A B, x⟩) :
    encodeICCGo fuel (e :: ws) ε domNest obsSlot
        (.case (.var x) .unit .unit) =
      encodeICCGo fuel (e :: ws) ε domNest obsSlot .unit := by
  match fuel with
  | 0 => simp [encodeICCGo]
  | fuel + 1 =>
      exact encodeICCGo_case_unit fuel e ws ε domNest obsSlot x hty hit hfind

/-! ### Right-introduction unfolds (nil worklist) -/

theorem forcedRule_nil_prod (L R : Object sig.nBases) :
    forcedRule ([] : List (PosEntry sig)) (.prod L R) = .rightProd L R := rfl

theorem forcedRule_nil_exp (Arg Ret : Object sig.nBases) :
    forcedRule ([] : List (PosEntry sig)) (.exp Arg Ret) = .rightExp Arg Ret := rfl

theorem encodeICCGo_pair_nil {Γ : Ctx sig} {L R : Object sig.nBases}
    (fuel : Nat) (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (t : InvTm Γ L) (u : InvTm Γ R) :
    encodeICCGo (fuel + 1) ([] : List (PosEntry sig)) ε domNest obsSlot (.pair t u) =
      match encodeICCGo fuel ([] : List (PosEntry sig)) ε domNest obsSlot t,
            encodeICCGo fuel ([] : List (PosEntry sig)) ε domNest obsSlot u with
      | some c₁, some c₂ => some (.pair c₁ c₂)
      | _, _ => none := by
  simp [encodeICCGo, forcedRule_nil_prod, peelPair]
  rfl

theorem encodeICCGo_lam_nil {Γ : Ctx sig} {Arg Ret : Object sig.nBases}
    (fuel : Nat) (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (body : InvTm (Γ ▻ Arg) Ret) :
    encodeICCGo (fuel + 1) ([] : List (PosEntry sig)) ε domNest obsSlot (.lam body) =
      match encodeICCGo fuel
            (pushPos ([] : List (PosEntry sig)) (.dom (sig := sig) domNest) Arg)
            (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) domNest))
            (domNest + 1) obsSlot body with
      | some c => some (.lam c)
      | none => none := by
  simp [encodeICCGo, forcedRule_nil_exp, peelLam]
  rfl

/-! ### Congruence and remaining generators -/

theorem forcedRule_cons_never (e : PosEntry sig) (ws : List (PosEntry sig))
    (hty : e.ty = .never) (goal : Object sig.nBases) :
    forcedRule (e :: ws) goal = .leftNever e := by
  simp [forcedRule, hty]

/-- Under forced `leftNever`, every abort encodes to the forced origin. -/
theorem encodeICCGo_abort_leftNever {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (e : PosEntry sig) (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (n : NegNeu Γ .never) (hty : e.ty = .never) :
    encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot (.abort (A := A) n) =
      some (.abort e.origin) := by
  simp [encodeICCGo, forcedRule_cons_never e ws hty A]

theorem encodeICC_abort_leftNever {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (n : NegNeu Γ .never)
    (hws : OriginEnv.posWorklist ε = e :: ws) (hty : e.ty = .never) :
    encodeICC ε (.abort (A := A) n) = some (.abort e.origin) := by
  unfold encodeICC
  rw [hws]
  have hpos := encodeFuel_pos (e :: ws) (.abort (A := A) n)
  obtain ⟨fuel, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  simpa [hm] using encodeICCGo_abort_leftNever fuel e ws ε 0 0 n hty

/-- `abort_eq` as `EncodeIccStep` under forced `leftNever`. -/
theorem encodeIccStep_abort_eq {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (n m : NegNeu Γ .never)
    (hws : OriginEnv.posWorklist ε = e :: ws) (hty : e.ty = .never) :
    EncodeIccStep ε (.abort (A := A) n) (.abort (A := A) m) :=
  EncodeIccStep.of_option_eq ε <| by
    rw [encodeICC_abort_leftNever ε e ws n hws hty,
      encodeICC_abort_leftNever ε e ws m hws hty]

/-- Saturation metadata is erased by encode (`sat_cong` / `sat_foc`). -/
theorem encodeFocGo_sat {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (s : Schedule sig.nBases) (t : InvTm Γ A) :
    encodeFocGo (fuel + 1) ws ε domNest obsSlot (.sat (.mk s t)) =
      match encodeICCGo fuel ws ε domNest obsSlot t with
      | some c => some (.foc (.body c))
      | none => none := by
  rw [encodeFocGo]
  rfl

theorem encodeICCGo_foc_sat {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (s : Schedule sig.nBases) (t : InvTm Γ A)
    (hforce : forcedRule ws A = .focus) :
    encodeICCGo (fuel + 2) ws ε domNest obsSlot (.foc (.sat (.mk s t))) =
      match encodeICCGo fuel ws ε domNest obsSlot t with
      | some c => some (.foc (.body c))
      | none => none := by
  rw [encodeICCGo, hforce, encodeFocGo_sat]

/-- Right-product congruence on codes when both sides peel as pairs. -/
theorem encodeICCGo_pair_cong {Γ : Ctx sig} {L R : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat)
    {t₁ t₂ : InvTm Γ L} {u₁ u₂ : InvTm Γ R}
    (hforce : forcedRule ws (.prod L R) = .rightProd L R)
    (ht : encodeICCGo fuel ws ε domNest obsSlot t₁ =
      encodeICCGo fuel ws ε domNest obsSlot t₂)
    (hu : encodeICCGo fuel ws ε domNest obsSlot u₁ =
      encodeICCGo fuel ws ε domNest obsSlot u₂) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.pair t₁ u₁) =
      encodeICCGo (fuel + 1) ws ε domNest obsSlot (.pair t₂ u₂) := by
  simp [encodeICCGo, hforce, peelPair, ht, hu]

/-- Right-λ: Go-level congruence when bodies agree under the same weakened env. -/
theorem encodeICCGo_lam_cong {Γ : Ctx sig} {Arg Ret : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat)
    {t u : InvTm (Γ ▻ Arg) Ret}
    (hforce : forcedRule ws (.exp Arg Ret) = .rightExp Arg Ret)
    (hbody : encodeICCGo fuel (pushPos ws (.dom (sig := sig) domNest) Arg)
        (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) domNest))
        (domNest + 1) obsSlot t =
      encodeICCGo fuel (pushPos ws (.dom (sig := sig) domNest) Arg)
        (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) domNest))
        (domNest + 1) obsSlot u) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.lam t) =
      encodeICCGo (fuel + 1) ws ε domNest obsSlot (.lam u) := by
  simp [encodeICCGo, hforce, peelLam, hbody]

/-- `case_cong` at Go level under a forced outer coprod. -/
theorem encodeICCGo_case_cong {Γ : Ctx sig} {A B C : Object sig.nBases}
    (fuel : Nat) (e : PosEntry sig) (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat)
    (x : Var Γ (.coprod A B))
    (t₁ t₂ : InvTm (Γ ▻ A) C) (u₁ u₂ : InvTm (Γ ▻ B) C)
    (hty : e.ty = .coprod A B) (hit : ε x = e.origin)
    (ht : encodeICCGo fuel
        (pushPos ws (.split e.origin false) A)
        (OriginEnv.weaken (A := A) ε (.split e.origin false))
        domNest obsSlot t₁ =
      encodeICCGo fuel
        (pushPos ws (.split e.origin false) A)
        (OriginEnv.weaken (A := A) ε (.split e.origin false))
        domNest obsSlot t₂)
    (hu : encodeICCGo fuel
        (pushPos ws (.split e.origin true) B)
        (OriginEnv.weaken (A := B) ε (.split e.origin true))
        domNest obsSlot u₁ =
      encodeICCGo fuel
        (pushPos ws (.split e.origin true) B)
        (OriginEnv.weaken (A := B) ε (.split e.origin true))
        domNest obsSlot u₂) :
    encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot (.case (.var x) t₁ u₁) =
      encodeICCGo (fuel + 1) (e :: ws) ε domNest obsSlot (.case (.var x) t₂ u₂) := by
  have hforce := forcedRule_cons_coprod e ws hty C
  have hpeel1 := peelCaseOuter_case_var_hit ε e.origin x t₁ u₁ hit
  have hpeel2 := peelCaseOuter_case_var_hit ε e.origin x t₂ u₂ hit
  simp [encodeICCGo, hforce, hpeel1, hpeel2, encodeLeftCoprodBranches, List.tail_cons,
    ht, hu]

/-! ### Open obligations (design E remaining work)

Tracked as goal Props in `Completeness.lean`:

1. ~~`OriginCollisionFree` API~~ **Done** (`Origin.dom`, `obsSlot`/`domNest`)
2. ~~Peel soundness (`peelCaseOuter_icc`)~~ **Done**
3. `EncodeIccInvariant` (`ValidEncodeFragment` → `EncodeIccStep`) — commute
   rules packaged; `case_unit` left-η; `abort_eq` under `leftNever`; sat erase
   and Go-level pair/lam/case congruence landed; fuel mono / top-level cong /
   `EncodeIccStep` packaging without `hdom` landed; full `ofHyps` induction open.
4. `EncodeTotal` — `EncodeReady` ⇒ encodable proved (`encodeReady_go_some`);
   `ValidEncodeFragment` ⇒ `EncodeReady` still open (`EncodeTotal_of_ready`).
5. `ReferenceCompareTotal` + iff — erase `2048` from decidability
6. Wire code equality into the total `referenceCompare`; resume 8G
-/

end Equality
end Gimbal
