/-
  Canonical-form invariant for the ICC canonicalizer (Milestone 8F).

  A term is canonical when a further pass of `canonicalizeInv` would be the
  identity. For `case` nodes that is recorded as the fixpoint equation
  `caseCommute n t u = .case n t u`, so the redex conditions of the rewriter
  do not have to be re-derived structurally.
-/

import Gimbal.Equality.ICCWell
import Gimbal.Equality.ICCCanon

namespace Gimbal
namespace Equality

variable {sig : Signature}

mutual
/-- An invertible term that is a fixed point of the canonicalizer. -/
inductive CanonInv : {Γ : Ctx sig} → {A : Object sig.nBases} → InvTm Γ A → Prop where
  | unit {Γ} : CanonInv (.unit (Γ := Γ))
  | pair {Γ A B} {t : InvTm Γ A} {u : InvTm Γ B} :
      CanonInv t → CanonInv u → CanonInv (.pair t u)
  | lam {Γ A B} {t : InvTm (Γ ▻ A) B} :
      CanonInv t → CanonInv (.lam t)
  | abort {Γ A} (n : NegNeu Γ .never) : CanonInv (.abort (A := A) n)
  | case {Γ A B C} {n : NegNeu Γ (.coprod A B)}
      {t : InvTm (Γ ▻ A) C} {u : InvTm (Γ ▻ B) C} :
      CanonInv t → CanonInv u →
      caseCommute n t u = .case n t u →
      CanonInv (.case n t u)
  | foc {Γ A} {f : FocTm Γ A} :
      CanonFoc f → CanonInv (.foc f)

/-- A focused term that is a fixed point of the canonicalizer. -/
inductive CanonFoc : {Γ : Ctx sig} → {A : Object sig.nBases} → FocTm Γ A → Prop where
  | pos {Γ A} (p : PosIntro Γ A) : CanonFoc (.pos p)
  | neg {Γ A} (n : NegElim Γ A) : CanonFoc (.neg n)
  | letPos {Γ P A} {n : NegNeu Γ P} {t : InvTm (Γ ▻ P) A} :
      CanonInv t → CanonFoc (.letPos n t)
  /-- Saturation metadata is erased by the canonicalizer, so a canonical
  focused term never wraps a focus; the body itself must be canonical. -/
  | sat {Γ A} {t : InvTm Γ A} :
      (∀ f : FocTm Γ A, t ≠ .foc f) → CanonInv t →
      CanonFoc (.sat (.mk ⟨#[]⟩ t))
end

mutual
/-- `canonicalizeInv` is the identity on a canonical invertible term. -/
theorem canonicalizeInv_eq_of_canon {Γ : Ctx sig} {A : Object sig.nBases} :
    ∀ {t : InvTm Γ A}, CanonInv t → canonicalizeInv t = t
  | .unit, .unit => rfl
  | .pair _ _, .pair ht hu => by
      simp [canonicalizeInv, canonicalizeInv_eq_of_canon ht, canonicalizeInv_eq_of_canon hu]
  | .lam _, .lam ht => by
      simp [canonicalizeInv, canonicalizeInv_eq_of_canon ht]
  | .abort _, .abort _ => rfl
  | .case _ _ _, .case ht hu hfix => by
      simp [canonicalizeInv, canonicalizeInv_eq_of_canon ht,
        canonicalizeInv_eq_of_canon hu, hfix]
  | .foc _, .foc hf => by
      simp [canonicalizeInv, canonicalizeFoc_eq_of_canon hf]

/-- `canonicalizeFoc` is the identity on a canonical focused term. -/
theorem canonicalizeFoc_eq_of_canon {Γ : Ctx sig} {A : Object sig.nBases} :
    ∀ {f : FocTm Γ A}, CanonFoc f → canonicalizeFoc f = f
  | .pos _, .pos _ => rfl
  | .neg _, .neg _ => rfl
  | .letPos _ _, .letPos ht => by
      simp [canonicalizeFoc, canonicalizeInv_eq_of_canon ht]
  | .sat (.mk _ _), .sat hnf ht => by
      have h := canonicalizeInv_eq_of_canon ht
      rw [canonicalizeFoc, h]
      rename_i t
      cases t with
      | foc f => exact absurd rfl (hnf f)
      | unit => rfl
      | pair _ _ => rfl
      | lam _ => rfl
      | case _ _ _ => rfl
      | abort _ => rfl
end

/-- Idempotence once the output is known to be canonical. -/
theorem canonicalize_idempotent_of_canon {Γ : Ctx sig} {A : Object sig.nBases}
    (t : InvTm Γ A) (h : CanonInv (canonicalize t)) :
    canonicalize (canonicalize t) = canonicalize t :=
  canonicalizeInv_eq_of_canon h

/-- `mkCase` that did not contract η is the plain `case` constructor. -/
theorem mkCase_eq_case_of_none {Γ : Ctx sig} {A B C : Object sig.nBases}
    (n : NegNeu Γ (.coprod A B))
    (t : InvTm (Γ ▻ A) C) (u : InvTm (Γ ▻ B) C)
    (h : tryCoprodEta n t u = none) :
    mkCase n t u = .case n t u := by
  simp [mkCase, h]

/-- A successful η contraction is always a focused scrutinee, never a `case`. -/
theorem tryCoprodEta_eq_foc {Γ : Ctx sig} {A B C : Object sig.nBases}
    (n : NegNeu Γ (.coprod A B))
    (t : InvTm (Γ ▻ A) C) (u : InvTm (Γ ▻ B) C)
    {r : InvTm Γ C} (h : tryCoprodEta n t u = some r) :
    ∃ (f : FocTm Γ C), r = .foc f := by
  unfold tryCoprodEta at h
  split at h
  · rename_i hC
    subst hC
    split at h
    · cases h
      exact ⟨_, rfl⟩
    · cases h
  · cases h

/-- If `mkCase` produced a `case` node, η did not fire. -/
theorem tryCoprodEta_none_of_mkCase_case {Γ : Ctx sig} {A B C : Object sig.nBases}
    {n : NegNeu Γ (.coprod A B)}
    {t : InvTm (Γ ▻ A) C} {u : InvTm (Γ ▻ B) C}
    {n' : NegNeu Γ (.coprod A B)}
    {t' : InvTm (Γ ▻ A) C} {u' : InvTm (Γ ▻ B) C}
    (h : mkCase n t u = .case n' t' u') :
    tryCoprodEta n t u = none ∧ n' = n ∧ t' = t ∧ u' = u := by
  cases hEta : tryCoprodEta n t u with
  | none =>
      simp only [mkCase, hEta] at h
      cases h
      exact ⟨rfl, rfl, rfl, rfl⟩
  | some r =>
      simp only [mkCase, hEta] at h
      obtain ⟨f, rfl⟩ := tryCoprodEta_eq_foc n t u hEta
      cases h

end Equality
end Gimbal
