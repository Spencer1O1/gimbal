/-
  The ICC canonicalizer stays inside the ICC class.

  `canonicalize` rewrites with exactly the rules of `ICCEq`: it commutes a
  `case` past the invertible introductions, contracts a coproduct η-expansion,
  and drops saturation metadata. Proving that gives, via `ICCEq.tmEq`,
  soundness of the canonicalizer for the equational theory — a successful
  structural comparison of canonical forms really does mean equal morphisms.
-/

import Gimbal.Equality.ICCSound

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Unweakening is inverse to weakening -/

theorem NegNeu.eq_weaken_of_unweaken? {Γ : Ctx sig} {B : Object sig.nBases} :
    ∀ {A : Object sig.nBases} (n : NegNeu (Γ ▻ B) A) (m : NegNeu Γ A),
      NegNeu.unweaken? n = some m → n = NegNeu.weaken m
  | _, .var .here, _, h => by simp [NegNeu.unweaken?] at h
  | _, .var (.there _), _, h => by
      simp only [NegNeu.unweaken?, Option.some.injEq] at h
      subst h
      rfl
  | _, .app _ _, _, h => by simp [NegNeu.unweaken?] at h
  | _, .fst n, m, h => by
      cases hn : NegNeu.unweaken? n with
      | none => rw [NegNeu.unweaken?, hn] at h; simp at h
      | some m' =>
          rw [NegNeu.unweaken?, hn] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          rw [NegNeu.eq_weaken_of_unweaken? n m' hn]
          rfl
  | _, .snd n, m, h => by
      cases hn : NegNeu.unweaken? n with
      | none => rw [NegNeu.unweaken?, hn] at h; simp at h
      | some m' =>
          rw [NegNeu.unweaken?, hn] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          rw [NegNeu.eq_weaken_of_unweaken? n m' hn]
          rfl

/-! ### Each rewriting step is an ICC step -/

/-- Commuting a `case` outward is an ICC conversion. -/
theorem caseCommute_icc {Γ : Ctx sig} {A B C : Object sig.nBases}
    (n : NegNeu Γ (.coprod A B))
    (t : InvTm (Γ ▻ A) C) (u : InvTm (Γ ▻ B) C) :
    ICCEq (caseCommute n t u) (.case n t u) := by
  fun_induction caseCommute n t u
  case case1 => exact .symm (.case_unit _)
  case case3 =>
      rename_i ih2 ih1
      exact .trans (.pair_cong ih2 ih1) (.symm (.case_pair _ _ _ _ _))
  case case5 =>
      rename_i ih1
      exact .trans (.lam_cong ih1) (.symm (.case_lam _ _ _))
  case case7 =>
      rename_i hn₂ _t₁ _t₂' _u₁ _u₂' n₁ m₁ hn₁ hbeq ih2 ih1
      have h₁ := NegNeu.eq_weaken_of_unweaken? n₁ m₁ hn₁
      have h₂ := NegNeu.eq_weaken_of_unweaken? _ _ hn₂
      rw [Bool.and_eq_true] at hbeq
      obtain ⟨_, hm⟩ := NegNeu.eq_of_beq _ _ hbeq.1
      cases eq_of_heq hm
      subst h₁
      subst h₂
      exact .trans (.case_cong ih2 ih1) (.symm (.case_case _ _ _ _ _ _))
  all_goals exact .refl _

/-- Contracting a coproduct η-expansion is an ICC conversion. -/
theorem tryCoprodEta_icc {Γ : Ctx sig} {A B C : Object sig.nBases}
    (n : NegNeu Γ (.coprod A B)) (t : InvTm (Γ ▻ A) C) (u : InvTm (Γ ▻ B) C)
    {r : InvTm Γ C} (h : tryCoprodEta n t u = some r) :
    ICCEq r (.case n t u) := by
  unfold tryCoprodEta at h
  split at h
  · rename_i hC
    subst hC
    split at h
    · rename_i hb
      simp only [Bool.and_eq_true] at hb
      rw [InvTm.eq_of_beq _ _ hb.1, InvTm.eq_of_beq _ _ hb.2]
      cases h
      exact .symm (.coprod_eta n)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ### Soundness of the canonicalizer -/

mutual
/-- Canonicalization stays inside the ICC class. -/
theorem canonicalizeInv_icc {Γ : Ctx sig} {A : Object sig.nBases} :
    (t : InvTm Γ A) → ICCEq (canonicalizeInv t) t
  | .unit => .refl _
  | .pair t u => .pair_cong (canonicalizeInv_icc t) (canonicalizeInv_icc u)
  | .lam t => .lam_cong (canonicalizeInv_icc t)
  | .abort _ => .refl _
  | .foc f => .foc_cong (canonicalizeFoc_icc f)
  | .case n t u => by
      have hcong : ICCEq (.case n (canonicalizeInv t) (canonicalizeInv u))
          (.case n t u) :=
        .case_cong (canonicalizeInv_icc t) (canonicalizeInv_icc u)
      rw [canonicalizeInv]
      split
      · rename_i _r heq
        exact .trans (tryCoprodEta_icc n _ _ heq) hcong
      · exact .trans (caseCommute_icc n _ _) hcong

theorem canonicalizeFoc_icc {Γ : Ctx sig} {A : Object sig.nBases} :
    (f : FocTm Γ A) → ICCFocEq (canonicalizeFoc f) f
  | .pos _ => .refl _
  | .neg _ => .refl _
  | .letPos _ t => .letPos_cong (canonicalizeInv_icc t)
  | .sat (.mk s t) => by
      have ih := canonicalizeInv_icc t
      rw [canonicalizeFoc]
      split
      · rename_i f heq
        rw [heq] at ih
        exact .symm (.trans (.sat_cong ih.symm) (.sat_foc s f))
      · exact .sat_cong ih
end

theorem canonicalize_icc {Γ : Ctx sig} {A : Object sig.nBases} (t : InvTm Γ A) :
    ICCEq (canonicalize t) t :=
  canonicalizeInv_icc t

/-- The canonicalizer preserves meaning. -/
theorem tmEq_canonicalize {Γ : Ctx sig} {A : Object sig.nBases} (t : InvTm Γ A) :
    TmEq (canonicalize t).erase t.erase :=
  (canonicalize_icc t).tmEq

end Equality
end Gimbal
