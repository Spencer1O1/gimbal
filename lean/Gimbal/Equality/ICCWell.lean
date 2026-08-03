/-
  ICC canonicalization stays inside the focused fragment.

  The canonicalizer rearranges a term without inventing syntax: it commutes an
  invertible `case` outward, contracts a coproduct η-expansion into its
  scrutinee, and drops saturation metadata. Each of those keeps phase legality,
  so a well-focused input has a well-focused canonical form. Together with
  `wellInv_focusTm` and `wellInv_applyPairObs` this covers every stage the
  reference comparator puts a term through.
-/

import Gimbal.Equality.ICCCanon

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- Unweakening a legal spine leaves a legal spine. -/
theorem wellNeg_of_unweaken? {Γ : Ctx sig} {B : Object sig.nBases} :
    ∀ {A : Object sig.nBases} {n : NegNeu (Γ ▻ B) A} {m : NegNeu Γ A},
      NegNeu.unweaken? n = some m → WellNeg n → WellNeg m
  | _, .var .here, _, h, _ => by simp [NegNeu.unweaken?] at h
  | _, .var (.there _), _, h, _ => by
      simp only [NegNeu.unweaken?, Option.some.injEq] at h
      subst h
      exact .var
  | _, .app _ _, _, h, _ => by simp [NegNeu.unweaken?] at h
  | _, .fst n, m, h, hw => by
      cases hn : NegNeu.unweaken? n with
      | none => rw [NegNeu.unweaken?, hn] at h; simp at h
      | some m' =>
          rw [NegNeu.unweaken?, hn] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          cases hw with | fst hw => exact .fst (wellNeg_of_unweaken? hn hw)
  | _, .snd n, m, h, hw => by
      cases hn : NegNeu.unweaken? n with
      | none => rw [NegNeu.unweaken?, hn] at h; simp at h
      | some m' =>
          rw [NegNeu.unweaken?, hn] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          cases hw with | snd hw => exact .snd (wellNeg_of_unweaken? hn hw)

/-- Commuting a `case` outward preserves phase legality. -/
theorem wellInv_caseCommute : ∀ {Γ : Ctx sig} {A B C : Object sig.nBases}
    (n : NegNeu Γ (.coprod A B)) (t : InvTm (Γ ▻ A) C) (u : InvTm (Γ ▻ B) C),
    WellNeg n → WellInv t → WellInv u → WellInv (caseCommute n t u) := by
  intro Γ A B C n t u
  fun_induction caseCommute n t u <;> intro hn ht hu
  case case3 =>
      rename_i ih2 ih1
      cases ht with | pair h₁ h₂ =>
      cases hu with | pair h₃ h₄ =>
      exact .pair (ih2 hn h₁ h₃) (ih1 hn h₂ h₄)
  case case5 =>
      rename_i ih1
      cases ht with | lam h₁ =>
      cases hu with | lam h₂ =>
      exact .lam (ih1 (wellNeg_rename _ hn) (wellInv_rename _ h₁) (wellInv_rename _ h₂))
  case case7 =>
      rename_i ih2 ih1
      cases ht with | case hm h₁ h₂ =>
      cases hu with | case _ h₃ h₄ =>
      exact .case (wellNeg_of_unweaken? (by assumption) hm)
        (ih2 (wellNeg_rename _ hn) (wellInv_rename _ h₁) (wellInv_rename _ h₃))
        (ih1 (wellNeg_rename _ hn) (wellInv_rename _ h₂) (wellInv_rename _ h₄))
  all_goals first
    | exact .unit
    | exact .case hn ht hu

/-- Contracting a coproduct η-expansion preserves phase legality. -/
theorem wellInv_tryCoprodEta {Γ : Ctx sig} {A B C : Object sig.nBases}
    (n : NegNeu Γ (.coprod A B)) (t : InvTm (Γ ▻ A) C) (u : InvTm (Γ ▻ B) C)
    (hn : WellNeg n) {r : InvTm Γ C} (h : tryCoprodEta n t u = some r) :
    WellInv r := by
  rw [tryCoprodEta] at h
  split at h
  · rename_i hC
    subst hC
    split at h
    · cases h
      exact .foc (.pos rfl (.neu rfl hn))
    · exact absurd h (by simp)
  · exact absurd h (by simp)

mutual
/-- Canonicalization preserves phase legality. -/
theorem wellInv_canonicalizeInv {Γ : Ctx sig} {A : Object sig.nBases} :
    ∀ {t : InvTm Γ A}, WellInv t → WellInv (canonicalizeInv t)
  | .unit, _ => .unit
  | .pair _ _, .pair h₁ h₂ =>
      .pair (wellInv_canonicalizeInv h₁) (wellInv_canonicalizeInv h₂)
  | .lam _, .lam h => .lam (wellInv_canonicalizeInv h)
  | .abort _, .abort hn => .abort hn
  | .foc _, .foc hf => .foc (wellFoc_canonicalizeFoc hf)
  | .case n _ _, .case hn h₁ h₂ => by
      rw [canonicalizeInv]
      split
      · exact wellInv_tryCoprodEta n _ _ hn (by assumption)
      · exact wellInv_caseCommute n _ _ hn
          (wellInv_canonicalizeInv h₁) (wellInv_canonicalizeInv h₂)

theorem wellFoc_canonicalizeFoc {Γ : Ctx sig} {A : Object sig.nBases} :
    ∀ {f : FocTm Γ A}, WellFoc f → WellFoc (canonicalizeFoc f)
  | .pos _, h => h
  | .neg _, h => h
  | .letPos _ _, .letPos hpol hn ht =>
      .letPos hpol hn (wellInv_canonicalizeInv ht)
  | .sat (.mk _ _), .sat ht => by
      have ih := wellInv_canonicalizeInv ht
      rw [canonicalizeFoc]
      split
      · rename_i heq
        rw [heq] at ih
        cases ih with | foc hf => exact hf
      · exact .sat ih
end

/-- The canonical form of a well-focused term is well focused. -/
theorem wellInv_canonicalize {Γ : Ctx sig} {A : Object sig.nBases}
    {t : InvTm Γ A} (h : WellInv t) : WellInv (canonicalize t) :=
  wellInv_canonicalizeInv h

end Equality
end Gimbal
