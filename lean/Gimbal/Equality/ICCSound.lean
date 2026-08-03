/-
  Invertible commuting conversions are sound for the equational theory.

  Every rule of `ICCEq` is one of the laws proved in `TmEq`, so ICC-equal
  focused terms erase to `TmEq`-equal terms — hence to the same morphism.
  This is the half of the ICC bridge that the comparison procedure needs in
  order to conclude `DefEq` from a successful structural match.
-/

import Gimbal.Equality.ICC
import Gimbal.Equality.Preserve

namespace Gimbal
namespace Equality

variable {sig : Signature}

mutual
/-- ICC-equal invertible terms erase to equal terms. -/
theorem ICCEq.tmEq : {Γ : Ctx sig} → {A : Object sig.nBases} →
    {t u : InvTm Γ A} → ICCEq t u → TmEq t.erase u.erase
  | _, _, _, _, .refl _ => .refl _
  | _, _, _, _, .symm h => (ICCEq.tmEq h).symm
  | _, _, _, _, .trans h₁ h₂ => (ICCEq.tmEq h₁).trans (ICCEq.tmEq h₂)
  | _, _, _, _, .pair_cong h₁ h₂ => TmEq.pair (ICCEq.tmEq h₁) (ICCEq.tmEq h₂)
  | _, _, _, _, .lam_cong h => TmEq.lam (ICCEq.tmEq h)
  | _, _, _, _, .case_cong h₁ h₂ =>
      TmEq.case (.refl _) (ICCEq.tmEq h₁) (ICCEq.tmEq h₂)
  | _, _, _, _, .foc_cong h => ICCFocEq.tmEq h
  | _, _, _, _, .case_unit _ => TmEq.eta_unit _
  | _, _, _, _, .case_pair _ _ _ _ _ => TmEq.cc_case_pair _ _ _ _ _
  | _, _, _, _, .case_lam _ _ _ => by
      simp only [InvTm.erase, NegNeu.erase_weaken, InvTm.erase_rename]
      exact TmEq.cc_case_lam _ _ _
  | _, _, _, _, .case_case _ _ _ _ _ _ => by
      simp only [InvTm.erase, NegNeu.erase_weaken, InvTm.erase_rename]
      exact TmEq.cc_case_swap _ _ _ _ _ _
  | _, _, _, _, .abort_eq n _ => TmEq.of_never n.erase _ _
  | _, _, _, _, .coprod_eta _ => by
      simp only [InvTm.erase]
      exact (TmEq.case (.refl _) (tmEq_etaInl _ _) (tmEq_etaInr _ _)).trans
        (TmEq.eta_coprod _)

/-- ICC-equal focus terms erase to equal terms. -/
theorem ICCFocEq.tmEq : {Γ : Ctx sig} → {A : Object sig.nBases} →
    {f g : FocTm Γ A} → ICCFocEq f g → TmEq f.erase g.erase
  | _, _, _, _, .refl _ => .refl _
  | _, _, _, _, .symm h => (ICCFocEq.tmEq h).symm
  | _, _, _, _, .trans h₁ h₂ => (ICCFocEq.tmEq h₁).trans (ICCFocEq.tmEq h₂)
  | _, _, _, _, .letPos_cong h => TmEq.subst0_congr (ICCEq.tmEq h) (.refl _)
  | _, _, _, _, .pos_cong h => .of_eq (by rw [h])
  | _, _, _, _, .neg_cong h => .of_eq (by rw [h])
  | _, _, _, _, .sat_cong h => ICCEq.tmEq h
  | _, _, _, _, .sat_foc _ _ => .refl _
end

end Equality
end Gimbal
