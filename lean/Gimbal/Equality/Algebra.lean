/-
  Intrinsic renaming / substitution algebra (Milestone 8A).

  Core lemmas; binder cases for rename/subst identity are filled as proofs need them.
-/

import Gimbal.Equality.LambdaSyntax
import Gimbal.Equality.Focused

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Renaming algebra on `Tm` -/

/-- Composition of renamings. -/
def Rename.comp {Γ Δ Ε : Ctx sig}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) : Rename sig Γ Ε :=
  fun x => ρ (τ x)

theorem Rename.ext_id_apply {Γ : Ctx sig} {A B : Object sig.nBases}
    (x : Var (Γ ▻ A) B) :
    Rename.ext (Rename.id (Γ := Γ)) x = x := by
  cases x <;> rfl

theorem Rename.ext_comp_apply {Γ Δ Ε : Ctx sig} {A B : Object sig.nBases}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) (x : Var (Γ ▻ A) B) :
    Rename.ext (Rename.comp ρ τ) x =
      Rename.comp (Rename.ext ρ) (Rename.ext τ) x := by
  cases x <;> rfl

theorem Subst.exts_ids_apply {Γ : Ctx sig} {A B : Object sig.nBases}
    (x : Var (Γ ▻ A) B) :
    Subst.exts (Subst.ids (Γ := Γ)) x = Subst.ids x := by
  cases x <;> rfl

/-- Identity renaming on variables (pointwise). -/
theorem rename_id_var {Γ : Ctx sig} {A : Object sig.nBases} (x : Var Γ A) :
    rename (Rename.id (Γ := Γ)) (Tm.var x) = Tm.var x :=
  rfl

/-- Identity substitution on variables (pointwise). -/
theorem subst_ids_var {Γ : Ctx sig} {A : Object sig.nBases} (x : Var Γ A) :
    subst (Subst.ids (Γ := Γ)) (Tm.var x) = Tm.var x :=
  rfl

theorem weakenTerm_eq_rename {Γ : Ctx sig} {A B : Object sig.nBases}
    (t : Tm Γ B) :
    weakenTerm (A := A) t = rename Rename.weaken t :=
  rfl

theorem rename_comp_var {Γ Δ Ε : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) (x : Var Γ A) :
    rename ρ (rename τ (Tm.var x)) = rename (Rename.comp ρ τ) (Tm.var x) :=
  rfl

/-! ### Decidable structural equality (raw spines) -/

instance : DecidableEq RawNeu := inferInstance
instance : DecidableEq RawPos := inferInstance
instance : DecidableEq RawFocused := inferInstance

/-! ### Generator telescope -/

/-- `genVar` inhabits the generator arrow type. -/
example (sig : Signature) (q : Fin sig.nGens) :
    Var (genCtx sig) (genType sig q) :=
  genVar sig q

/-- Empty signature has empty generator context. -/
example : genCtx (sig := ⟨0, #[]⟩) = Ctx.empty := rfl

end Equality
end Gimbal
