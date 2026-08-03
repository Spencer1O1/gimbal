/-
  Intrinsic renaming / substitution algebra (Milestone 8A).
-/

import Gimbal.Equality.LambdaSyntax
import Gimbal.Equality.Focused

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Renaming -/

def Rename.comp {Γ Δ Ε : Ctx sig}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) : Rename sig Γ Ε :=
  fun {A} (x : Var Γ A) => ρ (τ x)

@[simp] theorem Rename.ext_id_apply {Γ : Ctx sig} {A B : Object sig.nBases}
    (x : Var (Γ ▻ A) B) :
    Rename.ext (Rename.id (Γ := Γ)) x = x := by
  cases x <;> rfl

@[simp] theorem Rename.ext_comp_apply {Γ Δ Ε : Ctx sig} {A B : Object sig.nBases}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) (x : Var (Γ ▻ A) B) :
    Rename.ext (Rename.comp ρ τ) x =
      Rename.comp (Rename.ext ρ) (Rename.ext τ) x := by
  cases x <;> rfl

@[simp] theorem Subst.exts_ids_apply {Γ : Ctx sig} {A B : Object sig.nBases}
    (x : Var (Γ ▻ A) B) :
    Subst.exts (Subst.ids (Γ := Γ)) x = Subst.ids x := by
  cases x <;> rfl

private theorem rename_ext_pointwise {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ τ : Rename sig Γ Δ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B), ρ x = τ x)
    {B : Object sig.nBases} (x : Var (Γ ▻ A) B) :
    Rename.ext ρ x = Rename.ext τ x := by
  cases x with
  | here => rfl
  | there y => exact congrArg Var.there (h y)

/-- Pointwise-equal renamings act the same on terms. -/
theorem rename_eq_of_pointwise {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ τ : Rename sig Γ Δ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B), ρ x = τ x)
    (t : Tm Γ A) : rename ρ t = rename τ t := by
  revert Δ ρ τ h
  induction t with
  | var x =>
      intro Δ ρ τ h
      exact congrArg Tm.var (h x)
  | unit =>
      intro Δ ρ τ h; rfl
  | abort t ih =>
      intro Δ ρ τ h
      change Tm.abort (rename ρ t) = Tm.abort (rename τ t)
      rw [ih h]
  | pair t u iht ihu =>
      intro Δ ρ τ h
      change Tm.pair (rename ρ t) (rename ρ u) = Tm.pair (rename τ t) (rename τ u)
      rw [iht h, ihu h]
  | fst t ih =>
      intro Δ ρ τ h
      change Tm.fst (rename ρ t) = Tm.fst (rename τ t); rw [ih h]
  | snd t ih =>
      intro Δ ρ τ h
      change Tm.snd (rename ρ t) = Tm.snd (rename τ t); rw [ih h]
  | inl t ih =>
      intro Δ ρ τ h
      change Tm.inl (rename ρ t) = Tm.inl (rename τ t); rw [ih h]
  | inr t ih =>
      intro Δ ρ τ h
      change Tm.inr (rename ρ t) = Tm.inr (rename τ t); rw [ih h]
  | case s t u ihs iht ihu =>
      intro Δ ρ τ h
      change Tm.case (rename ρ s) (rename (Rename.ext ρ) t) (rename (Rename.ext ρ) u) =
        Tm.case (rename τ s) (rename (Rename.ext τ) t) (rename (Rename.ext τ) u)
      rw [ihs h, iht (rename_ext_pointwise h), ihu (rename_ext_pointwise h)]
  | lam t ih =>
      intro Δ ρ τ h
      change Tm.lam (rename (Rename.ext ρ) t) = Tm.lam (rename (Rename.ext τ) t)
      rw [ih (rename_ext_pointwise h)]
  | app t u iht ihu =>
      intro Δ ρ τ h
      change Tm.app (rename ρ t) (rename ρ u) = Tm.app (rename τ t) (rename τ u)
      rw [iht h, ihu h]

@[simp] theorem rename_id {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) :
    rename (Rename.id (Γ := Γ)) t = t := by
  induction t with
  | var | unit => rfl
  | abort t ih => simp [rename, ih]
  | pair t u iht ihu => simp [rename, iht, ihu]
  | fst t ih | snd t ih | inl t ih | inr t ih => simp [rename, ih]
  | case s t u ihs iht ihu =>
      change Tm.case (rename Rename.id s)
        (rename (Rename.ext Rename.id) t)
        (rename (Rename.ext Rename.id) u) = Tm.case s t u
      rw [ihs,
        (rename_eq_of_pointwise Rename.ext_id_apply t).trans iht,
        (rename_eq_of_pointwise Rename.ext_id_apply u).trans ihu]
  | lam t ih =>
      change Tm.lam (rename (Rename.ext Rename.id) t) = Tm.lam t
      rw [(rename_eq_of_pointwise Rename.ext_id_apply t).trans ih]
  | app t u iht ihu => simp [rename, iht, ihu]

theorem rename_comp {Γ Δ Ε : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) (t : Tm Γ A) :
    rename ρ (rename τ t) = rename (Rename.comp ρ τ) t := by
  induction t generalizing Δ Ε with
  | var | unit => rfl
  | abort t ih => simp [rename, ih]
  | pair t u iht ihu => simp [rename, iht, ihu]
  | fst t ih | snd t ih | inl t ih | inr t ih => simp [rename, ih]
  | case s t u ihs iht ihu =>
      change Tm.case (rename ρ (rename τ s))
        (rename (Rename.ext ρ) (rename (Rename.ext τ) t))
        (rename (Rename.ext ρ) (rename (Rename.ext τ) u)) =
        Tm.case (rename (Rename.comp ρ τ) s)
          (rename (Rename.ext (Rename.comp ρ τ)) t)
          (rename (Rename.ext (Rename.comp ρ τ)) u)
      rw [ihs ρ τ, iht (Rename.ext ρ) (Rename.ext τ),
          ihu (Rename.ext ρ) (Rename.ext τ)]
      rw [rename_eq_of_pointwise (fun x => (Rename.ext_comp_apply ρ τ x).symm) t,
          rename_eq_of_pointwise (fun x => (Rename.ext_comp_apply ρ τ x).symm) u]
  | lam t ih =>
      change Tm.lam (rename (Rename.ext ρ) (rename (Rename.ext τ) t)) =
        Tm.lam (rename (Rename.ext (Rename.comp ρ τ)) t)
      rw [ih (Rename.ext ρ) (Rename.ext τ)]
      exact congrArg Tm.lam
        (rename_eq_of_pointwise (fun x => (Rename.ext_comp_apply ρ τ x).symm) t)
  | app t u iht ihu => simp [rename, iht, ihu]

/-! ### Substitution -/

private theorem subst_exts_pointwise {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {σ τ : Subst sig Γ Δ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B), σ x = τ x)
    {B : Object sig.nBases} (x : Var (Γ ▻ A) B) :
    Subst.exts σ x = Subst.exts τ x := by
  cases x with
  | here => rfl
  | there y => exact congrArg weakenTerm (h y)

theorem subst_eq_of_pointwise {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {σ τ : Subst sig Γ Δ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B), σ x = τ x)
    (t : Tm Γ A) : subst σ t = subst τ t := by
  revert Δ σ τ h
  induction t with
  | var x =>
      intro Δ σ τ h; exact h x
  | unit =>
      intro Δ σ τ h; rfl
  | abort t ih =>
      intro Δ σ τ h
      change Tm.abort (subst σ t) = Tm.abort (subst τ t); rw [ih h]
  | pair t u iht ihu =>
      intro Δ σ τ h
      change Tm.pair (subst σ t) (subst σ u) = Tm.pair (subst τ t) (subst τ u)
      rw [iht h, ihu h]
  | fst t ih =>
      intro Δ σ τ h
      change Tm.fst (subst σ t) = Tm.fst (subst τ t); rw [ih h]
  | snd t ih =>
      intro Δ σ τ h
      change Tm.snd (subst σ t) = Tm.snd (subst τ t); rw [ih h]
  | inl t ih =>
      intro Δ σ τ h
      change Tm.inl (subst σ t) = Tm.inl (subst τ t); rw [ih h]
  | inr t ih =>
      intro Δ σ τ h
      change Tm.inr (subst σ t) = Tm.inr (subst τ t); rw [ih h]
  | case s t u ihs iht ihu =>
      intro Δ σ τ h
      change Tm.case (subst σ s) (subst (Subst.exts σ) t) (subst (Subst.exts σ) u) =
        Tm.case (subst τ s) (subst (Subst.exts τ) t) (subst (Subst.exts τ) u)
      rw [ihs h, iht (subst_exts_pointwise h), ihu (subst_exts_pointwise h)]
  | lam t ih =>
      intro Δ σ τ h
      change Tm.lam (subst (Subst.exts σ) t) = Tm.lam (subst (Subst.exts τ) t)
      rw [ih (subst_exts_pointwise h)]
  | app t u iht ihu =>
      intro Δ σ τ h
      change Tm.app (subst σ t) (subst σ u) = Tm.app (subst τ t) (subst τ u)
      rw [iht h, ihu h]

@[simp] theorem subst_ids {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) :
    subst (Subst.ids (Γ := Γ)) t = t := by
  induction t with
  | var | unit => rfl
  | abort t ih => simp [subst, ih]
  | pair t u iht ihu => simp [subst, iht, ihu]
  | fst t ih | snd t ih | inl t ih | inr t ih => simp [subst, ih]
  | case s t u ihs iht ihu =>
      change Tm.case (subst Subst.ids s)
        (subst (Subst.exts Subst.ids) t)
        (subst (Subst.exts Subst.ids) u) = Tm.case s t u
      rw [ihs,
        (subst_eq_of_pointwise Subst.exts_ids_apply t).trans iht,
        (subst_eq_of_pointwise Subst.exts_ids_apply u).trans ihu]
  | lam t ih =>
      change Tm.lam (subst (Subst.exts Subst.ids) t) = Tm.lam t
      rw [(subst_eq_of_pointwise Subst.exts_ids_apply t).trans ih]
  | app t u iht ihu => simp [subst, iht, ihu]

/-- Rename then substitute equals substitute of the renamed environment. -/
def Subst.compRename {Γ Δ Ε : Ctx sig}
    (σ : Subst sig Δ Ε) (ρ : Rename sig Γ Δ) : Subst sig Γ Ε :=
  fun {A} (x : Var Γ A) => σ (ρ x)

private theorem Subst.exts_compRename_apply {Γ Δ Ε : Ctx sig}
    {A B : Object sig.nBases}
    (σ : Subst sig Δ Ε) (ρ : Rename sig Γ Δ) (x : Var (Γ ▻ A) B) :
    Subst.compRename (Subst.exts σ) (Rename.ext ρ) x =
      Subst.exts (Subst.compRename σ ρ) x := by
  cases x <;> rfl

theorem subst_rename {Γ Δ Ε : Ctx sig} {A : Object sig.nBases}
    (σ : Subst sig Δ Ε) (ρ : Rename sig Γ Δ) (t : Tm Γ A) :
    subst σ (rename ρ t) = subst (Subst.compRename σ ρ) t := by
  induction t generalizing Δ Ε with
  | var | unit => rfl
  | abort t ih => simp [rename, subst, ih]
  | pair t u iht ihu => simp [rename, subst, iht, ihu]
  | fst t ih | snd t ih | inl t ih | inr t ih => simp [rename, subst, ih]
  | case s t u ihs iht ihu =>
      change Tm.case (subst σ (rename ρ s))
        (subst (Subst.exts σ) (rename (Rename.ext ρ) t))
        (subst (Subst.exts σ) (rename (Rename.ext ρ) u)) =
        Tm.case (subst (Subst.compRename σ ρ) s)
          (subst (Subst.exts (Subst.compRename σ ρ)) t)
          (subst (Subst.exts (Subst.compRename σ ρ)) u)
      rw [ihs σ ρ, iht (Subst.exts σ) (Rename.ext ρ),
          ihu (Subst.exts σ) (Rename.ext ρ)]
      rw [subst_eq_of_pointwise (Subst.exts_compRename_apply σ ρ) t,
          subst_eq_of_pointwise (Subst.exts_compRename_apply σ ρ) u]
  | lam t ih =>
      change Tm.lam (subst (Subst.exts σ) (rename (Rename.ext ρ) t)) =
        Tm.lam (subst (Subst.exts (Subst.compRename σ ρ)) t)
      rw [ih (Subst.exts σ) (Rename.ext ρ)]
      exact congrArg Tm.lam
        (subst_eq_of_pointwise (Subst.exts_compRename_apply σ ρ) t)
  | app t u iht ihu => simp [rename, subst, iht, ihu]

/-- Rename each term of a substitution. -/
def renameSubst {Γ Δ Ε : Ctx sig}
    (ρ : Rename sig Δ Ε) (σ : Subst sig Γ Δ) : Subst sig Γ Ε :=
  fun {A} (x : Var Γ A) => rename ρ (σ x)

private theorem renameSubst_exts_apply {Γ Δ Ε : Ctx sig} {A B : Object sig.nBases}
    (ρ : Rename sig Δ Ε) (σ : Subst sig Γ Δ) (x : Var (Γ ▻ A) B) :
    renameSubst (Rename.ext ρ) (Subst.exts σ) x =
      Subst.exts (renameSubst ρ σ) x := by
  cases x with
  | here => rfl
  | there y =>
      simp only [renameSubst, Subst.exts, weakenTerm]
      rw [rename_comp Rename.weaken ρ (σ y),
          rename_comp (Rename.ext ρ) Rename.weaken (σ y)]
      apply rename_eq_of_pointwise
      intro C z
      rfl

theorem rename_subst {Γ Δ Ε : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Δ Ε) (σ : Subst sig Γ Δ) (t : Tm Γ A) :
    rename ρ (subst σ t) = subst (renameSubst ρ σ) t := by
  induction t generalizing Δ Ε with
  | var | unit => rfl
  | abort t ih => simp [rename, subst, ih]
  | pair t u iht ihu => simp [rename, subst, iht, ihu]
  | fst t ih | snd t ih | inl t ih | inr t ih => simp [rename, subst, ih]
  | case s t u ihs iht ihu =>
      change Tm.case (rename ρ (subst σ s))
        (rename (Rename.ext ρ) (subst (Subst.exts σ) t))
        (rename (Rename.ext ρ) (subst (Subst.exts σ) u)) =
        Tm.case (subst (renameSubst ρ σ) s)
          (subst (Subst.exts (renameSubst ρ σ)) t)
          (subst (Subst.exts (renameSubst ρ σ)) u)
      rw [ihs ρ σ, iht (Rename.ext ρ) (Subst.exts σ),
          ihu (Rename.ext ρ) (Subst.exts σ)]
      rw [subst_eq_of_pointwise (renameSubst_exts_apply ρ σ) t,
          subst_eq_of_pointwise (renameSubst_exts_apply ρ σ) u]
  | lam t ih =>
      change Tm.lam (rename (Rename.ext ρ) (subst (Subst.exts σ) t)) =
        Tm.lam (subst (Subst.exts (renameSubst ρ σ)) t)
      rw [ih (Rename.ext ρ) (Subst.exts σ)]
      exact congrArg Tm.lam (subst_eq_of_pointwise (renameSubst_exts_apply ρ σ) t)
  | app t u iht ihu => simp [rename, subst, iht, ihu]

def substComp {Γ Δ Ε : Ctx sig}
    (σ : Subst sig Δ Ε) (τ : Subst sig Γ Δ) : Subst sig Γ Ε :=
  fun {A} (x : Var Γ A) => subst σ (τ x)

theorem substComp_exts_apply {Γ Δ Ε : Ctx sig} {A B : Object sig.nBases}
    (σ : Subst sig Δ Ε) (τ : Subst sig Γ Δ) (x : Var (Γ ▻ A) B) :
    Subst.exts (substComp σ τ) x =
      substComp (Subst.exts σ) (Subst.exts τ) x := by
  cases x with
  | here => rfl
  | there y =>
      simp only [substComp, Subst.exts, weakenTerm]
      rw [rename_subst Rename.weaken σ (τ y),
          subst_rename (Subst.exts σ) Rename.weaken (τ y)]
      apply subst_eq_of_pointwise
      intro C z
      rfl

theorem subst_comp {Γ Δ Ε : Ctx sig} {A : Object sig.nBases}
    (σ : Subst sig Δ Ε) (τ : Subst sig Γ Δ) (t : Tm Γ A) :
    subst σ (subst τ t) = subst (substComp σ τ) t := by
  induction t generalizing Δ Ε with
  | var | unit => rfl
  | abort t ih => simp [subst, ih]
  | pair t u iht ihu => simp [subst, iht, ihu]
  | fst t ih | snd t ih | inl t ih | inr t ih => simp [subst, ih]
  | case s t u ihs iht ihu =>
      change Tm.case (subst σ (subst τ s))
        (subst (Subst.exts σ) (subst (Subst.exts τ) t))
        (subst (Subst.exts σ) (subst (Subst.exts τ) u)) =
        Tm.case (subst (substComp σ τ) s)
          (subst (Subst.exts (substComp σ τ)) t)
          (subst (Subst.exts (substComp σ τ)) u)
      rw [ihs σ τ, iht (Subst.exts σ) (Subst.exts τ),
          ihu (Subst.exts σ) (Subst.exts τ)]
      rw [subst_eq_of_pointwise (fun x => (substComp_exts_apply σ τ x).symm) t,
          subst_eq_of_pointwise (fun x => (substComp_exts_apply σ τ x).symm) u]
  | lam t ih =>
      change Tm.lam (subst (Subst.exts σ) (subst (Subst.exts τ) t)) =
        Tm.lam (subst (Subst.exts (substComp σ τ)) t)
      rw [ih (Subst.exts σ) (Subst.exts τ)]
      exact congrArg Tm.lam
        (subst_eq_of_pointwise (fun x => (substComp_exts_apply σ τ x).symm) t)
  | app t u iht ihu => simp [subst, iht, ihu]

theorem weakenTerm_eq_rename {Γ : Ctx sig} {A B : Object sig.nBases}
    (t : Tm Γ B) :
    weakenTerm (A := A) t = rename Rename.weaken t :=
  rfl

@[simp] theorem subst0_here {Γ : Ctx sig} {A : Object sig.nBases} (n : Tm Γ A) :
    subst0 (.var .here) n = n :=
  rfl

@[simp] theorem subst0_there {Γ : Ctx sig} {A B : Object sig.nBases}
    (x : Var Γ B) (n : Tm Γ A) :
    subst0 (.var (.there x)) n = .var x :=
  rfl

/-- Renaming commutes with substitution for the newest binder. -/
theorem rename_subst0 {Γ Δ : Ctx sig} {A B : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (t : Tm (Γ ▻ A) B) (n : Tm Γ A) :
    rename ρ (subst0 t n) = subst0 (rename (Rename.ext ρ) t) (rename ρ n) := by
  show rename ρ (subst (Subst.single n) t) =
    subst (Subst.single (rename ρ n)) (rename (Rename.ext ρ) t)
  rw [rename_subst, subst_rename]
  refine subst_eq_of_pointwise ?_ t
  intro C x
  cases x <;> rfl

/-! ### Erasure commutes with renaming

Focused syntax is erased to ordinary terms before it is interpreted, so every
re-indexing performed by focusing has to be visible on the erasure.
-/

mutual
theorem NegNeu.erase_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (n : NegNeu Γ A) :
    NegNeu.erase (NegNeu.rename ρ n) = rename ρ (NegNeu.erase n) :=
  match n with
  | .var _ => rfl
  | .app m t => by
      simp [NegNeu.rename, NegNeu.erase, rename, NegNeu.erase_rename ρ m,
        InvTm.erase_rename ρ t]
  | .fst m => by
      simp [NegNeu.rename, NegNeu.erase, rename, NegNeu.erase_rename ρ m]
  | .snd m => by
      simp [NegNeu.rename, NegNeu.erase, rename, NegNeu.erase_rename ρ m]

theorem PosNeu.erase_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (p : PosNeu Γ A) :
    PosNeu.erase (PosNeu.rename ρ p) = rename ρ (PosNeu.erase p) :=
  match p with
  | .neu n => by
      simp [PosNeu.rename, PosNeu.erase, NegNeu.erase_rename ρ n]
  | .inl q => by
      simp [PosNeu.rename, PosNeu.erase, rename, PosNeu.erase_rename ρ q]
  | .inr q => by
      simp [PosNeu.rename, PosNeu.erase, rename, PosNeu.erase_rename ρ q]
  | .val t => by
      simp [PosNeu.rename, PosNeu.erase, InvTm.erase_rename ρ t]

theorem InvTm.erase_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (t : InvTm Γ A) :
    InvTm.erase (InvTm.rename ρ t) = rename ρ (InvTm.erase t) :=
  match t with
  | .unit => rfl
  | .pair t u => by
      simp [InvTm.rename, InvTm.erase, rename, InvTm.erase_rename ρ t,
        InvTm.erase_rename ρ u]
  | .lam t => by
      simp [InvTm.rename, InvTm.erase, rename,
        InvTm.erase_rename (Rename.ext ρ) t]
  | .case n t u => by
      simp [InvTm.rename, InvTm.erase, rename, NegNeu.erase_rename ρ n,
        InvTm.erase_rename (Rename.ext ρ) t,
        InvTm.erase_rename (Rename.ext ρ) u]
  | .abort n => by
      simp [InvTm.rename, InvTm.erase, rename, NegNeu.erase_rename ρ n]
  | .foc f => by
      simp [InvTm.rename, InvTm.erase, FocTm.erase_rename ρ f]

theorem FocTm.erase_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (f : FocTm Γ A) :
    FocTm.erase (FocTm.rename ρ f) = rename ρ (FocTm.erase f) :=
  match f with
  | .pos (.done p) => by
      simp [FocTm.rename, PosIntro.rename, FocTm.erase, PosIntro.erase,
        PosNeu.erase_rename ρ p]
  | .neg (.done n) => by
      simp [FocTm.rename, NegElim.rename, FocTm.erase, NegElim.erase,
        NegNeu.erase_rename ρ n]
  | .letPos n t => by
      simp [FocTm.rename, FocTm.erase, rename_subst0, NegNeu.erase_rename ρ n,
        InvTm.erase_rename (Rename.ext ρ) t]
  | .sat (.mk _ t) => by
      simp [FocTm.rename, SatTm.rename, FocTm.erase, SatTm.erase,
        InvTm.erase_rename ρ t]
end

@[simp] theorem InvTm.erase_weaken {Γ : Ctx sig} {A B : Object sig.nBases}
    (t : InvTm Γ A) :
    InvTm.erase (InvTm.weaken (B := B) t) = weakenTerm (InvTm.erase t) :=
  InvTm.erase_rename _ t

@[simp] theorem NegNeu.erase_weaken {Γ : Ctx sig} {A B : Object sig.nBases}
    (n : NegNeu Γ A) :
    NegNeu.erase (NegNeu.weaken (B := B) n) = weakenTerm (NegNeu.erase n) :=
  NegNeu.erase_rename _ n

/-! ### Decidable structural equality -/

def Ctx.decidableEq : (Γ Δ : Ctx sig) → Decidable (Γ = Δ)
  | .empty, .empty => isTrue rfl
  | .snoc Γ A, .snoc Δ B =>
      match Ctx.decidableEq Γ Δ, decEq A B with
      | isTrue hΓ, isTrue hA => isTrue (by cases hΓ; cases hA; rfl)
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .empty, .snoc _ _ => isFalse (by intro h; cases h)
  | .snoc _ _, .empty => isFalse (by intro h; cases h)

instance : DecidableEq (Ctx sig) := Ctx.decidableEq

def Var.decidableEq {Γ : Ctx sig} {A : Object sig.nBases} :
    (x y : Var Γ A) → Decidable (x = y)
  | .here, .here => isTrue rfl
  | .there x, .there y =>
      match Var.decidableEq x y with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .here, .there _ => isFalse (by intro h; cases h)
  | .there _, .here => isFalse (by intro h; cases h)

instance instDecidableEqVar {Γ : Ctx sig} {A : Object sig.nBases} :
    DecidableEq (Var Γ A) :=
  Var.decidableEq

instance : DecidableEq RawNeu := inferInstance
instance : DecidableEq RawPos := inferInstance
instance : DecidableEq RawFocused := inferInstance

/-! ### Generator telescope -/

theorem genCtx_empty :
    genCtx (sig := ⟨0, #[]⟩) = Ctx.empty :=
  rfl

theorem genTelescope_var (sig : Signature) (q : Fin sig.nGens) :
    (genTelescope sig).var q = genVar sig q :=
  rfl

theorem genTelescope_ctx (sig : Signature) :
    (genTelescope sig).ctx = genCtx sig :=
  rfl

example (sig : Signature) (q : Fin sig.nGens) :
    Var (genCtx sig) (genType sig q) :=
  genVar sig q

end Equality
end Gimbal
