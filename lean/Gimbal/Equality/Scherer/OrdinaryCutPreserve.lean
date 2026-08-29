/-
  Erasure preservation for the executable ordinary principal cut.

  This module is deliberately downstream of `OrdinaryCutProto`: it proves the
  public cut computation sound in `TmEq` without defining the root `Tm`
  producer or importing the legacy focused/hereditary pipeline.
-/

import Gimbal.Equality.Scherer.OrdinaryCutProto
import Gimbal.Equality.Scherer.EraseComm
import Gimbal.Equality.TmEq

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Context algebra for a stable variable below pending positives -/

/-- Weaken a base context through every pending positive binder. -/
def Pending.weakenBase {Γ : Ctx sig} :
    (ps : Pending sig) → Rename sig Γ (Pending.eraseAux ps Γ)
  | .empty => by
      simpa only [Pending.eraseAux] using (Rename.id : Rename sig Γ Γ)
  | .cons P qs =>
      renameComp (Pending.weakenBase (Γ := Γ.snoc P.erase) qs) Rename.weaken

/-- `TmEq` is stable under object-context renaming. -/
theorem TmEq.rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) {t u : Tm Γ A} (h : TmEq t u) :
    TmEq (rename ρ t) (rename ρ u) := by
  refine ⟨?_⟩
  intro X env
  rw [interpret_rename, interpret_rename]
  exact h.qm_eq (Env.rename env ρ)

theorem subst_exts_single_rename_skip1_cut {Γ : Ctx sig}
    {A P C : Object sig.nBases} (t : Tm (Γ.snoc A) C) (n : Tm Γ P) :
    subst (Subst.exts (Subst.single n)) (Equality.rename Rename.skip1 t) = t := by
  rw [subst_rename]
  refine Eq.trans (subst_eq_of_pointwise (τ := fun {_} => Subst.ids) ?_ t)
    (subst_ids t)
  intro B x
  cases x <;> rfl

theorem subst0_subst0_comm_cut {Γ : Ctx sig}
    {A P C : Object sig.nBases}
    (t : Tm (Γ.snoc A |>.snoc P) C) (n : Tm (Γ.snoc A) P)
    (v : Tm Γ A) :
    subst0 (subst (Subst.exts (Subst.single v)) t) (subst0 n v) =
      subst0 (subst0 t n) v := by
  show subst (Subst.single (subst (Subst.single v) n))
      (subst (Subst.exts (Subst.single v)) t) =
    subst (Subst.single v) (subst (Subst.single n) t)
  rw [subst_comp, subst_comp]
  refine subst_eq_of_pointwise ?_ t
  intro D x
  match x with
  | .here => rfl
  | .there .here => exact subst0_weakenTerm v (subst (Subst.single v) n)
  | .there (.there _) => rfl

@[simp] theorem rename_ext_id_cut {Γ : Ctx sig} {A B : Object sig.nBases}
    (t : Tm (Γ.snoc A) B) :
    Equality.rename (Rename.ext (Rename.id : Rename sig Γ Γ)) t = t :=
  (rename_eq_of_pointwise Rename.ext_id_apply t).trans (rename_id t)

theorem rename_ext_id_skip1_id_cut {Γ : Ctx sig}
    {A B C : Object sig.nBases} (t : Tm (Γ.snoc A) C) :
    rename (Rename.ext (Rename.id : Rename sig (Γ.snoc B) (Γ.snoc B)))
        (rename (Rename.skip1 (Γ := Γ) (A := A) (B := B))
          (rename (Rename.id : Rename sig (Γ.snoc A) (Γ.snoc A)) t)) =
      rename (Rename.skip1 (Γ := Γ) (A := A) (B := B)) t := by
  rw [rename_ext_id_cut, rename_id]

theorem rename_ext_weakenBase_empty_cut {Γ : Ctx sig}
    {P C : Object sig.nBases} (t : Tm (Γ.snoc P) C) :
    rename (Rename.ext
      (Pending.weakenBase (sig := sig) (Γ := Γ) .empty)) t = t := by
  refine (rename_eq_of_pointwise ?_ t).trans (rename_id t)
  intro A x
  cases x <;> rfl

theorem erase_caseSum_empty_eq {Γ : StableCtx sig}
    {A B : Pos sig.nBases} {G : Goal sig.nBases}
    (l : Inv Γ (.cons A .empty) G) (r : Inv Γ (.cons B .empty) G) :
    Inv.erase (.caseSum l r) =
      .case (.var .here)
        (rename (Rename.skip1 (Γ := Γ.erase) (A := A.erase)
          (B := (Pos.sum A B).erase)) l.erase)
        (rename (Rename.skip1 (Γ := Γ.erase) (A := B.erase)
          (B := (Pos.sum A B).erase)) r.erase) := by
  simp only [Inv.erase, Pending.eraseAux, rotateHeadToNewest,
    rotateNewestToHead, Equality.rename, rename_id]
  congr 1
  · exact rename_ext_id_cut _
  · exact rename_ext_id_cut _

theorem subst0_erase_caseSum_empty {Γ : StableCtx sig}
    {A B : Pos sig.nBases} {G : Goal sig.nBases}
    (l : Inv Γ (.cons A .empty) G) (r : Inv Γ (.cons B .empty) G)
    (p : Tm Γ.erase (Pos.sum A B).erase) :
    subst0 (Inv.erase (.caseSum l r)) p =
      .case p l.erase r.erase := by
  rw [erase_caseSum_empty_eq]
  simp only [subst0, subst]
  congr 1
  · exact subst_exts_single_rename_skip1_cut
      (A := A.erase) (P := (Pos.sum A B).erase) l.erase p
  · exact subst_exts_single_rename_skip1_cut
      (A := B.erase) (P := (Pos.sum A B).erase) r.erase p

theorem Inv.erase_rebuildCaseSum {Γ : StableCtx sig}
    {A B : Pos sig.nBases} {ps : Pending sig} {G : Goal sig.nBases}
    (k : Inv Γ (.cons (.sum A B) ps) G) :
    Inv.erase (.caseSum k.asCaseSum.1 k.asCaseSum.2) = k.erase := by
  cases k
  rfl

theorem Inv.erase_asStoreShift {Γ : StableCtx sig}
    {N : Neg sig.nBases} {ps : Pending sig} {G : Goal sig.nBases}
    (k : Inv Γ (.cons (.shift N) ps) G) :
    k.asStoreShift.erase = k.erase := by
  cases k
  rfl

theorem StableRename.erase_replaceNewestAtom_apply {Γ : StableCtx sig}
    {q : Fin sig.nBases} (x : StableVar Γ (.atom q))
    {A : Object sig.nBases} (y : Var (Γ.snoc (.atom q)).erase A) :
    StableRename.erase (StableRename.replaceNewestAtom x) y =
      Rename.subst0Var x.erase y := by
  cases y with
  | here => rfl
  | there y =>
      have hid := StableRename.erase_id_apply (Γ := Γ) y
      unfold StableRename.erase at hid ⊢
      rw [StableRename.ofEraseVar_there]
      generalize hp : StableRename.ofEraseVar Γ y = p at hid ⊢
      obtain ⟨S, h, z⟩ := p
      simpa [StableRename.id, StableRename.replaceNewestAtom,
        Rename.subst0Var] using hid

theorem StableRename.erase_replaceNewestNeg_apply {Γ : StableCtx sig}
    {N : Neg sig.nBases} (x : StableVar Γ (.neg N))
    {A : Object sig.nBases} (y : Var (Γ.snoc (.neg N)).erase A) :
    StableRename.erase (StableRename.replaceNewestNeg x) y =
      Rename.subst0Var x.erase y := by
  cases y with
  | here => rfl
  | there y =>
      have hid := StableRename.erase_id_apply (Γ := Γ) y
      unfold StableRename.erase at hid ⊢
      rw [StableRename.ofEraseVar_there]
      generalize hp : StableRename.ofEraseVar Γ y = p at hid ⊢
      obtain ⟨S, h, z⟩ := p
      simpa [StableRename.id, StableRename.replaceNewestNeg,
        Rename.subst0Var] using hid

theorem StableRename.erase_exchange_apply {Γ : StableCtx sig}
    {S T : StableTy sig.nBases} {A : Object sig.nBases}
    (x : Var ((Γ.snoc S).snoc T).erase A) :
    StableRename.erase (StableRename.exchange (Γ := Γ) (S := S) (T := T)) x =
      Rename.exchange x := by
  cases x with
  | here => rfl
  | there x =>
      cases x with
      | here => rfl
      | there y =>
          have hid := StableRename.erase_id_apply (Γ := Γ) y
          unfold StableRename.erase at hid ⊢
          rw [StableRename.ofEraseVar_there, StableRename.ofEraseVar_there]
          generalize hp : StableRename.ofEraseVar Γ y = p at hid ⊢
          obtain ⟨U, h, z⟩ := p
          change h ▸ (StableVar.erase z).there.there = y.there.there
          refine (cast_var_there (S := S.erase) h
            (Var.there (B := T.erase) (StableVar.erase z))).trans ?_
          apply congrArg (Var.there (B := S.erase))
          refine (cast_var_there (S := T.erase) h (StableVar.erase z)).trans ?_
          exact congrArg (Var.there (B := T.erase)) hid

/-! ### Erased results and public preservation statements -/

def NegSubstResult.erase {Γ : StableCtx sig} {Cut N : Neg sig.nBases} :
    NegSubstResult Γ Cut N → Tm Γ.erase N.erase
  | .neu n => n.erase
  | .value t _ => t.erase

/-- The ordinary term denoted by a strongly retrievable positive. -/
def StrongPos.erase {Γ : StableCtx sig} {P : Pos sig.nBases} :
    StrongPos Γ P → Tm Γ.erase P.erase
  | .negVar x => .var x.erase
  | .atomVar x => .var x.erase
  | .inl p => .inl p.erase
  | .inr p => .inr p.erase

/-- Erasure of a continuation after moving its cut binder past pending inputs. -/
def Pending.liftSubst {Γ Δ : Ctx sig} (σ : Subst sig Γ Δ) :
    (ps : Pending sig) →
      Subst sig (Pending.eraseAux ps Γ) (Pending.eraseAux ps Δ)
  | .empty => σ
  | .cons _ qs => qs.liftSubst (Subst.exts σ)

/-- Substitute a newest stable negative below all pending positive binders. -/
def substBelowPending {Γ : StableCtx sig} {Cut : Neg sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    (t : Inv (Γ.snoc (.neg Cut)) ps G) (v : Inv Γ .empty (.neg Cut)) :
    Tm (eraseInvCtx Γ ps) G.erase :=
  subst (ps.liftSubst (Subst.single v.erase)) t.erase

/-- Erasure of a positive cut below an arbitrary pending prefix. -/
def bindBelowPending {Γ : StableCtx sig} {qs : Pending sig}
    {P : Pos sig.nBases} {G : Goal sig.nBases}
    (d : Inv Γ qs (.pos P)) (k : Inv Γ (.cons P .empty) G) :
    Tm (eraseInvCtx Γ qs) G.erase :=
  subst0
    (rename (Rename.ext (Pending.weakenBase qs)) k.erase)
    d.erase

theorem Pending.liftSubst_renameEraseAux_apply {Γ Δ Ε : Ctx sig}
    (ps : Pending sig) (ρ : Rename sig Γ Δ)
    (σ : Subst sig Δ Ε) (τ : Subst sig Γ Ε)
    (h : ∀ {A : Object sig.nBases} (x : Var Γ A), σ (ρ x) = τ x)
    {A : Object sig.nBases} (x : Var (Pending.eraseAux ps Γ) A) :
    ps.liftSubst σ (renameEraseAux ρ ps x) = ps.liftSubst τ x := by
  induction ps generalizing Γ Δ Ε with
  | empty => exact h x
  | cons P qs ih =>
      apply ih
      intro B y
      cases y with
      | here => rfl
      | there z => exact congrArg weakenTerm (h z)

theorem Pending.liftSubst_eq_of_pointwise {Γ Δ : Ctx sig}
    (ps : Pending sig) {σ τ : Subst sig Γ Δ}
    (h : ∀ {A : Object sig.nBases} (x : Var Γ A), σ x = τ x)
    {A : Object sig.nBases} (x : Var (Pending.eraseAux ps Γ) A) :
    ps.liftSubst σ x = ps.liftSubst τ x := by
  induction ps generalizing Γ Δ with
  | empty => exact h x
  | cons Q qs ih =>
      apply ih
      intro B y
      cases y with
      | here => rfl
      | there z => exact congrArg weakenTerm (h z)

theorem Subst.exts_renameSubst_apply_cut {Γ Δ Ε : Ctx sig}
    {A B : Object sig.nBases} (ρ : Rename sig Δ Ε)
    (σ : Subst sig Γ Δ) (x : Var (Γ.snoc A) B) :
    Subst.exts (renameSubst ρ σ) x =
      renameSubst (Rename.ext ρ) (Subst.exts σ) x := by
  cases x with
  | here => rfl
  | there y =>
      simp only [renameSubst, Subst.exts, weakenTerm]
      rw [rename_comp Rename.weaken ρ (σ y),
        rename_comp (Rename.ext ρ) Rename.weaken (σ y)]
      apply rename_eq_of_pointwise
      intro C z
      rfl

theorem Pending.liftSubst_renameSubst_apply {Γ Δ Ε : Ctx sig}
    (ps : Pending sig) (ρ : Rename sig Δ Ε) (σ : Subst sig Γ Δ)
    {A : Object sig.nBases} (x : Var (Pending.eraseAux ps Γ) A) :
    ps.liftSubst (renameSubst ρ σ) x =
      rename (renameEraseAux ρ ps) (ps.liftSubst σ x) := by
  induction ps generalizing Γ Δ Ε with
  | empty => rfl
  | cons Q qs ih =>
      refine Eq.trans (Pending.liftSubst_eq_of_pointwise qs
        (Subst.exts_renameSubst_apply_cut ρ σ) x) ?_
      exact ih (Rename.ext ρ) (Subst.exts σ) x

theorem Subst.exts2_exchange_apply_cut {Γ Δ : Ctx sig}
    {A B C : Object sig.nBases} (σ : Subst sig Γ Δ)
    (x : Var ((Γ.snoc A).snoc B) C) :
    Subst.exts (Subst.exts σ) (Rename.exchange x) =
      rename Rename.exchange (Subst.exts (Subst.exts σ) x) := by
  cases x with
  | here => rfl
  | there x =>
      cases x with
      | here => rfl
      | there y =>
          simp only [Subst.exts, weakenTerm]
          change rename Rename.weaken (rename Rename.weaken (σ y)) =
            rename Rename.exchange
              (rename Rename.weaken (rename Rename.weaken (σ y)))
          rw [rename_comp, rename_comp, rename_comp]
          apply rename_eq_of_pointwise
          intro D z
          rfl

theorem Pending.liftSubst_rotateNewest_here {Γ Δ : Ctx sig}
    {H : Object sig.nBases} (ps : Pending sig) (σ : Subst sig Γ Δ) :
    ps.liftSubst (Subst.exts σ)
        (rotateNewestToHead (Δ := Γ) (A := H) ps Var.here) =
      .var (rotateNewestToHead (Δ := Δ) (A := H) ps Var.here) := by
  induction ps generalizing Γ Δ with
  | empty => rfl
  | cons Q qs ih =>
      simp only [Pending.liftSubst, rotateNewestToHead, renameComp]
      refine Eq.trans (Pending.liftSubst_renameEraseAux_apply qs
        (Rename.exchange (Γ := Γ) (A := Q.erase) (B := H))
        (Subst.exts (Subst.exts σ))
        (renameSubst (Rename.exchange (Γ := Δ) (A := Q.erase) (B := H))
          (Subst.exts (Subst.exts σ)))
        (fun x => Subst.exts2_exchange_apply_cut σ x)
        (rotateNewestToHead (Δ := Γ.snoc Q.erase) (A := H) qs Var.here)) ?_
      rw [Pending.liftSubst_renameSubst_apply, ih]
      rfl

theorem Pending.liftSubst_rotateNewest_apply {Γ Δ : Ctx sig}
    {H C : Object sig.nBases} (ps : Pending sig) (σ : Subst sig Γ Δ)
    (x : Var ((Pending.eraseAux ps Γ).snoc H) C) :
    ps.liftSubst (Subst.exts σ)
        (rotateNewestToHead (Δ := Γ) (A := H) ps x) =
      rename (rotateNewestToHead (Δ := Δ) (A := H) ps)
        (Subst.exts (ps.liftSubst σ) x) := by
  induction ps generalizing Γ Δ C with
  | empty =>
      cases x with
      | here => rfl
      | there y =>
          simp only [Pending.liftSubst, rotateNewestToHead, Subst.exts]
          change weakenTerm (σ y) = rename Rename.id (weakenTerm (σ y))
          exact (rename_id (weakenTerm (σ y))).symm
  | cons Q qs ih =>
      simp only [Pending.liftSubst, rotateNewestToHead, renameComp]
      refine Eq.trans (Pending.liftSubst_renameEraseAux_apply qs
        (Rename.exchange (Γ := Γ) (A := Q.erase) (B := H))
        (Subst.exts (Subst.exts σ))
        (renameSubst (Rename.exchange (Γ := Δ) (A := Q.erase) (B := H))
          (Subst.exts (Subst.exts σ)))
        (fun x => Subst.exts2_exchange_apply_cut σ x)
        (rotateNewestToHead (Δ := Γ.snoc Q.erase) (A := H) qs x)) ?_
      rw [Pending.liftSubst_renameSubst_apply,
        ih (Subst.exts σ), rename_comp]
      rfl

theorem Pending.liftSubst_rotateHead_apply {Γ Δ : Ctx sig}
    {H C : Object sig.nBases} (ps : Pending sig) (σ : Subst sig Γ Δ)
    (x : Var (Pending.eraseAux ps (Γ.snoc H)) C) :
    Subst.exts (ps.liftSubst σ)
        (rotateHeadToNewest (Δ := Γ) (H := H) ps x) =
      rename (rotateHeadToNewest (Δ := Δ) (H := H) ps)
        (ps.liftSubst (Subst.exts σ) x) := by
  induction ps generalizing Γ Δ C with
  | empty =>
      simp only [Pending.liftSubst, rotateHeadToNewest]
      exact (rename_id (Subst.exts σ x)).symm
  | cons Q qs ih =>
      simp only [Pending.liftSubst, rotateHeadToNewest, renameComp]
      erw [ih (Subst.exts σ)]
      change _ = rename (Rename.comp
        (rotateHeadToNewest (Δ := Δ.snoc Q.erase) (H := H) qs)
        (renameEraseAux
          (Rename.exchange (Γ := Δ) (A := H) (B := Q.erase)) qs)) _
      rw [← rename_comp
        (rotateHeadToNewest (Δ := Δ.snoc Q.erase) (H := H) qs)
        (renameEraseAux
          (Rename.exchange (Γ := Δ) (A := H) (B := Q.erase)) qs)]
      refine congrArg (rename
        (rotateHeadToNewest (Δ := Δ.snoc Q.erase) (H := H) qs)) ?_
      refine Eq.trans (Pending.liftSubst_renameEraseAux_apply qs
        (Rename.exchange (Γ := Γ) (A := H) (B := Q.erase))
        (Subst.exts (Subst.exts σ))
        (renameSubst (Rename.exchange (Γ := Δ) (A := H) (B := Q.erase))
          (Subst.exts (Subst.exts σ)))
        (fun x => Subst.exts2_exchange_apply_cut σ x) x) ?_
      rw [Pending.liftSubst_renameSubst_apply]

theorem Pending.ext_liftSubst_rotateNewest_apply {Γ Δ : Ctx sig}
    {H A C : Object sig.nBases} (ps : Pending sig) (σ : Subst sig Γ Δ)
    (x : Var (((Pending.eraseAux ps Γ).snoc H).snoc A) C) :
    Subst.exts (ps.liftSubst (Subst.exts σ))
        (Rename.ext (rotateNewestToHead (Δ := Γ) (A := H) ps) x) =
      rename (Rename.ext (rotateNewestToHead (Δ := Δ) (A := H) ps))
        (Subst.exts (Subst.exts (ps.liftSubst σ)) x) := by
  cases x with
  | here => rfl
  | there y =>
      simp only [Subst.exts, Rename.ext, weakenTerm]
      rw [Pending.liftSubst_rotateNewest_apply]
      rw [rename_comp, rename_comp]
      apply rename_eq_of_pointwise
      intro D z
      rfl

theorem Subst.exts2_skip1_apply_cut {Γ Δ : Ctx sig}
    {A B C : Object sig.nBases} (σ : Subst sig Γ Δ)
    (x : Var (Γ.snoc A) C) :
    Subst.exts (Subst.exts σ) (Rename.skip1 (B := B) x) =
      rename (Rename.skip1 (B := B)) (Subst.exts σ x) := by
  cases x with
  | here => rfl
  | there y =>
      simp only [Subst.exts, Rename.skip1, weakenTerm]
      rw [rename_comp, rename_comp]
      apply rename_eq_of_pointwise
      intro D z
      rfl

theorem subst_case_branch_cut {Γ Δ : Ctx sig}
    {S A : Pos sig.nBases} {C : Object sig.nBases}
    (ps : Pending sig) (σ : Subst sig Γ Δ)
    (t : Tm (Pending.eraseAux ps (Γ.snoc A.erase)) C) :
    subst (Subst.exts ((Pending.cons S ps).liftSubst σ))
        (rename (Rename.ext
            (rotateNewestToHead (Δ := Γ) (A := S.erase) ps))
          (rename (Rename.skip1 (Γ := Pending.eraseAux ps Γ)
              (A := A.erase) (B := S.erase))
            (rename (rotateHeadToNewest (Δ := Γ) (H := A.erase) ps) t))) =
      rename (Rename.ext
          (rotateNewestToHead (Δ := Δ) (A := S.erase) ps))
        (rename (Rename.skip1 (Γ := Pending.eraseAux ps Δ)
            (A := A.erase) (B := S.erase))
          (rename (rotateHeadToNewest (Δ := Δ) (H := A.erase) ps)
            (subst ((Pending.cons A ps).liftSubst σ) t))) := by
  rw [subst_rename, subst_rename, subst_rename]
  simp only [rename_subst]
  apply subst_eq_of_pointwise
  intro D x
  change Subst.exts (ps.liftSubst (Subst.exts σ))
      (Rename.ext (rotateNewestToHead (Δ := Γ) (A := S.erase) ps)
        (Rename.skip1
          (rotateHeadToNewest (Δ := Γ) (H := A.erase) ps x))) = _
  rw [Pending.ext_liftSubst_rotateNewest_apply,
    Subst.exts2_skip1_apply_cut,
    Pending.liftSubst_rotateHead_apply]
  rfl

theorem subst_store_cut_eq {Γ : Ctx sig} {Cut : Object sig.nBases}
    {P : Pos sig.nBases} {ps : Pending sig} {C : Object sig.nBases}
    (t : Tm (Pending.eraseAux ps ((Γ.snoc Cut).snoc P.erase)) C)
    (v : Tm Γ Cut) :
    subst (ps.liftSubst (Subst.single (weakenTerm v)))
        (rename (renameEraseAux Rename.exchange ps) t) =
      subst ((Pending.cons P ps).liftSubst (Subst.single v)) t := by
  rw [subst_rename]
  refine subst_eq_of_pointwise ?_ t
  intro A x
  apply Pending.liftSubst_renameEraseAux_apply
  intro B y
  cases y with
  | here => rfl
  | there y =>
      cases y <;> rfl

theorem Inv.erase_weaken_eq {Γ : StableCtx sig} {S : StableTy sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases} (t : Inv Γ ps G) :
    (Inv.weaken (S := S) t).erase =
      Equality.rename (renameEraseAux Rename.weaken ps) t.erase := by
  rw [Inv.erase_weaken]
  apply rename_eq_of_pointwise
  exact renameEraseAux_eq_of_pointwise
    (fun x => StableRename.erase_weaken_apply x) ps

theorem Inv.erase_rename_exchange {Γ : StableCtx sig}
    {S T : StableTy sig.nBases} {ps : Pending sig} {G : Goal sig.nBases}
    (t : Inv ((Γ.snoc S).snoc T) ps G) :
    (Inv.rename StableRename.exchange t).erase =
      Equality.rename (renameEraseAux Rename.exchange ps) t.erase := by
  rw [Inv.erase_rename]
  apply rename_eq_of_pointwise
  exact renameEraseAux_eq_of_pointwise
    (fun x => StableRename.erase_exchange_apply x) ps

theorem bindBelowPending_weaken_eq_atom {Γ : StableCtx sig}
    {q : Fin sig.nBases} {qs : Pending sig} {P : Pos sig.nBases}
    {G : Goal sig.nBases} (t : Inv (Γ.snoc (.atom q)) qs (.pos P))
    (k : Inv Γ (.cons P .empty) G) :
    bindBelowPending t (Inv.weaken (S := .atom q) k) =
      bindBelowPending (.storeAtom t) k := by
  unfold bindBelowPending
  rw [Inv.erase_weaken_eq]
  congr 1
  calc
    rename (Rename.ext (Pending.weakenBase qs))
        (rename (renameEraseAux Rename.weaken (.cons P .empty)) k.erase) =
      rename (Rename.comp (Rename.ext (Pending.weakenBase qs))
        (renameEraseAux Rename.weaken (.cons P .empty))) k.erase :=
        rename_comp _ _ _
    _ = rename (Rename.ext (Pending.weakenBase (.cons (.atom q) qs)))
        k.erase := by
      apply rename_eq_of_pointwise
      intro A x
      cases x <;> rfl

theorem bindBelowPending_weaken_eq_shift {Γ : StableCtx sig}
    {N : Neg sig.nBases} {qs : Pending sig} {P : Pos sig.nBases}
    {G : Goal sig.nBases} (t : Inv (Γ.snoc (.neg N)) qs (.pos P))
    (k : Inv Γ (.cons P .empty) G) :
    bindBelowPending t (Inv.weaken (S := .neg N) k) =
      bindBelowPending (.storeShift t) k := by
  unfold bindBelowPending
  rw [Inv.erase_weaken_eq]
  congr 1
  calc
    rename (Rename.ext (Pending.weakenBase qs))
        (rename (renameEraseAux Rename.weaken (.cons P .empty)) k.erase) =
      rename (Rename.comp (Rename.ext (Pending.weakenBase qs))
        (renameEraseAux Rename.weaken (.cons P .empty))) k.erase :=
        rename_comp _ _ _
    _ = rename (Rename.ext (Pending.weakenBase (.cons (.shift N) qs)))
        k.erase := by
      apply rename_eq_of_pointwise
      intro A x
      cases x <;> rfl

theorem Inv.tmEq_pendingFst {Γ : StableCtx sig} {ps : Pending sig}
    {A B : Neg sig.nBases} (t : Inv Γ ps (.neg (.prod A B))) :
    TmEq t.pendingFst.erase (.fst t.erase) :=
  match t with
  | .caseSum (A := L) (B := R) (ps := rest) l r => by
      simp only [Inv.pendingFst, Inv.erase]
      let rotL : Rename sig (Pending.eraseAux rest (Γ.erase.snoc L.erase))
          ((Pending.eraseAux rest Γ.erase).snoc L.erase) :=
        rotateHeadToNewest (Δ := Γ.erase) (H := L.erase) rest
      let rotR : Rename sig (Pending.eraseAux rest (Γ.erase.snoc R.erase))
          ((Pending.eraseAux rest Γ.erase).snoc R.erase) :=
        rotateHeadToNewest (Δ := Γ.erase) (H := R.erase) rest
      let out : Rename sig
          ((Pending.eraseAux rest Γ.erase).snoc (.coprod L.erase R.erase))
          (Pending.eraseAux rest (Γ.erase.snoc (.coprod L.erase R.erase))) :=
        rotateNewestToHead (Δ := Γ.erase) (A := (.coprod L.erase R.erase)) rest
      let s : Tm ((Pending.eraseAux rest Γ.erase).snoc (.coprod L.erase R.erase))
          (.coprod L.erase R.erase) := .var .here
      let skipL : Rename sig
          ((Pending.eraseAux rest Γ.erase).snoc L.erase)
          (((Pending.eraseAux rest Γ.erase).snoc (.coprod L.erase R.erase)).snoc L.erase) :=
        Rename.skip1
      let skipR : Rename sig
          ((Pending.eraseAux rest Γ.erase).snoc R.erase)
          (((Pending.eraseAux rest Γ.erase).snoc (.coprod L.erase R.erase)).snoc R.erase) :=
        Rename.skip1
      let bl := Equality.rename skipL (Equality.rename rotL l.erase)
      let br := Equality.rename skipR (Equality.rename rotR r.erase)
      have hl : TmEq
          (Equality.rename skipL
            (Equality.rename rotL l.pendingFst.erase)) (.fst bl) := by
        simpa [bl, Equality.rename, Goal.erase, Neg.erase, Pos.erase] using
          TmEq.rename skipL (TmEq.rename rotL (Inv.tmEq_pendingFst l))
      have hr : TmEq
          (Equality.rename skipR
            (Equality.rename rotR r.pendingFst.erase)) (.fst br) := by
        simpa [br, Equality.rename, Goal.erase, Neg.erase, Pos.erase] using
          TmEq.rename skipR (TmEq.rename rotR (Inv.tmEq_pendingFst r))
      have hinner : TmEq
          (.case s
            (Equality.rename skipL (Equality.rename rotL l.pendingFst.erase))
            (Equality.rename skipR (Equality.rename rotR r.pendingFst.erase)))
          (.fst (.case s bl br)) :=
        TmEq.trans (TmEq.«case» (TmEq.refl s) hl hr)
          (TmEq.cc_fst_case s bl br).symm
      simpa [out, rotL, rotR, skipL, skipR, s, bl, br, Equality.rename,
        eraseInvCtx, Goal.erase, Neg.erase, Pos.erase] using
        TmEq.rename out hinner
  | .abort (ps := rest) => by
      let n := Inv.erase
        (.abort : Inv Γ (.cons .zero rest) (.pos .zero))
      exact TmEq.of_never n _ _
  | .storeAtom t => by
      simpa [Inv.pendingFst, Inv.erase, eraseInvCtx, StableCtx.erase_snoc,
        StableTy.erase, Pos.erase, Neg.erase] using
        Inv.tmEq_pendingFst t
  | .storeShift t => by
      simpa [Inv.pendingFst, Inv.erase, eraseInvCtx, StableCtx.erase_snoc,
        StableTy.erase, Pos.erase, Neg.erase] using
        Inv.tmEq_pendingFst t
  | .pair t u => by
      simpa [Inv.pendingFst, Inv.erase] using (TmEq.beta_fst t.erase u.erase).symm
termination_by t.nodeSize
decreasing_by all_goals simp [Inv.nodeSize] <;> omega

theorem Inv.tmEq_pendingSnd {Γ : StableCtx sig} {ps : Pending sig}
    {A B : Neg sig.nBases} (t : Inv Γ ps (.neg (.prod A B))) :
    TmEq t.pendingSnd.erase (.snd t.erase) :=
  match t with
  | .caseSum (A := L) (B := R) (ps := rest) l r => by
      simp only [Inv.pendingSnd, Inv.erase]
      let rotL : Rename sig (Pending.eraseAux rest (Γ.erase.snoc L.erase))
          ((Pending.eraseAux rest Γ.erase).snoc L.erase) :=
        rotateHeadToNewest (Δ := Γ.erase) (H := L.erase) rest
      let rotR : Rename sig (Pending.eraseAux rest (Γ.erase.snoc R.erase))
          ((Pending.eraseAux rest Γ.erase).snoc R.erase) :=
        rotateHeadToNewest (Δ := Γ.erase) (H := R.erase) rest
      let out : Rename sig
          ((Pending.eraseAux rest Γ.erase).snoc (.coprod L.erase R.erase))
          (Pending.eraseAux rest (Γ.erase.snoc (.coprod L.erase R.erase))) :=
        rotateNewestToHead (Δ := Γ.erase) (A := (.coprod L.erase R.erase)) rest
      let s : Tm ((Pending.eraseAux rest Γ.erase).snoc (.coprod L.erase R.erase))
          (.coprod L.erase R.erase) := .var .here
      let skipL : Rename sig
          ((Pending.eraseAux rest Γ.erase).snoc L.erase)
          (((Pending.eraseAux rest Γ.erase).snoc (.coprod L.erase R.erase)).snoc L.erase) :=
        Rename.skip1
      let skipR : Rename sig
          ((Pending.eraseAux rest Γ.erase).snoc R.erase)
          (((Pending.eraseAux rest Γ.erase).snoc (.coprod L.erase R.erase)).snoc R.erase) :=
        Rename.skip1
      let bl := Equality.rename skipL (Equality.rename rotL l.erase)
      let br := Equality.rename skipR (Equality.rename rotR r.erase)
      have hl : TmEq
          (Equality.rename skipL
            (Equality.rename rotL l.pendingSnd.erase)) (.snd bl) := by
        simpa [bl, Equality.rename, Goal.erase, Neg.erase, Pos.erase] using
          TmEq.rename skipL (TmEq.rename rotL (Inv.tmEq_pendingSnd l))
      have hr : TmEq
          (Equality.rename skipR
            (Equality.rename rotR r.pendingSnd.erase)) (.snd br) := by
        simpa [br, Equality.rename, Goal.erase, Neg.erase, Pos.erase] using
          TmEq.rename skipR (TmEq.rename rotR (Inv.tmEq_pendingSnd r))
      have hinner : TmEq
          (.case s
            (Equality.rename skipL (Equality.rename rotL l.pendingSnd.erase))
            (Equality.rename skipR (Equality.rename rotR r.pendingSnd.erase)))
          (.snd (.case s bl br)) :=
        TmEq.trans (TmEq.«case» (TmEq.refl s) hl hr)
          (TmEq.cc_snd_case s bl br).symm
      simpa [out, rotL, rotR, skipL, skipR, s, bl, br, Equality.rename,
        eraseInvCtx, Goal.erase, Neg.erase, Pos.erase] using
        TmEq.rename out hinner
  | .abort (ps := rest) => by
      let n := Inv.erase
        (.abort : Inv Γ (.cons .zero rest) (.pos .zero))
      exact TmEq.of_never n _ _
  | .storeAtom t => by
      simpa [Inv.pendingSnd, Inv.erase, eraseInvCtx, StableCtx.erase_snoc,
        StableTy.erase, Pos.erase, Neg.erase] using
        Inv.tmEq_pendingSnd t
  | .storeShift t => by
      simpa [Inv.pendingSnd, Inv.erase, eraseInvCtx, StableCtx.erase_snoc,
        StableTy.erase, Pos.erase, Neg.erase] using
        Inv.tmEq_pendingSnd t
  | .pair t u => by
      simpa [Inv.pendingSnd, Inv.erase] using (TmEq.beta_snd t.erase u.erase).symm
termination_by t.nodeSize
decreasing_by all_goals simp [Inv.nodeSize] <;> omega

theorem Inv.tmEq_pendingShiftToPos {Γ : StableCtx sig} {ps : Pending sig}
    {P : Pos sig.nBases} (t : Inv Γ ps (.neg (.shift P))) :
    TmEq t.pendingShiftToPos.erase t.erase :=
  match t with
  | .caseSum (A := L) (B := R) (ps := rest) l r => by
      simp only [Inv.pendingShiftToPos, Inv.erase]
      let rotL : Rename sig (Pending.eraseAux rest (Γ.erase.snoc L.erase))
          ((Pending.eraseAux rest Γ.erase).snoc L.erase) :=
        rotateHeadToNewest (Δ := Γ.erase) (H := L.erase) rest
      let rotR : Rename sig (Pending.eraseAux rest (Γ.erase.snoc R.erase))
          ((Pending.eraseAux rest Γ.erase).snoc R.erase) :=
        rotateHeadToNewest (Δ := Γ.erase) (H := R.erase) rest
      let out : Rename sig
          ((Pending.eraseAux rest Γ.erase).snoc (.coprod L.erase R.erase))
          (Pending.eraseAux rest (Γ.erase.snoc (.coprod L.erase R.erase))) :=
        rotateNewestToHead (Δ := Γ.erase) (A := (.coprod L.erase R.erase)) rest
      let s : Tm ((Pending.eraseAux rest Γ.erase).snoc (.coprod L.erase R.erase))
          (.coprod L.erase R.erase) := .var .here
      let skipL : Rename sig
          ((Pending.eraseAux rest Γ.erase).snoc L.erase)
          (((Pending.eraseAux rest Γ.erase).snoc (.coprod L.erase R.erase)).snoc L.erase) :=
        Rename.skip1
      let skipR : Rename sig
          ((Pending.eraseAux rest Γ.erase).snoc R.erase)
          (((Pending.eraseAux rest Γ.erase).snoc (.coprod L.erase R.erase)).snoc R.erase) :=
        Rename.skip1
      have hinner := TmEq.«case» (TmEq.refl s)
        (TmEq.rename skipL
          (TmEq.rename rotL (Inv.tmEq_pendingShiftToPos l)))
        (TmEq.rename skipR
          (TmEq.rename rotR (Inv.tmEq_pendingShiftToPos r)))
      simpa [out, rotL, rotR, skipL, skipR, s, Equality.rename, eraseInvCtx,
        Goal.erase, Neg.erase, Pos.erase] using
        TmEq.rename out hinner
  | .abort => by simp [Inv.pendingShiftToPos]; exact TmEq.refl _
  | .storeAtom t => by
      simpa [Inv.pendingShiftToPos, Inv.erase, eraseInvCtx, StableCtx.erase_snoc,
        StableTy.erase, Pos.erase, Neg.erase] using
        Inv.tmEq_pendingShiftToPos t
  | .storeShift t => by
      simpa [Inv.pendingShiftToPos, Inv.erase, eraseInvCtx, StableCtx.erase_snoc,
        StableTy.erase, Pos.erase, Neg.erase] using
        Inv.tmEq_pendingShiftToPos t
  | .focusShift f => by simp [Inv.pendingShiftToPos]; exact TmEq.refl _
termination_by t.nodeSize
decreasing_by all_goals simp [Inv.nodeSize] <;> omega

theorem tmEq_cutStrong {Γ : StableCtx sig} {P : Pos sig.nBases}
    {G : Goal sig.nBases} (p : StrongPos Γ P)
    (k : Inv Γ (.cons P .empty) G) :
    TmEq (cutStrong p k).erase (subst0 k.erase p.erase) := by
  cases p with
  | atomVar x =>
      cases k with
      | storeAtom t =>
          simp only [cutStrong, Inv.asStoreAtom, StrongPos.erase, Inv.erase]
          rw [Inv.erase_rename]
          apply TmEq.of_eq
          change
            rename (StableRename.erase
              (StableRename.replaceNewestAtom x)) t.erase =
            subst0 t.erase (.var x.erase)
          rw [
            rename_eq_of_pointwise
              (StableRename.erase_replaceNewestAtom_apply x),
            subst0_var]
          rfl
  | negVar x =>
      cases k with
      | storeShift t =>
          simp only [cutStrong, Inv.asStoreShift, StrongPos.erase, Inv.erase]
          rw [Inv.erase_rename]
          apply TmEq.of_eq
          change
            rename (StableRename.erase
              (StableRename.replaceNewestNeg x)) t.erase =
            subst0 t.erase (.var x.erase)
          rw [
            rename_eq_of_pointwise
              (StableRename.erase_replaceNewestNeg_apply x),
            subst0_var]
          rfl
  | inl p =>
      cases k with
      | caseSum l r =>
          refine TmEq.trans (tmEq_cutStrong p l) ?_
          refine TmEq.trans (TmEq.beta_case_inl p.erase l.erase r.erase).symm ?_
          apply TmEq.of_eq
          exact (subst0_erase_caseSum_empty l r (.inl p.erase)).symm
  | inr p =>
      cases k with
      | caseSum l r =>
          refine TmEq.trans (tmEq_cutStrong p r) ?_
          refine TmEq.trans (TmEq.beta_case_inr p.erase l.erase r.erase).symm ?_
          apply TmEq.of_eq
          exact (subst0_erase_caseSum_empty l r (.inr p.erase)).symm

theorem tmEq_caseSum_substBelow {Γ : StableCtx sig} {Cut : Neg sig.nBases}
    {A B : Pos sig.nBases} {ps : Pending sig} {G : Goal sig.nBases}
    (l : Inv (Γ.snoc (.neg Cut)) (.cons A ps) G)
    (r : Inv (Γ.snoc (.neg Cut)) (.cons B ps) G)
    (v : Inv Γ .empty (.neg Cut))
    (l' : Inv Γ (.cons A ps) G) (r' : Inv Γ (.cons B ps) G)
    (hl : TmEq l'.erase (substBelowPending l v))
    (hr : TmEq r'.erase (substBelowPending r v)) :
    TmEq (Inv.erase (.caseSum l' r'))
      (substBelowPending (.caseSum l r) v) := by
  let rotL : Rename sig (Pending.eraseAux ps (Γ.erase.snoc A.erase))
      ((Pending.eraseAux ps Γ.erase).snoc A.erase) :=
    rotateHeadToNewest (Δ := Γ.erase) (H := A.erase) ps
  let rotR : Rename sig (Pending.eraseAux ps (Γ.erase.snoc B.erase))
      ((Pending.eraseAux ps Γ.erase).snoc B.erase) :=
    rotateHeadToNewest (Δ := Γ.erase) (H := B.erase) ps
  let out : Rename sig
      ((Pending.eraseAux ps Γ.erase).snoc (.coprod A.erase B.erase))
      (Pending.eraseAux ps (Γ.erase.snoc (.coprod A.erase B.erase))) :=
    rotateNewestToHead (Δ := Γ.erase) (A := (.coprod A.erase B.erase)) ps
  let s : Tm ((Pending.eraseAux ps Γ.erase).snoc (.coprod A.erase B.erase))
      (.coprod A.erase B.erase) := .var .here
  let skipL : Rename sig
      ((Pending.eraseAux ps Γ.erase).snoc A.erase)
      (((Pending.eraseAux ps Γ.erase).snoc (.coprod A.erase B.erase)).snoc A.erase) :=
    Rename.skip1
  let skipR : Rename sig
      ((Pending.eraseAux ps Γ.erase).snoc B.erase)
      (((Pending.eraseAux ps Γ.erase).snoc (.coprod A.erase B.erase)).snoc B.erase) :=
    Rename.skip1
  have hinner := TmEq.«case» (TmEq.refl s)
    (TmEq.rename skipL (TmEq.rename rotL hl))
    (TmEq.rename skipR (TmEq.rename rotR hr))
  have hout := TmEq.rename out hinner
  refine hout.trans (TmEq.of_eq ?_)
  simp only [out, rotL, rotR, skipL, skipR, s, Inv.erase,
    substBelowPending]
  symm
  simp only [Equality.rename, subst]
  congr 1
  · exact Pending.liftSubst_rotateNewest_here ps (Subst.single v.erase)
  · exact subst_case_branch_cut
      (S := .sum A B) (A := A) ps (Subst.single v.erase) l.erase
  · exact subst_case_branch_cut
      (S := .sum A B) (A := B) ps (Subst.single v.erase) r.erase

theorem TmEq.subst0_case_cut {Γ : Ctx sig}
    {A B P C : Object sig.nBases}
    (s : Tm Γ (.coprod A B))
    (l : Tm (Γ.snoc A) P) (r : Tm (Γ.snoc B) P)
    (k : Tm (Γ.snoc P) C) :
    TmEq (subst0 k (.case s l r))
      (.case s
        (subst0 (Equality.rename (Rename.ext Rename.weaken) k) l)
        (subst0 (Equality.rename (Rename.ext Rename.weaken) k) r)) := by
  refine ⟨?_⟩
  intro X env
  rw [interpret_qm_subst0]
  simp only [interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib]
  rw [cs_pair_diag_comp, CategoryTheory.Category.assoc, cs_comm_conv]
  rw [interpret_qm_subst0, interpret_qm_subst0]
  erw [interpret_qm_skip1, interpret_qm_skip1]
  simp only [← CategoryTheory.Category.assoc, ← cs_pair_fst_eq]

theorem Pending.renameEraseAux_weakenBase_apply {Γ Δ : Ctx sig}
    (ρ : Rename sig Γ Δ) (ps : Pending sig)
    {D : Object sig.nBases} (y : Var Γ D) :
    renameEraseAux ρ ps (ps.weakenBase y) = ps.weakenBase (ρ y) := by
  induction ps generalizing Γ Δ with
  | empty => rfl
  | cons Q qs ih =>
      simp only [renameEraseAux, Pending.weakenBase]
      exact ih (Rename.ext ρ) (Rename.weaken y)

theorem Pending.rotateHead_weakenBase_apply {Γ : Ctx sig}
    {A : Pos sig.nBases} (ps : Pending sig)
    {D : Object sig.nBases} (y : Var Γ D) :
    rotateHeadToNewest (Δ := Γ) (H := A.erase) ps
        ((Pending.cons A ps).weakenBase y) =
      Rename.weaken (ps.weakenBase y) := by
  induction ps generalizing Γ with
  | empty => rfl
  | cons Q qs ih =>
      simp only [Pending.weakenBase, rotateHeadToNewest, renameComp]
      rw [Pending.renameEraseAux_weakenBase_apply]
      exact ih (Rename.weaken y)

theorem Pending.rotateNewest_weakenBase_apply {Γ : Ctx sig}
    {S : Pos sig.nBases} (ps : Pending sig)
    {D : Object sig.nBases} (y : Var Γ D) :
    rotateNewestToHead (Δ := Γ) (A := S.erase) ps
        (Rename.weaken (ps.weakenBase y)) =
      (Pending.cons S ps).weakenBase y := by
  induction ps generalizing Γ with
  | empty => rfl
  | cons Q qs ih =>
      simp only [Pending.weakenBase, rotateNewestToHead, renameComp]
      calc
        _ = renameEraseAux
              (Rename.exchange (Γ := Γ) (A := Q.erase) (B := S.erase)) qs
              ((Pending.cons S qs).weakenBase (Rename.weaken y)) :=
          congrArg
            (renameEraseAux
              (Rename.exchange (Γ := Γ) (A := Q.erase) (B := S.erase)) qs)
            (ih (Γ := Γ.snoc Q.erase) (Rename.weaken y))
        _ = _ := by
          simp only [Pending.weakenBase, renameComp]
          rw [Pending.renameEraseAux_weakenBase_apply]
          rfl

theorem Pending.weakenBase_case_apply {Γ : Ctx sig}
    {S A : Pos sig.nBases} (ps : Pending sig)
    {D : Object sig.nBases} (y : Var Γ D) :
    Rename.weaken ((Pending.cons S ps).weakenBase y) =
      Rename.ext (rotateNewestToHead (Δ := Γ) (A := S.erase) ps)
        (Rename.skip1
          (rotateHeadToNewest (Δ := Γ) (H := A.erase) ps
            ((Pending.cons A ps).weakenBase y))) := by
  rw [Pending.rotateHead_weakenBase_apply]
  change Rename.weaken ((Pending.cons S ps).weakenBase y) =
    Rename.ext (rotateNewestToHead (Δ := Γ) (A := S.erase) ps)
      (Rename.skip1 (Rename.weaken (ps.weakenBase y)))
  change Rename.weaken ((Pending.cons S ps).weakenBase y) =
    Rename.weaken
      (rotateNewestToHead (Δ := Γ) (A := S.erase) ps
        (Rename.weaken (ps.weakenBase y)))
  exact congrArg Rename.weaken
    (Pending.rotateNewest_weakenBase_apply ps y).symm

theorem bind_case_branch_cut {Γ : Ctx sig}
    {S A P : Pos sig.nBases} {ps : Pending sig}
    {C : Object sig.nBases}
    (l : Tm (Pending.eraseAux ps (Γ.snoc A.erase)) P.erase)
    (k : Tm (Γ.snoc P.erase) C) :
    subst0
      (rename (Rename.ext Rename.weaken)
        (rename (Rename.ext (Pending.weakenBase (.cons S ps))) k))
      (rename (Rename.ext
          (rotateNewestToHead (Δ := Γ) (A := S.erase) ps))
        (rename (Rename.skip1 (Γ := Pending.eraseAux ps Γ)
            (A := A.erase) (B := S.erase))
          (rename (rotateHeadToNewest (Δ := Γ) (H := A.erase) ps) l))) =
    rename (Rename.ext
        (rotateNewestToHead (Δ := Γ) (A := S.erase) ps))
      (rename (Rename.skip1 (Γ := Pending.eraseAux ps Γ)
          (A := A.erase) (B := S.erase))
        (rename (rotateHeadToNewest (Δ := Γ) (H := A.erase) ps)
          (subst0
            (rename (Rename.ext (Pending.weakenBase (.cons A ps))) k) l))) := by
  simp only [subst0]
  rw [subst_rename, subst_rename, subst_rename]
  rw [rename_subst, rename_subst, rename_subst]
  apply subst_eq_of_pointwise
  intro D x
  cases x with
  | here => rfl
  | there y =>
      simp only [Subst.compRename, renameSubst, Subst.single, Rename.ext]
      change Tm.var (Rename.weaken ((Pending.cons S ps).weakenBase y)) =
        rename (Rename.ext (rotateNewestToHead (Δ := Γ) (A := S.erase) ps))
          (rename (Rename.skip1 (Γ := Pending.eraseAux ps Γ)
              (A := A.erase) (B := S.erase))
            (rename (rotateHeadToNewest (Δ := Γ) (H := A.erase) ps)
              (.var ((Pending.cons A ps).weakenBase y))))
      simp only [Equality.rename]
      exact congrArg Tm.var (Pending.weakenBase_case_apply ps y)

set_option linter.tacticCheckInstances false in
theorem tmEq_caseSum_bindBelow {Γ : StableCtx sig}
    {A B P : Pos sig.nBases} {ps : Pending sig} {G : Goal sig.nBases}
    (l : Inv Γ (.cons A ps) (.pos P))
    (r : Inv Γ (.cons B ps) (.pos P))
    (k : Inv Γ (.cons P .empty) G)
    (l' : Inv Γ (.cons A ps) G) (r' : Inv Γ (.cons B ps) G)
    (hl : TmEq l'.erase (bindBelowPending l k))
    (hr : TmEq r'.erase (bindBelowPending r k)) :
    TmEq (Inv.erase (.caseSum l' r'))
      (bindBelowPending (.caseSum l r) k) := by
  let rotL : Rename sig (Pending.eraseAux ps (Γ.erase.snoc A.erase))
      ((Pending.eraseAux ps Γ.erase).snoc A.erase) :=
    rotateHeadToNewest (Δ := Γ.erase) (H := A.erase) ps
  let rotR : Rename sig (Pending.eraseAux ps (Γ.erase.snoc B.erase))
      ((Pending.eraseAux ps Γ.erase).snoc B.erase) :=
    rotateHeadToNewest (Δ := Γ.erase) (H := B.erase) ps
  let out : Rename sig
      ((Pending.eraseAux ps Γ.erase).snoc (.coprod A.erase B.erase))
      (Pending.eraseAux ps (Γ.erase.snoc (.coprod A.erase B.erase))) :=
    rotateNewestToHead (Δ := Γ.erase) (A := (.coprod A.erase B.erase)) ps
  let s : Tm ((Pending.eraseAux ps Γ.erase).snoc (.coprod A.erase B.erase))
      (.coprod A.erase B.erase) := .var .here
  let skipL : Rename sig
      ((Pending.eraseAux ps Γ.erase).snoc A.erase)
      (((Pending.eraseAux ps Γ.erase).snoc (.coprod A.erase B.erase)).snoc A.erase) :=
    Rename.skip1
  let skipR : Rename sig
      ((Pending.eraseAux ps Γ.erase).snoc B.erase)
      (((Pending.eraseAux ps Γ.erase).snoc (.coprod A.erase B.erase)).snoc B.erase) :=
    Rename.skip1
  have hinner := TmEq.«case» (TmEq.refl s)
    (TmEq.rename skipL (TmEq.rename rotL hl))
    (TmEq.rename skipR (TmEq.rename rotR hr))
  have hout := TmEq.rename out hinner
  refine hout.trans ?_
  have hcomm := (TmEq.subst0_case_cut
    (rename out s)
    (rename (Rename.ext out) (rename skipL (rename rotL l.erase)))
    (rename (Rename.ext out) (rename skipR (rename rotR r.erase)))
    (rename (Rename.ext (Pending.weakenBase (.cons (.sum A B) ps)))
      k.erase)).symm
  have hbranches := TmEq.«case» (TmEq.refl (rename out s))
    (TmEq.of_eq (bind_case_branch_cut
      (S := .sum A B) (A := A) (ps := ps) l.erase k.erase))
    (TmEq.of_eq (bind_case_branch_cut
      (S := .sum A B) (A := B) (ps := ps) r.erase k.erase))
  have h := hbranches.symm.trans hcomm
  simp only [out, rotL, rotR, skipL, skipR, s, Inv.erase,
    bindBelowPending, Equality.rename]
  convert h using 1 <;> rfl

theorem subst0_rename_ext_weaken_here_cut {Γ : Ctx sig}
    {A C : Object sig.nBases} (t : Tm (Γ.snoc A) C) :
    subst0 (rename (Rename.ext Rename.weaken) t) (.var .here) = t := by
  simp only [subst0]
  rw [subst_rename]
  refine (subst_eq_of_pointwise (τ := fun {_} => Subst.ids) ?_ t).trans
    (subst_ids t)
  intro D x
  cases x <;> rfl

theorem subst0_rename_ext_subst_injLeft_cut {Γ Δ : Ctx sig}
    {A B C : Object sig.nBases} (ρ : Rename sig Γ Δ)
    (t : Tm (Γ.snoc (.coprod A B)) C) (p : Tm Δ A) :
    subst0 (rename (Rename.ext ρ) (subst Subst.injLeft t)) p =
      subst0 (rename (Rename.ext ρ) t) (.inl p) := by
  simp only [subst0]
  rw [rename_subst, subst_comp, subst_rename]
  apply subst_eq_of_pointwise
  intro D x
  cases x <;> rfl

theorem subst0_rename_ext_subst_injRight_cut {Γ Δ : Ctx sig}
    {A B C : Object sig.nBases} (ρ : Rename sig Γ Δ)
    (t : Tm (Γ.snoc (.coprod A B)) C) (p : Tm Δ B) :
    subst0 (rename (Rename.ext ρ) (subst Subst.injRight t)) p =
      subst0 (rename (Rename.ext ρ) t) (.inr p) := by
  simp only [subst0]
  rw [rename_subst, subst_comp, subst_rename]
  apply subst_eq_of_pointwise
  intro D x
  cases x <;> rfl

theorem rename_ext_weaken_cut {Γ Δ : Ctx sig}
    {A B : Object sig.nBases} (ρ : Rename sig Γ Δ) (t : Tm Γ B) :
    rename (Rename.ext (A := A) ρ) (weakenTerm t) =
      weakenTerm (rename ρ t) := by
  simp only [weakenTerm_eq_rename]
  rw [rename_comp, rename_comp]
  apply rename_eq_of_pointwise
  intro D x
  rfl

theorem subst0_rename_ext_app_var_cut {Γ Δ : Ctx sig}
    {A C : Object sig.nBases} (ρ : Rename sig Γ Δ)
    (f : Tm Γ (.exp A C)) (p : Tm Δ A) :
    subst0 (rename (Rename.ext ρ) (.app (weakenTerm f) (.var .here))) p =
      .app (rename ρ f) p := by
  change Tm.app (subst0 (rename (Rename.ext ρ) (weakenTerm f)) p) p = _
  rw [rename_ext_weaken_cut, subst0_weakenTerm]

theorem rename_ext_erase_weaken_cut {Γ : StableCtx sig}
    {S : StableTy sig.nBases} {C : Object sig.nBases}
    (t : Tm (Γ.erase.snoc S.erase) C) :
    rename (Rename.ext (StableRename.erase
      (StableRename.weaken (Γ := Γ) (S := S)))) t =
      rename (Rename.ext Rename.weaken) t := by
  apply rename_eq_of_pointwise
  intro D x
  cases x with
  | here => rfl
  | there y => exact congrArg Var.there (StableRename.erase_weaken_apply y)

theorem subst0_rename_ext_erase_weaken_here_cut {Γ : StableCtx sig}
    {S : StableTy sig.nBases} {C : Object sig.nBases}
    (t : Tm (Γ.erase.snoc S.erase) C) :
    subst0 (rename (Rename.ext (StableRename.erase
      (StableRename.weaken (Γ := Γ) (S := S)))) t)
        (.var (StableVar.erase (.here : StableVar (Γ.snoc S) S))) = t := by
  rw [rename_ext_erase_weaken_cut]
  exact subst0_rename_ext_weaken_here_cut t

theorem case_committed_eta_cut {Γ : Ctx sig}
    {A B C : Object sig.nBases} (t : Tm (Γ.snoc (.coprod A B)) C) :
    TmEq
      (.case (.var .here)
        (rename (Rename.skip1 (Γ := Γ) (A := A) (B := .coprod A B))
          (subst (Subst.injLeft (A := A) (B := B)) t))
        (rename (Rename.skip1 (Γ := Γ) (A := B) (B := .coprod A B))
          (subst (Subst.injRight (A := A) (B := B)) t)))
      t := by
  let w : Tm ((Γ.snoc (.coprod A B)).snoc (.coprod A B)) C :=
    rename (Rename.ext (Rename.weaken (Γ := Γ) (A := .coprod A B))) t
  have h := TmEq.sum_eta
    (Tm.var (.here : Var (Γ.snoc (.coprod A B)) (.coprod A B))) w
  have hL :
      subst (Subst.injLeft (Γ := Γ.snoc (.coprod A B)) (A := A) (B := B)) w =
        rename (Rename.skip1 (Γ := Γ) (A := A) (B := .coprod A B))
          (subst (Subst.injLeft (Γ := Γ) (A := A) (B := B)) t) := by
    simp only [w, subst_rename, rename_subst]
    apply subst_eq_of_pointwise
    intro D x
    cases x <;> rfl
  have hR :
      subst (Subst.injRight (Γ := Γ.snoc (.coprod A B)) (A := A) (B := B)) w =
        rename (Rename.skip1 (Γ := Γ) (A := B) (B := .coprod A B))
          (subst (Subst.injRight (Γ := Γ) (A := A) (B := B)) t) := by
    simp only [w, subst_rename, rename_subst]
    apply subst_eq_of_pointwise
    intro D x
    cases x <;> rfl
  rw [hL, hR] at h
  refine h.trans (TmEq.of_eq (subst0_rename_ext_weaken_here_cut t))

mutual
theorem tmEq_etaNeg (N : Neg sig.nBases) {Γ : StableCtx sig}
    (n : NegNeu Γ N) : TmEq (etaNeg N n).erase n.erase := by
  match N with
  | .one =>
      simp only [etaNeg, Inv.erase]
      exact (TmEq.eta_unit n.erase).symm
  | .prod A B =>
      simp only [etaNeg, Inv.erase]
      exact (TmEq.pair (tmEq_etaNeg A (.fst n))
        (tmEq_etaNeg B (.snd n))).trans (TmEq.eta_prod n.erase)
  | .arr P M =>
      let t : Tm (Γ.erase.snoc P.erase) M.erase :=
        .app (weakenTerm n.erase) (.var .here)
      have hb := tmEq_withPendingPos P
        (fun ρ p => etaNeg M (.app (NegNeu.rename ρ n) p)) t (by
          intro Δ ρ p
          refine (tmEq_etaNeg M (.app (NegNeu.rename ρ n) p)).trans
            (TmEq.of_eq ?_)
          simp only [NegNeu.erase, t]
          rw [NegNeu.erase_rename]
          exact (subst0_rename_ext_app_var_cut
            (StableRename.erase ρ) n.erase p.erase).symm)
      simpa only [etaNeg, Inv.erase, eraseInvCtx, Pending.eraseAux,
        Goal.erase, Neg.erase, Pos.erase, t] using
        (TmEq.lam hb).trans (TmEq.eta_lam n.erase)
  | .shift P =>
      let t : Tm (Γ.erase.snoc P.erase) P.erase := .var .here
      have hb := tmEq_withPendingPos P
        (fun _ p => .focusPos (.up p)) t (by
          intro Δ ρ p
          simp only [Inv.erase, Foc.erase, PosNeu.erase, t]
          exact TmEq.refl _
        )
      simpa only [etaNeg, Inv.erase, Foc.erase, eraseInvCtx, Pending.eraseAux,
        Goal.erase, Neg.erase, Pos.erase, t] using
        (TmEq.subst0_congr hb (TmEq.refl n.erase)).trans
          (TmEq.of_eq (subst0_here n.erase))
termination_by negCutSize N
decreasing_by all_goals simp [negCutSize, posCutSize] <;> omega

theorem tmEq_withPendingPos (P : Pos sig.nBases) {Γ : StableCtx sig}
    {G : Goal sig.nBases}
    (k : ∀ {Δ : StableCtx sig}, StableRename Γ Δ →
      PosNeu Δ P → Inv Δ .empty G)
    (t : Tm (Γ.erase.snoc P.erase) G.erase)
    (hk : ∀ {Δ : StableCtx sig} (ρ : StableRename Γ Δ) (p : PosNeu Δ P),
      TmEq (k ρ p).erase
        (subst0 (rename (Rename.ext (StableRename.erase ρ)) t) p.erase)) :
    TmEq (withPendingPos P k).erase t := by
  match P with
  | .atom q =>
      have h := hk StableRename.weaken (.atom .here)
      simp only [PosNeu.erase] at h
      simpa only [withPendingPos, Inv.erase, PosNeu.erase,
        StableCtx.erase_snoc, StableTy.erase, eraseInvCtx,
        Pending.eraseAux, Pos.erase] using
        h.trans (TmEq.of_eq
          (subst0_rename_ext_erase_weaken_here_cut
            (Γ := Γ) (S := .atom q) t))
  | .zero =>
      let z : Tm (Γ.erase.snoc .never) .never := .var .here
      exact TmEq.of_never z _ _
  | .sum A B =>
      let tL := subst (Subst.injLeft (A := A.erase) (B := B.erase)) t
      let tR := subst (Subst.injRight (A := A.erase) (B := B.erase)) t
      have hL := tmEq_withPendingPos A
        (fun ρ p => k ρ (.inl p)) tL (by
          intro Δ ρ p
          exact (hk ρ (.inl p)).trans (TmEq.of_eq
            (subst0_rename_ext_subst_injLeft_cut
              (StableRename.erase ρ) t p.erase).symm))
      have hR := tmEq_withPendingPos B
        (fun ρ p => k ρ (.inr p)) tR (by
          intro Δ ρ p
          exact (hk ρ (.inr p)).trans (TmEq.of_eq
            (subst0_rename_ext_subst_injRight_cut
              (StableRename.erase ρ) t p.erase).symm))
      have hc := TmEq.«case»
        (TmEq.refl
          (Tm.var (.here : Var (Γ.erase.snoc (.coprod A.erase B.erase))
            (.coprod A.erase B.erase))))
        (TmEq.rename Rename.skip1 hL)
        (TmEq.rename Rename.skip1 hR)
      change TmEq (Inv.erase (.caseSum
        (withPendingPos A fun ρ p => k ρ (.inl p))
        (withPendingPos B fun ρ p => k ρ (.inr p)))) t
      rw [erase_caseSum_empty_eq]
      exact hc.trans (case_committed_eta_cut t)
  | .shift M =>
      have h := hk StableRename.weaken (.shift (etaNeg M (.var .here)))
      simp only [PosNeu.erase] at h
      have hη := tmEq_etaNeg M (.var (.here : StableVar (Γ.snoc (.neg M)) (.neg M)))
      refine ?_
      simpa only [withPendingPos, Inv.erase, PosNeu.erase,
        StableCtx.erase_snoc, StableTy.erase, eraseInvCtx,
        Pending.eraseAux, Pos.erase, Neg.erase] using
        h.trans ((TmEq.subst0_congr (TmEq.refl _) hη).trans
          (TmEq.of_eq (subst0_rename_ext_erase_weaken_here_cut
            (Γ := Γ) (S := .neg M) t)))
termination_by posCutSize P
decreasing_by all_goals simp [negCutSize, posCutSize] <;> omega
end

theorem StrongPos.erase_rename {Γ Δ : StableCtx sig}
    {P : Pos sig.nBases} (ρ : StableRename Γ Δ) (p : StrongPos Γ P) :
    (p.rename ρ).erase = Equality.rename (StableRename.erase ρ) p.erase := by
  induction p with
  | negVar x | atomVar x => exact congrArg Tm.var (StableVar.erase_rename ρ x)
  | inl p ih => exact congrArg Tm.inl ih
  | inr p ih => exact congrArg Tm.inr ih

theorem rename_skip1_weakenTerm_cut {Γ : Ctx sig}
    {A B C : Object sig.nBases} (t : Tm Γ C) :
    Equality.rename (Rename.skip1 (Γ := Γ) (A := A) (B := B))
        (weakenTerm t) =
      weakenTerm (A := A) (weakenTerm (A := B) t) := by
  simp only [weakenTerm_eq_rename, rename_comp]
  apply rename_eq_of_pointwise
  intro D x
  rfl

theorem Inv.tmEq_pendingAppStrongOne {Γ : StableCtx sig}
    {P A : Pos sig.nBases} {N : Neg sig.nBases}
    (f : Inv Γ (.cons P .empty) (.neg (.arr A N))) (a : StrongPos Γ A) :
    TmEq (pendingAppStrong f a).erase
      (.app f.erase (weakenTerm a.erase)) := by
  match f with
  | .caseSum (A := L) (B := R) l r =>
      have hl := Inv.tmEq_pendingAppStrongOne l a
      have hr := Inv.tmEq_pendingAppStrongOne r a
      simp only [pendingAppStrong]
      rw [erase_caseSum_empty_eq, erase_caseSum_empty_eq]
      have hc := TmEq.«case»
        (TmEq.refl
          (Tm.var (.here : Var (Γ.erase.snoc (.coprod L.erase R.erase))
            (.coprod L.erase R.erase))))
        (TmEq.rename Rename.skip1 hl) (TmEq.rename Rename.skip1 hr)
      simp only [Goal.erase] at hc ⊢
      refine hc.trans ?_
      have happ := (TmEq.cc_app_case (.var .here)
          (Equality.rename Rename.skip1 l.erase)
          (Equality.rename Rename.skip1 r.erase)
          (weakenTerm a.erase)).symm
      convert happ using 1 <;>
        simp only [Equality.rename, rename_skip1_weakenTerm_cut,
          Goal.erase, Neg.erase] <;> rfl
  | .abort =>
      let z := Inv.erase
        (.abort : Inv Γ (.cons .zero .empty) (.pos .zero))
      exact TmEq.of_never z _ _
  | .storeAtom t =>
      cases t with
      | lam body =>
          have hs := tmEq_cutStrong
            (StrongPos.rename StableRename.weaken a) body
          rw [StrongPos.erase_rename] at hs
          rw [rename_eq_of_pointwise
            (fun x => StableRename.erase_weaken_apply x)] at hs
          simp only [pendingAppStrong, Inv.erase, weakenTerm_eq_rename,
            eraseInvCtx, Pending.eraseAux, StableCtx.erase_snoc,
            StableTy.erase, Pos.erase]
          convert hs.trans (TmEq.beta_app body.erase
            (weakenTerm a.erase)).symm using 1 <;> rfl
  | .storeShift t =>
      cases t with
      | lam body =>
          have hs := tmEq_cutStrong
            (StrongPos.rename StableRename.weaken a) body
          rw [StrongPos.erase_rename] at hs
          rw [rename_eq_of_pointwise
            (fun x => StableRename.erase_weaken_apply x)] at hs
          simp only [pendingAppStrong, Inv.erase, weakenTerm_eq_rename,
            eraseInvCtx, Pending.eraseAux, StableCtx.erase_snoc,
            StableTy.erase, Pos.erase, Neg.erase]
          convert hs.trans (TmEq.beta_app body.erase
            (weakenTerm a.erase)).symm using 1 <;> rfl
termination_by f.nodeSize
decreasing_by all_goals simp [Inv.nodeSize] <;> omega

theorem tmEq_withPendingStrong (P : Pos sig.nBases) {Γ : StableCtx sig}
    {G : Goal sig.nBases}
    (k : ∀ {Δ : StableCtx sig}, StableRename Γ Δ →
      (p : PosNeu Δ P) → StrongPos Δ P → Inv Δ .empty G)
    (t : Tm (Γ.erase.snoc P.erase) G.erase)
    (hk : ∀ {Δ : StableCtx sig} (ρ : StableRename Γ Δ)
      (p : PosNeu Δ P) (sp : StrongPos Δ P),
      TmEq p.erase sp.erase →
      TmEq (k ρ p sp).erase
        (subst0 (rename (Rename.ext (StableRename.erase ρ)) t) p.erase)) :
    TmEq (withPendingStrong P k).erase t := by
  match P with
  | .atom q =>
      have h := hk StableRename.weaken (.atom .here) (.atomVar .here)
        (TmEq.refl _)
      simp only [PosNeu.erase] at h
      simpa only [withPendingStrong, Inv.erase, eraseInvCtx, Pending.eraseAux,
        StableCtx.erase_snoc, StableTy.erase, Pos.erase] using
        h.trans (TmEq.of_eq (subst0_rename_ext_erase_weaken_here_cut
          (Γ := Γ) (S := .atom q) t))
  | .zero =>
      let z : Tm (Γ.erase.snoc .never) .never := .var .here
      exact TmEq.of_never z _ _
  | .sum A B =>
      let tL := subst (Subst.injLeft (A := A.erase) (B := B.erase)) t
      let tR := subst (Subst.injRight (A := A.erase) (B := B.erase)) t
      have hL := tmEq_withPendingStrong A
        (fun ρ p sp => k ρ (.inl p) (.inl sp)) tL (by
          intro Δ ρ p sp hps
          exact (hk ρ (.inl p) (.inl sp) (TmEq.inl hps)).trans (TmEq.of_eq
            (subst0_rename_ext_subst_injLeft_cut
              (StableRename.erase ρ) t p.erase).symm))
      have hR := tmEq_withPendingStrong B
        (fun ρ p sp => k ρ (.inr p) (.inr sp)) tR (by
          intro Δ ρ p sp hps
          exact (hk ρ (.inr p) (.inr sp) (TmEq.inr hps)).trans (TmEq.of_eq
            (subst0_rename_ext_subst_injRight_cut
              (StableRename.erase ρ) t p.erase).symm))
      have hc := TmEq.«case»
        (TmEq.refl (Tm.var (.here : Var
          (Γ.erase.snoc (.coprod A.erase B.erase)) (.coprod A.erase B.erase))))
        (TmEq.rename Rename.skip1 hL) (TmEq.rename Rename.skip1 hR)
      change TmEq (Inv.erase (.caseSum
        (withPendingStrong A fun ρ p sp => k ρ (.inl p) (.inl sp))
        (withPendingStrong B fun ρ p sp => k ρ (.inr p) (.inr sp)))) t
      rw [erase_caseSum_empty_eq]
      exact hc.trans (case_committed_eta_cut t)
  | .shift M =>
      have hη := tmEq_etaNeg M
        (.var (.here : StableVar (Γ.snoc (.neg M)) (.neg M)))
      have h := hk StableRename.weaken
        (.shift (etaNeg M (.var .here))) (.negVar .here) hη
      simp only [PosNeu.erase] at h
      simpa only [withPendingStrong, Inv.erase, eraseInvCtx, Pending.eraseAux,
        StableCtx.erase_snoc, StableTy.erase, Pos.erase, Neg.erase] using
        h.trans ((TmEq.subst0_congr (TmEq.refl _) hη).trans
          (TmEq.of_eq (subst0_rename_ext_erase_weaken_here_cut
            (Γ := Γ) (S := .neg M) t)))
termination_by posCutSize P
decreasing_by all_goals simp [posCutSize] <;> omega

theorem tmEq_bindAfterShift {P Q : Pos sig.nBases} (bound : Nat)
    (bind : ∀ {Γ : StableCtx sig} {qs : Pending sig} {G : Goal sig.nBases},
      (d : Inv Γ qs (.pos P)) → d.nodeSize ≤ bound →
      Inv Γ (.cons P .empty) G → Inv Γ qs G)
    (hbind : ∀ {Γ : StableCtx sig} {qs : Pending sig} {G : Goal sig.nBases}
      (d : Inv Γ qs (.pos P)) (h : d.nodeSize ≤ bound)
      (k : Inv Γ (.cons P .empty) G),
      TmEq (bind d h k).erase (bindBelowPending d k))
    {Γ : StableCtx sig} (n : NegNeu Γ (.shift Q))
    (d : Inv Γ (.cons Q .empty) (.pos P)) (h : d.nodeSize ≤ bound)
    {G : Goal sig.nBases} (k : Inv Γ (.cons P .empty) G) :
    TmEq (subst0 (bind d h k).erase n.erase)
      (subst0 k.erase (subst0 d.erase n.erase)) := by
  refine (TmEq.subst0_congr (hbind d h k) (TmEq.refl _)).trans ?_
  have hren :
      rename (Rename.ext (Pending.weakenBase (.cons Q .empty))) k.erase =
        rename (Rename.ext Rename.weaken) k.erase := by
    apply rename_eq_of_pointwise
    intro D x
    cases x <;> rfl
  unfold bindBelowPending
  refine (TmEq.subst0_congr
    (TmEq.subst0_congr (TmEq.of_eq hren) (TmEq.refl _)) (TmEq.refl _)).trans ?_
  have hc := subst0_subst0_comm_cut
    (rename (Rename.ext Rename.weaken) k.erase) d.erase n.erase
  have hdrop : subst (Subst.exts (Subst.single n.erase))
      (rename (Rename.ext Rename.weaken) k.erase) = k.erase := by
    exact subst_exts_single_rename_skip1_cut k.erase n.erase
  exact (TmEq.of_eq hc.symm).trans
    (TmEq.subst0_congr (TmEq.of_eq hdrop) (TmEq.refl _))

theorem tmEq_composeShiftSized {P : Pos sig.nBases} (bound : Nat)
    (bind : ∀ {Γ : StableCtx sig} {qs : Pending sig} {G : Goal sig.nBases},
      (d : Inv Γ qs (.pos P)) → d.nodeSize ≤ bound →
      Inv Γ (.cons P .empty) G → Inv Γ qs G)
    (hbind : ∀ {Γ : StableCtx sig} {qs : Pending sig} {G : Goal sig.nBases}
      (d : Inv Γ qs (.pos P)) (h : d.nodeSize ≤ bound)
      (k : Inv Γ (.cons P .empty) G),
      TmEq (bind d h k).erase (bindBelowPending d k))
    {Γ : StableCtx sig} {Q : Pos sig.nBases} (G : Goal sig.nBases)
    (n : NegNeu Γ (.shift Q)) (d : Inv Γ (.cons Q .empty) (.pos P))
    (h : d.nodeSize ≤ bound) (k : Inv Γ (.cons P .empty) G) :
    TmEq (composeShiftSized bound bind G n d h k).erase
      (subst0 k.erase (subst0 d.erase n.erase)) := by
  match G with
  | .pos _ =>
      simp only [composeShiftSized, Inv.erase, Foc.erase]
      convert tmEq_bindAfterShift bound bind hbind n d h k using 1 <;> rfl
  | .neg .one =>
      simp only [composeShiftSized, Inv.erase]
      exact (TmEq.eta_unit _).symm
  | .neg (.prod A B) =>
      simp only [composeShiftSized, Inv.erase]
      refine (TmEq.pair
        (tmEq_composeShiftSized bound bind hbind (.neg A) n d h k.pendingFst)
        (tmEq_composeShiftSized bound bind hbind (.neg B) n d h k.pendingSnd)).trans ?_
      exact (TmEq.pair
        (TmEq.subst0_congr (Inv.tmEq_pendingFst k) (TmEq.refl _))
        (TmEq.subst0_congr (Inv.tmEq_pendingSnd k) (TmEq.refl _))).trans
          (TmEq.eta_prod _)
  | .neg (.arr A N) =>
      let z := subst0 k.erase (subst0 d.erase n.erase)
      let t : Tm (Γ.erase.snoc A.erase) N.erase :=
        .app (weakenTerm z) (.var .here)
      have hb := tmEq_withPendingStrong A
        (fun ρ _ sp => composeShiftSized bound bind (.neg N)
          (NegNeu.rename ρ n) (Inv.rename ρ d) (by simpa using h)
          (pendingAppStrong (Inv.rename ρ k) sp)) t (by
            intro Δ ρ p sp hps
            have hi := tmEq_composeShiftSized bound bind hbind (.neg N)
              (NegNeu.rename ρ n) (Inv.rename ρ d) (by simpa using h)
              (pendingAppStrong (Inv.rename ρ k) sp)
            refine hi.trans ?_
            refine (TmEq.subst0_congr
              (Inv.tmEq_pendingAppStrongOne (Inv.rename ρ k) sp)
              (TmEq.refl _)).trans ?_
            let x := subst0 (Inv.rename ρ d).erase (NegNeu.rename ρ n).erase
            have happSub : subst0
                (.app (Inv.rename ρ k).erase (weakenTerm sp.erase)) x =
                .app (subst0 (Inv.rename ρ k).erase x) sp.erase := by
              change Tm.app (subst0 (Inv.rename ρ k).erase x)
                (subst0 (weakenTerm sp.erase) x) = _
              rw [subst0_weakenTerm]
            refine (TmEq.of_eq happSub).trans ?_
            have hz : subst0 (Inv.rename ρ k).erase
                (subst0 (Inv.rename ρ d).erase (NegNeu.rename ρ n).erase) =
                rename (StableRename.erase ρ) z := by
              rw [Inv.erase_rename, Inv.erase_rename, NegNeu.erase_rename]
              exact (congrArg (subst0 (rename (Rename.ext
                (StableRename.erase ρ)) k.erase))
                  (rename_subst0 (StableRename.erase ρ) d.erase n.erase).symm).trans
                (rename_subst0 (StableRename.erase ρ) k.erase
                  (subst0 d.erase n.erase)).symm
            refine (TmEq.app (TmEq.of_eq hz) hps.symm).trans (TmEq.of_eq ?_)
            simp only [t]
            exact (subst0_rename_ext_app_var_cut
              (StableRename.erase ρ) z p.erase).symm)
      simpa only [composeShiftSized, Inv.erase, t, z, eraseInvCtx,
        Pending.eraseAux, Goal.erase, Neg.erase] using
        (TmEq.lam hb).trans (TmEq.eta_lam z)
  | .neg (.shift R) =>
      simpa only [composeShiftSized, Inv.erase, Foc.erase, Goal.erase,
        Neg.erase, Pos.erase, eraseInvCtx, Pending.eraseAux] using
        (tmEq_bindAfterShift bound bind hbind n d h k.pendingShiftToPos).trans
          (TmEq.subst0_congr (Inv.tmEq_pendingShiftToPos k) (TmEq.refl _))
termination_by match G with | .pos _ => 0 | .neg N => negCutSize N
decreasing_by all_goals simp [negCutSize] <;> omega

/-! ### One semantic contract for every recursive cut call -/

def CutCall.Sound : (c : CutCall sig) → Prop
  | .bind d k => TmEq (cutEval (.bind d k)).erase (bindBelowPending d k)
  | .appValue f a =>
      TmEq (cutEval (.appValue f a)).erase (.app f.erase a.erase)
  | .neu n v =>
      TmEq (NegSubstResult.erase (cutEval (.neu n v))) (subst0 n.erase v.erase)
  | .pos p v => TmEq (cutEval (.pos p v)).erase (subst0 p.erase v.erase)
  | .foc f v => TmEq (cutEval (.foc f v)).erase (subst0 f.erase v.erase)
  | .inv t v => TmEq (cutEval (.inv t v)).erase (substBelowPending t v)

theorem tmEq_cutEval : (c : CutCall sig) → c.Sound := by
  intro c
  fun_induction cutEval c
  all_goals simp only [CutCall.Sound] at *
  case case1 =>
    rw [cutEval]
    exact TmEq.refl _
  case case2 =>
    rw [cutEval]
    exact TmEq.refl _
  case case3 x n n' h ih =>
    rw [cutEval, h]
    rw [h] at ih
    convert TmEq.fst ih using 1 <;> rfl
  case case4 x n w hw h ih =>
    rw [cutEval, h]
    rw [h] at ih
    refine (Inv.tmEq_pendingFst w).trans ?_
    convert TmEq.fst ih using 1 <;> rfl
  case case5 x n n' h ih =>
    rw [cutEval, h]
    rw [h] at ih
    convert TmEq.snd ih using 1 <;> rfl
  case case6 x n w hw h ih =>
    rw [cutEval, h]
    rw [h] at ih
    refine (Inv.tmEq_pendingSnd w).trans ?_
    convert TmEq.snd ih using 1 <;> rfl
  case case7 x A n p p' n' h ihp ihn =>
    rw [cutEval, h]
    rw [h] at ihn
    convert TmEq.app ihn ihp using 1 <;> rfl
  case case8 x A n p p' w hw h ihp ihn ihapp =>
    rw [cutEval, h]
    rw [h] at ihn
    refine ihapp.trans ?_
    exact TmEq.app ihn ihp
  case case9 =>
    rw [cutEval]
    exact TmEq.refl _
  case case10 A B p ih =>
    rw [cutEval]
    simpa [CutCall.Sound, PosNeu.erase, Pos.erase, subst0, subst] using
      TmEq.inl ih
  case case11 A B p ih =>
    rw [cutEval]
    simpa [CutCall.Sound, PosNeu.erase, Pos.erase, subst0, subst] using
      TmEq.inr ih
  case case12 N t ih =>
    rw [cutEval]
    convert ih using 1 <;> rfl
  case case13 P p ih =>
    rw [cutEval]
    simpa [CutCall.Sound, Inv.erase, Foc.erase] using ih
  case case14 Γ Cut Pout v P n body n' h ihn ihbody =>
    rw [cutEval, h]
    rw [h] at ihn
    refine TmEq.trans (TmEq.subst0_congr ihbody ihn) (TmEq.of_eq ?_)
    exact subst0_subst0_comm_cut body.erase n.erase v.erase
  case case15 Γ Cut Pout v P n body hw g h ihn ihbody ihbind =>
    rw [cutEval, h]
    rw [h] at ihn
    have ihbind' : TmEq
        (Inv.erase (cutEval (.bind (.focusPos g) (cutEval (.inv body v)))))
        (subst0 (Inv.erase (cutEval (.inv body v))) g.erase) := by
      unfold bindBelowPending at ihbind
      refine ihbind.trans ?_
      exact TmEq.subst0_congr
        (TmEq.of_eq (rename_ext_weakenBase_empty_cut _)) (TmEq.refl _)
    refine ihbind'.trans ?_
    refine TmEq.trans (TmEq.subst0_congr ihbody ihn) (TmEq.of_eq ?_)
    exact subst0_subst0_comm_cut body.erase n.erase v.erase
  case case16 Γ Cut v G A B ps l r ihl ihr =>
    rw [cutEval]
    exact tmEq_caseSum_substBelow l r v
      (cutEval (.inv l v)) (cutEval (.inv r v)) ihl ihr
  case case18 Γ Cut v G q ps t ih =>
    rw [cutEval]
    unfold substBelowPending at ih ⊢
    rw [Inv.erase_rename_exchange, Inv.erase_weaken_eq] at ih
    refine ih.trans (TmEq.of_eq ?_)
    exact subst_store_cut_eq (Γ := Γ.erase) (Cut := Cut.erase)
      (P := .atom q) (ps := ps) t.erase v.erase
  case case19 Γ Cut v G N ps t ih =>
    rw [cutEval]
    unfold substBelowPending at ih ⊢
    rw [Inv.erase_rename_exchange, Inv.erase_weaken_eq] at ih
    refine ih.trans (TmEq.of_eq ?_)
    exact subst_store_cut_eq (Γ := Γ.erase) (Cut := Cut.erase)
      (P := .shift N) (ps := ps) t.erase v.erase
  case case17 Γ Cut v G ps =>
    rw [cutEval]
    unfold substBelowPending
    let z := subst
      ((Pending.cons .zero ps).liftSubst (Subst.single v.erase))
      (Inv.erase (.abort :
        Inv (Γ.snoc (.neg Cut)) (.cons .zero ps) (.pos .zero)))
    exact TmEq.of_never z _ _
  case case20 =>
    rw [cutEval]
    exact TmEq.refl _
  case case21 A B t u iht ihu =>
    rw [cutEval]
    convert TmEq.pair iht ihu using 1 <;> rfl
  case case22 A B t ih =>
    rw [cutEval]
    convert TmEq.lam ih using 1 <;> rfl
  case case23 P f ih =>
    rw [cutEval]
    convert ih using 1 <;> rfl
  case case24 P f g h ih =>
    rw [cutEval, h]
    rw [h] at ih
    convert ih using 1 <;> rfl
  case case25 Γ A N a body ih =>
    rw [cutEval]
    unfold bindBelowPending at ih
    refine ih.trans ?_
    refine TmEq.trans (TmEq.subst0_congr
      (TmEq.of_eq (rename_ext_weakenBase_empty_cut _)) (TmEq.refl _)) ?_
    exact (TmEq.beta_app body.erase a.erase).symm
  case case26 Γ A B ps P G l r k ihl ihr =>
    rw [cutEval]
    exact tmEq_caseSum_bindBelow l r k
      (cutEval (.bind l k)) (cutEval (.bind r k)) ihl ihr
  case case27 Γ qs P G k =>
    rw [cutEval]
    let z := Inv.erase
      (.abort : Inv Γ (.cons .zero qs) (.pos .zero))
    exact TmEq.of_never z _ _
  case case28 Γ q qs P G t k ih =>
    rw [cutEval]
    exact ih.trans (TmEq.of_eq (bindBelowPending_weaken_eq_atom t k))
  case case29 Γ N qs P G t k ih =>
    rw [cutEval]
    exact ih.trans (TmEq.of_eq (bindBelowPending_weaken_eq_shift t k))
  case case30 Γ q G x k =>
    rw [cutEval]
    unfold bindBelowPending
    refine (tmEq_cutStrong (.atomVar x) k).trans ?_
    exact TmEq.subst0_congr
      (TmEq.of_eq (rename_ext_weakenBase_empty_cut k.erase).symm)
      (TmEq.refl _)
  case case31 L R G p k ih =>
    rw [cutEval]
    unfold bindBelowPending at ih ⊢
    refine ih.trans (TmEq.subst0_congr
      (TmEq.of_eq (rename_ext_weakenBase_empty_cut _)) (TmEq.refl _)) |>.trans ?_
    refine TmEq.trans (TmEq.beta_case_inl p.erase
      (Inv.asCaseSum k).1.erase (Inv.asCaseSum k).2.erase).symm ?_
    refine TmEq.trans (TmEq.of_eq
      (subst0_erase_caseSum_empty
        (Inv.asCaseSum k).1 (Inv.asCaseSum k).2 (.inl p.erase)).symm) ?_
    exact TmEq.subst0_congr
      (TmEq.of_eq ((Inv.erase_rebuildCaseSum k).trans
        (rename_ext_weakenBase_empty_cut k.erase).symm))
      (TmEq.refl _)
  case case32 L R G p k ih =>
    rw [cutEval]
    unfold bindBelowPending at ih ⊢
    refine ih.trans (TmEq.subst0_congr
      (TmEq.of_eq (rename_ext_weakenBase_empty_cut _)) (TmEq.refl _)) |>.trans ?_
    refine TmEq.trans (TmEq.beta_case_inr p.erase
      (Inv.asCaseSum k).1.erase (Inv.asCaseSum k).2.erase).symm ?_
    refine TmEq.trans (TmEq.of_eq
      (subst0_erase_caseSum_empty
        (Inv.asCaseSum k).1 (Inv.asCaseSum k).2 (.inr p.erase)).symm) ?_
    exact TmEq.subst0_congr
      (TmEq.of_eq ((Inv.erase_rebuildCaseSum k).trans
        (rename_ext_weakenBase_empty_cut k.erase).symm))
      (TmEq.refl _)
  case case33 N G v k ih =>
    rw [cutEval]
    unfold substBelowPending at ih
    simp only [Pending.liftSubst] at ih
    unfold bindBelowPending
    refine ih.trans ?_
    exact TmEq.subst0_congr
      (TmEq.of_eq ((Inv.erase_asStoreShift k).trans
        (rename_ext_weakenBase_empty_cut k.erase).symm))
      (TmEq.refl _)
  case case34 Γ Pout G P n body k ih =>
    rw [cutEval]
    have hc := tmEq_composeShiftSized body.nodeSize
      (fun d _ k => cutEval (.bind d k))
      (fun d h k => ih d h k) G n body (Nat.le_refl _) k
    refine hc.trans ?_
    unfold bindBelowPending
    exact TmEq.subst0_congr
      (TmEq.of_eq (rename_ext_weakenBase_empty_cut k.erase).symm)
      (TmEq.refl _)

/-! ### Public preservation API -/

theorem tmEq_substNegNeu {Γ : StableCtx sig} {Cut N : Neg sig.nBases}
    (n : NegNeu (Γ.snoc (.neg Cut)) N) (v : Inv Γ .empty (.neg Cut)) :
    TmEq (substNegNeu n v).erase (subst0 n.erase v.erase) :=
  tmEq_cutEval (.neu n v)

theorem tmEq_substPosNeu {Γ : StableCtx sig} {Cut : Neg sig.nBases}
    {P : Pos sig.nBases} (p : PosNeu (Γ.snoc (.neg Cut)) P)
    (v : Inv Γ .empty (.neg Cut)) :
    TmEq (substPosNeu p v).erase (subst0 p.erase v.erase) :=
  tmEq_cutEval (.pos p v)

theorem tmEq_substFoc {Γ : StableCtx sig} {Cut : Neg sig.nBases}
    {P : Pos sig.nBases} (f : Foc (Γ.snoc (.neg Cut)) P)
    (v : Inv Γ .empty (.neg Cut)) :
    TmEq (substFoc f v).erase (subst0 f.erase v.erase) :=
  tmEq_cutEval (.foc f v)

theorem tmEq_substInv {Γ : StableCtx sig} {Cut : Neg sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    (t : Inv (Γ.snoc (.neg Cut)) ps G) (v : Inv Γ .empty (.neg Cut)) :
    TmEq (substInv t v).erase (substBelowPending t v) :=
  tmEq_cutEval (.inv t v)

theorem tmEq_bindPending {Γ : StableCtx sig} {qs : Pending sig}
    {P : Pos sig.nBases} {G : Goal sig.nBases}
    (d : Inv Γ qs (.pos P)) (k : Inv Γ (.cons P .empty) G) :
    TmEq (bindPending d k).erase (bindBelowPending d k) :=
  tmEq_cutEval (.bind d k)

theorem tmEq_bindPending_empty {Γ : StableCtx sig} {P : Pos sig.nBases}
    {G : Goal sig.nBases} (d : Inv Γ .empty (.pos P))
    (k : Inv Γ (.cons P .empty) G) :
    TmEq (bindPending d k).erase (subst0 k.erase d.erase) := by
  refine (tmEq_bindPending d k).trans ?_
  unfold bindBelowPending
  exact TmEq.subst0_congr
    (TmEq.of_eq (rename_ext_weakenBase_empty_cut k.erase)) (TmEq.refl _)

theorem tmEq_cutUp {Γ : StableCtx sig} {P : Pos sig.nBases}
    {G : Goal sig.nBases} (p : PosNeu Γ P)
    (k : Inv Γ (.cons P .empty) G) :
    TmEq (cutUp p k).erase (subst0 k.erase p.erase) := by
  exact tmEq_bindPending_empty (.focusPos (.up p)) k

def castTmObject {Γ : Ctx sig} {A B : Object sig.nBases}
    (h : A = B) (t : Tm Γ A) : Tm Γ B := h ▸ t

theorem tmEq_cutObject {Γ : StableCtx sig} {A C : Object sig.nBases}
    (v : Inv Γ .empty (.neg (asNeg A)))
    (k : Inv Γ (.cons (asPos A) .empty) (.neg (asNeg C))) :
    TmEq (cutObject v k).erase
      (subst0 k.erase (castTmObject
        ((erase_asNeg A).trans (erase_asPos A).symm) v.erase)) := by
  cases A with
  | base q | never | coprod A B =>
      cases v with
      | focusShift f =>
          simpa [cutObject, castTmObject, asPos, asNeg, Pos.erase, Neg.erase,
            Inv.erase, Foc.erase] using
            (tmEq_bindPending_empty (.focusPos f) k)
  | unit | prod A B | exp A B =>
      simpa [cutObject, castTmObject, asPos, asNeg, Pos.erase, Neg.erase,
        Inv.erase, Foc.erase, PosNeu.erase] using
        (tmEq_bindPending_empty (.focusPos (.up (.shift v))) k)

end Gimbal.Equality.Scherer
