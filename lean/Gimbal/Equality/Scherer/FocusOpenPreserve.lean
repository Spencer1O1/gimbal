/-
  Erasure preservation for the direct producer under an explicit `RootEnv`.
  Root-context inversion and `focusRoot` preservation are intentionally left
  to the next gate.
-/

import Gimbal.Equality.Scherer.FocusRoot
import Gimbal.Equality.Scherer.OrdinaryCutPreserve

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

private theorem castTmObject_rename {Γ Δ : Ctx sig}
    {A B : Object sig.nBases} (h : A = B) (ρ : Rename sig Γ Δ)
    (t : Tm Γ A) :
    castTmObject h (Equality.rename ρ t) =
      Equality.rename ρ (castTmObject h t) := by
  subst h
  rfl

private theorem castTmObject_subst0_early {Γ : Ctx sig}
    {A B C : Object sig.nBases} (h : A = B)
    (t : Tm (Γ.snoc C) A) (v : Tm Γ C) :
    castTmObject h (subst0 t v) = subst0 (castTmObject h t) v := by
  subst h
  rfl

namespace Subst

/-- Extend a substitution when the new target binder is propositionally equal
to the new source binder. -/
def extsCast {Γ Δ : Ctx sig} {A A' : Object sig.nBases}
    (h : A' = A) (σ : Subst sig Γ Δ) : Subst sig (Γ.snoc A) (Δ.snoc A')
  | _, .here => castTmObject h (.var .here)
  | _, .there x => weakenTerm (σ x)

end Subst

namespace RootEnv

/-- Erase a source-variable environment to an ordinary parallel substitution. -/
def erase {Γ : Ctx sig} {Δ : StableCtx sig}
    (ε : RootEnv Γ Δ) : Subst sig Γ Δ.erase :=
  fun {A} x => castTmObject (erase_asPos A) (ε x).erase

@[simp] theorem erase_snoc_here {Γ : Ctx sig} {Δ : StableCtx sig}
    {A : Object sig.nBases} (ε : RootEnv Γ Δ)
    (p : PosNeu Δ (asPos A)) :
    RootEnv.erase (RootEnv.snoc ε p) (.here : Var (Γ.snoc A) A) =
      castTmObject (erase_asPos A) p.erase := rfl

@[simp] theorem erase_snoc_there {Γ : Ctx sig} {Δ : StableCtx sig}
    {A B : Object sig.nBases} (ε : RootEnv Γ Δ)
    (p : PosNeu Δ (asPos A)) (x : Var Γ B) :
    RootEnv.erase (RootEnv.snoc ε p) (.there x) = RootEnv.erase ε x := rfl

theorem erase_rename_apply {Γ : Ctx sig} {Δ Ε : StableCtx sig}
    (ε : RootEnv Γ Δ) (ρ : StableRename Δ Ε)
    {A : Object sig.nBases} (x : Var Γ A) :
    RootEnv.erase (RootEnv.rename ε ρ) x =
      Equality.rename (StableRename.erase ρ) (RootEnv.erase ε x) := by
  unfold RootEnv.erase RootEnv.rename
  rw [PosNeu.erase_rename]
  exact castTmObject_rename (erase_asPos A) (StableRename.erase ρ) _

/-- Substitute old variables through `ε` while representing the newest source
variable by the newest positive-polarized binder. -/
def extendPos {Γ : Ctx sig} {Δ : StableCtx sig} {A : Object sig.nBases}
    (ε : RootEnv Γ Δ) :
    Subst sig (Γ.snoc A) (Δ.erase.snoc (asPos A).erase)
  := Subst.extsCast (erase_asPos A) ε.erase

theorem subst0_rename_extendPos {Γ : Ctx sig} {Δ Ε : StableCtx sig}
    {A B : Object sig.nBases} (ε : RootEnv Γ Δ)
    (ρ : StableRename Δ Ε) (p : PosNeu Ε (asPos A))
    (t : Tm (Γ.snoc A) B) :
    subst0
        (Equality.rename (Rename.ext (StableRename.erase ρ))
          (subst (RootEnv.extendPos ε) t)) p.erase =
      subst (RootEnv.erase (RootEnv.snoc (RootEnv.rename ε ρ) p)) t := by
  rw [rename_subst, subst0, subst_comp]
  apply subst_eq_of_pointwise
  intro C x
  cases x with
  | here =>
      change subst0
          (Equality.rename (Rename.ext (StableRename.erase ρ))
            (castTmObject (erase_asPos A) (.var .here))) p.erase =
        castTmObject (erase_asPos A) p.erase
      rw [← castTmObject_rename, ← castTmObject_subst0_early]
      rfl
  | there x =>
      change subst0
          (Equality.rename (Rename.ext (StableRename.erase ρ))
            (weakenTerm (RootEnv.erase ε x))) p.erase =
        RootEnv.erase (RootEnv.rename ε ρ) x
      rw [rename_ext_weaken_cut, subst0_weakenTerm]
      exact (RootEnv.erase_rename_apply ε ρ x).symm

end RootEnv

/-! ### Cast algebra at the object boundary -/

theorem TmEq.castObject {Γ : Ctx sig} {A B : Object sig.nBases}
    (h : A = B) {t u : Tm Γ A} (ht : TmEq t u) :
    TmEq (castTmObject h t) (castTmObject h u) := by
  subst h
  exact ht

theorem castTmObject_trans {Γ : Ctx sig} {A B C : Object sig.nBases}
    (h : A = B) (k : B = C) (t : Tm Γ A) :
    castTmObject k (castTmObject h t) = castTmObject (h.trans k) t := by
  subst h
  subst k
  rfl

theorem castTmObject_comp {Γ : Ctx sig} {A B C : Object sig.nBases}
    (h : A = B) (k : B = C) (l : A = C) (t : Tm Γ A) :
    castTmObject k (castTmObject h t) = castTmObject l t := by
  subst h
  subst k
  rfl

theorem castTmObject_subst {Γ Δ : Ctx sig}
    {A B : Object sig.nBases} (h : A = B) (σ : Subst sig Γ Δ)
    (t : Tm Γ A) :
    castTmObject h (subst σ t) = subst σ (castTmObject h t) := by
  subst h
  rfl

theorem castTmObject_subst0 {Γ : Ctx sig}
    {A B C : Object sig.nBases} (h : A = B)
    (t : Tm (Γ.snoc C) A) (v : Tm Γ C) :
    castTmObject h (subst0 t v) = subst0 (castTmObject h t) v := by
  subst h
  rfl

theorem castTmObject_pair {Γ : Ctx sig}
    {A A' B B' : Object sig.nBases} (hA : A = A') (hB : B = B')
    (t : Tm Γ A) (u : Tm Γ B) :
    castTmObject (congrArg₂ Object.prod hA hB) (.pair t u) =
      .pair (castTmObject hA t) (castTmObject hB u) := by
  subst hA
  subst hB
  rfl

theorem castTmObject_fst {Γ : Ctx sig}
    {A A' B B' : Object sig.nBases} (hA : A = A') (hB : B = B')
    (t : Tm Γ (.prod A B)) :
    castTmObject hA (.fst t) =
      .fst (castTmObject (congrArg₂ Object.prod hA hB) t) := by
  subst hA
  subst hB
  rfl

theorem castTmObject_snd {Γ : Ctx sig}
    {A A' B B' : Object sig.nBases} (hA : A = A') (hB : B = B')
    (t : Tm Γ (.prod A B)) :
    castTmObject hB (.snd t) =
      .snd (castTmObject (congrArg₂ Object.prod hA hB) t) := by
  subst hA
  subst hB
  rfl

theorem castTmObject_inl {Γ : Ctx sig}
    {A A' B B' : Object sig.nBases} (hA : A = A') (hB : B = B')
    (t : Tm Γ A) :
    castTmObject (congrArg₂ Object.coprod hA hB) (.inl (B := B) t) =
      .inl (B := B') (castTmObject hA t) := by
  subst hA
  subst hB
  rfl

theorem castTmObject_inr {Γ : Ctx sig}
    {A A' B B' : Object sig.nBases} (hA : A = A') (hB : B = B')
    (t : Tm Γ B) :
    castTmObject (congrArg₂ Object.coprod hA hB) (.inr (A := A) t) =
      .inr (A := A') (castTmObject hB t) := by
  subst hA
  subst hB
  rfl

theorem castTmObject_lam_extsCast {Γ Δ : Ctx sig}
    {A A' B B' : Object sig.nBases} (hA : A' = A) (hB : B = B')
    (σ : Subst sig Γ Δ) (t : Tm (Γ.snoc A) B) :
    .lam (castTmObject hB (subst (Subst.extsCast hA σ) t)) =
      castTmObject (congrArg₂ Object.exp hA.symm hB)
        (.lam (subst (Subst.exts σ) t)) := by
  subst hA
  subst hB
  rfl

theorem castTmObject_app {Γ : Ctx sig}
    {A A' B B' : Object sig.nBases} (hA : A = A') (hB : B = B')
    (f : Tm Γ (.exp A B)) (a : Tm Γ A) :
    .app (castTmObject (congrArg₂ Object.exp hA hB) f)
        (castTmObject hA a) =
      castTmObject hB (.app f a) := by
  subst hA
  subst hB
  rfl

theorem castTmObject_case_extsCast {Γ Δ : Ctx sig}
    {A A' B B' C C' : Object sig.nBases}
    (hA : A' = A) (hB : B' = B) (hC : C = C')
    (σ : Subst sig Γ Δ) (s : Tm Γ (.coprod A B))
    (l : Tm (Γ.snoc A) C) (r : Tm (Γ.snoc B) C) :
    .case
        (castTmObject (congrArg₂ Object.coprod hA.symm hB.symm)
          (subst σ s))
        (castTmObject hC (subst (Subst.extsCast hA σ) l))
        (castTmObject hC (subst (Subst.extsCast hB σ) r)) =
      castTmObject hC (subst σ (.case s l r)) := by
  subst hA
  subst hB
  subst hC
  rfl

/-! ### Producer helper semantics -/

theorem tmEq_reflectObject {Γ : StableCtx sig} (A : Object sig.nBases)
    (p : PosNeu Γ (asPos A)) :
    TmEq (reflectObject A p).erase
      (castTmObject ((erase_asPos A).trans (erase_asNeg A).symm) p.erase) := by
  cases A <;> cases p <;>
    simp [reflectObject, castTmObject, asPos, asNeg, Pos.erase, Neg.erase,
      Inv.erase, Foc.erase] <;>
    exact TmEq.refl _

theorem tmEq_reflectObject_source {Γ : StableCtx sig}
    (A : Object sig.nBases) (p : PosNeu Γ (asPos A)) :
    TmEq (reflectObject A p).erase
      (castTmObject (erase_asNeg A).symm
        (castTmObject (erase_asPos A) p.erase)) := by
  refine (tmEq_reflectObject A p).trans (TmEq.of_eq ?_)
  rw [castTmObject_trans]

/-- Recast a compiled argument from negative to positive erasure. -/
theorem tmEq_cutArgument {Γ : StableCtx sig} {A : Object sig.nBases}
    {v : Inv Γ .empty (.neg (asNeg A))} {u : Tm Γ.erase A}
    (h : TmEq v.erase (castTmObject (erase_asNeg A).symm u)) :
    TmEq
      (castTmObject ((erase_asNeg A).trans (erase_asPos A).symm) v.erase)
      (castTmObject (erase_asPos A).symm u) := by
  have hc := TmEq.castObject
    ((erase_asNeg A).trans (erase_asPos A).symm) h
  refine hc.trans (TmEq.of_eq ?_)
  exact castTmObject_comp _ _ _ u

/-- The source body, substituted by an open producer environment and recast
to the negative erasure expected by the compiled goal. -/
def openBodyRef {Γ : Ctx sig} {Δ : StableCtx sig}
    {A B : Object sig.nBases} (ε : RootEnv Γ Δ)
    (t : Tm (Γ.snoc A) B) :
    Tm (Δ.erase.snoc (asPos A).erase) (asNeg B).erase :=
  castTmObject (erase_asNeg B).symm (subst (RootEnv.extendPos ε) t)

theorem subst0_rename_openBodyRef {Γ : Ctx sig}
    {Δ Ε : StableCtx sig} {A B : Object sig.nBases}
    (ε : RootEnv Γ Δ) (ρ : StableRename Δ Ε)
    (p : PosNeu Ε (asPos A)) (t : Tm (Γ.snoc A) B) :
    subst0
        (Equality.rename (Rename.ext (StableRename.erase ρ))
          (openBodyRef ε t)) p.erase =
      castTmObject (erase_asNeg B).symm
        (subst (RootEnv.erase (RootEnv.snoc (RootEnv.rename ε ρ) p)) t) := by
  unfold openBodyRef
  rw [← castTmObject_rename, ← castTmObject_subst0]
  exact congrArg (castTmObject (erase_asNeg B).symm)
    (RootEnv.subst0_rename_extendPos ε ρ p t)

theorem Inv.erase_asLam_eq {Γ : StableCtx sig}
    {P : Pos sig.nBases} {N : Neg sig.nBases}
    (v : Inv Γ .empty (.neg (.arr P N))) :
    v.erase = .lam v.asLam.erase := by
  cases v
  rfl

private theorem tmEq_inlContinuation {Γ : StableCtx sig}
    (A B : Object sig.nBases) :
    TmEq
      (withPendingPos (asPos A) fun _ p =>
        Inv.focusShift (Foc.up (PosNeu.inl (B := asPos B) p))).erase
      (.inl (B := (asPos B).erase)
        (.var (.here : Var (Γ.erase.snoc (asPos A).erase)
          (asPos A).erase))) := by
  apply tmEq_withPendingPos
  intro Δ ρ p
  simp only [Inv.erase, Foc.erase, PosNeu.erase]
  exact TmEq.refl _

private theorem tmEq_inrContinuation {Γ : StableCtx sig}
    (A B : Object sig.nBases) :
    TmEq
      (withPendingPos (asPos B) fun _ p =>
        Inv.focusShift (Foc.up (PosNeu.inr (A := asPos A) p))).erase
      (.inr (A := (asPos A).erase)
        (.var (.here : Var (Γ.erase.snoc (asPos B).erase)
          (asPos B).erase))) := by
  apply tmEq_withPendingPos
  intro Δ ρ p
  simp only [Inv.erase, Foc.erase, PosNeu.erase]
  exact TmEq.refl _

/-! ### Open producer preservation -/

theorem tmEq_focusOpen {Γ : Ctx sig} {Δ : StableCtx sig}
    (ε : RootEnv Γ Δ) {A : Object sig.nBases} (t : Tm Γ A) :
    TmEq (focusOpen ε t).erase
      (castTmObject (erase_asNeg A).symm (subst ε.erase t)) := by
  induction t generalizing Δ with
  | var x =>
      simpa [focusOpen, Equality.subst, RootEnv.erase] using
        (tmEq_reflectObject_source _ (ε x))
  | unit =>
      exact TmEq.refl _
  | abort t ih =>
      exact TmEq.of_never (focusOpen ε t).erase _ _
  | pair t u iht ihu =>
      refine (TmEq.pair (iht ε) (ihu ε)).trans (TmEq.of_eq ?_)
      simpa [focusOpen, Equality.subst, asNeg, Neg.erase] using
        (castTmObject_pair (erase_asNeg _).symm (erase_asNeg _).symm
          (subst ε.erase t) (subst ε.erase u)).symm
  | fst t ih =>
      refine (Inv.tmEq_pendingFst (focusOpen ε t)).trans ?_
      refine (TmEq.fst (ih ε)).trans (TmEq.of_eq ?_)
      simpa [focusOpen, Equality.subst, asNeg, Neg.erase] using
        (castTmObject_fst (erase_asNeg _).symm (erase_asNeg _).symm
          (subst ε.erase t)).symm
  | snd t ih =>
      refine (Inv.tmEq_pendingSnd (focusOpen ε t)).trans ?_
      refine (TmEq.snd (ih ε)).trans (TmEq.of_eq ?_)
      simpa [focusOpen, Equality.subst, asNeg, Neg.erase] using
        (castTmObject_snd (erase_asNeg _).symm (erase_asNeg _).symm
          (subst ε.erase t)).symm
  | inl t ih =>
      rw [focusOpen]
      refine (tmEq_cutObject (focusOpen ε t) _).trans ?_
      refine (TmEq.subst0_congr (tmEq_inlContinuation _ _)
        (tmEq_cutArgument (ih ε))).trans (TmEq.of_eq ?_)
      simp only [subst0, Equality.subst, Subst.single]
      change Tm.inl (castTmObject _ (subst ε.erase t)) =
        castTmObject _ (Tm.inl (subst ε.erase t))
      simpa only [asNeg, Neg.erase, Pos.erase, Goal.erase] using
        (castTmObject_inl (erase_asPos _).symm (erase_asPos _).symm
          (subst ε.erase t)).symm
  | inr t ih =>
      rw [focusOpen]
      refine (tmEq_cutObject (focusOpen ε t) _).trans ?_
      refine (TmEq.subst0_congr (tmEq_inrContinuation _ _)
        (tmEq_cutArgument (ih ε))).trans (TmEq.of_eq ?_)
      simp only [subst0, Equality.subst, Subst.single]
      change Tm.inr (castTmObject _ (subst ε.erase t)) =
        castTmObject _ (Tm.inr (subst ε.erase t))
      simpa only [asNeg, Neg.erase, Pos.erase, Goal.erase] using
        (castTmObject_inr (erase_asPos _).symm (erase_asPos _).symm
          (subst ε.erase t)).symm
  | case s l r ihs ihl ihr =>
      rw [focusOpen]
      have hscr := tmEq_cutArgument (ihs ε)
      refine (tmEq_cutObject (focusOpen ε s) _).trans ?_
      refine (TmEq.subst0_congr (TmEq.refl _) hscr).trans ?_
      refine (TmEq.of_eq (subst0_erase_caseSum_empty _ _ _)).trans ?_
      have hL := tmEq_withPendingPos (asPos _)
        (fun ρ p =>
          focusOpen (RootEnv.snoc (RootEnv.rename ε ρ) p) l)
        (openBodyRef ε l) (by
          intro Ε ρ p
          refine (ihl (RootEnv.snoc (RootEnv.rename ε ρ) p)).trans
            (TmEq.of_eq ?_)
          exact (subst0_rename_openBodyRef ε ρ p l).symm)
      have hR := tmEq_withPendingPos (asPos _)
        (fun ρ p =>
          focusOpen (RootEnv.snoc (RootEnv.rename ε ρ) p) r)
        (openBodyRef ε r) (by
          intro Ε ρ p
          refine (ihr (RootEnv.snoc (RootEnv.rename ε ρ) p)).trans
            (TmEq.of_eq ?_)
          exact (subst0_rename_openBodyRef ε ρ p r).symm)
      refine (TmEq.«case» (TmEq.refl _) hL hR).trans (TmEq.of_eq ?_)
      simpa [openBodyRef, RootEnv.extendPos, Equality.subst,
        asPos, Pos.erase, asNeg, Neg.erase, Goal.erase] using
        (castTmObject_case_extsCast
          (erase_asPos _) (erase_asPos _) (erase_asNeg _).symm
          ε.erase s l r)
  | lam t ih =>
      rw [focusOpen]
      have hb := tmEq_withPendingPos (asPos _)
        (fun ρ p =>
          focusOpen (RootEnv.snoc (RootEnv.rename ε ρ) p) t)
        (openBodyRef ε t) (by
          intro Ε ρ p
          refine (ih (RootEnv.snoc (RootEnv.rename ε ρ) p)).trans
            (TmEq.of_eq ?_)
          exact (subst0_rename_openBodyRef ε ρ p t).symm)
      refine (TmEq.lam hb).trans (TmEq.of_eq ?_)
      simpa [openBodyRef, RootEnv.extendPos, Equality.subst, asNeg, Neg.erase]
        using (castTmObject_lam_extsCast
          (erase_asPos _)
          (erase_asNeg _).symm ε.erase t)
  | app f a ihf iha =>
      rw [focusOpen]
      let vf := focusOpen ε f
      let va := focusOpen ε a
      have harg := tmEq_cutArgument (iha ε)
      refine (tmEq_cutObject va vf.asLam).trans ?_
      refine (TmEq.subst0_congr (TmEq.refl _) harg).trans ?_
      refine (TmEq.beta_app vf.asLam.erase
        (castTmObject (erase_asPos _).symm (subst ε.erase a))).symm.trans ?_
      refine (TmEq.app (TmEq.of_eq (Inv.erase_asLam_eq vf).symm)
        (TmEq.refl _)).trans ?_
      refine (TmEq.app (ihf ε) (TmEq.refl _)).trans (TmEq.of_eq ?_)
      simpa [Equality.subst, asNeg, Neg.erase, Goal.erase] using
        (castTmObject_app (erase_asPos _).symm (erase_asNeg _).symm
          (subst ε.erase f) (subst ε.erase a))

/-! ### Theorem-level regression fixtures -/

namespace FocusOpenPreserveFixtures

open FocusRootFixtures

theorem beta_identity_preserved :
    TmEq
      (focusOpen
        (RootEnv.empty : RootEnv (.empty : Ctx Fixtures.sig0)
          (.empty : StableCtx Fixtures.sig0))
        betaIdentityTm).erase
      (castTmObject (erase_asNeg UnitObj).symm
        (subst (RootEnv.erase (RootEnv.empty : RootEnv (.empty : Ctx Fixtures.sig0)
          (.empty : StableCtx Fixtures.sig0))) betaIdentityTm)) :=
  tmEq_focusOpen _ _

theorem case_on_inl_preserved :
    TmEq
      (focusOpen
        (RootEnv.empty : RootEnv (.empty : Ctx Fixtures.sig0)
          (.empty : StableCtx Fixtures.sig0))
        caseInlTm).erase
      (castTmObject (erase_asNeg SumUnit).symm
        (subst (RootEnv.erase (RootEnv.empty : RootEnv (.empty : Ctx Fixtures.sig0)
          (.empty : StableCtx Fixtures.sig0))) caseInlTm)) :=
  tmEq_focusOpen _ _

theorem opaque_generator_preserved {Δ : StableCtx sigOpaque}
    (ε : RootEnv (genCtx sigOpaque) Δ) :
    TmEq (focusOpen ε opaqueGeneratorAppTm).erase
      (castTmObject (erase_asNeg OpaqueX).symm
        (subst ε.erase opaqueGeneratorAppTm)) :=
  tmEq_focusOpen ε _

theorem computed_shifted_argument_preserved {Δ : StableCtx sigComputed}
    (ε : RootEnv (genCtx sigComputed) Δ) :
    TmEq (focusOpen ε computedShiftedArgumentTm).erase
      (castTmObject (erase_asNeg (.unit : Object sigComputed.nBases)).symm
        (subst ε.erase computedShiftedArgumentTm)) :=
  tmEq_focusOpen ε _

end FocusOpenPreserveFixtures

end Gimbal.Equality.Scherer
