/-
  Erasure preservation for root-context inversion and the final direct
  producer.  This module closes the public `Tm` to ordinary Scherer bridge.
-/

import Gimbal.Equality.Scherer.FocusOpenPreserve

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Pending rotation and context casts -/

/-- Transport a term across a propositional equality of its context. -/
def castTmCtx {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (h : Γ = Δ) (t : Tm Γ A) : Tm Δ A :=
  h ▸ t

theorem TmEq.castCtx {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (h : Γ = Δ) {t u : Tm Γ A} (ht : TmEq t u) :
    TmEq (castTmCtx h t) (castTmCtx h u) := by
  subst h
  exact ht

theorem castTmCtx_comp {Γ Δ Ε : Ctx sig} {A : Object sig.nBases}
    (h : Γ = Δ) (k : Δ = Ε) (l : Γ = Ε) (t : Tm Γ A) :
    castTmCtx k (castTmCtx h t) = castTmCtx l t := by
  subst h
  subst k
  rfl

theorem renameEraseAux_leftInverse {Γ Δ : Ctx sig}
    (ρ : Rename sig Δ Γ) (τ : Rename sig Γ Δ)
    (h : ∀ {A : Object sig.nBases} (x : Var Γ A), ρ (τ x) = x)
    (ps : Pending sig) {A : Object sig.nBases}
    (x : Var (Pending.eraseAux ps Γ) A) :
    renameEraseAux ρ ps (renameEraseAux τ ps x) = x := by
  induction ps generalizing Γ Δ A with
  | empty => exact h x
  | cons Q qs ih =>
      apply ih
      intro B y
      cases y with
      | here => rfl
      | there z => exact congrArg Var.there (h z)

theorem rotateHead_newest_apply {Γ : Ctx sig}
    {H A : Object sig.nBases} (ps : Pending sig)
    (x : Var ((Pending.eraseAux ps Γ).snoc H) A) :
    rotateHeadToNewest (Δ := Γ) (H := H) ps
        (rotateNewestToHead (Δ := Γ) (A := H) ps x) = x := by
  induction ps generalizing Γ A with
  | empty => rfl
  | cons Q qs ih =>
      simp only [rotateHeadToNewest, rotateNewestToHead, renameComp]
      rw [renameEraseAux_leftInverse
        (Rename.exchange (Γ := Γ) (A := H) (B := Q.erase))
        (Rename.exchange (Γ := Γ) (A := Q.erase) (B := H))
        (by
          intro B y
          cases y with
          | here => rfl
          | there z => cases z <;> rfl) qs]
      exact ih _

theorem rotateNewest_head_apply {Γ : Ctx sig}
    {H A : Object sig.nBases} (ps : Pending sig)
    (x : Var (Pending.eraseAux ps (Γ.snoc H)) A) :
    rotateNewestToHead (Δ := Γ) (A := H) ps
        (rotateHeadToNewest (Δ := Γ) (H := H) ps x) = x := by
  induction ps generalizing Γ A with
  | empty => rfl
  | cons Q qs ih =>
      simp only [rotateHeadToNewest, rotateNewestToHead, renameComp]
      rw [ih]
      exact renameEraseAux_leftInverse
        (Rename.exchange (Γ := Γ) (A := Q.erase) (B := H))
        (Rename.exchange (Γ := Γ) (A := H) (B := Q.erase))
        (by
          intro B y
          cases y with
          | here => rfl
          | there z => cases z <;> rfl) qs x

theorem rename_rotateHead_newest {Γ : Ctx sig}
    {H A : Object sig.nBases} (ps : Pending sig)
    (t : Tm ((Pending.eraseAux ps Γ).snoc H) A) :
    Equality.rename (rotateHeadToNewest (Δ := Γ) (H := H) ps)
        (Equality.rename (rotateNewestToHead (Δ := Γ) (A := H) ps) t) = t := by
  rw [rename_comp]
  exact (rename_eq_of_pointwise (rotateHead_newest_apply ps) t).trans
    (rename_id t)

theorem rename_rotateNewest_head {Γ : Ctx sig}
    {H A : Object sig.nBases} (ps : Pending sig)
    (t : Tm (Pending.eraseAux ps (Γ.snoc H)) A) :
    Equality.rename (rotateNewestToHead (Δ := Γ) (A := H) ps)
        (Equality.rename (rotateHeadToNewest (Δ := Γ) (H := H) ps) t) = t := by
  rw [rename_comp]
  exact (rename_eq_of_pointwise (rotateNewest_head_apply ps) t).trans
    (rename_id t)

/-- Erasing a root pending telescope reconstructs the source context before
erasing the arbitrary tail. -/
theorem eraseInvCtx_root (Γ : Ctx sig) (tail : Pending sig) :
    eraseInvCtx (.empty : StableCtx sig) (Pending.rootThen Γ tail) =
      Pending.eraseAux tail Γ := by
  induction Γ generalizing tail with
  | empty => rfl
  | snoc Γ A ih =>
      simp only [Pending.rootThen]
      rw [ih]
      simp only [Pending.eraseAux]
      rw [erase_asPos]

/-! ### Arbitrary-tail positive inversion -/

/-- Instantiate a pending head after renaming the stable base, while retaining
all later pending binders. -/
def instantiatePendingHead {Γ Δ : StableCtx sig}
    (tail : Pending sig) {P : Pos sig.nBases}
    (ρ : StableRename Γ Δ) (p : PosNeu Δ P)
    {G : Object sig.nBases}
    (t : Tm (Pending.eraseAux tail (Γ.erase.snoc P.erase)) G) :
    Tm (Pending.eraseAux tail Δ.erase) G :=
  subst (tail.liftSubst (Subst.single p.erase))
    (Equality.rename
      (renameEraseAux (Rename.ext (StableRename.erase ρ)) tail) t)

theorem Pending.liftSubst_ids_apply {Γ : Ctx sig} (ps : Pending sig)
    {A : Object sig.nBases} (x : Var (Pending.eraseAux ps Γ) A) :
    ps.liftSubst (Subst.ids (sig := sig)) x = .var x := by
  induction ps generalizing Γ A with
  | empty => rfl
  | cons Q qs ih =>
      apply Eq.trans (Pending.liftSubst_eq_of_pointwise qs
        (σ := Subst.exts Subst.ids) (τ := Subst.ids) (fun {_} y => by
          cases y <;> rfl) x)
      exact ih (Γ := Γ.snoc Q.erase) x

theorem Pending.liftSubst_substComp_apply {Γ Δ Ε : Ctx sig}
    (ps : Pending sig) (σ : Subst sig Δ Ε) (τ : Subst sig Γ Δ)
    {A : Object sig.nBases} (x : Var (Pending.eraseAux ps Γ) A) :
    substComp (ps.liftSubst σ) (ps.liftSubst τ) x =
      ps.liftSubst (substComp σ τ) x := by
  induction ps generalizing Γ Δ Ε A with
  | empty => rfl
  | cons Q qs ih =>
      refine Eq.trans (ih (Subst.exts σ) (Subst.exts τ) x) ?_
      exact (Pending.liftSubst_eq_of_pointwise qs
        (fun {_} y => (substComp_exts_apply σ τ y).symm) x)

theorem TmEq.subst_pointwise {Γ Δ : Ctx sig}
    {σ τ : Subst sig Γ Δ}
    (h : ∀ {A : Object sig.nBases} (x : Var Γ A), TmEq (σ x) (τ x)) :
    {A : Object sig.nBases} → (t : Tm Γ A) → TmEq (subst σ t) (subst τ t)
  | _, .var x => h x
  | _, .unit => .refl _
  | _, .abort t => .abort (TmEq.subst_pointwise h t)
  | _, .pair t u => .pair (TmEq.subst_pointwise h t) (TmEq.subst_pointwise h u)
  | _, .fst t => .fst (TmEq.subst_pointwise h t)
  | _, .snd t => .snd (TmEq.subst_pointwise h t)
  | _, .inl t => .inl (TmEq.subst_pointwise h t)
  | _, .inr t => .inr (TmEq.subst_pointwise h t)
  | _, .case s l r =>
      .«case» (TmEq.subst_pointwise h s)
        (TmEq.subst_pointwise (fun x => by
          cases x with
          | here => exact .refl _
          | there y => exact TmEq.rename Rename.weaken (h y)) l)
        (TmEq.subst_pointwise (fun x => by
          cases x with
          | here => exact .refl _
          | there y => exact TmEq.rename Rename.weaken (h y)) r)
  | _, .lam t =>
      .lam (TmEq.subst_pointwise (fun x => by
        cases x with
        | here => exact .refl _
        | there y => exact TmEq.rename Rename.weaken (h y)) t)
  | _, .app f a => .app (TmEq.subst_pointwise h f) (TmEq.subst_pointwise h a)

theorem Pending.liftSubst_congr {Γ Δ : Ctx sig} (ps : Pending sig)
    {σ τ : Subst sig Γ Δ}
    (h : ∀ {A : Object sig.nBases} (x : Var Γ A), TmEq (σ x) (τ x))
    {A : Object sig.nBases} (x : Var (Pending.eraseAux ps Γ) A) :
    TmEq (ps.liftSubst σ x) (ps.liftSubst τ x) := by
  induction ps generalizing Γ Δ A with
  | empty => exact h x
  | cons Q qs ih =>
      apply ih
      intro B y
      cases y with
      | here => exact .refl _
      | there z => exact TmEq.rename Rename.weaken (h z)

theorem instantiatePendingHead_atom_weaken_here {Γ : StableCtx sig}
    (tail : Pending sig) {q : Fin sig.nBases} {G : Object sig.nBases}
    (t : Tm (Pending.eraseAux tail (Γ.erase.snoc (.base q))) G) :
    instantiatePendingHead tail StableRename.weaken
        (PosNeu.atom (.here : StableVar (Γ.snoc (.atom q)) (.atom q)))
        t = t := by
  simp only [instantiatePendingHead, PosNeu.erase]
  rw [subst_rename]
  refine (subst_eq_of_pointwise (τ := Subst.ids) ?_ t).trans (subst_ids t)
  intro A x
  refine Eq.trans (Pending.liftSubst_renameEraseAux_apply tail _ _
    (Subst.ids (sig := sig)) ?_ x) ?_
  · intro B y
    cases y with
    | here => rfl
    | there z => exact congrArg Tm.var (StableRename.erase_weaken_apply z)
  · exact Pending.liftSubst_ids_apply tail x

theorem instantiatePendingHead_shift_weaken {Γ : StableCtx sig}
    (tail : Pending sig) {N : Neg sig.nBases} {G : Object sig.nBases}
    (t : Tm (Pending.eraseAux tail (Γ.erase.snoc N.erase)) G) :
    TmEq
      (instantiatePendingHead tail StableRename.weaken
        (PosNeu.shift (etaNeg N (.var .here))) t) t := by
  let p : PosNeu (Γ.snoc (.neg N)) (.shift N) :=
    .shift (etaNeg N (.var .here))
  change TmEq (instantiatePendingHead tail StableRename.weaken p t) t
  simp only [instantiatePendingHead]
  rw [subst_rename]
  refine (TmEq.subst_pointwise ?_ t).trans (TmEq.of_eq (subst_ids t))
  intro A x
  have hη := tmEq_etaNeg N
    (.var (.here : StableVar (Γ.snoc (.neg N)) (.neg N)))
  let σ : Subst sig
      ((Γ.snoc (.neg N)).erase.snoc (Pos.shift N).erase)
      (Γ.snoc (.neg N)).erase := Subst.single p.erase
  let ρ : Rename sig (Γ.erase.snoc (Pos.shift N).erase)
      ((Γ.snoc (.neg N)).erase.snoc (Pos.shift N).erase) :=
    Rename.ext (StableRename.erase StableRename.weaken)
  have hc : ∀ {B : Object sig.nBases}
      (y : Var (Γ.erase.snoc (Pos.shift N).erase) B),
      TmEq (Subst.compRename σ ρ y) (Subst.ids y) := by
    intro B y
    cases y with
    | here => exact hη
    | there z =>
        change TmEq
          (.var (StableRename.erase StableRename.weaken z)) (.var (.there z))
        exact TmEq.of_eq
          (congrArg Tm.var (StableRename.erase_weaken_apply z))
  refine (TmEq.of_eq (Pending.liftSubst_renameEraseAux_apply tail ρ σ
    (Subst.compRename σ ρ) (fun _ => rfl) x)).trans ?_
  refine (Pending.liftSubst_congr tail hc x).trans (TmEq.of_eq ?_)
  exact Pending.liftSubst_ids_apply tail x

theorem instantiatePendingHead_inl {Γ Δ : StableCtx sig}
    (tail : Pending sig) {A B : Pos sig.nBases}
    (ρ : StableRename Γ Δ) (p : PosNeu Δ A)
    {G : Object sig.nBases}
    (t : Tm (Pending.eraseAux tail
      (Γ.erase.snoc (.coprod A.erase B.erase))) G) :
    instantiatePendingHead tail ρ p
        (subst (tail.liftSubst Subst.injLeft) t) =
      instantiatePendingHead tail ρ (.inl p) t := by
  simp only [instantiatePendingHead]
  rw [rename_subst, subst_comp, subst_rename]
  apply subst_eq_of_pointwise
  intro C x
  let ρA : Rename sig (Γ.erase.snoc A.erase) (Δ.erase.snoc A.erase) :=
    Rename.ext (StableRename.erase ρ)
  let ρS : Rename sig (Γ.erase.snoc (.coprod A.erase B.erase))
      (Δ.erase.snoc (.coprod A.erase B.erase)) :=
    Rename.ext (StableRename.erase ρ)
  let σp : Subst sig (Δ.erase.snoc A.erase) Δ.erase := Subst.single p.erase
  let σi : Subst sig (Δ.erase.snoc (.coprod A.erase B.erase)) Δ.erase :=
    Subst.single (.inl p.erase)
  calc
    substComp (tail.liftSubst σp)
        (renameSubst (renameEraseAux ρA tail)
          (tail.liftSubst Subst.injLeft)) x =
      substComp (tail.liftSubst σp)
        (tail.liftSubst (renameSubst ρA Subst.injLeft)) x := by
          exact congrArg (subst (tail.liftSubst σp))
            (Pending.liftSubst_renameSubst_apply tail ρA
              Subst.injLeft x).symm
    _ = tail.liftSubst
        (substComp σp (renameSubst ρA Subst.injLeft)) x :=
      Pending.liftSubst_substComp_apply tail σp _ x
    _ = tail.liftSubst (Subst.compRename σi ρS) x := by
      apply Pending.liftSubst_eq_of_pointwise
      intro D y
      cases y <;> rfl
    _ = tail.liftSubst σi (renameEraseAux ρS tail x) := by
      symm
      apply Pending.liftSubst_renameEraseAux_apply
      intro D y
      rfl

theorem instantiatePendingHead_inr {Γ Δ : StableCtx sig}
    (tail : Pending sig) {A B : Pos sig.nBases}
    (ρ : StableRename Γ Δ) (p : PosNeu Δ B)
    {G : Object sig.nBases}
    (t : Tm (Pending.eraseAux tail
      (Γ.erase.snoc (.coprod A.erase B.erase))) G) :
    instantiatePendingHead tail ρ p
        (subst (tail.liftSubst Subst.injRight) t) =
      instantiatePendingHead tail ρ (.inr p) t := by
  simp only [instantiatePendingHead]
  rw [rename_subst, subst_comp, subst_rename]
  apply subst_eq_of_pointwise
  intro C x
  let ρB : Rename sig (Γ.erase.snoc B.erase) (Δ.erase.snoc B.erase) :=
    Rename.ext (StableRename.erase ρ)
  let ρS : Rename sig (Γ.erase.snoc (.coprod A.erase B.erase))
      (Δ.erase.snoc (.coprod A.erase B.erase)) :=
    Rename.ext (StableRename.erase ρ)
  let σp : Subst sig (Δ.erase.snoc B.erase) Δ.erase := Subst.single p.erase
  let σi : Subst sig (Δ.erase.snoc (.coprod A.erase B.erase)) Δ.erase :=
    Subst.single (.inr p.erase)
  calc
    substComp (tail.liftSubst σp)
        (renameSubst (renameEraseAux ρB tail)
          (tail.liftSubst Subst.injRight)) x =
      substComp (tail.liftSubst σp)
        (tail.liftSubst (renameSubst ρB Subst.injRight)) x := by
          exact congrArg (subst (tail.liftSubst σp))
            (Pending.liftSubst_renameSubst_apply tail ρB
              Subst.injRight x).symm
    _ = tail.liftSubst
        (substComp σp (renameSubst ρB Subst.injRight)) x :=
      Pending.liftSubst_substComp_apply tail σp _ x
    _ = tail.liftSubst (Subst.compRename σi ρS) x := by
      apply Pending.liftSubst_eq_of_pointwise
      intro D y
      cases y <;> rfl
    _ = tail.liftSubst σi (renameEraseAux ρS tail x) := by
      symm
      apply Pending.liftSubst_renameEraseAux_apply
      intro D y
      rfl

theorem Subst.rename_exchange_exts_injLeft_apply {Γ : Ctx sig}
    {A B Q C : Object sig.nBases}
    (x : Var ((Γ.snoc (.coprod A B)).snoc Q) C) :
    Equality.rename
        (Rename.exchange (Γ := Γ) (A := A) (B := Q))
        (Subst.exts (Subst.injLeft (Γ := Γ) (A := A) (B := B)) x) =
      Subst.injLeft (Γ := Γ.snoc Q)
        (Rename.exchange (Γ := Γ) (A := .coprod A B) (B := Q) x) := by
  cases x with
  | here => rfl
  | there y => cases y <;> rfl

theorem Subst.rename_exchange_exts_injRight_apply {Γ : Ctx sig}
    {A B Q C : Object sig.nBases}
    (x : Var ((Γ.snoc (.coprod A B)).snoc Q) C) :
    Equality.rename
        (Rename.exchange (Γ := Γ) (A := B) (B := Q))
        (Subst.exts (Subst.injRight (Γ := Γ) (A := A) (B := B)) x) =
      Subst.injRight (Γ := Γ.snoc Q)
        (Rename.exchange (Γ := Γ) (A := .coprod A B) (B := Q) x) := by
  cases x with
  | here => rfl
  | there y => cases y <;> rfl

theorem Pending.renameExchange_lift_exts_injLeft {Γ : Ctx sig}
    (qs : Pending sig) {A B Q C : Object sig.nBases}
    (x : Var (Pending.eraseAux qs
      ((Γ.snoc (.coprod A B)).snoc Q)) C) :
    Equality.rename
        (renameEraseAux
          (Rename.exchange (Γ := Γ) (A := A) (B := Q)) qs)
        (qs.liftSubst
          (Subst.exts (Subst.injLeft (Γ := Γ) (A := A) (B := B))) x) =
      qs.liftSubst (Subst.injLeft (Γ := Γ.snoc Q))
        (renameEraseAux
          (Rename.exchange (Γ := Γ) (A := .coprod A B) (B := Q)) qs x) := by
  rw [← Pending.liftSubst_renameSubst_apply]
  refine Eq.trans (Pending.liftSubst_eq_of_pointwise qs
    (fun y => Subst.rename_exchange_exts_injLeft_apply y) x) ?_
  symm
  apply Pending.liftSubst_renameEraseAux_apply
  intro D y
  rfl

theorem Pending.renameExchange_lift_exts_injRight {Γ : Ctx sig}
    (qs : Pending sig) {A B Q C : Object sig.nBases}
    (x : Var (Pending.eraseAux qs
      ((Γ.snoc (.coprod A B)).snoc Q)) C) :
    Equality.rename
        (renameEraseAux
          (Rename.exchange (Γ := Γ) (A := B) (B := Q)) qs)
        (qs.liftSubst
          (Subst.exts (Subst.injRight (Γ := Γ) (A := A) (B := B))) x) =
      qs.liftSubst (Subst.injRight (Γ := Γ.snoc Q))
        (renameEraseAux
          (Rename.exchange (Γ := Γ) (A := .coprod A B) (B := Q)) qs x) := by
  rw [← Pending.liftSubst_renameSubst_apply]
  refine Eq.trans (Pending.liftSubst_eq_of_pointwise qs
    (fun y => Subst.rename_exchange_exts_injRight_apply y) x) ?_
  symm
  apply Pending.liftSubst_renameEraseAux_apply
  intro D y
  rfl

theorem Pending.rename_rotateHead_lift_injLeft {Γ : Ctx sig}
    (tail : Pending sig) {A B C : Object sig.nBases}
    (x : Var (Pending.eraseAux tail (Γ.snoc (.coprod A B))) C) :
    Equality.rename (rotateHeadToNewest (Δ := Γ) (H := A) tail)
        (tail.liftSubst (Subst.injLeft (Γ := Γ)) x) =
      Subst.injLeft
        (rotateHeadToNewest (Δ := Γ) (H := .coprod A B) tail x) := by
  induction tail generalizing Γ C with
  | empty => cases x <;> rfl
  | cons Q qs ih =>
      simp only [Pending.liftSubst, rotateHeadToNewest, renameComp]
      change Equality.rename (Rename.comp
        (rotateHeadToNewest (Δ := Γ.snoc Q.erase) (H := A) qs)
        (renameEraseAux
          (Rename.exchange (Γ := Γ) (A := A) (B := Q.erase)) qs))
          _ = _
      rw [← rename_comp, Pending.renameExchange_lift_exts_injLeft]
      exact ih (Γ := Γ.snoc Q.erase)
        (renameEraseAux
          (Rename.exchange (Γ := Γ) (A := .coprod A B) (B := Q.erase)) qs x)

theorem Pending.rename_rotateHead_lift_injRight {Γ : Ctx sig}
    (tail : Pending sig) {A B C : Object sig.nBases}
    (x : Var (Pending.eraseAux tail (Γ.snoc (.coprod A B))) C) :
    Equality.rename (rotateHeadToNewest (Δ := Γ) (H := B) tail)
        (tail.liftSubst (Subst.injRight (Γ := Γ)) x) =
      Subst.injRight
        (rotateHeadToNewest (Δ := Γ) (H := .coprod A B) tail x) := by
  induction tail generalizing Γ C with
  | empty => cases x <;> rfl
  | cons Q qs ih =>
      simp only [Pending.liftSubst, rotateHeadToNewest, renameComp]
      change Equality.rename (Rename.comp
        (rotateHeadToNewest (Δ := Γ.snoc Q.erase) (H := B) qs)
        (renameEraseAux
          (Rename.exchange (Γ := Γ) (A := B) (B := Q.erase)) qs))
          _ = _
      rw [← rename_comp, Pending.renameExchange_lift_exts_injRight]
      exact ih (Γ := Γ.snoc Q.erase)
        (renameEraseAux
          (Rename.exchange (Γ := Γ) (A := .coprod A B) (B := Q.erase)) qs x)

theorem rename_rotateHead_subst_lift_injLeft {Γ : Ctx sig}
    (tail : Pending sig) {A B C : Object sig.nBases}
    (t : Tm (Pending.eraseAux tail (Γ.snoc (.coprod A B))) C) :
    Equality.rename (rotateHeadToNewest (Δ := Γ) (H := A) tail)
        (subst (tail.liftSubst (Subst.injLeft (Γ := Γ))) t) =
      subst (Subst.injLeft (Γ := Pending.eraseAux tail Γ))
        (Equality.rename
          (rotateHeadToNewest (Δ := Γ) (H := .coprod A B) tail) t) := by
  rw [rename_subst, subst_rename]
  apply subst_eq_of_pointwise
  intro D x
  exact Pending.rename_rotateHead_lift_injLeft tail x

theorem rename_rotateHead_subst_lift_injRight {Γ : Ctx sig}
    (tail : Pending sig) {A B C : Object sig.nBases}
    (t : Tm (Pending.eraseAux tail (Γ.snoc (.coprod A B))) C) :
    Equality.rename (rotateHeadToNewest (Δ := Γ) (H := B) tail)
        (subst (tail.liftSubst (Subst.injRight (Γ := Γ))) t) =
      subst (Subst.injRight (Γ := Pending.eraseAux tail Γ))
        (Equality.rename
          (rotateHeadToNewest (Δ := Γ) (H := .coprod A B) tail) t) := by
  rw [rename_subst, subst_rename]
  apply subst_eq_of_pointwise
  intro D x
  exact Pending.rename_rotateHead_lift_injRight tail x

theorem case_committed_eta_pending {Γ : Ctx sig}
    (tail : Pending sig) {A B C : Object sig.nBases}
    (t : Tm (Pending.eraseAux tail (Γ.snoc (.coprod A B))) C) :
    TmEq
      (Equality.rename
        (rotateNewestToHead (Δ := Γ) (A := .coprod A B) tail)
        (.case (.var .here)
          (Equality.rename (Rename.skip1
            (Γ := Pending.eraseAux tail Γ) (A := A) (B := .coprod A B))
            (Equality.rename
              (rotateHeadToNewest (Δ := Γ) (H := A) tail)
              (subst (tail.liftSubst (Subst.injLeft (Γ := Γ))) t)))
          (Equality.rename (Rename.skip1
            (Γ := Pending.eraseAux tail Γ) (A := B) (B := .coprod A B))
            (Equality.rename
              (rotateHeadToNewest (Δ := Γ) (H := B) tail)
              (subst (tail.liftSubst (Subst.injRight (Γ := Γ))) t)))))
      t := by
  let tNew := Equality.rename
    (rotateHeadToNewest (Δ := Γ) (H := .coprod A B) tail) t
  have hL := rename_rotateHead_subst_lift_injLeft tail t
  have hR := rename_rotateHead_subst_lift_injRight tail t
  have hc : TmEq
      (.case (.var .here)
        (Equality.rename (Rename.skip1
          (Γ := Pending.eraseAux tail Γ) (A := A) (B := .coprod A B))
          (Equality.rename
            (rotateHeadToNewest (Δ := Γ) (H := A) tail)
            (subst (tail.liftSubst (Subst.injLeft (Γ := Γ))) t)))
        (Equality.rename (Rename.skip1
          (Γ := Pending.eraseAux tail Γ) (A := B) (B := .coprod A B))
          (Equality.rename
            (rotateHeadToNewest (Δ := Γ) (H := B) tail)
            (subst (tail.liftSubst (Subst.injRight (Γ := Γ))) t))))
      (.case (.var .here)
        (Equality.rename (Rename.skip1
          (Γ := Pending.eraseAux tail Γ) (A := A) (B := .coprod A B))
          (subst (Subst.injLeft (Γ := Pending.eraseAux tail Γ)) tNew))
        (Equality.rename (Rename.skip1
          (Γ := Pending.eraseAux tail Γ) (A := B) (B := .coprod A B))
          (subst (Subst.injRight (Γ := Pending.eraseAux tail Γ)) tNew))) :=
    TmEq.«case» (.refl _)
      (TmEq.rename Rename.skip1 (TmEq.of_eq hL))
      (TmEq.rename Rename.skip1 (TmEq.of_eq hR))
  exact (TmEq.rename _ hc).trans
    ((TmEq.rename _ (case_committed_eta_cut tNew)).trans
      (TmEq.of_eq (rename_rotateNewest_head tail t)))

theorem tmEq_withPendingPosTail (P : Pos sig.nBases)
    {Γ : StableCtx sig} (tail : Pending sig) {G : Goal sig.nBases}
    (k : ∀ {Δ : StableCtx sig}, StableRename Γ Δ →
      PosNeu Δ P → Inv Δ tail G)
    (t : Tm (Pending.eraseAux tail (Γ.erase.snoc P.erase)) G.erase)
    (hk : ∀ {Δ : StableCtx sig} (ρ : StableRename Γ Δ)
      (p : PosNeu Δ P),
      TmEq (k ρ p).erase (instantiatePendingHead tail ρ p t)) :
    TmEq (withPendingPosTail P tail k).erase t := by
  match P with
  | .atom q =>
      have h := hk StableRename.weaken (.atom .here)
      simpa only [withPendingPosTail, Inv.erase, PosNeu.erase,
        eraseInvCtx, Pending.eraseAux, StableCtx.erase_snoc,
        StableTy.erase, Pos.erase] using
        h.trans (TmEq.of_eq
          (instantiatePendingHead_atom_weaken_here tail t))
  | .zero =>
      let z : Tm (Pending.eraseAux tail (Γ.erase.snoc .never)) .never :=
        .var (pendingHeadVar tail)
      exact TmEq.of_never z _ _
  | .sum A B =>
      let tL := subst (tail.liftSubst
        (Subst.injLeft (Γ := Γ.erase) (A := A.erase) (B := B.erase))) t
      let tR := subst (tail.liftSubst
        (Subst.injRight (Γ := Γ.erase) (A := A.erase) (B := B.erase))) t
      have hL := tmEq_withPendingPosTail A tail
        (fun ρ p => k ρ (.inl p)) tL (by
          intro Δ ρ p
          exact (hk ρ (.inl p)).trans (TmEq.of_eq
            (instantiatePendingHead_inl tail ρ p t).symm))
      have hR := tmEq_withPendingPosTail B tail
        (fun ρ p => k ρ (.inr p)) tR (by
          intro Δ ρ p
          exact (hk ρ (.inr p)).trans (TmEq.of_eq
            (instantiatePendingHead_inr tail ρ p t).symm))
      have hc := TmEq.«case»
        (TmEq.refl
          (Tm.var (.here : Var
            ((Pending.eraseAux tail Γ.erase).snoc
              (.coprod A.erase B.erase))
            (.coprod A.erase B.erase))))
        (TmEq.rename (Rename.skip1
          (Γ := Pending.eraseAux tail Γ.erase)
          (A := A.erase) (B := .coprod A.erase B.erase))
          (TmEq.rename
            (rotateHeadToNewest (Δ := Γ.erase) (H := A.erase) tail) hL))
        (TmEq.rename (Rename.skip1
          (Γ := Pending.eraseAux tail Γ.erase)
          (A := B.erase) (B := .coprod A.erase B.erase))
          (TmEq.rename
            (rotateHeadToNewest (Δ := Γ.erase) (H := B.erase) tail) hR))
      rw [withPendingPosTail]
      change TmEq (Inv.erase (.caseSum
        (withPendingPosTail A tail fun ρ p => k ρ (.inl p))
        (withPendingPosTail B tail fun ρ p => k ρ (.inr p)))) t
      simpa only [Inv.erase, eraseInvCtx, Pending.eraseAux, Pos.erase] using
        (TmEq.rename
          (rotateNewestToHead (Δ := Γ.erase)
            (A := .coprod A.erase B.erase) tail) hc).trans
          (case_committed_eta_pending tail t)
  | .shift M =>
      have h := hk StableRename.weaken (.shift (etaNeg M (.var .here)))
      simpa only [withPendingPosTail, Inv.erase, PosNeu.erase,
        eraseInvCtx, Pending.eraseAux, StableCtx.erase_snoc, StableTy.erase,
        Pos.erase, Neg.erase] using
        h.trans (instantiatePendingHead_shift_weaken tail t)

/-! ### Root-context inversion -/

theorem subst_lift_castSnoc {Γ Δ : Ctx sig}
    (tail : Pending sig) {A A' C : Object sig.nBases}
    (h : A' = A) (σ : Subst sig Γ Δ)
    (t : Tm (Pending.eraseAux tail (Γ.snoc A)) C) :
    subst (tail.liftSubst (Subst.exts σ))
        (castTmCtx
          (congrArg (Pending.eraseAux tail)
            (congrArg (Ctx.snoc Γ) h.symm)) t) =
      subst (tail.liftSubst (Subst.extsCast h σ)) t := by
  subst h
  rfl

theorem RootEnv.substComp_single_rename_extendPos_apply
    {Γ : Ctx sig} {Δ Ε : StableCtx sig}
    {A C : Object sig.nBases} (ε : RootEnv Γ Δ)
    (ρ : StableRename Δ Ε) (p : PosNeu Ε (asPos A))
    (x : Var (Γ.snoc A) C) :
    substComp (Subst.single p.erase)
        (renameSubst (Rename.ext (StableRename.erase ρ))
          (RootEnv.extendPos ε)) x =
      RootEnv.erase (RootEnv.snoc (RootEnv.rename ε ρ) p) x := by
  have h := RootEnv.subst0_rename_extendPos ε ρ p (.var x)
  simpa only [subst0, Equality.subst, substComp, renameSubst] using h

theorem instantiatePendingHead_subst_extendPos
    {Γ : Ctx sig} {Δ Ε : StableCtx sig}
    (tail : Pending sig) {A C : Object sig.nBases}
    (ε : RootEnv Γ Δ) (ρ : StableRename Δ Ε)
    (p : PosNeu Ε (asPos A))
    (t : Tm (Pending.eraseAux tail (Γ.snoc A)) C) :
    instantiatePendingHead tail ρ p
        (subst (tail.liftSubst (RootEnv.extendPos ε)) t) =
      subst (tail.liftSubst
        (RootEnv.erase (RootEnv.snoc (RootEnv.rename ε ρ) p))) t := by
  simp only [instantiatePendingHead]
  rw [rename_subst, subst_comp]
  apply subst_eq_of_pointwise
  intro D x
  let ρA : Rename sig (Δ.erase.snoc (asPos A).erase)
      (Ε.erase.snoc (asPos A).erase) :=
    Rename.ext (StableRename.erase ρ)
  let σp : Subst sig (Ε.erase.snoc (asPos A).erase) Ε.erase :=
    Subst.single p.erase
  calc
    substComp (tail.liftSubst σp)
        (renameSubst (renameEraseAux ρA tail)
          (tail.liftSubst (RootEnv.extendPos ε))) x =
      substComp (tail.liftSubst σp)
        (tail.liftSubst
          (renameSubst ρA (RootEnv.extendPos ε))) x := by
            exact congrArg (subst (tail.liftSubst σp))
              (Pending.liftSubst_renameSubst_apply tail ρA
                (RootEnv.extendPos ε) x).symm
    _ = tail.liftSubst
        (substComp σp (renameSubst ρA (RootEnv.extendPos ε))) x :=
      Pending.liftSubst_substComp_apply tail σp _ x
    _ = tail.liftSubst
        (RootEnv.erase (RootEnv.snoc (RootEnv.rename ε ρ) p)) x := by
      apply Pending.liftSubst_eq_of_pointwise
      intro F y
      exact RootEnv.substComp_single_rename_extendPos_apply ε ρ p y

theorem subst_lift_empty (tail : Pending sig)
    {C : Object sig.nBases}
    (t : Tm (Pending.eraseAux tail (.empty : Ctx sig)) C) :
    subst (tail.liftSubst
      (RootEnv.erase (RootEnv.empty : RootEnv (.empty : Ctx sig)
        (.empty : StableCtx sig)))) t = t := by
  refine (subst_eq_of_pointwise ?_ t).trans (subst_ids t)
  intro D x
  calc
    tail.liftSubst
        (RootEnv.erase (RootEnv.empty : RootEnv (.empty : Ctx sig)
          (.empty : StableCtx sig))) x =
      tail.liftSubst (Subst.ids (sig := sig)) x := by
        apply Pending.liftSubst_eq_of_pointwise
        intro F y
        nomatch y
    _ = .var x := Pending.liftSubst_ids_apply tail x

theorem tmEq_withRootContext (Γ : Ctx sig) (tail : Pending sig)
    {G : Goal sig.nBases}
    (k : ∀ {Δ : StableCtx sig}, RootEnv Γ Δ → Inv Δ tail G)
    (t : Tm (Pending.eraseAux tail Γ) G.erase)
    (hk : ∀ {Δ : StableCtx sig} (ε : RootEnv Γ Δ),
      TmEq (k ε).erase (subst (tail.liftSubst ε.erase) t)) :
    TmEq (withRootContext Γ tail k).erase
      (castTmCtx (eraseInvCtx_root Γ tail).symm t) := by
  induction Γ generalizing tail with
  | empty =>
      have h := hk
        (RootEnv.empty : RootEnv (.empty : Ctx sig)
          (.empty : StableCtx sig))
      simpa only [withRootContext, Pending.rootThen, castTmCtx] using
        h.trans (TmEq.of_eq (subst_lift_empty tail t))
  | snoc Γ A ih =>
      let hA : Pending.eraseAux tail (Γ.snoc A) =
          Pending.eraseAux tail (Γ.snoc (asPos A).erase) :=
        congrArg (Pending.eraseAux tail)
          (congrArg (Ctx.snoc Γ) (erase_asPos A).symm)
      let tPol : Tm
          (Pending.eraseAux tail (Γ.snoc (asPos A).erase)) G.erase :=
        castTmCtx hA t
      have hout := ih (.cons (asPos A) tail)
        (fun ε => withPendingPosTail (asPos A) tail fun ρ p =>
          k (RootEnv.snoc (RootEnv.rename ε ρ) p))
        tPol (by
          intro Δ ε
          let u := subst
            ((Pending.cons (asPos A) tail).liftSubst ε.erase) tPol
          have hu : u =
              subst (tail.liftSubst (RootEnv.extendPos ε)) t := by
            exact subst_lift_castSnoc tail (erase_asPos A) ε.erase t
          exact tmEq_withPendingPosTail (asPos A) tail
            (fun ρ p => k (RootEnv.snoc (RootEnv.rename ε ρ) p))
            u (by
              intro Ε ρ p
              have hfinal := hk
                (RootEnv.snoc (RootEnv.rename ε ρ) p)
              have hinst := instantiatePendingHead_subst_extendPos
                tail ε ρ p t
              have hi : instantiatePendingHead tail ρ p u =
                  subst (tail.liftSubst
                    (RootEnv.erase
                      (RootEnv.snoc (RootEnv.rename ε ρ) p))) t :=
                (congrArg (instantiatePendingHead tail ρ p) hu).trans hinst
              exact hfinal.trans (TmEq.of_eq hi.symm)))
      rw [withRootContext]
      refine hout.trans (TmEq.of_eq ?_)
      exact castTmCtx_comp hA
        (eraseInvCtx_root Γ (.cons (asPos A) tail)).symm
        (eraseInvCtx_root (Γ.snoc A) tail).symm t

/-! ### Final producer preservation -/

theorem Inv.erase_castPending {Γ : StableCtx sig} {ps qs : Pending sig}
    {G : Goal sig.nBases} (h : ps = qs) (d : Inv Γ ps G) :
    (Inv.castPending h d).erase =
      castTmCtx (congrArg (eraseInvCtx Γ) h) d.erase := by
  subst h
  rfl

theorem eraseInvCtx_asPending (Γ : Ctx sig) :
    eraseInvCtx (.empty : StableCtx sig) (asPending Γ) = Γ := by
  simpa only [eraseInvCtx, StableCtx.erase, Pending.erase] using
    erase_asPending Γ

/-- Exact preservation theorem at the public producer boundary. -/
theorem tmEq_focusRoot {Γ : Ctx sig} {A : Object sig.nBases}
    (t : Tm Γ A) :
    TmEq (focusRoot t).erase
      (castTmCtx (eraseInvCtx_asPending Γ).symm
        (castTmObject (erase_asNeg A).symm t)) := by
  let d : Inv (.empty : StableCtx sig) (Pending.rootThen Γ .empty)
      (.neg (asNeg A)) :=
    withRootContext Γ .empty fun ε => focusOpen ε t
  have hd : TmEq d.erase
      (castTmCtx (eraseInvCtx_root Γ .empty).symm
        (castTmObject (erase_asNeg A).symm t)) :=
    tmEq_withRootContext Γ .empty
      (fun ε => focusOpen ε t)
      (castTmObject (erase_asNeg A).symm t) (by
        intro Δ ε
        refine (tmEq_focusOpen ε t).trans (TmEq.of_eq ?_)
        exact castTmObject_subst (erase_asNeg A).symm ε.erase t)
  let hp : Pending.rootThen Γ .empty = asPending Γ :=
    Pending.rootThen_empty Γ
  let hpCtx := congrArg (eraseInvCtx (.empty : StableCtx sig)) hp
  have hdc := TmEq.castCtx hpCtx hd
  change TmEq (Inv.castPending hp d).erase _
  refine (TmEq.of_eq (Inv.erase_castPending hp d)).trans (hdc.trans ?_)
  exact TmEq.of_eq (castTmCtx_comp
    (eraseInvCtx_root Γ .empty).symm hpCtx
    (eraseInvCtx_asPending Γ).symm
    (castTmObject (erase_asNeg A).symm t))

/-- Friendly cast-back form: after erasing the polarized root context and
goal casts, the producer is equal to the original public term. -/
theorem tmEq_focusRoot_castBack {Γ : Ctx sig} {A : Object sig.nBases}
    (t : Tm Γ A) :
    TmEq
      (castTmCtx (eraseInvCtx_asPending Γ) (focusRoot t).erase)
      (castTmObject (erase_asNeg A).symm t) := by
  have h := TmEq.castCtx (eraseInvCtx_asPending Γ) (tmEq_focusRoot t)
  exact h.trans (TmEq.of_eq (castTmCtx_comp
    (eraseInvCtx_asPending Γ).symm (eraseInvCtx_asPending Γ) rfl
    (castTmObject (erase_asNeg A).symm t)))

/-! ### Final theorem-level regression fixtures -/

namespace FocusRootPreserveFixtures

open FocusRootFixtures

theorem opaque_root_generator_preserved :
    TmEq
      (castTmCtx (eraseInvCtx_asPending (genCtx sigOpaque))
        (focusRoot opaqueGeneratorAppTm).erase)
      (castTmObject (erase_asNeg OpaqueX).symm opaqueGeneratorAppTm) :=
  tmEq_focusRoot_castBack opaqueGeneratorAppTm

abbrev TwoUnitCtx : Ctx Fixtures.sig0 :=
  (.empty : Ctx Fixtures.sig0).snoc .unit |>.snoc .unit

/-- The oldest and newest source variables retain their de Bruijn order. -/
def twoUnitOrderTm : Tm (sig := Fixtures.sig0) TwoUnitCtx
    (.prod .unit .unit) :=
  .pair (.var (.there .here)) (.var .here)

theorem multi_variable_context_order_preserved :
    TmEq
      (castTmCtx (eraseInvCtx_asPending TwoUnitCtx)
        (focusRoot twoUnitOrderTm).erase)
      (castTmObject (erase_asNeg (.prod .unit .unit)).symm
        twoUnitOrderTm) :=
  tmEq_focusRoot_castBack twoUnitOrderTm

theorem beta_application_preserved :
    TmEq
      (castTmCtx (eraseInvCtx_asPending (.empty : Ctx Fixtures.sig0))
        (focusRoot betaIdentityTm).erase)
      (castTmObject (erase_asNeg UnitObj).symm betaIdentityTm) :=
  tmEq_focusRoot_castBack betaIdentityTm

theorem case_produced_function_application_preserved :
    TmEq
      (castTmCtx (eraseInvCtx_asPending (.empty : Ctx Fixtures.sig0))
        (focusRoot caseFunctionAppliedTm).erase)
      (castTmObject (erase_asNeg UnitObj).symm caseFunctionAppliedTm) :=
  tmEq_focusRoot_castBack caseFunctionAppliedTm

end FocusRootPreserveFixtures

end Gimbal.Equality.Scherer
