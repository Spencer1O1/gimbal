/-
  Focusing preserves meaning.

  Every hereditary operation is sound for the equational theory `TmEq` (hence
  for the categorical interpretation), so `focusTm t` erases to a term equal to
  `t`. Together with `wellInv_focusTm` this says focusing computes a *focused
  representative* of every intrinsic term.
-/

import Gimbal.Equality.Hereditary
import Gimbal.Equality.TmEq

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Substitution idioms used by the hereditary operations -/

/-- Substituting the newest variable for itself contracts the two binders. -/
theorem subst0_var_here {Γ : Ctx sig} {A C : Object sig.nBases}
    (t : Tm (Γ ▻ A ▻ A) C) :
    subst0 t (.var .here) = rename Rename.diag t := by
  rw [subst0, ← subst_ids (rename Rename.diag t), subst_rename]
  refine subst_eq_of_pointwise ?_ t
  intro B x
  match x with
  | .here => rfl
  | .there .here => rfl
  | .there (.there _) => rfl

/-- Exchanging the two newest binders turns `subst0` into a substitution under one. -/
theorem subst0_rename_exchange {Γ : Ctx sig} {A B C : Object sig.nBases}
    (t : Tm (Γ ▻ A ▻ B) C) (v : Tm Γ A) :
    subst0 (rename Rename.exchange t) (weakenTerm v) =
      subst (Subst.exts (Subst.single v)) t := by
  rw [subst0, subst_rename]
  refine subst_eq_of_pointwise ?_ t
  intro D x
  match x with
  | .here => rfl
  | .there .here => rfl
  | .there (.there _) => rfl

/--
`letPos` / `case` exchange on erasures: cutting an independent observation
through a `case` equals casing then cutting in each branch (with binder
exchange). Erasure form of `ICCEq.case_letPos`.
-/
theorem cc_case_letPos {Γ : Ctx sig} {A B P C : Object sig.nBases}
    (m : Tm Γ (.coprod A B)) (n : Tm Γ P)
    (tL : Tm (Γ ▻ P ▻ A) C) (tR : Tm (Γ ▻ P ▻ B) C) :
    TmEq
      (subst0 (.case (weakenTerm m) tL tR) n)
      (.case m
        (subst0 (rename Rename.exchange tL) (weakenTerm n))
        (subst0 (rename Rename.exchange tR) (weakenTerm n))) := by
  apply TmEq.of_eq
  change
      Tm.case (subst0 (weakenTerm m) n)
        (subst (Subst.exts (Subst.single n)) tL)
        (subst (Subst.exts (Subst.single n)) tR) =
      Tm.case m
        (subst0 (rename Rename.exchange tL) (weakenTerm n))
        (subst0 (rename Rename.exchange tR) (weakenTerm n))
  rw [subst0_weakenTerm]
  -- `subst0_rename_exchange` has binders `(Γ ▻ A ▻ B)` with cut of type `A`;
  -- here the case binder is newest (`A`/`B`) and the observation `P` is older,
  -- so exchange then cut matches `exts (single n)` on the unexchanged body.
  have hL :
      subst0 (rename Rename.exchange tL) (weakenTerm n) =
        subst (Subst.exts (Subst.single n)) tL := by
    -- Rename.exchange : (Γ ▻ P ▻ A) → (Γ ▻ A ▻ P); cut has type A after exchange?
    -- Actually after exchange newest is P, and we cut with weaken n : Γ ▻ A ⊢ P.
    -- subst0_rename_exchange expects t : Γ ▻ A ▻ B with cut : Γ ⊢ A.
    -- We need the symmetric form: t : Γ ▻ P ▻ A, cut : Γ ⊢ P.
    -- Prove by unfolding like subst0_rename_exchange with swapped roles.
    rw [subst0, subst_rename]
    refine subst_eq_of_pointwise ?_ tL
    intro D x
    match x with
    | .here =>
        -- exchange maps here (A) to there here; exts (single n) on here = var here
        -- after rename+subst0 with weaken n on (Γ ▻ A ▻ P): here ↦ weaken n? No:
        -- After exchange, here is P-binder; subst0 (weaken n) substitutes n for P.
        -- Pointwise on original tL's here (A): exchange sends it to there.here (A under P);
        -- subst0 (weaken n) leaves there.here as var here (A). Good = exts here.
        rfl
    | .there .here =>
        rfl
    | .there (.there _) =>
        rfl
  have hR :
      subst0 (rename Rename.exchange tR) (weakenTerm n) =
        subst (Subst.exts (Subst.single n)) tR := by
    rw [subst0, subst_rename]
    refine subst_eq_of_pointwise ?_ tR
    intro D x
    match x with
    | .here => rfl
    | .there .here => rfl
    | .there (.there _) => rfl
  rw [hL, hR]

/-- A branch pushed under an extra binder is unaffected by the `letPos` cut. -/
theorem subst_exts_single_rename_skip1 {Γ : Ctx sig} {A P C : Object sig.nBases}
    (t : Tm (Γ ▻ A) C) (n : Tm Γ P) :
    subst (Subst.exts (Subst.single n)) (rename Rename.skip1 t) = t := by
  rw [subst_rename]
  refine Eq.trans (subst_eq_of_pointwise (τ := fun {_} => Subst.ids) ?_ t)
    (subst_ids t)
  intro B x
  cases x <;> rfl

/-- The two cuts of a `letPos` may be performed in either order. -/
theorem subst0_subst0_comm {Γ : Ctx sig} {A P C : Object sig.nBases}
    (t : Tm (Γ ▻ A ▻ P) C) (n : Tm (Γ ▻ A) P) (v : Tm Γ A) :
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
  | .there .here =>
      exact subst0_weakenTerm v (subst (Subst.single v) n)
  | .there (.there _) => rfl

/-! ### Identity expansion and injections preserve meaning -/

-- Push `erase` through the focused constructors.
attribute [local simp] InvTm.erase FocTm.erase PosIntro.erase NegElim.erase
  SatTm.erase PosNeu.erase NegNeu.erase InvTm.erase_weaken NegNeu.erase_weaken

theorem tmEq_eta : ∀ (A : Object sig.nBases) {Γ : Ctx sig} (n : NegNeu Γ A),
    TmEq (NegNeu.eta A n).erase n.erase := by
  intro A
  induction A with
  | base q => intro Γ n; exact .refl _
  | unit => intro Γ n; exact (TmEq.eta_unit n.erase).symm
  | never => intro Γ n; exact TmEq.of_never n.erase _ _
  | prod A B ihA ihB =>
      intro Γ n
      exact (TmEq.pair (ihA (.fst n)) (ihB (.snd n))).trans (TmEq.eta_prod n.erase)
  | coprod A B _ _ => intro Γ n; exact .refl _
  | exp A B ihA ihB =>
      intro Γ n
      refine TmEq.trans (TmEq.lam ?_) (TmEq.eta_lam n.erase)
      refine (ihB (.app (NegNeu.weaken n) (NegNeu.eta A (.var .here)))).trans ?_
      simp only [NegNeu.erase, NegNeu.erase_weaken]
      exact TmEq.app (.refl _) (ihA (.var .here))

theorem tmEq_toInv {Γ : Ctx sig} {A : Object sig.nBases} (p : PosNeu Γ A) :
    TmEq p.toInv.erase p.erase := by
  cases p with
  | neu n => exact tmEq_eta _ n
  | inl q => exact .refl _
  | inr q => exact .refl _
  | val t => exact .refl _

theorem tmEq_hinl {Γ : Ctx sig} {A : Object sig.nBases} (B : Object sig.nBases)
    (t : InvTm Γ A) : TmEq (InvTm.hinl B t).erase (.inl t.erase) := by
  induction t using InvTm.hinl.induct generalizing B with
  | case1 _ _ _ _ n t u iht ihu =>
      simp only [InvTm.hinl, InvTm.erase]
      exact (TmEq.case (.refl _) (iht B) (ihu B)).trans
        (TmEq.cc_inl_case n.erase t.erase u.erase).symm
  | case2 _ _ n => exact TmEq.of_never n.erase _ _
  | case3 _ _ _ n t iht =>
      simp only [InvTm.hinl, InvTm.erase, FocTm.erase]
      exact TmEq.subst0_congr (iht B) (.refl _)
  | case4 _ _ s t iht =>
      simp only [InvTm.hinl, InvTm.erase, FocTm.erase, SatTm.erase]
      exact iht B
  | case5 => exact .refl _
  | case6 _ _ n =>
      simp only [InvTm.hinl, InvTm.erase, FocTm.erase, PosIntro.erase,
        PosNeu.erase, NegElim.erase]
      exact TmEq.inl (tmEq_eta _ n)
  | case7 => exact .refl _
  | case8 => exact .refl _
  | case9 => exact .refl _

theorem tmEq_hinr {Γ : Ctx sig} {B : Object sig.nBases} (A : Object sig.nBases)
    (t : InvTm Γ B) : TmEq (InvTm.hinr A t).erase (.inr t.erase) := by
  induction t using InvTm.hinr.induct generalizing A with
  | case1 _ _ _ _ n t u iht ihu =>
      simp only [InvTm.hinr, InvTm.erase]
      exact (TmEq.case (.refl _) (iht A) (ihu A)).trans
        (TmEq.cc_inr_case n.erase t.erase u.erase).symm
  | case2 _ _ n => exact TmEq.of_never n.erase _ _
  | case3 _ _ _ n t iht =>
      simp only [InvTm.hinr, InvTm.erase, FocTm.erase]
      exact TmEq.subst0_congr (iht A) (.refl _)
  | case4 _ _ s t iht =>
      simp only [InvTm.hinr, InvTm.erase, FocTm.erase, SatTm.erase]
      exact iht A
  | case5 => exact .refl _
  | case6 _ _ n =>
      simp only [InvTm.hinr, InvTm.erase, FocTm.erase, PosIntro.erase,
        PosNeu.erase, NegElim.erase]
      exact TmEq.inr (tmEq_eta _ n)
  | case7 => exact .refl _
  | case8 => exact .refl _
  | case9 => exact .refl _

/-- The η-expanded left injection means what it looks like. -/
theorem tmEq_etaInl {Γ : Ctx sig} (A B : Object sig.nBases) :
    TmEq (InvTm.etaInl (Γ := Γ) A B).erase (.inl (.var .here)) :=
  (tmEq_hinl B _).trans (TmEq.inl (tmEq_eta A (.var .here)))

/-- The η-expanded right injection means what it looks like. -/
theorem tmEq_etaInr {Γ : Ctx sig} (A B : Object sig.nBases) :
    TmEq (InvTm.etaInr (Γ := Γ) A B).erase (.inr (.var .here)) :=
  (tmEq_hinr A _).trans (TmEq.inr (tmEq_eta B (.var .here)))

/-! ### Hereditary substitution preserves meaning -/

/-- Erasure of a spine-substitution result. -/
def HSubst.erase {Γ : Ctx sig} {A C : Object sig.nBases} :
    HSubst Γ A C → Tm Γ C
  | .neu n => n.erase
  | .here w _ => w.erase
  | .val w _ => w.erase

/-- Only the cut variable itself reduces to `HSubst.here`. -/
theorem hsubstNeu_eq_here {Γ : Ctx sig} {A C : Object sig.nBases}
    {n : NegNeu (Γ ▻ A) C} {v : InvTm Γ A} {w : InvTm Γ C} {h : A = C}
    (heq : hsubstNeu n v = .here w h) :
    HEq n (NegNeu.var (Var.here : Var (Γ ▻ A) A)) := by
  cases n with
  | var x =>
      cases x with
      | here => exact HEq.refl _
      | there y => rw [hsubstNeu] at heq; cases heq
  | app m u =>
      rw [hsubstNeu] at heq; split at heq <;> cases heq
  | fst m =>
      rw [hsubstNeu] at heq; split at heq <;> cases heq
  | snd m =>
      rw [hsubstNeu] at heq; split at heq <;> cases heq

mutual

theorem tmEq_happ {Γ : Ctx sig} {A B : Object sig.nBases}
    (f : InvTm Γ (.exp A B)) (u : InvTm Γ A) :
    TmEq (happ f u).erase (.app f.erase u.erase) := by
  match f with
  | .lam body =>
      rw [happ]
      exact (tmEq_hsubstInv body u).trans (TmEq.beta_app body.erase u.erase).symm
  | .case n t₁ t₂ =>
      rw [happ]
      simp only [InvTm.erase]
      refine TmEq.trans ?_
        (TmEq.cc_app_case n.erase t₁.erase t₂.erase u.erase).symm
      refine TmEq.case (.refl _) ?_ ?_
      · simpa using tmEq_happ t₁ (InvTm.weaken u)
      · simpa using tmEq_happ t₂ (InvTm.weaken u)
  | .abort n => exact TmEq.of_never n.erase _ _
  | .foc (.pos (.done (.neu n))) =>
      rw [happ]; exact tmEq_eta B (.app n u)
  | .foc (.pos (.done (.val w))) => rw [happ]; exact tmEq_happ w u
  | .foc (.neg (.done n)) => rw [happ]; exact tmEq_eta B (.app n u)
  | .foc (.letPos n w) =>
      rw [happ]
      simp only [InvTm.erase, FocTm.erase]
      have h1 : TmEq (happ w (InvTm.weaken u)).erase
          (Tm.app w.erase (weakenTerm u.erase)) := by
        simpa using tmEq_happ w (InvTm.weaken u)
      refine TmEq.trans (TmEq.subst0_congr h1 (TmEq.refl n.erase))
        (TmEq.of_eq ?_)
      show Tm.app (subst0 w.erase n.erase)
        (subst0 (weakenTerm u.erase) n.erase) = _
      rw [subst0_weakenTerm]
  | .foc (.sat (.mk s w)) => rw [happ]; exact tmEq_happ w u
termination_by (objectSize (Object.exp A B), 0, f.size)

theorem tmEq_hfst {Γ : Ctx sig} {A B : Object sig.nBases}
    (t : InvTm Γ (.prod A B)) : TmEq (hfst t).erase (.fst t.erase) := by
  match t with
  | .pair t₁ t₂ =>
      rw [hfst]; exact (TmEq.beta_fst t₁.erase t₂.erase).symm
  | .case n t₁ t₂ =>
      rw [hfst]
      simp only [InvTm.erase]
      exact (TmEq.case (.refl _) (tmEq_hfst t₁) (tmEq_hfst t₂)).trans
        (TmEq.cc_fst_case n.erase t₁.erase t₂.erase).symm
  | .abort n => exact TmEq.of_never n.erase _ _
  | .foc (.pos (.done (.neu n))) => rw [hfst]; exact tmEq_eta A (.fst n)
  | .foc (.pos (.done (.val w))) => rw [hfst]; exact tmEq_hfst w
  | .foc (.neg (.done n)) => rw [hfst]; exact tmEq_eta A (.fst n)
  | .foc (.letPos n w) =>
      rw [hfst]
      simp only [InvTm.erase, FocTm.erase]
      exact TmEq.subst0_congr (tmEq_hfst w) (.refl _)
  | .foc (.sat (.mk s w)) => rw [hfst]; exact tmEq_hfst w
termination_by (objectSize (Object.prod A B), 0, t.size)

theorem tmEq_hsnd {Γ : Ctx sig} {A B : Object sig.nBases}
    (t : InvTm Γ (.prod A B)) : TmEq (hsnd t).erase (.snd t.erase) := by
  match t with
  | .pair t₁ t₂ =>
      rw [hsnd]; exact (TmEq.beta_snd t₁.erase t₂.erase).symm
  | .case n t₁ t₂ =>
      rw [hsnd]
      simp only [InvTm.erase]
      exact (TmEq.case (.refl _) (tmEq_hsnd t₁) (tmEq_hsnd t₂)).trans
        (TmEq.cc_snd_case n.erase t₁.erase t₂.erase).symm
  | .abort n => exact TmEq.of_never n.erase _ _
  | .foc (.pos (.done (.neu n))) => rw [hsnd]; exact tmEq_eta B (.snd n)
  | .foc (.pos (.done (.val w))) => rw [hsnd]; exact tmEq_hsnd w
  | .foc (.neg (.done n)) => rw [hsnd]; exact tmEq_eta B (.snd n)
  | .foc (.letPos n w) =>
      rw [hsnd]
      simp only [InvTm.erase, FocTm.erase]
      exact TmEq.subst0_congr (tmEq_hsnd w) (.refl _)
  | .foc (.sat (.mk s w)) => rw [hsnd]; exact tmEq_hsnd w
termination_by (objectSize (Object.prod A B), 0, t.size)

theorem tmEq_hcase {Γ : Ctx sig} {A B C : Object sig.nBases}
    (s : InvTm Γ (.coprod A B)) (l : InvTm (Γ ▻ A) C) (r : InvTm (Γ ▻ B) C) :
    TmEq (hcase s l r).erase (.case s.erase l.erase r.erase) := by
  match s with
  | .case n s₁ s₂ =>
      rw [hcase]
      simp only [InvTm.erase]
      refine TmEq.trans ?_
        (TmEq.cc_case_case n.erase s₁.erase s₂.erase l.erase r.erase).symm
      refine TmEq.case (.refl _) ?_ ?_
      · simpa [InvTm.erase_rename] using
          tmEq_hcase s₁ (InvTm.rename Rename.skip1 l)
            (InvTm.rename Rename.skip1 r)
      · simpa [InvTm.erase_rename] using
          tmEq_hcase s₂ (InvTm.rename Rename.skip1 l)
            (InvTm.rename Rename.skip1 r)
  | .abort n => exact TmEq.of_never n.erase _ _
  | .foc (.pos (.done (.neu n))) => rw [hcase]; exact .refl _
  | .foc (.pos (.done (.inl p))) =>
      rw [hcase]
      refine (tmEq_hsubstInv l p.toInv).trans ?_
      refine TmEq.trans (TmEq.subst0_congr (.refl _) (tmEq_toInv p)) ?_
      exact (TmEq.beta_case_inl p.erase l.erase r.erase).symm
  | .foc (.pos (.done (.inr p))) =>
      rw [hcase]
      refine (tmEq_hsubstInv r p.toInv).trans ?_
      refine TmEq.trans (TmEq.subst0_congr (.refl _) (tmEq_toInv p)) ?_
      exact (TmEq.beta_case_inr p.erase l.erase r.erase).symm
  | .foc (.pos (.done (.val w))) => rw [hcase]; exact tmEq_hcase w l r
  | .foc (.neg (.done n)) => rw [hcase]; exact .refl _
  | .foc (.letPos n w) =>
      rw [hcase]
      simp only [InvTm.erase, FocTm.erase]
      have h1 : TmEq (hcase w (InvTm.rename Rename.skip1 l)
            (InvTm.rename Rename.skip1 r)).erase
          (Tm.case w.erase (rename Rename.skip1 l.erase)
            (rename Rename.skip1 r.erase)) := by
        simpa [InvTm.erase_rename] using
          tmEq_hcase w (InvTm.rename Rename.skip1 l)
            (InvTm.rename Rename.skip1 r)
      refine TmEq.trans (TmEq.subst0_congr h1 (TmEq.refl n.erase))
        (TmEq.of_eq ?_)
      · show Tm.case (subst0 w.erase n.erase)
          (subst (Subst.exts (Subst.single n.erase))
            (rename Rename.skip1 l.erase))
          (subst (Subst.exts (Subst.single n.erase))
            (rename Rename.skip1 r.erase)) = _
        rw [subst_exts_single_rename_skip1, subst_exts_single_rename_skip1]
  | .foc (.sat (.mk sc w)) => rw [hcase]; exact tmEq_hcase w l r
termination_by (objectSize (Object.coprod A B), 0, s.size)

theorem tmEq_hsubstInv {Γ : Ctx sig} {A C : Object sig.nBases}
    (t : InvTm (Γ ▻ A) C) (v : InvTm Γ A) :
    TmEq (hsubstInv t v).erase (subst0 t.erase v.erase) := by
  match t with
  | .unit => rw [hsubstInv]; exact .refl _
  | .pair t₁ t₂ =>
      rw [hsubstInv]
      simp only [InvTm.erase]
      exact TmEq.pair (tmEq_hsubstInv t₁ v) (tmEq_hsubstInv t₂ v)
  | .lam t₁ =>
      rw [hsubstInv]
      simp only [InvTm.erase]
      have hb : TmEq
          (hsubstInv (InvTm.rename Rename.exchange t₁) (InvTm.weaken v)).erase
          (subst (Subst.exts (Subst.single v.erase)) t₁.erase) := by
        refine (tmEq_hsubstInv (InvTm.rename Rename.exchange t₁)
          (InvTm.weaken v)).trans (TmEq.of_eq ?_)
        simp only [InvTm.erase_rename, InvTm.erase_weaken]
        exact subst0_rename_exchange t₁.erase v.erase
      exact TmEq.lam hb
  | .case n t₁ t₂ =>
      rw [hsubstInv]
      have hn := tmEq_hsubstNeu n v
      have hb₁ : TmEq
          (hsubstInv (InvTm.rename Rename.exchange t₁) (InvTm.weaken v)).erase
          (subst (Subst.exts (Subst.single v.erase)) t₁.erase) := by
        refine (tmEq_hsubstInv (InvTm.rename Rename.exchange t₁)
          (InvTm.weaken v)).trans (TmEq.of_eq ?_)
        simp only [InvTm.erase_rename, InvTm.erase_weaken]
        exact subst0_rename_exchange t₁.erase v.erase
      have hb₂ : TmEq
          (hsubstInv (InvTm.rename Rename.exchange t₂) (InvTm.weaken v)).erase
          (subst (Subst.exts (Subst.single v.erase)) t₂.erase) := by
        refine (tmEq_hsubstInv (InvTm.rename Rename.exchange t₂)
          (InvTm.weaken v)).trans (TmEq.of_eq ?_)
        simp only [InvTm.erase_rename, InvTm.erase_weaken]
        exact subst0_rename_exchange t₂.erase v.erase
      split
      · rename_i n' heq
        rw [heq] at hn
        simp only [HSubst.erase] at hn
        simp only [InvTm.erase]
        exact TmEq.case hn hb₁ hb₂
      · rename_i w h heq
        rw [heq] at hn
        simp only [HSubst.erase] at hn
        exact (tmEq_hcase w _ _).trans (TmEq.case hn hb₁ hb₂)
      · rename_i w hlt heq
        rw [heq] at hn
        simp only [HSubst.erase] at hn
        exact (tmEq_hcase w _ _).trans (TmEq.case hn hb₁ hb₂)
  | .abort n =>
      rw [hsubstInv]
      have hn := tmEq_hsubstNeu n v
      split
      · rename_i n' heq
        rw [heq] at hn
        simp only [HSubst.erase] at hn
        simp only [InvTm.erase]
        exact TmEq.abort hn
      · rename_i w h heq
        exact TmEq.of_never (subst0 (NegNeu.erase n) v.erase) _ _
      · rename_i w hlt heq
        exact TmEq.of_never (subst0 (NegNeu.erase n) v.erase) _ _
  | .foc (.pos (.done p)) => rw [hsubstInv]; exact tmEq_hsubstPos p v
  | .foc (.neg (.done n)) =>
      rw [hsubstInv]
      have hn := tmEq_hsubstNeu n v
      split
      · rename_i n' heq
        rw [heq] at hn
        simp only [HSubst.erase] at hn
        exact (tmEq_eta C n').trans hn
      · rename_i w h heq
        rw [heq] at hn
        simp only [HSubst.erase] at hn
        exact hn
      · rename_i w hlt heq
        rw [heq] at hn
        simp only [HSubst.erase] at hn
        exact hn
  | .foc (.letPos (P := P) n t₁) =>
      rw [hsubstInv]
      have hn := tmEq_hsubstNeu n v
      have hb : TmEq
          (hsubstInv (InvTm.rename Rename.exchange t₁) (InvTm.weaken v)).erase
          (subst (Subst.exts (Subst.single v.erase)) t₁.erase) := by
        refine (tmEq_hsubstInv (InvTm.rename Rename.exchange t₁)
          (InvTm.weaken v)).trans (TmEq.of_eq ?_)
        simp only [InvTm.erase_rename, InvTm.erase_weaken]
        exact subst0_rename_exchange t₁.erase v.erase
      split
      · rename_i n' heq
        rw [heq] at hn
        simp only [HSubst.erase] at hn
        simp only [InvTm.erase, FocTm.erase]
        refine TmEq.trans (TmEq.subst0_congr hb hn) (TmEq.of_eq ?_)
        exact subst0_subst0_comm t₁.erase n.erase v.erase
      · rename_i w h heq
        have hrec := tmEq_hsubstInv (InvTm.rename (Rename.diagEq h) t₁) v
        have hvar := hsubstNeu_eq_here heq
        subst h
        have hn0 : n = NegNeu.var (Var.here : Var (Γ ▻ A) A) := eq_of_heq hvar
        subst hn0
        simp only [InvTm.erase, FocTm.erase, NegNeu.erase]
        refine hrec.trans (TmEq.of_eq ?_)
        simp only [InvTm.erase_rename]
        rw [subst0_var_here]
        rfl
      · rename_i w hlt heq
        rw [heq] at hn
        simp only [HSubst.erase] at hn
        simp only [InvTm.erase, FocTm.erase]
        refine TmEq.trans (tmEq_hsubstInv
          (hsubstInv (InvTm.rename Rename.exchange t₁) (InvTm.weaken v)) w) ?_
        refine TmEq.trans (TmEq.subst0_congr hb hn) (TmEq.of_eq ?_)
        exact subst0_subst0_comm t₁.erase n.erase v.erase
  | .foc (.sat (.mk s t₁)) =>
      rw [hsubstInv]
      simp only [InvTm.erase, FocTm.erase, SatTm.erase]
      exact tmEq_hsubstInv t₁ v
termination_by (objectSize A, 1, t.size)
decreasing_by
  all_goals
    first
    | decreasing_tactic
    | (subst_vars; decreasing_tactic)

theorem tmEq_hsubstPos {Γ : Ctx sig} {A C : Object sig.nBases}
    (p : PosNeu (Γ ▻ A) C) (v : InvTm Γ A) :
    TmEq (hsubstPos p v).erase (subst0 p.erase v.erase) := by
  match p with
  | .neu n =>
      rw [hsubstPos]
      have hn := tmEq_hsubstNeu n v
      split
      · rename_i n' heq
        rw [heq] at hn
        simp only [HSubst.erase] at hn
        exact (tmEq_eta C n').trans hn
      · rename_i w h heq
        rw [heq] at hn
        simp only [HSubst.erase] at hn
        exact hn
      · rename_i w hlt heq
        rw [heq] at hn
        simp only [HSubst.erase] at hn
        exact hn
  | .inl (B := B₁) q =>
      rw [hsubstPos]
      refine (tmEq_hinl B₁ (hsubstPos q v)).trans ?_
      exact TmEq.inl (tmEq_hsubstPos q v)
  | .inr (A := A₁) q =>
      rw [hsubstPos]
      refine (tmEq_hinr A₁ (hsubstPos q v)).trans ?_
      exact TmEq.inr (tmEq_hsubstPos q v)
  | .val t => rw [hsubstPos]; exact tmEq_hsubstInv t v
termination_by (objectSize A, 1, p.size)

theorem tmEq_hsubstNeu {Γ : Ctx sig} {A C : Object sig.nBases}
    (n : NegNeu (Γ ▻ A) C) (v : InvTm Γ A) :
    TmEq (hsubstNeu n v).erase (subst0 n.erase v.erase) := by
  match n with
  | .var .here => rw [hsubstNeu]; exact .refl _
  | .var (.there x) => rw [hsubstNeu]; exact .refl _
  | .app m u =>
      rw [hsubstNeu]
      have hm := tmEq_hsubstNeu m v
      split
      · rename_i m' heq
        rw [heq] at hm
        simp only [HSubst.erase] at hm
        simp only [HSubst.erase, NegNeu.erase]
        exact TmEq.app hm (tmEq_hsubstInv u v)
      · rename_i w h heq
        rw [heq] at hm
        simp only [HSubst.erase] at hm
        simp only [HSubst.erase, NegNeu.erase]
        exact (tmEq_happ w (hsubstInv u v)).trans
          (TmEq.app hm (tmEq_hsubstInv u v))
      · rename_i w hlt heq
        rw [heq] at hm
        simp only [HSubst.erase] at hm
        simp only [HSubst.erase, NegNeu.erase]
        exact (tmEq_happ w (hsubstInv u v)).trans
          (TmEq.app hm (tmEq_hsubstInv u v))
  | .fst m =>
      rw [hsubstNeu]
      have hm := tmEq_hsubstNeu m v
      split
      · rename_i m' heq
        rw [heq] at hm
        simp only [HSubst.erase] at hm
        simp only [HSubst.erase, NegNeu.erase]
        exact TmEq.fst hm
      · rename_i w h heq
        rw [heq] at hm
        simp only [HSubst.erase] at hm
        simp only [HSubst.erase, NegNeu.erase]
        exact (tmEq_hfst w).trans (TmEq.fst hm)
      · rename_i w hlt heq
        rw [heq] at hm
        simp only [HSubst.erase] at hm
        simp only [HSubst.erase, NegNeu.erase]
        exact (tmEq_hfst w).trans (TmEq.fst hm)
  | .snd m =>
      rw [hsubstNeu]
      have hm := tmEq_hsubstNeu m v
      split
      · rename_i m' heq
        rw [heq] at hm
        simp only [HSubst.erase] at hm
        simp only [HSubst.erase, NegNeu.erase]
        exact TmEq.snd hm
      · rename_i w h heq
        rw [heq] at hm
        simp only [HSubst.erase] at hm
        simp only [HSubst.erase, NegNeu.erase]
        exact (tmEq_hsnd w).trans (TmEq.snd hm)
      · rename_i w hlt heq
        rw [heq] at hm
        simp only [HSubst.erase] at hm
        simp only [HSubst.erase, NegNeu.erase]
        exact (tmEq_hsnd w).trans (TmEq.snd hm)
termination_by (objectSize A, 1, n.size)
decreasing_by
  all_goals
    first
    | decreasing_tactic
    | (subst_vars; decreasing_tactic)

end

/-! ### Focusing preserves meaning -/

/-- Focusing computes a focused representative: the erasure is `TmEq` to the input. -/
theorem tmEq_focusTm {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) :
    TmEq (focusTm t).erase t := by
  induction t with
  | var x => exact tmEq_eta _ (.var x)
  | unit => exact .refl _
  | abort t ih => exact TmEq.of_never (focusTm t).erase _ _
  | pair _ _ iht ihu => exact TmEq.pair iht ihu
  | fst t ih => exact (tmEq_hfst (focusTm t)).trans (TmEq.fst ih)
  | snd t ih => exact (tmEq_hsnd (focusTm t)).trans (TmEq.snd ih)
  | inl t ih => exact (tmEq_hinl _ (focusTm t)).trans (TmEq.inl ih)
  | inr t ih => exact (tmEq_hinr _ (focusTm t)).trans (TmEq.inr ih)
  | «case» s t u ihs iht ihu =>
      exact (tmEq_hcase (focusTm s) (focusTm t) (focusTm u)).trans
        (TmEq.case ihs iht ihu)
  | lam _ ih => exact TmEq.lam ih
  | app t u iht ihu =>
      exact (tmEq_happ (focusTm t) (focusTm u)).trans (TmEq.app iht ihu)

/-- Focusing preserves the categorical interpretation up to `IntrinsicDefEq`. -/
theorem interpret_focusTm {X : Object sig.nBases} {Γ : Ctx sig}
    {A : Object sig.nBases} (ρ : Env X Γ) (t : Tm Γ A) :
    IntrinsicDefEq (interpret ρ (focusTm t).erase) (interpret ρ t) :=
  (tmEq_focusTm t).intrinsicDefEq ρ

end Equality
end Gimbal
