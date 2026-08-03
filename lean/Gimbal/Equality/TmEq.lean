/-
  `TmEq`: the intrinsic equational theory of the equality calculus.

  `TmEq` is *defined* semantically — two terms are equal when they have the
  same categorical interpretation in every environment — so soundness under
  interpretation holds by definition. What has to be proved is that the theory
  contains the rules the focusing transformations use: congruence, the βη laws,
  and the commuting conversions for `case` and `abort`.
-/

import Gimbal.Equality.Interpret

namespace Gimbal
namespace Equality

variable {sig : Signature}

open CategoryTheory

/-! ### Definition -/

/--
Two terms are equal when every environment interprets them the same way.

Stated in the quotient category `«CΣ»`, which is definitional equality of the
underlying morphisms (`IntrinsicDefEq`, see `TmEq.intrinsicDefEq`).
-/
structure TmEq {Γ : Ctx sig} {A : Object sig.nBases} (t u : Tm Γ A) : Prop where
  /-- Every environment gives the same morphism. -/
  qm_eq : ∀ {X : Object sig.nBases} (ρ : Env X Γ),
    qm (interpret ρ t) = qm (interpret ρ u)

namespace TmEq

@[refl] theorem refl {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) :
    TmEq t t := ⟨fun _ => rfl⟩

theorem symm {Γ : Ctx sig} {A : Object sig.nBases} {t u : Tm Γ A}
    (h : TmEq t u) : TmEq u t := ⟨fun ρ => (h.qm_eq ρ).symm⟩

theorem trans {Γ : Ctx sig} {A : Object sig.nBases} {t u v : Tm Γ A}
    (h₁ : TmEq t u) (h₂ : TmEq u v) : TmEq t v :=
  ⟨fun ρ => (h₁.qm_eq ρ).trans (h₂.qm_eq ρ)⟩

theorem of_eq {Γ : Ctx sig} {A : Object sig.nBases} {t u : Tm Γ A}
    (h : t = u) : TmEq t u := h ▸ refl t

/-- Soundness under interpretation. -/
theorem intrinsicDefEq {Γ : Ctx sig} {A : Object sig.nBases} {t u : Tm Γ A}
    (h : TmEq t u) {X : Object sig.nBases} (ρ : Env X Γ) :
    IntrinsicDefEq (interpret ρ t) (interpret ρ u) :=
  intrinsicDefEq_of_qm_eq (h.qm_eq ρ)

/-! ### Congruence -/

theorem pair {Γ : Ctx sig} {A B : Object sig.nBases} {t t' : Tm Γ A}
    {u u' : Tm Γ B} (ht : TmEq t t') (hu : TmEq u u') :
    TmEq (.pair t u) (.pair t' u') := by
  refine ⟨?_⟩; intro X ρ; simp only [interpret, qm_pair, ht.qm_eq ρ, hu.qm_eq ρ]

theorem fst {Γ : Ctx sig} {A B : Object sig.nBases} {t t' : Tm Γ (.prod A B)}
    (ht : TmEq t t') : TmEq (.fst t) (.fst t') := by
  refine ⟨?_⟩; intro X ρ; simp only [interpret, qm_compose, ht.qm_eq ρ]

theorem snd {Γ : Ctx sig} {A B : Object sig.nBases} {t t' : Tm Γ (.prod A B)}
    (ht : TmEq t t') : TmEq (.snd t) (.snd t') := by
  refine ⟨?_⟩; intro X ρ; simp only [interpret, qm_compose, ht.qm_eq ρ]

theorem inl {Γ : Ctx sig} {A B : Object sig.nBases} {t t' : Tm Γ A}
    (ht : TmEq t t') : TmEq (.inl (B := B) t) (.inl t') := by
  refine ⟨?_⟩; intro X ρ; simp only [interpret, qm_compose, ht.qm_eq ρ]

theorem inr {Γ : Ctx sig} {A B : Object sig.nBases} {t t' : Tm Γ B}
    (ht : TmEq t t') : TmEq (.inr (A := A) t) (.inr t') := by
  refine ⟨?_⟩; intro X ρ; simp only [interpret, qm_compose, ht.qm_eq ρ]

theorem abort {Γ : Ctx sig} {A : Object sig.nBases} {t t' : Tm Γ .never}
    (ht : TmEq t t') : TmEq (.abort (A := A) t) (.abort t') := by
  refine ⟨?_⟩; intro X ρ; simp only [interpret, qm_compose, ht.qm_eq ρ]

theorem lam {Γ : Ctx sig} {A B : Object sig.nBases} {t t' : Tm (Γ ▻ A) B}
    (ht : TmEq t t') : TmEq (.lam t) (.lam t') := by
  refine ⟨?_⟩; intro X ρ; simp only [interpret, qm_curry, ht.qm_eq (Env.extend ρ)]

theorem app {Γ : Ctx sig} {A B : Object sig.nBases} {t t' : Tm Γ (.exp A B)}
    {u u' : Tm Γ A} (ht : TmEq t t') (hu : TmEq u u') :
    TmEq (.app t u) (.app t' u') := by
  refine ⟨?_⟩; intro X ρ; simp only [interpret, qm_compose, qm_pair, ht.qm_eq ρ, hu.qm_eq ρ]

theorem «case» {Γ : Ctx sig} {A B C : Object sig.nBases}
    {s s' : Tm Γ (.coprod A B)} {t t' : Tm (Γ ▻ A) C} {u u' : Tm (Γ ▻ B) C}
    (hs : TmEq s s') (ht : TmEq t t') (hu : TmEq u u') :
    TmEq (.case s t u) (.case s' t' u') := by
  refine ⟨?_⟩
  intro X ρ
  simp only [interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib,
    hs.qm_eq ρ, ht.qm_eq (Env.extend ρ), hu.qm_eq (Env.extend ρ)]

end TmEq

/-! ### Interpretation of the substitution and weakening idioms -/

theorem interpret_qm_snocConst {X A₀ : Object sig.nBases} {Γ : Ctx sig}
    {B : Object sig.nBases} (ρ : Env X Γ) (c : IntrinsicMorphism sig X A₀)
    (t : Tm (Γ ▻ A₀) B) :
    qm (interpret (Env.snocConst ρ c) t) =
      cpair (𝟙 (quotientObject X)) (qm c) ≫
        qm (interpret (Env.extend ρ) t) := by
  have hpw : ∀ {D : Object sig.nBases} (x : Var (Γ ▻ A₀) D),
      qm (Env.precomp (IntrinsicMorphism.pair (.id X) c) (Env.extend ρ) x) =
        qm (Env.snocConst ρ c x) := by
    intro D x
    cases x with
    | here =>
        show qm (.compose (IntrinsicMorphism.pair (.id X) c)
          (IntrinsicMorphism.second X A₀)) = qm c
        simp
    | there y =>
        show qm (.compose (IntrinsicMorphism.pair (.id X) c)
          (.compose (IntrinsicMorphism.first X A₀) (ρ y))) = qm (ρ y)
        simp
  rw [← interpret_qm_eq_of_pointwise hpw t,
    ← interpret_qm_natural (IntrinsicMorphism.pair (.id X) c) (Env.extend ρ) t,
    qm_pair, qm_id]

theorem interpret_qm_subst0 {X A₀ : Object sig.nBases} {Γ : Ctx sig}
    {B : Object sig.nBases} (ρ : Env X Γ) (t : Tm (Γ ▻ A₀) B) (n : Tm Γ A₀) :
    qm (interpret ρ (subst0 t n)) =
      cpair (𝟙 (quotientObject X)) (qm (interpret ρ n)) ≫
        qm (interpret (Env.extend ρ) t) := by
  refine ((interpret_qm_subst ρ (Subst.single n) t).trans ?_).trans
    (interpret_qm_snocConst ρ (interpret ρ n) t)
  refine interpret_qm_eq_of_pointwise ?_ t
  intro C x
  cases x <;> rfl

theorem interpret_qm_weakenTerm {X A₀ : Object sig.nBases} {Γ : Ctx sig}
    {B : Object sig.nBases} (ρ : Env X Γ) (t : Tm Γ B) :
    qm (interpret (Env.extend (A := A₀) ρ) (weakenTerm t)) =
      cfst (quotientObject X) (quotientObject A₀) ≫ qm (interpret ρ t) := by
  simpa using qm_eq_of_intrinsicDefEq (interpret_weakenTerm (A₀ := A₀) ρ t)

/-- Interpreting under `Rename.skip1` re-indexes along `first × id`. -/
theorem interpret_qm_skip1 {X A₀ A₁ : Object sig.nBases} {Γ : Ctx sig}
    {B : Object sig.nBases} (ρ : Env X Γ) (t : Tm (Γ ▻ A₁) B) :
    qm (interpret (Env.extend (A := A₁) (Env.extend (A := A₀) ρ))
        (rename Rename.skip1 t)) =
      csProdFst (cfst (quotientObject X) (quotientObject A₀))
          (quotientObject A₁) ≫
        qm (interpret (Env.extend (A := A₁) ρ) t) := by
  have hpw : ∀ {D : Object sig.nBases} (x : Var (Γ ▻ A₁) D),
      qm (Env.rename (Env.extend (Env.extend ρ)) Rename.skip1 x) =
        qm (Env.precomp ((IntrinsicMorphism.first X A₀).prodFirst A₁)
          (Env.extend ρ) x) := by
    intro D x
    cases x with
    | here =>
        show qm (IntrinsicMorphism.second (.prod X A₀) A₁) =
          qm (.compose ((IntrinsicMorphism.first X A₀).prodFirst A₁)
            (IntrinsicMorphism.second X A₁))
        simp [IntrinsicMorphism.prodFirst]
    | there y =>
        show qm (.compose (IntrinsicMorphism.first (.prod X A₀) A₁)
            (.compose (IntrinsicMorphism.first X A₀) (ρ y))) =
          qm (.compose ((IntrinsicMorphism.first X A₀).prodFirst A₁)
            (.compose (IntrinsicMorphism.first X A₁) (ρ y)))
        simp [IntrinsicMorphism.prodFirst, ← Category.assoc]
  rw [interpret_rename, interpret_qm_eq_of_pointwise hpw t,
    ← interpret_qm_natural ((IntrinsicMorphism.first X A₀).prodFirst A₁)
      (Env.extend ρ) t, qm_prodFirst, qm_first]

/-! ### Categorical lemmas behind the equational rules -/

/-- Beta for exponentials, in `«CΣ»`. -/
theorem cs_beta_app {X A B : «CΣ» sig} (a : «CΣ».prodObj X A ⟶ B) (g : X ⟶ A) :
    cpair (ccurry a) g ≫ cev A B = cpair (𝟙 X) g ≫ a := by
  conv_rhs => rw [← cuncurry_ccurry a]
  rw [cuncurry_def, ← Category.assoc, cs_comp_pair]
  simp

/-- Pushing an injection into the second component of a diagonal pair. -/
theorem cs_pair_id_inl {X A B : «CΣ» sig} (g : X ⟶ A) :
    cpair (𝟙 X) (g ≫ cinl A B) = cpair (𝟙 X) g ≫ csProdSnd X (cinl A B) := by
  rw [csProdSnd, cs_comp_pair]
  simp

theorem cs_pair_id_inr {X A B : «CΣ» sig} (g : X ⟶ B) :
    cpair (𝟙 X) (g ≫ cinr A B) = cpair (𝟙 X) g ≫ csProdSnd X (cinr A B) := by
  rw [csProdSnd, cs_comp_pair]
  simp

/-- Reassociating an eliminated `case`: `⟨1, ⟨1, s⟩ ≫ k⟩ = ⟨1, s⟩ ≫ ⟨π₁, k⟩`. -/
theorem cs_pair_diag_comp {X Y Z : «CΣ» sig} (s : X ⟶ Y)
    (k : «CΣ».prodObj X Y ⟶ Z) :
    cpair (𝟙 X) (cpair (𝟙 X) s ≫ k) =
      cpair (𝟙 X) s ≫ cpair (cfst X Y) k := by
  rw [cs_comp_pair]
  simp

/--
The commuting conversion, in `«CΣ»`: an elimination frame `e` applied to a
`case` is the `case` whose branches are the frame applied pointwise.
-/
theorem cs_comm_conv {X A B C C' : «CΣ» sig}
    (a : «CΣ».prodObj X A ⟶ C) (b : «CΣ».prodObj X B ⟶ C)
    (e : «CΣ».prodObj X C ⟶ C') :
    cpair (cfst X («CΣ».coprodObj A B)) (csDistrib X A B ≫ ccase a b) ≫ e =
      csDistrib X A B ≫
        ccase (cpair (cfst X A) a ≫ e) (cpair (cfst X B) b ≫ e) := by
  refine cs_hom_ext_prod_coprod ?_ ?_
  · rw [csProdSnd_left_csDistrib_assoc, cinl_ccase, ← Category.assoc,
      cs_comp_pair, csProdSnd_left_csDistrib_assoc, cinl_ccase]
    simp [csProdSnd]
  · rw [csProdSnd_right_csDistrib_assoc, cinr_ccase, ← Category.assoc,
      cs_comp_pair, csProdSnd_right_csDistrib_assoc, cinr_ccase]
    simp [csProdSnd]

/-- Maps out of an object with a map to the initial object are unique. -/
theorem cs_hom_ext_of_initial {X Z : «CΣ» sig} (g : X ⟶ «CΣ».neverObj)
    (f₁ f₂ : X ⟶ Z) : f₁ = f₂ := by
  have key : ∀ h₁ h₂ : «CΣ».prodObj X «CΣ».neverObj ⟶ Z, h₁ = h₂ := by
    intro h₁ h₂
    have hc : ccurry (csSwap «CΣ».neverObj X ≫ h₁) =
        ccurry (csSwap «CΣ».neverObj X ≫ h₂) :=
      («CΣ».Hom.initial_uniq _).trans («CΣ».Hom.initial_uniq _).symm
    have hs := congrArg cuncurry hc
    rw [cuncurry_ccurry, cuncurry_ccurry] at hs
    have := congrArg (fun k => csSwap X «CΣ».neverObj ≫ k) hs
    simpa [← Category.assoc, csSwap_csSwap] using this
  have h₁ : f₁ = cpair (𝟙 X) g ≫ (cfst X «CΣ».neverObj ≫ f₁) := by simp
  have h₂ : f₂ = cpair (𝟙 X) g ≫ (cfst X «CΣ».neverObj ≫ f₂) := by simp
  rw [h₁, h₂, key (cfst X «CΣ».neverObj ≫ f₁) (cfst X «CΣ».neverObj ≫ f₂)]

/-- An application read as a post-composed frame on its function. -/
theorem cs_app_frame {X A B : «CΣ» sig} (m : X ⟶ «CΣ».expObj A B) (g : X ⟶ A) :
    cpair m g ≫ cev A B =
      cpair (𝟙 X) m ≫
        (cpair (csnd X («CΣ».expObj A B))
          (cfst X («CΣ».expObj A B) ≫ g) ≫ cev A B) := by
  rw [← Category.assoc, cs_comp_pair]
  simp

/-- Re-indexing a `case` frame along a projection. -/
theorem cs_frame_case {X Y A B Z : «CΣ» sig} (f : Y ⟶ X)
    (a : «CΣ».prodObj X A ⟶ Z) (b : «CΣ».prodObj X B ⟶ Z) :
    csProdFst f («CΣ».coprodObj A B) ≫ csDistrib X A B ≫ ccase a b =
      csDistrib Y A B ≫
        ccase (csProdFst f A ≫ a) (csProdFst f B ≫ b) := by
  rw [← Category.assoc, csDistrib_natural, Category.assoc, cs_case_comp]
  simp only [Category.assoc, cinl_ccase, cinr_ccase]

/-- `⟨π₁, a⟩ = ⟨1, a⟩ ≫ (f × 1)`. -/
theorem cs_pair_fst_eq {X Y C : «CΣ» sig} (f : Y ⟶ X) (a : Y ⟶ C) :
    cpair (f) a = cpair (𝟙 Y) a ≫ csProdFst f C := by
  rw [csProdFst, cs_comp_pair]
  simp

namespace TmEq

/-! ### βη -/

theorem beta_fst {Γ : Ctx sig} {A B : Object sig.nBases} (t : Tm Γ A)
    (u : Tm Γ B) : TmEq (.fst (.pair t u)) t := by
  refine ⟨?_⟩; intro X ρ; simp [interpret]

theorem beta_snd {Γ : Ctx sig} {A B : Object sig.nBases} (t : Tm Γ A)
    (u : Tm Γ B) : TmEq (.snd (.pair t u)) u := by
  refine ⟨?_⟩; intro X ρ; simp [interpret]

theorem eta_prod {Γ : Ctx sig} {A B : Object sig.nBases}
    (t : Tm Γ (.prod A B)) : TmEq (.pair (.fst t) (.snd t)) t := by
  refine ⟨?_⟩
  intro X ρ
  simp only [interpret, qm_pair, qm_compose, qm_first, qm_second]
  exact cpair_eta _

theorem eta_unit {Γ : Ctx sig} (t : Tm Γ .unit) : TmEq t .unit := by
  refine ⟨?_⟩
  intro X ρ
  simp only [interpret, qm_discard]
  exact cterminal_uniq _

theorem beta_app {Γ : Ctx sig} {A B : Object sig.nBases} (t : Tm (Γ ▻ A) B)
    (u : Tm Γ A) : TmEq (.app (.lam t) u) (subst0 t u) := by
  refine ⟨?_⟩
  intro X ρ
  rw [interpret_qm_subst0]
  simp only [interpret, qm_compose, qm_pair, qm_eval, qm_curry]
  exact cs_beta_app _ _

theorem eta_lam {Γ : Ctx sig} {A B : Object sig.nBases} (t : Tm Γ (.exp A B)) :
    TmEq (.lam (.app (weakenTerm t) (.var .here))) t := by
  refine ⟨?_⟩
  intro X ρ
  simp only [interpret, qm_curry, qm_compose, qm_pair, qm_eval,
    interpret_qm_weakenTerm]
  show ccurry (cpair (cfst _ _ ≫ qm (interpret ρ t))
    (qm (IntrinsicMorphism.second X A)) ≫ cev _ _) = qm (interpret ρ t)
  rw [qm_second, ← cuncurry_def, ccurry_cuncurry]

theorem beta_case_inl {Γ : Ctx sig} {A B C : Object sig.nBases} (t : Tm Γ A)
    (l : Tm (Γ ▻ A) C) (r : Tm (Γ ▻ B) C) :
    TmEq (.case (.inl t) l r) (subst0 l t) := by
  refine ⟨?_⟩
  intro X ρ
  rw [interpret_qm_subst0]
  simp only [interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib, qm_left]
  rw [cs_pair_id_inl, Category.assoc, csProdSnd_left_csDistrib_assoc, cinl_ccase]

theorem beta_case_inr {Γ : Ctx sig} {A B C : Object sig.nBases} (t : Tm Γ B)
    (l : Tm (Γ ▻ A) C) (r : Tm (Γ ▻ B) C) :
    TmEq (.case (.inr t) l r) (subst0 r t) := by
  refine ⟨?_⟩
  intro X ρ
  rw [interpret_qm_subst0]
  simp only [interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib, qm_right]
  rw [cs_pair_id_inr, Category.assoc, csProdSnd_right_csDistrib_assoc, cinr_ccase]

/-! ### Commuting conversions for `abort`

`never` is initial and `X` maps to it, so *every* pair of terms is equal there.
-/

theorem of_never {Γ : Ctx sig} {A : Object sig.nBases} (n : Tm Γ .never)
    (t u : Tm Γ A) : TmEq t u :=
  ⟨fun ρ => cs_hom_ext_of_initial (qm (interpret ρ n)) _ _⟩

/-! ### Commuting conversions for `case` -/

theorem cc_fst_case {Γ : Ctx sig} {A B C D : Object sig.nBases}
    (s : Tm Γ (.coprod A B)) (l : Tm (Γ ▻ A) (.prod C D))
    (r : Tm (Γ ▻ B) (.prod C D)) :
    TmEq (.fst (.case s l r)) (.case s (.fst l) (.fst r)) := by
  refine ⟨?_⟩
  intro X ρ
  simp only [interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib,
    Category.assoc, cs_case_comp]

theorem cc_snd_case {Γ : Ctx sig} {A B C D : Object sig.nBases}
    (s : Tm Γ (.coprod A B)) (l : Tm (Γ ▻ A) (.prod C D))
    (r : Tm (Γ ▻ B) (.prod C D)) :
    TmEq (.snd (.case s l r)) (.case s (.snd l) (.snd r)) := by
  refine ⟨?_⟩
  intro X ρ
  simp only [interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib,
    Category.assoc, cs_case_comp]

theorem cc_inl_case {Γ : Ctx sig} {A B C D : Object sig.nBases}
    (s : Tm Γ (.coprod A B)) (l : Tm (Γ ▻ A) C) (r : Tm (Γ ▻ B) C) :
    TmEq (.inl (B := D) (.case s l r)) (.case s (.inl l) (.inl r)) := by
  refine ⟨?_⟩
  intro X ρ
  simp only [interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib,
    Category.assoc, cs_case_comp]

theorem cc_inr_case {Γ : Ctx sig} {A B C D : Object sig.nBases}
    (s : Tm Γ (.coprod A B)) (l : Tm (Γ ▻ A) C) (r : Tm (Γ ▻ B) C) :
    TmEq (.inr (A := D) (.case s l r)) (.case s (.inr l) (.inr r)) := by
  refine ⟨?_⟩
  intro X ρ
  simp only [interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib,
    Category.assoc, cs_case_comp]

theorem cc_app_case {Γ : Ctx sig} {A B C D : Object sig.nBases}
    (s : Tm Γ (.coprod A B)) (l : Tm (Γ ▻ A) (.exp C D))
    (r : Tm (Γ ▻ B) (.exp C D)) (u : Tm Γ C) :
    TmEq (.app (.case s l r) u)
      (.case s (.app l (weakenTerm u)) (.app r (weakenTerm u))) := by
  refine ⟨?_⟩
  intro X ρ
  simp only [interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib,
    qm_eval, interpret_qm_weakenTerm]
  rw [cs_app_frame, cs_pair_diag_comp, Category.assoc, cs_comm_conv]
  refine congrArg (fun k => cpair (𝟙 _) (qm (interpret ρ s)) ≫ k) ?_
  refine congrArg (fun k => csDistrib _ _ _ ≫ k) ?_
  refine congrArg₂ ccase ?_ ?_ <;>
    (rw [← Category.assoc, cs_comp_pair]; simp)

theorem cc_case_case {Γ : Ctx sig} {A B C D Z : Object sig.nBases}
    (s : Tm Γ (.coprod A B)) (l : Tm (Γ ▻ A) (.coprod C D))
    (r : Tm (Γ ▻ B) (.coprod C D))
    (m₁ : Tm (Γ ▻ C) Z) (m₂ : Tm (Γ ▻ D) Z) :
    TmEq (.case (.case s l r) m₁ m₂)
      (.case s
        (.case l (rename Rename.skip1 m₁) (rename Rename.skip1 m₂))
        (.case r (rename Rename.skip1 m₁) (rename Rename.skip1 m₂))) := by
  refine ⟨?_⟩
  intro X ρ
  simp only [interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib,
    interpret_qm_skip1]
  rw [cs_pair_diag_comp, Category.assoc, cs_comm_conv]
  refine congrArg (fun k => cpair (𝟙 _) (qm (interpret ρ s)) ≫ k) ?_
  refine congrArg (fun k => csDistrib _ _ _ ≫ k) ?_
  refine congrArg₂ ccase ?_ ?_ <;>
    rw [cs_pair_fst_eq, Category.assoc, cs_frame_case]

end TmEq

/-! ### Sum η -/

namespace Subst

/-- Commit the newest binder to the left injection. -/
def injLeft {Γ : Ctx sig} {A B : Object sig.nBases} :
    Subst sig (Γ ▻ .coprod A B) (Γ ▻ A)
  | _, .here => .inl (.var .here)
  | _, .there y => .var (.there y)

/-- Commit the newest binder to the right injection. -/
def injRight {Γ : Ctx sig} {A B : Object sig.nBases} :
    Subst sig (Γ ▻ .coprod A B) (Γ ▻ B)
  | _, .here => .inr (.var .here)
  | _, .there y => .var (.there y)

end Subst

/-- `⟨π₁, π₂ ≫ inl⟩ : X × A ⟶ X × (A + B)`. -/
def IntrinsicMorphism.prodInl (X A B : Object sig.nBases) :
    IntrinsicMorphism sig (.prod X A) (.prod X (.coprod A B)) :=
  .pair (.first X A) (.compose (.second X A) (.left A B))

/-- `⟨π₁, π₂ ≫ inr⟩ : X × B ⟶ X × (A + B)`. -/
def IntrinsicMorphism.prodInr (X A B : Object sig.nBases) :
    IntrinsicMorphism sig (.prod X B) (.prod X (.coprod A B)) :=
  .pair (.first X B) (.compose (.second X B) (.right A B))

@[simp] theorem qm_prodInl (X A B : Object sig.nBases) :
    qm (IntrinsicMorphism.prodInl (sig := sig) X A B) =
      csProdSnd (quotientObject X)
        (cinl (quotientObject A) (quotientObject B)) := rfl

@[simp] theorem qm_prodInr (X A B : Object sig.nBases) :
    qm (IntrinsicMorphism.prodInr (sig := sig) X A B) =
      csProdSnd (quotientObject X)
        (cinr (quotientObject A) (quotientObject B)) := rfl

theorem interpret_qm_injLeft {X : Object sig.nBases} {Γ : Ctx sig}
    {A B Z : Object sig.nBases} (ρ : Env X Γ) (w : Tm (Γ ▻ .coprod A B) Z) :
    qm (interpret (Env.extend (A := A) ρ) (subst Subst.injLeft w)) =
      csProdSnd (quotientObject X) (cinl (quotientObject A) (quotientObject B)) ≫
        qm (interpret (Env.extend (A := .coprod A B) ρ) w) := by
  rw [interpret_qm_subst, ← qm_prodInl,
    interpret_qm_natural (IntrinsicMorphism.prodInl X A B) (Env.extend ρ) w]
  refine interpret_qm_eq_of_pointwise ?_ w
  intro C x
  cases x with
  | here =>
      show qm (IntrinsicMorphism.compose (IntrinsicMorphism.second X A)
        (IntrinsicMorphism.left A B)) =
          qm (.compose (IntrinsicMorphism.prodInl X A B)
            (IntrinsicMorphism.second X (.coprod A B)))
      simp [IntrinsicMorphism.prodInl]
  | there y =>
      show qm (IntrinsicMorphism.compose (IntrinsicMorphism.first X A) (ρ y)) =
          qm (.compose (IntrinsicMorphism.prodInl X A B)
            (.compose (IntrinsicMorphism.first X (.coprod A B)) (ρ y)))
      simp [IntrinsicMorphism.prodInl, ← Category.assoc]

theorem interpret_qm_injRight {X : Object sig.nBases} {Γ : Ctx sig}
    {A B Z : Object sig.nBases} (ρ : Env X Γ) (w : Tm (Γ ▻ .coprod A B) Z) :
    qm (interpret (Env.extend (A := B) ρ) (subst Subst.injRight w)) =
      csProdSnd (quotientObject X) (cinr (quotientObject A) (quotientObject B)) ≫
        qm (interpret (Env.extend (A := .coprod A B) ρ) w) := by
  rw [interpret_qm_subst, ← qm_prodInr,
    interpret_qm_natural (IntrinsicMorphism.prodInr X A B) (Env.extend ρ) w]
  refine interpret_qm_eq_of_pointwise ?_ w
  intro C x
  cases x with
  | here =>
      show qm (IntrinsicMorphism.compose (IntrinsicMorphism.second X B)
        (IntrinsicMorphism.right A B)) =
          qm (.compose (IntrinsicMorphism.prodInr X A B)
            (IntrinsicMorphism.second X (.coprod A B)))
      simp [IntrinsicMorphism.prodInr]
  | there y =>
      show qm (IntrinsicMorphism.compose (IntrinsicMorphism.first X B) (ρ y)) =
          qm (.compose (IntrinsicMorphism.prodInr X A B)
            (.compose (IntrinsicMorphism.first X (.coprod A B)) (ρ y)))
      simp [IntrinsicMorphism.prodInr, ← Category.assoc]

namespace TmEq

/--
Strong sum η: a `case` whose branches are the two injection instances of a
common body is that body applied to the scrutinee. This is the law that makes
a saturation split on a coproduct observation meaning-preserving even when the
branches genuinely use the observation.
-/
theorem sum_eta {Γ : Ctx sig} {A B Z : Object sig.nBases}
    (s : Tm Γ (.coprod A B)) (w : Tm (Γ ▻ .coprod A B) Z) :
    TmEq (.case s (subst Subst.injLeft w) (subst Subst.injRight w))
      (subst0 w s) := by
  refine ⟨?_⟩
  intro X ρ
  rw [interpret_qm_subst0]
  simp only [interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib]
  rw [interpret_qm_injLeft, interpret_qm_injRight]
  refine congrArg (fun k => cpair (𝟙 _) (qm (interpret ρ s)) ≫ k) ?_
  refine cs_hom_ext_prod_coprod ?_ ?_
  · rw [← Category.assoc, csProdSnd_left_csDistrib, cinl_ccase]
  · rw [← Category.assoc, csProdSnd_right_csDistrib, cinr_ccase]

/--
A `case` whose two branches ignore the bound variable is that branch.
This is the semantic content of a saturation split that has not yet used the
observation: the context grows, the meaning does not.
-/
theorem case_weaken_self {Γ : Ctx sig} {A B C : Object sig.nBases}
    (s : Tm Γ (.coprod A B)) (t : Tm Γ C) :
    TmEq (.case s (weakenTerm t) (weakenTerm t)) t := by
  refine ⟨?_⟩
  intro X ρ
  simp only [interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib,
    interpret_qm_weakenTerm]
  have key :
      csDistrib (quotientObject X) (quotientObject A) (quotientObject B) ≫
          ccase (cfst (quotientObject X) (quotientObject A) ≫ qm (interpret ρ t))
            (cfst (quotientObject X) (quotientObject B) ≫ qm (interpret ρ t)) =
        cfst (quotientObject X)
            («CΣ».coprodObj (quotientObject A) (quotientObject B)) ≫
          qm (interpret ρ t) := by
    refine cs_hom_ext_prod_coprod ?_ ?_
    · rw [← Category.assoc, csProdSnd_left_csDistrib, cinl_ccase]
      simp [csProdSnd]
    · rw [← Category.assoc, csProdSnd_right_csDistrib, cinr_ccase]
      simp [csProdSnd]
  rw [key]
  simp

/-! ### Congruence for substitution -/

theorem subst0_congr {Γ : Ctx sig} {A C : Object sig.nBases}
    {t t' : Tm (Γ ▻ A) C} {v v' : Tm Γ A} (ht : TmEq t t') (hv : TmEq v v') :
    TmEq (subst0 t v) (subst0 t' v') := by
  refine ⟨?_⟩
  intro X ρ
  rw [interpret_qm_subst0, interpret_qm_subst0, hv.qm_eq ρ, ht.qm_eq (Env.extend ρ)]

end TmEq

end Equality
end Gimbal
