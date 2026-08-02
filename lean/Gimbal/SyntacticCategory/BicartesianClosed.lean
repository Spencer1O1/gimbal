/-
  Bicartesian-closed packaging for `«CΣ»`:
  cartesian monoidal + finite coproducts + monoidal closed.
-/

import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Gimbal.SyntacticCategory.Cartesian
import Gimbal.SyntacticCategory.Initial
import Gimbal.SyntacticCategory.Coproduct
import Gimbal.SyntacticCategory.Exponential

namespace Gimbal

open CategoryTheory CategoryTheory.Limits MonoidalCategory

/-! ### Coproduct instance cluster -/

instance (sig : Signature) : HasInitial («CΣ» sig) :=
  («CΣ».neverIsInitial (sig := sig)).hasInitial

instance {sig : Signature} {A B : «CΣ» sig} : HasColimit (pair A B) :=
  HasColimit.mk («CΣ».coproductColimitCone A B)

instance (sig : Signature) : HasBinaryCoproducts («CΣ» sig) :=
  hasBinaryCoproducts_of_hasColimit_pair («CΣ» sig)

instance (sig : Signature) : HasFiniteCoproducts («CΣ» sig) :=
  hasFiniteCoproducts_of_has_binary_and_initial

/-! ### Monoidal closed via tensorRight, then braiding transport -/

namespace «CΣ»

variable {sig : Signature}

/-- Named cartesian braiding so bridge lemmas share the instance with `closedObject`. -/
@[implicit_reducible]
noncomputable def cartesianBraided (sig : Signature) : BraidedCategory («CΣ» sig) :=
  .ofCartesianMonoidalCategory

/-- Hom-equivalence for the right adjoint of `tensorRight A`. -/
def tensorRightHomEquiv (A : «CΣ» sig) (X B : «CΣ» sig) :
    ((tensorRight A).obj X ⟶ B) ≃ (X ⟶ expObj A B) :=
  Hom.curryEquiv X A B

theorem tensorRightHomEquiv_natural (A : «CΣ» sig)
    (X' X Y : «CΣ» sig) (f : X' ⟶ X) (g : (tensorRight A).obj X ⟶ Y) :
    tensorRightHomEquiv A X' Y ((tensorRight A).map f ≫ g) =
      f ≫ tensorRightHomEquiv A X Y g := by
  have hmap : (tensorRight A).map f = Hom.prodMap f (Hom.id A) := rfl
  rw [hmap]
  exact Hom.curry_natural_left (X := X') (X' := X) (A := A) (B := Y) f g

/-- Right adjoint of `tensorRight A`, built from `Hom.curryEquiv`. -/
noncomputable def expFunctor (A : «CΣ» sig) : «CΣ» sig ⥤ «CΣ» sig :=
  Adjunction.rightAdjointOfEquiv (tensorRightHomEquiv A) (tensorRightHomEquiv_natural A)

noncomputable def tensorRightAdj (A : «CΣ» sig) :
    tensorRight A ⊣ expFunctor A :=
  Adjunction.adjunctionOfEquivRight (tensorRightHomEquiv A) (tensorRightHomEquiv_natural A)

/-- `Adjunction.homEquiv` rebuilds from unit/counit; recover the chosen curry. -/
theorem tensorRightAdj_homEquiv_eq_curry {A Y B : «CΣ» sig}
    (g : (tensorRight A).obj Y ⟶ B) :
    (tensorRightAdj A).homEquiv Y B g = Hom.curry g := by
  dsimp only [tensorRightAdj, Adjunction.adjunctionOfEquivRight]
  erw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

theorem tensorRightAdj_homEquiv_symm_eq_uncurry {A Y B : «CΣ» sig}
    (h : Y ⟶ (expFunctor A).obj B) :
    ((tensorRightAdj A).homEquiv Y B).symm h = Hom.uncurry (h : Y ⟶ expObj A B) := by
  dsimp only [tensorRightAdj, Adjunction.adjunctionOfEquivRight]
  erw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- Transport the `tensorRight` adjunction across cartesian braiding to `tensorLeft`. -/
@[implicit_reducible]
noncomputable def closedObject (A : «CΣ» sig) : Closed A where
  rightAdj := expFunctor A
  adj := by
    letI := cartesianBraided sig
    exact (tensorRightAdj A).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight A).symm

end «CΣ»

noncomputable instance (sig : Signature) : MonoidalClosed («CΣ» sig) where
  closed := «CΣ».closedObject

namespace «CΣ»

variable {sig : Signature}

theorem expObj_asObject (A B : «CΣ» sig) :
    (expObj A B).asObject = .exp A.asObject B.asObject :=
  rfl

/-- The right adjoint object's value on objects is the chosen exponential. -/
theorem expFunctor_obj (A B : «CΣ» sig) :
    (expFunctor A).obj B = expObj A B :=
  rfl

/-- Mathlib `ihom` selects Gimbal's chosen exponential object. -/
theorem ihom_obj_eq_expObj (A B : «CΣ» sig) :
    (A ⟶[«CΣ» sig] B) = expObj A B :=
  expFunctor_obj A B

/-! ### Bridge lemmas: Mathlib left-tensor curry vs Gimbal X x A curry -/

section Bridge
variable {A Y B : «CΣ» sig}

attribute [local instance] cartesianBraided

/-- The closed adjunction is the transported `tensorRight` adjunction. -/
theorem closed_adjunction_eq :
    ihom.adjunction A =
      (tensorRightAdj A).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight A).symm := by
  rfl

/--
Mathlib currying (A tensor Y) equals Gimbal currying after braiding to Y tensor A.
-/
theorem monoidalClosed_curry_eq_hom_curry (f : A ⊗ Y ⟶ B) :
    MonoidalClosed.curry f = Hom.curry ((β_ A Y).inv ≫ f) := by
  let f' : (tensorLeft A).obj Y ⟶ B := f
  have step1 : MonoidalClosed.curry f = (ihom.adjunction A).homEquiv Y B f' := rfl
  have step2 :=
    congrArg (fun adj : _ ⊣ _ => adj.homEquiv Y B f') closed_adjunction_eq
  have step3 :=
    Adjunction.homEquiv_ofNatIsoLeft_apply (tensorRightAdj A)
      (BraidedCategory.tensorLeftIsoTensorRight A).symm (f := f')
  have step4 :=
    tensorRightAdj_homEquiv_eq_curry (g :=
      (BraidedCategory.tensorLeftIsoTensorRight A).symm.hom.app Y ≫ f')
  -- Identify braiding component with `β_.inv`.
  have step5 :
      (BraidedCategory.tensorLeftIsoTensorRight A).symm.hom.app Y ≫ f' =
        (β_ A Y).inv ≫ f := rfl
  exact step1.trans <| step2.trans <| step3.trans <| step4.trans (by rw [step5])

/--
Gimbal currying (Y x A) equals Mathlib currying after braiding to A tensor Y.
-/
theorem hom_curry_eq_monoidalClosed_curry (g : Hom (prodObj Y A) B) :
    Hom.curry g = MonoidalClosed.curry ((β_ A Y).hom ≫ g) := by
  rw [monoidalClosed_curry_eq_hom_curry, Iso.inv_hom_id_assoc]

/--
Mathlib uncurrying equals braiding followed by Gimbal uncurrying.
`h` lands in Mathlib's `ihom`; that object is definitionally `expObj`.
-/
theorem monoidalClosed_uncurry_eq_hom_uncurry (h : Y ⟶ A ⟶[«CΣ» sig] B) :
    MonoidalClosed.uncurry h =
      (β_ A Y).hom ≫ Hom.uncurry (h : Y ⟶ expObj A B) := by
  let h' : Y ⟶ (ihom A).obj B := h
  have step1 : MonoidalClosed.uncurry h = ((ihom.adjunction A).homEquiv Y B).symm h' :=
    rfl
  have step2 :=
    congrArg (fun adj : _ ⊣ _ => (adj.homEquiv Y B).symm h') closed_adjunction_eq
  have step3 :=
    Adjunction.homEquiv_ofNatIsoLeft_symm_apply (tensorRightAdj A)
      (BraidedCategory.tensorLeftIsoTensorRight A).symm (f := h')
  have u :=
    tensorRightAdj_homEquiv_symm_eq_uncurry
      (h := (h' : Y ⟶ (expFunctor A).obj B))
  have step4 :
      (BraidedCategory.tensorLeftIsoTensorRight A).symm.inv.app Y ≫
          ((tensorRightAdj A).homEquiv Y B).symm h' =
        (β_ A Y).hom ≫ Hom.uncurry (h : Y ⟶ expObj A B) := by
    change (β_ A Y).hom ≫ ((tensorRightAdj A).homEquiv Y B).symm h' = _
    rw [u]
  exact step1.trans <| step2.trans <| step3.trans step4

/-- `uncurry id = eval` for Gimbal's chosen exponential. -/
theorem hom_uncurry_id_eq_eval :
    Hom.uncurry (Hom.id (expObj A B)) = Hom.eval A B := by
  apply Quotient.sound
  let fst := Morphism.first (expObj A B).asObject A.asObject
  let snd := Morphism.second (expObj A B).asObject A.asObject
  let ev := Morphism.eval A.asObject B.asObject
  let idP := Morphism.id (.prod (expObj A B).asObject A.asObject)
  refine DefEq.trans
    (DefEq.cong_compose (DefEq.cong_pair (DefEq.id_right fst) (DefEq.refl snd))
      (DefEq.refl ev)) ?_
  refine DefEq.trans
    (DefEq.cong_compose
      (DefEq.symm (DefEq.cong_pair (DefEq.id_left fst) (DefEq.id_left snd)))
      (DefEq.refl ev)) ?_
  refine DefEq.trans (DefEq.cong_compose (DefEq.prod_eta idP) (DefEq.refl ev)) ?_
  exact DefEq.id_left ev

/--
Gimbal evaluation is Mathlib evaluation after braiding
`(A ⇒ B) ⊗ A` to `A ⊗ (A ⇒ B)`.
-/
theorem hom_eval_eq_ihom_ev :
    Hom.eval A B =
      (β_ A (A ⟶[«CΣ» sig] B)).inv ≫ (ihom.ev A).app B := by
  have key :=
    monoidalClosed_uncurry_eq_hom_uncurry (A := A) (Y := A ⟶[«CΣ» sig] B) (B := B)
      (𝟙 _)
  -- key: uncurry id = β.hom ≫ Hom.uncurry id = β.hom ≫ eval
  rw [MonoidalClosed.uncurry_id_eq_ev] at key
  have uncurry_id :
      Hom.uncurry (𝟙 (A ⟶[«CΣ» sig] B) : (A ⟶[«CΣ» sig] B) ⟶ expObj A B) =
        Hom.eval A B :=
    hom_uncurry_id_eq_eval
  rw [uncurry_id] at key
  exact ((Iso.inv_comp_eq _).mpr key).symm

end Bridge

end «CΣ»

/-! ### Acceptance synth checks (compile-time) -/

noncomputable section Acceptance
variable (sig : Signature)

example : CartesianMonoidalCategory («CΣ» sig) := inferInstance
example : HasFiniteProducts («CΣ» sig) := inferInstance
example : HasInitial («CΣ» sig) := inferInstance
example : HasBinaryCoproducts («CΣ» sig) := inferInstance
example : HasFiniteCoproducts («CΣ» sig) := inferInstance
example : MonoidalClosed («CΣ» sig) := inferInstance

end Acceptance

end Gimbal
