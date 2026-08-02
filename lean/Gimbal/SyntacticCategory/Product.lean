/-
  Chosen binary products of `«CΣ»`.
-/

import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Gimbal.SyntacticCategory

namespace Gimbal
namespace «CΣ»

open CategoryTheory CategoryTheory.Limits

variable {sig : Signature}

/-- Chosen product object. -/
def prodObj (A B : «CΣ» sig) : «CΣ» sig :=
  ⟨.prod A.asObject B.asObject⟩

def Hom.first (A B : «CΣ» sig) : Hom (prodObj A B) A :=
  Hom.mk (Morphism.first A.asObject B.asObject)

def Hom.second (A B : «CΣ» sig) : Hom (prodObj A B) B :=
  Hom.mk (Morphism.second A.asObject B.asObject)

def Hom.pair {X A B : «CΣ» sig} (f : Hom X A) (g : Hom X B) : Hom X (prodObj A B) :=
  Quotient.liftOn₂ f g (fun f g => Hom.mk (f.pair g))
    (by
      intro f₁ g₁ f₂ g₂ hf hg
      exact Quotient.sound (DefEq.cong_pair hf hg))

@[simp]
theorem Hom.pair_mk {X A B : «CΣ» sig}
    (f : Morphism sig X.asObject A.asObject)
    (g : Morphism sig X.asObject B.asObject) :
    Hom.pair (Hom.mk f) (Hom.mk g) = Hom.mk (f.pair g) :=
  rfl

@[simp]
theorem Hom.pair_first {X A B : «CΣ» sig} (f : X ⟶ A) (g : X ⟶ B) :
    Hom.pair f g ≫ Hom.first A B = f := by
  refine Quotient.inductionOn₂ f g ?_
  intro f g
  exact Quotient.sound (DefEq.prod_beta_first f g)

@[simp]
theorem Hom.pair_second {X A B : «CΣ» sig} (f : X ⟶ A) (g : X ⟶ B) :
    Hom.pair f g ≫ Hom.second A B = g := by
  refine Quotient.inductionOn₂ f g ?_
  intro f g
  exact Quotient.sound (DefEq.prod_beta_second f g)

@[simp]
theorem Hom.prod_eta {X A B : «CΣ» sig} (h : X ⟶ prodObj A B) :
    Hom.pair (h ≫ Hom.first A B) (h ≫ Hom.second A B) = h := by
  refine Quotient.inductionOn h ?_
  intro h
  exact Quotient.sound (DefEq.prod_eta h)

theorem Hom.pair_unique {X A B : «CΣ» sig} {f : X ⟶ A} {g : X ⟶ B}
    (h : X ⟶ prodObj A B) (hf : h ≫ Hom.first A B = f) (hg : h ≫ Hom.second A B = g) :
    h = Hom.pair f g := by
  rw [← hf, ← hg, Hom.prod_eta]

/-- Universal property of the chosen product as an equivalence. -/
def productLiftEquiv (X A B : «CΣ» sig) :
    (X ⟶ A) × (X ⟶ B) ≃ (X ⟶ prodObj A B) where
  toFun p := Hom.pair p.1 p.2
  invFun h := (h ≫ Hom.first A B, h ≫ Hom.second A B)
  left_inv := by
    intro p
    ext <;> simp
  right_inv := by
    intro h
    simp

def productFan (A B : «CΣ» sig) : BinaryFan A B :=
  BinaryFan.mk (Hom.first A B) (Hom.second A B)

def productIsLimit (A B : «CΣ» sig) : IsLimit (productFan A B) :=
  BinaryFan.IsLimit.mk _
    (fun f g => Hom.pair f g)
    (fun f g => Hom.pair_first f g)
    (fun f g => Hom.pair_second f g)
    (fun _ _ m hf hg => Hom.pair_unique m hf hg)

def productLimitCone (A B : «CΣ» sig) : LimitCone (pair A B) where
  cone := productFan A B
  isLimit := productIsLimit A B

end «CΣ»
end Gimbal
