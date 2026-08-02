/-
  Chosen binary coproducts of `«CΣ»`.
-/

import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Gimbal.SyntacticCategory

namespace Gimbal
namespace «CΣ»

open CategoryTheory CategoryTheory.Limits

variable {sig : Signature}

/-- Chosen coproduct object. -/
def coprodObj (A B : «CΣ» sig) : «CΣ» sig :=
  ⟨.coprod A.asObject B.asObject⟩

def Hom.left (A B : «CΣ» sig) : Hom A (coprodObj A B) :=
  Hom.mk (Morphism.left A.asObject B.asObject)

def Hom.right (A B : «CΣ» sig) : Hom B (coprodObj A B) :=
  Hom.mk (Morphism.right A.asObject B.asObject)

def Hom.case {A B X : «CΣ» sig} (f : Hom A X) (g : Hom B X) : Hom (coprodObj A B) X :=
  Quotient.liftOn₂ f g (fun f g => Hom.mk (f.case g))
    (by
      intro f₁ g₁ f₂ g₂ hf hg
      exact Quotient.sound (DefEq.cong_case hf hg))

@[simp]
theorem Hom.case_mk {A B X : «CΣ» sig}
    (f : Morphism sig A.asObject X.asObject)
    (g : Morphism sig B.asObject X.asObject) :
    Hom.case (Hom.mk f) (Hom.mk g) = Hom.mk (f.case g) :=
  rfl

@[simp]
theorem Hom.left_case {A B X : «CΣ» sig} (f : A ⟶ X) (g : B ⟶ X) :
    Hom.left A B ≫ Hom.case f g = f := by
  refine Quotient.inductionOn₂ f g ?_
  intro f g
  exact Quotient.sound (DefEq.coprod_beta_left f g)

@[simp]
theorem Hom.right_case {A B X : «CΣ» sig} (f : A ⟶ X) (g : B ⟶ X) :
    Hom.right A B ≫ Hom.case f g = g := by
  refine Quotient.inductionOn₂ f g ?_
  intro f g
  exact Quotient.sound (DefEq.coprod_beta_right f g)

@[simp]
theorem Hom.coprod_eta {A B X : «CΣ» sig} (h : coprodObj A B ⟶ X) :
    Hom.case (Hom.left A B ≫ h) (Hom.right A B ≫ h) = h := by
  refine Quotient.inductionOn h ?_
  intro h
  exact Quotient.sound (DefEq.coprod_eta h)

theorem Hom.case_unique {A B X : «CΣ» sig} {f : A ⟶ X} {g : B ⟶ X}
    (h : coprodObj A B ⟶ X) (hf : Hom.left A B ≫ h = f) (hg : Hom.right A B ≫ h = g) :
    h = Hom.case f g := by
  rw [← hf, ← hg, Hom.coprod_eta]

/-- Universal property of the chosen coproduct as an equivalence. -/
def coproductDescEquiv (A B X : «CΣ» sig) :
    (A ⟶ X) × (B ⟶ X) ≃ (coprodObj A B ⟶ X) where
  toFun p := Hom.case p.1 p.2
  invFun h := (Hom.left A B ≫ h, Hom.right A B ≫ h)
  left_inv := by
    intro p
    ext <;> simp
  right_inv := by
    intro h
    simp

def coproductCofan (A B : «CΣ» sig) : BinaryCofan A B :=
  BinaryCofan.mk (Hom.left A B) (Hom.right A B)

def coproductIsColimit (A B : «CΣ» sig) : IsColimit (coproductCofan A B) :=
  BinaryCofan.IsColimit.mk _
    (fun f g => Hom.case f g)
    (fun f g => Hom.left_case f g)
    (fun f g => Hom.right_case f g)
    (fun _ _ m hf hg => Hom.case_unique m hf hg)

def coproductColimitCone (A B : «CΣ» sig) : ColimitCocone (pair A B) where
  cocone := coproductCofan A B
  isColimit := coproductIsColimit A B

end «CΣ»
end Gimbal
