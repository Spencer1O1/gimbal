/-
  Chosen initial object of `«CΣ»`.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Gimbal.SyntacticCategory

namespace Gimbal
namespace «CΣ»

open CategoryTheory CategoryTheory.Limits

variable {sig : Signature}

/-- Chosen initial object: syntactic `Never`. -/
def neverObj : «CΣ» sig := ⟨.never⟩

def Hom.absurd (A : «CΣ» sig) : Hom neverObj A :=
  Hom.mk (Morphism.absurd A.asObject)

theorem Hom.initial_uniq {A : «CΣ» sig} (f : neverObj ⟶ A) : f = Hom.absurd A := by
  refine Quotient.inductionOn f ?_
  intro f
  exact Quotient.sound (DefEq.initial_uniq f)

def neverIsInitial : IsInitial (neverObj : «CΣ» sig) :=
  IsInitial.ofUniqueHom Hom.absurd fun _ => Hom.initial_uniq

def initialColimitCone : ColimitCocone (Functor.empty («CΣ» sig)) :=
  ⟨asEmptyCocone neverObj, neverIsInitial⟩

end «CΣ»
end Gimbal
