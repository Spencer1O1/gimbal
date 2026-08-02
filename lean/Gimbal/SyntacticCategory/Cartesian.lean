/-
  Cartesian monoidal structure on `«CΣ»` from chosen terminal and products.
-/

import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Gimbal.SyntacticCategory.Terminal
import Gimbal.SyntacticCategory.Product

namespace Gimbal

open CategoryTheory CategoryTheory.Limits MonoidalCategory

/-- Chosen finite products: `𝟙_` is `.unit` and `A ⊗ B` is `.prod`. -/
instance (sig : Signature) : CartesianMonoidalCategory («CΣ» sig) :=
  .ofChosenFiniteProducts
    («CΣ».terminalLimitCone (sig := sig))
    (fun A B => «CΣ».productLimitCone A B)

namespace «CΣ»

variable {sig : Signature}

/-- Mathlib tensor unit is Gimbal's chosen terminal object. -/
theorem tensorUnit_eq_unitObj :
    (𝟙_ («CΣ» sig)) = unitObj :=
  rfl

/-- Mathlib tensor product is Gimbal's chosen product object. -/
theorem tensorObj_eq_prodObj (A B : «CΣ» sig) :
    (A ⊗ B) = prodObj A B :=
  rfl

/-- Mathlib first projection is Gimbal's `Hom.first`. -/
theorem fst_eq_first (A B : «CΣ» sig) :
    CartesianMonoidalCategory.fst A B = Hom.first A B :=
  rfl

/-- Mathlib second projection is Gimbal's `Hom.second`. -/
theorem snd_eq_second (A B : «CΣ» sig) :
    CartesianMonoidalCategory.snd A B = Hom.second A B :=
  rfl

end «CΣ»
end Gimbal
