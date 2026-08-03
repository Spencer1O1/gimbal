/-
  Chosen terminal object of `«CΣ»`.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Gimbal.SyntacticCategory

namespace Gimbal
namespace «CΣ»

open CategoryTheory CategoryTheory.Limits

variable {sig : Signature}

/-- Chosen terminal object: syntactic `Unit`. -/
abbrev unitObj : «CΣ» sig := ⟨.unit⟩

def Hom.discard (A : «CΣ» sig) : Hom A unitObj :=
  Hom.mk (Morphism.discard A.asObject)

theorem Hom.terminal_uniq {A : «CΣ» sig} (f : A ⟶ unitObj) : f = Hom.discard A := by
  refine Quotient.inductionOn f ?_
  intro f
  exact Quotient.sound (DefEq.terminal_uniq f)

def unitIsTerminal : IsTerminal (unitObj : «CΣ» sig) :=
  IsTerminal.ofUniqueHom Hom.discard fun _ => Hom.terminal_uniq

def terminalLimitCone : LimitCone (Functor.empty («CΣ» sig)) :=
  ⟨asEmptyCone unitObj, unitIsTerminal⟩

end «CΣ»
end Gimbal
