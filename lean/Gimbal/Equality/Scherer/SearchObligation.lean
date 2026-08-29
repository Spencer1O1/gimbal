/-
  Finite resolved search obligations.

  Kept below search bounds and keys so normalized-query definitions can use
  the exact `(result, support)` carrier without importing the old forest stack.
-/

import Mathlib.Data.Fintype.Prod
import Gimbal.Equality.Scherer.ResolvedSupport

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-- Exact resolved search obligation: result type paired with dependency support. -/
structure Obligation (U : SearchUniverse sig) (O : Type) where
  result : UPos U
  support : DepSupport O
  deriving DecidableEq

namespace Obligation

variable {U : SearchUniverse sig} {O : Type}

theorem ext {o₁ o₂ : Obligation U O}
    (hP : o₁.result = o₂.result) (hK : o₁.support = o₂.support) : o₁ = o₂ := by
  cases o₁; cases o₂; cases hP; cases hK; rfl

/-- Canonical equivalence with the product of finite carriers. -/
def equivProd : Obligation U O ≃ UPos U × DepSupport O where
  toFun o := (o.result, o.support)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [DecidableEq O] [Fintype O] : Fintype (Obligation U O) :=
  Fintype.ofEquiv _ equivProd.symm

instance [Fintype O] : Finite (Obligation U O) := by
  letI := Fintype.ofFinite O
  letI : DecidableEq O := Classical.decEq O
  infer_instance

end Obligation

end Gimbal.Equality.Scherer
