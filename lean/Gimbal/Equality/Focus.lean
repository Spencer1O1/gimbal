/-
  Deterministic focusing: convert ordinary intrinsically typed terms into
  phase-indexed focused syntax.

  Focusing is total. Redexes exposed by a substitution are contracted by the
  hereditary operations of `Gimbal.Equality.Hereditary`, which terminate on an
  explicit lexicographic measure, so there is no fuel counter and no
  exhaustion outcome on the proof-critical path.
-/

import Gimbal.Equality.Hereditary

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- Focus a term. Total: every intrinsic term has a focused form. -/
def focus {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) : InvTm Γ A :=
  focusTm t

/-- Focusing always succeeds; kept as an `Option` for fixture ergonomics. -/
def focus! {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) : Option (InvTm Γ A) :=
  some (focus t)

@[simp] theorem focus!_eq_some {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) :
    focus! t = some (focusTm t) := rfl

@[simp] theorem focus!_isSome {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) :
    (focus! t).isSome = true := rfl

/-- Completeness: focusing produces a focused representative of every term. -/
theorem focus_wellInv {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) :
    WellInv (focus t) :=
  wellInv_focusTm t

/-- The executable phase check agrees with the proof above. -/
@[simp] theorem focus_wellFocused {Γ : Ctx sig} {A : Object sig.nBases}
    (t : Tm Γ A) : (focus t).wellFocused = true :=
  InvTm.wellFocused_of_wellInv (focus_wellInv t)

end Equality
end Gimbal
