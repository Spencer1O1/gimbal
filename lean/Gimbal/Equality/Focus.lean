/-
  Deterministic focusing: convert ordinary intrinsically typed terms into
  phase-indexed focused syntax.

  Focusing is total. Redexes exposed by a substitution are contracted by the
  hereditary operations of `Gimbal.Equality.Hereditary`, which terminate on an
  explicit lexicographic measure, so there is no fuel counter and no
  exhaustion outcome on the proof-critical path.
-/

import Gimbal.Equality.Preserve

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

/-- Soundness: the focused representative is equal to the term it came from. -/
theorem focus_tmEq {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) :
    TmEq (focus t).erase t :=
  tmEq_focusTm t

/-- Focusing preserves the categorical interpretation up to `IntrinsicDefEq`. -/
theorem interpret_focus {X : Object sig.nBases} {Γ : Ctx sig}
    {A : Object sig.nBases} (ρ : Env X Γ) (t : Tm Γ A) :
    IntrinsicDefEq (interpret ρ (focus t).erase) (interpret ρ t) :=
  interpret_focusTm ρ t

/--
Focusing a translated morphism yields a legal focused representative whose
interpretation is the morphism itself.
-/
theorem focus_translate {A B : Object sig.nBases}
    (f : IntrinsicMorphism sig A B) :
    WellInv (focus (translate f)) ∧
      IntrinsicDefEq
        (interpret (rootEnv A) (focus (translate f)).erase) f :=
  ⟨focus_wellInv _,
    ((focus_tmEq (translate f)).intrinsicDefEq (rootEnv A)).trans
      (interpret_translate f)⟩

end Equality
end Gimbal
