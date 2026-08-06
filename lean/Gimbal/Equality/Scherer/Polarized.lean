/-
  Scherer-core polarization surface (S1).

  Reuses the locked `Gimbal.Equality` polarization (`Polarity`, `Pos`, `Neg`,
  `asPos`, `asNeg`, erasure, shift detection). No second polarized-type
  universe. Adds only the stable-formula classification Scherer needs later:
  genuine negatives versus unshifted positive atoms.
-/

import Gimbal.Equality.Polarized

namespace Gimbal.Equality.Scherer

/-!
`Polarity`, `objectPolarity`, `Pos`, `Neg`, `Pos.erase`, `Neg.erase`,
`asPos`, `asNeg`, `erase_asPos`, `erase_asNeg`, `Pos.isShift`, and
`Neg.isShift` are the Equality definitions (in scope via this namespace nesting).
-/

/-- Depolarization alias for positive polarized types. -/
abbrev depolarizePos {n : Nat} (P : Pos n) : Object n := P.erase

/-- Depolarization alias for negative polarized types. -/
abbrev depolarizeNeg {n : Nat} (N : Neg n) : Object n := N.erase

/-- Polarization alias (positive). -/
abbrev polarizePos {n : Nat} : Object n → Pos n := asPos

/-- Polarization alias (negative). -/
abbrev polarizeNeg {n : Nat} : Object n → Neg n := asNeg

theorem depolarizePos_polarizePos {n : Nat} (A : Object n) :
    depolarizePos (polarizePos A) = A :=
  erase_asPos A

theorem depolarizeNeg_polarizeNeg {n : Nat} (A : Object n) :
    depolarizeNeg (polarizeNeg A) = A :=
  erase_asNeg A

theorem asPos_isShift_eq {n : Nat} (A : Object n) :
    (asPos A).isShift = (objectPolarity A == Polarity.neg) := by
  cases A <;> rfl

theorem asNeg_isShift_eq {n : Nat} (A : Object n) :
    (asNeg A).isShift = (objectPolarity A == Polarity.pos) := by
  cases A <;> rfl

theorem asPos_not_shift_of_pos {n : Nat} (A : Object n)
    (h : objectPolarity A = .pos) :
    (asPos A).isShift = false := by
  rw [asPos_isShift_eq, h]; rfl

theorem asNeg_not_shift_of_neg {n : Nat} (A : Object n)
    (h : objectPolarity A = .neg) :
    (asNeg A).isShift = false := by
  rw [asNeg_isShift_eq, h]; rfl

/--
Stable formula kind for the eventual Scherer stable context `Γ⁻ᵃ`.

- `neg N` — a genuine negative polarized type
- `atom q` — an unshifted positive atom

`Neg.shift (Pos.atom q)` is a negative polarized type (a down-shift), not
the stable atomic case; use `StableTy.atom q` for that.
-/
inductive StableTy (n : Nat) : Type where
  | neg : Neg n → StableTy n
  | atom : Fin n → StableTy n
  deriving DecidableEq

/-- Erase a stable formula to a Gimbal object. -/
def StableTy.erase {n : Nat} : StableTy n → Object n
  | .neg N => N.erase
  | .atom q => .base q

@[simp] theorem StableTy.erase_neg {n : Nat} (N : Neg n) :
    StableTy.erase (.neg N) = N.erase := rfl

@[simp] theorem StableTy.erase_atom {n : Nat} (q : Fin n) :
    StableTy.erase (.atom q) = .base q := rfl

/--
Erasure of a shifted atom coincides with the stable atom's erasure, but the
stable classification is `StableTy.atom`, not `StableTy.neg (.shift (.atom q))`.
-/
theorem StableTy.erase_atom_eq_erase_shift_atom {n : Nat} (q : Fin n) :
    StableTy.erase (.atom q) = Neg.erase (.shift (.atom q)) := rfl

end Gimbal.Equality.Scherer
