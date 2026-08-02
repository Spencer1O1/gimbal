/-
  Fixed Scherer polarization for Phase 0 objects.
  Atoms, empty, and coproducts are positive; unit, products, and functions
  are negative. Minimal shifts connect opposite polarities.
-/

import Gimbal.Object

namespace Gimbal
namespace Equality

/-- Structural polarity of an unpolarized Phase 0 object. -/
inductive Polarity where
  | pos
  | neg
  deriving DecidableEq, Repr

/-- Polarity assignment locked by the Milestone 7 handoff. -/
def objectPolarity {n : Nat} : Object n → Polarity
  | .base _ => .pos
  | .never => .pos
  | .coprod _ _ => .pos
  | .unit => .neg
  | .prod _ _ => .neg
  | .exp _ _ => .neg

@[simp] theorem objectPolarity_base {n} (q : Fin n) :
    objectPolarity (.base q) = .pos := rfl
@[simp] theorem objectPolarity_never {n} :
    objectPolarity (.never : Object n) = .pos := rfl
@[simp] theorem objectPolarity_coprod {n} (A B : Object n) :
    objectPolarity (.coprod A B) = .pos := rfl
@[simp] theorem objectPolarity_unit {n} :
    objectPolarity (.unit : Object n) = .neg := rfl
@[simp] theorem objectPolarity_prod {n} (A B : Object n) :
    objectPolarity (.prod A B) = .neg := rfl
@[simp] theorem objectPolarity_exp {n} (A B : Object n) :
    objectPolarity (.exp A B) = .neg := rfl

mutual
/-- Positive polarized types (with shift `↑` from negative). -/
inductive Pos (n : Nat) : Type where
  | atom : Fin n → Pos n
  | zero : Pos n
  | sum : Pos n → Pos n → Pos n
  | shift : Neg n → Pos n

/-- Negative polarized types (with shift `↓` from positive). -/
inductive Neg (n : Nat) : Type where
  | one : Neg n
  | prod : Neg n → Neg n → Neg n
  /-- Function type with positive domain and negative codomain. -/
  | arr : Pos n → Neg n → Neg n
  | shift : Pos n → Neg n
end

mutual
/-- Forget positive polarization (shifts erase). -/
def Pos.erase {n : Nat} : Pos n → Object n
  | .atom q => .base q
  | .zero => .never
  | .sum A B => .coprod (Pos.erase A) (Pos.erase B)
  | .shift N => Neg.erase N

/-- Forget negative polarization (shifts erase). -/
def Neg.erase {n : Nat} : Neg n → Object n
  | .one => .unit
  | .prod A B => .prod (Neg.erase A) (Neg.erase B)
  | .arr A B => .exp (Pos.erase A) (Neg.erase B)
  | .shift P => Pos.erase P
end

mutual
/-- Minimal embedding into positive polarity (insert `↑` when needed). -/
def asPos {n : Nat} : Object n → Pos n
  | .base q => .atom q
  | .never => .zero
  | .coprod A B => .sum (asPos A) (asPos B)
  | .unit => .shift .one
  | .prod A B => .shift (.prod (asNeg A) (asNeg B))
  | .exp A B => .shift (.arr (asPos A) (asNeg B))

/-- Minimal embedding into negative polarity (insert `↓` when needed). -/
def asNeg {n : Nat} : Object n → Neg n
  | .unit => .one
  | .prod A B => .prod (asNeg A) (asNeg B)
  | .exp A B => .arr (asPos A) (asNeg B)
  | .base q => .shift (.atom q)
  | .never => .shift .zero
  | .coprod A B => .shift (.sum (asPos A) (asPos B))
end

theorem erase_asPos_asNeg {n : Nat} (A : Object n) :
    (asPos A).erase = A ∧ (asNeg A).erase = A := by
  induction A with
  | base q => exact ⟨rfl, rfl⟩
  | unit => exact ⟨rfl, rfl⟩
  | never => exact ⟨rfl, rfl⟩
  | prod A B ihA ihB =>
    refine ⟨?_, ?_⟩
    · simp only [asPos, Pos.erase, Neg.erase, ihA.2, ihB.2]
    · simp only [asNeg, Neg.erase, ihA.2, ihB.2]
  | coprod A B ihA ihB =>
    refine ⟨?_, ?_⟩
    · simp only [asPos, Pos.erase, ihA.1, ihB.1]
    · simp only [asNeg, Neg.erase, Pos.erase, ihA.1, ihB.1]
  | exp A B ihA ihB =>
    refine ⟨?_, ?_⟩
    · simp only [asPos, Pos.erase, Neg.erase, ihA.1, ihB.2]
    · simp only [asNeg, Neg.erase, ihA.1, ihB.2]

theorem erase_asPos {n : Nat} (A : Object n) : (asPos A).erase = A :=
  (erase_asPos_asNeg A).1

theorem erase_asNeg {n : Nat} (A : Object n) : (asNeg A).erase = A :=
  (erase_asPos_asNeg A).2

/-- Whether a positive type is a shift (not structurally positive). -/
def Pos.isShift {n : Nat} : Pos n → Bool
  | .shift _ => true
  | _ => false

/-- Whether a negative type is a shift (not structurally negative). -/
def Neg.isShift {n : Nat} : Neg n → Bool
  | .shift _ => true
  | _ => false

end Equality
end Gimbal
