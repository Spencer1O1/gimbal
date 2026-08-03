/-
  Stable origins for invertible-phase reification (Milestone 8F design E).

  An origin names a processable positive assumption independently of the raw
  de Bruijn index it currently occupies. Phase-entry hypotheses use their
  oldest-first slot; case splits record parent origin plus branch; saturation
  observations use the canonical schedule slot assigned at phase entry —
  never a constant such as `obs 0` for every `letPos` (see
  `OriginCollisionFree` in `Completeness.lean`).

  Origins are the orientation key for the unique-order subsystem: the worklist
  is sorted by `Origin.cmp`, never by `NegNeu.blt` / raw spines.
-/

import Gimbal.Equality.Algebra
import Gimbal.Equality.Focused
import Gimbal.Equality.Polarized

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Origins -/

/--
Stable identity of a binder introduced during an invertible phase.

* `hyp i` — phase-entry hypothesis at oldest-first index `i`
* `obs i` — saturation observation at canonical schedule slot `i`
* `dom i` — λ-domain binder at nesting depth `i` from phase entry
* `split o side` — payload binder from casing on `o`
  (`false` = left/`inl`, `true` = right/`inr`)
-/
inductive Origin (sig : Signature) : Type where
  | hyp (idx : Nat)
  | obs (slot : Nat)
  | dom (nesting : Nat)
  | split (parent : Origin sig) (side : Bool)
  deriving DecidableEq, Repr

/-- Total order used to force left-to-right processing of the worklist. -/
def Origin.cmp : Origin sig → Origin sig → Ordering
  | .hyp i, .hyp j => compare i j
  | .hyp _, _ => .lt
  | .obs _, .hyp _ => .gt
  | .obs i, .obs j => compare i j
  | .obs _, .dom _ => .lt
  | .obs _, .split .. => .lt
  | .dom _, .hyp _ => .gt
  | .dom _, .obs _ => .gt
  | .dom i, .dom j => compare i j
  | .dom _, .split .. => .lt
  | .split .., .hyp _ => .gt
  | .split .., .obs _ => .gt
  | .split .., .dom _ => .gt
  | .split p false, .split q false => Origin.cmp p q
  | .split p true, .split q true => Origin.cmp p q
  | .split p false, .split q true =>
      match Origin.cmp p q with
      | .eq => .lt
      | o => o
  | .split p true, .split q false =>
      match Origin.cmp p q with
      | .eq => .gt
      | o => o

def Origin.blt (o₁ o₂ : Origin sig) : Bool :=
  Origin.cmp o₁ o₂ == .lt

def Origin.ble (o₁ o₂ : Origin sig) : Bool :=
  let c := Origin.cmp o₁ o₂
  c == .lt || c == .eq

@[simp] theorem Origin.cmp_hyp_hyp (i j : Nat) :
    Origin.cmp (.hyp (sig := sig) i) (.hyp j) = compare i j := rfl

/-- `cmp` agrees with equality on the nose for identical constructors. -/
theorem Origin.cmp_self (o : Origin sig) : Origin.cmp o o = .eq := by
  induction o with
  | hyp i =>
      simp only [Origin.cmp]
      change compareOfLessAndEq i i = .eq
      simp [compareOfLessAndEq]
  | obs i =>
      simp only [Origin.cmp]
      change compareOfLessAndEq i i = .eq
      simp [compareOfLessAndEq]
  | dom i =>
      simp only [Origin.cmp]
      change compareOfLessAndEq i i = .eq
      simp [compareOfLessAndEq]
  | split p s ih => cases s <;> simp [Origin.cmp, ih]

/-! ### Origin environments -/

/--
Assignment of a stable origin to every variable in `Γ`.
`here` is the newest binder; phase-entry `hyp` indices remain oldest-first.
-/
def OriginEnv (Γ : Ctx sig) : Type :=
  ∀ {A : Object sig.nBases}, Var Γ A → Origin sig

namespace OriginEnv

def empty : OriginEnv (sig := sig) .empty :=
  fun x => nomatch x

/-- Extend under a new newest binder. -/
def snoc {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) : OriginEnv (Γ ▻ A)
  | _, .here => o
  | _, .there x => ε x

/--
Phase-entry environment: hypothesis `i` (oldest-first) gets `Origin.hyp i`.
Uses `Var.toRawIdx` (0 = newest) so `hypIdx = size - 1 - rawIdx`.
-/
def ofHyps (hyps : Array (Object sig.nBases)) : OriginEnv (Ctx.ofHyps hyps) :=
  fun {A} x => .hyp (hyps.size - 1 - Var.toRawIdx x)

/-- Transport origins along a renaming: look up after mapping the variable. -/
def rename {Γ Δ : Ctx sig} (ρ : Rename sig Γ Δ) (ε : OriginEnv Δ) :
    OriginEnv Γ
  | _, x => ε (ρ x)

/-- Origins after weakening: old bindings unchanged; new binder gets `o`. -/
def weaken {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) : OriginEnv (Γ ▻ A) :=
  OriginEnv.snoc ε o

/--
Exchange the two newest variables while each binding keeps its origin.
`Rename.exchange` is applied in the inverse direction (it is an involution).
-/
def exchange {Γ : Ctx sig} {A B : Object sig.nBases}
    (ε : OriginEnv (Γ ▻ A ▻ B)) : OriginEnv (Γ ▻ B ▻ A)
  | _, x => ε (Rename.exchange (A := B) (B := A) x)

@[simp] theorem snoc_here {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) :
    OriginEnv.snoc (A := A) ε o .here = o := rfl

@[simp] theorem snoc_there {Γ : Ctx sig} {A B : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) (x : Var Γ B) :
    OriginEnv.snoc (A := A) ε o (.there x) = ε x := rfl

theorem rename_id_apply {Γ : Ctx sig} (ε : OriginEnv Γ)
    {A : Object sig.nBases} (x : Var Γ A) :
    OriginEnv.rename (Rename.id (Γ := Γ)) ε x = ε x := rfl

theorem rename_comp_apply {Γ Δ Ε : Ctx sig}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) (ε : OriginEnv Ε)
    {A : Object sig.nBases} (x : Var Γ A) :
    OriginEnv.rename (Rename.comp ρ τ) ε x =
      OriginEnv.rename τ (OriginEnv.rename ρ ε) x := rfl

/-- Exchange is involutive on variables. -/
theorem exchange_exchange_var {Γ : Ctx sig} {A B C : Object sig.nBases}
    (x : Var (Γ ▻ A ▻ B) C) :
    Rename.exchange (A := B) (B := A)
        (Rename.exchange (A := A) (B := B) x) = x := by
  cases x with
  | here => rfl
  | there x =>
      cases x with
      | here => rfl
      | there _ => rfl

theorem exchange_involutive_apply {Γ : Ctx sig} {A B C : Object sig.nBases}
    (ε : OriginEnv (Γ ▻ A ▻ B)) (x : Var (Γ ▻ A ▻ B) C) :
    OriginEnv.exchange (A := B) (B := A)
        (OriginEnv.exchange (A := A) (B := B) ε) x = ε x := by
  simp only [OriginEnv.exchange]
  exact congrArg ε (exchange_exchange_var x)

/-- Weakening does not change origins of older variables. -/
theorem weaken_there {Γ : Ctx sig} {A B : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) (x : Var Γ B) :
    OriginEnv.weaken (A := A) ε o (.there x) = ε x :=
  rfl

/--
Exchanging the two newest binders never changes the origin of a variable
from the parent context.
-/
theorem exchange_preserves_older {Γ : Ctx sig} {A B C : Object sig.nBases}
    (ε : OriginEnv (Γ ▻ A ▻ B)) (x : Var Γ C) :
    OriginEnv.exchange (A := A) (B := B) ε (.there (.there x)) =
      ε (.there (.there x)) := by
  simp only [OriginEnv.exchange, Rename.exchange]

end OriginEnv

/-! ### Positive worklist entries -/

/-- A processable positive assumption: its origin and formula. -/
structure PosEntry (sig : Signature) where
  origin : Origin sig
  ty : Object sig.nBases
  deriving DecidableEq, Repr

/-- Collect positively polarized variables as a worklist ordered by `Origin.cmp`. -/
def OriginEnv.posWorklist {Γ : Ctx sig} (ε : OriginEnv Γ) : List (PosEntry sig) :=
  let rec collect : (Δ : Ctx sig) → OriginEnv Δ → List (PosEntry sig)
    | .empty, _ => []
    | .snoc Δ A, ε' =>
        let rest := collect Δ (fun {A} x => ε' (Var.there x))
        if objectPolarity A == .pos then
          { origin := ε' .here, ty := A } :: rest
        else
          rest
  (collect Γ ε).mergeSort fun e₁ e₂ => Origin.ble e₁.origin e₂.origin

/-- Resolve an origin to the unique variable currently carrying it, if any. -/
def OriginEnv.find? {Γ : Ctx sig} (ε : OriginEnv Γ) (o : Origin sig) :
    Option ((A : Object sig.nBases) × Var Γ A) :=
  let rec go : (Δ : Ctx sig) → OriginEnv Δ → Option ((A : Object sig.nBases) × Var Δ A)
    | .empty, _ => none
    | .snoc Δ A, ε' =>
        if ε' (.here : Var (Δ ▻ A) A) == o then
          some ⟨A, .here⟩
        else
          (go Δ (fun {B} x => ε' (Var.there x))).map fun ⟨B, x⟩ =>
            ⟨B, .there x⟩
  go Γ ε

end Equality
end Gimbal
