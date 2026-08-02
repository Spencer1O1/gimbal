/-
  Deterministic focusing: convert ordinary intrinsically typed terms into
  phase-indexed focused syntax. Uses an explicit fuel counter (no `partial`);
  exhaustion is reported separately and must not be confused with inequality.
-/

import Gimbal.Equality.Focused

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- Result of a focusing attempt. -/
inductive FocusResult {sig : Signature} (Γ : Ctx sig) (A : Object sig.nBases) where
  | ok : InvTm Γ A → FocusResult Γ A
  | exhausted

def FocusResult.toOption {sig : Signature} {Γ : Ctx sig} {A : Object sig.nBases} :
    FocusResult Γ A → Option (InvTm Γ A)
  | .ok t => some t
  | .exhausted => none

/-- Structural size for fuel budgeting (computable). -/
def tmSize {Γ : Ctx sig} {A : Object sig.nBases} : Tm Γ A → Nat
  | .var _ => 1
  | .unit => 1
  | .abort t => 1 + tmSize t
  | .pair t u => 1 + tmSize t + tmSize u
  | .fst t => 1 + tmSize t
  | .snd t => 1 + tmSize t
  | .inl t => 1 + tmSize t
  | .inr t => 1 + tmSize t
  | .case s t u => 1 + tmSize s + tmSize t + tmSize u
  | .lam t => 1 + tmSize t
  | .app t u => 1 + tmSize t + tmSize u

mutual
/-- Focus a term into the invertible phase. -/
def focusInv {Γ : Ctx sig} {A : Object sig.nBases} :
    Nat → Tm Γ A → FocusResult Γ A
  | 0, _ => .exhausted
  | fuel + 1, t =>
    match t with
    | .unit =>
        .ok .unit
    | .pair t₁ t₂ =>
        match focusInv fuel t₁, focusInv fuel t₂ with
        | .ok t₁', .ok t₂' => .ok (.pair t₁' t₂')
        | .exhausted, _ | _, .exhausted => .exhausted
    | .lam t =>
        match focusInv fuel t with
        | .ok t' => .ok (.lam t')
        | .exhausted => .exhausted
    | .inl t =>
        match focusFoc fuel (.inl t) with
        | some f => .ok (.foc f)
        | none => .exhausted
    | .inr t =>
        match focusFoc fuel (.inr t) with
        | some f => .ok (.foc f)
        | none => .exhausted
    | .case s l r =>
        match focusNegNeu fuel s, focusInv fuel l, focusInv fuel r with
        | some n, .ok l', .ok r' => .ok (.case n l' r')
        | _, _, _ => focusInvByGoal (fuel + 1) (.case s l r)
    | .abort s =>
        match focusNegNeu fuel s with
        | some n => .ok (.abort n)
        | none => focusInvByGoal (fuel + 1) (.abort s)
    | .var x =>
        focusInvByGoal (fuel + 1) (.var x)
    | .fst t =>
        focusInvByGoal (fuel + 1) (.fst t)
    | .snd t =>
        focusInvByGoal (fuel + 1) (.snd t)
    | .app f a =>
        focusInvByGoal (fuel + 1) (.app f a)

/-- Type-directed invertible introductions / focusing entry. -/
def focusInvByGoal {Γ : Ctx sig} {A : Object sig.nBases} :
    Nat → Tm Γ A → FocusResult Γ A
  | 0, _ => .exhausted
  | fuel + 1, t =>
    match A with
    | .unit =>
        .ok .unit
    | .prod A B =>
        match focusInv fuel (.fst t), focusInv fuel (.snd t) with
        | .ok t₁, .ok t₂ => .ok (.pair t₁ t₂)
        | .exhausted, _ | _, .exhausted => .exhausted
    | .exp A B =>
        match focusInv fuel (.app (weakenTerm t) (.var .here)) with
        | .ok body => .ok (.lam body)
        | .exhausted => .exhausted
    | .never | .base _ | .coprod _ _ =>
        match focusFoc fuel t with
        | some f => .ok (.foc f)
        | none => .exhausted

/-- Try to read a term as a negative neutral spine. -/
def focusNegNeu {Γ : Ctx sig} {A : Object sig.nBases} :
    Nat → Tm Γ A → Option (NegNeu Γ A)
  | 0, _ => none
  | _fuel + 1, .var x =>
      some (.var x)
  | fuel + 1, .fst t => do
      let n ← focusNegNeu fuel t
      pure (.fst n)
  | fuel + 1, .snd t => do
      let n ← focusNegNeu fuel t
      pure (.snd n)
  | fuel + 1, .app f a => do
      let n ← focusNegNeu fuel f
      match focusInv fuel a with
      | .ok a' => pure (.app n a')
      | .exhausted => none
  | _, _ => none

/-- Try to read a term as a positive neutral spine. -/
def focusPosNeu {Γ : Ctx sig} {A : Object sig.nBases} :
    Nat → Tm Γ A → Option (PosNeu Γ A)
  | 0, _ => none
  | fuel + 1, .inl t => do
      let p ← focusPosNeu fuel t
      pure (.inl p)
  | fuel + 1, .inr t => do
      let p ← focusPosNeu fuel t
      pure (.inr p)
  | fuel + 1, t => do
      let n ← focusNegNeu fuel t
      pure (.neu n)

/-- Choice-of-focusing entry. -/
def focusFoc {Γ : Ctx sig} {A : Object sig.nBases} :
    Nat → Tm Γ A → Option (FocTm Γ A)
  | 0, _ => none
  | fuel + 1, t =>
    match objectPolarity A with
    | .pos => do
        let p ← focusPosNeu fuel t
        pure (.pos (.done p))
    | .neg => do
        let n ← focusNegNeu fuel t
        pure (.neg (.done n))
end

/-- Default fuel from term size. -/
def focusFuel {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) : Nat :=
  64 + 8 * tmSize t

/-- Focus a term; exhaustion is distinct from a focusing invariant failure. -/
def focus {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) : FocusResult Γ A :=
  focusInv (focusFuel t) t

/-- Focus and require success (for fixtures on small terms). -/
def focus! {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) : Option (InvTm Γ A) :=
  (focus t).toOption

end Equality
end Gimbal
