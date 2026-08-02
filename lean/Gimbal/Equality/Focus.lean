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

/-- Result of attempting to parse a neutral / focused spine. -/
inductive ParseResult (α : Type) where
  | ok : α → ParseResult α
  | exhausted
  | mismatch

def ParseResult.toOption {α} : ParseResult α → Option α
  | .ok a => some a
  | .exhausted | .mismatch => none

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
        | .ok f => .ok (.foc f)
        | .exhausted => .exhausted
        | .mismatch => .exhausted
    | .inr t =>
        match focusFoc fuel (.inr t) with
        | .ok f => .ok (.foc f)
        | .exhausted => .exhausted
        | .mismatch => .exhausted
    | .var x =>
        focusInvByGoal (fuel + 1) (.var x)
    | .fst (.pair t _) =>
        focusInv fuel t
    | .fst t =>
        focusInvByGoal (fuel + 1) (.fst t)
    | .snd (.pair _ u) =>
        focusInv fuel u
    | .snd t =>
        focusInvByGoal (fuel + 1) (.snd t)
    | .app (.lam body) a =>
        focusInv fuel (subst0 body a)
    | .app f a =>
        focusInvByGoal (fuel + 1) (.app f a)
    | .case (.inl v) l _ =>
        focusInv fuel (subst0 l v)
    | .case (.inr v) _ r =>
        focusInv fuel (subst0 r v)
    | .case s l r =>
        match focusNegNeu fuel s, focusInv fuel l, focusInv fuel r with
        | .ok n, .ok l', .ok r' => .ok (.case n l' r')
        | .exhausted, _, _ | _, .exhausted, _ | _, _, .exhausted => .exhausted
        | .mismatch, _, _ =>
            focusInvByGoal (fuel + 1) (.case s l r)
    | .abort s =>
        match focusNegNeu fuel s with
        | .ok n => .ok (.abort n)
        | .exhausted => .exhausted
        | .mismatch => focusInvByGoal (fuel + 1) (.abort s)

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
        | .ok f => .ok (.foc f)
        | .exhausted => .exhausted
        | .mismatch => .exhausted

/-- Try to read a term as a negative neutral spine. -/
def focusNegNeu {Γ : Ctx sig} {A : Object sig.nBases} :
    Nat → Tm Γ A → ParseResult (NegNeu Γ A)
  | 0, _ => .exhausted
  | _fuel + 1, .var x =>
      .ok (.var x)
  | fuel + 1, .fst (.pair t _) =>
      focusNegNeu fuel t
  | fuel + 1, .fst t =>
      match focusNegNeu fuel t with
      | .ok n => .ok (.fst n)
      | .exhausted => .exhausted
      | .mismatch => .mismatch
  | fuel + 1, .snd (.pair _ u) =>
      focusNegNeu fuel u
  | fuel + 1, .snd t =>
      match focusNegNeu fuel t with
      | .ok n => .ok (.snd n)
      | .exhausted => .exhausted
      | .mismatch => .mismatch
  | fuel + 1, .app f a =>
      match focusNegNeu fuel f, focusInv fuel a with
      | .ok n, .ok a' => .ok (.app n a')
      | .exhausted, _ | _, .exhausted => .exhausted
      | .mismatch, _ => .mismatch
  | _, _ => .mismatch

/-- Try to read a term as a positive neutral spine. -/
def focusPosNeu {Γ : Ctx sig} {A : Object sig.nBases} :
    Nat → Tm Γ A → ParseResult (PosNeu Γ A)
  | 0, _ => .exhausted
  | fuel + 1, .inl t =>
      match focusPosNeu fuel t with
      | .ok p => .ok (.inl p)
      | .exhausted => .exhausted
      | .mismatch => .mismatch
  | fuel + 1, .inr t =>
      match focusPosNeu fuel t with
      | .ok p => .ok (.inr p)
      | .exhausted => .exhausted
      | .mismatch => .mismatch
  | fuel + 1, t =>
      match focusNegNeu fuel t with
      | .ok n => .ok (.neu n)
      | .exhausted => .exhausted
      | .mismatch => .mismatch

/-- Choice-of-focusing entry. -/
def focusFoc {Γ : Ctx sig} {A : Object sig.nBases} :
    Nat → Tm Γ A → ParseResult (FocTm Γ A)
  | 0, _ => .exhausted
  | fuel + 1, t =>
    match objectPolarity A with
    | .pos =>
        match focusPosNeu fuel t with
        | .ok p => .ok (.pos (.done p))
        | .exhausted => .exhausted
        | .mismatch => .mismatch
    | .neg =>
        match focusNegNeu fuel t with
        | .ok n => .ok (.neg (.done n))
        | .exhausted => .exhausted
        | .mismatch => .mismatch
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
