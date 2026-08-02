/-
  Phase-indexed focused syntax for the equality calculus.
  Illegal phase transitions are unrepresentable.
  Saturation is represented as a phase with an explicit schedule slot;
  schedule construction lives in later Reachability/Saturation modules.
-/

import Gimbal.Equality.LambdaSyntax
import Gimbal.Equality.Polarized
import Gimbal.Equality.Reachability

namespace Gimbal
namespace Equality

/-- Focused proof phases (Scherer-style). -/
inductive Phase where
  | inv
  | sat
  | foc
  | posIntro
  | negElim
  deriving DecidableEq, Repr

variable {sig : Signature}

/-!
Focused syntax is mutually inductive across phases.
Contexts remain unpolarized `Object` contexts from `LambdaSyntax`;
polarity guides which constructors are legal at each phase.
-/

mutual
/-- Negative neutrals (`⇓` spines). -/
inductive NegNeu : Ctx sig → Object sig.nBases → Type where
  | var {Γ A} : Var Γ A → NegNeu Γ A
  | app {Γ A B} : NegNeu Γ (.exp A B) → InvTm Γ A → NegNeu Γ B
  | fst {Γ A B} : NegNeu Γ (.prod A B) → NegNeu Γ A
  | snd {Γ A B} : NegNeu Γ (.prod A B) → NegNeu Γ B

/-- Positive neutrals (`⇑` spines). -/
inductive PosNeu : Ctx sig → Object sig.nBases → Type where
  | neu {Γ A} : NegNeu Γ A → PosNeu Γ A
  | inl {Γ A B} : PosNeu Γ A → PosNeu Γ (.coprod A B)
  | inr {Γ A B} : PosNeu Γ B → PosNeu Γ (.coprod A B)

/-- Invertible-phase terms. -/
inductive InvTm : Ctx sig → Object sig.nBases → Type where
  | unit {Γ} : InvTm Γ .unit
  | pair {Γ A B} : InvTm Γ A → InvTm Γ B → InvTm Γ (.prod A B)
  | lam {Γ A B} : InvTm (Γ ▻ A) B → InvTm Γ (.exp A B)
  | case {Γ A B C} :
      NegNeu Γ (.coprod A B) →
      InvTm (Γ ▻ A) C →
      InvTm (Γ ▻ B) C →
      InvTm Γ C
  | abort {Γ A} : NegNeu Γ .never → InvTm Γ A
  | foc {Γ A} : FocTm Γ A → InvTm Γ A

/-- Choice-of-focusing terms. -/
inductive FocTm : Ctx sig → Object sig.nBases → Type where
  | pos {Γ A} : PosIntro Γ A → FocTm Γ A
  | neg {Γ A} : NegElim Γ A → FocTm Γ A
  | letPos {Γ P A} : NegNeu Γ P → InvTm (Γ ▻ P) A → FocTm Γ A
  | sat {Γ A} : SatTm Γ A → FocTm Γ A

/-- Positive introduction focus. -/
inductive PosIntro : Ctx sig → Object sig.nBases → Type where
  | done {Γ A} : PosNeu Γ A → PosIntro Γ A

/-- Negative elimination focus. -/
inductive NegElim : Ctx sig → Object sig.nBases → Type where
  | done {Γ A} : NegNeu Γ A → NegElim Γ A

/-- Saturation-phase terms carrying an explicit finite schedule. -/
inductive SatTm : Ctx sig → Object sig.nBases → Type where
  | mk {Γ A} : Schedule sig.nBases → InvTm Γ A → SatTm Γ A
end

/-- Package a focused term at an explicit phase. -/
def Focused : Phase → Ctx sig → Object sig.nBases → Type
  | .inv => InvTm
  | .sat => SatTm
  | .foc => FocTm
  | .posIntro => PosIntro
  | .negElim => NegElim

mutual
def NegNeu.erase {Γ : Ctx sig} {A : Object sig.nBases} : NegNeu Γ A → Tm Γ A
  | .var x => .var x
  | .app n t => .app (NegNeu.erase n) (InvTm.erase t)
  | .fst n => .fst (NegNeu.erase n)
  | .snd n => .snd (NegNeu.erase n)

def PosNeu.erase {Γ : Ctx sig} {A : Object sig.nBases} : PosNeu Γ A → Tm Γ A
  | .neu n => NegNeu.erase n
  | .inl p => .inl (PosNeu.erase p)
  | .inr p => .inr (PosNeu.erase p)

def InvTm.erase {Γ : Ctx sig} {A : Object sig.nBases} : InvTm Γ A → Tm Γ A
  | .unit => .unit
  | .pair t u => .pair (InvTm.erase t) (InvTm.erase u)
  | .lam t => .lam (InvTm.erase t)
  | .case n t u =>
      .case (NegNeu.erase n) (InvTm.erase t) (InvTm.erase u)
  | .abort n => .abort (NegNeu.erase n)
  | .foc f => FocTm.erase f

def FocTm.erase {Γ : Ctx sig} {A : Object sig.nBases} : FocTm Γ A → Tm Γ A
  | .pos p => PosIntro.erase p
  | .neg n => NegElim.erase n
  | .letPos n t => subst0 (InvTm.erase t) (NegNeu.erase n)
  | .sat s => SatTm.erase s

def PosIntro.erase {Γ : Ctx sig} {A : Object sig.nBases} : PosIntro Γ A → Tm Γ A
  | .done p => PosNeu.erase p

def NegElim.erase {Γ : Ctx sig} {A : Object sig.nBases} : NegElim Γ A → Tm Γ A
  | .done n => NegNeu.erase n

def SatTm.erase {Γ : Ctx sig} {A : Object sig.nBases} : SatTm Γ A → Tm Γ A
  | .mk _ t => InvTm.erase t
end

end Equality
end Gimbal
