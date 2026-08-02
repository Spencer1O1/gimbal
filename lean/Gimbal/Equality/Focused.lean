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

/-! ### Renaming / weakening for focused syntax -/

mutual
def NegNeu.rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) : NegNeu Γ A → NegNeu Δ A
  | .var x => .var (ρ x)
  | .app n t => .app (NegNeu.rename ρ n) (InvTm.rename ρ t)
  | .fst n => .fst (NegNeu.rename ρ n)
  | .snd n => .snd (NegNeu.rename ρ n)

def PosNeu.rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) : PosNeu Γ A → PosNeu Δ A
  | .neu n => .neu (NegNeu.rename ρ n)
  | .inl p => .inl (PosNeu.rename ρ p)
  | .inr p => .inr (PosNeu.rename ρ p)

def InvTm.rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) : InvTm Γ A → InvTm Δ A
  | .unit => .unit
  | .pair t u => .pair (InvTm.rename ρ t) (InvTm.rename ρ u)
  | .lam t => .lam (InvTm.rename (Rename.ext ρ) t)
  | .case n t u =>
      .case (NegNeu.rename ρ n) (InvTm.rename (Rename.ext ρ) t)
        (InvTm.rename (Rename.ext ρ) u)
  | .abort n => .abort (NegNeu.rename ρ n)
  | .foc f => .foc (FocTm.rename ρ f)

def FocTm.rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) : FocTm Γ A → FocTm Δ A
  | .pos p => .pos (PosIntro.rename ρ p)
  | .neg n => .neg (NegElim.rename ρ n)
  | .letPos n t => .letPos (NegNeu.rename ρ n) (InvTm.rename (Rename.ext ρ) t)
  | .sat s => .sat (SatTm.rename ρ s)

def PosIntro.rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) : PosIntro Γ A → PosIntro Δ A
  | .done p => .done (PosNeu.rename ρ p)

def NegElim.rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) : NegElim Γ A → NegElim Δ A
  | .done n => .done (NegNeu.rename ρ n)

def SatTm.rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) : SatTm Γ A → SatTm Δ A
  | .mk s t => .mk s (InvTm.rename ρ t)
end

/-- Weaken a focused term by one newest binder. -/
def InvTm.weaken {Γ : Ctx sig} {A B : Object sig.nBases}
    (t : InvTm Γ A) : InvTm (Γ ▻ B) A :=
  InvTm.rename Rename.weaken t

def NegNeu.weaken {Γ : Ctx sig} {A B : Object sig.nBases}
    (n : NegNeu Γ A) : NegNeu (Γ ▻ B) A :=
  NegNeu.rename Rename.weaken n

/-- Cast a negative neutral along a type equality. -/
def NegNeu.cast {Γ : Ctx sig} {A B : Object sig.nBases}
    (h : A = B) (n : NegNeu Γ A) : NegNeu Γ B :=
  h ▸ n

/-- Cast an invertible term along a type equality. -/
def InvTm.castTy {Γ : Ctx sig} {A B : Object sig.nBases}
    (h : A = B) (t : InvTm Γ A) : InvTm Γ B :=
  h ▸ t

/-- Cast an invertible term along a context equality. -/
def InvTm.castCtx {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (h : Γ = Δ) (t : InvTm Γ A) : InvTm Δ A :=
  h ▸ t

def NegNeu.castCtx {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (h : Γ = Δ) (n : NegNeu Γ A) : NegNeu Δ A :=
  h ▸ n

/-- Cast a negative neutral along an equality of hypothesis arrays. -/
def NegNeu.castHyps {hyps hyps' : Array (Object sig.nBases)} {A : Object sig.nBases}
    (h : hyps = hyps') (n : NegNeu (Ctx.ofHyps hyps) A) :
    NegNeu (Ctx.ofHyps hyps') A :=
  NegNeu.castCtx (congrArg Ctx.ofHyps h) n

/-- Cast an invertible term along an equality of hypothesis arrays. -/
def InvTm.castHyps {hyps hyps' : Array (Object sig.nBases)} {A : Object sig.nBases}
    (h : hyps = hyps') (t : InvTm (Ctx.ofHyps hyps) A) :
    InvTm (Ctx.ofHyps hyps') A :=
  InvTm.castCtx (congrArg Ctx.ofHyps h) t

/-! ### Untyped spines (ordering, structural compare, exact demands) -/

mutual
inductive RawNeu where
  | var (i : Nat)
  | app (n : RawNeu) (arg : RawFocused)
  | fst (n : RawNeu)
  | snd (n : RawNeu)
  deriving DecidableEq, Repr

inductive RawPos where
  | neu (n : RawNeu)
  | inl (p : RawPos)
  | inr (p : RawPos)
  deriving DecidableEq, Repr

inductive RawFocused where
  | unit
  | pair (t u : RawFocused)
  | lam (t : RawFocused)
  | case (scrut : RawNeu) (t u : RawFocused)
  | abort (n : RawNeu)
  | pos (p : RawPos)
  | neg (n : RawNeu)
  | letPos (n : RawNeu) (t : RawFocused)
  | sat (schedSize : Nat) (t : RawFocused)
  deriving DecidableEq, Repr
end

def Var.toRawIdx {Γ : Ctx sig} {A : Object sig.nBases} : Var Γ A → Nat
  | .here => 0
  | .there x => x.toRawIdx + 1

mutual
def NegNeu.toRaw {Γ : Ctx sig} {A : Object sig.nBases} : NegNeu Γ A → RawNeu
  | .var x => .var x.toRawIdx
  | .app n t => .app (NegNeu.toRaw n) (InvTm.toRaw t)
  | .fst n => .fst (NegNeu.toRaw n)
  | .snd n => .snd (NegNeu.toRaw n)

def PosNeu.toRaw {Γ : Ctx sig} {A : Object sig.nBases} : PosNeu Γ A → RawPos
  | .neu n => .neu (NegNeu.toRaw n)
  | .inl p => .inl (PosNeu.toRaw p)
  | .inr p => .inr (PosNeu.toRaw p)

def InvTm.toRaw {Γ : Ctx sig} {A : Object sig.nBases} : InvTm Γ A → RawFocused
  | .unit => .unit
  | .pair t u => .pair (InvTm.toRaw t) (InvTm.toRaw u)
  | .lam t => .lam (InvTm.toRaw t)
  | .case n t u => .case (NegNeu.toRaw n) (InvTm.toRaw t) (InvTm.toRaw u)
  | .abort n => .abort (NegNeu.toRaw n)
  | .foc f => FocTm.toRaw f

def FocTm.toRaw {Γ : Ctx sig} {A : Object sig.nBases} : FocTm Γ A → RawFocused
  | .pos (.done p) => .pos (PosNeu.toRaw p)
  | .neg (.done n) => .neg (NegNeu.toRaw n)
  | .letPos n t => .letPos (NegNeu.toRaw n) (InvTm.toRaw t)
  | .sat (.mk s t) => .sat s.size (InvTm.toRaw t)
end

end Equality
end Gimbal
