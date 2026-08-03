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
  /-- Shift `↓`: an invertible value of negative type used positively,
  e.g. the `⟨⟩` in `inl ⟨⟩ : Unit + B`. -/
  | val {Γ A} : InvTm Γ A → PosNeu Γ A

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
  | .val t => InvTm.erase t

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
  | .val t => .val (InvTm.rename ρ t)

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
  | val (t : RawFocused)
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

/-! ### Raw spine search (schedule dependency) -/

mutual
/-- `needle` occurs as a sub-neutral of `hay` (possibly equal). -/
def RawNeu.hasNeu (hay needle : RawNeu) : Bool :=
  hay == needle ||
    match hay with
    | .var _ => false
    | .app n a => RawNeu.hasNeu n needle || RawFocused.hasNeu a needle
    | .fst n => RawNeu.hasNeu n needle
    | .snd n => RawNeu.hasNeu n needle

def RawPos.hasNeu (hay : RawPos) (needle : RawNeu) : Bool :=
  match hay with
  | .neu n => RawNeu.hasNeu n needle
  | .inl p => RawPos.hasNeu p needle
  | .inr p => RawPos.hasNeu p needle
  | .val t => RawFocused.hasNeu t needle

def RawFocused.hasNeu (hay : RawFocused) (needle : RawNeu) : Bool :=
  match hay with
  | .unit => false
  | .pair t u => RawFocused.hasNeu t needle || RawFocused.hasNeu u needle
  | .lam t => RawFocused.hasNeu t needle
  | .case s t u =>
      RawNeu.hasNeu s needle || RawFocused.hasNeu t needle || RawFocused.hasNeu u needle
  | .abort n => RawNeu.hasNeu n needle
  | .pos p => RawPos.hasNeu p needle
  | .neg n => RawNeu.hasNeu n needle
  | .letPos n t => RawNeu.hasNeu n needle || RawFocused.hasNeu t needle
  | .sat _ t => RawFocused.hasNeu t needle
end

/-- Strict dependency: `outer` mentions `inner` as a proper sub-neutral. -/
def RawNeu.dependsOn (outer inner : RawNeu) : Bool :=
  outer != inner && RawNeu.hasNeu outer inner

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
  | .val t => .val (InvTm.toRaw t)

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
  -- Schedule annotations are operational metadata: erase before structural compare.
  | .sat (.mk _s t) => InvTm.toRaw t
end

/-! ### Phase legality (`WellFocused`) -/

mutual
/-- Invertible terms respect invertible introductions and legal focus entries. -/
inductive WellInv : {Γ : Ctx sig} → {A : Object sig.nBases} → InvTm Γ A → Prop where
  | unit {Γ} : WellInv (.unit (Γ := Γ))
  | pair {Γ A B} {t : InvTm Γ A} {u : InvTm Γ B} :
      WellInv t → WellInv u → WellInv (.pair t u)
  | lam {Γ A B} {t : InvTm (Γ ▻ A) B} :
      WellInv t → WellInv (.lam t)
  | case {Γ A B C} {n : NegNeu Γ (.coprod A B)}
      {t : InvTm (Γ ▻ A) C} {u : InvTm (Γ ▻ B) C} :
      WellInv t → WellInv u → WellInv (.case n t u)
  | abort {Γ A} {n : NegNeu Γ .never} : WellInv (.abort (A := A) n)
  | foc {Γ A} {f : FocTm Γ A} : WellFoc f → WellInv (.foc f)

/-- Focused terms match goal polarity (pos/neg) or binder/saturation forms. -/
inductive WellFoc : {Γ : Ctx sig} → {A : Object sig.nBases} → FocTm Γ A → Prop where
  | pos {Γ A} {p : PosNeu Γ A} :
      objectPolarity A = .pos → WellPos p → WellFoc (.pos (.done p))
  | neg {Γ A} {n : NegNeu Γ A} :
      objectPolarity A = .neg → WellFoc (.neg (.done n))
  | letPos {Γ P A} {n : NegNeu Γ P} {t : InvTm (Γ ▻ P) A} :
      objectPolarity P = .pos → WellInv t → WellFoc (.letPos n t)
  | sat {Γ A} {s : Schedule sig.nBases} {t : InvTm Γ A} :
      WellInv t → WellFoc (.sat (.mk s t))

/-- Positive values: neutrals at positive types, injections, and `↓` shifts. -/
inductive WellPos : {Γ : Ctx sig} → {A : Object sig.nBases} → PosNeu Γ A → Prop where
  | neu {Γ A} {n : NegNeu Γ A} :
      objectPolarity A = .pos → WellPos (.neu n)
  | inl {Γ A B} {p : PosNeu Γ A} : WellPos p → WellPos (.inl (B := B) p)
  | inr {Γ A B} {p : PosNeu Γ B} : WellPos p → WellPos (.inr (A := A) p)
  | val {Γ A} {t : InvTm Γ A} :
      objectPolarity A = .neg → WellInv t → WellPos (.val t)
end

mutual
def wellInvb {Γ : Ctx sig} {A : Object sig.nBases} : InvTm Γ A → Bool
  | .unit => true
  | .pair t u => wellInvb t && wellInvb u
  | .lam t => wellInvb t
  | .case _ t u => wellInvb t && wellInvb u
  | .abort _ => true
  | .foc f => wellFocb f

def wellFocb {Γ : Ctx sig} {A : Object sig.nBases} : FocTm Γ A → Bool
  | .pos (.done p) => objectPolarity A == .pos && wellPosb p
  | .neg (.done _) => objectPolarity A == .neg
  | .letPos (P := P) _ t => objectPolarity P == .pos && wellInvb t
  | .sat (.mk _ t) => wellInvb t

def wellPosb {Γ : Ctx sig} {A : Object sig.nBases} : PosNeu Γ A → Bool
  | .neu _ => objectPolarity A == .pos
  | .inl p => wellPosb p
  | .inr p => wellPosb p
  | .val t => objectPolarity A == .neg && wellInvb t
end

/-- Executable phase check (sound for `WellInv` / `WellFoc` by construction). -/
def InvTm.wellFocused {Γ : Ctx sig} {A : Object sig.nBases} (t : InvTm Γ A) : Bool :=
  wellInvb t

/-! ### Unweakening (for nested case/case commuting) -/

/--
Invert a single weakening on a negative neutral when the newest binder is unused.
Applications are refused (argument unweakening is not needed for case/case).
-/
def NegNeu.unweaken? {Γ : Ctx sig} {B A : Object sig.nBases} :
    NegNeu (Γ ▻ B) A → Option (NegNeu Γ A)
  | .var .here => none
  | .var (.there x) => some (.var x)
  | .fst n => (NegNeu.unweaken? n).map .fst
  | .snd n => (NegNeu.unweaken? n).map .snd
  | .app _ _ => none

end Equality
end Gimbal
