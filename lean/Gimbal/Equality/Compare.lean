/-
  Private candidate comparison for Milestone 7.

  Focus → shared-schedule saturation → ICC canonicalize → structural compare.
  Does **not** claim decidability of `DefEq`; exhaustion and invariant failure
  are distinct from inequality.
-/

import Gimbal.Equality.Focus
import Gimbal.Equality.ICC
import Gimbal.Equality.Saturation
import Gimbal.Equality.Translate

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- Stages reported when the candidate runner exhausts fuel. -/
inductive EqualityStage where
  | focus
  | saturate
  | canonicalize
  deriving DecidableEq, Repr

/--
Private comparison outcome. Milestone 8 must prove `exhausted` and
`invariantFailure` unreachable for the final bound.
-/
inductive CandidateResult where
  | equal
  | different
  | exhausted (stage : EqualityStage)
  | invariantFailure
  deriving DecidableEq, Repr

/-! ### Structural equality via erased untyped spines -/

/-- Untyped term spine for deterministic structural comparison. -/
inductive RawTm where
  | var (i : Nat)
  | unit
  | abort (t : RawTm)
  | pair (t u : RawTm)
  | fst (t : RawTm)
  | snd (t : RawTm)
  | inl (t : RawTm)
  | inr (t : RawTm)
  | case (s t u : RawTm)
  | lam (t : RawTm)
  | app (f a : RawTm)
  deriving DecidableEq, Repr

def Var.toRaw {Γ : Ctx sig} {A : Object sig.nBases} : Var Γ A → Nat
  | .here => 0
  | .there x => x.toRaw + 1

def Tm.toRaw {Γ : Ctx sig} {A : Object sig.nBases} : Tm Γ A → RawTm
  | .var x => .var x.toRaw
  | .unit => .unit
  | .abort t => .abort t.toRaw
  | .pair t u => .pair t.toRaw u.toRaw
  | .fst t => .fst t.toRaw
  | .snd t => .snd t.toRaw
  | .inl t => .inl t.toRaw
  | .inr t => .inr t.toRaw
  | .case s t u => .case s.toRaw t.toRaw u.toRaw
  | .lam t => .lam t.toRaw
  | .app f a => .app f.toRaw a.toRaw

/-- Structural equality after ICC canonicalization (via erasure). -/
def structurallyEqual {Γ : Ctx sig} {A : Object sig.nBases}
    (t u : InvTm Γ A) : Bool :=
  decide (Tm.toRaw (InvTm.erase t) == Tm.toRaw (InvTm.erase u))

/-- Compare two already-focused invertible terms under a shared reachability context. -/
def compareInv {A : Object sig.nBases}
    (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases)
    (t u : InvTm (Ctx.ofHyps Γ.hyps) A) (fuel : Nat := 2048) : CandidateResult :=
  match saturateInv (fuel := fuel) Γ goal t,
        saturateInv (fuel := fuel) Γ goal u with
  | .exhausted, _ | _, .exhausted => .exhausted .saturate
  | .invariantFailure, _ | _, .invariantFailure => .invariantFailure
  | .ok t', .ok u' =>
      let t'' := canonicalize (fuel := fuel) t'
      let u'' := canonicalize (fuel := fuel) u'
      if structurallyEqual t'' u'' then .equal else .different

/-- Compare two focused terms under an arbitrary snoc context. -/
def compareUnder {A : Object sig.nBases}
    (Γ : Ctx sig) (goal : Object sig.nBases)
    (t u : InvTm Γ A) (fuel : Nat := 2048) : CandidateResult :=
  match saturateUnder (fuel := fuel) Γ goal t,
        saturateUnder (fuel := fuel) Γ goal u with
  | .exhausted, _ | _, .exhausted => .exhausted .saturate
  | .invariantFailure, _ | _, .invariantFailure => .invariantFailure
  | .ok t', .ok u' =>
      let t'' := canonicalize (fuel := fuel) t'
      let u'' := canonicalize (fuel := fuel) u'
      if structurallyEqual t'' u'' then .equal else .different

/-- Focus then compare ordinary intrinsically typed terms. -/
def compareTm {Γ : Ctx sig} {A : Object sig.nBases}
    (goal : Object sig.nBases) (t u : Tm Γ A) (fuel : Nat := 2048) :
    CandidateResult :=
  match focusInv fuel t, focusInv fuel u with
  | .exhausted, _ | _, .exhausted => .exhausted .focus
  | .ok t', .ok u' => compareUnder Γ goal t' u' (fuel := fuel)

/--
Private candidate: compare two intrinsic morphisms via translate → focus →
shared saturation → ICC → structural equality.
-/
def compareIntrinsic {X Y : Object sig.nBases}
    (f g : IntrinsicMorphism sig X Y) (fuel : Nat := 2048) : CandidateResult :=
  compareTm (goal := Y) (translate f) (translate g) (fuel := fuel)

end Equality
end Gimbal
