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

/-! ### Structural equality on focused spines (preserves `letPos`) -/

mutual
/-- Untyped negative-neutral spine. -/
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

/-- Untyped focused spine for deterministic structural comparison. -/
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

/-- Structural equality after ICC canonicalization (focused spines, not `subst0`). -/
def structurallyEqual {Γ : Ctx sig} {A : Object sig.nBases}
    (t u : InvTm Γ A) : Bool :=
  decide (InvTm.toRaw t == InvTm.toRaw u)

/-- Compare two already-focused invertible terms under a shared reachability context. -/
def compareInv {A : Object sig.nBases}
    (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases)
    (t u : InvTm (Ctx.ofHyps Γ.hyps) A) (fuel : Nat := 2048) : CandidateResult :=
  let (sched, σ) := pairSchedule Γ goal t u
  match applyFixedSchedule fuel σ Γ.hyps sched t,
        applyFixedSchedule fuel σ Γ.hyps sched u with
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
  let r := Γ.toReachCtx
  have hctx : Ctx.ofHyps r.hyps = Γ := Ctx.ofHyps_toReachCtx Γ
  let t₀ : InvTm (Ctx.ofHyps r.hyps) A := InvTm.castCtx hctx.symm t
  let u₀ : InvTm (Ctx.ofHyps r.hyps) A := InvTm.castCtx hctx.symm u
  let (sched, σ) := pairSchedule r goal t₀ u₀
  match applyFixedSchedule fuel σ r.hyps sched t₀,
        applyFixedSchedule fuel σ r.hyps sched u₀ with
  | .exhausted, _ | _, .exhausted => .exhausted .saturate
  | .invariantFailure, _ | _, .invariantFailure => .invariantFailure
  | .ok t', .ok u' =>
      let t'' := canonicalize (fuel := fuel) (InvTm.castCtx hctx t')
      let u'' := canonicalize (fuel := fuel) (InvTm.castCtx hctx u')
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
