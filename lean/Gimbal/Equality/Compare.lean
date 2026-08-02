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

/-- Structural equality after ICC canonicalization (focused spines, not `subst0`). -/
def structurallyEqual {Γ : Ctx sig} {A : Object sig.nBases}
    (t u : InvTm Γ A) : Bool :=
  decide (InvTm.toRaw t == InvTm.toRaw u)

/-- Combine two candidate results (both sides must agree to be equal). -/
def CandidateResult.and : CandidateResult → CandidateResult → CandidateResult
  | .equal, .equal => .equal
  | .exhausted s, _ => .exhausted s
  | _, .exhausted s => .exhausted s
  | .invariantFailure, _ | _, .invariantFailure => .invariantFailure
  | _, _ => .different

/-- Old-prefix reachability context (`hyps[0:newFrom]`). -/
def ReachCtx.oldPrefix {n : Nat} (Γ : ReachCtx n) : ReachCtx n :=
  ⟨(Γ.hyps.toList.take Γ.newFrom).toArray, Γ.newFrom⟩

mutual
/--
Recursive pair-directed saturation under an explicit old/new split.
After applying the shared schedule (consistency ∪ exact demands), walk
invertible structure in lockstep and re-enter saturation under each new binder.
-/
def compareSatRec (fuel : Nat) (Γ : ReachCtx sig.nBases)
    (goal : Object sig.nBases) {A : Object sig.nBases}
    (t u : InvTm (Ctx.ofHyps Γ.hyps) A) : CandidateResult :=
  match fuel with
  | 0 => .exhausted .saturate
  | fuel + 1 =>
    -- Note: a full `checkOldInvariant` on Γold is too strong once opaque
    -- generators inhabit positives (targets are simply deducible from Γold
    -- without being retrievable there). Milestone 8 tightens this against
    -- Scherer's selection invariant; for M7 we only refuse on hard failure.
    --
    -- Fast path: if ICC already identifies the spines, skip re-saturation.
    -- Shared-schedule application preserves equality, so this stays sound for
    -- the candidate; it avoids pathological re-observation of sum-valued gens.
    let t0 := canonicalize (fuel := fuel) t
    let u0 := canonicalize (fuel := fuel) u
    if structurallyEqual t0 u0 then .equal
    else
      let (entries, σ) := pairObs Γ goal t0 u0
      match applyPairObs fuel σ Γ.hyps entries t0,
            applyPairObs fuel σ Γ.hyps entries u0 with
      | .exhausted, _ | _, .exhausted => .exhausted .saturate
      | .invariantFailure, _ | _, .invariantFailure => .invariantFailure
      | .ok t', .ok u' =>
          compareInvRec fuel Γ.hyps goal
            (canonicalize (fuel := fuel) t')
            (canonicalize (fuel := fuel) u')

/-- Lockstep invertible comparison with re-entry under new binders. -/
def compareInvRec (fuel : Nat) (hyps : Array (Object sig.nBases))
    (goal : Object sig.nBases) {A : Object sig.nBases}
    (t u : InvTm (Ctx.ofHyps hyps) A) : CandidateResult :=
  match fuel with
  | 0 => .exhausted .saturate
  | fuel + 1 =>
    match t, u with
    | .unit, .unit => .equal
    | .abort n, .abort m =>
        if NegNeu.toRaw n == NegNeu.toRaw m then .equal else .different
    | .pair t₁ t₂, .pair u₁ u₂ =>
        (compareInvRec fuel hyps goal t₁ u₁).and
          (compareInvRec fuel hyps goal t₂ u₂)
    | .lam (A := B) t₁, .lam u₁ =>
        let hyps' := hyps.push B
        have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ B :=
          Ctx.ofHyps_push hyps B
        let Γ' : ReachCtx sig.nBases := ⟨hyps', hyps.size⟩
        compareSatRec fuel Γ' goal
          (InvTm.castCtx hctx.symm t₁)
          (InvTm.castCtx hctx.symm u₁)
    | .case (A := L) (B := R) n t₁ t₂, .case (A := L') (B := R') m u₁ u₂ =>
        if NegNeu.toRaw n != NegNeu.toRaw m then .different
        else if hL : L = L' then
          if hR : R = R' then
            let hypsL := hyps.push L
            let hypsR := hyps.push R
            have hxL : Ctx.ofHyps hypsL = Ctx.ofHyps hyps ▻ L :=
              Ctx.ofHyps_push hyps L
            have hxR : Ctx.ofHyps hypsR = Ctx.ofHyps hyps ▻ R :=
              Ctx.ofHyps_push hyps R
            let ΓL : ReachCtx sig.nBases := ⟨hypsL, hyps.size⟩
            let ΓR : ReachCtx sig.nBases := ⟨hypsR, hyps.size⟩
            let u₁' : InvTm (Ctx.ofHyps hyps ▻ L) A :=
              hL ▸ u₁
            let u₂' : InvTm (Ctx.ofHyps hyps ▻ R) A :=
              hR ▸ u₂
            (compareSatRec fuel ΓL goal
                (InvTm.castCtx hxL.symm t₁)
                (InvTm.castCtx hxL.symm u₁')).and
              (compareSatRec fuel ΓR goal
                (InvTm.castCtx hxR.symm t₂)
                (InvTm.castCtx hxR.symm u₂'))
          else .different
        else .different
    | .foc (.letPos (P := P) n t₁), .foc (.letPos (P := P') m u₁) =>
        if NegNeu.toRaw n != NegNeu.toRaw m then .different
        else if hP : P = P' then
          let hyps' := hyps.push P
          have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ P :=
            Ctx.ofHyps_push hyps P
          let Γ' : ReachCtx sig.nBases := ⟨hyps', hyps.size⟩
          let u₁' : InvTm (Ctx.ofHyps hyps ▻ P) A := hP ▸ u₁
          compareSatRec fuel Γ' goal
            (InvTm.castCtx hctx.symm t₁)
            (InvTm.castCtx hctx.symm u₁')
        else .different
    | .foc (.pos (.done p)), .foc (.pos (.done q)) =>
        if PosNeu.toRaw p == PosNeu.toRaw q then .equal else .different
    | .foc (.neg (.done n)), .foc (.neg (.done m)) =>
        if NegNeu.toRaw n == NegNeu.toRaw m then .equal else .different
    | .foc (.sat (.mk _ t₁)), .foc (.sat (.mk _ u₁)) =>
        compareInvRec fuel hyps goal t₁ u₁
    | _, _ =>
        if structurallyEqual t u then .equal else .different
end

/-- Compare two already-focused invertible terms under a shared reachability context. -/
def compareInv {A : Object sig.nBases}
    (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases)
    (t u : InvTm (Ctx.ofHyps Γ.hyps) A) (fuel : Nat := 2048) : CandidateResult :=
  compareSatRec fuel Γ goal t u

/-- Compare two focused terms under an arbitrary snoc context (all hyps new). -/
def compareUnder {A : Object sig.nBases}
    (Γ : Ctx sig) (goal : Object sig.nBases)
    (t u : InvTm Γ A) (fuel : Nat := 2048) : CandidateResult :=
  let r := Γ.toReachCtx
  have hctx : Ctx.ofHyps r.hyps = Γ := Ctx.ofHyps_toReachCtx Γ
  compareSatRec fuel r goal
    (InvTm.castCtx hctx.symm t)
    (InvTm.castCtx hctx.symm u)

/--
Compare focused terms under `Γgen , x : X` with generators old and `x` new.
-/
def compareUnderMorphism {X A : Object sig.nBases}
    (goal : Object sig.nBases)
    (t u : InvTm (translateCtx X) A) (fuel : Nat := 2048) : CandidateResult :=
  let r := morphismReachCtx (sig := sig) X
  have hctx : Ctx.ofHyps r.hyps = translateCtx X := morphismReachCtx_ofHyps X
  compareSatRec fuel r goal
    (InvTm.castCtx hctx.symm t)
    (InvTm.castCtx hctx.symm u)

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

Uses `morphismReachCtx`: `Γgen` is old, the source binder is new.
-/
def compareIntrinsic {X Y : Object sig.nBases}
    (f g : IntrinsicMorphism sig X Y) (fuel : Nat := 2048) : CandidateResult :=
  match focusInv fuel (translate f), focusInv fuel (translate g) with
  | .exhausted, _ | _, .exhausted => .exhausted .focus
  | .ok t', .ok u' => compareUnderMorphism (goal := Y) t' u' (fuel := fuel)

end Equality
end Gimbal
