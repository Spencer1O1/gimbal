/-
  Reference equality pipeline (Milestone 8).

  Constructs complete saturated forms for both inputs under one shared
  admissible schedule, ICC-canonicalizes, then compares structural spines.
  This is the proof-facing decision procedure (Scherer-style). The on-the-fly
  `compareSatRec` in `Compare.lean` remains a private optimization candidate.
-/

import Gimbal.Equality.Focus
import Gimbal.Equality.ICC
import Gimbal.Equality.Saturation
import Gimbal.Equality.Translate
import Gimbal.Equality.Compare

namespace Gimbal
namespace Equality

variable {sig : Signature}

/--
Structural equality of ICC-canonical spines (sat metadata already erased).

Typed rather than raw: `InvTm.eq_of_beq` turns a successful comparison into an
equality of terms, which is what the soundness proof consumes.
-/
def referenceStructEq {Γ : Ctx sig} {A : Object sig.nBases}
    (t u : InvTm Γ A) : Bool :=
  InvTm.beq (canonicalize t) (canonicalize u)

/--
Budget handed to the saturation stage.

Applying a schedule costs two units per entry, so `2 * entries + 1` is enough
for the observation loop itself (`applyPairObs_ne_exhausted`); the ambient fuel
is kept as a floor because witness reconstruction inside the loop still spends
from the same counter.
-/
def saturationBudget (fuel entries : Nat) : Nat :=
  max fuel (2 * entries + 1)

theorem lt_saturationBudget (fuel entries : Nat) :
    2 * entries < saturationBudget fuel entries :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)

mutual
/--
Fully saturate `t` under reflexive pair-obs (complete form, no comparison).
Used to build reference normal forms under binders.
-/
def completeSatRec (fuel : Nat) (Γ : ReachCtx sig.nBases)
    (goal : Object sig.nBases) {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps Γ.hyps) A) :
    SaturateResult (Ctx.ofHyps Γ.hyps) A :=
  match fuel with
  | 0 => .exhausted
  | fuel + 1 =>
    if !checkOldInvariant Γ.oldPrefix goal then .invariantFailure
    else
      match pairObs Γ goal t t with
      | .invariantFailure => .invariantFailure
      | .ok entries c =>
        match applyPairObs (saturationBudget fuel entries.size) c.cert Γ.hyps entries t with
        | .exhausted => .exhausted
        | .invariantFailure => .invariantFailure
        | .ok t' =>
            completeInvRec fuel Γ.hyps goal (canonicalize t')

/-- Descend invertible structure, re-saturating under each new binder. -/
def completeInvRec (fuel : Nat) (hyps : Array (Object sig.nBases))
    (goal : Object sig.nBases) {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A) :
    SaturateResult (Ctx.ofHyps hyps) A :=
  match fuel with
  | 0 => .exhausted
  | fuel + 1 =>
    match t with
    | .unit => .ok .unit
    | .abort n => .ok (.abort n)
    | .pair t₁ t₂ =>
        match completeInvRec fuel hyps goal t₁,
              completeInvRec fuel hyps goal t₂ with
        | .ok t₁', .ok t₂' => .ok (.pair t₁' t₂')
        | .exhausted, _ | _, .exhausted => .exhausted
        | .invariantFailure, _ | _, .invariantFailure => .invariantFailure
    | .lam (A := B) t₁ =>
        let hyps' := hyps.push B
        have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ B :=
          Ctx.ofHyps_push hyps B
        let Γ' : ReachCtx sig.nBases := ⟨hyps', hyps.size⟩
        match completeSatRec fuel Γ' goal (InvTm.castCtx hctx.symm t₁) with
        | .ok body' => .ok (.lam (InvTm.castCtx hctx body'))
        | .exhausted => .exhausted
        | .invariantFailure => .invariantFailure
    | .case (A := L) (B := R) n t₁ t₂ =>
        let hypsL := hyps.push L
        let hypsR := hyps.push R
        have hxL : Ctx.ofHyps hypsL = Ctx.ofHyps hyps ▻ L :=
          Ctx.ofHyps_push hyps L
        have hxR : Ctx.ofHyps hypsR = Ctx.ofHyps hyps ▻ R :=
          Ctx.ofHyps_push hyps R
        let ΓL : ReachCtx sig.nBases := ⟨hypsL, hyps.size⟩
        let ΓR : ReachCtx sig.nBases := ⟨hypsR, hyps.size⟩
        match completeSatRec fuel ΓL goal (InvTm.castCtx hxL.symm t₁),
              completeSatRec fuel ΓR goal (InvTm.castCtx hxR.symm t₂) with
        | .ok t₁', .ok t₂' =>
            .ok (.case n (InvTm.castCtx hxL t₁') (InvTm.castCtx hxR t₂'))
        | .exhausted, _ | _, .exhausted => .exhausted
        | .invariantFailure, _ | _, .invariantFailure => .invariantFailure
    | .foc (.letPos (P := P) n t₁) =>
        let hyps' := hyps.push P
        have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ P :=
          Ctx.ofHyps_push hyps P
        let Γ' : ReachCtx sig.nBases := ⟨hyps', hyps.size⟩
        match completeSatRec fuel Γ' goal (InvTm.castCtx hctx.symm t₁) with
        | .ok body' =>
            .ok (.foc (.letPos n (InvTm.castCtx hctx body')))
        | .exhausted => .exhausted
        | .invariantFailure => .invariantFailure
    | .foc (.sat (.mk _ t₁)) =>
        completeInvRec fuel hyps goal t₁
    | .foc f =>
        .ok (.foc f)
end

mutual
/--
Reference phase: shared schedule → saturate both → ICC → lockstep compare,
re-entering under binders with a fresh shared schedule.
-/
def referenceSatRec (fuel : Nat) (Γ : ReachCtx sig.nBases)
    (goal : Object sig.nBases) {A : Object sig.nBases}
    (t u : InvTm (Ctx.ofHyps Γ.hyps) A) : CandidateResult :=
  match fuel with
  | 0 => .exhausted .saturate
  | fuel + 1 =>
    if !checkOldInvariant Γ.oldPrefix goal then .invariantFailure
    else
      match pairObs Γ goal t u with
      | .invariantFailure => .invariantFailure
      | .ok entries c =>
        match applyPairObs (saturationBudget fuel entries.size) c.cert Γ.hyps entries t,
              applyPairObs (saturationBudget fuel entries.size) c.cert Γ.hyps entries u with
        | .exhausted, _ | _, .exhausted => .exhausted .saturate
        | .invariantFailure, _ | _, .invariantFailure => .invariantFailure
        | .ok t', .ok u' =>
            referenceInvRec fuel Γ.hyps goal
              (canonicalize t')
              (canonicalize u')

/-- Lockstep comparison of completed phase results. -/
def referenceInvRec (fuel : Nat) (hyps : Array (Object sig.nBases))
    (goal : Object sig.nBases) {A : Object sig.nBases}
    (t u : InvTm (Ctx.ofHyps hyps) A) : CandidateResult :=
  match fuel with
  | 0 => .exhausted .saturate
  | fuel + 1 =>
    match t, u with
    | .unit, .unit => .equal
    | .abort _, .abort _ =>
        -- `never` is initial: any two terms under a proof of it are equal.
        .equal
    | .pair t₁ t₂, .pair u₁ u₂ =>
        (referenceInvRec fuel hyps goal t₁ u₁).and
          (referenceInvRec fuel hyps goal t₂ u₂)
    | .lam (A := B) t₁, .lam u₁ =>
        let hyps' := hyps.push B
        have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ B :=
          Ctx.ofHyps_push hyps B
        let Γ' : ReachCtx sig.nBases := ⟨hyps', hyps.size⟩
        referenceSatRec fuel Γ' goal
          (InvTm.castCtx hctx.symm t₁)
          (InvTm.castCtx hctx.symm u₁)
    | .case (A := L) (B := R) n t₁ t₂, .case (A := L') (B := R') m u₁ u₂ =>
        if !NegNeu.beq n m then .different
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
            let u₁' : InvTm (Ctx.ofHyps hyps ▻ L) A := hL ▸ u₁
            let u₂' : InvTm (Ctx.ofHyps hyps ▻ R) A := hR ▸ u₂
            (referenceSatRec fuel ΓL goal
                (InvTm.castCtx hxL.symm t₁)
                (InvTm.castCtx hxL.symm u₁')).and
              (referenceSatRec fuel ΓR goal
                (InvTm.castCtx hxR.symm t₂)
                (InvTm.castCtx hxR.symm u₂'))
          else .different
        else .different
    | .foc (.letPos (P := P) n t₁), .foc (.letPos (P := P') m u₁) =>
        if !NegNeu.beq n m then .different
        else if hP : P = P' then
          let hyps' := hyps.push P
          have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ P :=
            Ctx.ofHyps_push hyps P
          let Γ' : ReachCtx sig.nBases := ⟨hyps', hyps.size⟩
          let u₁' : InvTm (Ctx.ofHyps hyps ▻ P) A := hP ▸ u₁
          referenceSatRec fuel Γ' goal
            (InvTm.castCtx hctx.symm t₁)
            (InvTm.castCtx hctx.symm u₁')
        else .different
    | .foc (.pos (.done p)), .foc (.pos (.done q)) =>
        if PosNeu.beq p q then .equal else .different
    | .foc (.neg (.done n)), .foc (.neg (.done m)) =>
        if NegNeu.beq n m then .equal else .different
    | .foc (.sat (.mk _ t₁)), .foc (.sat (.mk _ u₁)) =>
        referenceInvRec fuel hyps goal t₁ u₁
    | _, _ =>
        if referenceStructEq t u then .equal else .different
end

/-- Reference compare on already-focused terms. -/
def referenceCompareInv {A : Object sig.nBases}
    (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases)
    (t u : InvTm (Ctx.ofHyps Γ.hyps) A) (fuel : Nat := 2048) : CandidateResult :=
  referenceSatRec fuel Γ goal t u

/-- Reference compare under an arbitrary snoc context (root wholly new). -/
def referenceCompareUnder {A : Object sig.nBases}
    (Γ : Ctx sig) (goal : Object sig.nBases)
    (t u : InvTm Γ A) (fuel : Nat := 2048) : CandidateResult :=
  let r := Γ.toReachCtx
  have hctx : Ctx.ofHyps r.hyps = Γ := Ctx.ofHyps_toReachCtx Γ
  referenceSatRec fuel r goal
    (InvTm.castCtx hctx.symm t)
    (InvTm.castCtx hctx.symm u)

/-- Focus then reference-compare ordinary terms. -/
def referenceCompareTm {Γ : Ctx sig} {A : Object sig.nBases}
    (goal : Object sig.nBases) (t u : Tm Γ A) (fuel : Nat := 2048) :
    CandidateResult :=
  referenceCompareUnder Γ goal (focus t) (focus u) (fuel := fuel)

/--
Reference comparator on intrinsic morphisms.
Proof target for Milestone 8G (`↔ DefEq`); the remaining fuel is for
saturation and ICC, which still need well-founded measures.
-/
def referenceCompare {X Y : Object sig.nBases}
    (f g : IntrinsicMorphism sig X Y) (fuel : Nat := 2048) : CandidateResult :=
  referenceCompareTm (goal := Y) (translate f) (translate g) (fuel := fuel)

end Equality
end Gimbal
