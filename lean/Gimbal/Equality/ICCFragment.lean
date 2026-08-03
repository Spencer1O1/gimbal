/-
  Valid encode fragment for ordered-phase codes (Milestone 8F design E).

  Encoding is not required on arbitrary `InvTm`. The reference comparator only
  feeds encode terms that have completed a shared-schedule saturation phase
  under a phase-entry origin environment. This module names that fragment and
  records that the reference pipeline produces it.

  `ReferenceScheduleOk` / `ReferenceProduced` are operational
  (`pairObs` / `applyPairObs` on the **raw** saturate result) plus phase-entry
  `EncodeReady` of the pre-schedule continuations. Successful schedule
  application preserves readiness (`encodeReady_applyPairObs` in `ICCTotal`).
  `canonicalize` remains in `referenceCompare` wiring; it is not part of the
  encode characterization.
-/

import Gimbal.Equality.ICCCode
import Gimbal.Equality.ICCWell
import Gimbal.Equality.Reference
import Gimbal.Equality.ReferenceWell
import Gimbal.Equality.SatWell

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Valid fragment -/

/--
Phase-entry origin environment adequacy: encoding of a `Ctx.ofHyps` term uses
`OriginEnv.ofHyps` (oldest-first `hyp` indices). Binder re-entry under λ / case
/ `letPos` rebuilds the same shape on the extended hyp array.
-/
def AdequateOriginEnv (hyps : Array (Object sig.nBases))
    (ε : OriginEnv (Ctx.ofHyps hyps)) : Prop :=
  ∀ {A : Object sig.nBases} (x : Var (Ctx.ofHyps hyps) A),
    ε x = OriginEnv.ofHyps hyps x

/-- Phase-entry `EncodeReady` under `ofHyps`. -/
def PhaseEncodeReady {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  EncodeReady (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))
    (OriginEnv.ofHyps hyps) 0 0 t

/--
Operational shared-schedule saturation: `pairObs` built a schedule,
`applyPairObs` returned `t'`, and both pre-schedule continuations are
phase-entry encode-ready (so schedule preservation can lift readiness to `t'`).
-/
def ReferenceScheduleOk {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t' : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  ∃ (newFrom : Nat) (goal : Object sig.nBases) (fuel : Nat)
      (entries : Array (PairEntry sig hyps)) (σ : ReachState sig.nBases)
      (t₀ u₀ : InvTm (Ctx.ofHyps hyps) A),
    checkOldInvariant (ReachCtx.oldPrefix ⟨hyps, newFrom⟩) goal = true ∧
      WellInv t₀ ∧
      WellInv u₀ ∧
      PhaseEncodeReady t₀ ∧
      PhaseEncodeReady u₀ ∧
      pairObs ⟨hyps, newFrom⟩ goal t₀ u₀ = .ok entries σ ∧
      (applyPairObs (saturationBudget fuel entries.size) σ hyps entries t₀ = .ok t' ∨
        applyPairObs (saturationBudget fuel entries.size) σ hyps entries u₀ = .ok t')

/--
Ready-to-encode production certificate: schedule success with ready
continuations. Prefer raw `applyPairObs` over a canonicalize image.
-/
def ReferenceProduced {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  ReferenceScheduleOk t

/-- Historical alias. -/
abbrev ReferenceSaturated {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  ReferenceProduced t

/--
Concrete valid fragment for `encodeICC` / `EncodeTotal`.

* **phase** — `Ctx.ofHyps` (in the type)
* **scoping** — `WellInv`
* **saturation** — `ReferenceProduced` (schedule + ready conts)
* **readiness** — `PhaseEncodeReady` on the schedule result (encode alignment)
-/
structure ValidEncodeFragment {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (t : InvTm (Ctx.ofHyps hyps) A) : Prop where
  well : WellInv t
  produced : ReferenceProduced t
  ready : PhaseEncodeReady t

/-- Phase-entry environment used to encode a valid-fragment term. -/
def ValidEncodeFragment.originEnv {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps) A}
    (_ : ValidEncodeFragment t) : OriginEnv (Ctx.ofHyps hyps) :=
  OriginEnv.ofHyps hyps

theorem ValidEncodeFragment.adequate {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps) A}
    (h : ValidEncodeFragment t) :
    AdequateOriginEnv hyps h.originEnv := by
  intro _ _; rfl

theorem ValidEncodeFragment.saturated {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps) A}
    (h : ValidEncodeFragment t) : ReferenceSaturated t :=
  h.produced

/-! ### Reference pipeline produces the fragment -/

/--
Package a schedule result once readiness of `t'` is known (from
`encodeReady_applyPairObs` once conts are phase-ready).
-/
theorem validEncodeFragment_mk {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t' : InvTm (Ctx.ofHyps hyps) A}
    (hw : WellInv t') (hs : ReferenceScheduleOk t') (hr : PhaseEncodeReady t') :
    ValidEncodeFragment t' :=
  ⟨hw, hs, hr⟩

/--
One reference phase saturating the left subject, given phase-ready inputs and
a proved-ready saturate result.
-/
theorem validEncodeFragment_referencePhase (fuel : Nat) {Γ : ReachCtx sig.nBases}
    {goal A : Object sig.nBases} {t u : InvTm (Ctx.ofHyps Γ.hyps) A}
    {entries : Array (PairEntry sig Γ.hyps)} {σ : ReachState sig.nBases}
    {t' : InvTm (Ctx.ofHyps Γ.hyps) A}
    (hinv : checkOldInvariant Γ.oldPrefix goal = true)
    (ht : WellInv t) (hu : WellInv u)
    (hreadyt : PhaseEncodeReady t) (hreadyu : PhaseEncodeReady u)
    (hobs : pairObs Γ goal t u = .ok entries σ)
    (h : applyPairObs (saturationBudget fuel entries.size) σ Γ.hyps entries t =
      .ok t')
    (hready' : PhaseEncodeReady t') :
    ValidEncodeFragment t' :=
  validEncodeFragment_mk
    (wellInv_saturate_pairObs (saturationBudget fuel entries.size) ht hu hobs ht h)
    ⟨Γ.newFrom, goal, fuel, entries, σ, t, u, hinv, ht, hu, hreadyt, hreadyu, hobs,
      Or.inl h⟩
    hready'

/-- Raw saturate result with readiness is a valid fragment. -/
theorem validEncodeFragment_scheduleOk {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t' : InvTm (Ctx.ofHyps hyps) A}
    (hw : WellInv t') (hs : ReferenceScheduleOk t') (hr : PhaseEncodeReady t') :
    ValidEncodeFragment t' :=
  validEncodeFragment_mk hw hs hr

/--
One reference phase saturating the right subject, given phase-ready inputs and
a proved-ready saturate result.
-/
theorem validEncodeFragment_referencePhase_right (fuel : Nat)
    {Γ : ReachCtx sig.nBases} {goal A : Object sig.nBases}
    {t u : InvTm (Ctx.ofHyps Γ.hyps) A}
    {entries : Array (PairEntry sig Γ.hyps)} {σ : ReachState sig.nBases}
    {u' : InvTm (Ctx.ofHyps Γ.hyps) A}
    (hinv : checkOldInvariant Γ.oldPrefix goal = true)
    (ht : WellInv t) (hu : WellInv u)
    (hreadyt : PhaseEncodeReady t) (hreadyu : PhaseEncodeReady u)
    (hobs : pairObs Γ goal t u = .ok entries σ)
    (h : applyPairObs (saturationBudget fuel entries.size) σ Γ.hyps entries u =
      .ok u')
    (hready' : PhaseEncodeReady u') :
    ValidEncodeFragment u' :=
  validEncodeFragment_mk
    (wellInv_saturate_pairObs (saturationBudget fuel entries.size) ht hu hobs hu h)
    ⟨Γ.newFrom, goal, fuel, entries, σ, t, u, hinv, ht, hu, hreadyt, hreadyu, hobs,
      Or.inr h⟩
    hready'

/-- Canonicalize image of a schedule result remains well-focused (compare path). -/
theorem wellInv_canonicalize_referencePhase (fuel : Nat) {Γ : ReachCtx sig.nBases}
    {goal A : Object sig.nBases} {t u : InvTm (Ctx.ofHyps Γ.hyps) A}
    {entries : Array (PairEntry sig Γ.hyps)} {σ : ReachState sig.nBases}
    {t' : InvTm (Ctx.ofHyps Γ.hyps) A}
    (ht : WellInv t) (hu : WellInv u)
    (hobs : pairObs Γ goal t u = .ok entries σ)
    (h : applyPairObs (saturationBudget fuel entries.size) σ Γ.hyps entries t =
      .ok t') :
    WellInv (canonicalize t') :=
  wellInv_referencePhase (saturationBudget fuel entries.size) ht hu hobs h

end Equality
end Gimbal
