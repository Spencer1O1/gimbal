/-
  Valid encode fragment for ordered-phase codes (Milestone 8F design E).

  Encoding is not required on arbitrary `InvTm`. The reference comparator only
  feeds encode terms that have completed a shared-schedule saturation phase
  under a phase-entry origin environment.

  Two production notions are kept visibly separate:

  * `RawReferenceProduced` — only operational evidence (`pairObs` /
    `applyPairObs`, with well-focused continuations and the old-invariant
    check). No `EncodeReady`.
  * `CertifiedReferenceProduced` — raw production plus `PhaseEncodeReady`.

  The required bridge is `RawReferenceProduced → PhaseEncodeReady` (equivalently
  raw → certified). Until that lands, `ValidEncodeFragment` may still stash
  readiness; `EncodeTotal_holds` that projects the stash is **provisional** and
  must not drive `referenceCompare` / characterization.

  `canonicalize` remains on the compare path only; it is not part of encode
  characterization.
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
Operational shared-schedule saturation only: `pairObs` built a schedule and
`applyPairObs` returned `t'`. Continuations are well-focused; **no**
`EncodeReady` is stored here.
-/
def RawReferenceProduced {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t' : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  ∃ (newFrom : Nat) (goal : Object sig.nBases) (fuel : Nat)
      (entries : Array (PairEntry sig hyps)) (σ : ReachState sig.nBases)
      (t₀ u₀ : InvTm (Ctx.ofHyps hyps) A),
    checkOldInvariant (ReachCtx.oldPrefix ⟨hyps, newFrom⟩) goal = true ∧
      WellInv t₀ ∧
      WellInv u₀ ∧
      pairObs ⟨hyps, newFrom⟩ goal t₀ u₀ = .ok entries σ ∧
      (applyPairObs (saturationBudget fuel entries.size) σ hyps entries t₀ = .ok t' ∨
        applyPairObs (saturationBudget fuel entries.size) σ hyps entries u₀ = .ok t')

/--
Raw production plus encode alignment of the schedule result.
Inhabited from `RawReferenceProduced` once the readiness loop closes.
-/
def CertifiedReferenceProduced {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (t : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  RawReferenceProduced t ∧ PhaseEncodeReady t

/--
Historical name for the operational schedule certificate (raw only).
Prefer `RawReferenceProduced` in new proofs.
-/
abbrev ReferenceScheduleOk {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t' : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  RawReferenceProduced t'

/-- Alias used by older notes: raw schedule production. -/
abbrev ReferenceProduced {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  RawReferenceProduced t

/-- Historical alias. -/
abbrev ReferenceSaturated {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  RawReferenceProduced t

/--
Concrete valid fragment for `encodeICC` / provisional `EncodeTotal`.

* **phase** — `Ctx.ofHyps` (in the type)
* **scoping** — `WellInv`
* **raw production** — `RawReferenceProduced`
* **readiness** — `PhaseEncodeReady` (**provisional stash**; must be derived by
  `RawReferenceProduced → PhaseEncodeReady` before final totality)

Final fragment should be `well` + `CertifiedReferenceProduced` with no separate
`ready` field.
-/
structure ValidEncodeFragment {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (t : InvTm (Ctx.ofHyps hyps) A) : Prop where
  well : WellInv t
  raw : RawReferenceProduced t
  ready : PhaseEncodeReady t

/-- Certified view of a (provisional) valid fragment. -/
theorem ValidEncodeFragment.certified {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps) A}
    (h : ValidEncodeFragment t) : CertifiedReferenceProduced t :=
  ⟨h.raw, h.ready⟩

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
  h.raw

/-- Package once readiness of `t'` is known (provisional; prefer certify). -/
theorem validEncodeFragment_mk {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t' : InvTm (Ctx.ofHyps hyps) A}
    (hw : WellInv t') (hr : RawReferenceProduced t') (hready : PhaseEncodeReady t') :
    ValidEncodeFragment t' :=
  ⟨hw, hr, hready⟩

/-- From a certified production witness. -/
theorem validEncodeFragment_of_certified {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps) A}
    (hw : WellInv t) (hc : CertifiedReferenceProduced t) :
    ValidEncodeFragment t :=
  ⟨hw, hc.1, hc.2⟩

/-! ### Reference pipeline produces raw / provisional certified fragments -/

/--
Raw certificate for one left-saturating reference phase (no readiness).
-/
theorem rawReferenceProduced_referencePhase (fuel : Nat) {Γ : ReachCtx sig.nBases}
    {goal A : Object sig.nBases} {t u : InvTm (Ctx.ofHyps Γ.hyps) A}
    {entries : Array (PairEntry sig Γ.hyps)} {σ : ReachState sig.nBases}
    {t' : InvTm (Ctx.ofHyps Γ.hyps) A}
    (hinv : checkOldInvariant Γ.oldPrefix goal = true)
    (ht : WellInv t) (hu : WellInv u)
    (hobs : pairObs Γ goal t u = .ok entries σ)
    (h : applyPairObs (saturationBudget fuel entries.size) σ Γ.hyps entries t =
      .ok t') :
    RawReferenceProduced t' :=
  ⟨Γ.newFrom, goal, fuel, entries, σ, t, u, hinv, ht, hu, hobs, Or.inl h⟩

/--
Provisional: left phase with an explicit readiness proof of `t'`.
Replace `hready'` by `encodeReady_of_rawReferenceProduced` once the loop closes.
-/
theorem validEncodeFragment_referencePhase (fuel : Nat) {Γ : ReachCtx sig.nBases}
    {goal A : Object sig.nBases} {t u : InvTm (Ctx.ofHyps Γ.hyps) A}
    {entries : Array (PairEntry sig Γ.hyps)} {σ : ReachState sig.nBases}
    {t' : InvTm (Ctx.ofHyps Γ.hyps) A}
    (hinv : checkOldInvariant Γ.oldPrefix goal = true)
    (ht : WellInv t) (hu : WellInv u)
    (hobs : pairObs Γ goal t u = .ok entries σ)
    (h : applyPairObs (saturationBudget fuel entries.size) σ Γ.hyps entries t =
      .ok t')
    (hready' : PhaseEncodeReady t') :
    ValidEncodeFragment t' :=
  validEncodeFragment_mk
    (wellInv_saturate_pairObs (saturationBudget fuel entries.size) ht hu hobs ht h)
    (rawReferenceProduced_referencePhase fuel hinv ht hu hobs h)
    hready'

/-- Raw saturate result packaged with an explicit readiness proof. -/
theorem validEncodeFragment_scheduleOk {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t' : InvTm (Ctx.ofHyps hyps) A}
    (hw : WellInv t') (hr : RawReferenceProduced t') (hready : PhaseEncodeReady t') :
    ValidEncodeFragment t' :=
  validEncodeFragment_mk hw hr hready

/--
Raw certificate for one right-saturating reference phase.
-/
theorem rawReferenceProduced_referencePhase_right (fuel : Nat)
    {Γ : ReachCtx sig.nBases} {goal A : Object sig.nBases}
    {t u : InvTm (Ctx.ofHyps Γ.hyps) A}
    {entries : Array (PairEntry sig Γ.hyps)} {σ : ReachState sig.nBases}
    {u' : InvTm (Ctx.ofHyps Γ.hyps) A}
    (hinv : checkOldInvariant Γ.oldPrefix goal = true)
    (ht : WellInv t) (hu : WellInv u)
    (hobs : pairObs Γ goal t u = .ok entries σ)
    (h : applyPairObs (saturationBudget fuel entries.size) σ Γ.hyps entries u =
      .ok u') :
    RawReferenceProduced u' :=
  ⟨Γ.newFrom, goal, fuel, entries, σ, t, u, hinv, ht, hu, hobs, Or.inr h⟩

/-- Provisional right-phase packaging with stashed readiness of `u'`. -/
theorem validEncodeFragment_referencePhase_right (fuel : Nat)
    {Γ : ReachCtx sig.nBases} {goal A : Object sig.nBases}
    {t u : InvTm (Ctx.ofHyps Γ.hyps) A}
    {entries : Array (PairEntry sig Γ.hyps)} {σ : ReachState sig.nBases}
    {u' : InvTm (Ctx.ofHyps Γ.hyps) A}
    (hinv : checkOldInvariant Γ.oldPrefix goal = true)
    (ht : WellInv t) (hu : WellInv u)
    (hobs : pairObs Γ goal t u = .ok entries σ)
    (h : applyPairObs (saturationBudget fuel entries.size) σ Γ.hyps entries u =
      .ok u')
    (hready' : PhaseEncodeReady u') :
    ValidEncodeFragment u' :=
  validEncodeFragment_mk
    (wellInv_saturate_pairObs (saturationBudget fuel entries.size) ht hu hobs hu h)
    (rawReferenceProduced_referencePhase_right fuel hinv ht hu hobs h)
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
