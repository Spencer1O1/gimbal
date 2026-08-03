/-
  Valid encode fragment for ordered-phase codes (Milestone 8F design E).

  Encoding is not required on arbitrary `InvTm`. The reference comparator only
  feeds encode terms that have completed a shared-schedule saturation phase
  under a phase-entry origin environment. This module names that fragment and
  records that the reference pipeline produces it.

  `ReferenceScheduleOk` is purely operational (`pairObs` / `applyPairObs`).
  `canonicalize` may wrap the result as proved-sound ICC preprocessing; it is
  not part of the encode characterization and must not be assumed complete or
  idempotent when proving `EncodeTotal` or code uniqueness.
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

/--
Operational shared-schedule saturation: `pairObs` built a schedule and
`applyPairObs` returned `t'`. No appeal to code equality, canonicalize
completeness, or unique NF.
-/
def ReferenceScheduleOk {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
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
Reference-produced term ready for encode/compare.

`t` is either the raw `applyPairObs` result or its `canonicalize` image.
Canonicalize is allowed only as proved-sound preprocessing
(`wellInv_canonicalize`, `tmEq_canonicalize`); `EncodeTotal` and code
uniqueness must not assume its completeness or idempotence.
-/
def ReferenceSaturated {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  ∃ t' : InvTm (Ctx.ofHyps hyps) A,
    ReferenceScheduleOk t' ∧ (t = t' ∨ t = canonicalize t')

/--
Concrete valid fragment for `encodeICC` / `EncodeTotal`.

Exactly the invariants encoding needs on reference-produced terms:

* **phase** — lives in a `Ctx.ofHyps` phase context (in the type)
* **scoping** — `WellInv` (focused invertible fragment)
* **saturation** — `ReferenceSaturated` (operational schedule success ± sound canonicalize)
* **origin environment** — phase-entry `OriginEnv.ofHyps`
-/
structure ValidEncodeFragment {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (t : InvTm (Ctx.ofHyps hyps) A) : Prop where
  well : WellInv t
  saturated : ReferenceSaturated t

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

/-! ### Reference pipeline produces the fragment -/

/--
One reference phase saturating the left subject yields a `ValidEncodeFragment`
(after sound canonicalize preprocessing, as in `referenceSatRec`).
-/
theorem validEncodeFragment_referencePhase (fuel : Nat) {Γ : ReachCtx sig.nBases}
    {goal A : Object sig.nBases} {t u : InvTm (Ctx.ofHyps Γ.hyps) A}
    {entries : Array (PairEntry sig Γ.hyps)} {σ : ReachState sig.nBases}
    {t' : InvTm (Ctx.ofHyps Γ.hyps) A}
    (hinv : checkOldInvariant Γ.oldPrefix goal = true)
    (ht : WellInv t) (hu : WellInv u)
    (hobs : pairObs Γ goal t u = .ok entries σ)
    (h : applyPairObs (saturationBudget fuel entries.size) σ Γ.hyps entries t =
      .ok t') :
    ValidEncodeFragment (canonicalize t') := by
  refine ⟨wellInv_referencePhase (saturationBudget fuel entries.size) ht hu hobs h, ?_⟩
  refine ⟨t', ⟨Γ.newFrom, goal, fuel, entries, σ, t, u, ?_, ht, hu, ?_, Or.inl h⟩, Or.inr rfl⟩
  · cases Γ; exact hinv
  · cases Γ; exact hobs

/-- Raw saturate result (no canonicalize) is also a valid fragment. -/
theorem validEncodeFragment_scheduleOk {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t' : InvTm (Ctx.ofHyps hyps) A}
    (hw : WellInv t') (hs : ReferenceScheduleOk t') :
    ValidEncodeFragment t' :=
  ⟨hw, ⟨t', hs, Or.inl rfl⟩⟩

/--
One reference phase saturating the right subject yields a `ValidEncodeFragment`.
-/
theorem validEncodeFragment_referencePhase_right (fuel : Nat)
    {Γ : ReachCtx sig.nBases} {goal A : Object sig.nBases}
    {t u : InvTm (Ctx.ofHyps Γ.hyps) A}
    {entries : Array (PairEntry sig Γ.hyps)} {σ : ReachState sig.nBases}
    {u' : InvTm (Ctx.ofHyps Γ.hyps) A}
    (hinv : checkOldInvariant Γ.oldPrefix goal = true)
    (ht : WellInv t) (hu : WellInv u)
    (hobs : pairObs Γ goal t u = .ok entries σ)
    (h : applyPairObs (saturationBudget fuel entries.size) σ Γ.hyps entries u =
      .ok u') :
    ValidEncodeFragment (canonicalize u') := by
  refine ⟨wellInv_canonicalize
      (wellInv_saturate_pairObs (saturationBudget fuel entries.size) ht hu hobs hu h), ?_⟩
  refine ⟨u', ⟨Γ.newFrom, goal, fuel, entries, σ, t, u, ?_, ht, hu, ?_, Or.inr h⟩, Or.inr rfl⟩
  · cases Γ; exact hinv
  · cases Γ; exact hobs
