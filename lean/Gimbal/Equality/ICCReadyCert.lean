/-
  Milestone 8F readiness certificate spike (induction-boundary correction).

  Status: **design spike only**. Enumeration of Raw→EncodeReady via
  `AtomDerivedContShape` / `CoprodDerivedContShape` / nil-rest disjunctions is
  **paused** (green checkpoint `192dae5` kept). This module does not switch
  `referenceCompare`, does not drop `ValidEncodeFragment.ready`, and does not
  use provisional `EncodeTotal_holds`.

  Diagnosis
  ---------
  `RawReferenceProduced` stores evaluator equations (`pairObs` / `applyPairObs`)
  and `WellInv` of the pre-saturation continuations, but not the derivation that
  built those continuations. Empty schedule exposes the gap:

      applyPairObsGo (fuel+1) σ hyps [] cont = .ok cont

  so schedule success + `WellInv cont` cannot invent `EncodeReady cont`.
  Readiness of `cont` must be produced by the focusing / intro phase that
  constructed it; schedule application can only **preserve** it.

  Split
  -----
  1. **Preservation** — proof-relevant `ApplyPairObsReadyCert`: schedule steps
     transport a stage readiness certificate from the input continuation to the
     saturated result (compositional in entries; no result-shape predicates).
  2. **Production** — `ContReadyCert` (here: `StageEncodeReady` at phase entry):
     inhabited when the reference/focusing phase builds the pre-saturation
     continuation, not reconstructed after the fact from `WellInv` alone.

  Preferred direction (boss): preserve readiness compositionally during
  production. Fallback if InvTm certification still demands history
  reconstruction: emit ordered `ICCCode` directly during the reference phase.

  Full refactor is deferred until this spike’s composition principle is accepted.
-/

import Gimbal.Equality.ICCCode
import Gimbal.Equality.ICCFragment
import Gimbal.Equality.ICCTotal
import Gimbal.Equality.Saturation

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Stage readiness (any `ofHyps` depth) -/

/--
`EncodeReady` under the stage’s own `ofHyps` worklist/env.
Phase entry is the special case `PhaseEncodeReady`.
-/
def StageEncodeReady {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  EncodeReady (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))
    (OriginEnv.ofHyps hyps) 0 0 t

theorem StageEncodeReady.toPhase {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps) A}
    (h : StageEncodeReady t) : PhaseEncodeReady t :=
  h

theorem PhaseEncodeReady.toStage {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps) A}
    (h : PhaseEncodeReady t) : StageEncodeReady t :=
  h

/-! ### Production certificate (pre-saturation continuation) -/

/--
Production obligation: the continuation fed to `applyPairObs` already carries
stage readiness. This is **not** derivable from `WellInv` alone (empty schedule).

Inhabiting this is the focusing / invertible-intro phase’s job when it builds
`t₀` / `u₀` (and when binder re-entry builds new continuations under `hyps.push`).
-/
abbrev ContReadyCert {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (cont : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  StageEncodeReady cont

/-! ### Preservation certificate (`applyPairObsGo`) -/

/--
Proof-relevant certificate that schedule application produced `t` **while
preserving** stage readiness from the input continuation.

Constructors follow evaluator structure (`nil` / atom `letPos` / coprod `case` /
inconsistent abort), not ad-hoc result-shape predicates
(`AtomDerivedContShape`, …). Recursive premises are themselves certificates (or
stage readiness of recursive results), so mixed multi-entry schedules compose.
-/
inductive ApplyPairObsReadyCert : ∀ {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases},
    Nat → ReachState sig.nBases → Array (Object sig.nBases) →
    List (PairEntry sig hyps) → InvTm (Ctx.ofHyps hyps) A →
    InvTm (Ctx.ofHyps hyps) A → Prop where
  /-- Empty schedule returns the continuation unchanged. -/
  | nil {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
      {fuel : Nat} {σ : ReachState sig.nBases}
      {cont t : InvTm (Ctx.ofHyps hyps) A}
      (hcont : ContReadyCert cont)
      (hok : applyPairObsGo (fuel + 1) σ hyps ([] : List (PairEntry sig hyps)) cont =
        .ok t)
      (heq : t = cont) :
      ApplyPairObsReadyCert (fuel + 1) σ hyps [] cont t
  /--
  Atom observation: readiness of the pushed recursive body (from a rest
  certificate / IH) wraps to outer `letPos` via existing atom packaging.
  No continuation-shape predicate on `cont`.
  -/
  | exactAtom {hyps : Array (Object sig.nBases)} {P A : Object sig.nBases}
      {fuel : Nat} {σ : ReachState sig.nBases}
      {nP : NegNeu (Ctx.ofHyps hyps) P}
      {rest : List (PairEntry sig hyps)}
      {cont : InvTm (Ctx.ofHyps hyps) A}
      {body' : InvTm (Ctx.ofHyps (hyps.push P)) A}
      {t : InvTm (Ctx.ofHyps hyps) A}
      (hP : P ≠ (.never : Object sig.nBases))
      (hNotCoprod : ∀ L R, P ≠ .coprod L R)
      (hcont : ContReadyCert cont)
      (hbody : StageEncodeReady body')
      (hok : applyPairObsGo (fuel + 1) σ hyps (.exact P nP :: rest) cont = .ok t)
      (ht : t = .foc (.letPos nP (InvTm.castCtx (Ctx.ofHyps_push hyps P) body')))
      (hwrap : StageEncodeReady t) :
      ApplyPairObsReadyCert (fuel + 1) σ hyps (.exact P nP :: rest) cont t
  /--
  Coproduct observation: branch readiness under the two pushes wraps to outer
  `case`. Again, premises are stage readiness of branches — not
  `CoprodDerivedContShape` on the parent continuation.
  -/
  | exactCoprod {hyps : Array (Object sig.nBases)} {L R A : Object sig.nBases}
      {fuel : Nat} {σ : ReachState sig.nBases}
      {n : NegNeu (Ctx.ofHyps hyps) (.coprod L R)}
      {rest : List (PairEntry sig hyps)}
      {cont : InvTm (Ctx.ofHyps hyps) A}
      {bodyL : InvTm (Ctx.ofHyps (hyps.push L)) A}
      {bodyR : InvTm (Ctx.ofHyps (hyps.push R)) A}
      {t : InvTm (Ctx.ofHyps hyps) A}
      (hcont : ContReadyCert cont)
      (hL : StageEncodeReady bodyL)
      (hR : StageEncodeReady bodyR)
      (hok : applyPairObsGo (fuel + 1) σ hyps
        (.exact (.coprod L R) n :: rest) cont = .ok t)
      (ht : t = .case n
        (InvTm.castCtx (Ctx.ofHyps_push hyps L) bodyL)
        (InvTm.castCtx (Ctx.ofHyps_push hyps R) bodyR))
      (hwrap : StageEncodeReady t) :
      ApplyPairObsReadyCert (fuel + 1) σ hyps
        (.exact (.coprod L R) n :: rest) cont t

/-- Preservation extract: a schedule certificate implies stage readiness of the result. -/
theorem ApplyPairObsReadyCert.stageReady {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {fuel : Nat} {σ : ReachState sig.nBases}
    {entries : List (PairEntry sig hyps)}
    {cont t : InvTm (Ctx.ofHyps hyps) A}
    (c : ApplyPairObsReadyCert fuel σ hyps entries cont t) :
    StageEncodeReady t := by
  cases c with
  | nil hcont _ heq =>
      subst heq
      exact hcont
  | exactAtom _ _ _ _ _ _ hwrap => exact hwrap
  | exactCoprod _ _ _ _ _ hwrap => exact hwrap

/-- Empty schedule: preservation is identity on the production certificate. -/
theorem applyPairObsReadyCert_nil {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {fuel : Nat} {σ : ReachState sig.nBases}
    {cont : InvTm (Ctx.ofHyps hyps) A}
    (hcont : ContReadyCert cont) :
    ApplyPairObsReadyCert (fuel + 1) σ hyps [] cont cont := by
  refine .nil hcont ?_ rfl
  simp [applyPairObsGo]

/-! ### Composition principle (no result-shape predicates) -/

/--
Atom step as pure preservation glue: given stage readiness of the recursive
body (from the rest schedule’s certificate), wrap with the existing atom
packaging. The parent continuation’s *syntax shape* is not inspected.
-/
theorem stageEncodeReady_of_atom_push_body
    {hyps : Array (Object sig.nBases)} {P A : Object sig.nBases}
    {nP : NegNeu (Ctx.ofHyps hyps) P}
    {body : InvTm (Ctx.ofHyps (hyps.push P)) A}
    (hws : ∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hbody : StageEncodeReady body) :
    StageEncodeReady
      (.foc (.letPos nP (InvTm.castCtx (Ctx.ofHyps_push hyps P) body))) :=
  encodeReady_applyObsNeu_atom_of_push_body_ready (n := nP) hws hfr hbody

/--
`exactAtom` with `hwrap` discharged from body readiness + packaging
(not from a continuation-shape predicate).
-/
theorem spike_exactAtom_wrap_from_body
    {hyps : Array (Object sig.nBases)} {P A : Object sig.nBases}
    {fuel : Nat} {σ : ReachState sig.nBases}
    {nP : NegNeu (Ctx.ofHyps hyps) P}
    {rest : List (PairEntry sig hyps)}
    {cont : InvTm (Ctx.ofHyps hyps) A}
    {body' : InvTm (Ctx.ofHyps (hyps.push P)) A}
    (hP : P ≠ (.never : Object sig.nBases))
    (hNotCoprod : ∀ L R, P ≠ .coprod L R)
    (hcont : ContReadyCert cont)
    (hws : ∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hbody : StageEncodeReady body')
    (hok : applyPairObsGo (fuel + 1) σ hyps (.exact P nP :: rest) cont =
      .ok (.foc (.letPos nP (InvTm.castCtx (Ctx.ofHyps_push hyps P) body')))) :
    ApplyPairObsReadyCert (fuel + 1) σ hyps (.exact P nP :: rest) cont
      (.foc (.letPos nP (InvTm.castCtx (Ctx.ofHyps_push hyps P) body'))) := by
  refine .exactAtom hP hNotCoprod hcont hbody hok rfl ?_
  exact stageEncodeReady_of_atom_push_body (nP := nP) hws hfr hbody

/--
Spike: **mixed** `exact atom :: (rest that yields a stage-ready mid-term)`.

Typical mid-term: outer `.case` from an exact coprod under the atom push,
obtained via `exactCoprod` / branch `StageEncodeReady`. One atom wrap then
yields parent readiness. No `AtomDerivedContShape` / `CoprodDerivedContShape`.
-/
theorem spike_mixed_atom_then_coprod_pres
    {hyps : Array (Object sig.nBases)} {P A : Object sig.nBases}
    {nP : NegNeu (Ctx.ofHyps hyps) P}
    {cont : InvTm (Ctx.ofHyps hyps) A}
    {mid : InvTm (Ctx.ofHyps (hyps.push P)) A}
    (hws : ∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (_hcont : ContReadyCert cont)
    (hmid : StageEncodeReady mid) :
    StageEncodeReady
      (.foc (.letPos nP (InvTm.castCtx (Ctx.ofHyps_push hyps P) mid))) :=
  stageEncodeReady_of_atom_push_body (nP := nP) hws hfr hmid

/-- Mixed schedule certificate: mid readiness (e.g. from nested coprod) + atom wrap. -/
theorem spike_mixed_atom_coprod_cert
    {hyps : Array (Object sig.nBases)} {P A : Object sig.nBases}
    {fuel : Nat} {σ : ReachState sig.nBases}
    {nP : NegNeu (Ctx.ofHyps hyps) P}
    {rest : List (PairEntry sig hyps)}
    {cont : InvTm (Ctx.ofHyps hyps) A}
    {mid : InvTm (Ctx.ofHyps (hyps.push P)) A}
    (hP : P ≠ (.never : Object sig.nBases))
    (hNotCoprod : ∀ L R, P ≠ .coprod L R)
    (hcont : ContReadyCert cont)
    (hws : ∀ e ∈ OriginEnv.posWorklist (OriginEnv.ofHyps hyps),
      ∃ b : Fin sig.nBases, e.ty = .base b)
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus)
    (hmid : StageEncodeReady mid)
    (hok : applyPairObsGo (fuel + 1) σ hyps (.exact P nP :: rest) cont =
      .ok (.foc (.letPos nP (InvTm.castCtx (Ctx.ofHyps_push hyps P) mid)))) :
    ApplyPairObsReadyCert (fuel + 1) σ hyps (.exact P nP :: rest) cont
      (.foc (.letPos nP (InvTm.castCtx (Ctx.ofHyps_push hyps P) mid))) :=
  spike_exactAtom_wrap_from_body hP hNotCoprod hcont hws hfr hmid hok

/-! ### Full pipeline certificate (proposed) -/

/--
Proof-relevant witness for one reference saturation phase (`Type`, not `Prop`,
so it can retain schedule data).

* `contReady` — production (focusing / intro) certificate for the pre-schedule
  continuation;
* `applyCert` — preservation certificate for `applyPairObs` / `applyPairObsGo`.

`CertifiedReferenceProduced` should eventually be inhabited from this, not from
stashed `ValidEncodeFragment.ready` or from post-hoc shape reconstruction.
-/
structure ReferencePhaseReadyCert {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (t : InvTm (Ctx.ofHyps hyps) A) where
  fuel : Nat
  entries : Array (PairEntry sig hyps)
  σ : ReachState sig.nBases
  cont : InvTm (Ctx.ofHyps hyps) A
  hwell : WellInv cont
  contReady : ContReadyCert cont
  applyCert : ApplyPairObsReadyCert
    (saturationBudget fuel entries.size) σ hyps entries.toList cont t

theorem ReferencePhaseReadyCert.stageReady {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps) A}
    (c : ReferencePhaseReadyCert t) : StageEncodeReady t :=
  c.applyCert.stageReady

theorem ReferencePhaseReadyCert.toPhaseEncodeReady {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps) A}
    (c : ReferencePhaseReadyCert t) : PhaseEncodeReady t :=
  c.stageReady.toPhase

/-! ### Collapse / migration notes (spike conclusions as comments)

Existing restricted lemmas in `ICCTotal` largely become *instances* of
production or of one preservation constructor:

* `encodeReady_applyPairObsGo_nil` / empty WellInv-intro →ready
  → `ApplyPairObsReadyCert.nil` + production `ContReadyCert`
* `encodeReady_applyObsNeu_atom_of_push_body_ready` / coprod-var packaging
  → wrap discharge inside `spike_exactAtom_wrap_from_body` / coprod analogue
* `AtomDerivedContShape` / `CoprodDerivedContShape` / nil-rest Raw fragments
  → **retire** once production inhabits `ContReadyCert` and preservation is
  proved by induction on entries (no post-hoc shape search)

Still required for a full refactor (not done here):

1. `ContReadyCert` transport under `atomPushCont` / `coprodPushCont*`
   (cut/abstr preserves stage readiness) — replaces shape-derived push ready.
2. Induction `applyPairObsGo … = .ok t → ContReadyCert cont →
   ApplyPairObsReadyCert … t` under the real evaluator (consistency witnesses,
   rest maps, inconsistency).
3. Focusing / `completeInvRec` / binder re-entry produces `ContReadyCert`.
4. Migrate `RawReferenceProduced` → carry `ReferencePhaseReadyCert` (or keep raw
   and require cert separately for encode totality).

Fallback: have the reference phase emit `ICCCode` alongside (or instead of)
saturated `InvTm`, so ordered readiness is definitional in the producer.

Expected migration cost: medium — quarantine enumeration lemmas as historical;
new induction lives in this module / thin wrappers; `ICCTotal` stops growing
shape cases. Do **not** delete green checkpoint lemmas until the preservation
induction closes a mixed schedule end-to-end from `ContReadyCert cont` alone
(transport under cut still open).
-/
