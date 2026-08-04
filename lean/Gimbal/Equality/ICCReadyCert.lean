/-
  Milestone 8F readiness certificate spike (induction-boundary correction).

  Status: compositional preservation attempt after pausing Raw→EncodeReady
  enumeration at green checkpoint `192dae5`. This module does not switch
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
  2. **Production** — `ContReadyCert` / `StageEncodeReady` at phase entry:
     inhabited when focusing / intro builds the pre-saturation continuation.

  Acceptance test (not yet met for general schedules):
  `ContReadyCert cont → applyPairObsGo … = .ok t → StageEncodeReady t`
  with no manually supplied mid-term readiness.
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
-/
abbrev ContReadyCert {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (cont : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  StageEncodeReady cont

/-! ### Preservation certificate (`applyPairObsGo`) -/

/--
Proof-relevant certificate that schedule application produced `t` while
preserving stage readiness. Constructors follow evaluator structure.
-/
inductive ApplyPairObsReadyCert : ∀ {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases},
    Nat → ReachState sig.nBases → Array (Object sig.nBases) →
    List (PairEntry sig hyps) → InvTm (Ctx.ofHyps hyps) A →
    InvTm (Ctx.ofHyps hyps) A → Prop where
  | nil {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
      {fuel : Nat} {σ : ReachState sig.nBases}
      {cont t : InvTm (Ctx.ofHyps hyps) A}
      (hcont : ContReadyCert cont)
      (hok : applyPairObsGo (fuel + 1) σ hyps ([] : List (PairEntry sig hyps)) cont =
        .ok t)
      (heq : t = cont) :
      ApplyPairObsReadyCert (fuel + 1) σ hyps [] cont t
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

theorem applyPairObsReadyCert_nil {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {fuel : Nat} {σ : ReachState sig.nBases}
    {cont : InvTm (Ctx.ofHyps hyps) A}
    (hcont : ContReadyCert cont) :
    ApplyPairObsReadyCert (fuel + 1) σ hyps [] cont cont := by
  refine .nil hcont ?_ rfl
  simp [applyPairObsGo]

/-! ### Atom wrap glue (mid readiness → parent; no cont-shape hyp) -/

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

/-- Mixed atom-then-coprod composition: mid ready ⇒ parent ready (one wrap). -/
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

/-! ### Pipeline certificate (proposed) -/

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

/-! ## Cut transport + evaluator induction attempt -/

theorem encodeReady_nil_of_basesOnly {Γ : Ctx sig} {A : Object sig.nBases}
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {domNest obsSlot : Nat} {t : InvTm Γ A}
    (hws : worklistBasesOnly ws)
    (h : EncodeReady ws ε domNest obsSlot t) :
    EncodeReady ([] : List (PosEntry sig)) ε domNest obsSlot t := by
  induction ws with
  | nil => exact h
  | cons e ws ih =>
      have ⟨b, hb⟩ := hws e (List.Mem.head _)
      exact ih (fun e' he' => hws e' (List.Mem.tail _ he'))
        (encodeReady_tail_of_base_head ⟨b, hb⟩ h)

theorem InvTm.abstr_weaken_unit {Γ : Ctx sig} {P : Object sig.nBases}
    (m : NegNeu Γ P) :
    InvTm.abstr (.here : Var (Γ ▻ P) P) (NegNeu.weaken (B := P) m)
      (InvTm.weaken (B := P) (.unit : InvTm Γ .unit)) =
      (.unit : InvTm (Γ ▻ P) .unit) := by
  simp only [InvTm.weaken_unit, InvTm.abstr_unit]

theorem InvTm.abstr_weaken_pair {Γ : Ctx sig} {P L R : Object sig.nBases}
    (m : NegNeu Γ P) (t : InvTm Γ L) (u : InvTm Γ R) :
    InvTm.abstr (.here : Var (Γ ▻ P) P) (NegNeu.weaken (B := P) m)
      (InvTm.weaken (B := P) (.pair t u)) =
      .pair
        (InvTm.abstr .here (NegNeu.weaken (B := P) m) (InvTm.weaken (B := P) t))
        (InvTm.abstr .here (NegNeu.weaken (B := P) m) (InvTm.weaken (B := P) u)) := by
  simp only [InvTm.weaken, InvTm.rename, InvTm.abstr]

/-! ### ContReadyCert under `atomPushCont` (closed fragment only) -/

theorem contReadyCert_atomPushCont_unit
    {hyps : Array (Object sig.nBases)} {b : Fin sig.nBases}
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))) :
    ContReadyCert (atomPushCont nP
      (.unit : InvTm (Ctx.ofHyps hyps) .unit)) :=
  encodeReady_atomPushCont_unit nP hws

theorem contReadyCert_atomPushCont_foc_pos
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {b : Fin sig.nBases}
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (p : PosNeu (Ctx.ofHyps hyps) A)
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    ContReadyCert (atomPushCont nP (.foc (.pos (.done p)))) :=
  encodeReady_atomPushCont_foc_pos nP p hws hfr

theorem contReadyCert_atomPushCont_foc_neg
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {b : Fin sig.nBases}
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (n : NegNeu (Ctx.ofHyps hyps) A)
    (hws : worklistBasesOnly
      (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)))
    (hfr : forcedRule ([] : List (PosEntry sig)) A = .focus) :
    ContReadyCert (atomPushCont nP (.foc (.neg (.done n)))) :=
  encodeReady_atomPushCont_foc_neg nP n hws hfr

/-! ### STOP — abstraction insufficient for full acceptance

**Blocked (EncodeReady naturality, not schedule-shape cases):**

1. Full `ContReadyCert cont → ContReadyCert (atomPushCont nP cont)` by
   induction on `EncodeReady` fails at:
   * `rightExp_lam` — body under `pushPos [] (.dom 0) Arg` (non-empty when Arg
     is positive); needs `Rename.ext (Rename.weaken)` readiness naturality.
   * `EncodeReadyFoc.letPos` — body under `pushPos [] (.obs k) Q`; cut-then-obs
     vs obs-then-cut needs obsSlot/rekey × abstr naturality.
2. Coprod: `StageEncodeReady (.case …)` cannot hold under bases-only `ofHyps`
   worklists (`forcedRule` strips to `.focus`, requiring `.foc`). Needs
   `.leftCoprod` worklist alignment or a different stage readiness notion.
   Gap in `StageEncodeReady := EncodeReady (posWorklist (ofHyps …))`.

Adding `*DerivedContShape` / nil-rest disjunctions would re-enter the paused
enumeration loop. Direct `ICCCode` production remains the fallback if these
naturality lemmas stay out of reach.

**Acceptance test:** not met for exact atom / coprod / consistency.
Only the nil schedule is closed with sole premise `ContReadyCert cont`.
Do **not** migrate totality, drop `ValidEncodeFragment.ready`, or retire
restricted `ICCTotal` lemmas.
-/

/-- Nil schedule: only readiness premise is `ContReadyCert cont`. -/
theorem stageEncodeReady_applyPairObsGo_nil
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {fuel : Nat} {σ : ReachState sig.nBases}
    {cont t : InvTm (Ctx.ofHyps hyps) A}
    (hcont : ContReadyCert cont)
    (hok : applyPairObsGo (fuel + 1) σ hyps ([] : List (PairEntry sig hyps)) cont =
      .ok t) :
    StageEncodeReady t := by
  simp only [applyPairObsGo] at hok
  cases hok
  exact hcont

theorem applyPairObsReadyCert_of_nil_ok
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {fuel : Nat} {σ : ReachState sig.nBases}
    {cont t : InvTm (Ctx.ofHyps hyps) A}
    (hcont : ContReadyCert cont)
    (hok : applyPairObsGo (fuel + 1) σ hyps ([] : List (PairEntry sig hyps)) cont =
      .ok t) :
    ApplyPairObsReadyCert (fuel + 1) σ hyps [] cont t := by
  simp only [applyPairObsGo] at hok
  cases hok
  exact applyPairObsReadyCert_nil hcont

end Equality
end Gimbal
