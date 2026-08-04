/-
  Retained Hof sum examples — EncodeIx code targets (parallel correctness path).

  Public evaluator/comparator stay on the contracted producer (`ae75c7f` green).
  These terms are the retained-binder forms that a future producer would emit for
  `hofSumId` / `hofSumEta`; we certify and encode them directly via `EncodeIx`.

  Does **not** change `applyObsNeu`, `checkOldInvariant`, `compareSatRec`,
  RawReference, or `referenceCompare`.
-/

import Gimbal.Equality.ICCEncodeIx
import Gimbal.Equality.ICCPeel
import Gimbal.Equality.ICCRetain
import Gimbal.Equality.ICCTotal
import Gimbal.Equality.Saturation
import Gimbal.Equality.Translate
import Gimbal.Fixtures

namespace Gimbal
namespace Equality

open Gimbal.Fixtures

/-! ### Signature and shared retained term -/

def HofSumSig : Signature where
  nBases := 1
  generators := #[⟨.unit, .coprod Number Number⟩]

private abbrev NumberH : Object HofSumSig.nBases := Number
private abbrev SumN : Object HofSumSig.nBases := .coprod NumberH NumberH

/-- Generator context hyps: `g : unit → Number+Number`, then `x : unit`. -/
def hofHyps : Array (Object HofSumSig.nBases) :=
  (translateCtx (sig := HofSumSig) .unit).toReachCtx.hyps

def hofΓ : Ctx HofSumSig := Ctx.ofHyps (sig := HofSumSig) hofHyps

def hofEntry : EncodeIx (sig := HofSumSig) hofΓ :=
  EncodeIx.entry (sig := HofSumSig) hofHyps

/-- Observation: `g ()` (matches focused translate of the Hof generator). -/
def hofObs : NegNeu hofΓ SumN :=
  .app (.var (.there .here)) .unit

/-- Contracted η-branches under a summand binder (producer empty-rest shape). -/
def hofBranchL : InvTm (hofΓ ▻ NumberH) SumN :=
  .foc (.pos (.done (.inl (.neu (.var .here)))))

def hofBranchR : InvTm (hofΓ ▻ NumberH) SumN :=
  .foc (.pos (.done (.inr (.neu (.var .here)))))

/--
Retained binder form for both Hof sum examples (gen and η-compose saturate to
the same contracted case on green tip; retain wraps that observation).
-/
def hofRetained : InvTm hofΓ SumN :=
  .foc (.letPos hofObs
    (.case (.var .here)
      (InvTm.rename (Rename.skip1 (B := SumN)) hofBranchL)
      (InvTm.rename (Rename.skip1 (B := SumN)) hofBranchR)))

def hofCaseBody : InvTm (hofΓ ▻ SumN) SumN :=
  .case (.var .here)
    (InvTm.rename (Rename.skip1 (B := SumN)) hofBranchL)
    (InvTm.rename (Rename.skip1 (B := SumN)) hofBranchR)

def hofAfterObs : EncodeIx (sig := HofSumSig) (hofΓ ▻ SumN) :=
  hofEntry.bindObs SumN

def hofObsEntry : PosEntry HofSumSig :=
  ⟨.obs (sig := HofSumSig) 0, SumN⟩

/-! ### Worklist / peel facts -/

theorem hofEntry_ws_nil : hofEntry.ws = [] := by
  simp only [hofEntry, EncodeIx.entry, hofHyps, OriginEnv.posWorklist,
    OriginEnv.posCollect, translateCtx, Ctx.toReachCtx]
  native_decide

theorem hof_forcedRule_entry :
    forcedRule (sig := HofSumSig) hofEntry.ws SumN = .focus := by
  simp only [hofEntry_ws_nil, forcedRule]

theorem hof_bindObs_ws :
    hofAfterObs.ws = [hofObsEntry] := by
  simp only [hofAfterObs, EncodeIx.bindObs, hofEntry_ws_nil, pushPos,
    hofObsEntry, SumN]
  native_decide

theorem hof_env_here_obs :
    hofAfterObs.env (Var.here : Var (sig := HofSumSig) (hofΓ ▻ SumN) SumN) =
      (.obs (sig := HofSumSig) 0 : Origin HofSumSig) := by
  simp [hofAfterObs, EncodeIx.bindObs, hofEntry, EncodeIx.entry,
    OriginEnv.weaken, OriginEnv.snoc]

theorem hof_peel_case :
    peelCaseOuter (sig := HofSumSig) hofAfterObs.env hofObsEntry.origin hofCaseBody =
      some ⟨NumberH, NumberH, .var .here,
        InvTm.rename (Rename.skip1 (B := SumN)) hofBranchL,
        InvTm.rename (Rename.skip1 (B := SumN)) hofBranchR⟩ := by
  simpa [hofCaseBody, hofObsEntry] using
    (peelCaseOuter_case_var_hit (sig := HofSumSig) hofAfterObs.env
      (.obs (sig := HofSumSig) 0)
      (Var.here : Var (sig := HofSumSig) (hofΓ ▻ SumN) SumN)
      _ _ hof_env_here_obs)

theorem hof_forcedRule_leftCoprod :
    forcedRule (sig := HofSumSig) [hofObsEntry] SumN =
      .leftCoprod hofObsEntry NumberH NumberH := by
  simp [forcedRule, hofObsEntry, SumN]

theorem hof_splitL_ws :
    (hofAfterObs.splitL hofObsEntry NumberH).ws =
      [{ origin := .split (.obs (sig := HofSumSig) 0) false, ty := NumberH }] := by
  simp only [EncodeIx.splitL, hof_bindObs_ws, pushPos, List.tail_cons]
  native_decide

theorem hof_splitR_ws :
    (hofAfterObs.splitR hofObsEntry NumberH).ws =
      [{ origin := .split (.obs (sig := HofSumSig) 0) true, ty := NumberH }] := by
  simp only [EncodeIx.splitR, hof_bindObs_ws, pushPos, List.tail_cons]
  native_decide

/-! ### Compositional certificates -/

theorem hof_branchL_cert :
    InvCert (hofAfterObs.splitL hofObsEntry NumberH)
      (InvTm.rename (Rename.skip1 (B := SumN)) hofBranchL) := by
  set s := hofAfterObs.splitL hofObsEntry NumberH
  have hws := hof_splitL_ws
  have hnil : EncodeReady (sig := HofSumSig) [] s.env s.domNext s.obsNext
      (InvTm.rename (Rename.skip1 (B := SumN)) hofBranchL) :=
    .focus (by simp [forcedRule]) .pos
  have hfr : forcedRule (sig := HofSumSig)
      ([{ origin := .split (.obs (sig := HofSumSig) 0) false, ty := NumberH }] :
        List (PosEntry HofSumSig)) SumN =
      .moveStable ⟨.split (.obs (sig := HofSumSig) 0) false, NumberH⟩ := by
    simp [forcedRule, NumberH, Number]
  change EncodeReady s.ws s.env s.domNext s.obsNext _
  rw [hws]
  exact EncodeReady.moveStable hfr hnil

theorem hof_branchR_cert :
    InvCert (hofAfterObs.splitR hofObsEntry NumberH)
      (InvTm.rename (Rename.skip1 (B := SumN)) hofBranchR) := by
  set s := hofAfterObs.splitR hofObsEntry NumberH
  have hws := hof_splitR_ws
  have hnil : EncodeReady (sig := HofSumSig) [] s.env s.domNext s.obsNext
      (InvTm.rename (Rename.skip1 (B := SumN)) hofBranchR) :=
    .focus (by simp [forcedRule]) .pos
  have hfr : forcedRule (sig := HofSumSig)
      ([{ origin := .split (.obs (sig := HofSumSig) 0) true, ty := NumberH }] :
        List (PosEntry HofSumSig)) SumN =
      .moveStable ⟨.split (.obs (sig := HofSumSig) 0) true, NumberH⟩ := by
    simp [forcedRule, NumberH, Number]
  change EncodeReady s.ws s.env s.domNext s.obsNext _
  rw [hws]
  exact EncodeReady.moveStable hfr hnil

theorem hof_caseBody_invCert : InvCert hofAfterObs hofCaseBody := by
  have hws := hof_bindObs_ws
  have hL : EncodeReady (sig := HofSumSig)
      (pushPos ([] : List (PosEntry HofSumSig))
        (.split hofObsEntry.origin false) NumberH)
      (OriginEnv.weaken (A := NumberH) hofAfterObs.env
        (.split hofObsEntry.origin false))
      hofAfterObs.domNext hofAfterObs.obsNext
      (InvTm.rename (Rename.skip1 (B := SumN)) hofBranchL) := by
    simpa [EncodeIx.splitL, hws, InvCert, List.tail_cons] using hof_branchL_cert
  have hR : EncodeReady (sig := HofSumSig)
      (pushPos ([] : List (PosEntry HofSumSig))
        (.split hofObsEntry.origin true) NumberH)
      (OriginEnv.weaken (A := NumberH) hofAfterObs.env
        (.split hofObsEntry.origin true))
      hofAfterObs.domNext hofAfterObs.obsNext
      (InvTm.rename (Rename.skip1 (B := SumN)) hofBranchR) := by
    simpa [EncodeIx.splitR, hws, InvCert, List.tail_cons] using hof_branchR_cert
  change EncodeReady hofAfterObs.ws hofAfterObs.env
    hofAfterObs.domNext hofAfterObs.obsNext hofCaseBody
  rw [hws]
  exact
    (invCert_leftCoprod_peel (sig := HofSumSig) (ws := []) hofObsEntry
      (.var (Var.here : Var (sig := HofSumSig) (hofΓ ▻ SumN) SumN))
      (InvTm.rename (Rename.skip1 (B := SumN)) hofBranchL)
      (InvTm.rename (Rename.skip1 (B := SumN)) hofBranchR)
      hofCaseBody hof_forcedRule_leftCoprod hof_peel_case hL hR)

theorem hofRetained_entryReady : EntryReady (sig := HofSumSig) hofRetained := by
  have hfr := hof_forcedRule_entry
  have hobs : hofEntry.obsNext = 0 := rfl
  refine invCert_focus hofEntry (.letPos hofObs hofCaseBody) hfr ?_
  have ht : EncodeReady (sig := HofSumSig)
      (pushPos ([] : List (PosEntry HofSumSig)) (.obs (sig := HofSumSig) 0) SumN)
      (OriginEnv.weaken (A := SumN) hofEntry.env (.obs (sig := HofSumSig) 0))
      hofEntry.domNext 1 hofCaseBody := by
    simpa [InvCert, hofAfterObs, EncodeIx.bindObs, hofEntry_ws_nil, hobs] using
      hof_caseBody_invCert
  rw [hofEntry_ws_nil, hobs]
  exact focCert_letPos (sig := HofSumSig) hofObs hofCaseBody ht

theorem hofRetained_encodes :
    ∃ c, encodeICC (OriginEnv.ofHyps (sig := HofSumSig) hofHyps) hofRetained =
      some c :=
  entryReady_encode_some hofRetained_entryReady

/-! ### Fixture-level code targets -/

/-- Shared retained code for both sides of `hofSumId` / `hofSumEta`. -/
def retainedCode_hof : Option (ICCCode hofΓ SumN) :=
  encodeICCHyps (sig := HofSumSig) hofRetained

/-- `hofSumId.left` retained code. -/
def retainedCode_hofSumId_left : Option (ICCCode hofΓ SumN) := retainedCode_hof
/-- `hofSumId.right` retained code. -/
def retainedCode_hofSumId_right : Option (ICCCode hofΓ SumN) := retainedCode_hof
/-- `hofSumEta.left` retained code (same retained sat form as gen on green tip). -/
def retainedCode_hofSumEta_left : Option (ICCCode hofΓ SumN) := retainedCode_hof
/-- `hofSumEta.right` retained code. -/
def retainedCode_hofSumEta_right : Option (ICCCode hofΓ SumN) := retainedCode_hof

theorem retainedCode_hofSumId_eq :
    retainedCode_hofSumId_left = retainedCode_hofSumId_right :=
  rfl

theorem retainedCode_hofSumEta_eq :
    retainedCode_hofSumEta_left = retainedCode_hofSumEta_right :=
  rfl

theorem retainedCode_hof_isSome : retainedCode_hof.isSome = true := by
  obtain ⟨c, hc⟩ := hofRetained_encodes
  simp only [retainedCode_hof, encodeICCHyps, hc]
  rfl

/-- Erasure bridge: retained Hof form agrees with contracted case on erase. -/
theorem hofRetained_erase_eq_contracted :
    hofRetained.erase =
      (InvTm.case hofObs hofBranchL hofBranchR).erase := by
  simpa [hofRetained, InvTm.erase, FocTm.erase, hofCaseBody] using
    erase_retained_coprod_obs (sig := HofSumSig) hofObs hofBranchL hofBranchR

end Equality
end Gimbal
