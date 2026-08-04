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

/-! ## Parallel certified retained producer (Hof schedule fragment)

Independent production for the generator and η-compose inputs. The public
`applyObsNeu` is not used. Observation binders are retained via the same
abstr+η+`Rename.skip1` recipe as the evaluator’s empty-rest coprod path, then
certified at `EncodeIx` states (not by returning `hofRetained` as the term).
`hofRetained` / `retainedCode_hof` remain expected-result fixtures only.
-/

/--
Empty-rest retained coproduct observation when the continuation is the
observed neu itself (identity-on-sum fragment used by Hof).
Generic term constructor — no certificate yet.
-/
def retainedCoprodIdObs {Γ : Ctx HofSumSig}
    (n : NegNeu Γ SumN) : InvTm Γ SumN :=
  let cont : InvTm Γ SumN := .foc (.pos (.done (.neu n)))
  let body : InvTm (Γ ▻ SumN) SumN :=
    InvTm.abstr (P := SumN) .here (NegNeu.weaken (B := SumN) n)
      (InvTm.weaken (B := SumN) cont)
  let uL := hsubstInv (InvTm.rename (Rename.skip1 (A := SumN) (B := NumberH)) body)
    (InvTm.etaInl (Γ := Γ) NumberH NumberH)
  let uR := hsubstInv (InvTm.rename (Rename.skip1 (A := SumN) (B := NumberH)) body)
    (InvTm.etaInr (Γ := Γ) NumberH NumberH)
  .foc (.letPos n (.case (.var .here)
    (InvTm.rename (Rename.skip1 (A := NumberH) (B := SumN)) uL)
    (InvTm.rename (Rename.skip1 (A := NumberH) (B := SumN)) uR)))

/-- Extract the coproduct observation from a Hof-focused term (neu or case). -/
def hofObsFromFocus (t : InvTm hofΓ SumN) : Option (NegNeu hofΓ SumN) :=
  match t with
  | .foc (.pos (.done (.neu n))) => some n
  | .case (A := L) (B := R) n _ _ =>
      if h : L = NumberH ∧ R = NumberH then
        some (NegNeu.cast (by simp [SumN, NumberH, h.1, h.2]) n)
      else none
  | _ => none

/-- Focus translate under the Hof generator context. -/
def hofFocusOf (f : IntrinsicMorphism HofSumSig .unit SumN) : InvTm hofΓ SumN :=
  have h := Ctx.ofHyps_toReachCtx (translateCtx (sig := HofSumSig) .unit)
  InvTm.castCtx h.symm (focus (translate (sig := HofSumSig) f))

def hofGen : IntrinsicMorphism HofSumSig .unit SumN := .generator ⟨0, by decide⟩

def hofEta : IntrinsicMorphism HofSumSig .unit SumN :=
  IntrinsicMorphism.compose (sig := HofSumSig) hofGen
    (IntrinsicMorphism.case (sig := HofSumSig)
      (IntrinsicMorphism.left (sig := HofSumSig) NumberH NumberH)
      (IntrinsicMorphism.right (sig := HofSumSig) NumberH NumberH))

/-- Producer output term for one Hof input (fails only if focus shape is unexpected). -/
def hofProduceTerm (f : IntrinsicMorphism HofSumSig .unit SumN) : Option (InvTm hofΓ SumN) :=
  match hofObsFromFocus (hofFocusOf f) with
  | some n => some (retainedCoprodIdObs n)
  | none => none

/-- Lift a successful `beq` evaluation on an optional term to propositional equality. -/
theorem optionInvTm_eq_of_beq
    (o : Option (InvTm hofΓ SumN)) (u : InvTm hofΓ SumN)
    (h : (match o with | some t => t.beq u | none => false) = true) :
    o = some u := by
  match ho : o with
  | none => simp at h
  | some t =>
    have heq := InvTm.eq_of_beq t u (by simpa [ho] using h)
    rw [heq]

/-- Lift a successful `beq` evaluation on an optional neu to propositional equality. -/
theorem optionNegNeu_eq_of_beq
    (o : Option (NegNeu hofΓ SumN)) (u : NegNeu hofΓ SumN)
    (h : (match o with | some n => n.beq u | none => false) = true) :
    o = some u := by
  match ho : o with
  | none => simp at h
  | some n =>
    obtain ⟨hty, hnm⟩ := NegNeu.eq_of_beq n u (by simpa [ho] using h)
    cases hty
    cases eq_of_heq hnm
    rfl

theorem hofProduceTerm_gen_eq_fixture :
    hofProduceTerm hofGen = some hofRetained :=
  optionInvTm_eq_of_beq _ _ (by native_decide)

theorem hofProduceTerm_eta_eq_fixture :
    hofProduceTerm hofEta = some hofRetained :=
  optionInvTm_eq_of_beq _ _ (by native_decide)

theorem invCert_of_eq {Γ : Ctx HofSumSig} {A : Object HofSumSig.nBases}
    (s : EncodeIx (sig := HofSumSig) Γ) {t u : InvTm Γ A}
    (h : t = u) (c : InvCert s t) : InvCert s u :=
  h ▸ c

/--
Certified production package: independently produced term + InvCert + code.
-/
structure CertifiedHofProduction where
  source : IntrinsicMorphism HofSumSig .unit SumN
  focus : InvTm hofΓ SumN
  obs : NegNeu hofΓ SumN
  term : InvTm hofΓ SumN
  cert : InvCert hofEntry term
  code : ICCCode hofΓ SumN
  encode_eq :
    encodeICC (OriginEnv.ofHyps (sig := HofSumSig) hofHyps) term = some code

/--
Package production when the produced retained term matches the fixture.
`hofRetained` is used only as the expected-result equality target for cert
transport and code comparison — not as the returned `term`.
-/
noncomputable def certifyHofProduction
    (f : IntrinsicMorphism HofSumSig .unit SumN)
    (n : NegNeu hofΓ SumN)
    (hterm : retainedCoprodIdObs n = hofRetained) :
    CertifiedHofProduction :=
  let term := retainedCoprodIdObs n
  let cert := invCert_of_eq hofEntry hterm.symm hofRetained_entryReady
  let hex := entryReady_encode_some cert
  { source := f
    focus := hofFocusOf f
    obs := n
    term := term
    cert := cert
    code := Classical.choose hex
    encode_eq := Classical.choose_spec hex }

theorem hofObsFromFocus_gen :
    hofObsFromFocus (hofFocusOf hofGen) = some hofObs :=
  optionNegNeu_eq_of_beq _ _ (by native_decide)

theorem hofObsFromFocus_gen_produce :
    retainedCoprodIdObs hofObs = hofRetained := by
  have hprod := hofProduceTerm_gen_eq_fixture
  simp only [hofProduceTerm, hofObsFromFocus_gen] at hprod
  exact Option.some.inj hprod

theorem hofObsFromFocus_eta :
    ∃ n, hofObsFromFocus (hofFocusOf hofEta) = some n ∧
      retainedCoprodIdObs n = hofRetained := by
  have hprod := hofProduceTerm_eta_eq_fixture
  simp only [hofProduceTerm] at hprod
  match hofObsFromFocus (hofFocusOf hofEta), hprod with
  | none, hprod => simp at hprod
  | some n, hprod =>
    exact ⟨n, rfl, Option.some.inj hprod⟩

/-- Independent certified production for the generator input. -/
noncomputable def certifiedHofGen : CertifiedHofProduction :=
  certifyHofProduction hofGen hofObs hofObsFromFocus_gen_produce

/-- Independent certified production for the η-compose input. -/
noncomputable def certifiedHofEta : CertifiedHofProduction :=
  let n := Classical.choose hofObsFromFocus_eta
  let h := Classical.choose_spec hofObsFromFocus_eta
  certifyHofProduction hofEta n h.2

theorem certifiedHofGen_code_eq_fixture :
    some certifiedHofGen.code = retainedCode_hof := by
  have he := certifiedHofGen.encode_eq
  have ht : certifiedHofGen.term = hofRetained := by
    simp only [certifiedHofGen, certifyHofProduction, hofObsFromFocus_gen_produce]
  simp only [retainedCode_hof, encodeICCHyps]
  calc some certifiedHofGen.code
      = encodeICC (OriginEnv.ofHyps (sig := HofSumSig) hofHyps)
          certifiedHofGen.term := he.symm
    _ = encodeICC (OriginEnv.ofHyps (sig := HofSumSig) hofHyps) hofRetained := by
        rw [ht]

theorem certifiedHofEta_code_eq_fixture :
    some certifiedHofEta.code = retainedCode_hof := by
  have he := certifiedHofEta.encode_eq
  have ht : certifiedHofEta.term = hofRetained := by
    simp only [certifiedHofEta, certifyHofProduction]
    exact (Classical.choose_spec hofObsFromFocus_eta).2
  simp only [retainedCode_hof, encodeICCHyps]
  calc some certifiedHofEta.code
      = encodeICC (OriginEnv.ofHyps (sig := HofSumSig) hofHyps)
          certifiedHofEta.term := he.symm
    _ = encodeICC (OriginEnv.ofHyps (sig := HofSumSig) hofHyps) hofRetained := by
        rw [ht]

theorem certifiedHof_codes_agree :
    certifiedHofGen.code = certifiedHofEta.code := by
  have hG := certifiedHofGen_code_eq_fixture
  have hE := certifiedHofEta_code_eq_fixture
  injection (hG.trans hE.symm)

/-!
### Producer-integration stop report

**Succeeded:** `hofGen` (neu focus) and `hofEta` (case focus) each extract an
observation, run `retainedCoprodIdObs` (abstr+η+skip1 retain), obtain an
`InvCert` (via transport once the produced term equals the fixture), and yield
an independently chosen ordered code equal to `retainedCode_hof`.

**Generic enough for a full certified producer**
* `retainedCoprodIdObs` — empty-rest identity-on-sum retain recipe
* `focus` / `letPos` / `leftCoprod_peel` / `moveStable` / `pos` packaging
* `invCert_encodeGo_some` / `entryReady_encode_some`
* erase bridge `erase_retained_coprod_obs`

**Still fixture-specific**
* `hofObsFromFocus` — only neu and `case` with `Number+Number` scrutinee
* identity-on-sum continuation (`cont := foc.pos.neu n`), not arbitrary `cont`
* empty-rest only (no schedule remainder)
* cert transport via `native_decide` equality to `hofRetained` (not a
  compositional cert built on the produced term’s own syntax)
* Hof signature / translate context wiring

Public evaluator, RawReference, totality, and comparator remain untouched.
-/

end Equality
end Gimbal
