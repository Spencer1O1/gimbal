/-
  Early Milestone 7 fixtures: elaboration, translation, polarization, focusing.
  Includes a short pre-reachability hardening pass.
-/

import Gimbal.Equality.Focus
import Gimbal.Equality.Opacity
import Gimbal.Equality.Translate
import Gimbal.Equality.Reachability
import Gimbal.Equality.Saturation
import Gimbal.Equality.ReconstructWF
import Gimbal.Equality.ICC
import Gimbal.Equality.ICCCode
import Gimbal.Equality.Compare
import Gimbal.Equality.Reference
import Gimbal.Fixtures

namespace Gimbal.Equality.Fixtures

open Gimbal Gimbal.Fixtures Gimbal.Equality

example : (ofMorphism two).erase = two.term :=
  ofMorphism_erase two

example : elaborate (sig := NumSig) illTypedComposeTerm = none :=
  rfl

example :
    translate (sig := NumSig) (.id Number) = .var .here :=
  rfl

example :
    translate (sig := NumSig) (.discard Number) = .unit :=
  rfl

example :
    translateMorphism two =
      .app (.var (.there (genVar NumSig ⟨0, by decide⟩))) (.var .here) :=
  rfl

/-- Fixed polarity assignment. -/
example : objectPolarity (Number : Object 1) = .pos := rfl
example : objectPolarity (.unit : Object 1) = .neg := rfl
example : objectPolarity (.prod Number Number) = .neg := rfl
example : objectPolarity (.coprod Number Number) = .pos := rfl
example : objectPolarity (.exp Number Number) = .neg := rfl

/-- Minimal shifts erase. -/
example : (asPos (Number : Object 1)).erase = Number :=
  erase_asPos _
example : (asNeg (.unit : Object 1)).erase = .unit :=
  erase_asNeg _

/-! ### Hardening helpers -/

private def isUnitInv {Γ : Ctx NumSig} : InvTm Γ .unit → Bool
  | .unit => true
  | _ => false

private def isIdFocused : InvTm (translateCtx (sig := NumSig) Number) Number → Bool
  | .foc (.pos (.done (.neu (.var .here)))) => true
  | _ => false

private def isFirstFocused :
    InvTm (translateCtx (sig := NumSig) (.prod Number Number)) Number → Bool
  | .foc (.pos (.done (.neu (.fst (.var .here))))) => true
  | _ => false

private def isLeftFocused :
    InvTm (translateCtx (sig := NumSig) Number) (.coprod Number Number) → Bool
  | .foc (.pos (.done (.inl (.neu (.var .here))))) => true
  | _ => false

private def isCaseUnit :
    InvTm (translateCtx (sig := NumSig) (.coprod Number Number)) .unit → Bool
  | .case (.var .here) .unit .unit => true
  | _ => false

private def isAbsurdFocused :
    InvTm (translateCtx (sig := NumSig) .never) Number → Bool
  | .abort (.var .here) => true
  | _ => false

/-! ### Hardening checks -/

def focusDiscardIsUnit : Bool :=
  match focus! (translate (sig := NumSig) (.discard Number)) with
  | some t => isUnitInv t
  | none => false

example : focusDiscardIsUnit = true := by native_decide

def focusIdIsVar : Bool :=
  match focus! (translate (sig := NumSig) (.id Number)) with
  | some t => isIdFocused t
  | none => false

example : focusIdIsVar = true := by native_decide

def focusFirstIsFst : Bool :=
  match focus! (translate (sig := NumSig) (.first Number Number)) with
  | some t => isFirstFocused t
  | none => false

example : focusFirstIsFst = true := by native_decide

def focusLeftIsInl : Bool :=
  match focus! (translate (sig := NumSig) (.left Number Number)) with
  | some t => isLeftFocused t
  | none => false

example : focusLeftIsInl = true := by native_decide

example : (focus! (translateMorphism two)).isSome = true := by
  native_decide

example : (focus! (translateMorphism curryAdd)).isSome = true := by
  native_decide

def caseDiscard : IntrinsicMorphism NumSig (.coprod Number Number) .unit :=
  IntrinsicMorphism.case (sig := NumSig)
    (.discard (sig := NumSig) Number)
    (.discard (sig := NumSig) Number)

def focusCaseIsCase : Bool :=
  match focus! (translate caseDiscard) with
  | some t => isCaseUnit t
  | none => false

example : focusCaseIsCase = true := by native_decide

def focusAbsurdIsAbort : Bool :=
  match focus! (translate (sig := NumSig) (.absurd Number)) with
  | some t => isAbsurdFocused t
  | none => false

example : focusAbsurdIsAbort = true := by native_decide

example :
    (focus! (translate (sig := NumSig) (.eval Number Number))).isSome = true := by
  native_decide

example : (focus! (translateMorphism pairThenAdd)).isSome = true := by
  native_decide

/-! ### Reachability spike gates -/

/-- `x : X, s : X → X` — type universe stays finite (no neutral explosion). -/
def cycleCtx : ReachCtx 1 where
  hyps := #[(.base 0 : Object 1), .exp (.base 0) (.base 0)]
  newFrom := 0

def cycleGoal : Object 1 := .base 0

def cycleState : ReachState 1 :=
  runReachability cycleCtx cycleGoal

/-- Subformula closure is tiny: X and X→X only. -/
example : (subformulaClosure (cycleCtx.roots cycleGoal)).size = 2 := by
  native_decide

/-- X is retrievable from the context variable. -/
example : isRetrievable cycleState (.base 0) = true := by
  native_decide

/-- Applying `s` does not enlarge the type universe. -/
example : (pendingWitnesses cycleState).size = 0 := by
  native_decide

/-- Inconsistent context: `x : 0` makes never simply deducible. -/
def neverCtx : ReachCtx 1 where
  hyps := #[(.never : Object 1)]
  newFrom := 0

example : (runReachability neverCtx (.base 0)).inconsistent = true := by
  native_decide

/--
New fragment: old has `s : X → Y`, new has `x : X`.
Then `Y` becomes simply deducible via app, not yet retrievable.
-/
def appCtx : ReachCtx 2 where
  hyps := #[
    .exp (.base 0) (.base 1), -- s : X → Y  (old)
    .base 0                    -- x : X      (new)
  ]
  newFrom := 1

def appState : ReachState 2 :=
  runReachability appCtx (.base 1)

example : isSimplyDeducible appState (.base 1) = true := by
  native_decide

example : isRetrievable appState (.base 1) = false := by
  native_decide

example : (pendingWitnesses appState).size = 1 := by
  native_decide

/-- Pending `Y` uses the new hypothesis `x`. -/
example : usesNew appState (.base 1) = true := by
  native_decide

/-- Schedule contains exactly that pending witness. -/
example : (buildSchedule appState).size = 1 := by
  native_decide

/--
Provenance lattice: old hyp `x : X` and new `f : 1 → X` both witness `X`.
Discovering the uses-new app does not erase the old-only hyp witness.
-/
def provenanceDualCtx : ReachCtx 1 where
  hyps := #[.base 0, .exp (.unit : Object 1) (.base 0)]
  newFrom := 1

def provenanceDualKeepsBoth : Bool :=
  let σ := runReachability provenanceDualCtx (.base 0)
  match σ.findTypeIdx (.base 0) with
  | some i =>
    let c := σ.getCell i
    c.oldWitness.isSome && c.newWitness.isSome && c.retrievable
  | none => false

example : provenanceDualKeepsBoth = true := by native_decide

/--
Fixture #8: when `X` carries both an old-only and a uses-new witness, dual-fire
records `Y` in *both* provenance slots — the old-only application `f x` and the
uses-new application through `x'`.
-/
def provenanceOverlapCtx : ReachCtx 2 where
  hyps := #[
    .base 0,                  -- x  : X  (old)
    .exp (.base 0) (.base 1), -- f  : X → Y (old)
    .base 0                   -- x' : X  (new)
  ]
  newFrom := 2

/-- Both provenance slots are inhabited for `Y`. -/
def provenanceOverlapKeepsBoth : Bool :=
  let σ := runReachability provenanceOverlapCtx (.base 1)
  match σ.findTypeIdx (.base 1) with
  | some i => (σ.getCell i).oldWitness.isSome && (σ.getCell i).newWitness.isSome
  | none => false

example : usesNew (runReachability provenanceOverlapCtx (.base 1)) (.base 1) = true := by
  native_decide

example : provenanceOverlapKeepsBoth = true := by native_decide

/-- Legacy name: previously pinned the single-fire gap; now false after dual-fire. -/
def provenanceOverlapOldSlotEmpty : Bool :=
  let σ := runReachability provenanceOverlapCtx (.base 1)
  match σ.findTypeIdx (.base 1) with
  | some i => !(σ.getCell i).oldWitness.isSome && (σ.getCell i).newWitness.isSome
  | none => false

example : provenanceOverlapOldSlotEmpty = false := by native_decide

/-- Product projection: `p : X × Y` makes both components deducible. -/
def prodCtx : ReachCtx 2 where
  hyps := #[.prod (.base 0) (.base 1)]
  newFrom := 0

def prodState : ReachState 2 :=
  runReachability prodCtx (.base 0)

example : isSimplyDeducible prodState (.base 0) = true := by
  native_decide

example : isSimplyDeducible prodState (.base 1) = true := by
  native_decide

private abbrev Sig2 : Signature := ⟨2, #[]⟩
private abbrev Sig1 : Signature := ⟨1, #[]⟩
private abbrev Sig3 : Signature := ⟨3, #[]⟩

/-! ### Split product projections (hyp vs type) and η tightening -/

/-- Hyp-product elimination records `fstHyp` / `sndHyp` (no cell parent). -/
def prodHypWitnessesAreHyp : Bool :=
  match prodState.findTypeIdx (.base 0), prodState.findTypeIdx (.base 1) with
  | some l, some r =>
    (match (prodState.getCell l).witness with
     | some (.fstHyp 0) => true
     | _ => false) &&
      (match (prodState.getCell r).witness with
       | some (.sndHyp 0) => true
       | _ => false)
  | _, _ => false

example : prodHypWitnessesAreHyp = true := by native_decide

/-- Hyp projections reconstruct from the context variable alone (WF API). -/
def prodHypReconstructOk : Bool :=
  let cr := certifiedRunReachability prodCtx (.base 0)
  let σ := cr.state
  let hyps := prodCtx.hyps
  match σ.findTypeIdx (.base 0), σ.findTypeIdx (.base 1) with
  | some l, some r =>
    (match (σ.getCell l).witness with
     | some w =>
       match reconstructWitnessWF_ofCell (sig := Sig2) cr.cert l hyps w with
       | some ⟨A, _⟩ => A == .base 0
       | none => false
     | none => false) &&
      (match (σ.getCell r).witness with
       | some w =>
         match reconstructWitnessWF_ofCell (sig := Sig2) cr.cert r hyps w with
         | some ⟨A, _⟩ => A == .base 1
         | none => false
       | none => false)
  | _, _ => false

example : prodHypReconstructOk = true := by native_decide

/-- Computed neutral product (`f : 1 → X × Y`) projects via `fstType` / `sndType`. -/
def neuProdCtx : ReachCtx 2 where
  hyps := #[.exp (.unit) (.prod (.base 0) (.base 1))]
  newFrom := 0

def neuProdState : ReachState 2 :=
  runReachability neuProdCtx (.base 0)

def neuProdWitnessesAreType : Bool :=
  let σ := neuProdState
  match σ.findTypeIdx (.base 0), σ.findTypeIdx (.base 1),
      σ.findTypeIdx (.prod (.base 0) (.base 1)) with
  | some l, some r, some p =>
    ((σ.getCell p).oldNeutral || (σ.getCell p).newNeutral) &&
      (match (σ.getCell l).witness with
       | some (.fstType p') => p' == p
       | _ => false) &&
      (match (σ.getCell r).witness with
       | some (.sndType p') => p' == p
       | _ => false)
  | _, _, _ => false

example : neuProdWitnessesAreType = true := by native_decide

/-- Type projections reconstruct by recursing to the parent product neutral (WF). -/
def neuProdReconstructOk : Bool :=
  let cr := certifiedRunReachability neuProdCtx (.base 0)
  let σ := cr.state
  let hyps := neuProdCtx.hyps
  match σ.findTypeIdx (.base 0) with
  | some l =>
    match (σ.getCell l).witness with
    | some (.fstType p) =>
      (match σ.typeAt p with
       | some (.prod _ _) => true
       | _ => false) &&
        (match reconstructWitnessWF_ofCell (sig := Sig2) cr.cert l hyps (.fstType p) with
         | some ⟨A, _⟩ => A == .base 0
         | none => false)
    | _ => false
  | none => false

example : neuProdReconstructOk = true := by native_decide

/-- η-only product: components from context, never `fstType` / `sndType`. -/
def etaOnlyProdCtx : ReachCtx 2 where
  hyps := #[.base 0, .base 1]
  newFrom := 0

def etaOnlyProdState : ReachState 2 :=
  runReachability etaOnlyProdCtx (.prod (.base 0) (.base 1))

def etaOnlyNoTypeProjection : Bool :=
  let σ := etaOnlyProdState
  match σ.findTypeIdx (.prod (.base 0) (.base 1)),
      σ.findTypeIdx (.base 0), σ.findTypeIdx (.base 1) with
  | some p, some l, some r =>
    let pc := σ.getCell p
    let isEta :=
      (match pc.oldWitness with | some .eta => true | _ => false) ||
        (match pc.newWitness with | some .eta => true | _ => false)
    let noTypeProj (c : ReachCell) : Bool :=
      (match c.oldWitness with
       | some (.fstType _) | some (.sndType _) => false
       | _ => true) &&
        (match c.newWitness with
         | some (.fstType _) | some (.sndType _) => false
         | _ => true)
    isEta && !pc.oldNeutral && !pc.newNeutral &&
      noTypeProj (σ.getCell l) && noTypeProj (σ.getCell r)
  | _, _, _ => false

example : etaOnlyNoTypeProjection = true := by native_decide

/--
Mixed provenance: old-neutral product from `f : 1 → X × Y`, plus new hyp
bindings for the components. Projections occupy the **neutral** slot only;
the uses-new component slots stay `ctxVar`, not fabricated `fstType`/`sndType`.
-/
def mixedNeuEtaCtx : ReachCtx 2 where
  hyps := #[
    .exp (.unit) (.prod (.base 0) (.base 1)),
    .base 0,
    .base 1
  ]
  newFrom := 1

def mixedNeuEtaState : ReachState 2 :=
  runReachability mixedNeuEtaCtx (.base 0)

def mixedNeuEtaNoFabricatedNewProj : Bool :=
  let σ := mixedNeuEtaState
  match σ.findTypeIdx (.prod (.base 0) (.base 1)),
      σ.findTypeIdx (.base 0), σ.findTypeIdx (.base 1) with
  | some p, some l, some r =>
    let pc := σ.getCell p
    let lc := σ.getCell l
    let rc := σ.getCell r
    -- Product carries an old neutral; projections may fill old component slots.
    pc.oldNeutral &&
      (match lc.oldWitness with | some (.fstType p') => p' == p | _ => false) &&
      (match rc.oldWitness with | some (.sndType p') => p' == p | _ => false) &&
      -- New slots are not type-projections (no η-fabricated neutrals).
      (match lc.newWitness with | some (.fstType _) | some (.sndType _) => false | _ => true) &&
      (match rc.newWitness with | some (.fstType _) | some (.sndType _) => false | _ => true)
  | _, _, _ => false

example : mixedNeuEtaNoFabricatedNewProj = true := by native_decide

/--
Regression: old Ret + new Arg with an η-only function must **not** manufacture
`.appTy` on Ret. η on the function is a β-detour; Ret was already deducible from
η, and intro/η must not count as neutral function provenance for `expAppRule`.
-/
def etaOnlyFnAppCtx : ReachCtx 2 where
  hyps := #[
    .base 1,  -- Ret (old)
    .base 0   -- Arg (new)
  ]
  newFrom := 1

def etaOnlyFnAppState : ReachState 2 :=
  runReachability etaOnlyFnAppCtx (.exp (.base 0) (.base 1))

def etaOnlyFnNoFabricatedAppTy : Bool :=
  let σ := etaOnlyFnAppState
  match σ.findTypeIdx (.exp (.base 0) (.base 1)),
      σ.findTypeIdx (.base 1) with
  | some f, some r =>
    let fc := σ.getCell f
    let rc := σ.getCell r
    let isEta :=
      (match fc.oldWitness with | some .eta => true | _ => false) ||
        (match fc.newWitness with | some .eta => true | _ => false)
    let noAppTy :=
      (match rc.oldWitness with | some (.appTy _ _) => false | _ => true) &&
        (match rc.newWitness with | some (.appTy _ _) => false | _ => true)
    isEta && !fc.oldNeutral && !fc.newNeutral && noAppTy &&
      isSimplyDeducible σ (.base 1) && isSimplyDeducible σ (.base 0)
  | _, _ => false

example : etaOnlyFnNoFabricatedAppTy = true := by native_decide

/-! ### Neutral selector + η-argument application (invOf deps) -/

/-- Preferred `witness` can be intro while `neutralWitness` still finds a neutral. -/
def neutralWitnessIgnoresNewEta : Bool :=
  let c : ReachCell :=
    { oldWitness := some (.ctxVar 0), newWitness := some .eta }
  (match c.witness with | some .eta => true | _ => false) &&
    (match c.neutralWitness with | some (.ctxVar 0) => true | _ => false)

example : neutralWitnessIgnoresNewEta = true := by native_decide

/--
Crafted dual provenance on a product cell: old `.app` (neutral) + new `.eta`.
`neutralWitness` must prefer the old neutral over preferred intro `witness`.
Full `neuOfTypeWF` on crafted (uncertified) states is out of scope for Bool
fixtures; certified selector coverage lives in `ReconstructWF`.
-/
def mixedOldNeutralNewEtaNeuOfOk : Bool :=
  let Γ : ReachCtx 2 := ⟨#[.exp (.unit) (.prod (.base 0) (.base 1)), .base 0], 0⟩
  let σ0 := mkReachState Γ (.prod (.base 0) (.base 1))
  match σ0.findTypeIdx (.prod (.base 0) (.base 1)),
      σ0.findTypeIdx (.unit : Object 2) with
  | some p, some u =>
    let σ1 := σ0.discover u false .unit
    let σ2 := σ1.discover p false (.app 0 u)
    let σ3 := σ2.discover p true .eta
    let c := σ3.getCell p
    (match c.witness with | some .eta => true | _ => false) &&
      (match c.neutralWitness with | some (.app _ _) => true | _ => false)
  | _, _ => false

example : mixedOldNeutralNewEtaNeuOfOk = true := by native_decide

/--
`f : (X × Y) → R` with `x : X`, `y : Y`: argument product is η-only; application
still reconstructs by `invOf` splitting to component neutrals.
-/
def etaArgAppCtx : ReachCtx 3 where
  hyps := #[
    .exp (.prod (.base 0) (.base 1)) (.base 2),
    .base 0,
    .base 1
  ]
  newFrom := 0

def etaArgAppState : ReachState 3 :=
  runReachability etaArgAppCtx (.base 2)

def etaArgAppReconstructOk : Bool :=
  let cr := certifiedRunReachability etaArgAppCtx (.base 2)
  let σ := cr.state
  match σ.findTypeIdx (.prod (.base 0) (.base 1)),
      σ.findTypeIdx (.base 2) with
  | some p, some r =>
    let pc := σ.getCell p
    let isEta :=
      (match pc.oldWitness with | some .eta => true | _ => false) ||
        (match pc.newWitness with | some .eta => true | _ => false)
    match (σ.getCell r).witness with
    | some (.app 0 p') =>
      isEta && !pc.oldNeutral && !pc.newNeutral && p' == p &&
        (match reconstructWitnessWF_ofCell (sig := Sig3) cr.cert r
            etaArgAppCtx.hyps (.app 0 p) with
         | some ⟨A, _⟩ => A == .base 2
         | none => false)
    | _ => false
  | _, _ => false

example : etaArgAppReconstructOk = true := by native_decide

/-- Old-only deduction: `Y` reachable without `Γnew` is not scheduled. -/
def oldOnlyCtx : ReachCtx 2 where
  hyps := #[
    .exp (.base 0) (.base 1),
    .base 0
  ]
  newFrom := 2  -- everything is old

example : (buildSchedule (runReachability oldOnlyCtx (.base 1))).size = 0 := by
  native_decide

example : isSimplyDeducible (runReachability oldOnlyCtx (.base 1)) (.base 1) = true := by
  native_decide

/-! ### Saturation schedule scaffolding -/

def satUnitEraseOk : Bool :=
  let s := saturate (sig := NumSig) neverCtx (.unit : Object 1)
    (InvTm.unit (Γ := Ctx.empty (sig := NumSig)))
  match s with
  | .mk sched cont =>
    sched.size == 0 &&
      match cont with
      | .unit => true
      | _ => false

example : satUnitEraseOk = true := by native_decide

/-! ### Schedule application -/

/-- Apply the appCtx schedule: `Y` becomes an observation via `s x`. -/
def applyAppScheduleIsLetPos : Bool :=
  let cont : InvTm (Ctx.ofHyps (sig := Sig2) appCtx.hyps) (.unit : Object 2) := .unit
  match saturateInv (sig := Sig2) (fuel := 128) appCtx (.base 1) cont with
  | .ok t =>
    match t with
    | .foc (.letPos _ .unit) => true
    | _ => false
  | _ => false

example : applyAppScheduleIsLetPos = true := by native_decide

/-- Inconsistent context collapses through abort. -/
def applyNeverAbortUnit : Bool :=
  let cont : InvTm (Ctx.ofHyps (sig := Sig1) neverCtx.hyps) (.unit : Object 1) := .unit
  match saturateInv (sig := Sig1) (fuel := 64) neverCtx (.base 0) cont with
  | .ok (.abort _) => true
  | _ => false

example : applyNeverAbortUnit = true := by native_decide

/--
Handoff adversarial #10: in an inconsistent context the comparison collapses two
genuinely different terms through the discovered proof of `0`. Context is
`z : 0`, `x y : X`; the two focused forms differ, and the comparison is `.equal`.
-/
def inconsistentCollapsesCompare : Bool :=
  let hyps : Array (Object 1) := #[.never, .base 0, .base 0]
  let Γ : ReachCtx 1 := ⟨hyps, 0⟩
  let t : Tm (Ctx.ofHyps (sig := Sig1) hyps) (.base 0) := .var (.there .here)
  let u : Tm (Ctx.ofHyps (sig := Sig1) hyps) (.base 0) := .var .here
  !InvTm.beq (focus t) (focus u) &&
    (match referenceCompareInv (sig := Sig1) Γ (.base 0) (focus t) (focus u) 256 with
     | .equal => true
     | _ => false)

example : inconsistentCollapsesCompare = true := by native_decide

/--
Handoff adversarial #9: at the root every hypothesis is new, so a generator
whose target is positive makes that positive a scheduled observation. The
counterfactual with the same hypothesis marked old schedules nothing, which is
exactly the observation that would have been dropped.
-/
def positiveGeneratorIsNewAtRoot : Bool :=
  let hyps : Array (Object 1) := #[.exp (.unit : Object 1) (.base 0)]
  let root : ReachCtx 1 := ⟨hyps, 0⟩
  let asOld : ReachCtx 1 := ⟨hyps, 1⟩
  (buildSchedule (runReachability root (.unit : Object 1))).size == 1 &&
    (buildSchedule (runReachability asOld (.unit : Object 1))).size == 0

example : positiveGeneratorIsNewAtRoot = true := by native_decide

/-! ### ICC canonicalizer -/

def iccCaseUnit :
    InvTm (translateCtx (sig := NumSig) (.coprod Number Number)) .unit :=
  .case (.var .here) .unit .unit

def iccCaseUnitCanonical : Bool :=
  match canonicalize iccCaseUnit with
  | .unit => true
  | _ => false

example : iccCaseUnitCanonical = true := by native_decide

/-- Nested case/case commuting + unit collapse. -/
def iccCaseCaseCanonical : Bool :=
  let hyps : Array (Object 4) := #[
    .coprod (.base 0) (.base 1),
    .coprod (.base 2) (.base 3)
  ]
  let Γ := Ctx.ofHyps (sig := ⟨4, #[]⟩) hyps
  let s : NegNeu Γ (.coprod (.base 0) (.base 1)) := .var (.there .here)
  let t : NegNeu Γ (.coprod (.base 2) (.base 3)) := .var .here
  let tm : InvTm Γ (.unit : Object 4) :=
    .case s
      (.case (NegNeu.weaken t) .unit .unit)
      (.case (NegNeu.weaken t) .unit .unit)
  match canonicalize tm with
  | .unit => true
  | _ => false

example : iccCaseCaseCanonical = true := by native_decide

/--
Handoff adversarial #11, with leaves that do not collapse: the two nestings of
an independent `case`/`case` pair canonicalize to the same term, and
canonicalization is idempotent on both. The second half is what the orientation
guard in `caseCommute` buys — without it the canonicalizer swaps the scrutinees
back on every pass.
-/
def iccCaseCaseOriented : Bool :=
  let hyps : Array (Object 5) := #[
    .base 0,
    .coprod (.base 1) (.base 2),
    .coprod (.base 3) (.base 4)
  ]
  let Γ := Ctx.ofHyps (sig := ⟨5, #[]⟩) hyps
  let s : NegNeu Γ (.coprod (.base 1) (.base 2)) := .var (.there .here)
  let t : NegNeu Γ (.coprod (.base 3) (.base 4)) := .var .here
  let leaf : ∀ L R : Object 5, InvTm (Γ ▻ L ▻ R) (.base 0) := fun _ _ =>
    .foc (.pos (.done (.neu (.var (.there (.there (.there (.there .here))))))))
  let x : InvTm Γ (.base 0) :=
    .case s
      (.case (NegNeu.weaken t) (leaf _ _) (leaf _ _))
      (.case (NegNeu.weaken t) (leaf _ _) (leaf _ _))
  let y : InvTm Γ (.base 0) :=
    .case t
      (.case (NegNeu.weaken s) (leaf _ _) (leaf _ _))
      (.case (NegNeu.weaken s) (leaf _ _) (leaf _ _))
  !InvTm.beq x y &&
    InvTm.beq (canonicalize x) (canonicalize y) &&
    InvTm.beq (canonicalize (canonicalize x)) (canonicalize x) &&
    InvTm.beq (canonicalize (canonicalize y)) (canonicalize y)

example : iccCaseCaseOriented = true := by native_decide

/-! ### Ordered-phase codes (design E) -/

/-- Right introductions encode under an empty positive worklist. -/
def encodeUnitPairLam : Bool :=
  let Sig : Signature := ⟨1, #[]⟩
  let Γ : Ctx Sig := .empty
  let ε : OriginEnv Γ := OriginEnv.empty
  let u : InvTm Γ (.unit : Object 1) := .unit
  let p : InvTm Γ (.prod (.unit) (.unit)) := .pair .unit .unit
  let l : InvTm Γ (.exp (.unit) (.unit)) := .lam .unit
  (encodeICC ε u).isSome &&
    (encodeICC ε p).isSome &&
    (encodeICC ε l).isSome

example : encodeUnitPairLam = true := by native_decide

/-- An already-outer case on a phase-entry hyp encodes under the worklist. -/
def encodeOuterCase : Bool :=
  let Sig : Signature := ⟨2, #[]⟩
  let hyps : Array (Object 2) := #[.base 0, .coprod (.base 0) (.base 0)]
  let n : NegNeu (Ctx.ofHyps (sig := Sig) hyps) (.coprod (.base 0) (.base 0)) :=
    .var .here
  let t : InvTm (Ctx.ofHyps (sig := Sig) hyps) (.base 0) :=
    .case n
      (.foc (.pos (.done (.neu (.var .here)))))
      (.foc (.pos (.done (.neu (.var .here)))))
  (encodeICCHyps t).isSome

example : encodeOuterCase = true := by native_decide

/-- Disordered `case`/`case` nestings encode to the same origin-keyed code. -/
def encodeCaseCaseAgree : Bool :=
  let hyps : Array (Object 5) := #[
    .base 0,
    .coprod (.base 1) (.base 2),
    .coprod (.base 3) (.base 4)
  ]
  let Sig : Signature := ⟨5, #[]⟩
  let s : NegNeu (Ctx.ofHyps (sig := Sig) hyps) (.coprod (.base 1) (.base 2)) :=
    .var (.there .here)
  let t : NegNeu (Ctx.ofHyps (sig := Sig) hyps) (.coprod (.base 3) (.base 4)) :=
    .var .here
  let leaf : ∀ L R : Object 5,
      InvTm (Ctx.ofHyps (sig := Sig) hyps ▻ L ▻ R) (.base 0) := fun _ _ =>
    .foc (.pos (.done (.neu (.var (.there (.there (.there (.there .here))))))))
  let x : InvTm (Ctx.ofHyps (sig := Sig) hyps) (.base 0) :=
    .case s
      (.case (NegNeu.weaken t) (leaf _ _) (leaf _ _))
      (.case (NegNeu.weaken t) (leaf _ _) (leaf _ _))
  let y : InvTm (Ctx.ofHyps (sig := Sig) hyps) (.base 0) :=
    .case t
      (.case (NegNeu.weaken s) (leaf _ _) (leaf _ _))
      (.case (NegNeu.weaken s) (leaf _ _) (leaf _ _))
  match encodeICCHyps x, encodeICCHyps y with
  | some cx, some cy => ICCCode.beq cx cy
  | _, _ => false

example : encodeCaseCaseAgree = true := by native_decide

/-- `case` distributed through `pair` encodes like the paired cases. -/
def encodeCasePairAgree : Bool :=
  let Sig : Signature := ⟨2, #[]⟩
  let hyps : Array (Object 2) := #[.unit, .coprod (.base 0) (.base 0)]
  let n : NegNeu (Ctx.ofHyps (sig := Sig) hyps) (.coprod (.base 0) (.base 0)) :=
    .var .here
  let leaf : InvTm (Ctx.ofHyps (sig := Sig) hyps ▻ (.base 0 : Object 2))
      (.unit : Object 2) := .unit
  let distributed : InvTm (Ctx.ofHyps (sig := Sig) hyps) (.prod (.unit) (.unit)) :=
    .pair (.case n leaf leaf) (.case n leaf leaf)
  let cased : InvTm (Ctx.ofHyps (sig := Sig) hyps) (.prod (.unit) (.unit)) :=
    .case n (.pair leaf leaf) (.pair leaf leaf)
  match encodeICCHyps distributed, encodeICCHyps cased with
  | some c₁, some c₂ => ICCCode.beq c₁ c₂
  | _, _ => false

example : encodeCasePairAgree = true := by native_decide

/-- Left-η: bare `.unit` and `.case x unit unit` share a code under a forced coprod. -/
def encodeCaseUnitAgree : Bool :=
  let Sig : Signature := ⟨1, #[]⟩
  let hyps : Array (Object 1) := #[.coprod (.base 0) (.base 0)]
  let n : NegNeu (Ctx.ofHyps (sig := Sig) hyps) (.coprod (.base 0) (.base 0)) :=
    .var .here
  let expanded : InvTm (Ctx.ofHyps (sig := Sig) hyps) (.unit : Object 1) :=
    .case n .unit .unit
  let contracted : InvTm (Ctx.ofHyps (sig := Sig) hyps) (.unit : Object 1) :=
    .unit
  match encodeICCHyps expanded, encodeICCHyps contracted with
  | some c₁, some c₂ => ICCCode.beq c₁ c₂
  | _, _ => false

example : encodeCaseUnitAgree = true := by native_decide

/--
Frozen counterexample for the *old* bottom-up `NegNeu.blt` canonicalizer.
Design E abandons repairing that path: do not re-canonicalize after exchange
and do not weaken this fixture. Unique order is obtained by `encodeICC` with
stable `Origin`s instead.
-/
def iccExchangeCanonNotUnique : Bool :=
  let Sig : Signature := ⟨1, #[]⟩
  let X : Object 1 := .base 0
  let S : Object 1 := .coprod X X
  let SS : Object 1 := .coprod S S
  let Γ : Ctx Sig := Ctx.empty ▻ X ▻ SS
  let Δ : Ctx Sig := Γ ▻ S ▻ S
  let x0 : NegNeu Γ X := .var (.there .here)
  let x1 := NegNeu.weaken (B := S) x0
  let x2 := NegNeu.weaken (B := S) x1
  let x3 := NegNeu.weaken (B := X) x2
  let x4 := NegNeu.weaken (B := X) x3
  let lf : InvTm (Δ ▻ X ▻ X) X := .foc (.pos (.done (.neu x4)))
  let body : InvTm Δ X :=
    .case (.var .here : NegNeu Δ S)
      (.case (NegNeu.weaken (.var (.there .here) : NegNeu Δ S)) lf lf)
      (.case (NegNeu.weaken (.var (.there .here) : NegNeu Δ S)) lf lf)
  let bodyEx :=
    InvTm.rename (Rename.exchange (sig := Sig) (Γ := Γ) (A := S) (B := S)) body
  let nW : NegNeu (Γ ▻ S) SS := NegNeu.weaken (.var .here : NegNeu Γ SS)
  let r := caseCommute nW bodyEx bodyEx
  let r2 := caseCommute nW (canonicalize bodyEx) (canonicalize bodyEx)
  InvTm.beq body (canonicalize body) &&
    !InvTm.beq bodyEx (canonicalize bodyEx) &&
    InvTm.beq r (canonicalize r) &&
    InvTm.beq r2 (canonicalize r2) &&
    !InvTm.beq r r2

example : iccExchangeCanonNotUnique = true := by native_decide

/-- Focusing produces well-focused terms (phase polarity OK). -/
def focusIdWellFocused : Bool :=
  match focus! (translate (sig := NumSig) (.id Number)) with
  | some t => t.wellFocused
  | none => false

example : focusIdWellFocused = true := by native_decide

/-! ### Candidate compare

M8 Slice 1: with root context wholly new and `checkOldInvariant` restored,
compares that enter a recursive saturation phase after observing a positive
currently return `invariantFailure` when opaque generators remain in `Γold`
and make that positive simply deducible without retrievability. Intended
semantic results are recorded in comments; unblocking is M8 corrections 5–6
(provenance / selection), not weakening the invariant again.
-/

/-- Root morphism context is wholly new (empty old fragment). -/
example :
    (translateCtx (sig := NumSig) Number).toReachCtx.newFrom = 0 := by
  native_decide

example :
    compareIntrinsic (sig := NumSig)
      (IntrinsicMorphism.id (sig := NumSig) Number)
      (IntrinsicMorphism.id (sig := NumSig) Number) =
      CandidateResult.equal := by
  native_decide

/-- Reference pipeline agrees with the private candidate on identity. -/
example :
    referenceCompare (sig := NumSig)
      (IntrinsicMorphism.id (sig := NumSig) Number)
      (IntrinsicMorphism.id (sig := NumSig) Number) =
      CandidateResult.equal := by
  native_decide

example :
    compareIntrinsic (sig := NumSig)
      (IntrinsicMorphism.discard (sig := NumSig) Number)
      (IntrinsicMorphism.discard (sig := NumSig) Number) =
      CandidateResult.equal := by
  native_decide

example :
    compareIntrinsic (sig := NumSig)
      (IntrinsicMorphism.left (sig := NumSig) Number Number)
      (IntrinsicMorphism.right (sig := NumSig) Number Number) =
      CandidateResult.different := by
  native_decide

/-! ### Hardening: demands, generators, exhaustion -/

/-- Demands from a focused identity are just the positive source atom. -/
def idDemandsHasNumber : Bool :=
  match focus! (translate (sig := NumSig) (.id Number)) with
  | some t => (collectDemands t).contains Number
  | none => false

example : idDemandsHasNumber = true := by native_decide

/-- Pair schedule for `id` vs `id` stays consistent (demand already retrievable). -/
def pairScheduleIdSize : Nat :=
  match focus! (translate (sig := NumSig) (.id Number)) with
  | some t => (pairSchedule (translateCtx Number).toReachCtx Number t t).1.size
  | none => 999

example : pairScheduleIdSize = 0 := by native_decide

/-- Distinct unconstrained generators remain unequal (intended: `different`). -/
example :
    compareIntrinsic (ofMorphism two) (ofMorphism three) =
      CandidateResult.invariantFailure := by
  native_decide

/-- Identity law (left): `id ∘ two = two` (intended: `equal`). -/
example :
    compareIntrinsic
      (ofMorphism ((Morphism.id .unit).compose two))
      (ofMorphism two) =
      CandidateResult.invariantFailure := by
  native_decide

/-- Product β (first): `⟨two, three⟩ ≫ first = two` (intended: `equal`). -/
example :
    compareIntrinsic
      (ofMorphism ((two.pair three).compose (Morphism.first (sig := NumSig) Number Number)))
      (ofMorphism two) =
      CandidateResult.invariantFailure := by
  native_decide

/-- Fuel exhaustion is not reported as `different`. -/
example :
    compareIntrinsic (fuel := 0)
      (IntrinsicMorphism.id (sig := NumSig) Number)
      (IntrinsicMorphism.id (sig := NumSig) Number) =
      CandidateResult.exhausted .saturate := by
  native_decide

/-! ### Unit / Never generator laws & observation order -/

/-- Signature: two gens `Unit → Unit` (should compare equal). -/
def UnitUnitSig : Signature where
  nBases := 1
  generators := #[⟨.unit, .unit⟩, ⟨.unit, .unit⟩]

example :
    compareIntrinsic (sig := UnitUnitSig)
      (.generator ⟨0, by decide⟩) (.generator ⟨1, by decide⟩) =
      CandidateResult.equal := by
  native_decide

/-- Signature: two gens `Never → Number` (should compare equal). -/
def NeverNumSig : Signature where
  nBases := 1
  generators := #[⟨.never, Number⟩, ⟨.never, Number⟩]

example :
    compareIntrinsic (sig := NeverNumSig)
      (.generator ⟨0, by decide⟩) (.generator ⟨1, by decide⟩) =
      CandidateResult.equal := by
  native_decide

/-- Unit η for apps: `f : 1 → X` with no unit hyp still fires when unit is η-available. -/
def unitAppCtx : ReachCtx 1 where
  hyps := #[.exp (.unit : Object 1) (.base 0)]
  newFrom := 0

example :
    isSimplyDeducible (runReachability unitAppCtx (.base 0)) (.base 0) = true := by
  native_decide

/--
Observation-order independence: observing the same atom via two schedule
entries in a shared schedule yields equal continuations (empty body).
-/
def obsOrderEqual : Bool :=
  let Γ : ReachCtx 2 := appCtx
  let goal : Object 2 := .base 1
  let cont : InvTm (Ctx.ofHyps (sig := Sig2) Γ.hyps) (.unit : Object 2) := .unit
  match saturateInv (sig := Sig2) (fuel := 128) Γ goal cont with
  | .ok t =>
    -- Intended: `.equal`. Slice 1: recursive old-invariant blocks.
    match compareInv (sig := Sig2) Γ goal t t (fuel := 128) with
    | .invariantFailure => true
    | _ => false
  | _ => false

example : obsOrderEqual = true := by native_decide

/-- Nested inconsistency: after observing `Y` from `s : X → 0` and `x : X`. -/
def nestedNeverCtx : ReachCtx 2 where
  hyps := #[
    .exp (.base 0) (.never : Object 2),
    .base 0
  ]
  newFrom := 1

example :
    (runReachability nestedNeverCtx (.base 0)).inconsistent = true := by
  native_decide

def nestedNeverAborts : Bool :=
  let cont : InvTm (Ctx.ofHyps (sig := Sig2) nestedNeverCtx.hyps) (.unit : Object 2) :=
    .unit
  match saturateInv (sig := Sig2) (fuel := 128) nestedNeverCtx (.unit : Object 2)
      cont with
  | .ok (.abort _) => true
  | _ => false

example : nestedNeverAborts = true := by native_decide

/-- Coproduct η-ish: `case` into unit (intended: `equal`). -/
example :
    compareIntrinsic (sig := NumSig)
      (IntrinsicMorphism.case
        (IntrinsicMorphism.discard (sig := NumSig) Number)
        (IntrinsicMorphism.discard (sig := NumSig) Number))
      (IntrinsicMorphism.discard (sig := NumSig) (.coprod Number Number)) =
      CandidateResult.invariantFailure := by
  native_decide

/-! ### Exact demands + remaining categorical laws -/

/-- Exact demand from a focused identity is the source variable. -/
def idExactIsHere : Bool :=
  match focus! (translate (sig := NumSig) (.id Number)) with
  | some t =>
    match collectExact t with
    | #[⟨P, n⟩] => P == Number && NegNeu.toRaw n == .var 0
    | _ => false
  | none => false

example : idExactIsHere = true := by native_decide

/-- Product β (second) (intended: `equal`). -/
example :
    compareIntrinsic
      (ofMorphism ((two.pair three).compose (Morphism.second (sig := NumSig) Number Number)))
      (ofMorphism three) =
      CandidateResult.invariantFailure := by
  native_decide

/-- Associativity via compare (intended: `equal`). -/
example :
    compareIntrinsic
      (ofMorphism
        ((two.compose (Morphism.id (sig := NumSig) Number)).compose
          (Morphism.id (sig := NumSig) Number)))
      (ofMorphism
        (two.compose
          ((Morphism.id (sig := NumSig) Number).compose
            (Morphism.id (sig := NumSig) Number)))) =
      CandidateResult.invariantFailure := by
  native_decide

/-- Exponential β: `curry(eval) = id` (intended: `equal`). -/
example :
    compareIntrinsic (sig := NumSig)
      (IntrinsicMorphism.curry (sig := NumSig)
        (IntrinsicMorphism.eval (sig := NumSig) Number Number))
      (IntrinsicMorphism.id (sig := NumSig) (.exp Number Number)) =
      CandidateResult.invariantFailure := by
  native_decide

/-- Signature with `Unit → Never` collapses distinct gens into Number. -/
def CollapseSig : Signature where
  nBases := 1
  generators := #[
    ⟨.unit, Number⟩,
    ⟨.unit, Number⟩,
    ⟨.unit, (.never : Object 1)⟩
  ]

/-- With `Unit → Never`, gens collapse (intended: `equal`). -/
def collapseTwoThree : CandidateResult :=
  compareIntrinsic (sig := CollapseSig)
    (.generator ⟨0, by decide⟩) (.generator ⟨1, by decide⟩)

example : collapseTwoThree = CandidateResult.equal := by
  native_decide

/-- Product η: `⟨first, second⟩ = id` (intended: `equal`). -/
example :
    compareIntrinsic (sig := NumSig)
      (IntrinsicMorphism.pair (sig := NumSig)
        (IntrinsicMorphism.first (sig := NumSig) Number Number)
        (IntrinsicMorphism.second (sig := NumSig) Number Number))
      (IntrinsicMorphism.id (sig := NumSig) (.prod Number Number)) =
      CandidateResult.invariantFailure := by
  native_decide

/-! ### Coproduct / exponential laws & observation fixtures -/

/-- Coproduct commuting conversion: `case` past `pair` (ICC). -/
def iccCasePairCanonical : Bool :=
  let n : NegNeu (translateCtx (sig := NumSig) (.coprod Number Number))
      (.coprod Number Number) := .var .here
  let t : InvTm (translateCtx (sig := NumSig) (.coprod Number Number) ▻ Number)
      (.prod (.unit : Object 1) (.unit : Object 1)) :=
    .pair .unit .unit
  let u : InvTm (translateCtx (sig := NumSig) (.coprod Number Number) ▻ Number)
      (.prod (.unit : Object 1) (.unit : Object 1)) :=
    .pair .unit .unit
  match canonicalize (.case n t u) with
  | .pair .unit .unit => true
  | _ => false

example : iccCasePairCanonical = true := by native_decide

/-- Coproduct β (left): `left ≫ case(id,id) = id`. -/
def coprodBetaLeft : CandidateResult :=
  compareIntrinsic (sig := NumSig) (fuel := 512)
    (IntrinsicMorphism.compose (sig := NumSig)
      (IntrinsicMorphism.left (sig := NumSig) Number Number)
      (IntrinsicMorphism.case (sig := NumSig)
        (IntrinsicMorphism.id (sig := NumSig) Number)
        (IntrinsicMorphism.id (sig := NumSig) Number)))
    (IntrinsicMorphism.id (sig := NumSig) Number)

example : coprodBetaLeft = CandidateResult.equal := by native_decide

/-- Coproduct β (right): `right ≫ case(id,id) = id`. -/
def coprodBetaRight : CandidateResult :=
  compareIntrinsic (sig := NumSig) (fuel := 512)
    (IntrinsicMorphism.compose (sig := NumSig)
      (IntrinsicMorphism.right (sig := NumSig) Number Number)
      (IntrinsicMorphism.case (sig := NumSig)
        (IntrinsicMorphism.id (sig := NumSig) Number)
        (IntrinsicMorphism.id (sig := NumSig) Number)))
    (IntrinsicMorphism.id (sig := NumSig) Number)

example : coprodBetaRight = CandidateResult.equal := by native_decide

/-- Coproduct η: `case(left, right) = id` (intended: `equal`). -/
def coprodEta : CandidateResult :=
  compareIntrinsic (sig := NumSig) (fuel := 512)
    (IntrinsicMorphism.case (sig := NumSig)
      (IntrinsicMorphism.left (sig := NumSig) Number Number)
      (IntrinsicMorphism.right (sig := NumSig) Number Number))
    (IntrinsicMorphism.id (sig := NumSig) (.coprod Number Number))

example : coprodEta = CandidateResult.invariantFailure := by native_decide

/-- Exponential η: `curry((f × id) ≫ eval) = f` at `id : A ⇒ B`. -/
def uncurryIdExp : IntrinsicMorphism NumSig
    (.prod (.exp Number Number) Number) Number :=
  IntrinsicMorphism.compose (sig := NumSig)
    (IntrinsicMorphism.pair (sig := NumSig)
      (IntrinsicMorphism.compose (sig := NumSig)
        (IntrinsicMorphism.first (sig := NumSig) (.exp Number Number) Number)
        (IntrinsicMorphism.id (sig := NumSig) (.exp Number Number)))
      (IntrinsicMorphism.second (sig := NumSig) (.exp Number Number) Number))
    (IntrinsicMorphism.eval (sig := NumSig) Number Number)

def expEta : CandidateResult :=
  compareIntrinsic (sig := NumSig) (fuel := 512)
    (IntrinsicMorphism.curry (sig := NumSig) uncurryIdExp)
    (IntrinsicMorphism.id (sig := NumSig) (.exp Number Number))

/-- Intended: `.equal` (curry/uncurry η). Still blocked on ICC / reference path. -/
example : expEta = CandidateResult.invariantFailure := by native_decide

/--
Independent neutrals `Y`, `Z` from `s : X→Y`, `t : X→Z`, `x : X`.
Shared schedule has both; order is subformula-table (not term demand order).
-/
def twoAppCtx : ReachCtx 3 where
  hyps := #[
    .exp (.base 0) (.base 1),
    .exp (.base 0) (.base 2),
    .base 0
  ]
  newFrom := 2

def twoAppScheduleSize : Nat :=
  (buildSchedule (runReachability twoAppCtx (.unit : Object 3))).size

example : twoAppScheduleSize = 2 := by native_decide

/-- Pair-directed compare under two independent observations. -/
def twoAppObsEqual : Bool :=
  let Γ := twoAppCtx
  let goal : Object 3 := .unit
  let cont : InvTm (Ctx.ofHyps (sig := Sig3) Γ.hyps) (.unit : Object 3) := .unit
  match compareInv (sig := Sig3) Γ goal cont cont (fuel := 256) with
  | .invariantFailure => true  -- intended: `.equal` (Slice 1 old-invariant)
  | _ => false

example : twoAppObsEqual = true := by native_decide

/--
Redundant repeated observation: duplicating the schedule list yields the same
raw saturated syntax as applying it once (second copy is still applied as
`letPos`, but compare of once-saturated continuations stays equal).
Here we check merge dedup: exact∪consistency schedule size equals consistency
size when the focused term contributes no extra exact positives.
-/
def redundantObsDedup : Bool :=
  let Γ := twoAppCtx
  let goal : Object 3 := .unit
  let cont : InvTm (Ctx.ofHyps (sig := Sig3) Γ.hyps) (.unit : Object 3) := .unit
  let σ := runReachability Γ goal
  let sched := buildSchedule σ
  match pairObs (sig := Sig3) Γ goal cont cont with
  | .ok entries _ => entries.size == sched.size && sched.size == 2
  | .invariantFailure => false

example : redundantObsDedup = true := by native_decide

/--
`x : X`, `s : X → X`: concrete observation chains are infinite, but the finite
subformula schedule stays empty (atom already retrievable from the hyp).
-/
def loopCtx : ReachCtx 1 where
  hyps := #[.exp (.base 0) (.base 0), .base 0]
  newFrom := 1

example :
    (buildSchedule (runReachability loopCtx (.unit : Object 1))).size = 0 := by
  native_decide

example :
    isSimplyDeducible (runReachability loopCtx (.base 0)) (.base 0) = true := by
  native_decide

example :
    isRetrievable (runReachability loopCtx (.base 0)) (.base 0) = true := by
  native_decide

/-- Higher-order generator returning a sum. -/
def HofSumSig : Signature where
  nBases := 1
  generators := #[⟨.unit, .coprod Number Number⟩]

def hofSumId : CandidateResult :=
  compareIntrinsic (sig := HofSumSig) (fuel := 512)
    (.generator ⟨0, by decide⟩) (.generator ⟨0, by decide⟩)

example : hofSumId = CandidateResult.equal := by native_decide

/--
`g ≫ case(left,right) = g` (sum η).
Closed once saturation commits a coproduct observation by substituting the
η patterns into one abstracted body: both sides then saturate to the same
`case`, and ICC contracts it.
-/
def hofSumEta : CandidateResult :=
  compareIntrinsic (sig := HofSumSig) (fuel := 512)
    (IntrinsicMorphism.compose (sig := HofSumSig)
      (.generator ⟨0, by decide⟩)
      (IntrinsicMorphism.case (sig := HofSumSig)
        (IntrinsicMorphism.left (sig := HofSumSig) Number Number)
        (IntrinsicMorphism.right (sig := HofSumSig) Number Number)))
    (.generator ⟨0, by decide⟩)

example : hofSumEta = CandidateResult.equal := by native_decide

/-- Higher-order generator returning a function. -/
def HofExpSig : Signature where
  nBases := 1
  generators := #[⟨.unit, .exp Number Number⟩]

def hofExpId : CandidateResult :=
  compareIntrinsic (sig := HofExpSig) (fuel := 512)
    (.generator ⟨0, by decide⟩) (.generator ⟨0, by decide⟩)

example : hofExpId = CandidateResult.equal := by native_decide

/-! ### M8 Slice 2: exact identity + newness -/

/-- Two distinct exact neutrals of the same positive type are both retained. -/
def twoExactHyps : Array (Object 2) := #[
  .exp (.base 0) (.base 1),
  .exp (.base 0) (.base 1),
  .base 0
]

def twoExactSameTyRetained : Bool :=
  let tm : Tm (Ctx.ofHyps (sig := Sig2) twoExactHyps)
      (.prod (.base 1) (.base 1)) :=
    .pair
      (.app (.var (.there (.there .here))) (.var .here))
      (.app (.var (.there .here)) (.var .here))
  match focus! tm with
  | some t =>
    let ys := (collectExact (sig := Sig2) t).filter (fun e => e.1 == .base 1)
    ys.size == 2 &&
      (match ys[0]?, ys[1]? with
      | some e0, some e1 => NegNeu.toRaw e0.2 != NegNeu.toRaw e1.2
      | _, _ => false)
  | none => false

example : twoExactSameTyRetained = true := by native_decide

/-- Pair schedule keeps both same-type exacts (not collapsed by type). -/
def twoExactBothScheduled : Bool :=
  let Γ : ReachCtx 2 := ⟨twoExactHyps, 2⟩
  let tm : Tm (Ctx.ofHyps (sig := Sig2) twoExactHyps)
      (.prod (.base 1) (.base 1)) :=
    .pair
      (.app (.var (.there (.there .here))) (.var .here))
      (.app (.var (.there .here)) (.var .here))
  match focus! tm with
  | some t =>
    match pairObs (sig := Sig2) Γ (.unit : Object 2) t t with
    | .ok entries _ =>
      let nExact :=
        entries.foldl (init := 0) fun n e =>
          match e with
          | .exact .. => n + 1
          | .consistency .. => n
      nExact == 2
    | .invariantFailure => false
  | none => false

example : twoExactBothScheduled = true := by native_decide

/-- Old-only exact observation is an invariant failure. -/
def oldOnlyExactInvariantFailure : Bool :=
  let hyps : Array (Object 1) := #[.exp (.unit : Object 1) (.base 0)]
  let Γ : ReachCtx 1 := ⟨hyps, 1⟩
  let tm : Tm (Ctx.ofHyps (sig := Sig1) hyps) (.base 0) :=
    .app (.var .here) .unit
  match focus! tm with
  | some t =>
    match pairObs (sig := Sig1) Γ (.base 0) t t with
    | .invariantFailure => true
    | .ok .. => false
  | none => false

example : oldOnlyExactInvariantFailure = true := by native_decide

/-! ### M8 Slice 3: canonical shared schedule -/

/-- Left/right swap yields the same canonical schedule. -/
def scheduleLeftRightSymmetric : Bool :=
  let tmL : Tm (Ctx.ofHyps (sig := Sig2) twoExactHyps)
      (.prod (.base 1) (.base 1)) :=
    .pair
      (.app (.var (.there (.there .here))) (.var .here))
      (.app (.var (.there .here)) (.var .here))
  let tmR : Tm (Ctx.ofHyps (sig := Sig2) twoExactHyps)
      (.prod (.base 1) (.base 1)) :=
    .pair
      (.app (.var (.there .here)) (.var .here))
      (.app (.var (.there (.there .here))) (.var .here))
  let Γ : ReachCtx 2 := ⟨twoExactHyps, 2⟩
  match focus! tmL, focus! tmR with
  | some t, some u =>
    match pairObs (sig := Sig2) Γ (.unit : Object 2) t u,
          pairObs (sig := Sig2) Γ (.unit : Object 2) u t with
    | .ok a _, .ok b _ => pairObsEntriesEq a b
    | _, _ => false
  | _, _ => false

example : scheduleLeftRightSymmetric = true := by native_decide

/-- Exact union is idempotent. -/
def exactUnionIdempotent : Bool :=
  let tm : Tm (Ctx.ofHyps (sig := Sig2) twoExactHyps)
      (.prod (.base 1) (.base 1)) :=
    .pair
      (.app (.var (.there (.there .here))) (.var .here))
      (.app (.var (.there .here)) (.var .here))
  match focus! tm with
  | some t =>
    let ex := collectExact (sig := Sig2) t
    (unionExact ex ex).size == ex.size
  | none => false

example : exactUnionIdempotent = true := by native_decide

/--
Dependent neutrals: `g (f x)` is scheduled after `f x`.
Context `f : X→Y`, `g : Y→Z`, `x : X`.
-/
def depAppHyps : Array (Object 3) := #[
  .exp (.base 0) (.base 1),
  .exp (.base 1) (.base 2),
  .base 0
]

def depAppOrdered : Bool :=
  let fx : Tm (Ctx.ofHyps (sig := Sig3) depAppHyps) (.base 1) :=
    .app (.var (.there (.there .here))) (.var .here)
  let tm : Tm (Ctx.ofHyps (sig := Sig3) depAppHyps)
      (.prod (.base 1) (.base 2)) :=
    .pair fx (.app (.var (.there .here)) fx)
  let Γ : ReachCtx 3 := ⟨depAppHyps, 2⟩
  match focus! tm with
  | some t =>
    match pairObs (sig := Sig3) Γ (.unit : Object 3) t t with
    | .ok entries _ =>
      Id.run do
        let mut iY : Option Nat := none
        let mut iZ : Option Nat := none
        for i in [:entries.size] do
          match entries[i]? with
          | some (.exact P _) =>
            if P == (.base 1 : Object 3) && iY.isNone then iY := some i
            if P == (.base 2 : Object 3) && iZ.isNone then iZ := some i
          | _ => pure ()
        match iY, iZ with
        | some y, some z => pure (decide (y < z))
        | _, _ => pure false
    | .invariantFailure => false
  | none => false

example : depAppOrdered = true := by native_decide

/--
Independent consistency observations: reversing the *canonical* schedule and
re-sorting recovers the same order (canonicalization is a projection).
-/
def reverseThenCanonicalSame : Bool :=
  let Γ := twoAppCtx
  let goal : Object 3 := .unit
  let cont : InvTm (Ctx.ofHyps (sig := Sig3) Γ.hyps) (.unit : Object 3) := .unit
  match pairObs (sig := Sig3) Γ goal cont cont with
  | .ok entries σ =>
    let rev := entries.reverse
    pairObsEntriesEq (canonicalizePairObsOrder σ rev) entries
  | .invariantFailure => false

example : reverseThenCanonicalSame = true := by native_decide

/-!
### Audit regressions (Steve §5)

Supporting evidence from the pre-M8 `compareSatRec` audit.
Intended semantics in comments; examples assert current executable behavior
until the foundation that fixes them lands. Not a replacement for the M8 handoff.
-/

/--
Audit 5.1 / handoff #12: schedule annotations are erased from structural spines.
Distinct schedules with the same body compare equal; length alone never decides.
-/
def auditSatRawErasesSchedule : Bool :=
  let s1 : Schedule 1 := ⟨#[((.base 0 : Object 1), Witness.ctxVar 0)]⟩
  let s2 : Schedule 1 := ⟨#[((.base 0 : Object 1), Witness.ctxVar 1)]⟩
  let t1 : InvTm (Ctx.empty : Ctx Sig1) (.unit : Object 1) :=
    .foc (.sat (.mk s1 .unit))
  let t2 : InvTm (Ctx.empty : Ctx Sig1) (.unit : Object 1) :=
    .foc (.sat (.mk s2 .unit))
  s1 != s2 && InvTm.toRaw t1 == InvTm.toRaw t2 && InvTm.toRaw t1 == .unit

example : auditSatRawErasesSchedule = true := by native_decide

/--
Audit 5.2 sharp: `x : X`, `f : 1 → X`, term `f ()`.
Exact `f()` remains scheduled even though `X` is retrievable from `x`.
-/
def auditExactKeptWhenRetrievable : Bool :=
  let hyps : Array (Object 1) := #[.base 0, .exp (.unit : Object 1) (.base 0)]
  let tm : Tm (Ctx.ofHyps (sig := Sig1) hyps) (.base 0) :=
    .app (.var .here) .unit
  match focus! tm with
  | none => false
  | some t =>
    let σ := runReachability (⟨hyps, 0⟩ : ReachCtx 1) (.base 0)
    let ex := collectExact (sig := Sig1) t
    let sel := selectExactObs (sig := Sig1) σ hyps ex
    ex.size == 1 && isRetrievable σ (.base 0) && sel.size == 1

example : auditExactKeptWhenRetrievable = true := by native_decide

/-- Audit 5.3: dependency order (also Slice 3 `depAppOrdered`). -/
example : depAppOrdered = true := by native_decide

/--
Audit 5.4: observing `n` on continuation `n` abstracts to `let x = n in x`.
-/
def auditAbstractionReplacesNeutral : Bool :=
  let hyps : Array (Object 1) := #[.exp (.unit : Object 1) (.base 0)]
  let Γ : ReachCtx 1 := ⟨hyps, 0⟩
  let tm : Tm (Ctx.ofHyps (sig := Sig1) hyps) (.base 0) :=
    .app (.var .here) .unit
  match focus! tm with
  | none => false
  | some t =>
    match pairObs (sig := Sig1) Γ (.base 0) t t with
    | .invariantFailure => false
    | .ok entries σ =>
      match applyPairObs (sig := Sig1) 64 σ hyps entries t with
      | .ok t' =>
        match InvTm.toRaw t' with
        | .letPos _ body => body == .pos (.neu (.var 0))
        | _ => false
      | _ => false

example : auditAbstractionReplacesNeutral = true := by native_decide

/--
Audit 5.5: `f : (X+Y) → Z`, `x : X` makes `Z` simply deducible via `f (inl x)`.
-/
def auditInlSynthesis : Bool :=
  let hyps : Array (Object 3) := #[
    .exp (.coprod (.base 0) (.base 1)) (.base 2),
    .base 0
  ]
  let Γ : ReachCtx 3 := ⟨hyps, 0⟩
  isSimplyDeducible (runReachability Γ (.base 2)) (.base 2)

example : auditInlSynthesis = true := by native_decide

/--
Handoff adversarial #7: `g : (X → Y) → Z`, `y : Y` derives `Z` via `g (λ _. y)`.
-/
def auditHoIdentityExpansion : Bool :=
  let hyps : Array (Object 3) := #[
    .exp (.exp (.base 0) (.base 1)) (.base 2),
    .base 1
  ]
  let Γ : ReachCtx 3 := ⟨hyps, 0⟩
  isSimplyDeducible (runReachability Γ (.base 2)) (.base 2)

example : auditHoIdentityExpansion = true := by native_decide

/--
Audit 5.6: hidden inconsistency via `f (inl x) : 0` collapses `a = b`.
-/
def auditHiddenInconsistency : Bool :=
  let hyps : Array (Object 3) := #[
    .exp (.coprod (.base 0) (.base 1)) (.never : Object 3),
    .base 0,
    .base 2,
    .base 2
  ]
  let Γ : ReachCtx 3 := ⟨hyps, 0⟩
  let t : InvTm (Ctx.ofHyps (sig := Sig3) hyps) (.base 2) :=
    .foc (.pos (.done (.neu (.var (.there .here)))))
  let u : InvTm (Ctx.ofHyps (sig := Sig3) hyps) (.base 2) :=
    .foc (.pos (.done (.neu (.var .here))))
  -- a = there.here (older Z), b = here (newer Z) under snoc … ▻ a ▻ b
  match compareInv (sig := Sig3) Γ (.base 2) t u (fuel := 64) with
  | .equal => true
  | _ => false

example : auditHiddenInconsistency = true := by native_decide

/-- Same hidden-`0` case on the reference comparator. -/
def auditHiddenInconsistencyRef : Bool :=
  let hyps : Array (Object 3) := #[
    .exp (.coprod (.base 0) (.base 1)) (.never : Object 3),
    .base 0,
    .base 2,
    .base 2
  ]
  let Γ : ReachCtx 3 := ⟨hyps, 0⟩
  let t : InvTm (Ctx.ofHyps (sig := Sig3) hyps) (.base 2) :=
    .foc (.pos (.done (.neu (.var (.there .here)))))
  let u : InvTm (Ctx.ofHyps (sig := Sig3) hyps) (.base 2) :=
    .foc (.pos (.done (.neu (.var .here))))
  match referenceCompareInv (sig := Sig3) Γ (.base 2) t u (fuel := 64) with
  | .equal => true
  | _ => false

example : auditHiddenInconsistencyRef = true := by native_decide

/-- Audit 5.7: fuel zero is exhaustion, never a semantic `.different`. -/
example :
    compareIntrinsic (fuel := 0)
      (IntrinsicMorphism.id (sig := NumSig) Number)
      (IntrinsicMorphism.id (sig := NumSig) Number) =
      CandidateResult.exhausted .saturate := by
  native_decide

/-! ### M8 8C: hereditary focusing invariants

`two` is the generator `q : Unit ⟶ Number`, so its translation is a spine
headed by a generator variable. These fixtures pin the properties that
Milestone 8C proves in general: focusing is total and phase-legal, its erasure
is `TmEq` to the input, and the generator spine comes through untouched.
-/

/-- Raw shape of the focused form of `two = q`. -/
def focusTwoRaw : RawFocused :=
  (focus (translateMorphism two)).toRaw

/--
Opacity, concretely. Focusing `q x` eta-expands the generator variable and then
contracts the expansion again, leaving the spine `app (var 3) unit`: the
argument is eta-expanded to the unit value, while the generator head — de
Bruijn index `3`, generator `0` seen through the source binder — is neither
reduced nor inspected.
-/
example : focusTwoRaw = .pos (.neu (.app (.var 3) .unit)) := by
  native_decide

/-- The focused output is phase-legal. -/
example : WellInv (focus (translateMorphism two)) :=
  focus_wellInv _

/-- The executable phase check agrees. -/
example : (focus (translateMorphism two)).wellFocused = true :=
  focus_wellFocused _

/-- Focusing preserves meaning: the erasure is `TmEq` to the term it came from. -/
example :
    TmEq (focus (translateMorphism two)).erase (translateMorphism two) :=
  focus_tmEq _

/-- Focusing a translated morphism recovers that morphism categorically. -/
example :
    IntrinsicDefEq
      (interpret (rootEnv (sig := NumSig) (.unit : Object 1))
        (focus (translate (ofMorphism two))).erase)
      (ofMorphism two) :=
  (focus_translate (ofMorphism two)).2

/--
Opacity in general: a spine headed by the generator variable is never
contracted by hereditary substitution for a later binder, and the result is
still headed by that same generator variable.
-/
example {A C : Object 1}
    (n : NegNeu (translateCtx (sig := NumSig) (.unit : Object 1) ▻ A) C)
    (h : n.HeadVar (.there (.there (genVar NumSig ⟨0, by decide⟩))))
    (v : InvTm (translateCtx (sig := NumSig) (.unit : Object 1)) A) :
    ∃ n' : NegNeu (translateCtx (sig := NumSig) (.unit : Object 1)) C,
      hsubstNeu n v = .neu n' ∧
        n'.HeadVar (.there (genVar NumSig ⟨0, by decide⟩)) :=
  hsubstNeu_opaque h v

end Gimbal.Equality.Fixtures
