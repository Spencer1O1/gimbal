/-
  Retained-state-indexed exact schedule (`CertifiedScheduleIx`).

  Parallel to legacy `CertifiedSchedule` / `PairEntry` / `ofHyps` indexing.
  Exact observation entries and remainder maps live in the actual EncodeIx
  context so `.obs` / `.split` origins are preserved by construction.

  **Coproduct clause restriction:** `certifiedScheduleIx_exactCoprod` currently
  lifts branch results from `split.pop` to `split` only when each summand is
  discharged by `forcedRule = .moveStable` (stable/atomic positive heads —
  bases and other non-`coprod`/`never` positives). Nested-coproduct summands
  require a generic forced-inversion helper (separate from schedule recursion).

  Does **not** replace legacy `PairEntry`, delete `CertifiedSchedule`, or
  change `applyObsNeu` / comparator. Consistency witnesses deferred.
-/

import Gimbal.Equality.ICCEncodeIx
import Gimbal.Equality.Saturation

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ## Exact entries at the actual context -/

/--
Exact observation schedule entry indexed by the real context `Γ`.
Does not mention `ofHyps` / hyp arrays; neutrals are already in `Γ`.
-/
structure IxExactEntry (Γ : Ctx sig) where
  P : Object sig.nBases
  neu : NegNeu Γ P

abbrev IxExactSchedule (Γ : Ctx sig) : Type := List (IxExactEntry Γ)

/-! ## Retained-state transitions (boundary → binder → boundary) -/

/-- After retaining a base observation: `bindObs` then `pop` restores the boundary. -/
def afterIxAtom {Γ : Ctx sig} (b : Fin sig.nBases)
    (s : EncodeIx (sig := sig) Γ) :
    EncodeIx (sig := sig) (Γ ▻ .base b) :=
  (s.bindObs (.base b)).pop

theorem afterIxAtom_boundary {Γ : Ctx sig} (b : Fin sig.nBases)
    (s : EncodeIx (sig := sig) Γ) (hb : AtSaturationBoundary s) :
    AtSaturationBoundary (afterIxAtom b s) :=
  bindObs_pop_boundary s (.base b) hb rfl

/-- Raw left split state (may carry a split worklist head). -/
def retainedSplitLIx {Γ : Ctx sig} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) Γ) :
    EncodeIx (sig := sig) (Γ ▻ .coprod L R ▻ L) :=
  (s.bindObs (.coprod L R)).splitL (obsEntryOf s (.coprod L R)) L

def retainedSplitRIx {Γ : Ctx sig} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) Γ) :
    EncodeIx (sig := sig) (Γ ▻ .coprod L R ▻ R) :=
  (s.bindObs (.coprod L R)).splitR (obsEntryOf s (.coprod L R)) R

/--
After left coproduct split: `bindObs` → `splitL` → `pop` restores the boundary
at `Γ ▻ .coprod L R ▻ L`, keeping the observation origin in `env` by construction.
-/
def afterIxCoprodL {Γ : Ctx sig} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) Γ) :
    EncodeIx (sig := sig) (Γ ▻ .coprod L R ▻ L) :=
  (retainedSplitLIx L R s).pop

def afterIxCoprodR {Γ : Ctx sig} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) Γ) :
    EncodeIx (sig := sig) (Γ ▻ .coprod L R ▻ R) :=
  (retainedSplitRIx L R s).pop

theorem retainedSplitLIx_ws_of_boundary {Γ : Ctx sig}
    (L R : Object sig.nBases) (s : EncodeIx (sig := sig) Γ)
    (hb : AtSaturationBoundary s) :
    (retainedSplitLIx L R s).ws =
      pushPos ([] : List (PosEntry sig))
        (.split (obsEntryOf s (.coprod L R)).origin false) L := by
  have hpos : objectPolarity (.coprod L R : Object sig.nBases) = .pos := by
    simp [objectPolarity_coprod]
  have hwsObs :
      (s.bindObs (.coprod L R)).ws = [obsEntryOf s (.coprod L R)] :=
    bindObs_ws_of_boundary s (.coprod L R) hb hpos
  simp only [retainedSplitLIx, EncodeIx.splitL, hwsObs, List.tail_cons]

theorem afterIxCoprodL_boundary {Γ : Ctx sig}
    (L R : Object sig.nBases) (s : EncodeIx (sig := sig) Γ)
    (hb : AtSaturationBoundary s) :
    AtSaturationBoundary (afterIxCoprodL L R s) := by
  have hws := retainedSplitLIx_ws_of_boundary L R s hb
  dsimp only [AtSaturationBoundary, afterIxCoprodL, EncodeIx.pop]
  rw [hws]
  dsimp only [pushPos]
  split
  · simp [List.mergeSort_singleton]
  · rfl

theorem retainedSplitRIx_ws_of_boundary {Γ : Ctx sig}
    (L R : Object sig.nBases) (s : EncodeIx (sig := sig) Γ)
    (hb : AtSaturationBoundary s) :
    (retainedSplitRIx L R s).ws =
      pushPos ([] : List (PosEntry sig))
        (.split (obsEntryOf s (.coprod L R)).origin true) R := by
  have hpos : objectPolarity (.coprod L R : Object sig.nBases) = .pos := by
    simp [objectPolarity_coprod]
  have hwsObs :
      (s.bindObs (.coprod L R)).ws = [obsEntryOf s (.coprod L R)] :=
    bindObs_ws_of_boundary s (.coprod L R) hb hpos
  simp only [retainedSplitRIx, EncodeIx.splitR, hwsObs, List.tail_cons]

theorem afterIxCoprodR_boundary {Γ : Ctx sig}
    (L R : Object sig.nBases) (s : EncodeIx (sig := sig) Γ)
    (hb : AtSaturationBoundary s) :
    AtSaturationBoundary (afterIxCoprodR L R s) := by
  have hws := retainedSplitRIx_ws_of_boundary L R s hb
  dsimp only [AtSaturationBoundary, afterIxCoprodR, EncodeIx.pop]
  rw [hws]
  dsimp only [pushPos]
  split
  · simp [List.mergeSort_singleton]
  · rfl

/-! ## Remainder maps (reuse `abstractAtom` / `abstractSum` at general `Γ`) -/

/--
Map remaining exact entries under a retained base observation binder.
Uses saturation’s `NegNeu.abstractAtom` (context-general); no `ofHyps` cast.
-/
def mapIxRestAtom {Γ : Ctx sig} (b : Fin sig.nBases)
    (nP : NegNeu Γ (.base b)) (rest : IxExactSchedule Γ) :
    IxExactSchedule (Γ ▻ .base b) :=
  let targetRaw := NegNeu.toRaw (NegNeu.weaken (B := .base b) nP)
  rest.map fun e =>
    ⟨e.P, NegNeu.abstractAtom (P := .base b) .here targetRaw (NegNeu.weaken e.neu)⟩

/--
Map remaining exact entries into the retained left split context
`Γ ▻ .coprod L R ▻ L`. Double-weaken then `abstractSum` — same operations as
`mapRestAbstractSumInl`, generalized off `ofHyps`.
-/
def mapIxRestCoprodL {Γ : Ctx sig} (L R : Object sig.nBases)
    (nSum : NegNeu Γ (.coprod L R)) (rest : IxExactSchedule Γ) :
    IxExactSchedule (Γ ▻ .coprod L R ▻ L) :=
  let targetRaw :=
    NegNeu.toRaw
      (NegNeu.weaken (B := L) (NegNeu.weaken (B := .coprod L R) nSum))
  rest.map fun e =>
    let n1 := NegNeu.weaken (B := .coprod L R) e.neu
    let n2 := NegNeu.weaken (B := L) n1
    ⟨e.P, NegNeu.abstractSum (B := L) .here targetRaw n2⟩

def mapIxRestCoprodR {Γ : Ctx sig} (L R : Object sig.nBases)
    (nSum : NegNeu Γ (.coprod L R)) (rest : IxExactSchedule Γ) :
    IxExactSchedule (Γ ▻ .coprod L R ▻ R) :=
  let targetRaw :=
    NegNeu.toRaw
      (NegNeu.weaken (B := R) (NegNeu.weaken (B := .coprod L R) nSum))
  rest.map fun e =>
    let n1 := NegNeu.weaken (B := .coprod L R) e.neu
    let n2 := NegNeu.weaken (B := R) n1
    ⟨e.P, NegNeu.abstractSum (B := R) .here targetRaw n2⟩

/-! ## `CertifiedScheduleIx` -/

/--
Proof-relevant consumption of an exact schedule fragment at a saturation
boundary, indexed by the actual EncodeIx state (not `ofHyps`).
-/
structure CertifiedScheduleIx {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ)
    (entries : IxExactSchedule Γ)
    (A : Object sig.nBases) where
  boundary : AtSaturationBoundary s
  produced : Produced s A

/-- Empty schedule: return the already-certified continuation unchanged. -/
def certifiedScheduleIx_nil {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hb : AtSaturationBoundary s) (cont : Produced s A) :
    CertifiedScheduleIx s [] A :=
  ⟨hb, cont⟩

/--
Exact base-atom clause: map remainder with `mapIxRestAtom`, take an arbitrary
recursive `CertifiedScheduleIx` at `afterIxAtom`, wrap with
`retainedAtomObsCertified` (origins preserved; state is definitionally
`(bindObs).pop`).
-/
def certifiedScheduleIx_exactAtom {Γ : Ctx sig} {b : Fin sig.nBases}
    {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hfr : forcedRule (sig := sig) s.ws A = .focus)
    (nP : NegNeu Γ (.base b))
    (rest : IxExactSchedule Γ)
    (rec : CertifiedScheduleIx (afterIxAtom b s) (mapIxRestAtom b nP rest) A) :
    CertifiedScheduleIx s (⟨.base b, nP⟩ :: rest) A :=
  let hb : AtSaturationBoundary s := atSaturationBoundary_of_forcedRule_focus s hfr
  ⟨hb, retainedAtomObsCertified s nP hb hfr rec.produced⟩

/-- Lift a boundary continuation at `splitL.pop` through `moveStable` to `splitL`. -/
def produced_splitL_of_pop {Γ : Ctx sig} {L R X : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hws : (retainedSplitLIx L R s).ws =
      [{ origin := .split (obsEntryOf s (.coprod L R)).origin false, ty := L }])
    (hfr : forcedRule (sig := sig)
        [{ origin := .split (obsEntryOf s (.coprod L R)).origin false, ty := L }] X =
      .moveStable
        { origin := .split (obsEntryOf s (.coprod L R)).origin false, ty := L })
    (p : Produced (afterIxCoprodL L R s) X) :
    Produced (retainedSplitLIx L R s) X :=
  produced_moveStable_singleton (retainedSplitLIx L R s)
    ⟨.split (obsEntryOf s (.coprod L R)).origin false, L⟩ hws hfr
    (by simpa [afterIxCoprodL] using p)

def produced_splitR_of_pop {Γ : Ctx sig} {L R X : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hws : (retainedSplitRIx L R s).ws =
      [{ origin := .split (obsEntryOf s (.coprod L R)).origin true, ty := R }])
    (hfr : forcedRule (sig := sig)
        [{ origin := .split (obsEntryOf s (.coprod L R)).origin true, ty := R }] X =
      .moveStable
        { origin := .split (obsEntryOf s (.coprod L R)).origin true, ty := R })
    (p : Produced (afterIxCoprodR L R s) X) :
    Produced (retainedSplitRIx L R s) X :=
  produced_moveStable_singleton (retainedSplitRIx L R s)
    ⟨.split (obsEntryOf s (.coprod L R)).origin true, R⟩ hws hfr
    (by simpa [afterIxCoprodR] using p)

/--
Exact coproduct clause (`moveStable` summands only): map remainder into both
retained split contexts, take arbitrary recursive `CertifiedScheduleIx` results
at `afterIxCoprodL/R` (= `split.pop`), lift via `moveStable` to `splitL/splitR`,
package with `retainedCoprodObsCertified`.

**Restriction:** `hfrL` / `hfrR` require `forcedRule = .moveStable` on each
summand head. Nested-coproduct summands are out of scope here — use
`certifiedForcedInvert` once it lands.
-/
def certifiedScheduleIx_exactCoprod_of_moveStableSummands
    {Γ : Ctx sig} {L R A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hfr : forcedRule (sig := sig) s.ws A = .focus)
    (nSum : NegNeu Γ (.coprod L R))
    (rest : IxExactSchedule Γ)
    (hwsL : (retainedSplitLIx L R s).ws =
      [{ origin := .split (obsEntryOf s (.coprod L R)).origin false, ty := L }])
    (hwsR : (retainedSplitRIx L R s).ws =
      [{ origin := .split (obsEntryOf s (.coprod L R)).origin true, ty := R }])
    (hfrL : forcedRule (sig := sig)
        [{ origin := .split (obsEntryOf s (.coprod L R)).origin false, ty := L }] A =
      .moveStable
        { origin := .split (obsEntryOf s (.coprod L R)).origin false, ty := L })
    (hfrR : forcedRule (sig := sig)
        [{ origin := .split (obsEntryOf s (.coprod L R)).origin true, ty := R }] A =
      .moveStable
        { origin := .split (obsEntryOf s (.coprod L R)).origin true, ty := R })
    (recL : CertifiedScheduleIx (afterIxCoprodL L R s)
      (mapIxRestCoprodL L R nSum rest) A)
    (recR : CertifiedScheduleIx (afterIxCoprodR L R s)
      (mapIxRestCoprodR L R nSum rest) A) :
    CertifiedScheduleIx s (⟨.coprod L R, nSum⟩ :: rest) A :=
  let hb : AtSaturationBoundary s := atSaturationBoundary_of_forcedRule_focus s hfr
  let left := produced_splitL_of_pop s hwsL hfrL recL.produced
  let right := produced_splitR_of_pop s hwsR hfrR recR.produced
  ⟨hb, retainedCoprodObsCertified s nSum hb hfr left right⟩

/-- Prefer `certifiedScheduleIx_exactCoprod_of_moveStableSummands` (name records the
summand restriction). This short alias is for the existing example call sites. -/
def certifiedScheduleIx_exactCoprod
    {Γ : Ctx sig} {L R A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hfr : forcedRule (sig := sig) s.ws A = .focus)
    (nSum : NegNeu Γ (.coprod L R))
    (rest : IxExactSchedule Γ)
    (hwsL : (retainedSplitLIx L R s).ws =
      [{ origin := .split (obsEntryOf s (.coprod L R)).origin false, ty := L }])
    (hwsR : (retainedSplitRIx L R s).ws =
      [{ origin := .split (obsEntryOf s (.coprod L R)).origin true, ty := R }])
    (hfrL : forcedRule (sig := sig)
        [{ origin := .split (obsEntryOf s (.coprod L R)).origin false, ty := L }] A =
      .moveStable
        { origin := .split (obsEntryOf s (.coprod L R)).origin false, ty := L })
    (hfrR : forcedRule (sig := sig)
        [{ origin := .split (obsEntryOf s (.coprod L R)).origin true, ty := R }] A =
      .moveStable
        { origin := .split (obsEntryOf s (.coprod L R)).origin true, ty := R })
    (recL : CertifiedScheduleIx (afterIxCoprodL L R s)
      (mapIxRestCoprodL L R nSum rest) A)
    (recR : CertifiedScheduleIx (afterIxCoprodR L R s)
      (mapIxRestCoprodR L R nSum rest) A) :
    CertifiedScheduleIx s (⟨.coprod L R, nSum⟩ :: rest) A :=
  certifiedScheduleIx_exactCoprod_of_moveStableSummands s hfr nSum rest
    hwsL hwsR hfrL hfrR recL recR

/-! ## Atom → coproduct example via `CertifiedScheduleIx` only -/

def TwoObsIxSig : Signature where
  nBases := 1
  generators := #[]

private abbrev AtomIx : Object TwoObsIxSig.nBases := .base ⟨0, by decide⟩
private abbrev SumIx : Object TwoObsIxSig.nBases := .coprod AtomIx AtomIx
private abbrev atomIxB : Fin TwoObsIxSig.nBases := ⟨0, by decide⟩

/-- Phase hyps kept only to build the entry EncodeIx; schedule proofs use `Γ`. -/
def twoObsIxHyps : Array (Object TwoObsIxSig.nBases) :=
  #[.exp .unit AtomIx, .exp .unit SumIx]

def twoObsIxΓ : Ctx TwoObsIxSig := Ctx.ofHyps (sig := TwoObsIxSig) twoObsIxHyps

def twoObsIxEntry : EncodeIx (sig := TwoObsIxSig) twoObsIxΓ :=
  EncodeIx.entry (sig := TwoObsIxSig) twoObsIxHyps

theorem twoObsIxEntry_boundary : AtSaturationBoundary twoObsIxEntry := by
  simp only [AtSaturationBoundary, twoObsIxEntry, EncodeIx.entry, twoObsIxHyps,
    OriginEnv.posWorklist, OriginEnv.posCollect]
  native_decide

theorem twoObsIx_forcedRule_entry :
    forcedRule (sig := TwoObsIxSig) twoObsIxEntry.ws SumIx = .focus := by
  simp only [twoObsIxEntry_boundary, forcedRule]

def twoObsIxAtom : NegNeu twoObsIxΓ AtomIx :=
  .app (.var (.there .here)) .unit

def twoObsIxSumOuter : NegNeu twoObsIxΓ SumIx :=
  .app (.var .here) .unit

def twoObsIxRest : IxExactSchedule twoObsIxΓ :=
  [⟨SumIx, twoObsIxSumOuter⟩]

def twoObsIxAfterAtom : EncodeIx (sig := TwoObsIxSig) (twoObsIxΓ ▻ AtomIx) :=
  afterIxAtom (sig := TwoObsIxSig) atomIxB twoObsIxEntry

theorem twoObsIxAfterAtom_boundary :
    AtSaturationBoundary twoObsIxAfterAtom :=
  afterIxAtom_boundary (sig := TwoObsIxSig) atomIxB twoObsIxEntry twoObsIxEntry_boundary

theorem twoObsIxAfterAtom_forcedRule :
    forcedRule (sig := TwoObsIxSig) twoObsIxAfterAtom.ws SumIx = .focus := by
  simp only [twoObsIxAfterAtom_boundary, forcedRule]

def twoObsIxRestMapped : IxExactSchedule (twoObsIxΓ ▻ AtomIx) :=
  mapIxRestAtom (sig := TwoObsIxSig) atomIxB twoObsIxAtom twoObsIxRest

/-- Mapped second observation under the retained atom binder. -/
def twoObsIxSum : NegNeu (twoObsIxΓ ▻ AtomIx) SumIx :=
  NegNeu.abstractAtom (P := AtomIx) .here
    (NegNeu.toRaw (NegNeu.weaken (B := AtomIx) twoObsIxAtom))
    (NegNeu.weaken (B := AtomIx) twoObsIxSumOuter)

theorem twoObsIxRestMapped_eq :
    twoObsIxRestMapped = [⟨SumIx, twoObsIxSum⟩] :=
  rfl

/-- Left identity branch written directly in the retained split context. -/
def twoObsIxBranchL :
    InvTm (twoObsIxΓ ▻ AtomIx ▻ SumIx ▻ AtomIx) SumIx :=
  .foc (.pos (.done (.inl (.neu (.var .here)))))

def twoObsIxBranchR :
    InvTm (twoObsIxΓ ▻ AtomIx ▻ SumIx ▻ AtomIx) SumIx :=
  .foc (.pos (.done (.inr (.neu (.var .here)))))

def twoObsIxAfterCoprodL : EncodeIx (sig := TwoObsIxSig)
    (twoObsIxΓ ▻ AtomIx ▻ SumIx ▻ AtomIx) :=
  afterIxCoprodL (sig := TwoObsIxSig) AtomIx AtomIx twoObsIxAfterAtom

def twoObsIxAfterCoprodR : EncodeIx (sig := TwoObsIxSig)
    (twoObsIxΓ ▻ AtomIx ▻ SumIx ▻ AtomIx) :=
  afterIxCoprodR (sig := TwoObsIxSig) AtomIx AtomIx twoObsIxAfterAtom

theorem twoObsIxAfterCoprodL_boundary :
    AtSaturationBoundary twoObsIxAfterCoprodL :=
  afterIxCoprodL_boundary (sig := TwoObsIxSig) AtomIx AtomIx twoObsIxAfterAtom
    twoObsIxAfterAtom_boundary

theorem twoObsIxAfterCoprodR_boundary :
    AtSaturationBoundary twoObsIxAfterCoprodR :=
  afterIxCoprodR_boundary (sig := TwoObsIxSig) AtomIx AtomIx twoObsIxAfterAtom
    twoObsIxAfterAtom_boundary

theorem twoObsIx_branchL_cert :
    InvCert twoObsIxAfterCoprodL twoObsIxBranchL := by
  change EncodeReady twoObsIxAfterCoprodL.ws twoObsIxAfterCoprodL.env
    twoObsIxAfterCoprodL.domNext twoObsIxAfterCoprodL.obsNext twoObsIxBranchL
  have hb := twoObsIxAfterCoprodL_boundary
  rw [show twoObsIxAfterCoprodL.ws = [] from hb]
  exact EncodeReady.focus (by simp [forcedRule]) (.pos (p := .inl (.neu (.var .here))))

theorem twoObsIx_branchR_cert :
    InvCert twoObsIxAfterCoprodR twoObsIxBranchR := by
  change EncodeReady twoObsIxAfterCoprodR.ws twoObsIxAfterCoprodR.env
    twoObsIxAfterCoprodR.domNext twoObsIxAfterCoprodR.obsNext twoObsIxBranchR
  have hb := twoObsIxAfterCoprodR_boundary
  rw [show twoObsIxAfterCoprodR.ws = [] from hb]
  exact EncodeReady.focus (by simp [forcedRule]) (.pos (p := .inr (.neu (.var .here))))

def twoObsIxBranchL_produced : Produced twoObsIxAfterCoprodL SumIx :=
  ⟨twoObsIxBranchL, twoObsIx_branchL_cert⟩

def twoObsIxBranchR_produced : Produced twoObsIxAfterCoprodR SumIx :=
  ⟨twoObsIxBranchR, twoObsIx_branchR_cert⟩

/-- Inner nil schedules for empty rest under each split. -/
def twoObsIxRecL :
    CertifiedScheduleIx (sig := TwoObsIxSig) twoObsIxAfterCoprodL
      (mapIxRestCoprodL AtomIx AtomIx twoObsIxSum []) SumIx :=
  certifiedScheduleIx_nil twoObsIxAfterCoprodL twoObsIxAfterCoprodL_boundary
    twoObsIxBranchL_produced

def twoObsIxRecR :
    CertifiedScheduleIx (sig := TwoObsIxSig) twoObsIxAfterCoprodR
      (mapIxRestCoprodR AtomIx AtomIx twoObsIxSum []) SumIx :=
  certifiedScheduleIx_nil twoObsIxAfterCoprodR twoObsIxAfterCoprodR_boundary
    twoObsIxBranchR_produced

theorem twoObsIx_splitL_ws :
    (retainedSplitLIx (sig := TwoObsIxSig) AtomIx AtomIx twoObsIxAfterAtom).ws =
      [{ origin := .split (obsEntryOf twoObsIxAfterAtom SumIx).origin false,
         ty := AtomIx }] := by
  rw [retainedSplitLIx_ws_of_boundary (sig := TwoObsIxSig) AtomIx AtomIx
    twoObsIxAfterAtom twoObsIxAfterAtom_boundary]
  simp [pushPos, AtomIx, objectPolarity, List.mergeSort_singleton]

theorem twoObsIx_splitR_ws :
    (retainedSplitRIx (sig := TwoObsIxSig) AtomIx AtomIx twoObsIxAfterAtom).ws =
      [{ origin := .split (obsEntryOf twoObsIxAfterAtom SumIx).origin true,
         ty := AtomIx }] := by
  rw [retainedSplitRIx_ws_of_boundary (sig := TwoObsIxSig) AtomIx AtomIx
    twoObsIxAfterAtom twoObsIxAfterAtom_boundary]
  simp [pushPos, AtomIx, objectPolarity, List.mergeSort_singleton]

theorem twoObsIx_splitL_moveStable :
    forcedRule (sig := TwoObsIxSig)
      [{ origin := .split (obsEntryOf twoObsIxAfterAtom SumIx).origin false,
         ty := AtomIx }]
      SumIx =
      .moveStable
        { origin := .split (obsEntryOf twoObsIxAfterAtom SumIx).origin false,
          ty := AtomIx } := by
  simp [forcedRule, AtomIx]

theorem twoObsIx_splitR_moveStable :
    forcedRule (sig := TwoObsIxSig)
      [{ origin := .split (obsEntryOf twoObsIxAfterAtom SumIx).origin true,
         ty := AtomIx }]
      SumIx =
      .moveStable
        { origin := .split (obsEntryOf twoObsIxAfterAtom SumIx).origin true,
          ty := AtomIx } := by
  simp [forcedRule, AtomIx]

/-- Inner exact-coproduct schedule at the post-atom boundary (empty remainder). -/
def twoObsIxInner :
    CertifiedScheduleIx (sig := TwoObsIxSig) twoObsIxAfterAtom
      twoObsIxRestMapped SumIx :=
  twoObsIxRestMapped_eq ▸
    certifiedScheduleIx_exactCoprod (sig := TwoObsIxSig) twoObsIxAfterAtom
      twoObsIxAfterAtom_forcedRule twoObsIxSum []
      twoObsIx_splitL_ws twoObsIx_splitR_ws
      twoObsIx_splitL_moveStable twoObsIx_splitR_moveStable
      twoObsIxRecL twoObsIxRecR

/-- Full atom → coproduct via retained-state-indexed clauses only. -/
def twoObsIxSchedule :
    CertifiedScheduleIx (sig := TwoObsIxSig) twoObsIxEntry
      (⟨AtomIx, twoObsIxAtom⟩ :: twoObsIxRest) SumIx :=
  certifiedScheduleIx_exactAtom (sig := TwoObsIxSig) twoObsIxEntry
    twoObsIx_forcedRule_entry twoObsIxAtom twoObsIxRest twoObsIxInner

def twoObsIxProduced : Produced twoObsIxEntry SumIx :=
  twoObsIxSchedule.produced

theorem twoObsIx_encodes :
    ∃ c, encodeICC (OriginEnv.ofHyps (sig := TwoObsIxSig) twoObsIxHyps)
        twoObsIxProduced.term = some c :=
  entryReady_encode_some (by
    simpa [EntryReady, InvCert, twoObsIxEntry, EncodeIx.entry, twoObsIxΓ] using
      twoObsIxProduced.cert)

def twoObsIxCode_hyps : Option (ICCCode twoObsIxΓ SumIx) :=
  encodeICCHyps (sig := TwoObsIxSig) twoObsIxProduced.term

theorem twoObsIxCode_hyps_isSome : twoObsIxCode_hyps.isSome = true := by
  native_decide

/-!
### Stop report — retained-state-indexed exact schedule

**Landed:** `IxExactEntry`, `mapIxRestAtom` / `mapIxRestCoprodL/R`,
`afterIxAtom` / `afterIxCoprodL/R`, `CertifiedScheduleIx` with nil, exact-atom,
and `certifiedScheduleIx_exactCoprod_of_moveStableSummands`. Example
`twoObsIxSchedule` uses only these.

**Explicit restriction:** coproduct branch lift is `moveStable` only (stable /
atomic summands). Nested-coproduct summands need `certifiedForcedInvert`.

Legacy `CertifiedSchedule` kept. Consistency / public evaluator deferred.
-/

end Equality
end Gimbal
