/-
  Retained-state-indexed exact schedule (`CertifiedScheduleIx`).

  Parallel to legacy `CertifiedSchedule` / `PairEntry` / `ofHyps` indexing.
  Exact observation entries and remainder maps live in the actual EncodeIx
  context so `.obs` / `.split` origins are preserved by construction.

  **Coproduct clause:** `certifiedScheduleIx_exactCoprod` drains each summand via
  peel-based `certifiedForcedInvert` (nested `leftCoprod` / `moveStable` /
  `leftNever`). `certifiedScheduleIx_exactCoprod_of_moveStableSummands` keeps the
  `WorklistMoveStableOnly` specialization (stable/atomic summand heads only).

  Never / inconsistent / consistency resolution land here: exact-never abort,
  top-level inconsistent delegation, and witness → `IxExactEntry` → existing
  exact clauses (no duplicated atom/coprod/never production).

  Does **not** replace legacy `PairEntry`, delete `CertifiedSchedule`, or
  change `applyObsNeu` / comparator. Full reachability adapter / EncodeTotal
  deferred.
-/

import Gimbal.Equality.ICCEncodeIx
import Gimbal.Equality.ICCEncodeEmbed
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

/-! ## Certified forced inversion (drain positive worklist)

Separate from schedule recursion: mirrors `forcedRule`, decreases
`worklistWeight s.ws`, and returns `Produced` at the actual EncodeIx.

* Empty worklist → return the boundary leaf.
* `moveStable` → recurse on `pop`, lift.
* `leftNever` → canonical `.abort` when `find?` resolves a never binder.
* `leftCoprod` → peel branches via `pushPos`/`weaken`, recurse, reassemble
  (`leftCoprod_unitEta` for goal `.unit`; `encodeReady_case_var_leftCoprod`
  when a general leaf transports).

**Non-unit `leftCoprod` leaf transport:** measure decreases on
`splitL`/`splitR` (`worklistWeight`). Full `produced_of_embedding` via
`encodeIxEmbedding_emptyWs_splitL/R` + `invCert_leftCoprod_peel` is packaged in
`certifiedForcedInvert`. Empty-worklist unused-binder branch embeddings use
`WellFormed.emptyWs` + `fresh_split`.
-/

/-- EncodeIx with the same env/counters as `s` but an empty worklist. -/
def emptyWsEncode {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ) :
    EncodeIx (sig := sig) Γ where
  ws := []
  env := s.env
  domNext := s.domNext
  obsNext := s.obsNext

theorem emptyWsEncode_boundary {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ) :
    AtSaturationBoundary (emptyWsEncode s) :=
  rfl

theorem emptyWsEncode_pop {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ) :
    emptyWsEncode s.pop = emptyWsEncode s :=
  rfl

theorem emptyWsEncode_eq_of_boundary {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (hb : AtSaturationBoundary s) :
    emptyWsEncode s = s := by
  cases s
  cases hb
  rfl

def forcedInvertMeasure {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ) : Nat :=
  worklistWeight s.ws

/-- Branch EncodeIx under forced `leftCoprod` (left summand). -/
def splitEncodeL {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ)
    (e : PosEntry sig) (tail : List (PosEntry sig)) (L : Object sig.nBases)
    (_hws : s.ws = e :: tail) :
    EncodeIx (sig := sig) (Γ ▻ L) where
  ws := pushPos tail (.split e.origin false) L
  env := OriginEnv.weaken (A := L) s.env (.split e.origin false)
  domNext := s.domNext
  obsNext := s.obsNext

def splitEncodeR {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ)
    (e : PosEntry sig) (tail : List (PosEntry sig)) (R : Object sig.nBases)
    (_hws : s.ws = e :: tail) :
    EncodeIx (sig := sig) (Γ ▻ R) where
  ws := pushPos tail (.split e.origin true) R
  env := OriginEnv.weaken (A := R) s.env (.split e.origin true)
  domNext := s.domNext
  obsNext := s.obsNext

/-- Unused-binder embedding: `emptyWsEncode s → emptyWsEncode (splitEncodeL …)`.

Requires `EncodeIx.WellFormed s` with `e` on the worklist head so
`fresh_split` / `ws_bounded` / `ws_in_env` discharge `weaken_unused`.
-/
theorem encodeIxEmbedding_emptyWs_splitL {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (L : Object sig.nBases)
    (hws : s.ws = e :: tail)
    (hwf : EncodeIx.WellFormed s) :
    EncodeIxEmbedding (Rename.weaken (A := L))
      (emptyWsEncode s)
      (emptyWsEncode (splitEncodeL s e tail L hws)) := by
  change EncodeIxEmbedding _ (emptyWsEncode s)
    ⟨[], OriginEnv.weaken (A := L) s.env (.split e.origin false), s.domNext, s.obsNext⟩
  have hempty : EncodeIx.WellFormed (emptyWsEncode s) := by
    simpa [emptyWsEncode] using EncodeIx.WellFormed.emptyWs hwf
  have hfresh : OriginEnv.Fresh (emptyWsEncode s).env (.split e.origin false) :=
    hwf.fresh_split (by simp [hws]) false
  have hb : Origin.counterBounded (.split e.origin false)
      (emptyWsEncode s).domNext (emptyWsEncode s).obsNext :=
    hwf.ws_bounded (by simp [hws])
  exact encodeIxEmbedding_weaken (emptyWsEncode s) (.split e.origin false) hempty
    hfresh hb
    (fun side => EncodeIx.WellFormed.fresh_of_fresh_parent hempty hfresh side)
    (fun p side heq => by
      cases heq
      obtain ⟨C, y, hy⟩ := hwf.ws_in_env (show e ∈ s.ws by simp [hws])
      exact ⟨C, y, hy⟩)
    (fun he => by cases he)

theorem encodeIxEmbedding_emptyWs_splitR {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (R : Object sig.nBases)
    (hws : s.ws = e :: tail)
    (hwf : EncodeIx.WellFormed s) :
    EncodeIxEmbedding (Rename.weaken (A := R))
      (emptyWsEncode s)
      (emptyWsEncode (splitEncodeR s e tail R hws)) := by
  change EncodeIxEmbedding _ (emptyWsEncode s)
    ⟨[], OriginEnv.weaken (A := R) s.env (.split e.origin true), s.domNext, s.obsNext⟩
  have hempty : EncodeIx.WellFormed (emptyWsEncode s) := by
    simpa [emptyWsEncode] using EncodeIx.WellFormed.emptyWs hwf
  have hfresh : OriginEnv.Fresh (emptyWsEncode s).env (.split e.origin true) :=
    hwf.fresh_split (by simp [hws]) true
  have hb : Origin.counterBounded (.split e.origin true)
      (emptyWsEncode s).domNext (emptyWsEncode s).obsNext :=
    hwf.ws_bounded (by simp [hws])
  exact encodeIxEmbedding_weaken (emptyWsEncode s) (.split e.origin true) hempty
    hfresh hb
    (fun side => EncodeIx.WellFormed.fresh_of_fresh_parent hempty hfresh side)
    (fun p side heq => by
      cases heq
      obtain ⟨C, y, hy⟩ := hwf.ws_in_env (show e ∈ s.ws by simp [hws])
      exact ⟨C, y, hy⟩)
    (fun he => by cases he)

/-- Peel-free leaf transport into a left split empty-worklist state. -/
def produced_emptyWs_splitL_noPeel {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (L : Object sig.nBases)
    (hws : s.ws = e :: tail)
    (hwf : EncodeIx.WellFormed s)
    (p : Produced (emptyWsEncode s) A)
    (h : EncodeReadyNoPeel (sig := sig) (emptyWsEncode s).ws
      (emptyWsEncode s).env (emptyWsEncode s).domNext (emptyWsEncode s).obsNext
      p.term) :
    Produced (emptyWsEncode (splitEncodeL s e tail L hws)) A :=
  produced_of_embedding_noPeel
    (encodeIxEmbedding_emptyWs_splitL s e tail L hws hwf) p h

def produced_emptyWs_splitR_noPeel {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (R : Object sig.nBases)
    (hws : s.ws = e :: tail)
    (hwf : EncodeIx.WellFormed s)
    (p : Produced (emptyWsEncode s) A)
    (h : EncodeReadyNoPeel (sig := sig) (emptyWsEncode s).ws
      (emptyWsEncode s).env (emptyWsEncode s).domNext (emptyWsEncode s).obsNext
      p.term) :
    Produced (emptyWsEncode (splitEncodeR s e tail R hws)) A :=
  produced_of_embedding_noPeel
    (encodeIxEmbedding_emptyWs_splitR s e tail R hws hwf) p h

/-- Full leaf transport into a left split empty-worklist state (peel-capable). -/
def produced_emptyWs_splitL {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (L : Object sig.nBases)
    (hws : s.ws = e :: tail)
    (hwf : EncodeIx.WellFormed s)
    (p : Produced (emptyWsEncode s) A) :
    Produced (emptyWsEncode (splitEncodeL s e tail L hws)) A :=
  produced_of_embedding
    (encodeIxEmbedding_emptyWs_splitL s e tail L hws hwf) p

def produced_emptyWs_splitR {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (R : Object sig.nBases)
    (hws : s.ws = e :: tail)
    (hwf : EncodeIx.WellFormed s)
    (p : Produced (emptyWsEncode s) A) :
    Produced (emptyWsEncode (splitEncodeR s e tail R hws)) A :=
  produced_of_embedding
    (encodeIxEmbedding_emptyWs_splitR s e tail R hws hwf) p

theorem splitEncodeL_eq_splitL {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (L : Object sig.nBases)
    (hws : s.ws = e :: tail) :
    splitEncodeL s e tail L hws = s.splitL e L := by
  cases s with
  | mk ws env d o =>
    change ws = e :: tail at hws
    subst hws
    rfl

theorem splitEncodeR_eq_splitR {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (R : Object sig.nBases)
    (hws : s.ws = e :: tail) :
    splitEncodeR s e tail R hws = s.splitR e R := by
  cases s with
  | mk ws env d o =>
    change ws = e :: tail at hws
    subst hws
    rfl

theorem WellFormed_splitEncodeL {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (L : Object sig.nBases)
    (hws : s.ws = e :: tail) (hwf : EncodeIx.WellFormed s) :
    EncodeIx.WellFormed (splitEncodeL s e tail L hws) := by
  simpa [splitEncodeL_eq_splitL s e tail L hws] using
    EncodeIx.WellFormed.splitL hwf e tail L hws

theorem WellFormed_splitEncodeR {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (R : Object sig.nBases)
    (hws : s.ws = e :: tail) (hwf : EncodeIx.WellFormed s) :
    EncodeIx.WellFormed (splitEncodeR s e tail R hws) := by
  simpa [splitEncodeR_eq_splitR s e tail R hws] using
    EncodeIx.WellFormed.splitR hwf e tail R hws

theorem forcedInvertMeasure_pop_lt {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig) (tail : List (PosEntry sig))
    (hws : s.ws = e :: tail) :
    forcedInvertMeasure s.pop < forcedInvertMeasure s := by
  simp only [forcedInvertMeasure, EncodeIx.pop, hws, List.tail_cons, worklistWeight_cons]
  have := objectWeight_pos e.ty
  omega

theorem forcedInvertMeasure_splitL_lt {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig) (tail : List (PosEntry sig))
    (L R : Object sig.nBases) (_hws : s.ws = e :: tail)
    (hty : e.ty = .coprod L R) :
    forcedInvertMeasure (splitEncodeL s e tail L _hws) < forcedInvertMeasure s := by
  simp only [forcedInvertMeasure, splitEncodeL, _hws, worklistWeight_cons, hty,
    objectWeight]
  rw [worklistWeight_pushPos]
  split
  · have := objectWeight_pos R; omega
  · have := objectWeight_pos L; have := objectWeight_pos R; omega

theorem forcedInvertMeasure_splitR_lt {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig) (tail : List (PosEntry sig))
    (L R : Object sig.nBases) (_hws : s.ws = e :: tail)
    (hty : e.ty = .coprod L R) :
    forcedInvertMeasure (splitEncodeR s e tail R _hws) < forcedInvertMeasure s := by
  simp only [forcedInvertMeasure, splitEncodeR, _hws, worklistWeight_cons, hty,
    objectWeight]
  rw [worklistWeight_pushPos]
  split
  · have := objectWeight_pos L; omega
  · have := objectWeight_pos L; have := objectWeight_pos R; omega

/-- Lift through `moveStable` for an arbitrary head (not only singleton). -/
def produced_moveStable {Γ : Ctx sig} {X : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig))
    (hws : s.ws = e :: tail)
    (hfr : forcedRule (sig := sig) (e :: tail) X = .moveStable e)
    (cont : Produced s.pop X) : Produced s X where
  term := cont.term
  cert := by
    have ht : EncodeReady (sig := sig) tail s.env s.domNext s.obsNext cont.term := by
      simpa [EncodeIx.pop, InvCert, hws] using cont.cert
    have hmove : EncodeReady (sig := sig) (e :: tail) s.env s.domNext s.obsNext
        cont.term :=
      EncodeReady.moveStable hfr ht
    change EncodeReady s.ws s.env s.domNext s.obsNext cont.term
    rw [hws]
    exact hmove

/-- Unit leaf at any empty-worklist EncodeIx. -/
def produced_unit_emptyWs {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ) :
    Produced (emptyWsEncode s) (.unit : Object sig.nBases) where
  term := .unit
  cert := by
    simpa [emptyWsEncode, InvCert] using
      encodeReady_unit_nil (sig := sig) s.env s.domNext s.obsNext

/--
Goal-polymorphic forced inversion mirroring `forcedRule`.

* `[]` — cast the boundary leaf via `emptyWsEncode_eq_of_boundary`
* `moveStable` — IH on `pop`, lift with `produced_moveStable`
* `leftNever` — canonical `.abort` when `find?` resolves a never binder
* `leftCoprod` — transport leaf via full `produced_emptyWs_splitL/R`, IH on both
  splits, reassemble with `invCert_leftCoprod_peel` / `find?` +
  `peelCaseOuter_case_var_hit`

Returns `none` when a forced origin cannot be resolved via `find?` (or the
recovered type mismatches the forced connective). Requires
`EncodeIx.WellFormed` for unused-binder embeddings / Fresh.
-/
def certifiedForcedInvert {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hwf : EncodeIx.WellFormed s)
    (leaf : Produced (emptyWsEncode s) A) :
    Option (Produced s A) :=
  match hws : s.ws with
  | [] =>
      some (emptyWsEncode_eq_of_boundary s (by simp [AtSaturationBoundary, hws]) ▸ leaf)
  | e :: tail =>
      match hty : e.ty with
      | .never =>
          match hfind : OriginEnv.find? s.env e.origin with
          | some ⟨P, x⟩ =>
              if hP : P = (.never : Object sig.nBases) then
                some ⟨.abort (NegNeu.cast hP (.var x)), by
                  change EncodeReady s.ws s.env s.domNext s.obsNext _
                  rw [hws]
                  exact encodeReady_abort_leftNever s.env e tail s.domNext s.obsNext
                    (NegNeu.cast hP (.var x)) hty⟩
              else
                none
          | none => none
      | .coprod L R =>
          let sL := splitEncodeL s e tail L (by simp [hws])
          let sR := splitEncodeR s e tail R (by simp [hws])
          let hwfL : EncodeIx.WellFormed sL :=
            WellFormed_splitEncodeL s e tail L (by simp [hws]) hwf
          let hwfR : EncodeIx.WellFormed sR :=
            WellFormed_splitEncodeR s e tail R (by simp [hws]) hwf
          let leafL :=
            produced_emptyWs_splitL s e tail L (by simp [hws]) hwf leaf
          let leafR :=
            produced_emptyWs_splitR s e tail R (by simp [hws]) hwf leaf
          match certifiedForcedInvert sL hwfL leafL,
                certifiedForcedInvert sR hwfR leafR with
          | some pL, some pR =>
              match hfind : OriginEnv.find? s.env e.origin with
              | some ⟨P, x⟩ =>
                  if hP : P = .coprod L R then
                    let x' : Var Γ (.coprod L R) := hP ▸ x
                    have heq : s.env x' = e.origin :=
                      OriginEnv.find?_eq_some_eq s.env e.origin x' (by
                        subst hP; exact hfind)
                    let body : InvTm Γ A := .case (.var x') pL.term pR.term
                    have hfr : forcedRule (sig := sig) (e :: tail) A =
                        .leftCoprod e L R := by
                      simp [forcedRule, hty]
                    have hpeel :
                        peelCaseOuter s.env e.origin body =
                          some ⟨L, R, .var x', pL.term, pR.term⟩ :=
                      peelCaseOuter_case_var_hit s.env e.origin x' pL.term pR.term heq
                    some ⟨body, by
                      change EncodeReady s.ws s.env s.domNext s.obsNext body
                      rw [hws]
                      exact
                        (invCert_leftCoprod_peel (sig := sig) (ws := tail) e
                          (.var x') pL.term pR.term body hfr hpeel
                          (by simpa [splitEncodeL, sL, InvCert] using pL.cert)
                          (by simpa [splitEncodeR, sR, InvCert] using pR.cert))⟩
                  else
                    none
              | none => none
          | _, _ => none
      | .base _ | .unit | .prod _ _ | .exp _ _ =>
          have hfr : forcedRule (sig := sig) (e :: tail) A = .moveStable e := by
            simp only [forcedRule, hty]
          let hleaf : Produced (emptyWsEncode s.pop) A := by
            simpa [emptyWsEncode_pop] using leaf
          match certifiedForcedInvert s.pop (EncodeIx.WellFormed.pop hwf) hleaf with
          | some cont =>
              some (produced_moveStable s e tail (by simp [hws])
                (by simpa [hws] using hfr) cont)
          | none => none
termination_by forcedInvertMeasure s
decreasing_by
  · exact forcedInvertMeasure_splitL_lt s e tail L R (by simp [hws]) hty
  · exact forcedInvertMeasure_splitR_lt s e tail L R (by simp [hws]) hty
  · exact forcedInvertMeasure_pop_lt s e tail (by simp [hws])
  · exact forcedInvertMeasure_pop_lt s e tail (by simp [hws])
  · exact forcedInvertMeasure_pop_lt s e tail (by simp [hws])
  · exact forcedInvertMeasure_pop_lt s e tail (by simp [hws])

/-- Convenience: forced invert when `find?` / peel succeed. -/
def certifiedForcedInvert_get {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hwf : EncodeIx.WellFormed s)
    (leaf : Produced (emptyWsEncode s) A)
    (h : (certifiedForcedInvert s hwf leaf).isSome = true) :
    Produced s A :=
  (certifiedForcedInvert s hwf leaf).get h

/-- No coproduct heads on the worklist (all discharged by `moveStable` / empty). -/
def WorklistMoveStableOnly (ws : List (PosEntry sig)) : Prop :=
  ∀ e ∈ ws, (∀ L R, e.ty ≠ .coprod L R) ∧ e.ty ≠ (.never : Object sig.nBases)

theorem WorklistMoveStableOnly_tail {e : PosEntry sig} {tail : List (PosEntry sig)}
    (h : WorklistMoveStableOnly (e :: tail)) : WorklistMoveStableOnly tail :=
  fun e' he' => h e' (List.Mem.tail _ he')

theorem WorklistMoveStableOnly_forcedRule_moveStable
    {e : PosEntry sig} {tail : List (PosEntry sig)} {A : Object sig.nBases}
    (h : WorklistMoveStableOnly (e :: tail)) :
    forcedRule (sig := sig) (e :: tail) A = .moveStable e := by
  have ⟨hc, hn⟩ := h e (List.Mem.head _)
  simp only [forcedRule]
  cases hty : e.ty <;> first
    | exact False.elim (hn hty)
    | exact False.elim (hc _ _ hty)
    | rfl

/--
Forced inversion along `moveStable` only (stable/atomic positive heads).
Used by `certifiedScheduleIx_exactCoprod` to drain each summand after split.
-/
def certifiedForcedInvert_moveStableOnly {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (leaf : Produced (emptyWsEncode s) A)
    (hws : WorklistMoveStableOnly s.ws) :
    Produced s A :=
  match hlist : s.ws with
  | [] =>
      emptyWsEncode_eq_of_boundary s (by simp [AtSaturationBoundary, hlist]) ▸ leaf
  | e :: tail =>
      let hfr := WorklistMoveStableOnly_forcedRule_moveStable (by simpa [hlist] using hws)
      let hleaf : Produced (emptyWsEncode s.pop) A := by
        simpa [emptyWsEncode_pop] using leaf
      let ih := certifiedForcedInvert_moveStableOnly s.pop hleaf
        (by simpa [EncodeIx.pop, hlist] using WorklistMoveStableOnly_tail (by simpa [hlist] using hws))
      produced_moveStable s e tail (by simp [hlist]) (by simpa [hlist] using hfr) ih
termination_by forcedInvertMeasure s
decreasing_by
  simp only [forcedInvertMeasure, EncodeIx.pop, hlist, List.tail_cons, worklistWeight_cons]
  have := objectWeight_pos e.ty
  omega

/--
Certificate that `.unit` is encode-ready under forced inversion of `s`
(`moveStable` / `leftCoprod_unitEta`). Uses `PLift` so the package lives in `Type`.
-/
def UnitForcedCert {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ) : Type :=
  PLift (EncodeReady (sig := sig) s.ws s.env s.domNext s.obsNext
    (.unit : InvTm Γ .unit))

def UnitForcedCert.toProduced {Γ : Ctx sig} {s : EncodeIx (sig := sig) Γ}
    (c : UnitForcedCert s) : Produced s (.unit : Object sig.nBases) where
  term := .unit
  cert := c.down

/--
Unit-goal forced inversion mirroring `forcedRule` (`moveStable` / `leftCoprod_unitEta`).
Does not cover `leftNever` (see `certifiedForcedInvert_unit?`).
-/
def certifiedForcedInvert_unit_eta? {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) :
    Option (UnitForcedCert s) :=
  match hws : s.ws with
  | [] =>
      some ⟨by
        simpa [hws] using
          encodeReady_unit_nil (sig := sig) s.env s.domNext s.obsNext⟩
  | e :: tail =>
      match hty : e.ty with
      | .never => none
      | .coprod L R =>
          let sL := splitEncodeL s e tail L (by simp [hws])
          let sR := splitEncodeR s e tail R (by simp [hws])
          match certifiedForcedInvert_unit_eta? sL, certifiedForcedInvert_unit_eta? sR with
          | some cL, some cR =>
              match hfind : OriginEnv.find? s.env e.origin with
              | some ⟨P, x⟩ =>
                  if hP : P = .coprod L R then
                    let x' : Var Γ (.coprod L R) := hP ▸ x
                    have heq : s.env x' = e.origin :=
                      OriginEnv.find?_eq_some_eq s.env e.origin x' (by
                        subst hP; exact hfind)
                    have hit : (s.env x' == e.origin) = true := by
                      simp [heq]
                    have hfr : forcedRule (sig := sig) (e :: tail)
                        (.unit : Object sig.nBases) = .leftCoprod e L R := by
                      simp [forcedRule, hty]
                    have hfind' :
                        OriginEnv.find? s.env e.origin =
                          some ⟨.coprod L R, x'⟩ := by
                      subst hP; exact hfind
                    some ⟨by
                      change EncodeReady s.ws s.env s.domNext s.obsNext _
                      rw [hws]
                      exact EncodeReady.leftCoprod_unitEta hfr hfind' hit
                        (by simpa [splitEncodeL, sL] using cL.down)
                        (by simpa [splitEncodeR, sR] using cR.down)⟩
                  else
                    none
              | none => none
          | _, _ => none
      | .base _ | .unit | .prod _ _ | .exp _ _ =>
          have hfr : forcedRule (sig := sig) (e :: tail) (.unit : Object sig.nBases) =
              .moveStable e := by
            simp only [forcedRule, hty]
          match certifiedForcedInvert_unit_eta? s.pop with
          | some c =>
              some ⟨by
                change EncodeReady s.ws s.env s.domNext s.obsNext _
                rw [hws]
                exact EncodeReady.moveStable hfr (by
                  simpa [EncodeIx.pop, hws] using c.down)⟩
          | none => none
termination_by forcedInvertMeasure s
decreasing_by
  · exact forcedInvertMeasure_splitL_lt s e tail L R (by simp [hws]) hty
  · exact forcedInvertMeasure_splitR_lt s e tail L R (by simp [hws]) hty
  · exact forcedInvertMeasure_pop_lt s e tail (by simp [hws])
  · exact forcedInvertMeasure_pop_lt s e tail (by simp [hws])
  · exact forcedInvertMeasure_pop_lt s e tail (by simp [hws])
  · exact forcedInvertMeasure_pop_lt s e tail (by simp [hws])

/--
Unit-goal forced inversion mirroring `forcedRule`, including nested `leftCoprod`.
`leftNever` returns the canonical `.abort` terminal; other rules certify `.unit`.
Returns `none` if a forced origin cannot be resolved via `find?`.
-/
def certifiedForcedInvert_unit? {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) :
    Option (Produced s (.unit : Object sig.nBases)) :=
  match hws : s.ws with
  | e :: tail =>
      match hty : e.ty with
      | .never =>
          match hfind : OriginEnv.find? s.env e.origin with
          | some ⟨P, x⟩ =>
              if hP : P = (.never : Object sig.nBases) then
                some ⟨.abort (NegNeu.cast hP (.var x)), by
                  change EncodeReady s.ws s.env s.domNext s.obsNext _
                  rw [hws]
                  exact encodeReady_abort_leftNever s.env e tail s.domNext s.obsNext
                    (NegNeu.cast hP (.var x)) hty⟩
              else
                none
          | none => none
      | _ =>
          (certifiedForcedInvert_unit_eta? s).map UnitForcedCert.toProduced
  | [] =>
      (certifiedForcedInvert_unit_eta? s).map UnitForcedCert.toProduced

/-- Convenience: unit invert when `find?` succeeds (retained split/obs states). -/
def certifiedForcedInvert_unit {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ)
    (h : (certifiedForcedInvert_unit? s).isSome = true) :
    Produced s (.unit : Object sig.nBases) :=
  (certifiedForcedInvert_unit? s).get h

theorem emptyWsEncode_eq_afterIxCoprodL {Γ : Ctx sig} {L R : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hws : (retainedSplitLIx L R s).ws =
      [{ origin := .split (obsEntryOf s (.coprod L R)).origin false, ty := L }]) :
    emptyWsEncode (retainedSplitLIx L R s) = afterIxCoprodL L R s := by
  simp only [emptyWsEncode, afterIxCoprodL, EncodeIx.pop, hws, List.tail_cons]

theorem emptyWsEncode_eq_afterIxCoprodR {Γ : Ctx sig} {L R : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hws : (retainedSplitRIx L R s).ws =
      [{ origin := .split (obsEntryOf s (.coprod L R)).origin true, ty := R }]) :
    emptyWsEncode (retainedSplitRIx L R s) = afterIxCoprodR L R s := by
  simp only [emptyWsEncode, afterIxCoprodR, EncodeIx.pop, hws, List.tail_cons]

/--
Exact coproduct clause (moveStable-summand specialization): map remainder into
both retained split contexts, take recursive `CertifiedScheduleIx` at
`afterIxCoprodL/R`, lift each summand through
`certifiedForcedInvert_moveStableOnly`, package with `retainedCoprodObsCertified`.

**Restriction:** `hstableL` / `hstableR` require each summand worklist to be
`WorklistMoveStableOnly`. Prefer `certifiedScheduleIx_exactCoprod` when summands
may carry nested coproducts.
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
    (hstableL : WorklistMoveStableOnly (retainedSplitLIx L R s).ws)
    (hstableR : WorklistMoveStableOnly (retainedSplitRIx L R s).ws)
    (recL : CertifiedScheduleIx (afterIxCoprodL L R s)
      (mapIxRestCoprodL L R nSum rest) A)
    (recR : CertifiedScheduleIx (afterIxCoprodR L R s)
      (mapIxRestCoprodR L R nSum rest) A) :
    CertifiedScheduleIx s (⟨.coprod L R, nSum⟩ :: rest) A :=
  let hb : AtSaturationBoundary s := atSaturationBoundary_of_forcedRule_focus s hfr
  let leafL : Produced (emptyWsEncode (retainedSplitLIx L R s)) A :=
    Produced.castState (emptyWsEncode_eq_afterIxCoprodL s hwsL).symm recL.produced
  let leafR : Produced (emptyWsEncode (retainedSplitRIx L R s)) A :=
    Produced.castState (emptyWsEncode_eq_afterIxCoprodR s hwsR).symm recR.produced
  let left := certifiedForcedInvert_moveStableOnly (retainedSplitLIx L R s) leafL hstableL
  let right := certifiedForcedInvert_moveStableOnly (retainedSplitRIx L R s) leafR hstableR
  ⟨hb, retainedCoprodObsCertified s nSum hb hfr left right⟩

/--
Exact coproduct clause: drain each retained summand via peel-based
`certifiedForcedInvert` (supports nested `leftCoprod`), then package with
`retainedCoprodObsCertified`.

`hinvL` / `hinvR` witness that forced invert succeeds (`find?` resolves forced
origins). Failure modes of `certifiedForcedInvert` are documented there.
-/
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
    (hwfL : EncodeIx.WellFormed (retainedSplitLIx L R s))
    (hwfR : EncodeIx.WellFormed (retainedSplitRIx L R s))
    (recL : CertifiedScheduleIx (afterIxCoprodL L R s)
      (mapIxRestCoprodL L R nSum rest) A)
    (recR : CertifiedScheduleIx (afterIxCoprodR L R s)
      (mapIxRestCoprodR L R nSum rest) A)
    (hinvL :
      (certifiedForcedInvert (retainedSplitLIx L R s) hwfL
        (Produced.castState (emptyWsEncode_eq_afterIxCoprodL s hwsL).symm
          recL.produced)).isSome = true)
    (hinvR :
      (certifiedForcedInvert (retainedSplitRIx L R s) hwfR
        (Produced.castState (emptyWsEncode_eq_afterIxCoprodR s hwsR).symm
          recR.produced)).isSome = true) :
    CertifiedScheduleIx s (⟨.coprod L R, nSum⟩ :: rest) A :=
  let hb : AtSaturationBoundary s := atSaturationBoundary_of_forcedRule_focus s hfr
  let leafL : Produced (emptyWsEncode (retainedSplitLIx L R s)) A :=
    Produced.castState (emptyWsEncode_eq_afterIxCoprodL s hwsL).symm recL.produced
  let leafR : Produced (emptyWsEncode (retainedSplitRIx L R s)) A :=
    Produced.castState (emptyWsEncode_eq_afterIxCoprodR s hwsR).symm recR.produced
  let left := certifiedForcedInvert_get (retainedSplitLIx L R s) hwfL leafL hinvL
  let right := certifiedForcedInvert_get (retainedSplitRIx L R s) hwfR leafR hinvR
  ⟨hb, retainedCoprodObsCertified s nSum hb hfr left right⟩

/-! ## Exact never + inconsistent + consistency resolution -/

/--
Exact never clause: consume `NegNeu Γ .never`, produce canonical `.abort`.
Matches `applyObsNeu`'s never arm — `rest` is not consumed (irrelevant once
inconsistency is observed). Readiness/encoding via `retainedNeverObsCertified`
(`EncodeReady.abortFocus`).
-/
def certifiedScheduleIx_exactNever {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hfr : forcedRule (sig := sig) s.ws A = .focus)
    (nNever : NegNeu Γ .never)
    (rest : IxExactSchedule Γ) :
    CertifiedScheduleIx s (⟨.never, nNever⟩ :: rest) A :=
  let hb : AtSaturationBoundary s := atSaturationBoundary_of_forcedRule_focus s hfr
  -- `rest` intentionally unused: abort discards remaining schedule entries.
  let _ := rest
  ⟨hb, retainedNeverObsCertified s nNever hb hfr⟩

/--
Top-level inconsistent path: a never-typed neutral (e.g. from `neuOfType`)
delegates to the same certified exact-never core. Schedule `entries` are ignored,
matching `applyPairObs` / `applyFixedSchedule` when `σ.inconsistent`.
-/
def certifiedScheduleIx_inconsistent {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hfr : forcedRule (sig := sig) s.ws A = .focus)
    (nNever : NegNeu Γ .never)
    (entries : IxExactSchedule Γ) :
    CertifiedScheduleIx s entries A :=
  let hb : AtSaturationBoundary s := atSaturationBoundary_of_forcedRule_focus s hfr
  let _ := entries
  ⟨hb, retainedNeverObsCertified s nNever hb hfr⟩

/--
Resolve a consistency witness to an `IxExactEntry` when reconstruction succeeds.
No readiness or encodability premise. Returns `none` when reconstruction fails
or the recovered type mismatches `P` — totality is **not** assumed (8D).
-/
def ixExactEntry_of_consistencyWitness (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (P : Object sig.nBases) (w : Witness) :
    Option (IxExactEntry (Ctx.ofHyps (sig := sig) hyps)) :=
  match reconstructWitness fuel σ hyps w with
  | some ⟨P', n⟩ =>
      if hP : P' = P then
        some ⟨P, hP ▸ n⟩
      else
        none
  | none => none

/--
Conditional correctness: successful reconstruction yields a well-phased neutral
of type `P`. Does not prove reconstruction always succeeds.
-/
theorem ixExactEntry_of_consistencyWitness_correct (fuel : Nat)
    (σ : ReachState sig.nBases) (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases) (w : Witness)
    {e : IxExactEntry (Ctx.ofHyps (sig := sig) hyps)}
    (h : ixExactEntry_of_consistencyWitness (sig := sig) fuel σ hyps P w = some e) :
    e.P = P ∧ WellNeg e.neu := by
  simp only [ixExactEntry_of_consistencyWitness] at h
  split at h
  · next P' n hrec =>
      split at h
      · next hP =>
          cases h
          subst hP
          exact ⟨rfl, wellNeg_reconstructWitness fuel σ hyps w hrec⟩
      · cases h
  · cases h

/--
8D obligation (open): reconstruction of a consistency witness always succeeds
with the declared type. Not assumed by the retained schedule core.
-/
def ReconstructWitnessTotal (sig : Signature) : Prop :=
  ∀ (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (P : Object sig.nBases) (w : Witness),
    ∃ (n : NegNeu (Ctx.ofHyps (sig := sig) hyps) P),
      reconstructWitness fuel σ hyps w = some ⟨P, n⟩

/--
Consistency → exact never: after successful witness reconstruction to `.never`,
delegate to `certifiedScheduleIx_exactNever` (no duplicated abort production).
-/
def certifiedScheduleIx_consistencyNever {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hfr : forcedRule (sig := sig) s.ws A = .focus)
    (nNever : NegNeu Γ .never)
    (rest : IxExactSchedule Γ) :
    CertifiedScheduleIx s (⟨.never, nNever⟩ :: rest) A :=
  certifiedScheduleIx_exactNever s hfr nNever rest

/--
Consistency → exact atom: after successful witness reconstruction to `.base b`,
delegate to `certifiedScheduleIx_exactAtom` (no duplicated letPos production).
-/
def certifiedScheduleIx_consistencyAtom {Γ : Ctx sig} {b : Fin sig.nBases}
    {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hfr : forcedRule (sig := sig) s.ws A = .focus)
    (nP : NegNeu Γ (.base b))
    (rest : IxExactSchedule Γ)
    (rec : CertifiedScheduleIx (afterIxAtom b s) (mapIxRestAtom b nP rest) A) :
    CertifiedScheduleIx s (⟨.base b, nP⟩ :: rest) A :=
  certifiedScheduleIx_exactAtom s hfr nP rest rec

/--
Consistency → exact coproduct: after successful witness reconstruction to
`.coprod L R`, delegate to `certifiedScheduleIx_exactCoprod`.
-/
def certifiedScheduleIx_consistencyCoprod {Γ : Ctx sig}
    {L R A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (hfr : forcedRule (sig := sig) s.ws A = .focus)
    (nSum : NegNeu Γ (.coprod L R))
    (rest : IxExactSchedule Γ)
    (hwsL : (retainedSplitLIx L R s).ws =
      [{ origin := .split (obsEntryOf s (.coprod L R)).origin false, ty := L }])
    (hwsR : (retainedSplitRIx L R s).ws =
      [{ origin := .split (obsEntryOf s (.coprod L R)).origin true, ty := R }])
    (hwfL : EncodeIx.WellFormed (retainedSplitLIx L R s))
    (hwfR : EncodeIx.WellFormed (retainedSplitRIx L R s))
    (recL : CertifiedScheduleIx (afterIxCoprodL L R s)
      (mapIxRestCoprodL L R nSum rest) A)
    (recR : CertifiedScheduleIx (afterIxCoprodR L R s)
      (mapIxRestCoprodR L R nSum rest) A)
    (hinvL :
      (certifiedForcedInvert (retainedSplitLIx L R s) hwfL
        (Produced.castState (emptyWsEncode_eq_afterIxCoprodL s hwsL).symm
          recL.produced)).isSome = true)
    (hinvR :
      (certifiedForcedInvert (retainedSplitRIx L R s) hwfR
        (Produced.castState (emptyWsEncode_eq_afterIxCoprodR s hwsR).symm
          recR.produced)).isSome = true) :
    CertifiedScheduleIx s (⟨.coprod L R, nSum⟩ :: rest) A :=
  certifiedScheduleIx_exactCoprod s hfr nSum rest hwsL hwsR hwfL hwfR
    recL recR hinvL hinvR

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

theorem twoObsIx_splitL_moveStableOnly :
    WorklistMoveStableOnly
      (retainedSplitLIx (sig := TwoObsIxSig) AtomIx AtomIx twoObsIxAfterAtom).ws := by
  intro e he
  rw [twoObsIx_splitL_ws] at he
  cases he with
  | head =>
      refine ⟨?_, by simp [AtomIx]⟩
      intro L R h
      cases h
  | tail _ h =>
      cases h

theorem twoObsIx_splitR_moveStableOnly :
    WorklistMoveStableOnly
      (retainedSplitRIx (sig := TwoObsIxSig) AtomIx AtomIx twoObsIxAfterAtom).ws := by
  intro e he
  rw [twoObsIx_splitR_ws] at he
  cases he with
  | head =>
      refine ⟨?_, by simp [AtomIx]⟩
      intro L R h
      cases h
  | tail _ h =>
      cases h

/-- Inner exact-coproduct schedule at the post-atom boundary (empty remainder). -/
def twoObsIxInner :
    CertifiedScheduleIx (sig := TwoObsIxSig) twoObsIxAfterAtom
      twoObsIxRestMapped SumIx :=
  twoObsIxRestMapped_eq ▸
    certifiedScheduleIx_exactCoprod_of_moveStableSummands (sig := TwoObsIxSig)
      twoObsIxAfterAtom
      twoObsIxAfterAtom_forcedRule twoObsIxSum []
      twoObsIx_splitL_ws twoObsIx_splitR_ws
      twoObsIx_splitL_moveStableOnly twoObsIx_splitR_moveStableOnly
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

/-! ## Nested coproduct fixture: `P = (A + B) + C`

Forced-inversion only (empty schedule). Every positive head is drained by
`certifiedForcedInvert` / `certifiedForcedInvert_unit?` mirroring `forcedRule`;
no nesting-depth constructors.
-/

def NestedIxSig : Signature where
  nBases := 3
  generators := #[]

private abbrev NestedA : Object NestedIxSig.nBases := .base ⟨0, by decide⟩
private abbrev NestedB : Object NestedIxSig.nBases := .base ⟨1, by decide⟩
private abbrev NestedC : Object NestedIxSig.nBases := .base ⟨2, by decide⟩
private abbrev NestedInner : Object NestedIxSig.nBases := .coprod NestedA NestedB
private abbrev NestedP : Object NestedIxSig.nBases := .coprod NestedInner NestedC

/-- Empty well-formed seed used to build the retained-obs nested state. -/
def nestedIxEmpty : EncodeIx (sig := NestedIxSig) Ctx.empty where
  ws := []
  env := OriginEnv.empty
  domNext := 0
  obsNext := 0

theorem nestedIxEmpty_wf : EncodeIx.WellFormed nestedIxEmpty where
  env_wf := OriginEnv.WellFormed.empty
  env_bounded := fun x => nomatch x
  ws_bounded := fun he => by cases he
  ws_in_env := fun he => by cases he
  ws_nodup := List.nodup_nil
  ws_split_fresh := fun he _ => by cases he
  split_parent_live := fun x _ _ _ => nomatch x

/-- Boundary state that has just retained observation `P = (A+B)+C`. -/
def nestedIxAfterObs : EncodeIx (sig := NestedIxSig) (Ctx.empty ▻ NestedP) :=
  nestedIxEmpty.bindObs NestedP

theorem nestedIxAfterObs_eq :
    nestedIxAfterObs =
      ⟨[⟨.obs (sig := NestedIxSig) 0, NestedP⟩],
        OriginEnv.weaken (A := NestedP) OriginEnv.empty (.obs (sig := NestedIxSig) 0),
        0, 1⟩ := by
  simp [nestedIxAfterObs, nestedIxEmpty, EncodeIx.bindObs, pushPos, NestedP,
    objectPolarity_coprod, List.mergeSort_singleton]

theorem nestedIxAfterObs_wf : EncodeIx.WellFormed nestedIxAfterObs :=
  EncodeIx.WellFormed.bindObs nestedIxEmpty_wf NestedP

theorem nestedIxAfterObs_forcedRule :
    forcedRule (sig := NestedIxSig) nestedIxAfterObs.ws (.unit : Object NestedIxSig.nBases) =
      .leftCoprod ⟨.obs (sig := NestedIxSig) 0, NestedP⟩ NestedInner NestedC := by
  simp [forcedRule, nestedIxAfterObs_eq, NestedP, NestedInner]

/-- Left summand state after the outer leftCoprod step: head is nested `A+B`. -/
def nestedIxSplitInner : EncodeIx (sig := NestedIxSig)
    (Ctx.empty ▻ NestedP ▻ NestedInner) :=
  splitEncodeL nestedIxAfterObs ⟨.obs (sig := NestedIxSig) 0, NestedP⟩ [] NestedInner
    (by simp [nestedIxAfterObs_eq])

/-- Right summand state after the outer leftCoprod step: head is atomic `C`. -/
def nestedIxSplitC : EncodeIx (sig := NestedIxSig)
    (Ctx.empty ▻ NestedP ▻ NestedC) :=
  splitEncodeR nestedIxAfterObs ⟨.obs (sig := NestedIxSig) 0, NestedP⟩ [] NestedC
    (by simp [nestedIxAfterObs_eq])

theorem nestedIxSplitInner_ws :
    nestedIxSplitInner.ws =
      [{ origin := .split (.obs (sig := NestedIxSig) 0) false, ty := NestedInner }] := by
  simp [nestedIxSplitInner, splitEncodeL, pushPos, NestedInner, objectPolarity,
    List.mergeSort_singleton]

theorem nestedIxSplitC_ws :
    nestedIxSplitC.ws =
      [{ origin := .split (.obs (sig := NestedIxSig) 0) true, ty := NestedC }] := by
  simp [nestedIxSplitC, splitEncodeR, pushPos, NestedC, objectPolarity,
    List.mergeSort_singleton]

theorem nestedIxSplitInner_forcedRule :
    forcedRule (sig := NestedIxSig) nestedIxSplitInner.ws
      (.unit : Object NestedIxSig.nBases) =
      .leftCoprod ⟨.split (.obs (sig := NestedIxSig) 0) false, NestedInner⟩
        NestedA NestedB := by
  simp [forcedRule, nestedIxSplitInner_ws, NestedInner]

theorem nestedIxSplitC_forcedRule :
    forcedRule (sig := NestedIxSig) nestedIxSplitC.ws
      (.unit : Object NestedIxSig.nBases) =
      .moveStable ⟨.split (.obs (sig := NestedIxSig) 0) true, NestedC⟩ := by
  simp [forcedRule, nestedIxSplitC_ws, NestedC]

/-- Atomic left-left leaf after draining nested `A+B`. -/
def nestedIxLeafA : EncodeIx (sig := NestedIxSig)
    (Ctx.empty ▻ NestedP ▻ NestedInner ▻ NestedA) :=
  splitEncodeL nestedIxSplitInner
    ⟨.split (.obs (sig := NestedIxSig) 0) false, NestedInner⟩ [] NestedA
    (by simp [nestedIxSplitInner_ws])

def nestedIxLeafB : EncodeIx (sig := NestedIxSig)
    (Ctx.empty ▻ NestedP ▻ NestedInner ▻ NestedB) :=
  splitEncodeR nestedIxSplitInner
    ⟨.split (.obs (sig := NestedIxSig) 0) false, NestedInner⟩ [] NestedB
    (by simp [nestedIxSplitInner_ws])

theorem nestedIxLeafA_boundary :
    AtSaturationBoundary (nestedIxLeafA.pop) := by
  simp [AtSaturationBoundary, nestedIxLeafA, splitEncodeL, EncodeIx.pop, pushPos,
    NestedA, objectPolarity, List.mergeSort_singleton]

theorem nestedIxLeafB_boundary :
    AtSaturationBoundary (nestedIxLeafB.pop) := by
  simp [AtSaturationBoundary, nestedIxLeafB, splitEncodeR, EncodeIx.pop, pushPos,
    NestedB, objectPolarity, List.mergeSort_singleton]

theorem nestedIxSplitC_pop_boundary :
    AtSaturationBoundary nestedIxSplitC.pop := by
  simp [AtSaturationBoundary, nestedIxSplitC_ws, EncodeIx.pop]

/-- Full nested invert at the retained obs state reaches a certified `.unit`. -/
theorem nestedIx_unit_forcedInvert_isSome :
    (certifiedForcedInvert_unit? (sig := NestedIxSig) nestedIxAfterObs).isSome = true := by
  native_decide

def nestedIxUnitProduced :
    Produced nestedIxAfterObs (.unit : Object NestedIxSig.nBases) :=
  certifiedForcedInvert_unit nestedIxAfterObs nestedIx_unit_forcedInvert_isSome

/-- Compositional branch readiness: each atomic leaf's pop is a saturation boundary. -/
theorem nestedIx_branches_reach_boundary :
    AtSaturationBoundary nestedIxLeafA.pop ∧
    AtSaturationBoundary nestedIxLeafB.pop ∧
    AtSaturationBoundary nestedIxSplitC.pop :=
  ⟨nestedIxLeafA_boundary, nestedIxLeafB_boundary, nestedIxSplitC_pop_boundary⟩

/-! ### Non-unit nested invert: goal `NestedA` via unused atom binder -/

/-- Unused atom binder; NestedA is available as `.here` for the non-unit leaf. -/
def nestedIxAtomBase : EncodeIx (sig := NestedIxSig) (Ctx.empty ▻ NestedA) where
  ws := []
  env := OriginEnv.weaken (A := NestedA) OriginEnv.empty (.hyp (sig := NestedIxSig) 0)
  domNext := 0
  obsNext := 0

theorem nestedIxAtomBase_wf : EncodeIx.WellFormed nestedIxAtomBase :=
  EncodeIx.WellFormed.weaken_unused (B := NestedA) nestedIxEmpty_wf
    (.hyp (sig := NestedIxSig) 0)
    (OriginEnv.Fresh.empty _)
    (Origin.counterBounded_hyp (sig := NestedIxSig) 0 0 0)
    (fun _ => OriginEnv.Fresh.empty _)
    (fun _ _ heq => by cases heq)
    (fun he => by cases he)

/-- Retained obs `P` over an unused NestedA binder (non-unit goal carrier). -/
def nestedIxNonUnitAfterObs : EncodeIx (sig := NestedIxSig)
    (Ctx.empty ▻ NestedA ▻ NestedP) :=
  nestedIxAtomBase.bindObs NestedP

theorem nestedIxNonUnitAfterObs_wf :
    EncodeIx.WellFormed nestedIxNonUnitAfterObs :=
  EncodeIx.WellFormed.bindObs nestedIxAtomBase_wf NestedP

theorem nestedIxNonUnitAfterObs_ws :
    nestedIxNonUnitAfterObs.ws =
      [⟨.obs (sig := NestedIxSig) 0, NestedP⟩] := by
  simp [nestedIxNonUnitAfterObs, nestedIxAtomBase, EncodeIx.bindObs, pushPos,
    NestedP, objectPolarity_coprod, List.mergeSort_singleton]

/-- Boundary leaf: focus on the unused NestedA binder (non-unit base goal). -/
def nestedIxNonUnitLeafTerm :
    InvTm (sig := NestedIxSig) (Ctx.empty ▻ NestedA ▻ NestedP) NestedA :=
  .foc (.pos (.done (.neu (.var (.there .here)))))

def nestedIxNonUnitLeaf :
    Produced (emptyWsEncode nestedIxNonUnitAfterObs) NestedA where
  term := nestedIxNonUnitLeafTerm
  cert := by
    change EncodeReady [] (emptyWsEncode nestedIxNonUnitAfterObs).env
      (emptyWsEncode nestedIxNonUnitAfterObs).domNext
      (emptyWsEncode nestedIxNonUnitAfterObs).obsNext nestedIxNonUnitLeafTerm
    exact EncodeReady.focus (by simp [forcedRule])
      (.pos (p := .neu (.var (.there .here))))

theorem nestedIx_nonUnit_forcedInvert_isSome :
    (certifiedForcedInvert nestedIxNonUnitAfterObs nestedIxNonUnitAfterObs_wf
      nestedIxNonUnitLeaf).isSome = true := by
  native_decide

def nestedIxNonUnitProduced : Produced nestedIxNonUnitAfterObs NestedA :=
  certifiedForcedInvert_get nestedIxNonUnitAfterObs nestedIxNonUnitAfterObs_wf
    nestedIxNonUnitLeaf nestedIx_nonUnit_forcedInvert_isSome

/-! ### Nested-summand schedule: observe `(A+B)+C`, drain nested left via peel invert -/

def nestedSchedHyps : Array (Object NestedIxSig.nBases) :=
  #[.exp .unit NestedP]

def nestedSchedΓ : Ctx NestedIxSig := Ctx.ofHyps (sig := NestedIxSig) nestedSchedHyps

def nestedSchedEntry : EncodeIx (sig := NestedIxSig) nestedSchedΓ :=
  EncodeIx.entry (sig := NestedIxSig) nestedSchedHyps

theorem nestedSchedEntry_wf : EncodeIx.WellFormed nestedSchedEntry :=
  EncodeIx.entry_wellFormed (sig := NestedIxSig) nestedSchedHyps

theorem nestedSchedEntry_boundary : AtSaturationBoundary nestedSchedEntry := by
  simp only [AtSaturationBoundary, nestedSchedEntry, EncodeIx.entry, nestedSchedHyps,
    OriginEnv.posWorklist, OriginEnv.posCollect]
  native_decide

theorem nestedSched_forcedRule_entry :
    forcedRule (sig := NestedIxSig) nestedSchedEntry.ws NestedP = .focus := by
  simp only [nestedSchedEntry_boundary, forcedRule]

def nestedSchedSum : NegNeu nestedSchedΓ NestedP :=
  .app (.var .here) .unit

/-- Left branch at `Γ ▻ P ▻ (A+B)`: inject the nested summand. -/
def nestedSchedBranchL :
    InvTm (nestedSchedΓ ▻ NestedP ▻ NestedInner) NestedP :=
  .foc (.pos (.done (.inl (.neu (.var .here)))))

def nestedSchedBranchR :
    InvTm (nestedSchedΓ ▻ NestedP ▻ NestedC) NestedP :=
  .foc (.pos (.done (.inr (.neu (.var .here)))))

def nestedSchedAfterL : EncodeIx (sig := NestedIxSig)
    (nestedSchedΓ ▻ NestedP ▻ NestedInner) :=
  afterIxCoprodL (sig := NestedIxSig) NestedInner NestedC nestedSchedEntry

def nestedSchedAfterR : EncodeIx (sig := NestedIxSig)
    (nestedSchedΓ ▻ NestedP ▻ NestedC) :=
  afterIxCoprodR (sig := NestedIxSig) NestedInner NestedC nestedSchedEntry

theorem nestedSchedAfterL_boundary :
    AtSaturationBoundary nestedSchedAfterL :=
  afterIxCoprodL_boundary (sig := NestedIxSig) NestedInner NestedC nestedSchedEntry
    nestedSchedEntry_boundary

theorem nestedSchedAfterR_boundary :
    AtSaturationBoundary nestedSchedAfterR :=
  afterIxCoprodR_boundary (sig := NestedIxSig) NestedInner NestedC nestedSchedEntry
    nestedSchedEntry_boundary

theorem nestedSched_branchL_cert :
    InvCert nestedSchedAfterL nestedSchedBranchL := by
  change EncodeReady nestedSchedAfterL.ws nestedSchedAfterL.env
    nestedSchedAfterL.domNext nestedSchedAfterL.obsNext nestedSchedBranchL
  have hb := nestedSchedAfterL_boundary
  rw [show nestedSchedAfterL.ws = [] from hb]
  exact EncodeReady.focus (by simp [forcedRule])
    (.pos (p := .inl (.neu (.var .here))))

theorem nestedSched_branchR_cert :
    InvCert nestedSchedAfterR nestedSchedBranchR := by
  change EncodeReady nestedSchedAfterR.ws nestedSchedAfterR.env
    nestedSchedAfterR.domNext nestedSchedAfterR.obsNext nestedSchedBranchR
  have hb := nestedSchedAfterR_boundary
  rw [show nestedSchedAfterR.ws = [] from hb]
  exact EncodeReady.focus (by simp [forcedRule])
    (.pos (p := .inr (.neu (.var .here))))

def nestedSchedRecL :
    CertifiedScheduleIx (sig := NestedIxSig) nestedSchedAfterL
      (mapIxRestCoprodL NestedInner NestedC nestedSchedSum []) NestedP :=
  certifiedScheduleIx_nil nestedSchedAfterL nestedSchedAfterL_boundary
    ⟨nestedSchedBranchL, nestedSched_branchL_cert⟩

def nestedSchedRecR :
    CertifiedScheduleIx (sig := NestedIxSig) nestedSchedAfterR
      (mapIxRestCoprodR NestedInner NestedC nestedSchedSum []) NestedP :=
  certifiedScheduleIx_nil nestedSchedAfterR nestedSchedAfterR_boundary
    ⟨nestedSchedBranchR, nestedSched_branchR_cert⟩

theorem nestedSched_splitL_ws :
    (retainedSplitLIx (sig := NestedIxSig) NestedInner NestedC nestedSchedEntry).ws =
      [{ origin := .split (obsEntryOf nestedSchedEntry NestedP).origin false,
         ty := NestedInner }] := by
  rw [retainedSplitLIx_ws_of_boundary (sig := NestedIxSig) NestedInner NestedC
    nestedSchedEntry nestedSchedEntry_boundary]
  simp [pushPos, NestedInner, objectPolarity, List.mergeSort_singleton]

theorem nestedSched_splitR_ws :
    (retainedSplitRIx (sig := NestedIxSig) NestedInner NestedC nestedSchedEntry).ws =
      [{ origin := .split (obsEntryOf nestedSchedEntry NestedP).origin true,
         ty := NestedC }] := by
  rw [retainedSplitRIx_ws_of_boundary (sig := NestedIxSig) NestedInner NestedC
    nestedSchedEntry nestedSchedEntry_boundary]
  simp [pushPos, NestedC, objectPolarity, List.mergeSort_singleton]

theorem nestedSched_splitL_wf :
    EncodeIx.WellFormed
      (retainedSplitLIx (sig := NestedIxSig) NestedInner NestedC nestedSchedEntry) := by
  have hws := nestedSched_splitL_ws
  have hbind := EncodeIx.WellFormed.bindObs nestedSchedEntry_wf NestedP
  have hpos : objectPolarity (NestedP : Object NestedIxSig.nBases) = .pos := by
    simp [NestedP, objectPolarity_coprod]
  have hwsObs :
      (nestedSchedEntry.bindObs NestedP).ws =
        [obsEntryOf nestedSchedEntry NestedP] :=
    bindObs_ws_of_boundary nestedSchedEntry NestedP nestedSchedEntry_boundary hpos
  simpa [retainedSplitLIx, EncodeIx.splitL, hwsObs] using
    EncodeIx.WellFormed.splitL hbind (obsEntryOf nestedSchedEntry NestedP) [] NestedInner
      (by simp [hwsObs])

theorem nestedSched_splitR_wf :
    EncodeIx.WellFormed
      (retainedSplitRIx (sig := NestedIxSig) NestedInner NestedC nestedSchedEntry) := by
  have hbind := EncodeIx.WellFormed.bindObs nestedSchedEntry_wf NestedP
  have hpos : objectPolarity (NestedP : Object NestedIxSig.nBases) = .pos := by
    simp [NestedP, objectPolarity_coprod]
  have hwsObs :
      (nestedSchedEntry.bindObs NestedP).ws =
        [obsEntryOf nestedSchedEntry NestedP] :=
    bindObs_ws_of_boundary nestedSchedEntry NestedP nestedSchedEntry_boundary hpos
  simpa [retainedSplitRIx, EncodeIx.splitR, hwsObs] using
    EncodeIx.WellFormed.splitR hbind (obsEntryOf nestedSchedEntry NestedP) [] NestedC
      (by simp [hwsObs])

theorem nestedSched_invL_isSome :
    (certifiedForcedInvert
      (retainedSplitLIx (sig := NestedIxSig) NestedInner NestedC nestedSchedEntry)
      nestedSched_splitL_wf
      (Produced.castState
        (emptyWsEncode_eq_afterIxCoprodL nestedSchedEntry nestedSched_splitL_ws).symm
        nestedSchedRecL.produced)).isSome = true := by
  native_decide

theorem nestedSched_invR_isSome :
    (certifiedForcedInvert
      (retainedSplitRIx (sig := NestedIxSig) NestedInner NestedC nestedSchedEntry)
      nestedSched_splitR_wf
      (Produced.castState
        (emptyWsEncode_eq_afterIxCoprodR nestedSchedEntry nestedSched_splitR_ws).symm
        nestedSchedRecR.produced)).isSome = true := by
  native_decide

/-- Exact coproduct schedule whose left summand is the nested `(A+B)`. -/
def nestedSchedIx :
    CertifiedScheduleIx (sig := NestedIxSig) nestedSchedEntry
      [⟨NestedP, nestedSchedSum⟩] NestedP :=
  certifiedScheduleIx_exactCoprod (sig := NestedIxSig) nestedSchedEntry
    nestedSched_forcedRule_entry nestedSchedSum []
    nestedSched_splitL_ws nestedSched_splitR_ws
    nestedSched_splitL_wf nestedSched_splitR_wf
    nestedSchedRecL nestedSchedRecR
    nestedSched_invL_isSome nestedSched_invR_isSome

def nestedSchedProduced : Produced nestedSchedEntry NestedP :=
  nestedSchedIx.produced

/-! ## Never / inconsistency / consistency fixtures -/

/-- Signature for exact-never and inconsistent fixtures. -/
def NeverIxSig : Signature where
  nBases := 1
  generators := #[]

private abbrev NeverIxGoal : Object NeverIxSig.nBases := .base ⟨0, by decide⟩

/--
`f : 1 → 0` is negative, so `EncodeIx.entry` is already a saturation boundary.
Never is observed as `f ()`, not as a worklist hyp.
-/
def neverIxHyps : Array (Object NeverIxSig.nBases) :=
  #[.exp (.unit : Object NeverIxSig.nBases) .never]

def neverIxΓ : Ctx NeverIxSig := Ctx.ofHyps (sig := NeverIxSig) neverIxHyps

def neverIxEntry : EncodeIx (sig := NeverIxSig) neverIxΓ :=
  EncodeIx.entry (sig := NeverIxSig) neverIxHyps

theorem neverIxEntry_boundary : AtSaturationBoundary neverIxEntry := by
  simp only [AtSaturationBoundary, neverIxEntry, EncodeIx.entry, neverIxHyps,
    OriginEnv.posWorklist, OriginEnv.posCollect]
  native_decide

theorem neverIx_forcedRule :
    forcedRule (sig := NeverIxSig) neverIxEntry.ws NeverIxGoal = .focus := by
  simp only [neverIxEntry_boundary, forcedRule]

/-- Exact never observation: `f () : never`. -/
def neverIxNeu : NegNeu neverIxΓ .never :=
  .app (.var .here) (.unit (Γ := neverIxΓ))

/-- Distractor rest (ignored by exact-never abort). -/
def neverIxRestDistractor : IxExactSchedule neverIxΓ :=
  [⟨.never, neverIxNeu⟩]

/-- Exact never schedule with a distractor rest entry. -/
def neverIxSched :
    CertifiedScheduleIx (sig := NeverIxSig) neverIxEntry
      (⟨.never, neverIxNeu⟩ :: neverIxRestDistractor) NeverIxGoal :=
  certifiedScheduleIx_exactNever (sig := NeverIxSig) neverIxEntry
    neverIx_forcedRule neverIxNeu neverIxRestDistractor

theorem neverIxSched_term :
    neverIxSched.produced.term = .abort (A := NeverIxGoal) neverIxNeu :=
  rfl

theorem neverIxSched_encodes :
    ∃ c, encodeICCGo (encodeFuel neverIxEntry.ws neverIxSched.produced.term)
        neverIxEntry.ws neverIxEntry.env neverIxEntry.domNext neverIxEntry.obsNext
        neverIxSched.produced.term = some c :=
  invCert_encodeGo_some neverIxEntry neverIxSched.produced.term
    neverIxSched.produced.cert

/-- Reachability hyps that make the state inconsistent (`x : never`). -/
def neverIxInconsistHyps : Array (Object NeverIxSig.nBases) :=
  #[(.never : Object NeverIxSig.nBases)]

def neverIxInconsistΓ : Ctx NeverIxSig :=
  Ctx.ofHyps (sig := NeverIxSig) neverIxInconsistHyps

/--
Boundary EncodeIx over `x : never` with empty worklist (schedule observes never
at focus; invertible `leftNever` on the ofHyps worklist is not re-run here).
-/
def neverIxInconsistEntry : EncodeIx (sig := NeverIxSig) neverIxInconsistΓ where
  ws := []
  env := OriginEnv.ofHyps (sig := NeverIxSig) neverIxInconsistHyps
  domNext := 0
  obsNext := 0

theorem neverIxInconsist_forcedRule :
    forcedRule (sig := NeverIxSig) neverIxInconsistEntry.ws NeverIxGoal = .focus := by
  simp [forcedRule, neverIxInconsistEntry]

def neverIxReachCtx : ReachCtx NeverIxSig.nBases where
  hyps := neverIxInconsistHyps
  newFrom := 0

def neverIxReachState : ReachState NeverIxSig.nBases :=
  runReachability neverIxReachCtx NeverIxGoal

theorem neverIxReach_inconsistent :
    neverIxReachState.inconsistent = true := by
  native_decide

theorem neverIx_neuOfType_some :
    (neuOfType (sig := NeverIxSig) 32 neverIxReachState neverIxInconsistHyps
      (.never : Object NeverIxSig.nBases)).isSome = true := by
  native_decide

def neverIxInconsistentNeu : NegNeu neverIxInconsistΓ .never :=
  (neuOfType (sig := NeverIxSig) 32 neverIxReachState neverIxInconsistHyps
    (.never : Object NeverIxSig.nBases)).get neverIx_neuOfType_some

/-- Inconsistent reachability → same exact-never core (entries ignored). -/
def neverIxInconsistentSched :
    CertifiedScheduleIx (sig := NeverIxSig) neverIxInconsistEntry
      ([] : IxExactSchedule neverIxInconsistΓ) NeverIxGoal :=
  certifiedScheduleIx_inconsistent (sig := NeverIxSig) neverIxInconsistEntry
    neverIxInconsist_forcedRule neverIxInconsistentNeu []

theorem neverIxInconsistentSched_term :
    neverIxInconsistentSched.produced.term =
      .abort (A := NeverIxGoal) neverIxInconsistentNeu :=
  rfl

/-! ### Consistency → atom -/

def consistAtomIxSig : Signature where
  nBases := 1
  generators := #[]

private abbrev ConsistAtom : Object consistAtomIxSig.nBases := .base ⟨0, by decide⟩
private abbrev consistAtomB : Fin consistAtomIxSig.nBases := ⟨0, by decide⟩

def consistAtomHyps : Array (Object consistAtomIxSig.nBases) := #[ConsistAtom]

def consistAtomΓ : Ctx consistAtomIxSig :=
  Ctx.ofHyps (sig := consistAtomIxSig) consistAtomHyps

/-- Boundary over `x : Atom` with empty worklist (consistency resolves the hyp). -/
def consistAtomEntry : EncodeIx (sig := consistAtomIxSig) consistAtomΓ where
  ws := []
  env := OriginEnv.ofHyps (sig := consistAtomIxSig) consistAtomHyps
  domNext := 0
  obsNext := 0

theorem consistAtom_forcedRule :
    forcedRule (sig := consistAtomIxSig) consistAtomEntry.ws ConsistAtom = .focus := by
  simp [forcedRule, consistAtomEntry]

def consistAtomReach : ReachState consistAtomIxSig.nBases :=
  runReachability ⟨consistAtomHyps, 0⟩ ConsistAtom

theorem consistAtom_resolve_some :
    (ixExactEntry_of_consistencyWitness (sig := consistAtomIxSig) 8
      consistAtomReach consistAtomHyps ConsistAtom (.ctxVar 0)).isSome = true := by
  native_decide

def consistAtomEntryResolved : IxExactEntry consistAtomΓ :=
  (ixExactEntry_of_consistencyWitness (sig := consistAtomIxSig) 8
    consistAtomReach consistAtomHyps ConsistAtom (.ctxVar 0)).get
    consistAtom_resolve_some

theorem consistAtom_resolve_eq :
    ixExactEntry_of_consistencyWitness (sig := consistAtomIxSig) 8
      consistAtomReach consistAtomHyps ConsistAtom (.ctxVar 0) =
      some consistAtomEntryResolved :=
  (Option.some_get consistAtom_resolve_some).symm

theorem consistAtom_resolve_correct :
    consistAtomEntryResolved.P = ConsistAtom ∧ WellNeg consistAtomEntryResolved.neu :=
  ixExactEntry_of_consistencyWitness_correct (sig := consistAtomIxSig) 8
    consistAtomReach consistAtomHyps ConsistAtom (.ctxVar 0)
    consistAtom_resolve_eq

/-- Reconstructed atom neutral (definitionally `.var .here` for `ctxVar 0`). -/
def consistAtomNeu : NegNeu consistAtomΓ ConsistAtom :=
  .var .here

theorem consistAtomEntryResolved_P :
    consistAtomEntryResolved.P = ConsistAtom :=
  consistAtom_resolve_correct.1

def consistAtomAfter : EncodeIx (sig := consistAtomIxSig)
    (consistAtomΓ ▻ ConsistAtom) :=
  afterIxAtom consistAtomB consistAtomEntry

theorem consistAtomAfter_boundary :
    AtSaturationBoundary consistAtomAfter :=
  afterIxAtom_boundary consistAtomB consistAtomEntry rfl

/-- Leaf under the retained atom binder: return the bound atom. -/
def consistAtomLeaf : InvTm (consistAtomΓ ▻ ConsistAtom) ConsistAtom :=
  .foc (.pos (.done (.neu (.var .here))))

theorem consistAtomLeaf_cert : InvCert consistAtomAfter consistAtomLeaf := by
  change EncodeReady consistAtomAfter.ws consistAtomAfter.env
    consistAtomAfter.domNext consistAtomAfter.obsNext consistAtomLeaf
  have hb := consistAtomAfter_boundary
  rw [show consistAtomAfter.ws = [] from hb]
  exact EncodeReady.focus (by simp [forcedRule])
    (.pos (p := .neu (.var .here)))

def consistAtomRec :
    CertifiedScheduleIx (sig := consistAtomIxSig) consistAtomAfter [] ConsistAtom :=
  certifiedScheduleIx_nil consistAtomAfter consistAtomAfter_boundary
    ⟨consistAtomLeaf, consistAtomLeaf_cert⟩

/-- Consistency witness → IxExactEntry → `certifiedScheduleIx_consistencyAtom`. -/
def consistAtomSched :
    CertifiedScheduleIx (sig := consistAtomIxSig) consistAtomEntry
      [⟨ConsistAtom, consistAtomNeu⟩] ConsistAtom :=
  certifiedScheduleIx_consistencyAtom (sig := consistAtomIxSig) consistAtomEntry
    consistAtom_forcedRule consistAtomNeu [] consistAtomRec

/-! ### Consistency → coproduct -/

def consistCoprodIxSig : Signature where
  nBases := 1
  generators := #[]

private abbrev ConsistCAtom : Object consistCoprodIxSig.nBases := .base ⟨0, by decide⟩
private abbrev ConsistSum : Object consistCoprodIxSig.nBases :=
  .coprod ConsistCAtom ConsistCAtom

def consistCoprodHyps : Array (Object consistCoprodIxSig.nBases) := #[ConsistSum]

def consistCoprodΓ : Ctx consistCoprodIxSig :=
  Ctx.ofHyps (sig := consistCoprodIxSig) consistCoprodHyps

def consistCoprodEntry : EncodeIx (sig := consistCoprodIxSig) consistCoprodΓ where
  ws := []
  env := OriginEnv.ofHyps (sig := consistCoprodIxSig) consistCoprodHyps
  domNext := 0
  obsNext := 0

theorem consistCoprod_forcedRule :
    forcedRule (sig := consistCoprodIxSig) consistCoprodEntry.ws ConsistSum = .focus := by
  simp [forcedRule, consistCoprodEntry]

def consistCoprodReach : ReachState consistCoprodIxSig.nBases :=
  runReachability ⟨consistCoprodHyps, 0⟩ ConsistSum

theorem consistCoprod_resolve_some :
    (ixExactEntry_of_consistencyWitness (sig := consistCoprodIxSig) 8
      consistCoprodReach consistCoprodHyps ConsistSum (.ctxVar 0)).isSome = true := by
  native_decide

def consistCoprodEntryResolved : IxExactEntry consistCoprodΓ :=
  (ixExactEntry_of_consistencyWitness (sig := consistCoprodIxSig) 8
    consistCoprodReach consistCoprodHyps ConsistSum (.ctxVar 0)).get
    consistCoprod_resolve_some

theorem consistCoprod_resolve_eq :
    ixExactEntry_of_consistencyWitness (sig := consistCoprodIxSig) 8
      consistCoprodReach consistCoprodHyps ConsistSum (.ctxVar 0) =
      some consistCoprodEntryResolved :=
  (Option.some_get consistCoprod_resolve_some).symm

theorem consistCoprod_resolve_correct :
    consistCoprodEntryResolved.P = ConsistSum ∧ WellNeg consistCoprodEntryResolved.neu :=
  ixExactEntry_of_consistencyWitness_correct (sig := consistCoprodIxSig) 8
    consistCoprodReach consistCoprodHyps ConsistSum (.ctxVar 0)
    consistCoprod_resolve_eq

def consistCoprodNeu : NegNeu consistCoprodΓ ConsistSum := .var .here

theorem consistCoprodEntryResolved_P :
    consistCoprodEntryResolved.P = ConsistSum :=
  consistCoprod_resolve_correct.1

def consistCoprodAfterL : EncodeIx (sig := consistCoprodIxSig)
    (consistCoprodΓ ▻ ConsistSum ▻ ConsistCAtom) :=
  afterIxCoprodL ConsistCAtom ConsistCAtom consistCoprodEntry

def consistCoprodAfterR : EncodeIx (sig := consistCoprodIxSig)
    (consistCoprodΓ ▻ ConsistSum ▻ ConsistCAtom) :=
  afterIxCoprodR ConsistCAtom ConsistCAtom consistCoprodEntry

theorem consistCoprodAfterL_boundary :
    AtSaturationBoundary consistCoprodAfterL :=
  afterIxCoprodL_boundary ConsistCAtom ConsistCAtom consistCoprodEntry rfl

theorem consistCoprodAfterR_boundary :
    AtSaturationBoundary consistCoprodAfterR :=
  afterIxCoprodR_boundary ConsistCAtom ConsistCAtom consistCoprodEntry rfl

def consistCoprodBranchL :
    InvTm (consistCoprodΓ ▻ ConsistSum ▻ ConsistCAtom) ConsistSum :=
  .foc (.pos (.done (.inl (.neu (.var .here)))))

def consistCoprodBranchR :
    InvTm (consistCoprodΓ ▻ ConsistSum ▻ ConsistCAtom) ConsistSum :=
  .foc (.pos (.done (.inr (.neu (.var .here)))))

theorem consistCoprodBranchL_cert :
    InvCert consistCoprodAfterL consistCoprodBranchL := by
  change EncodeReady consistCoprodAfterL.ws consistCoprodAfterL.env
    consistCoprodAfterL.domNext consistCoprodAfterL.obsNext consistCoprodBranchL
  have hb := consistCoprodAfterL_boundary
  rw [show consistCoprodAfterL.ws = [] from hb]
  exact EncodeReady.focus (by simp [forcedRule])
    (.pos (p := .inl (.neu (.var .here))))

theorem consistCoprodBranchR_cert :
    InvCert consistCoprodAfterR consistCoprodBranchR := by
  change EncodeReady consistCoprodAfterR.ws consistCoprodAfterR.env
    consistCoprodAfterR.domNext consistCoprodAfterR.obsNext consistCoprodBranchR
  have hb := consistCoprodAfterR_boundary
  rw [show consistCoprodAfterR.ws = [] from hb]
  exact EncodeReady.focus (by simp [forcedRule])
    (.pos (p := .inr (.neu (.var .here))))

def consistCoprodRecL :
    CertifiedScheduleIx (sig := consistCoprodIxSig) consistCoprodAfterL [] ConsistSum :=
  certifiedScheduleIx_nil consistCoprodAfterL consistCoprodAfterL_boundary
    ⟨consistCoprodBranchL, consistCoprodBranchL_cert⟩

def consistCoprodRecR :
    CertifiedScheduleIx (sig := consistCoprodIxSig) consistCoprodAfterR [] ConsistSum :=
  certifiedScheduleIx_nil consistCoprodAfterR consistCoprodAfterR_boundary
    ⟨consistCoprodBranchR, consistCoprodBranchR_cert⟩

theorem consistCoprod_splitL_ws :
    (retainedSplitLIx (sig := consistCoprodIxSig) ConsistCAtom ConsistCAtom
      consistCoprodEntry).ws =
      [{ origin := .split (obsEntryOf consistCoprodEntry ConsistSum).origin false,
         ty := ConsistCAtom }] := by
  rw [retainedSplitLIx_ws_of_boundary ConsistCAtom ConsistCAtom consistCoprodEntry rfl]
  simp [pushPos, ConsistCAtom, objectPolarity, List.mergeSort_singleton]

theorem consistCoprod_splitR_ws :
    (retainedSplitRIx (sig := consistCoprodIxSig) ConsistCAtom ConsistCAtom
      consistCoprodEntry).ws =
      [{ origin := .split (obsEntryOf consistCoprodEntry ConsistSum).origin true,
         ty := ConsistCAtom }] := by
  rw [retainedSplitRIx_ws_of_boundary ConsistCAtom ConsistCAtom consistCoprodEntry rfl]
  simp [pushPos, ConsistCAtom, objectPolarity, List.mergeSort_singleton]

theorem consistCoprod_splitL_wf :
    EncodeIx.WellFormed
      (retainedSplitLIx (sig := consistCoprodIxSig) ConsistCAtom ConsistCAtom
        consistCoprodEntry) := by
  have hentry : EncodeIx.WellFormed consistCoprodEntry :=
    { env_wf := OriginEnv.ofHyps_wellFormed _
      env_bounded := by
        intro A x
        simp only [consistCoprodEntry, OriginEnv.ofHyps]
        exact Origin.counterBounded_hyp _ _ _
      ws_bounded := fun he => by cases he
      ws_in_env := fun he => by cases he
      ws_nodup := by simp [consistCoprodEntry]
      ws_split_fresh := by
        intro e he side A x hx
        simp only [consistCoprodEntry] at he
        cases he
      split_parent_live := by
        intro A x p side hx
        simp only [consistCoprodEntry, OriginEnv.ofHyps] at hx
        cases hx }
  have hbind := EncodeIx.WellFormed.bindObs hentry ConsistSum
  have hpos : objectPolarity (ConsistSum : Object _) = .pos := by
    simp [ConsistSum, objectPolarity_coprod]
  have hwsObs :
      (consistCoprodEntry.bindObs ConsistSum).ws =
        [obsEntryOf consistCoprodEntry ConsistSum] :=
    bindObs_ws_of_boundary consistCoprodEntry ConsistSum rfl hpos
  simpa [retainedSplitLIx, EncodeIx.splitL, hwsObs] using
    EncodeIx.WellFormed.splitL hbind (obsEntryOf consistCoprodEntry ConsistSum) []
      ConsistCAtom (by simp [hwsObs])

theorem consistCoprod_splitR_wf :
    EncodeIx.WellFormed
      (retainedSplitRIx (sig := consistCoprodIxSig) ConsistCAtom ConsistCAtom
        consistCoprodEntry) := by
  have hentry : EncodeIx.WellFormed consistCoprodEntry :=
    { env_wf := OriginEnv.ofHyps_wellFormed _
      env_bounded := by
        intro A x
        simp only [consistCoprodEntry, OriginEnv.ofHyps]
        exact Origin.counterBounded_hyp _ _ _
      ws_bounded := fun he => by cases he
      ws_in_env := fun he => by cases he
      ws_nodup := by simp [consistCoprodEntry]
      ws_split_fresh := by
        intro e he side A x hx
        simp only [consistCoprodEntry] at he
        cases he
      split_parent_live := by
        intro A x p side hx
        simp only [consistCoprodEntry, OriginEnv.ofHyps] at hx
        cases hx }
  have hbind := EncodeIx.WellFormed.bindObs hentry ConsistSum
  have hpos : objectPolarity (ConsistSum : Object _) = .pos := by
    simp [ConsistSum, objectPolarity_coprod]
  have hwsObs :
      (consistCoprodEntry.bindObs ConsistSum).ws =
        [obsEntryOf consistCoprodEntry ConsistSum] :=
    bindObs_ws_of_boundary consistCoprodEntry ConsistSum rfl hpos
  simpa [retainedSplitRIx, EncodeIx.splitR, hwsObs] using
    EncodeIx.WellFormed.splitR hbind (obsEntryOf consistCoprodEntry ConsistSum) []
      ConsistCAtom (by simp [hwsObs])

theorem consistCoprod_invL_isSome :
    (certifiedForcedInvert
      (retainedSplitLIx (sig := consistCoprodIxSig) ConsistCAtom ConsistCAtom
        consistCoprodEntry)
      consistCoprod_splitL_wf
      (Produced.castState
        (emptyWsEncode_eq_afterIxCoprodL consistCoprodEntry consistCoprod_splitL_ws).symm
        consistCoprodRecL.produced)).isSome = true := by
  native_decide

theorem consistCoprod_invR_isSome :
    (certifiedForcedInvert
      (retainedSplitRIx (sig := consistCoprodIxSig) ConsistCAtom ConsistCAtom
        consistCoprodEntry)
      consistCoprod_splitR_wf
      (Produced.castState
        (emptyWsEncode_eq_afterIxCoprodR consistCoprodEntry consistCoprod_splitR_ws).symm
        consistCoprodRecR.produced)).isSome = true := by
  native_decide

/-- Consistency witness → IxExactEntry → `certifiedScheduleIx_consistencyCoprod`. -/
def consistCoprodSched :
    CertifiedScheduleIx (sig := consistCoprodIxSig) consistCoprodEntry
      [⟨ConsistSum, consistCoprodNeu⟩] ConsistSum :=
  certifiedScheduleIx_consistencyCoprod (sig := consistCoprodIxSig)
    consistCoprodEntry consistCoprod_forcedRule consistCoprodNeu []
    consistCoprod_splitL_ws consistCoprod_splitR_ws
    consistCoprod_splitL_wf consistCoprod_splitR_wf
    consistCoprodRecL consistCoprodRecR
    consistCoprod_invL_isSome consistCoprod_invR_isSome

/-!
### Status — forced inversion + nested fixtures + never/consistency

**Landed:**
* `certifiedForcedInvert` — peel-based, goal-polymorphic
* `certifiedScheduleIx_exactCoprod` / nested fixtures
* `certifiedScheduleIx_exactNever` / `certifiedScheduleIx_inconsistent`
* Consistency resolution: `ixExactEntry_of_consistencyWitness` →
  `certifiedScheduleIx_consistency{Never,Atom,Coprod}` (delegates only)
* Reconstruction totality left open as `ReconstructWitnessTotal` (8D)

**Deferred:** full reachability adapter / EncodeTotal / Cleanup B.
-/

end Equality
end Gimbal
