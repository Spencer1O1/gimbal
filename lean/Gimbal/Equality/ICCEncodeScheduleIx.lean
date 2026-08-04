/-
  Retained-state-indexed exact schedule (`CertifiedScheduleIx`).

  Parallel to legacy `CertifiedSchedule` / `PairEntry` / `ofHyps` indexing.
  Exact observation entries and remainder maps live in the actual EncodeIx
  context so `.obs` / `.split` origins are preserved by construction.

  **Coproduct clause restriction:** `certifiedScheduleIx_exactCoprod` drains each
  summand via `certifiedForcedInvert_moveStableOnly` (worklists that are
  `WorklistMoveStableOnly` — stable/atomic positives, no nested `coprod`/`never`
  heads). Nested-coproduct summands use `certifiedForcedInvert_unit_eta?` /
  `certifiedForcedInvert_unit?` (forced-inversion recursion, separate from
  schedule recursion).

  Does **not** replace legacy `PairEntry`, delete `CertifiedSchedule`, or
  change `applyObsNeu` / comparator. Consistency witnesses deferred.
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

**STOP (non-unit `leftCoprod` leaf transport):** measure decreases on
`splitL`/`splitR` (`worklistWeight`). `EncodeIxEmbedding` + peel-free
`Produced` transport land in `ICCEncodeEmbed` (λ / `letPos` exercises OK;
`letPos` is **not** blocked — counters agree). Remaining law for arbitrary
leaves: `peelCaseOuter` / `find?` naturality under rename. Until that lifts
`encodeReadyNoPeel_of_embedding` to full `EncodeReady`, non-unit nested
`leftCoprod` forced inversion stays on the unit-η path.
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

Requires the allocated split origin to be fresh in `s.env` (otherwise the
unused-binder target collides and `find?` prefers the newest binder).
-/
theorem encodeIxEmbedding_emptyWs_splitL {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (L : Object sig.nBases)
    (hws : s.ws = e :: tail)
    (hwf : OriginEnv.WellFormed s.env)
    (hfresh : OriginEnv.Fresh s.env (.split e.origin false)) :
    EncodeIxEmbedding (Rename.weaken (A := L))
      (emptyWsEncode s)
      (emptyWsEncode (splitEncodeL s e tail L hws)) := by
  change EncodeIxEmbedding _ (emptyWsEncode s)
    ⟨[], OriginEnv.weaken (A := L) s.env (.split e.origin false), s.domNext, s.obsNext⟩
  exact encodeIxEmbedding_weaken (emptyWsEncode s) (.split e.origin false) hwf hfresh

theorem encodeIxEmbedding_emptyWs_splitR {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (R : Object sig.nBases)
    (hws : s.ws = e :: tail)
    (hwf : OriginEnv.WellFormed s.env)
    (hfresh : OriginEnv.Fresh s.env (.split e.origin true)) :
    EncodeIxEmbedding (Rename.weaken (A := R))
      (emptyWsEncode s)
      (emptyWsEncode (splitEncodeR s e tail R hws)) := by
  change EncodeIxEmbedding _ (emptyWsEncode s)
    ⟨[], OriginEnv.weaken (A := R) s.env (.split e.origin true), s.domNext, s.obsNext⟩
  exact encodeIxEmbedding_weaken (emptyWsEncode s) (.split e.origin true) hwf hfresh

/-- Peel-free leaf transport into a left split empty-worklist state. -/
def produced_emptyWs_splitL_noPeel {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (L : Object sig.nBases)
    (hws : s.ws = e :: tail)
    (hwf : OriginEnv.WellFormed s.env)
    (hfresh : OriginEnv.Fresh s.env (.split e.origin false))
    (p : Produced (emptyWsEncode s) A)
    (h : EncodeReadyNoPeel (sig := sig) (emptyWsEncode s).ws
      (emptyWsEncode s).env (emptyWsEncode s).domNext (emptyWsEncode s).obsNext
      p.term) :
    Produced (emptyWsEncode (splitEncodeL s e tail L hws)) A :=
  produced_of_embedding_noPeel
    (encodeIxEmbedding_emptyWs_splitL s e tail L hws hwf hfresh) p h

def produced_emptyWs_splitR_noPeel {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (tail : List (PosEntry sig)) (R : Object sig.nBases)
    (hws : s.ws = e :: tail)
    (hwf : OriginEnv.WellFormed s.env)
    (hfresh : OriginEnv.Fresh s.env (.split e.origin true))
    (p : Produced (emptyWsEncode s) A)
    (h : EncodeReadyNoPeel (sig := sig) (emptyWsEncode s).ws
      (emptyWsEncode s).env (emptyWsEncode s).domNext (emptyWsEncode s).obsNext
      p.term) :
    Produced (emptyWsEncode (splitEncodeR s e tail R hws)) A :=
  produced_of_embedding_noPeel
    (encodeIxEmbedding_emptyWs_splitR s e tail R hws hwf hfresh) p h

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
Exact coproduct clause: map remainder into both retained split contexts, take
recursive `CertifiedScheduleIx` at `afterIxCoprodL/R` (= `split.pop` = empty
worklist / saturation boundary after draining), lift each summand through
`certifiedForcedInvert_moveStableOnly`, package with `retainedCoprodObsCertified`.

**Restriction:** `hstableL` / `hstableR` require each summand worklist to be
`WorklistMoveStableOnly` (heads discharged by `moveStable` — stable/atomic
positives). Nested-coproduct summands use `certifiedForcedInvert_unit_eta?` /
`certifiedForcedInvert_unit?` instead (separate forced-inversion recursion).
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

/-- Alias documenting the moveStable-summand restriction. -/
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
    (hstableL : WorklistMoveStableOnly (retainedSplitLIx L R s).ws)
    (hstableR : WorklistMoveStableOnly (retainedSplitRIx L R s).ws)
    (recL : CertifiedScheduleIx (afterIxCoprodL L R s)
      (mapIxRestCoprodL L R nSum rest) A)
    (recR : CertifiedScheduleIx (afterIxCoprodR L R s)
      (mapIxRestCoprodR L R nSum rest) A) :
    CertifiedScheduleIx s (⟨.coprod L R, nSum⟩ :: rest) A :=
  certifiedScheduleIx_exactCoprod_of_moveStableSummands s hfr nSum rest
    hwsL hwsR hstableL hstableR recL recR

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
    certifiedScheduleIx_exactCoprod (sig := TwoObsIxSig) twoObsIxAfterAtom
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
`certifiedForcedInvert_unit_eta?` mirroring `forcedRule`; no nesting-depth
constructors. Goal `.unit` so branch leaves need no unused-binder transport.
-/

def NestedIxSig : Signature where
  nBases := 3
  generators := #[]

private abbrev NestedA : Object NestedIxSig.nBases := .base ⟨0, by decide⟩
private abbrev NestedB : Object NestedIxSig.nBases := .base ⟨1, by decide⟩
private abbrev NestedC : Object NestedIxSig.nBases := .base ⟨2, by decide⟩
private abbrev NestedInner : Object NestedIxSig.nBases := .coprod NestedA NestedB
private abbrev NestedP : Object NestedIxSig.nBases := .coprod NestedInner NestedC

/-- Boundary state that has just retained observation `P = (A+B)+C`. -/
def nestedIxAfterObs : EncodeIx (sig := NestedIxSig) (Ctx.empty ▻ NestedP) where
  ws := [⟨.obs (sig := NestedIxSig) 0, NestedP⟩]
  env := OriginEnv.weaken (A := NestedP) OriginEnv.empty (.obs (sig := NestedIxSig) 0)
  domNext := 0
  obsNext := 1

theorem nestedIxAfterObs_forcedRule :
    forcedRule (sig := NestedIxSig) nestedIxAfterObs.ws (.unit : Object NestedIxSig.nBases) =
      .leftCoprod ⟨.obs (sig := NestedIxSig) 0, NestedP⟩ NestedInner NestedC := by
  simp [forcedRule, nestedIxAfterObs, NestedP, NestedInner]

/-- Left summand state after the outer leftCoprod step: head is nested `A+B`. -/
def nestedIxSplitInner : EncodeIx (sig := NestedIxSig)
    (Ctx.empty ▻ NestedP ▻ NestedInner) :=
  splitEncodeL nestedIxAfterObs ⟨.obs (sig := NestedIxSig) 0, NestedP⟩ [] NestedInner rfl

/-- Right summand state after the outer leftCoprod step: head is atomic `C`. -/
def nestedIxSplitC : EncodeIx (sig := NestedIxSig)
    (Ctx.empty ▻ NestedP ▻ NestedC) :=
  splitEncodeR nestedIxAfterObs ⟨.obs (sig := NestedIxSig) 0, NestedP⟩ [] NestedC rfl

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

/-!
### Stop report — forced inversion + nested fixture

**Landed:**
* `certifiedForcedInvert_moveStableOnly` — drains `WorklistMoveStableOnly` worklists
* `certifiedForcedInvert_unit_eta?` / `certifiedForcedInvert_unit?` — mirrors
  `forcedRule` including nested `leftCoprod` (unit-η) and `leftNever` (abort)
* `certifiedScheduleIx_exactCoprod` invokes moveStable-only invert per summand
* Nested fixture `P = (A+B)+C`: outer/inner leftCoprod + atomic `moveStable`;
  every atomic branch pop is `AtSaturationBoundary`; full invert isSome

**STOP (non-unit leftCoprod leaf transport):** measure decreases on
`splitEncodeL/R`. `EncodeIxEmbedding` + peel-free transport land (`ICCEncodeEmbed`;
λ/`letPos` exercises; `letPos` not blocked). Remaining: `peelCaseOuter`/`find?`
rename naturality to lift to full `EncodeReady`. No fuel; no nesting-depth cases.

Legacy `CertifiedSchedule` kept. Consistency / public evaluator deferred.
-/

end Equality
end Gimbal
