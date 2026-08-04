/-
  Certified schedule composition at `AtSaturationBoundary`.

  Proof-relevant schedule results + generic nil and exact-atom recursive clauses.
  Exact-coproduct scaffolding + skip-binder transport spike: observation origin
  is not recoverable from legacy ofHyps branch states (see in-file STOP).

  Does **not** change `applyObsNeu`, RawReference, totality, or `referenceCompare`.
  Consistency schedule clauses are deferred.
-/

import Gimbal.Equality.Abstract
import Gimbal.Equality.ICCEncodeIx
import Gimbal.Equality.ICCPeel
import Gimbal.Equality.Saturation

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ## EncodeIx / Produced context casts -/

def EncodeIx.castCtx {Γ Δ : Ctx sig} (h : Γ = Δ) (s : EncodeIx (sig := sig) Γ) :
    EncodeIx (sig := sig) Δ :=
  h ▸ s

theorem EncodeIx.castCtx_symm_castCtx {Γ Δ : Ctx sig} (h : Γ = Δ)
    (s : EncodeIx (sig := sig) Δ) :
    (s.castCtx h.symm).castCtx h = s := by
  cases h; rfl

theorem AtSaturationBoundary.castCtx {Γ Δ : Ctx sig} (h : Γ = Δ)
    {s : EncodeIx (sig := sig) Γ} (hb : AtSaturationBoundary s) :
    AtSaturationBoundary (EncodeIx.castCtx h s) := by
  cases h; exact hb

theorem InvCert.castCtx {Γ Δ : Ctx sig} {A : Object sig.nBases} (h : Γ = Δ)
    {s : EncodeIx (sig := sig) Γ} {t : InvTm Γ A} (c : InvCert s t) :
    InvCert (EncodeIx.castCtx h s) (InvTm.castCtx h t) := by
  cases h; exact c

def Produced.castCtx {Γ Δ : Ctx sig} {A : Object sig.nBases} (h : Γ = Δ)
    {s : EncodeIx (sig := sig) Γ} (p : Produced s A) :
    Produced (EncodeIx.castCtx h s) A where
  term := InvTm.castCtx h p.term
  cert := InvCert.castCtx h p.cert

/-! ## Certified schedule result -/

/--
Proof-relevant result of consuming a schedule fragment at a saturation boundary.
Indexed by the entry list at an `ofHyps` context.
-/
structure CertifiedSchedule
    {hyps : Array (Object sig.nBases)}
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps))
    (entries : List (PairEntry sig hyps))
    (A : Object sig.nBases) where
  boundary : AtSaturationBoundary s
  produced : Produced s A

/-- Package a boundary `Produced` for a given entry list (bridge until further
schedule clauses exist). -/
def CertifiedSchedule.ofProduced
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)}
    (entries : List (PairEntry sig hyps))
    (hb : AtSaturationBoundary s) (p : Produced s A) :
    CertifiedSchedule s entries A :=
  ⟨hb, p⟩

/-! ### Nil clause -/

/-- Empty schedule: return the already-certified continuation unchanged. -/
def certifiedSchedule_nil
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps))
    (hb : AtSaturationBoundary s) (cont : Produced s A) :
    CertifiedSchedule s [] A :=
  ⟨hb, cont⟩

/-! ### Exact base-atom clause -/

/-- State after retaining a base observation, reindexed to `ofHyps (hyps.push …)`. -/
def afterExactAtom
    {hyps : Array (Object sig.nBases)} (b : Fin sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    EncodeIx (sig := sig) (Ctx.ofHyps (hyps.push (.base b))) :=
  EncodeIx.castCtx (Ctx.ofHyps_push hyps (.base b)).symm
    (s.bindObs (.base b)).pop

theorem afterExactAtom_boundary
    {hyps : Array (Object sig.nBases)} (b : Fin sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps))
    (hb : AtSaturationBoundary s) :
    AtSaturationBoundary (afterExactAtom b s) :=
  AtSaturationBoundary.castCtx _
    (bindObs_pop_boundary s (.base b) hb rfl)

theorem afterExactAtom_cast_pop
    {hyps : Array (Object sig.nBases)} (b : Fin sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    EncodeIx.castCtx (Ctx.ofHyps_push hyps (.base b)) (afterExactAtom b s) =
      (s.bindObs (.base b)).pop :=
  EncodeIx.castCtx_symm_castCtx (Ctx.ofHyps_push hyps (.base b)) _

/-- Evaluator’s `mapRestAbstractAtom` on a remaining schedule. -/
def mapRestExactAtom
    (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (b : Fin sig.nBases)
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (rest : List (PairEntry sig hyps)) :
    List (PairEntry sig (hyps.push (.base b))) :=
  let hctx := Ctx.ofHyps_push hyps (.base b)
  let targetRaw := NegNeu.toRaw (NegNeu.weaken (B := .base b) nP)
  rest.map (mapRestAbstractAtom fuel σ hyps (.base b) hctx targetRaw)

/-- Continuation cut corresponding to evaluator `atomPushCont`. -/
abbrev exactAtomPushCont
    {hyps : Array (Object sig.nBases)} {b : Fin sig.nBases} {A : Object sig.nBases}
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (cont : InvTm (Ctx.ofHyps hyps) A) :
    InvTm (Ctx.ofHyps (hyps.push (.base b))) A :=
  atomPushCont nP cont

/--
Exact non-coproduct (base) observation clause.

Maps `rest` with `mapRestAbstractAtom`, takes an **arbitrary** certified
recursive result for that mapped rest at the restored boundary, restores the
boundary via `moveStable` inside `retainedAtomObsCertified`, and wraps the atom
observation.
-/
def certifiedSchedule_exactAtom
    {hyps : Array (Object sig.nBases)} {b : Fin sig.nBases} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps))
    (hfr : forcedRule (sig := sig) s.ws A = .focus)
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (rest : List (PairEntry sig hyps))
    (fuel : Nat) (σ : ReachState sig.nBases)
    (rec : CertifiedSchedule (afterExactAtom b s)
      (mapRestExactAtom fuel σ hyps b nP rest) A) :
    CertifiedSchedule s (.exact (.base b) nP :: rest) A :=
  let hb : AtSaturationBoundary s := atSaturationBoundary_of_forcedRule_focus s hfr
  let hpush := Ctx.ofHyps_push hyps (.base b)
  -- Build the pop-continuation with an explicit body so the produced term is
  -- definitionally `letPos` of `InvTm.castCtx hpush rec.produced.term`.
  let body : InvTm (Ctx.ofHyps hyps ▻ .base b) A :=
    InvTm.castCtx hpush rec.produced.term
  let certPop : InvCert (s.bindObs (.base b)).pop body :=
    afterExactAtom_cast_pop b s ▸ InvCert.castCtx hpush rec.produced.cert
  ⟨hb, retainedAtomObsCertified s nP hb hfr ⟨body, certPop⟩⟩

theorem certifiedSchedule_exactAtom_term
    {hyps : Array (Object sig.nBases)} {b : Fin sig.nBases} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps))
    (hfr : forcedRule (sig := sig) s.ws A = .focus)
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (rest : List (PairEntry sig hyps))
    (fuel : Nat) (σ : ReachState sig.nBases)
    (rec : CertifiedSchedule (afterExactAtom b s)
      (mapRestExactAtom fuel σ hyps b nP rest) A) :
    (certifiedSchedule_exactAtom s hfr nP rest fuel σ rec).produced.term =
      .foc (.letPos nP
        (InvTm.castCtx (Ctx.ofHyps_push hyps (.base b)) rec.produced.term)) :=
  rfl

/-- Retained atom observation erases by cutting the recursive body (evaluator shape). -/
theorem certifiedSchedule_exactAtom_erase
    {hyps : Array (Object sig.nBases)} {b : Fin sig.nBases} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps))
    (hfr : forcedRule (sig := sig) s.ws A = .focus)
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (rest : List (PairEntry sig hyps))
    (fuel : Nat) (σ : ReachState sig.nBases)
    (rec : CertifiedSchedule (afterExactAtom b s)
      (mapRestExactAtom fuel σ hyps b nP rest) A) :
    (certifiedSchedule_exactAtom s hfr nP rest fuel σ rec).produced.term.erase =
      subst0
        (InvTm.castCtx (Ctx.ofHyps_push hyps (.base b)) rec.produced.term).erase
        nP.erase := by
  simp only [certifiedSchedule_exactAtom_term, InvTm.erase, FocTm.erase]

/-- Empty-rest specialization: recursive body = `atomPushCont` ⇒ evaluator cut erasure. -/
theorem certifiedSchedule_exactAtom_erase_atomPushCont
    {hyps : Array (Object sig.nBases)} {b : Fin sig.nBases} {A : Object sig.nBases}
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps))
    (hfr : forcedRule (sig := sig) s.ws A = .focus)
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (fuel : Nat) (σ : ReachState sig.nBases)
    (cont : InvTm (Ctx.ofHyps hyps) A)
    (rec : CertifiedSchedule (afterExactAtom b s)
      (mapRestExactAtom fuel σ hyps b nP []) A)
    (hrec : rec.produced.term = exactAtomPushCont nP cont) :
    (certifiedSchedule_exactAtom s hfr nP [] fuel σ rec).produced.term.erase =
      cont.erase := by
  have hterm := certifiedSchedule_exactAtom_term s hfr nP [] fuel σ rec
  rw [hterm, hrec, exactAtomPushCont, atomPushCont]
  simp only [InvTm.castCtx_cancel_symm, InvTm.erase, FocTm.erase]
  exact erase_letPos_abstr nP cont

theorem certifiedSchedule_exactAtom_encodes
    {hyps : Array (Object sig.nBases)} {b : Fin sig.nBases} {A : Object sig.nBases}
    (hfr : forcedRule (sig := sig) (EncodeIx.entry (sig := sig) hyps).ws A = .focus)
    (nP : NegNeu (Ctx.ofHyps hyps) (.base b))
    (rest : List (PairEntry sig hyps))
    (fuel : Nat) (σ : ReachState sig.nBases)
    (rec : CertifiedSchedule (afterExactAtom b (EncodeIx.entry (sig := sig) hyps))
      (mapRestExactAtom fuel σ hyps b nP rest) A) :
    ∃ c, encodeICC (OriginEnv.ofHyps hyps)
        (certifiedSchedule_exactAtom (EncodeIx.entry (sig := sig) hyps) hfr nP rest
          fuel σ rec).produced.term =
      some c :=
  entryReady_encode_some (by
    simpa [EntryReady, InvCert, EncodeIx.entry] using
      (certifiedSchedule_exactAtom (EncodeIx.entry (sig := sig) hyps) hfr nP rest
        fuel σ rec).produced.cert)

/-!
### Exact-atom clause status

Generic over `rest` and an arbitrary `CertifiedSchedule` recursive result for
`mapRestExactAtom … rest`. Uses real `atomPushCont` / `mapRestAbstractAtom`.
No continuation-shape specialization in the clause itself.
-/

/-! ### Exact-coproduct clause — scaffolding + stop -/

/-- Evaluator’s `mapRestAbstractSumInl` on a remaining schedule. -/
def mapRestExactCoprodL
    (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases)
    (nSum : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (rest : List (PairEntry sig hyps)) :
    List (PairEntry sig (hyps.push L)) :=
  let hL := Ctx.ofHyps_push hyps L
  let targetL := NegNeu.toRaw (NegNeu.weaken (B := L) nSum)
  rest.map (mapRestAbstractSumInl fuel σ hyps L R hL targetL)

/-- Evaluator’s `mapRestAbstractSumInr` on a remaining schedule. -/
def mapRestExactCoprodR
    (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases)
    (nSum : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (rest : List (PairEntry sig hyps)) :
    List (PairEntry sig (hyps.push R)) :=
  let hR := Ctx.ofHyps_push hyps R
  let targetR := NegNeu.toRaw (NegNeu.weaken (B := R) nSum)
  rest.map (mapRestAbstractSumInr fuel σ hyps L R hR targetR)

/-- Left η-substituted continuation from saturation’s `applyObsNeu` coprod arm. -/
abbrev exactCoprodPushContL
    {hyps : Array (Object sig.nBases)} {L R A : Object sig.nBases}
    (n : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A) :
    InvTm (Ctx.ofHyps (hyps.push L)) A :=
  coprodPushContL n cont

/-- Right η-substituted continuation from saturation’s `applyObsNeu` coprod arm. -/
abbrev exactCoprodPushContR
    {hyps : Array (Object sig.nBases)} {L R A : Object sig.nBases}
    (n : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (cont : InvTm (Ctx.ofHyps hyps) A) :
    InvTm (Ctx.ofHyps (hyps.push R)) A :=
  coprodPushContR n cont

/--
Evaluator-aligned left branch state for a recursive `CertifiedSchedule`: empty
worklist at `ofHyps (hyps.push L)`, counters stepped past the parent observation.
This matches `mapRestExactCoprodL` / `PairEntry` indexing — **not** the retained
encode `splitL` context `Γ ▻ .coprod L R ▻ L`.
-/
def afterExactCoprodL
    {hyps : Array (Object sig.nBases)} (L _R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    EncodeIx (sig := sig) (Ctx.ofHyps (hyps.push L)) where
  ws := []
  env := OriginEnv.ofHyps (hyps.push L)
  domNext := s.domNext
  obsNext := s.obsNext + 1

/-- Evaluator-aligned right branch state (symmetric to `afterExactCoprodL`). -/
def afterExactCoprodR
    {hyps : Array (Object sig.nBases)} (_L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    EncodeIx (sig := sig) (Ctx.ofHyps (hyps.push R)) where
  ws := []
  env := OriginEnv.ofHyps (hyps.push R)
  domNext := s.domNext
  obsNext := s.obsNext + 1

theorem afterExactCoprodL_boundary
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    AtSaturationBoundary (afterExactCoprodL L R s) :=
  rfl

theorem afterExactCoprodR_boundary
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    AtSaturationBoundary (afterExactCoprodR L R s) :=
  rfl

/--
Retained-encode left branch context after `bindObs` + `splitL`, reindexed to
`ofHyps (hyps.push (.coprod L R) |>.push L)`.

Same EncodeIx transition family as `retainedCoprodObsCertified`’s left arm —
**different hyps array** from `mapRestExactCoprodL`’s `hyps.push L`.
(Pop-to-boundary is not required to state the mismatch.)
-/
def afterExactCoprodL_retained
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    EncodeIx (sig := sig)
      (Ctx.ofHyps (hyps.push (.coprod L R) |>.push L)) :=
  let P : Object sig.nBases := .coprod L R
  let e := obsEntryOf s P
  let sSplit := (s.bindObs P).splitL e L
  have hctx :
      Ctx.ofHyps (hyps.push P |>.push L) =
        Ctx.ofHyps hyps ▻ P ▻ L := by
    calc
      Ctx.ofHyps (hyps.push P |>.push L)
          = Ctx.ofHyps (hyps.push P) ▻ L := Ctx.ofHyps_push (hyps.push P) L
      _ = Ctx.ofHyps hyps ▻ P ▻ L := by
            rw [Ctx.ofHyps_push hyps P]
  EncodeIx.castCtx hctx.symm sSplit

/-! ## Skip-binder transport spike (exact-coproduct prerequisite)

Contexts are intentionally unequal: legacy `Γ ▻ L` embeds into retained
`Γ ▻ .coprod L R ▻ L` by `Rename.skip1`. This section defines that embedding,
the legacy↔retained state transition, and checks whether the retained
observation origin is recoverable from the legacy branch state.
-/

/-- Snoc-form rename: `(Γ ▻ L) → (Γ ▻ .coprod L R ▻ L)`. -/
abbrev branchEmbedRenameL {Γ : Ctx sig} (L R : Object sig.nBases) :
    Rename sig (Γ ▻ L) (Γ ▻ .coprod L R ▻ L) :=
  Rename.skip1 (B := .coprod L R)

abbrev branchEmbedRenameR {Γ : Ctx sig} (L R : Object sig.nBases) :
    Rename sig (Γ ▻ R) (Γ ▻ .coprod L R ▻ R) :=
  Rename.skip1 (B := .coprod L R)

/--
`ofHyps` legacy term → retained snoc context via `ofHyps_push` then `skip1`.
No appeal to a finished expected term.
-/
def branchEmbedTermL
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    {X : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps (hyps.push L)) X) :
    InvTm (Ctx.ofHyps hyps ▻ .coprod L R ▻ L) X :=
  InvTm.rename (branchEmbedRenameL (Γ := Ctx.ofHyps hyps) L R)
    (InvTm.castCtx (Ctx.ofHyps_push hyps L) t)

def branchEmbedTermR
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    {X : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps (hyps.push R)) X) :
    InvTm (Ctx.ofHyps hyps ▻ .coprod L R ▻ R) X :=
  InvTm.rename (branchEmbedRenameR (Γ := Ctx.ofHyps hyps) L R)
    (InvTm.castCtx (Ctx.ofHyps_push hyps R) t)

/-- Retained left split state (snoc form) — target of packaging. -/
def retainedSplitL
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    EncodeIx (sig := sig) (Ctx.ofHyps hyps ▻ .coprod L R ▻ L) :=
  (s.bindObs (.coprod L R)).splitL (obsEntryOf s (.coprod L R)) L

def retainedSplitR
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    EncodeIx (sig := sig) (Ctx.ofHyps hyps ▻ .coprod L R ▻ R) :=
  (s.bindObs (.coprod L R)).splitR (obsEntryOf s (.coprod L R)) R

/-- Observation origin introduced by `bindObs` at parent `s` (explicit, not defeq). -/
def retainedObsOrigin (s : EncodeIx (sig := sig) Γ) : Origin sig :=
  .obs (sig := sig) s.obsNext

/--
Explicit transition witness between legacy `afterExactCoprodL` and `retainedSplitL`.
Bundles the related states; equality of the two EncodeIx values is not claimed.
-/
structure BranchStateTransitionL
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) where
  /-- Parent saturation boundary (needed for singleton-split worklist). -/
  boundary : AtSaturationBoundary s

/-- Counters agree (both stepped past the retained observation). -/
theorem branchState_domNext_eq
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    (afterExactCoprodL L R s).domNext = (retainedSplitL L R s).domNext :=
  rfl

theorem branchState_obsNext_eq
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    (afterExactCoprodL L R s).obsNext = (retainedSplitL L R s).obsNext :=
  rfl

theorem afterExactCoprodL_ws_nil
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    (afterExactCoprodL L R s).ws = [] :=
  rfl

/--
Under a parent boundary, retained left worklist is `pushPos` of the split
entry onto the empty tail (singleton when `L` is positive; empty when negative).
-/
theorem retainedSplitL_ws_of_boundary
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps))
    (hb : AtSaturationBoundary s) :
    (retainedSplitL L R s).ws =
      pushPos ([] : List (PosEntry sig))
        (.split (retainedObsOrigin s) false) L := by
  have hpos : objectPolarity (.coprod L R : Object sig.nBases) = .pos := by
    simp [objectPolarity_coprod]
  have hwsObs :
      (s.bindObs (.coprod L R)).ws = [obsEntryOf s (.coprod L R)] :=
    bindObs_ws_of_boundary s (.coprod L R) hb hpos
  simp only [retainedSplitL, retainedObsOrigin, EncodeIx.splitL, hwsObs, obsEntryOf,
    List.tail_cons]

/-- Retained env at the L binder is the split of the retained observation. -/
theorem retainedSplitL_env_here
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    (retainedSplitL L R s).env (Var.here : Var _ L) =
      .split (retainedObsOrigin s) false :=
  rfl

/--
Pullback of retained env along `skip1`: L carries `split obs false`;
Γ variables read through parent `s.env` (obs binder skipped).
-/
theorem retainedSplitL_env_rename_skip1_here
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    OriginEnv.rename (branchEmbedRenameL (Γ := Ctx.ofHyps hyps) L R)
        (retainedSplitL L R s).env
        (Var.here : Var (Ctx.ofHyps hyps ▻ L) L) =
      .split (retainedObsOrigin s) false :=
  rfl

theorem retainedSplitL_env_rename_skip1_there
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps))
    {A : Object sig.nBases} (x : Var (Ctx.ofHyps hyps) A) :
    OriginEnv.rename (branchEmbedRenameL (Γ := Ctx.ofHyps hyps) L R)
        (retainedSplitL L R s).env (.there x) =
      s.env x :=
  rfl

/-- Legacy `ofHyps` env on the newest binder is a hyp — never the retained obs. -/
theorem afterExactCoprodL_env_here_is_hyp
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    (afterExactCoprodL L R s).env (OriginEnv.herePush hyps L) =
      Origin.hyp (sig := sig) hyps.size := by
  simpa [afterExactCoprodL] using OriginEnv.ofHyps_here_push hyps L

/-- Every legacy `ofHyps` origin is a `hyp` (no `obs` / `split` / `dom`). -/
theorem afterExactCoprodL_env_is_hyp
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps))
    {A : Object sig.nBases} (x : Var (Ctx.ofHyps (hyps.push L)) A) :
    ∃ i, (afterExactCoprodL L R s).env x = .hyp (sig := sig) i :=
  ⟨(hyps.push L).size - 1 - Var.toRawIdx x, by
    simp [afterExactCoprodL, OriginEnv.ofHyps]⟩

/-- The retained observation origin does not appear anywhere in the legacy env. -/
theorem afterExactCoprodL_env_ne_obsOrigin
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps))
    {A : Object sig.nBases} (x : Var (Ctx.ofHyps (hyps.push L)) A) :
    (afterExactCoprodL L R s).env x ≠ retainedObsOrigin s := by
  obtain ⟨i, hi⟩ := afterExactCoprodL_env_is_hyp L R s x
  intro h
  simp [hi, retainedObsOrigin] at h

/--
Pullback mismatch on `here`: retained skip1-pullback carries `split obs`,
while legacy `ofHyps` weaken carries `hyp hyps.size`.
-/
theorem branchEmbed_env_here_mismatch
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    OriginEnv.rename (branchEmbedRenameL (Γ := Ctx.ofHyps hyps) L R)
        (retainedSplitL L R s).env
        (Var.here : Var (Ctx.ofHyps hyps ▻ L) L) ≠
      OriginEnv.weaken (A := L) (OriginEnv.ofHyps hyps)
        (.hyp (sig := sig) hyps.size)
        (Var.here : Var (Ctx.ofHyps hyps ▻ L) L) := by
  intro h
  have hret := retainedSplitL_env_rename_skip1_here L R s
  simp only [OriginEnv.weaken, OriginEnv.snoc] at h
  have : (Origin.split (retainedObsOrigin s) false : Origin sig) =
      .hyp (sig := sig) hyps.size := by
    rw [← hret, h]
  cases this

/-!
### Attempted certificate transport

Target law (generic in the produced term/cert):

```
Produced (afterExactCoprodL L R s) X →
Produced (retainedSplitL L R s) X
```

with term `branchEmbedTermL L R p.term`.

The retained *target state* (incl. `.obs s.obsNext` in `env`) is built from
parent `s`, not from the legacy `Produced` package. The legacy state’s env is
`OriginEnv.ofHyps (hyps.push L)`, which by `afterExactCoprodL_env_ne_obsOrigin`
never mentions that observation. Pullback along `skip1` therefore cannot be
matched to the legacy env (`branchEmbed_env_here_mismatch`: `split obs` vs
`hyp`).

So InvCert transport that requires env agreement under the embedding cannot
be obtained from the legacy certificate alone: the observation identity was
discarded when `afterExactCoprodL` replaced `s.env` by `ofHyps`.
-/

/-- Term component of the would-be transport (always definable). -/
def produced_branchEmbedTermL
    {hyps : Array (Object sig.nBases)} {L R X : Object sig.nBases}
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps))
    (p : Produced (afterExactCoprodL L R s) X) :
    InvTm (Ctx.ofHyps hyps ▻ .coprod L R ▻ L) X :=
  branchEmbedTermL L R p.term

/--
Spike test: an arbitrary certified legacy branch (`.unit`), no shape
classification beyond inhabitance of `Produced`.
-/
def spikeLegacyUnit
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    Produced (afterExactCoprodL L R s) (.unit : Object sig.nBases) where
  term := .unit
  cert := by
    change EncodeReady (afterExactCoprodL L R s).ws
      (afterExactCoprodL L R s).env
      (afterExactCoprodL L R s).domNext
      (afterExactCoprodL L R s).obsNext
      (.unit : InvTm _ .unit)
    simpa [afterExactCoprodL] using
      encodeReady_unit_nil (OriginEnv.ofHyps (hyps.push L))
        s.domNext (s.obsNext + 1)

theorem spikeLegacyUnit_embed_term
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps)) :
    produced_branchEmbedTermL s (spikeLegacyUnit L R s) =
      (.unit : InvTm (Ctx.ofHyps hyps ▻ .coprod L R ▻ L) .unit) := by
  simp [produced_branchEmbedTermL, branchEmbedTermL, spikeLegacyUnit,
    InvTm.castCtx_unit, InvTm.rename]

/--
Unit is encode-ready under *any* env at empty worklist, so the renamed unit
is ready at `retainedSplitL.pop` under the retained env — but that still uses
parent-derived `retainedSplitL`, not recovery from legacy env.
-/
theorem spikeUnit_ready_at_retained_pop
    {hyps : Array (Object sig.nBases)} (L R : Object sig.nBases)
    (s : EncodeIx (sig := sig) (Ctx.ofHyps hyps))
    (hb : AtSaturationBoundary s) :
    EncodeReady (sig := sig)
      (retainedSplitL L R s).pop.ws
      (retainedSplitL L R s).env
      (retainedSplitL L R s).domNext
      (retainedSplitL L R s).obsNext
      (.unit : InvTm _ .unit) := by
  have htail : (retainedSplitL L R s).pop.ws = [] := by
    rw [EncodeIx.pop, retainedSplitL_ws_of_boundary L R s hb]
    dsimp only [pushPos]
    split
    · simp [List.mergeSort_singleton]
    · rfl
  simpa [htail] using
    encodeReady_unit_nil (retainedSplitL L R s).env
      (retainedSplitL L R s).domNext (retainedSplitL L R s).obsNext

/-!
### Transport-spike STOP

**Outcome:** the generic skip-binder *term* embedding is fine
(`branchEmbedTermL` / `produced_branchEmbedTermL`). Counter and singleton-split
worklist compatibility under `AtSaturationBoundary` are fine
(`branchState_domNext_eq`, `branchState_obsNext_eq`,
`retainedSplitL_ws_of_boundary`).

**Failure mode:** the retained observation origin
(`retainedObsOrigin s = .obs s.obsNext`) is **not** present in
`afterExactCoprodL`’s `OriginEnv.ofHyps (hyps.push L)`
(`afterExactCoprodL_env_ne_obsOrigin`). The skip1 pullback of the retained env
carries `split obs` on `here`, while the legacy ofHyps weaken carries `hyp`
(`branchEmbed_env_here_mismatch`). That env is obtained from parent `s` via
`bindObs`/`splitL`, not from the legacy `Produced` package.

Therefore a generic
`Produced legacy → Produced retainedSplit` certificate transport cannot be
fed solely by the legacy state’s fields: the observation identity was
discarded when the legacy branch state was built from `ofHyps`.

**Representation conclusion:** `CertifiedSchedule` remains too coupled to
legacy `PairEntry` / `ofHyps` contexts for the retained EncodeIx path.
Repair is **retained-state-indexed schedule entries** (entries whose neutrals
and readiness live under the retained `EncodeIx` after `bindObs`/`split`),
not another ofHyps↔split rekey lemma.

Do not resume the full exact-coproduct schedule clause until that
representation shift is designed. Consistency / public evaluator still deferred.
-/

/-! ## Atom → coproduct example via `certifiedSchedule_exactAtom` -/

def TwoObsSig : Signature where
  nBases := 1
  generators := #[]

private abbrev Atom : Object TwoObsSig.nBases := .base ⟨0, by decide⟩
private abbrev SumA : Object TwoObsSig.nBases := .coprod Atom Atom
private abbrev atomB : Fin TwoObsSig.nBases := ⟨0, by decide⟩

def twoObsHyps : Array (Object TwoObsSig.nBases) :=
  #[.exp .unit Atom, .exp .unit SumA]

def twoObsEntry : EncodeIx (sig := TwoObsSig) (Ctx.ofHyps twoObsHyps) :=
  EncodeIx.entry (sig := TwoObsSig) twoObsHyps

theorem twoObsEntry_boundary : AtSaturationBoundary twoObsEntry := by
  simp only [AtSaturationBoundary, twoObsEntry, EncodeIx.entry, twoObsHyps,
    OriginEnv.posWorklist, OriginEnv.posCollect]
  native_decide

theorem twoObs_forcedRule_entry :
    forcedRule (sig := TwoObsSig) twoObsEntry.ws SumA = .focus := by
  simp only [twoObsEntry_boundary, forcedRule]

def twoObsAtom : NegNeu (Ctx.ofHyps twoObsHyps) Atom :=
  .app (.var (.there .here)) .unit

def twoObsSumOuter : NegNeu (Ctx.ofHyps twoObsHyps) SumA :=
  .app (.var .here) .unit

def twoObsσ : ReachState TwoObsSig.nBases :=
  runReachability (Ctx.ofHyps twoObsHyps).toReachCtx SumA

def twoObsRest : List (PairEntry TwoObsSig twoObsHyps) :=
  [.exact SumA twoObsSumOuter]

def twoObsAfterAtom : EncodeIx (sig := TwoObsSig)
    (Ctx.ofHyps (twoObsHyps.push Atom)) :=
  afterExactAtom (sig := TwoObsSig) atomB twoObsEntry

theorem twoObsAfterAtom_boundary :
    AtSaturationBoundary twoObsAfterAtom :=
  afterExactAtom_boundary (sig := TwoObsSig) atomB twoObsEntry twoObsEntry_boundary

theorem twoObsAfterAtom_forcedRule :
    forcedRule (sig := TwoObsSig) twoObsAfterAtom.ws SumA = .focus := by
  simp only [twoObsAfterAtom_boundary, forcedRule]

def twoObsRestMapped : List (PairEntry TwoObsSig (twoObsHyps.push Atom)) :=
  mapRestExactAtom (sig := TwoObsSig) 8 twoObsσ twoObsHyps atomB twoObsAtom twoObsRest

/-- Mapped second observation under the atom binder (same as `mapRestAbstractAtom`). -/
def twoObsSum : NegNeu (Ctx.ofHyps (twoObsHyps.push Atom)) SumA :=
  let hctx := Ctx.ofHyps_push twoObsHyps Atom
  let targetRaw := NegNeu.toRaw (NegNeu.weaken (B := Atom) twoObsAtom)
  let nA := NegNeu.abstractAtom (P := Atom) .here targetRaw
    (NegNeu.weaken (B := Atom) twoObsSumOuter)
  NegNeu.castCtx hctx.symm nA

theorem twoObsRestMapped_eq :
    twoObsRestMapped = [.exact SumA twoObsSum] :=
  rfl

def twoObsBranchL : InvTm (Ctx.ofHyps (twoObsHyps.push Atom) ▻ Atom) SumA :=
  .foc (.pos (.done (.inl (.neu (.var .here)))))

def twoObsBranchR : InvTm (Ctx.ofHyps (twoObsHyps.push Atom) ▻ Atom) SumA :=
  .foc (.pos (.done (.inr (.neu (.var .here)))))

def twoObsAfterSum : EncodeIx (sig := TwoObsSig)
    (Ctx.ofHyps (twoObsHyps.push Atom) ▻ SumA) :=
  twoObsAfterAtom.bindObs SumA

def twoObsSumEntry : PosEntry TwoObsSig := obsEntryOf twoObsAfterAtom SumA

theorem twoObs_splitL_ws :
    (twoObsAfterSum.splitL twoObsSumEntry Atom).ws =
      [{ origin := .split twoObsSumEntry.origin false, ty := Atom }] := by
  have hws := bindObs_ws_of_boundary twoObsAfterAtom SumA twoObsAfterAtom_boundary
    (by simp [SumA, objectPolarity_coprod])
  simp only [twoObsAfterSum, EncodeIx.splitL, hws, twoObsSumEntry, pushPos,
    List.tail_cons]
  native_decide

theorem twoObs_splitR_ws :
    (twoObsAfterSum.splitR twoObsSumEntry Atom).ws =
      [{ origin := .split twoObsSumEntry.origin true, ty := Atom }] := by
  have hws := bindObs_ws_of_boundary twoObsAfterAtom SumA twoObsAfterAtom_boundary
    (by simp [SumA, objectPolarity_coprod])
  simp only [twoObsAfterSum, EncodeIx.splitR, hws, twoObsSumEntry, pushPos,
    List.tail_cons]
  native_decide

theorem twoObs_branchL_cert :
    InvCert (twoObsAfterSum.splitL twoObsSumEntry Atom)
      (InvTm.rename (Rename.skip1 (B := SumA)) twoObsBranchL) := by
  set s := twoObsAfterSum.splitL twoObsSumEntry Atom
  have hws := twoObs_splitL_ws
  have hnil : EncodeReady (sig := TwoObsSig) [] s.env s.domNext s.obsNext
      (InvTm.rename (Rename.skip1 (B := SumA)) twoObsBranchL) :=
    .focus (by simp [forcedRule]) .pos
  change EncodeReady s.ws s.env s.domNext s.obsNext _
  rw [hws]
  exact EncodeReady.moveStable (by simp [forcedRule, Atom]) hnil

theorem twoObs_branchR_cert :
    InvCert (twoObsAfterSum.splitR twoObsSumEntry Atom)
      (InvTm.rename (Rename.skip1 (B := SumA)) twoObsBranchR) := by
  set s := twoObsAfterSum.splitR twoObsSumEntry Atom
  have hws := twoObs_splitR_ws
  have hnil : EncodeReady (sig := TwoObsSig) [] s.env s.domNext s.obsNext
      (InvTm.rename (Rename.skip1 (B := SumA)) twoObsBranchR) :=
    .focus (by simp [forcedRule]) .pos
  change EncodeReady s.ws s.env s.domNext s.obsNext _
  rw [hws]
  exact EncodeReady.moveStable (by simp [forcedRule, Atom]) hnil

theorem twoObs_splitL_state_eq :
    twoObsAfterSum.splitL twoObsSumEntry Atom =
      (twoObsAfterAtom.bindObs SumA).splitL (obsEntryOf twoObsAfterAtom SumA) Atom :=
  rfl

theorem twoObs_splitR_state_eq :
    twoObsAfterSum.splitR twoObsSumEntry Atom =
      (twoObsAfterAtom.bindObs SumA).splitR (obsEntryOf twoObsAfterAtom SumA) Atom :=
  rfl

def twoObsBranchL_produced : Produced
    ((twoObsAfterAtom.bindObs SumA).splitL (obsEntryOf twoObsAfterAtom SumA) Atom)
      SumA :=
  Produced.castState twoObs_splitL_state_eq
    ⟨InvTm.rename (Rename.skip1 (B := SumA)) twoObsBranchL, twoObs_branchL_cert⟩

def twoObsBranchR_produced : Produced
    ((twoObsAfterAtom.bindObs SumA).splitR (obsEntryOf twoObsAfterAtom SumA) Atom)
      SumA :=
  Produced.castState twoObs_splitR_state_eq
    ⟨InvTm.rename (Rename.skip1 (B := SumA)) twoObsBranchR, twoObs_branchR_cert⟩

/-- Inner coprod body (manual until coprod schedule clause). -/
def twoObsCoprodProduced : Produced twoObsAfterAtom SumA :=
  retainedCoprodObsCertified (sig := TwoObsSig) twoObsAfterAtom twoObsSum
    twoObsAfterAtom_boundary twoObsAfterAtom_forcedRule
    twoObsBranchL_produced twoObsBranchR_produced

/-- Recursive schedule result for the mapped rest (pack until coprod clause). -/
def twoObsInnerSchedule :
    CertifiedSchedule (sig := TwoObsSig) twoObsAfterAtom twoObsRestMapped SumA :=
  CertifiedSchedule.ofProduced twoObsRestMapped twoObsAfterAtom_boundary
    twoObsCoprodProduced

/-- Full example: exact-atom clause with arbitrary (here length-1) mapped rest. -/
def twoObsSchedule :
    CertifiedSchedule (sig := TwoObsSig) twoObsEntry
      (.exact Atom twoObsAtom :: twoObsRest) SumA :=
  certifiedSchedule_exactAtom (sig := TwoObsSig) twoObsEntry twoObs_forcedRule_entry
    twoObsAtom twoObsRest 8 twoObsσ twoObsInnerSchedule

def twoObsProduced : Produced twoObsEntry SumA :=
  twoObsSchedule.produced

theorem twoObs_encodes :
    ∃ c, encodeICC (OriginEnv.ofHyps (sig := TwoObsSig) twoObsHyps)
        twoObsProduced.term = some c :=
  certifiedSchedule_exactAtom_encodes (sig := TwoObsSig) twoObs_forcedRule_entry
    twoObsAtom twoObsRest 8 twoObsσ twoObsInnerSchedule

def twoObsCode_hyps : Option (ICCCode (Ctx.ofHyps twoObsHyps) SumA) :=
  encodeICCHyps (sig := TwoObsSig) twoObsProduced.term

theorem twoObsCode_hyps_isSome : twoObsCode_hyps.isSome = true := by
  native_decide

noncomputable def twoObsCode : ICCCode (Ctx.ofHyps twoObsHyps) SumA :=
  Classical.choose twoObs_encodes

theorem twoObsCode_encode_eq :
    encodeICC (OriginEnv.ofHyps (sig := TwoObsSig) twoObsHyps) twoObsProduced.term =
      some twoObsCode :=
  Classical.choose_spec twoObs_encodes

private def twoObs_encode_beq_hyps : Bool :=
  match encodeICC (OriginEnv.ofHyps (sig := TwoObsSig) twoObsHyps) twoObsProduced.term,
    twoObsCode_hyps with
  | some c, some d => ICCCode.beq c d
  | _, _ => false

theorem twoObs_encode_beq_hyps_true : twoObs_encode_beq_hyps = true := by
  native_decide

theorem twoObsCode_eq_hyps :
    some twoObsCode = twoObsCode_hyps := by
  have he := twoObsCode_encode_eq
  have hb := twoObs_encode_beq_hyps_true
  simp only [twoObs_encode_beq_hyps] at hb
  rw [he] at hb
  match hhyps : twoObsCode_hyps with
  | none => simp [hhyps] at hb
  | some d =>
      simp only [hhyps] at hb
      exact congrArg some (ICCCode.eq_of_beq twoObsCode d hb)

/-!
### Stop report

**Exact-atom clause:** landed.

**Exact-coproduct clause:** not resumed. Transport spike shows the skip1 *term*
embedding and counter/worklist compatibility work, but
`afterExactCoprodL`’s `ofHyps` env permanently discards the retained observation
origin. Generic `Produced` cert transport to `retainedSplitL` cannot recover it.
**Repair:** retained-state-indexed schedule entries — not more ofHyps rekey lemmas.

**Example:** `twoObsSchedule` still uses `ofProduced` for the inner coprod.

Public evaluator / comparator untouched.
-/

end Equality
end Gimbal
