/-
  Certified schedule composition at `AtSaturationBoundary`.

  Proof-relevant schedule results + generic nil and exact-atom recursive clauses.
  The atom→coproduct example instantiates the exact-atom clause.

  Does **not** change `applyObsNeu`, RawReference, totality, or `referenceCompare`.
  Coproduct / consistency schedule clauses are deferred.
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

Coproduct recursive clause and consistency entries: deferred.
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

**Generic exact-atom clause:** `certifiedSchedule_nil`, `certifiedSchedule_exactAtom`
with arbitrary `rest` and arbitrary recursive `CertifiedSchedule` for
`mapRestExactAtom rest`. Erasure + encode theorems included.
Uses real `atomPushCont` / `mapRestAbstractAtom`.

**Example:** `twoObsSchedule` instantiates exact-atom; inner coprod is
`CertifiedSchedule.ofProduced` until the coprod clause exists.

**Not blocked** on abstr/rekey naturality for this clause — readiness comes from
the recursive `Produced`, not from transporting a parent continuation’s cert.

Public evaluator / comparator untouched. Next: coprod clause (rekey rest into
both branches); consistency last.
-/

end Equality
end Gimbal
