/-
  Two-observation EncodeIx schedule composition at `AtSaturationBoundary`.

  Atom observation, then (after `moveStable` restores the boundary) a retained
  coproduct observation. Certificates and codes are compositional.

  Does **not** change `applyObsNeu`, RawReference, totality, or `referenceCompare`.
-/

import Gimbal.Equality.ICCEncodeIx
import Gimbal.Equality.ICCPeel

namespace Gimbal
namespace Equality

/-! ## Atom → coproduct schedule fragment

Phase: observe an atom, invert it (`moveStable` → boundary), then observe a
coproduct and invert via `retainedCoprodObsCertified`.
-/

def TwoObsSig : Signature where
  nBases := 1
  generators := #[]

private abbrev Atom : Object TwoObsSig.nBases := .base ⟨0, by decide⟩
private abbrev SumA : Object TwoObsSig.nBases := .coprod Atom Atom

/-- Hyps: `f : unit → Atom`, `g : unit → Atom+Atom` (newest last). -/
def twoObsHyps : Array (Object TwoObsSig.nBases) :=
  #[.exp .unit Atom, .exp .unit SumA]

def twoObsΓ : Ctx TwoObsSig := Ctx.ofHyps (sig := TwoObsSig) twoObsHyps

def twoObsEntry : EncodeIx (sig := TwoObsSig) twoObsΓ :=
  EncodeIx.entry (sig := TwoObsSig) twoObsHyps

theorem twoObsEntry_boundary : AtSaturationBoundary twoObsEntry := by
  simp only [AtSaturationBoundary, twoObsEntry, EncodeIx.entry, twoObsHyps,
    OriginEnv.posWorklist, OriginEnv.posCollect]
  native_decide

theorem twoObs_forcedRule_entry :
    forcedRule (sig := TwoObsSig) twoObsEntry.ws SumA = .focus := by
  simp only [twoObsEntry_boundary, forcedRule]

/-- First observation: `f ()`. -/
def twoObsAtom : NegNeu twoObsΓ Atom :=
  .app (.var (.there .here)) .unit

/-- After binding the atom, `g ()` under the fresh binder. -/
def twoObsSum : NegNeu (twoObsΓ ▻ Atom) SumA :=
  .app (.var (.there .here)) .unit

def twoObsBranchL : InvTm (twoObsΓ ▻ Atom ▻ Atom) SumA :=
  .foc (.pos (.done (.inl (.neu (.var .here)))))

def twoObsBranchR : InvTm (twoObsΓ ▻ Atom ▻ Atom) SumA :=
  .foc (.pos (.done (.inr (.neu (.var .here)))))

/-! ### Boundary restored after the atom observation -/

def twoObsAfterAtom : EncodeIx (sig := TwoObsSig) (twoObsΓ ▻ Atom) :=
  (twoObsEntry.bindObs Atom).pop

theorem twoObsAfterAtom_boundary :
    AtSaturationBoundary twoObsAfterAtom :=
  bindObs_pop_boundary twoObsEntry Atom twoObsEntry_boundary rfl

theorem twoObsAfterAtom_forcedRule :
    forcedRule (sig := TwoObsSig) twoObsAfterAtom.ws SumA = .focus := by
  simp only [twoObsAfterAtom_boundary, forcedRule]

theorem twoObsAfterAtom_obsNext :
    twoObsAfterAtom.obsNext = 1 := by
  simp only [twoObsAfterAtom, EncodeIx.pop, EncodeIx.bindObs, twoObsEntry,
    EncodeIx.entry]

/-! ### Coproduct branches at the second observation -/

def twoObsSumEntry : PosEntry TwoObsSig :=
  obsEntryOf twoObsAfterAtom SumA

theorem twoObsSumEntry_eq :
    twoObsSumEntry = ⟨.obs (sig := TwoObsSig) 1, SumA⟩ := by
  simp only [twoObsSumEntry, obsEntryOf, twoObsAfterAtom_obsNext]

def twoObsAfterSum : EncodeIx (sig := TwoObsSig) (twoObsΓ ▻ Atom ▻ SumA) :=
  twoObsAfterAtom.bindObs SumA

theorem twoObs_splitL_ws :
    (twoObsAfterSum.splitL twoObsSumEntry Atom).ws =
      [{ origin := .split (.obs (sig := TwoObsSig) 1) false, ty := Atom }] := by
  have hbound := twoObsAfterAtom_boundary
  have hpos : objectPolarity SumA = .pos := by simp [SumA, objectPolarity_coprod]
  have hws := bindObs_ws_of_boundary twoObsAfterAtom SumA hbound hpos
  simp only [twoObsAfterSum, EncodeIx.splitL, hws, twoObsSumEntry, obsEntryOf,
    twoObsAfterAtom_obsNext, pushPos, List.tail_cons]
  native_decide

theorem twoObs_splitR_ws :
    (twoObsAfterSum.splitR twoObsSumEntry Atom).ws =
      [{ origin := .split (.obs (sig := TwoObsSig) 1) true, ty := Atom }] := by
  have hbound := twoObsAfterAtom_boundary
  have hpos : objectPolarity SumA = .pos := by simp [SumA, objectPolarity_coprod]
  have hws := bindObs_ws_of_boundary twoObsAfterAtom SumA hbound hpos
  simp only [twoObsAfterSum, EncodeIx.splitR, hws, twoObsSumEntry, obsEntryOf,
    twoObsAfterAtom_obsNext, pushPos, List.tail_cons]
  native_decide

theorem twoObs_branchL_cert :
    InvCert (twoObsAfterSum.splitL twoObsSumEntry Atom)
      (InvTm.rename (Rename.skip1 (B := SumA)) twoObsBranchL) := by
  set s := twoObsAfterSum.splitL twoObsSumEntry Atom
  have hws := twoObs_splitL_ws
  have hnil : EncodeReady (sig := TwoObsSig) [] s.env s.domNext s.obsNext
      (InvTm.rename (Rename.skip1 (B := SumA)) twoObsBranchL) :=
    .focus (by simp [forcedRule]) .pos
  have hfr : forcedRule (sig := TwoObsSig)
      ([{ origin := .split (.obs (sig := TwoObsSig) 1) false, ty := Atom }] :
        List (PosEntry TwoObsSig)) SumA =
      .moveStable ⟨.split (.obs (sig := TwoObsSig) 1) false, Atom⟩ := by
    simp [forcedRule, Atom]
  change EncodeReady s.ws s.env s.domNext s.obsNext _
  rw [hws]
  exact EncodeReady.moveStable hfr hnil

theorem twoObs_branchR_cert :
    InvCert (twoObsAfterSum.splitR twoObsSumEntry Atom)
      (InvTm.rename (Rename.skip1 (B := SumA)) twoObsBranchR) := by
  set s := twoObsAfterSum.splitR twoObsSumEntry Atom
  have hws := twoObs_splitR_ws
  have hnil : EncodeReady (sig := TwoObsSig) [] s.env s.domNext s.obsNext
      (InvTm.rename (Rename.skip1 (B := SumA)) twoObsBranchR) :=
    .focus (by simp [forcedRule]) .pos
  have hfr : forcedRule (sig := TwoObsSig)
      ([{ origin := .split (.obs (sig := TwoObsSig) 1) true, ty := Atom }] :
        List (PosEntry TwoObsSig)) SumA =
      .moveStable ⟨.split (.obs (sig := TwoObsSig) 1) true, Atom⟩ := by
    simp [forcedRule, Atom]
  change EncodeReady s.ws s.env s.domNext s.obsNext _
  rw [hws]
  exact EncodeReady.moveStable hfr hnil

/-- Align `twoObsAfterSum` with `(twoObsAfterAtom.bindObs SumA)` naming. -/
theorem twoObs_splitL_state_eq :
    twoObsAfterSum.splitL twoObsSumEntry Atom =
      (twoObsAfterAtom.bindObs SumA).splitL (obsEntryOf twoObsAfterAtom SumA) Atom := by
  simp only [twoObsAfterSum, twoObsSumEntry]

theorem twoObs_splitR_state_eq :
    twoObsAfterSum.splitR twoObsSumEntry Atom =
      (twoObsAfterAtom.bindObs SumA).splitR (obsEntryOf twoObsAfterAtom SumA) Atom := by
  simp only [twoObsAfterSum, twoObsSumEntry]

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

/-- Second observation: retained coproduct at the restored boundary. -/
def twoObsCoprodProduced : Produced twoObsAfterAtom SumA :=
  retainedCoprodObsCertified (sig := TwoObsSig) twoObsAfterAtom twoObsSum
    twoObsAfterAtom_boundary twoObsAfterAtom_forcedRule
    twoObsBranchL_produced twoObsBranchR_produced

/-- Full atom → coproduct production at phase entry. -/
def twoObsProduced : Produced twoObsEntry SumA :=
  retainedAtomObsCertified (sig := TwoObsSig) twoObsEntry twoObsAtom
    twoObsEntry_boundary twoObs_forcedRule_entry twoObsCoprodProduced

theorem twoObs_after_atom_still_boundary :
    AtSaturationBoundary ((twoObsEntry.bindObs Atom).pop) :=
  twoObsAfterAtom_boundary

/-! ### Codes: compositional encode + propositional `ICCCode` equality -/

theorem twoObs_entryReady : EntryReady (sig := TwoObsSig) twoObsProduced.term := by
  simpa [EntryReady, InvCert, twoObsEntry, EncodeIx.entry, twoObsΓ] using
    twoObsProduced.cert

/-- Computable encode of the two-observation term (for `native_decide`). -/
def twoObsCode_hyps : Option (ICCCode twoObsΓ SumA) :=
  encodeICCHyps (sig := TwoObsSig) twoObsProduced.term

theorem twoObsCode_hyps_isSome : twoObsCode_hyps.isSome = true := by
  native_decide

noncomputable def twoObsCode : ICCCode twoObsΓ SumA :=
  Classical.choose (entryReady_encode_some twoObs_entryReady)

theorem twoObsCode_encode_eq :
    encodeICC (OriginEnv.ofHyps (sig := TwoObsSig) twoObsHyps) twoObsProduced.term =
      some twoObsCode :=
  Classical.choose_spec (entryReady_encode_some twoObs_entryReady)

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
### Schedule-composition stop report

**Boundary invariant:** `AtSaturationBoundary` (`ws = []`) is required by
`retainedAtomObsCertified` / `retainedCoprodObsCertified`. Audit: every
`forcedRule = .focus` path has empty `ws`; encode enters `letPos` only via focus /
right-foc. No EncodeIx observation introduction with nonempty parent worklist
found — constructor not weakened.

**Two-observation sequence:** atom `letPos` → `moveStable` restores boundary →
retained coprod `letPos`. `twoObs_after_atom_still_boundary` records the return.
Codes agree as `ICCCode` equality via `ICCCode.eq_of_beq` / `beq_iff_eq`.

Public evaluator, RawReference, totality, and comparator untouched.
-/

end Equality
end Gimbal
