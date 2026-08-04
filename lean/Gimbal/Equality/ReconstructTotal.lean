/-
  8D reconstruction-totality package over `certifiedRunReachability`.

  Domains (not arbitrary state / witnesses / commands):
  * stored neutral witness — `StoredNeutralDomain`
  * reconstructible invertible value — `InvertibleArgDomain`
  * requested neutral known-retrievable — `RequestedNeutralDomain`

  Intro-only witnesses never imply neutral reconstruction.
  Worker: well-founded `reconstructGoWF` (rank × phase × object size).
-/

import Gimbal.Equality.ReconstructWF
import Gimbal.Equality.ReachSound
import Gimbal.Equality.Saturation

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ## Certified completion package -/

/--
Completed certified reachability: projects to the computational runner and
carries index-range / result-type agreement (`ReachSound.reconOk`) plus ranks.
-/
structure CertifiedComplete (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases) where
  result : CertifiedReachResult sig.nBases
  soundFor : result.soundFor Γ goal
  sound : ReachSound Γ result.state

def certifiedComplete (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases) :
    CertifiedComplete (sig := sig) Γ goal where
  result := certifiedRunReachability Γ goal
  soundFor := certifiedRunReachability_soundFor Γ goal
  sound := by
    have hproj := certifiedRunReachability_project Γ goal
    have hs := runReachability_sound Γ goal
    rw [← hproj] at hs
    simpa [CertifiedReachResult.project] using hs

/-! ## Domain-scoped totality predicates (WF API) -/

/-- Every stored **neutral** witness reconstructs at its cell type under `Γ.hyps`. -/
def StoredWitnessReconstructsWF {Γ : ReachCtx sig.nBases}
    {goal : Object sig.nBases} (C : CertifiedComplete (sig := sig) Γ goal)
    (i : Nat) (b : SlotNew) (w : Witness) : Prop :=
  ∃ (A : Object sig.nBases) (n : NegNeu (Ctx.ofHyps (sig := sig) Γ.hyps) A),
    C.result.state.typeAt i = some A ∧
      Witness.isNeutral w = true ∧
      reconstructWitnessWF (sig := sig) C.result.cert i b Γ.hyps w = some ⟨A, n⟩

def ReconstructWitnessTotalWF (sig : Signature) : Prop :=
  ∀ (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases),
    let C := certifiedComplete (sig := sig) Γ goal
    ∀ (i : Nat) (b : SlotNew) (w : Witness),
      StoredNeutralDomain C.result.cert i b w →
        StoredWitnessReconstructsWF C i b w

/-- Consistency schedule entries reconstruct at the declared type. -/
def ConsistencyWitnessTotalWF (sig : Signature) : Prop :=
  ∀ (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases),
    let C := certifiedComplete (sig := sig) Γ goal
    let σ := C.result.state
    ∀ (P : Object sig.nBases) (w : Witness),
      (buildSchedule σ).entries.any (fun e => e.1 == P && e.2 == w) = true →
        ∃ (n : NegNeu (Ctx.ofHyps (sig := sig) Γ.hyps) P),
          ∃ i b,
            σ.typeAt i = some P ∧
              (σ.getCell i).slotWitness b = some w ∧
                reconstructWitnessWF (sig := sig) C.result.cert i b Γ.hyps w =
                  some ⟨P, n⟩

/-- Inconsistent completed states supply a reconstructable `.never` neutral. -/
def InconsistentNeverTotalWF (sig : Signature) : Prop :=
  ∀ (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases),
    let C := certifiedComplete (sig := sig) Γ goal
    C.result.state.inconsistent = true →
      (neuOfTypeWF (sig := sig) C.result.cert Γ.hyps
          (.never : Object sig.nBases)).isSome = true

/--
Invertible arguments under a strictly larger ambient rank reconstruct
(when `InvertibleArgDomain` holds).
-/
def InvertibleArgTotalWF (sig : Signature) : Prop :=
  ∀ (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases),
    let C := certifiedComplete (sig := sig) Γ goal
    ∀ (ambientRank : Nat) (A : Object sig.nBases),
      InvertibleArgDomain C.result.cert ambientRank A →
        (invOfTypeWF (sig := sig) C.result.cert ambientRank Γ.hyps A).isSome = true

/--
Requested neutrals that are hyp-or-ranked-retrievable reconstruct.
-/
def RequestedNeutralTotalWF (sig : Signature) : Prop :=
  ∀ (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases),
    let C := certifiedComplete (sig := sig) Γ goal
    ∀ (A : Object sig.nBases),
      RequestedNeutralDomain C.result.cert Γ.hyps A →
        (neuOfTypeWF (sig := sig) C.result.cert Γ.hyps A).isSome = true

/--
Full package: stored neutrals, invertible args, consistency, inconsistent-never,
and the none / type-mismatch branches are unreachable on domain-valid inputs.
-/
def ReconstructTotalityPackage (sig : Signature) : Prop :=
  ReconstructWitnessTotalWF sig ∧
    ConsistencyWitnessTotalWF sig ∧
    InconsistentNeverTotalWF sig ∧
    InvertibleArgTotalWF sig ∧
    RequestedNeutralTotalWF sig

/-! ## Legacy fueled names (migration bridge)

Prefer the WF predicates above. These aliases keep older call sites compiling
until fueled reconstruction is removed.
-/

/-- @deprecated use `StoredWitnessReconstructsWF` -/
def StoredWitnessReconstructs (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (i : Nat) (w : Witness) : Prop :=
  ∃ (A : Object sig.nBases) (n : NegNeu (Ctx.ofHyps (sig := sig) hyps) A),
    σ.typeAt i = some A ∧
      Witness.isNeutral w = true ∧
      ∃ fuel, reconstructWitness (sig := sig) fuel σ hyps w = some ⟨A, n⟩

/-- @deprecated use `ReconstructWitnessTotalWF` -/
def ReconstructWitnessTotal (sig : Signature) : Prop :=
  ∀ (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases),
    let σ := runReachability (n := sig.nBases) Γ goal
    ∀ (i : Nat) (w : Witness),
      i < σ.cells.size →
        ((σ.getCell i).oldWitness = some w ∨ (σ.getCell i).newWitness = some w) →
          Witness.isNeutral w = true →
            StoredWitnessReconstructs (sig := sig) σ Γ.hyps i w

/-- @deprecated use `ConsistencyWitnessTotalWF` -/
def ConsistencyWitnessTotal (sig : Signature) : Prop :=
  ∀ (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases),
    let σ := runReachability (n := sig.nBases) Γ goal
    ∀ (P : Object sig.nBases) (w : Witness),
      (buildSchedule σ).entries.any (fun e => e.1 == P && e.2 == w) = true →
        ∃ (n : NegNeu (Ctx.ofHyps (sig := sig) Γ.hyps) P) (fuel : Nat),
          reconstructWitness (sig := sig) fuel σ Γ.hyps w = some ⟨P, n⟩

/-- @deprecated use `InconsistentNeverTotalWF` -/
def InconsistentNeverTotal (sig : Signature) : Prop :=
  ∀ (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases),
    let σ := runReachability (n := sig.nBases) Γ goal
    σ.inconsistent = true →
      ∃ (n : NegNeu (Ctx.ofHyps (sig := sig) Γ.hyps) .never) (fuel : Nat),
        neuOfType (sig := sig) fuel σ Γ.hyps .never = some n

theorem InconsistentNeverTotalWF_of_package {sig : Signature}
    (h : ReconstructTotalityPackage sig) : InconsistentNeverTotalWF sig :=
  h.2.2.1

/-! ## Leaf reconstruction from `WitnessReconShape` -/

theorem reconstructGoWF_ctxVar {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) (hypIdx : Nat)
    {A : Object sig.nBases}
    (hshape : WitnessReconShape σ hyps A (.ctxVar hypIdx)) :
    ∃ n, reconstructGoWF (sig := sig) cert ambientRank (.witness hyps (.ctxVar hypIdx)) =
      some (.wit hyps ⟨A, n⟩) := by
  obtain ⟨x, hx⟩ := Ctx.varOldest_eq_of_getElem? (sig := sig) hyps hypIdx hshape
  refine ⟨.var x, ?_⟩
  simp [reconstructGoWF, hx]

theorem reconstructGoWF_fstHyp {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) (hypIdx : Nat)
    {A : Object sig.nBases}
    (hshape : WitnessReconShape σ hyps A (.fstHyp hypIdx)) :
    ∃ n, reconstructGoWF (sig := sig) cert ambientRank (.witness hyps (.fstHyp hypIdx)) =
      some (.wit hyps ⟨A, n⟩) := by
  obtain ⟨L, R, hhyps, hA⟩ := hshape
  subst hA
  obtain ⟨x, hx⟩ := Ctx.varOldest_eq_of_getElem? (sig := sig) hyps hypIdx hhyps
  refine ⟨.fst (NegNeu.cast (by rfl) (.var x)), ?_⟩
  simp [reconstructGoWF, hhyps, hx]

theorem reconstructGoWF_sndHyp {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) (hypIdx : Nat)
    {A : Object sig.nBases}
    (hshape : WitnessReconShape σ hyps A (.sndHyp hypIdx)) :
    ∃ n, reconstructGoWF (sig := sig) cert ambientRank (.witness hyps (.sndHyp hypIdx)) =
      some (.wit hyps ⟨A, n⟩) := by
  obtain ⟨L, R, hhyps, hA⟩ := hshape
  subst hA
  obtain ⟨x, hx⟩ := Ctx.varOldest_eq_of_getElem? (sig := sig) hyps hypIdx hhyps
  refine ⟨.snd (NegNeu.cast (by rfl) (.var x)), ?_⟩
  simp [reconstructGoWF, hhyps, hx]

/-! ## Status

Landed infrastructure for `ReconstructTotalityPackage`:
* WF worker `reconstructGoWF` (rank × phase × size) with rank-bounded
  `selectNeutralLt` / `selectNeutralLe` (no invOf→neuOf phase-only decrease)
* `WitnessReconShape` + `ReachSound.reconOk` (index-range / result-type)
* Domain predicates + package Prop over `certifiedRunReachability`
* Leaf reconstruction for `.ctxVar` / `.fstHyp` / `.sndHyp`

Remaining: WF induction for `.fstType` / `.sndType` / `.app` / `.appTy`,
invertible / requested / consistency / inconsistent-never, then fueled migration
and reachability cleanup.
-/

end Equality
end Gimbal
