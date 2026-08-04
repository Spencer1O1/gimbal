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
      InvertibleArgDomain C.result.cert ambientRank Γ.hyps A →
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

/-! ## Bounded neutral selection from a ranked neutral parent -/

theorem ReachRankCert.tryNeutralSlot_eq_some {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (ok : Nat → Bool)
    {w : Witness} {r : Nat}
    (hw : (σ.getCell i).slotWitness b = some w)
    (hne : Witness.isNeutral w = true)
    (hr : cert.rank i b = some r)
    (hok : ok r = true) :
    cert.tryNeutralSlot i b ok = some (w, r) := by
  simp [ReachRankCert.tryNeutralSlot, hw, hne, hr, hok]

theorem ReachRankCert.selectNeutralLt_isSome_of_ranked_neutral {n : Nat}
    {σ : ReachState n} (cert : ReachRankCert σ) (i ambient : Nat)
    {b : SlotNew} {w : Witness} {r : Nat}
    (hw : (σ.getCell i).slotWitness b = some w)
    (hne : Witness.isNeutral w = true)
    (hr : cert.rank i b = some r)
    (hlt : r < ambient) :
    ∃ w' r', cert.selectNeutralLt i ambient = some (w', r') := by
  have htry :=
    cert.tryNeutralSlot_eq_some i b (fun r => decide (r < ambient)) hw hne hr
      (decide_eq_true hlt)
  cases b with
  | true =>
      refine ⟨w, r, ?_⟩
      simpa [ReachRankCert.selectNeutralLt, htry]
  | false =>
      cases hnew : cert.tryNeutralSlot i true (fun r => decide (r < ambient)) with
      | some wr =>
          refine ⟨wr.1, wr.2, ?_⟩
          simp [ReachRankCert.selectNeutralLt, hnew]
      | none =>
          refine ⟨w, r, ?_⟩
          simpa [ReachRankCert.selectNeutralLt, hnew, htry]

/-- From a stored projection/app witness + certified `neutralParent_lt` at its rank,
the selected neutral parent is available strictly below any ambient `≥` child rank. -/
theorem ReachRankCert.selectNeutralLt_of_fstType {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i ambient : Nat) {b : SlotNew} {r : Nat} {p : Nat}
    (hw : (σ.getCell i).slotWitness b = some (.fstType p))
    (hr : cert.rank i b = some r)
    (hle : r ≤ ambient) :
    ∃ w' r', cert.selectNeutralLt p ambient = some (w', r') := by
  obtain ⟨bP, wP, rP, hwP, hne, hrP, hlt⟩ :=
    cert.neutralParent_lt i b r (.fstType p) hr hw
  exact cert.selectNeutralLt_isSome_of_ranked_neutral p ambient hwP hne hrP
    (Nat.lt_of_lt_of_le hlt hle)

theorem ReachRankCert.selectNeutralLt_of_sndType {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i ambient : Nat) {b : SlotNew} {r : Nat} {p : Nat}
    (hw : (σ.getCell i).slotWitness b = some (.sndType p))
    (hr : cert.rank i b = some r)
    (hle : r ≤ ambient) :
    ∃ w' r', cert.selectNeutralLt p ambient = some (w', r') := by
  obtain ⟨bP, wP, rP, hwP, hne, hrP, hlt⟩ :=
    cert.neutralParent_lt i b r (.sndType p) hr hw
  exact cert.selectNeutralLt_isSome_of_ranked_neutral p ambient hwP hne hrP
    (Nat.lt_of_lt_of_le hlt hle)

theorem ReachRankCert.selectNeutralLt_of_appTy {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i ambient : Nat) {b : SlotNew} {r : Nat}
    {fn arg : Nat}
    (hw : (σ.getCell i).slotWitness b = some (.appTy fn arg))
    (hr : cert.rank i b = some r)
    (hle : r ≤ ambient) :
    ∃ w' r', cert.selectNeutralLt fn ambient = some (w', r') := by
  obtain ⟨bP, wP, rP, hwP, hne, hrP, hlt⟩ :=
    cert.neutralParent_lt i b r (.appTy fn arg) hr hw
  exact cert.selectNeutralLt_isSome_of_ranked_neutral fn ambient hwP hne hrP
    (Nat.lt_of_lt_of_le hlt hle)

/-! ## Recursive witness cases

Explicit decreases: parent `neuOf` via `selectNeutralLt` (rank ↓);
`.app` / `.appTy` also use same-ambient `invOf` (phase ↓).
-/

theorem reconstructGoWF_fstType {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) (pIdx : Nat)
    {A : Object sig.nBases}
    (hshape : WitnessReconShape σ hyps A (.fstType pIdx))
    {wP : Witness} {rP : Nat}
    (hsel : cert.selectNeutralLt pIdx ambientRank = some (wP, rP))
    (hneOf : ∀ {L R : Object sig.nBases},
      σ.typeAt pIdx = some (.prod L R) → A = L →
        ∃ (n : NegNeu (Ctx.ofHyps (sig := sig) hyps) (.prod L R)),
          reconstructGoWF (sig := sig) cert rP (.neuOf hyps (.prod L R)) =
            some (.neu hyps (.prod L R) n)) :
    ∃ n, reconstructGoWF (sig := sig) cert ambientRank (.witness hyps (.fstType pIdx)) =
      some (.wit hyps ⟨A, n⟩) := by
  obtain ⟨L, R, hty, hA⟩ := hshape
  subst hA
  obtain ⟨n, hn⟩ := hneOf hty rfl
  refine ⟨.fst n, ?_⟩
  rw [reconstructGoWF.eq_5, hty]
  cases hsel' : cert.selectNeutralLt pIdx ambientRank with
  | none => cases hsel'.symm.trans hsel
  | some wr =>
      have hwr : wr = (wP, rP) := Option.some.inj (hsel'.symm.trans hsel)
      subst hwr
      simp [hn, NegNeu.castHyps, NegNeu.castCtx, NegNeu.cast]
theorem reconstructGoWF_sndType {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) (pIdx : Nat)
    {A : Object sig.nBases}
    (hshape : WitnessReconShape σ hyps A (.sndType pIdx))
    {wP : Witness} {rP : Nat}
    (hsel : cert.selectNeutralLt pIdx ambientRank = some (wP, rP))
    (hneOf : ∀ {L R : Object sig.nBases},
      σ.typeAt pIdx = some (.prod L R) → A = R →
        ∃ (n : NegNeu (Ctx.ofHyps (sig := sig) hyps) (.prod L R)),
          reconstructGoWF (sig := sig) cert rP (.neuOf hyps (.prod L R)) =
            some (.neu hyps (.prod L R) n)) :
    ∃ n, reconstructGoWF (sig := sig) cert ambientRank (.witness hyps (.sndType pIdx)) =
      some (.wit hyps ⟨A, n⟩) := by
  obtain ⟨L, R, hty, hA⟩ := hshape
  subst hA
  obtain ⟨n, hn⟩ := hneOf hty rfl
  refine ⟨.snd n, ?_⟩
  rw [reconstructGoWF.eq_6, hty]
  cases hsel' : cert.selectNeutralLt pIdx ambientRank with
  | none => cases hsel'.symm.trans hsel
  | some wr =>
      have hwr : wr = (wP, rP) := Option.some.inj (hsel'.symm.trans hsel)
      subst hwr
      simp [hn, NegNeu.castHyps, NegNeu.castCtx, NegNeu.cast]
theorem reconstructGoWF_app {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) (fnHypIdx argIdx : Nat)
    {A : Object sig.nBases}
    (hshape : WitnessReconShape σ hyps A (.app fnHypIdx argIdx))
    (hinv : ∀ {Arg Ret : Object sig.nBases},
      hyps[fnHypIdx]? = some (.exp Arg Ret) →
        σ.typeAt argIdx = some Arg → A = Ret →
          ∃ (t : InvTm (Ctx.ofHyps (sig := sig) hyps) Arg),
            reconstructGoWF (sig := sig) cert ambientRank (.invOf hyps Arg) =
              some (.inv hyps Arg t)) :
    ∃ n, reconstructGoWF (sig := sig) cert ambientRank
        (.witness hyps (.app fnHypIdx argIdx)) =
      some (.wit hyps ⟨A, n⟩) := by
  obtain ⟨Arg, Ret, hfn, harg, hA⟩ := hshape
  subst hA
  obtain ⟨x, hx⟩ := Ctx.varOldest_eq_of_getElem? (sig := sig) hyps fnHypIdx hfn
  obtain ⟨t, ht⟩ := hinv hfn harg rfl
  refine ⟨.app (.var x) t, ?_⟩
  rw [reconstructGoWF.eq_7]
  simp [hfn, harg, hx, ht, NegNeu.cast, InvTm.castHyps, InvTm.castCtx, InvTm.castTy]

theorem reconstructGoWF_appTy {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) (fnTypeIdx argIdx : Nat)
    {A : Object sig.nBases}
    (hshape : WitnessReconShape σ hyps A (.appTy fnTypeIdx argIdx))
    {wFn : Witness} {rFn : Nat}
    (hsel : cert.selectNeutralLt fnTypeIdx ambientRank = some (wFn, rFn))
    (hneOf : ∀ {Arg Ret : Object sig.nBases},
      σ.typeAt fnTypeIdx = some (.exp Arg Ret) →
        σ.typeAt argIdx = some Arg → A = Ret →
          ∃ (n : NegNeu (Ctx.ofHyps (sig := sig) hyps) (.exp Arg Ret)),
            reconstructGoWF (sig := sig) cert rFn (.neuOf hyps (.exp Arg Ret)) =
              some (.neu hyps (.exp Arg Ret) n))
    (hinv : ∀ {Arg Ret : Object sig.nBases},
      σ.typeAt fnTypeIdx = some (.exp Arg Ret) →
        σ.typeAt argIdx = some Arg → A = Ret →
          ∃ (t : InvTm (Ctx.ofHyps (sig := sig) hyps) Arg),
            reconstructGoWF (sig := sig) cert ambientRank (.invOf hyps Arg) =
              some (.inv hyps Arg t)) :
    ∃ n, reconstructGoWF (sig := sig) cert ambientRank
        (.witness hyps (.appTy fnTypeIdx argIdx)) =
      some (.wit hyps ⟨A, n⟩) := by
  obtain ⟨Arg, Ret, hfn, harg, hA⟩ := hshape
  subst hA
  obtain ⟨n, hn⟩ := hneOf hfn harg rfl
  obtain ⟨t, ht⟩ := hinv hfn harg rfl
  refine ⟨.app n t, ?_⟩
  rw [reconstructGoWF.eq_8]
  simp only [hfn, harg, ↓reduceIte]
  cases hsel' : cert.selectNeutralLt fnTypeIdx ambientRank with
  | none => cases hsel'.symm.trans hsel
  | some wr =>
      have hwr : wr = (wFn, rFn) := Option.some.inj (hsel'.symm.trans hsel)
      subst hwr
      simp [hn, ht, NegNeu.castHyps, NegNeu.castCtx, NegNeu.cast,
        InvTm.castHyps, InvTm.castCtx, InvTm.castTy]

/-! ## InvertibleArgDomain boundary fixtures -/

private abbrev Sig1 : Signature := ⟨1, #[]⟩
private abbrev Sig2b : Signature := ⟨2, #[]⟩

private def bareBaseΓ : ReachCtx 1 := ⟨#[], 0⟩
private def bareBaseC : CertifiedComplete (sig := Sig1) bareBaseΓ (.base 0) :=
  certifiedComplete (sig := Sig1) bareBaseΓ (.base 0)

/-- Bare positive base: no hyp, not unit, not simply deducible → outside domain. -/
theorem invertibleArg_bareBase_outside :
    ¬ InvertibleArgDomain bareBaseC.result.cert 0 bareBaseΓ.hyps (.base 0) := by
  have hproj : bareBaseC.result.state = runReachability bareBaseΓ (.base 0) :=
    bareBaseC.soundFor
  have hhyp : (findHypVar (sig := Sig1) bareBaseΓ.hyps (.base 0)).isSome = false := by
    native_decide
  refine InvertibleArgDomain.not_of_unsupported bareBaseC.result.cert 0 bareBaseΓ.hyps
    (.base 0) hhyp (by decide) ?_
  intro i hfind
  have hfind' : (runReachability bareBaseΓ (.base 0)).findTypeIdx (.base 0) = some i := by
    rwa [← hproj]
  have hsd : isSimplyDeducible (runReachability bareBaseΓ (.base 0)) (.base 0) = false := by
    native_decide
  simp only [isSimplyDeducible, hfind'] at hsd
  simpa [hproj] using hsd

private def neverΓ : ReachCtx 1 := ⟨#[], 0⟩
private def neverC : CertifiedComplete (sig := Sig1) neverΓ (.never) :=
  certifiedComplete (sig := Sig1) neverΓ (.never)

/-- `.never` with no hyp/rank support is outside the domain. -/
theorem invertibleArg_never_outside :
    ¬ InvertibleArgDomain neverC.result.cert 0 neverΓ.hyps (.never : Object 1) := by
  have hproj : neverC.result.state = runReachability neverΓ (.never) :=
    neverC.soundFor
  have hhyp : (findHypVar (sig := Sig1) neverΓ.hyps (.never : Object 1)).isSome = false := by
    native_decide
  refine InvertibleArgDomain.not_of_unsupported neverC.result.cert 0 neverΓ.hyps
    (.never : Object 1) hhyp (by decide) ?_
  intro i hfind
  have hfind' : (runReachability neverΓ (.never)).findTypeIdx (.never : Object 1) = some i := by
    rwa [← hproj]
  have hsd :
      (match (runReachability neverΓ (.never)).findTypeIdx (.never : Object 1) with
       | some j => ((runReachability neverΓ (.never)).getCell j).simplyDeducible
       | none => false) = false := by
    native_decide
  simp only [hfind'] at hsd
  simpa [hproj] using hsd

/-- `.unit` is always inside the domain. -/
theorem invertibleArg_unit_inside {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) :
    InvertibleArgDomain cert ambientRank hyps .unit :=
  InvertibleArgDomain.of_unit cert ambientRank hyps

/-- A negative hypothesis is inside via `findHypVar`. -/
theorem invertibleArg_negHyp_inside :
    let hyps : Array (Object 2) := #[.prod (.base 0) (.base 1)]
    let cert := ReachRankCert.emptyTable (n := 2) hyps
    InvertibleArgDomain (sig := Sig2b) cert 0 hyps (.prod (.base 0) (.base 1)) := by
  apply InvertibleArgDomain.of_hyp
  native_decide

/--
η-constructed product argument: ranked intro at the product cell puts `Arg` in
domain below a strictly larger ambient (as in `hypApp` / `RankedParents.freshRank`).
-/
theorem invertibleArg_etaProd_inside_of_ranked {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) (pIdx : Nat) {b : SlotNew} {r : Nat}
    {L R : Object sig.nBases}
    (hfind : σ.findTypeIdx (.prod L R) = some pIdx)
    (hr : cert.rank pIdx b = some r) (hlt : r < ambientRank) :
    InvertibleArgDomain cert ambientRank hyps (.prod L R) :=
  InvertibleArgDomain.of_ranked_lt cert ambientRank hyps (.prod L R) hfind hr hlt

/-! ## Bridge lemmas for WF totality -/

theorem ReachCell.slotWitness_empty (b : SlotNew) :
    ReachCell.empty.slotWitness b = none := by
  cases b <;> rfl

theorem ReachState.lt_cells_of_slotWitness {n : Nat} {σ : ReachState n}
    {i : Nat} {b : SlotNew} {w : Witness}
    (h : (σ.getCell i).slotWitness b = some w) : i < σ.cells.size := by
  cases hc : σ.cells[i]? with
  | none =>
      have heq : σ.getCell i = ReachCell.empty := by
        simp [ReachState.getCell, hc]
      rw [heq, ReachCell.slotWitness_empty] at h
      cases h
  | some c =>
      exact (Array.getElem?_eq_some_iff.mp hc).1

theorem ReachState.typeAt_isSome_of_lt_sized {n : Nat} {σ : ReachState n}
    {i : Nat} (hsz : ReachState.Sized σ) (hi : i < σ.cells.size) :
    ∃ A, σ.typeAt i = some A := by
  have hi' : i < σ.types.size := by
    rw [ReachState.Sized] at hsz
    rwa [← hsz]
  refine ⟨σ.types[i], ?_⟩
  simp [ReachState.typeAt, Array.getElem?_eq_getElem hi']

theorem ReachCell.neutralWitness_slot {c : ReachCell} {w : Witness}
    (h : c.neutralWitness = some w) :
    (c.newNeutral = true ∧ c.slotWitness true = some w) ∨
      (c.newNeutral = false ∧ c.slotWitness false = some w) := by
  dsimp [ReachCell.neutralWitness, ReachCell.newNeutral, ReachCell.slotWitness] at h ⊢
  cases hn : c.newWitness with
  | some wN =>
      simp only [hn] at h ⊢
      cases hneN : Witness.isNeutral wN
      · simp only [hneN] at h
        cases ho : c.oldWitness with
        | some wO =>
            simp only [ho] at h ⊢
            cases hneO : Witness.isNeutral wO
            · simp [hneO] at h
            · simp only [hneO] at h
              cases h
              exact Or.inr ⟨by simp [hn, hneN], rfl⟩
        | none => simp [ho] at h
      · simp only [hneN] at h
        cases h
        exact Or.inl ⟨by simp [hn, hneN], rfl⟩
  | none =>
      simp only [hn] at h ⊢
      cases ho : c.oldWitness with
      | some wO =>
          simp only [ho] at h ⊢
          cases hneO : Witness.isNeutral wO
          · simp [hneO] at h
          · simp only [hneO] at h
            cases h
            exact Or.inr ⟨by simp [hn], rfl⟩
      | none => simp [ho] at h

theorem ReachCell.neutralWitness_isNeutral {c : ReachCell} {w : Witness}
    (h : c.neutralWitness = some w) : Witness.isNeutral w = true := by
  dsimp [ReachCell.neutralWitness] at h
  split at h
  · next wN =>
      split at h
      · cases h; assumption
      · split at h
        · next wO =>
            split at h
            · cases h; assumption
            · cases h
        · cases h
  · next =>
      split at h
      · next wO =>
          split at h
          · cases h; assumption
          · cases h
      · cases h

theorem ReachRankCert.selectNeutralLe_isSome_of_ranked_neutral {n : Nat}
    {σ : ReachState n} (cert : ReachRankCert σ) (i ambient : Nat)
    {b : SlotNew} {w : Witness} {r : Nat}
    (hw : (σ.getCell i).slotWitness b = some w)
    (hne : Witness.isNeutral w = true)
    (hr : cert.rank i b = some r)
    (hle : r ≤ ambient) :
    ∃ w' r', cert.selectNeutralLe i ambient = some (w', r') := by
  have htry :=
    cert.tryNeutralSlot_eq_some i b (fun r => decide (r ≤ ambient)) hw hne hr
      (decide_eq_true hle)
  cases b with
  | true =>
      refine ⟨w, r, ?_⟩
      simpa [ReachRankCert.selectNeutralLe, htry]
  | false =>
      cases hnew : cert.tryNeutralSlot i true (fun r => decide (r ≤ ambient)) with
      | some wr =>
          refine ⟨wr.1, wr.2, ?_⟩
          simp [ReachRankCert.selectNeutralLe, hnew]
      | none =>
          refine ⟨w, r, ?_⟩
          simpa [ReachRankCert.selectNeutralLe, hnew, htry]

theorem ReachRankCert.selectNeutralLe_of_rankOfNeutralSlot {n : Nat}
    {σ : ReachState n} (cert : ReachRankCert σ) (i ambient : Nat) {r : Nat}
    (hr : cert.rankOfNeutralSlot i = some r) (hle : r ≤ ambient) :
    ∃ w r', cert.selectNeutralLe i ambient = some (w, r') := by
  dsimp [ReachRankCert.rankOfNeutralSlot] at hr
  cases hnw : (σ.getCell i).neutralWitness with
  | none => simp [hnw] at hr
  | some w =>
      simp only [hnw] at hr
      have hne := ReachCell.neutralWitness_isNeutral hnw
      rcases ReachCell.neutralWitness_slot hnw with ⟨hnew, hw⟩ | ⟨hnew, hw⟩
      · simp only [hnew, ↓reduceIte] at hr
        exact cert.selectNeutralLe_isSome_of_ranked_neutral i ambient hw hne hr hle
      · simp only [hnew, Bool.false_eq_true, ↓reduceIte] at hr
        exact cert.selectNeutralLe_isSome_of_ranked_neutral i ambient hw hne hr hle

theorem CertifiedComplete.sized {Γ : ReachCtx sig.nBases} {goal : Object sig.nBases}
    (C : CertifiedComplete (sig := sig) Γ goal) :
    ReachState.Sized C.result.state := by
  rw [show C.result.state = runReachability Γ goal from C.soundFor]
  exact runReachability_sized Γ goal

theorem StoredNeutralDomain.typeAt_reconOk {Γ : ReachCtx sig.nBases}
    {goal : Object sig.nBases} (C : CertifiedComplete (sig := sig) Γ goal)
    {i : Nat} {b : SlotNew} {w : Witness}
    (hdom : StoredNeutralDomain C.result.cert i b w) :
    ∃ (A : Object sig.nBases),
      C.result.state.typeAt i = some A ∧
        WitnessReconShape C.result.state Γ.hyps A w := by
  obtain ⟨hw, hne, _hrs⟩ := hdom
  have hi := ReachState.lt_cells_of_slotWitness hw
  obtain ⟨A, hA⟩ := ReachState.typeAt_isSome_of_lt_sized C.sized hi
  have hwMem :
      (C.result.state.getCell i).oldWitness = some w ∨
        (C.result.state.getCell i).newWitness = some w := by
    cases b with
    | false => exact Or.inl (by simpa [ReachCell.slotWitness] using hw)
    | true => exact Or.inr (by simpa [ReachCell.slotWitness] using hw)
  exact ⟨A, hA, C.sound.reconOk i A w hA hwMem hne⟩

theorem mem_buildSchedule_storedNeutral {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) {P : Object n} {w : Witness}
    (h : (P, w) ∈ (buildSchedule σ).entries) :
    ∃ i, σ.typeAt i = some P ∧
      (σ.getCell i).slotWitness true = some w ∧
        Witness.isNeutral w = true ∧
          (cert.rank i true).isSome = true := by
  rw [buildSchedule, Array.mem_filterMap] at h
  obtain ⟨i, _, hi⟩ := h
  dsimp [scheduleEntryAt] at hi
  cases hty : σ.typeAt i with
  | none => simp [hty] at hi
  | some A =>
      simp only [hty] at hi
      split at hi
      · next hpol =>
          cases hw : (σ.getCell i).newWitness with
          | none => simp [hw] at hi
          | some w' =>
              simp only [hw] at hi
              split at hi
              · next hne =>
                  cases hi
                  refine ⟨i, hty, by simpa [ReachCell.slotWitness, hw], hne, ?_⟩
                  have hiff := cert.rank_iff i true
                  simpa [ReachCell.slotWitness, hw] using hiff.symm
              · cases hi
      · cases hi

/-! ## Status

* `InvertibleArgDomain` tightened (no polarity shortcut); hypApp/expApp inhabitation
  lemmas; boundary fixtures above.
* Leaf + recursive case lemmas for `.fstType` / `.sndType` / `.app` / `.appTy`
  (recursive premises: bounded selection + IH on lower measure).
* `ReachRankCert.neutralParent_lt` threads fire-time neutral parents; selectors
  obtain `NeutralParentLt` from that field (not a free hypothesis).
* Bridge lemmas: sized typeAt, `selectNeutralLe` from `rankOfNeutralSlot`,
  schedule → stored new-neutral, `StoredNeutralDomain` → `reconOk` shape.

Remaining for `ReconstructTotalityPackage`:
* measure induction wiring case lemmas + domain inheritance for `invOf`;
* specialize the five package conjuncts;
* fueled migration and reachability cleanup remain blocked until the package lands.
-/

end Equality
end Gimbal
