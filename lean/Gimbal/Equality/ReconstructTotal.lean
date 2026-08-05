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

/-! ## Nodup lookup: `typeAt` recovers `findTypeIdx` -/

theorem ReachState.findTypeIdx_of_typeAt {n : Nat} {σ : ReachState n}
    {A : Object n} {i : Nat}
    (hnodup : σ.types.toList.Nodup) (h : σ.typeAt i = some A) :
    σ.findTypeIdx A = some i := by
  have hi : i < σ.types.size := (Array.getElem?_eq_some_iff.mp h).1
  have hAi : σ.types[i] = A := (Array.getElem?_eq_some_iff.mp h).2
  have hbeq : (σ.types[i] == A) = true := by simp [hAi]
  refine Array.findIdx?_eq_some_iff_getElem.mpr ⟨hi, hbeq, ?_⟩
  intro j hj
  have hjsize : j < σ.types.size := Nat.lt_trans hj hi
  have hne : σ.types[j] ≠ A := by
    intro heq
    have hji : j = i := by
      have :=
        (List.getElem?_inj (l := σ.types.toList)
          (i := j) (j := i) (by simpa [Array.length_toList] using hjsize) hnodup).1
      refine this ?_
      simp [Array.getElem?_eq_getElem hjsize, Array.getElem?_eq_getElem hi,
        Array.getElem_toList, heq, hAi]
    exact absurd hji (Nat.ne_of_lt hj)
  simpa [beq_eq_false_iff_ne] using hne

theorem CertifiedComplete.types_nodup {Γ : ReachCtx sig.nBases}
    {goal : Object sig.nBases} (C : CertifiedComplete (sig := sig) Γ goal) :
    C.result.state.types.toList.Nodup := by
  have htypes : C.result.state.types = subformulaClosure (Γ.roots goal) := by
    rw [show C.result.state = runReachability Γ goal from C.soundFor]
    exact runReachability_types Γ goal
  rw [htypes, subformulaClosure]
  have hround :
      (subformulaClosureList (Γ.roots goal)).toArray.toList =
        subformulaClosureList (Γ.roots goal) :=
    (List.toArray_eq_iff).mp rfl
  rw [hround]
  exact subformulaClosureList_nodup (Γ.roots goal)

theorem WitnessReconShape.push {n : Nat} {σ : ReachState n}
    {hyps : Array (Object n)} {A B : Object n} {w : Witness}
    (h : WitnessReconShape σ hyps A w) :
    WitnessReconShape σ (hyps.push B) A w := by
  cases w with
  | ctxVar i =>
      change hyps[i]? = some A at h
      have hi : i < hyps.size := (Array.getElem?_eq_some_iff.mp h).1
      have hAi : hyps[i] = A := (Array.getElem?_eq_some_iff.mp h).2
      change (hyps.push B)[i]? = some A
      simp [Array.getElem?_push_lt (x := B) hi, hAi]
  | fstHyp i =>
      obtain ⟨L, R, hhyps, hA⟩ := h
      have hi : i < hyps.size := (Array.getElem?_eq_some_iff.mp hhyps).1
      have hty : hyps[i] = .prod L R := (Array.getElem?_eq_some_iff.mp hhyps).2
      exact ⟨L, R, by simp [Array.getElem?_push_lt (x := B) hi, hty], hA⟩
  | sndHyp i =>
      obtain ⟨L, R, hhyps, hA⟩ := h
      have hi : i < hyps.size := (Array.getElem?_eq_some_iff.mp hhyps).1
      have hty : hyps[i] = .prod L R := (Array.getElem?_eq_some_iff.mp hhyps).2
      exact ⟨L, R, by simp [Array.getElem?_push_lt (x := B) hi, hty], hA⟩
  | fstType p => exact h
  | sndType p => exact h
  | app fn arg =>
      obtain ⟨Arg, Ret, hfn, harg, hA⟩ := h
      have hi : fn < hyps.size := (Array.getElem?_eq_some_iff.mp hfn).1
      have hty : hyps[fn] = .exp Arg Ret := (Array.getElem?_eq_some_iff.mp hfn).2
      exact ⟨Arg, Ret, by simp [Array.getElem?_push_lt (x := B) hi, hty], harg, hA⟩
  | appTy fn arg => exact h
  | unit | inl _ | inr _ | eta => exact h

/-! ## Domain inheritance for `invOf` structural parents -/

theorem InvertibleArgDomain.of_eta_prod_components {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases))
    (hnodup : σ.types.toList.Nodup)
    {i : Nat} {b : SlotNew} {r : Nat} {L R : Object sig.nBases}
    (hw : (σ.getCell i).slotWitness b = some .eta)
    (hty : σ.typeAt i = some (.prod L R))
    (hr : cert.rank i b = some r) (hlt : r < ambientRank) :
    InvertibleArgDomain cert ambientRank hyps L ∧
      InvertibleArgDomain cert ambientRank hyps R := by
  obtain ⟨lIdx, rIdx, bL, rL, bR, rR, _, hL, hR, hrL, hltL, hrR, hltR⟩ :=
    cert.ranked_parents_of_eta_prod hw hty hr
  have hfL := σ.findTypeIdx_of_typeAt hnodup hL
  have hfR := σ.findTypeIdx_of_typeAt hnodup hR
  refine ⟨InvertibleArgDomain.of_ranked_lt cert ambientRank hyps L hfL hrL
      (Nat.lt_trans hltL hlt),
    InvertibleArgDomain.of_ranked_lt cert ambientRank hyps R hfR hrR
      (Nat.lt_trans hltR hlt)⟩

theorem InvertibleArgDomain.of_eta_exp_ret {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases))
    (hnodup : σ.types.toList.Nodup)
    {i : Nat} {b : SlotNew} {r : Nat} {Arg Ret : Object sig.nBases}
    (hw : (σ.getCell i).slotWitness b = some .eta)
    (hty : σ.typeAt i = some (.exp Arg Ret))
    (hr : cert.rank i b = some r) (hlt : r < ambientRank) :
    InvertibleArgDomain cert ambientRank hyps Ret := by
  obtain ⟨retIdx, bRet, rRet, _, hRet, hrRet, hltRet⟩ :=
    cert.ranked_parents_of_eta_exp hw hty hr
  exact InvertibleArgDomain.of_ranked_lt cert ambientRank hyps Ret
    (σ.findTypeIdx_of_typeAt hnodup hRet) hrRet (Nat.lt_trans hltRet hlt)

theorem InvertibleArgDomain.of_inl_payload {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases))
    (hnodup : σ.types.toList.Nodup)
    {i : Nat} {b : SlotNew} {r p : Nat} {L R : Object sig.nBases}
    (hw : (σ.getCell i).slotWitness b = some (.inl p))
    (hty : σ.typeAt i = some (.coprod L R))
    (hr : cert.rank i b = some r) (hlt : r < ambientRank) :
    InvertibleArgDomain cert ambientRank hyps L := by
  obtain ⟨bP, rP, _, hL, hrP, hltP⟩ := cert.ranked_parent_of_inl hw hty hr
  exact InvertibleArgDomain.of_ranked_lt cert ambientRank hyps L
    (σ.findTypeIdx_of_typeAt hnodup hL) hrP (Nat.lt_trans hltP hlt)

theorem InvertibleArgDomain.of_inr_payload {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases))
    (hnodup : σ.types.toList.Nodup)
    {i : Nat} {b : SlotNew} {r p : Nat} {L R : Object sig.nBases}
    (hw : (σ.getCell i).slotWitness b = some (.inr p))
    (hty : σ.typeAt i = some (.coprod L R))
    (hr : cert.rank i b = some r) (hlt : r < ambientRank) :
    InvertibleArgDomain cert ambientRank hyps R := by
  obtain ⟨bP, rP, _, hR, hrP, hltP⟩ := cert.ranked_parent_of_inr hw hty hr
  exact InvertibleArgDomain.of_ranked_lt cert ambientRank hyps R
    (σ.findTypeIdx_of_typeAt hnodup hR) hrP (Nat.lt_trans hltP hlt)

theorem InvertibleArgDomain.of_app_arg {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases))
    (hnodup : σ.types.toList.Nodup)
    {i : Nat} {b : SlotNew} {r fnHyp argIdx : Nat}
    {Arg Ret : Object sig.nBases}
    (hw : (σ.getCell i).slotWitness b = some (.app fnHyp argIdx))
    (harg : σ.typeAt argIdx = some Arg)
    (hr : cert.rank i b = some r) (hle : r ≤ ambientRank) :
    InvertibleArgDomain cert ambientRank hyps Arg := by
  have hdeps : cert.deps i b = RuleDeps.hypApp argIdx :=
    cert.deps_sound i b (.app fnHyp argIdx) hw
  have hmem : argIdx ∈ cert.deps i b := by simp [hdeps, RuleDeps.hypApp]
  obtain ⟨bP, rP, hrP, hlt⟩ := cert.parents_lt i b r hr argIdx hmem
  exact InvertibleArgDomain.of_ranked_lt cert ambientRank hyps Arg
    (σ.findTypeIdx_of_typeAt hnodup harg) hrP (Nat.lt_of_lt_of_le hlt hle)

theorem InvertibleArgDomain.of_appTy_arg {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases))
    (hnodup : σ.types.toList.Nodup)
    {i : Nat} {b : SlotNew} {r fnIdx argIdx : Nat}
    {Arg Ret : Object sig.nBases}
    (hw : (σ.getCell i).slotWitness b = some (.appTy fnIdx argIdx))
    (harg : σ.typeAt argIdx = some Arg)
    (hr : cert.rank i b = some r) (hle : r ≤ ambientRank) :
    InvertibleArgDomain cert ambientRank hyps Arg := by
  have hdeps : cert.deps i b = RuleDeps.typeApp fnIdx argIdx :=
    cert.deps_sound i b (.appTy fnIdx argIdx) hw
  have hmem : argIdx ∈ cert.deps i b := by simp [hdeps, RuleDeps.typeApp]
  obtain ⟨bP, rP, hrP, hlt⟩ := cert.parents_lt i b r hr argIdx hmem
  exact InvertibleArgDomain.of_ranked_lt cert ambientRank hyps Arg
    (σ.findTypeIdx_of_typeAt hnodup harg) hrP (Nat.lt_of_lt_of_le hlt hle)

/-! ## Master measure induction

Under domain hypotheses on a `CertifiedComplete` state, `reconstructGoWF`
succeeds. Lex measure: `(ambientRank, phase.toNat, objSize)`.
-/

/-- `hyps` is `Γ.hyps` with zero or more arguments pushed (for nested `exp` η). -/
def HypsExt (Γ : ReachCtx sig.nBases) (hyps : Array (Object sig.nBases)) : Prop :=
  ∃ extra : List (Object sig.nBases), hyps = extra.foldl Array.push Γ.hyps

theorem HypsExt.refl (Γ : ReachCtx sig.nBases) : HypsExt (sig := sig) Γ Γ.hyps :=
  ⟨[], rfl⟩

theorem HypsExt.push {Γ : ReachCtx sig.nBases} {hyps : Array (Object sig.nBases)}
    (h : HypsExt (sig := sig) Γ hyps) (A : Object sig.nBases) :
    HypsExt (sig := sig) Γ (hyps.push A) := by
  obtain ⟨extra, rfl⟩ := h
  exact ⟨extra ++ [A], by simp [List.foldl_append]⟩

theorem WitnessReconShape.of_foldl_push {n : Nat} {σ : ReachState n}
    {hyps : Array (Object n)} {A : Object n} {w : Witness}
    (h : WitnessReconShape σ hyps A w) (extra : List (Object n)) :
    WitnessReconShape σ (extra.foldl Array.push hyps) A w := by
  induction extra generalizing hyps with
  | nil => exact h
  | cons B rest ih => exact ih (WitnessReconShape.push h)

theorem WitnessReconShape.of_hypsExt {Γ : ReachCtx sig.nBases}
    {σ : ReachState sig.nBases} {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {w : Witness}
    (hext : HypsExt (sig := sig) Γ hyps)
    (h : WitnessReconShape σ Γ.hyps A w) :
    WitnessReconShape σ hyps A w := by
  obtain ⟨extra, rfl⟩ := hext
  exact WitnessReconShape.of_foldl_push h extra

/-- Extract the ranked neutral slot chosen by `selectNeutralLe`. -/
theorem ReachRankCert.selectNeutralLe_slot {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) {i ambient : Nat} {w : Witness} {r : Nat}
    (h : cert.selectNeutralLe i ambient = some (w, r)) :
    ∃ b : SlotNew,
      (σ.getCell i).slotWitness b = some w ∧
        Witness.isNeutral w = true ∧
          cert.rank i b = some r := by
  dsimp [ReachRankCert.selectNeutralLe] at h
  cases h1 : cert.tryNeutralSlot i true (fun r => decide (r ≤ ambient)) with
  | some wr =>
      simp only [h1] at h
      have hwr : wr = (w, r) := Option.some.inj h
      subst hwr
      dsimp [ReachRankCert.tryNeutralSlot] at h1
      cases hw : (σ.getCell i).slotWitness true with
      | none => simp [hw] at h1
      | some w' =>
          simp only [hw] at h1
          split at h1
          · split at h1
            · next r' hr' =>
                split at h1
                · cases h1; exact ⟨true, hw, ‹_›, hr'⟩
                · cases h1
            · cases h1
          · cases h1
  | none =>
      simp only [h1] at h
      dsimp [ReachRankCert.tryNeutralSlot] at h
      cases hw : (σ.getCell i).slotWitness false with
      | none => simp [hw] at h
      | some w' =>
          simp only [hw] at h
          split at h
          · split at h
            · next r' hr' =>
                split at h
                · cases h; exact ⟨false, hw, ‹_›, hr'⟩
                · cases h
            · cases h
          · cases h

/-- Extract the ranked neutral slot chosen by `selectNeutralLt`. -/
theorem ReachRankCert.selectNeutralLt_slot {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) {i ambient : Nat} {w : Witness} {r : Nat}
    (h : cert.selectNeutralLt i ambient = some (w, r)) :
    ∃ b : SlotNew,
      (σ.getCell i).slotWitness b = some w ∧
        Witness.isNeutral w = true ∧
          cert.rank i b = some r := by
  dsimp [ReachRankCert.selectNeutralLt] at h
  cases h1 : cert.tryNeutralSlot i true (fun r => decide (r < ambient)) with
  | some wr =>
      simp only [h1] at h
      have hwr : wr = (w, r) := Option.some.inj h
      subst hwr
      dsimp [ReachRankCert.tryNeutralSlot] at h1
      cases hw : (σ.getCell i).slotWitness true with
      | none => simp [hw] at h1
      | some w' =>
          simp only [hw] at h1
          split at h1
          · split at h1
            · next r' hr' =>
                split at h1
                · cases h1; exact ⟨true, hw, ‹_›, hr'⟩
                · cases h1
            · cases h1
          · cases h1
  | none =>
      simp only [h1] at h
      dsimp [ReachRankCert.tryNeutralSlot] at h
      cases hw : (σ.getCell i).slotWitness false with
      | none => simp [hw] at h
      | some w' =>
          simp only [hw] at h
          split at h
          · split at h
            · next r' hr' =>
                split at h
                · cases h; exact ⟨false, hw, ‹_›, hr'⟩
                · cases h
            · cases h
          · cases h

theorem ReachCell.slotWitness_mem {c : ReachCell} {b : SlotNew} {w : Witness}
    (h : c.slotWitness b = some w) :
    c.oldWitness = some w ∨ c.newWitness = some w := by
  cases b with
  | false => exact Or.inl (by simpa [ReachCell.slotWitness] using h)
  | true => exact Or.inr (by simpa [ReachCell.slotWitness] using h)


/-! ## Closing lemmas for structural `invOf` -/

/-- `selectNeutralLt = none` erases the named-match tryNeu branch (via `congrArg`). -/
theorem selectNeutralLt_tryNeu_eq_none {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ)
    (i ambient : Nat) (A : Object sig.nBases)
    (hyps : Array (Object sig.nBases))
    (hsel : cert.selectNeutralLt i ambient = none) :
    (match hsel : cert.selectNeutralLt i ambient with
      | none => none
      | some (w, rNeu) =>
        match reconstructGoWF (sig := sig) cert rNeu
            (ReconstructCmd.witness hyps w) with
        | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
          if hH : hyps' = hyps then
            if hA : B = A then
              let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
              match objectPolarity A with
              | Polarity.pos =>
                some (ReconstructVal.inv hyps A
                  (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n')))))
              | Polarity.neg =>
                some (ReconstructVal.inv hyps A
                  (InvTm.foc (FocTm.neg (NegElim.done n'))))
            else none
          else none
        | _ => none) = (none : Option (ReconstructVal sig)) :=
  Eq.trans (congrArg
    (fun o =>
      match hsel : o with
      | none => none
      | some (w, rNeu) =>
        match reconstructGoWF (sig := sig) cert rNeu
            (ReconstructCmd.witness hyps w) with
        | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
          if hH : hyps' = hyps then
            if hA : B = A then
              let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
              match objectPolarity A with
              | Polarity.pos =>
                some (ReconstructVal.inv hyps A
                  (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n')))))
              | Polarity.neg =>
                some (ReconstructVal.inv hyps A
                  (InvTm.foc (FocTm.neg (NegElim.done n'))))
            else none
          else none
        | _ => none)
    hsel) rfl

theorem reconstructGoWF_invOf_eta_prod {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases) (i : Nat)
    (tL : InvTm (Ctx.ofHyps hyps) L) (tR : InvTm (Ctx.ofHyps hyps) R)
    (hhyp : findHypVar (sig := sig) hyps (.prod L R) = none)
    (hfind : σ.findTypeIdx (.prod L R) = some i)
    (hsel : cert.selectNeutralLt i a = none)
    (htL : reconstructGoWF (sig := sig) cert a (.invOf hyps L) =
      some (ReconstructVal.inv hyps L tL))
    (htR : reconstructGoWF (sig := sig) cert a (.invOf hyps R) =
      some (ReconstructVal.inv hyps R tR)) :
    reconstructGoWF (sig := sig) cert a (.invOf hyps (.prod L R)) =
      some (ReconstructVal.inv hyps (.prod L R) (.pair tL tR)) := by
  rw [reconstructGoWF.eq_14, hhyp]
  simp only [hfind]
  refine Eq.trans (congrArg
      (fun t : Option (ReconstructVal sig) =>
        match t with
        | some v => some v
        | none =>
          match reconstructGoWF (sig := sig) cert a (.invOf hyps L),
                reconstructGoWF (sig := sig) cert a (.invOf hyps R) with
          | some (ReconstructVal.inv hyps₁ A₁ t),
            some (ReconstructVal.inv hyps₂ A₂ u) =>
            if h1 : hyps₁ = hyps then
              if h2 : hyps₂ = hyps then
                if hL : A₁ = L then
                  if hR : A₂ = R then
                    some (ReconstructVal.inv hyps (.prod L R)
                      ((InvTm.castTy hL (InvTm.castHyps h1 t)).pair
                        (InvTm.castTy hR (InvTm.castHyps h2 u))))
                  else none
                else none
              else none
            else none
          | _, _ => none)
      (selectNeutralLt_tryNeu_eq_none (A := .prod L R) cert i a hyps hsel)) ?_
  simp [htL, htR, InvTm.castHyps, InvTm.castTy, InvTm.castCtx]


/-! ## `invOf` tryNeu-some closes -/

theorem reconstructGoWF_invOf_tryNeu_prod {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases) (i : Nat)
    (w : Witness) (rNeu : Nat) (n : NegNeu (Ctx.ofHyps hyps) (.prod L R))
    (hhyp : findHypVar (sig := sig) hyps (.prod L R) = none)
    (hfind : σ.findTypeIdx (.prod L R) = some i)
    (hsel : cert.selectNeutralLt i a = some (w, rNeu))
    (hn : reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) =
      some (.wit hyps ⟨.prod L R, n⟩)) :
    reconstructGoWF (sig := sig) cert a (.invOf hyps (.prod L R)) =
      some (.inv hyps (.prod L R) (.foc (.neg (.done n)))) := by
  rw [reconstructGoWF.eq_14, hhyp]
  simp only [hfind]
  have hin :
      (match hsel : cert.selectNeutralLt i a with
        | none => none
        | some (w, rNeu) =>
          match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
          | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
            if hH : hyps' = hyps then
              if hA : B = L.prod R then
                let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
                match objectPolarity (L.prod R) with
                | Polarity.pos =>
                  some (ReconstructVal.inv hyps (L.prod R)
                    (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n')))))
                | Polarity.neg =>
                  some (ReconstructVal.inv hyps (L.prod R)
                    (InvTm.foc (FocTm.neg (NegElim.done n'))))
              else none
            else none
          | _ => none) =
        some (ReconstructVal.inv hyps (L.prod R)
          (InvTm.foc (FocTm.neg (NegElim.done n)))) := by
    refine Eq.trans (congrArg
      (fun o =>
        match hsel : o with
        | none => none
        | some (w, rNeu) =>
          match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
          | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
            if hH : hyps' = hyps then
              if hA : B = L.prod R then
                let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
                match objectPolarity (L.prod R) with
                | Polarity.pos =>
                  some (ReconstructVal.inv hyps (L.prod R)
                    (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n')))))
                | Polarity.neg =>
                  some (ReconstructVal.inv hyps (L.prod R)
                    (InvTm.foc (FocTm.neg (NegElim.done n'))))
              else none
            else none
          | _ => none)
      hsel) ?_
    simp [hn, NegNeu.castHyps, NegNeu.cast, NegNeu.castCtx]
  refine Eq.trans (congrArg
      (fun t : Option (ReconstructVal sig) =>
        match t with
        | some v => some v
        | none =>
          match reconstructGoWF (sig := sig) cert a (.invOf hyps L),
                reconstructGoWF (sig := sig) cert a (.invOf hyps R) with
          | some (ReconstructVal.inv hyps₁ A₁ t),
            some (ReconstructVal.inv hyps₂ A₂ u) =>
            if h1 : hyps₁ = hyps then
              if h2 : hyps₂ = hyps then
                if hL : A₁ = L then
                  if hR : A₂ = R then
                    some (ReconstructVal.inv hyps (L.prod R)
                      ((InvTm.castTy hL (InvTm.castHyps h1 t)).pair
                        (InvTm.castTy hR (InvTm.castHyps h2 u))))
                  else none
                else none
              else none
            else none
          | _, _ => none)
      hin) rfl

theorem reconstructGoWF_invOf_tryNeu_exp {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (Arg Ret : Object sig.nBases) (i : Nat)
    (w : Witness) (rNeu : Nat) (n : NegNeu (Ctx.ofHyps hyps) (.exp Arg Ret))
    (hhyp : findHypVar (sig := sig) hyps (.exp Arg Ret) = none)
    (hfind : σ.findTypeIdx (.exp Arg Ret) = some i)
    (hsel : cert.selectNeutralLt i a = some (w, rNeu))
    (hn : reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) =
      some (.wit hyps ⟨.exp Arg Ret, n⟩)) :
    reconstructGoWF (sig := sig) cert a (.invOf hyps (.exp Arg Ret)) =
      some (.inv hyps (.exp Arg Ret) (.foc (.neg (.done n)))) := by
  rw [reconstructGoWF.eq_16, hhyp]
  simp only [hfind]
  have hin :
      (match hsel : cert.selectNeutralLt i a with
        | none => none
        | some (w, rNeu) =>
          match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
          | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
            if hH : hyps' = hyps then
              if hA : B = Arg.exp Ret then
                let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
                match objectPolarity (Arg.exp Ret) with
                | Polarity.pos =>
                  some (ReconstructVal.inv hyps (Arg.exp Ret)
                    (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n')))))
                | Polarity.neg =>
                  some (ReconstructVal.inv hyps (Arg.exp Ret)
                    (InvTm.foc (FocTm.neg (NegElim.done n'))))
              else none
            else none
          | _ => none) =
        some (ReconstructVal.inv hyps (Arg.exp Ret)
          (InvTm.foc (FocTm.neg (NegElim.done n)))) := by
    refine Eq.trans (congrArg
      (fun o =>
        match hsel : o with
        | none => none
        | some (w, rNeu) =>
          match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
          | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
            if hH : hyps' = hyps then
              if hA : B = Arg.exp Ret then
                let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
                match objectPolarity (Arg.exp Ret) with
                | Polarity.pos =>
                  some (ReconstructVal.inv hyps (Arg.exp Ret)
                    (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n')))))
                | Polarity.neg =>
                  some (ReconstructVal.inv hyps (Arg.exp Ret)
                    (InvTm.foc (FocTm.neg (NegElim.done n'))))
              else none
            else none
          | _ => none)
      hsel) ?_
    simp [hn, NegNeu.castHyps, NegNeu.cast, NegNeu.castCtx]
  refine Eq.trans (congrArg
      (fun t : Option (ReconstructVal sig) =>
        match t with
        | some v => some v
        | none =>
          let hyps' := hyps.push Arg
          have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ Arg :=
            Ctx.ofHyps_push hyps Arg
          match reconstructGoWF (sig := sig) cert a (.invOf hyps' Ret) with
          | some (ReconstructVal.inv hyps'' B t) =>
            if hH : hyps'' = hyps' then
              if hB : B = Ret then
                some (ReconstructVal.inv hyps (Arg.exp Ret)
                  (.lam (InvTm.castCtx hctx
                    (InvTm.castTy hB (InvTm.castHyps hH t)))))
              else none
            else none
          | _ => none)
      hin) rfl

theorem reconstructGoWF_invOf_tryNeu_unit {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (i : Nat)
    (w : Witness) (rNeu : Nat) (n : NegNeu (Ctx.ofHyps hyps) .unit)
    (hhyp : findHypVar (sig := sig) hyps .unit = none)
    (hfind : σ.findTypeIdx (.unit : Object sig.nBases) = some i)
    (hsel : cert.selectNeutralLt i a = some (w, rNeu))
    (hn : reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) =
      some (.wit hyps ⟨.unit, n⟩)) :
    reconstructGoWF (sig := sig) cert a (.invOf hyps .unit) =
      some (.inv hyps .unit (.foc (.neg (.done n)))) := by
  rw [reconstructGoWF.eq_13, hhyp]
  simp only [hfind]
  have hin :
      (match hsel : cert.selectNeutralLt i a with
        | none => none
        | some (w, rNeu) =>
          match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
          | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
            if hH : hyps' = hyps then
              if hA : B = Object.unit then
                let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
                match objectPolarity (Object.unit : Object sig.nBases) with
                | Polarity.pos =>
                  some (ReconstructVal.inv hyps .unit
                    (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n')))))
                | Polarity.neg =>
                  some (ReconstructVal.inv hyps .unit
                    (InvTm.foc (FocTm.neg (NegElim.done n'))))
              else none
            else none
          | _ => none) =
        some (ReconstructVal.inv hyps .unit
          (InvTm.foc (FocTm.neg (NegElim.done n)))) := by
    refine Eq.trans (congrArg
      (fun o =>
        match hsel : o with
        | none => none
        | some (w, rNeu) =>
          match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
          | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
            if hH : hyps' = hyps then
              if hA : B = Object.unit then
                let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
                match objectPolarity (Object.unit : Object sig.nBases) with
                | Polarity.pos =>
                  some (ReconstructVal.inv hyps .unit
                    (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n')))))
                | Polarity.neg =>
                  some (ReconstructVal.inv hyps .unit
                    (InvTm.foc (FocTm.neg (NegElim.done n'))))
              else none
            else none
          | _ => none)
      hsel) ?_
    simp [hn, NegNeu.castHyps, NegNeu.cast, NegNeu.castCtx]
  exact Eq.trans (congrArg
      (fun t : Option (ReconstructVal sig) =>
        match t with
        | some v => some v
        | none => some (ReconstructVal.inv hyps .unit InvTm.unit))
      hin) rfl

theorem reconstructGoWF_invOf_unit_structural {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases))
    (hhyp : findHypVar (sig := sig) hyps .unit = none)
    (htry : (match σ.findTypeIdx (.unit : Object sig.nBases) with
        | none => none
        | some i =>
          match hsel : cert.selectNeutralLt i a with
          | none => none
          | some (w, rNeu) =>
            match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
            | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
              if hH : hyps' = hyps then
                if hA : B = Object.unit then
                  let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
                  match objectPolarity (Object.unit : Object sig.nBases) with
                  | Polarity.pos =>
                    some (ReconstructVal.inv hyps .unit
                      (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n')))))
                  | Polarity.neg =>
                    some (ReconstructVal.inv hyps .unit
                      (InvTm.foc (FocTm.neg (NegElim.done n'))))
                else none
              else none
            | _ => none) =
        (none : Option (ReconstructVal sig))) :
    reconstructGoWF (sig := sig) cert a (.invOf hyps .unit) =
      some (.inv hyps .unit .unit) := by
  rw [reconstructGoWF.eq_13, hhyp]
  exact Eq.trans (congrArg
      (fun t : Option (ReconstructVal sig) =>
        match t with
        | some v => some v
        | none => some (ReconstructVal.inv hyps .unit InvTm.unit))
      htry) rfl


theorem reconstructGoWF_invOf_tryNeu_base (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (q : Fin sig.nBases) (i : Nat)
    (w : Witness) (rNeu : Nat) (n : NegNeu (Ctx.ofHyps hyps) (.base q))
    (hhyp : findHypVar (sig := sig) hyps (.base q) = none)
    (hfind : σ.findTypeIdx (.base q) = some i)
    (hsel : cert.selectNeutralLt i a = some (w, rNeu))
    (hn : reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) =
      some (.wit hyps ⟨.base q, n⟩)) :
    reconstructGoWF (sig := sig) cert a (.invOf hyps (.base q)) =
      some (.inv hyps (.base q) (.foc (.pos (.done (.neu n))))) := by
  rw [reconstructGoWF.eq_17 cert a hyps (.base q)
      (fun h => by cases h)
      (fun _ _ h => by cases h)
      (fun _ _ h => by cases h)
      (fun _ _ h => by cases h),
    hhyp]
  simp only [hfind]
  have hin :
      (match hsel : cert.selectNeutralLt i a with
        | none => none
        | some (w, rNeu) =>
          match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
          | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
            if hH : hyps' = hyps then
              if hA : B = Object.base q then
                let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
                match objectPolarity (Object.base q) with
                | Polarity.pos =>
                  some (ReconstructVal.inv hyps (.base q)
                    (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n')))))
                | Polarity.neg =>
                  some (ReconstructVal.inv hyps (.base q)
                    (InvTm.foc (FocTm.neg (NegElim.done n'))))
              else none
            else none
          | _ => none) =
        some (ReconstructVal.inv hyps (.base q)
          (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n))))) := by
    refine Eq.trans (congrArg
      (fun o =>
        match hsel : o with
        | none => none
        | some (w, rNeu) =>
          match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
          | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
            if hH : hyps' = hyps then
              if hA : B = Object.base q then
                let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
                match objectPolarity (Object.base q) with
                | Polarity.pos =>
                  some (ReconstructVal.inv hyps (.base q)
                    (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n')))))
                | Polarity.neg =>
                  some (ReconstructVal.inv hyps (.base q)
                    (InvTm.foc (FocTm.neg (NegElim.done n'))))
              else none
            else none
          | _ => none)
      hsel) ?_
    simp [hn, NegNeu.castHyps, NegNeu.cast, NegNeu.castCtx]
  exact Eq.trans (congrArg
      (fun t : Option (ReconstructVal sig) =>
        match t with
        | some v => some v
        | none => none)
      hin) rfl


theorem reconstructGoWF_invOf_tryNeu_never {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (i : Nat)
    (w : Witness) (rNeu : Nat) (n : NegNeu (Ctx.ofHyps hyps) .never)
    (hhyp : findHypVar (sig := sig) hyps .never = none)
    (hfind : σ.findTypeIdx (.never : Object sig.nBases) = some i)
    (hsel : cert.selectNeutralLt i a = some (w, rNeu))
    (hn : reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) =
      some (.wit hyps ⟨.never, n⟩)) :
    reconstructGoWF (sig := sig) cert a (.invOf hyps .never) =
      some (.inv hyps .never (.foc (.pos (.done (.neu n))))) := by
  rw [reconstructGoWF.eq_17 cert a hyps (.never)
      (fun h => by cases h)
      (fun _ _ h => by cases h)
      (fun _ _ h => by cases h)
      (fun _ _ h => by cases h),
    hhyp]
  simp only [hfind]
  have hin :
      (match hsel : cert.selectNeutralLt i a with
        | none => none
        | some (w, rNeu) =>
          match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
          | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
            if hH : hyps' = hyps then
              if hA : B = Object.never then
                let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
                match objectPolarity (Object.never : Object sig.nBases) with
                | Polarity.pos =>
                  some (ReconstructVal.inv hyps .never
                    (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n')))))
                | Polarity.neg =>
                  some (ReconstructVal.inv hyps .never
                    (InvTm.foc (FocTm.neg (NegElim.done n'))))
              else none
            else none
          | _ => none) =
        some (ReconstructVal.inv hyps .never
          (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n))))) := by
    refine Eq.trans (congrArg
      (fun o =>
        match hsel : o with
        | none => none
        | some (w, rNeu) =>
          match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
          | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
            if hH : hyps' = hyps then
              if hA : B = Object.never then
                let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
                match objectPolarity (Object.never : Object sig.nBases) with
                | Polarity.pos =>
                  some (ReconstructVal.inv hyps .never
                    (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.neu n')))))
                | Polarity.neg =>
                  some (ReconstructVal.inv hyps .never
                    (InvTm.foc (FocTm.neg (NegElim.done n'))))
              else none
            else none
          | _ => none)
      hsel) ?_
    simp [hn, NegNeu.castHyps, NegNeu.cast, NegNeu.castCtx]
  exact Eq.trans (congrArg
      (fun t : Option (ReconstructVal sig) =>
        match t with
        | some v => some v
        | none => none)
      hin) rfl

theorem reconstructGoWF_invOf_eta_exp {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (Arg Ret : Object sig.nBases) (i : Nat)
    (t : InvTm (Ctx.ofHyps (hyps.push Arg)) Ret)
    (hhyp : findHypVar (sig := sig) hyps (.exp Arg Ret) = none)
    (hfind : σ.findTypeIdx (.exp Arg Ret) = some i)
    (hsel : cert.selectNeutralLt i a = none)
    (ht : reconstructGoWF (sig := sig) cert a (.invOf (hyps.push Arg) Ret) =
      some (.inv (hyps.push Arg) Ret t)) :
    reconstructGoWF (sig := sig) cert a (.invOf hyps (.exp Arg Ret)) =
      some (.inv hyps (.exp Arg Ret)
        (.lam (InvTm.castCtx (Ctx.ofHyps_push hyps Arg) t))) := by
  rw [reconstructGoWF.eq_16, hhyp]
  simp only [hfind]
  refine Eq.trans (congrArg
      (fun t : Option (ReconstructVal sig) =>
        match t with
        | some v => some v
        | none =>
          let hyps' := hyps.push Arg
          have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ Arg :=
            Ctx.ofHyps_push hyps Arg
          match reconstructGoWF (sig := sig) cert a (.invOf hyps' Ret) with
          | some (ReconstructVal.inv hyps'' B t) =>
            if hH : hyps'' = hyps' then
              if hB : B = Ret then
                some (ReconstructVal.inv hyps (Arg.exp Ret)
                  (.lam (InvTm.castCtx hctx
                    (InvTm.castTy hB (InvTm.castHyps hH t)))))
              else none
            else none
          | _ => none)
      (selectNeutralLt_tryNeu_eq_none (A := .exp Arg Ret) cert i a hyps hsel)) ?_
  simp [ht, InvTm.castHyps, InvTm.castTy, InvTm.castCtx]

theorem reconstructGoWF_invOf_tryNeu_coprod {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases) (i : Nat)
    (w : Witness) (rNeu : Nat) (n : NegNeu (Ctx.ofHyps hyps) (.coprod L R))
    (hhyp : findHypVar (sig := sig) hyps (.coprod L R) = none)
    (hfind : σ.findTypeIdx (.coprod L R) = some i)
    (hsel : cert.selectNeutralLt i a = some (w, rNeu))
    (hn : reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) =
      some (.wit hyps ⟨.coprod L R, n⟩)) :
    reconstructGoWF (sig := sig) cert a (.invOf hyps (.coprod L R)) =
      some (.inv hyps (.coprod L R) (.foc (.pos (.done (.neu n))))) := by
  rw [reconstructGoWF.eq_15, hhyp]
  simp only [hfind]
  set desired : ReconstructVal sig :=
    .inv hyps (.coprod L R) (.foc (.pos (.done (.neu n))))
  have hin :
      (match hsel : cert.selectNeutralLt i a with
        | none => (none : Option (ReconstructVal sig))
        | some (w, rNeu) =>
          match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
          | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
            if h : hyps' = hyps then
              if h_1 : B = L.coprod R then
                match objectPolarity (L.coprod R) with
                | Polarity.pos =>
                  some (ReconstructVal.inv hyps (L.coprod R)
                    (InvTm.foc (FocTm.pos (PosIntro.done
                      (PosNeu.neu (NegNeu.cast h_1 (NegNeu.castHyps h n)))))))
                | Polarity.neg =>
                  some (ReconstructVal.inv hyps (L.coprod R)
                    (InvTm.foc (FocTm.neg (NegElim.done
                      (NegNeu.cast h_1 (NegNeu.castHyps h n))))))
              else none
            else none
          | _ => none) =
        some desired := by
    refine Eq.trans (congrArg
      (fun o =>
        match hsel : o with
        | none => none
        | some (w, rNeu) =>
          match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
          | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
            if h : hyps' = hyps then
              if h_1 : B = L.coprod R then
                match objectPolarity (L.coprod R) with
                | Polarity.pos =>
                  some (ReconstructVal.inv hyps (L.coprod R)
                    (InvTm.foc (FocTm.pos (PosIntro.done
                      (PosNeu.neu (NegNeu.cast h_1 (NegNeu.castHyps h n)))))))
                | Polarity.neg =>
                  some (ReconstructVal.inv hyps (L.coprod R)
                    (InvTm.foc (FocTm.neg (NegElim.done
                      (NegNeu.cast h_1 (NegNeu.castHyps h n))))))
              else none
            else none
          | _ => none)
      hsel) ?_
    simp [desired, hn, NegNeu.castHyps, NegNeu.cast, NegNeu.castCtx]
  have houter :
      ∀ (structural : Option (ReconstructVal sig)),
        (match
            (match hsel : cert.selectNeutralLt i a with
              | none => (none : Option (ReconstructVal sig))
              | some (w, rNeu) =>
                match reconstructGoWF (sig := sig) cert rNeu (.witness hyps w) with
                | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
                  if h : hyps' = hyps then
                    if h_1 : B = L.coprod R then
                      match objectPolarity (L.coprod R) with
                      | Polarity.pos =>
                        some (ReconstructVal.inv hyps (L.coprod R)
                          (InvTm.foc (FocTm.pos (PosIntro.done
                            (PosNeu.neu (NegNeu.cast h_1 (NegNeu.castHyps h n)))))))
                      | Polarity.neg =>
                        some (ReconstructVal.inv hyps (L.coprod R)
                          (InvTm.foc (FocTm.neg (NegElim.done
                            (NegNeu.cast h_1 (NegNeu.castHyps h n))))))
                    else none
                  else none
                | _ => none) with
          | some v => some v
          | none => structural) =
          some desired := by
    intro structural
    rw [hin]
  exact houter _


/-! ## `invOf` structural coprod closes -/

private theorem reconstructGoWF_invOf_coprod_reduce {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases) (i : Nat)
    (hhyp : findHypVar (sig := sig) hyps (.coprod L R) = none)
    (hfind : σ.findTypeIdx (.coprod L R) = some i)
    (hsel : cert.selectNeutralLt i a = none) :
    reconstructGoWF (sig := sig) cert a (.invOf hyps (.coprod L R)) =
      (if
          (match (σ.getCell i).witness with
            | some (Witness.inr _) => true
            | _ => false) =
            true then
        match
          match reconstructGoWF (sig := sig) cert a (.invOf hyps R) with
          | some (ReconstructVal.inv hyps' A' tR) =>
            if h : hyps' = hyps then
              if h_1 : A' = R then
                if (objectPolarity R == Polarity.neg) = true then
                  some (ReconstructVal.inv hyps (L.coprod R)
                    (InvTm.foc (FocTm.pos (PosIntro.done
                      (PosNeu.inr (PosNeu.val
                        (InvTm.castTy h_1 (InvTm.castHyps h tR))))))))
                else
                  match InvTm.castTy h_1 (InvTm.castHyps h tR) with
                  | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                    some (ReconstructVal.inv hyps (L.coprod R)
                      (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inr p)))))
                  | _ => none
              else none
            else none
          | _ => none with
        | some v => some v
        | none =>
          match reconstructGoWF (sig := sig) cert a (.invOf hyps L) with
          | some (ReconstructVal.inv hyps' A' tL) =>
            if h : hyps' = hyps then
              if h_1 : A' = L then
                if (objectPolarity L == Polarity.neg) = true then
                  some (ReconstructVal.inv hyps (L.coprod R)
                    (InvTm.foc (FocTm.pos (PosIntro.done
                      (PosNeu.inl (PosNeu.val
                        (InvTm.castTy h_1 (InvTm.castHyps h tL))))))))
                else
                  match InvTm.castTy h_1 (InvTm.castHyps h tL) with
                  | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                    some (ReconstructVal.inv hyps (L.coprod R)
                      (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inl p)))))
                  | _ => none
              else none
            else none
          | _ => none
      else
        match
          match reconstructGoWF (sig := sig) cert a (.invOf hyps L) with
          | some (ReconstructVal.inv hyps' A' tL) =>
            if h : hyps' = hyps then
              if h_1 : A' = L then
                if (objectPolarity L == Polarity.neg) = true then
                  some (ReconstructVal.inv hyps (L.coprod R)
                    (InvTm.foc (FocTm.pos (PosIntro.done
                      (PosNeu.inl (PosNeu.val
                        (InvTm.castTy h_1 (InvTm.castHyps h tL))))))))
                else
                  match InvTm.castTy h_1 (InvTm.castHyps h tL) with
                  | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                    some (ReconstructVal.inv hyps (L.coprod R)
                      (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inl p)))))
                  | _ => none
              else none
            else none
          | _ => none with
        | some v => some v
        | none =>
          match reconstructGoWF (sig := sig) cert a (.invOf hyps R) with
          | some (ReconstructVal.inv hyps' A' tR) =>
            if h : hyps' = hyps then
              if h_1 : A' = R then
                if (objectPolarity R == Polarity.neg) = true then
                  some (ReconstructVal.inv hyps (L.coprod R)
                    (InvTm.foc (FocTm.pos (PosIntro.done
                      (PosNeu.inr (PosNeu.val
                        (InvTm.castTy h_1 (InvTm.castHyps h tR))))))))
                else
                  match InvTm.castTy h_1 (InvTm.castHyps h tR) with
                  | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                    some (ReconstructVal.inv hyps (L.coprod R)
                      (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inr p)))))
                  | _ => none
              else none
            else none
          | _ => none) := by
  rw [reconstructGoWF.eq_15, hhyp]
  simp only [hfind]
  exact Eq.trans (congrArg
    (fun t : Option (ReconstructVal sig) =>
      match t with
      | some v => some v
      | none =>
        if
            (match (σ.getCell i).witness with
              | some (Witness.inr _) => true
              | _ => false) =
              true then
          match
            match reconstructGoWF (sig := sig) cert a (.invOf hyps R) with
            | some (ReconstructVal.inv hyps' A' tR) =>
              if h : hyps' = hyps then
                if h_1 : A' = R then
                  if (objectPolarity R == Polarity.neg) = true then
                    some (ReconstructVal.inv hyps (L.coprod R)
                      (InvTm.foc (FocTm.pos (PosIntro.done
                        (PosNeu.inr (PosNeu.val
                          (InvTm.castTy h_1 (InvTm.castHyps h tR))))))))
                  else
                    match InvTm.castTy h_1 (InvTm.castHyps h tR) with
                    | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                      some (ReconstructVal.inv hyps (L.coprod R)
                        (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inr p)))))
                    | _ => none
                else none
              else none
            | _ => none with
          | some v => some v
          | none =>
            match reconstructGoWF (sig := sig) cert a (.invOf hyps L) with
            | some (ReconstructVal.inv hyps' A' tL) =>
              if h : hyps' = hyps then
                if h_1 : A' = L then
                  if (objectPolarity L == Polarity.neg) = true then
                    some (ReconstructVal.inv hyps (L.coprod R)
                      (InvTm.foc (FocTm.pos (PosIntro.done
                        (PosNeu.inl (PosNeu.val
                          (InvTm.castTy h_1 (InvTm.castHyps h tL))))))))
                  else
                    match InvTm.castTy h_1 (InvTm.castHyps h tL) with
                    | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                      some (ReconstructVal.inv hyps (L.coprod R)
                        (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inl p)))))
                    | _ => none
                else none
              else none
            | _ => none
        else
          match
            match reconstructGoWF (sig := sig) cert a (.invOf hyps L) with
            | some (ReconstructVal.inv hyps' A' tL) =>
              if h : hyps' = hyps then
                if h_1 : A' = L then
                  if (objectPolarity L == Polarity.neg) = true then
                    some (ReconstructVal.inv hyps (L.coprod R)
                      (InvTm.foc (FocTm.pos (PosIntro.done
                        (PosNeu.inl (PosNeu.val
                          (InvTm.castTy h_1 (InvTm.castHyps h tL))))))))
                  else
                    match InvTm.castTy h_1 (InvTm.castHyps h tL) with
                    | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                      some (ReconstructVal.inv hyps (L.coprod R)
                        (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inl p)))))
                    | _ => none
                else none
              else none
            | _ => none with
          | some v => some v
          | none =>
            match reconstructGoWF (sig := sig) cert a (.invOf hyps R) with
            | some (ReconstructVal.inv hyps' A' tR) =>
              if h : hyps' = hyps then
                if h_1 : A' = R then
                  if (objectPolarity R == Polarity.neg) = true then
                    some (ReconstructVal.inv hyps (L.coprod R)
                      (InvTm.foc (FocTm.pos (PosIntro.done
                        (PosNeu.inr (PosNeu.val
                          (InvTm.castTy h_1 (InvTm.castHyps h tR))))))))
                  else
                    match InvTm.castTy h_1 (InvTm.castHyps h tR) with
                    | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                      some (ReconstructVal.inv hyps (L.coprod R)
                        (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inr p)))))
                    | _ => none
                else none
              else none
            | _ => none)
    (selectNeutralLt_tryNeu_eq_none (A := .coprod L R) cert i a hyps hsel)) rfl

/-- Shape of any `some` value from the structural `inrVal` arm. -/
private theorem coprod_inrVal_shape {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases)
    (v : ReconstructVal sig)
    (hinr :
      (match reconstructGoWF (sig := sig) cert a (.invOf hyps R) with
        | some (ReconstructVal.inv hyps' A' tR) =>
          if h : hyps' = hyps then
            if h_1 : A' = R then
              if (objectPolarity R == Polarity.neg) = true then
                some (ReconstructVal.inv hyps (L.coprod R)
                  (InvTm.foc (FocTm.pos (PosIntro.done
                    (PosNeu.inr (PosNeu.val
                      (InvTm.castTy h_1 (InvTm.castHyps h tR))))))))
              else
                match InvTm.castTy h_1 (InvTm.castHyps h tR) with
                | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                  some (ReconstructVal.inv hyps (L.coprod R)
                    (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inr p)))))
                | _ => none
            else none
          else none
        | _ => none) = some v) :
    ∃ t', v = .inv hyps (.coprod L R) t' ∧ ∃ p, t' = .foc (.pos (.done p)) := by
  match hR : reconstructGoWF (sig := sig) cert a (.invOf hyps R) with
  | none => simp [hR] at hinr
  | some (ReconstructVal.neu _ _ _) | some (ReconstructVal.wit _ _) =>
      simp [hR] at hinr
  | some (ReconstructVal.inv hyps' A' tR) =>
      by_cases hH : hyps' = hyps
      · by_cases hA : A' = R
        · cases hpolR : (objectPolarity R == Polarity.neg) with
          | true =>
              simp [hR, hH, hA, hpolR] at hinr
              cases hinr
              exact ⟨_, rfl, ⟨_, rfl⟩⟩
          | false =>
              simp [hR, hH, hA, hpolR] at hinr
              split at hinr
              · next _ =>
                  cases hinr
                  exact ⟨_, rfl, ⟨_, rfl⟩⟩
              · cases hinr
        · simp [hR, hH, hA] at hinr
      · simp [hR, hH] at hinr

/-- Shape of any `some` value from the structural `inlVal` arm. -/
private theorem coprod_inlVal_shape {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases)
    (v : ReconstructVal sig)
    (hinl :
      (match reconstructGoWF (sig := sig) cert a (.invOf hyps L) with
        | some (ReconstructVal.inv hyps' A' tL) =>
          if h : hyps' = hyps then
            if h_1 : A' = L then
              if (objectPolarity L == Polarity.neg) = true then
                some (ReconstructVal.inv hyps (L.coprod R)
                  (InvTm.foc (FocTm.pos (PosIntro.done
                    (PosNeu.inl (PosNeu.val
                      (InvTm.castTy h_1 (InvTm.castHyps h tL))))))))
              else
                match InvTm.castTy h_1 (InvTm.castHyps h tL) with
                | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                  some (ReconstructVal.inv hyps (L.coprod R)
                    (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inl p)))))
                | _ => none
            else none
          else none
        | _ => none) = some v) :
    ∃ t', v = .inv hyps (.coprod L R) t' ∧ ∃ p, t' = .foc (.pos (.done p)) := by
  match hL : reconstructGoWF (sig := sig) cert a (.invOf hyps L) with
  | none => simp [hL] at hinl
  | some (ReconstructVal.neu _ _ _) | some (ReconstructVal.wit _ _) =>
      simp [hL] at hinl
  | some (ReconstructVal.inv hyps' A' tL) =>
      by_cases hH : hyps' = hyps
      · by_cases hA : A' = L
        · cases hpolL : (objectPolarity L == Polarity.neg) with
          | true =>
              simp [hL, hH, hA, hpolL] at hinl
              cases hinl
              exact ⟨_, rfl, ⟨_, rfl⟩⟩
          | false =>
              simp [hL, hH, hA, hpolL] at hinl
              split at hinl
              · next _ =>
                  cases hinl
                  exact ⟨_, rfl, ⟨_, rfl⟩⟩
              · cases hinl
        · simp [hL, hH, hA] at hinl
      · simp [hL, hH] at hinl

theorem reconstructGoWF_invOf_coprod_inl_neg {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases) (i : Nat)
    (t : InvTm (Ctx.ofHyps hyps) L)
    (hhyp : findHypVar (sig := sig) hyps (.coprod L R) = none)
    (hfind : σ.findTypeIdx (.coprod L R) = some i)
    (hsel : cert.selectNeutralLt i a = none)
    (ht : reconstructGoWF (sig := sig) cert a (.invOf hyps L) =
      some (.inv hyps L t))
    (hpol : objectPolarity L = .neg) :
    ∃ t', reconstructGoWF (sig := sig) cert a (.invOf hyps (.coprod L R)) =
        some (.inv hyps (.coprod L R) t') ∧
      ∃ p, t' = .foc (.pos (.done p)) := by
  rw [reconstructGoWF_invOf_coprod_reduce cert a hyps L R i hhyp hfind hsel]
  cases hpr :
      ((match (σ.getCell i).witness with
        | some (Witness.inr _) => true
        | _ => false) : Bool) with
  | false =>
      simp [hpr, ht, hpol, InvTm.castHyps, InvTm.castTy]
  | true =>
      cases hinr :
          (match reconstructGoWF (sig := sig) cert a (.invOf hyps R) with
            | some (ReconstructVal.inv hyps' A' tR) =>
              if h : hyps' = hyps then
                if h_1 : A' = R then
                  if (objectPolarity R == Polarity.neg) = true then
                    some (ReconstructVal.inv hyps (L.coprod R)
                      (InvTm.foc (FocTm.pos (PosIntro.done
                        (PosNeu.inr (PosNeu.val
                          (InvTm.castTy h_1 (InvTm.castHyps h tR))))))))
                  else
                    match InvTm.castTy h_1 (InvTm.castHyps h tR) with
                    | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                      some (ReconstructVal.inv hyps (L.coprod R)
                        (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inr p)))))
                    | _ => none
                else none
              else none
            | _ => none) with
      | none =>
          simp [hpr, hinr, ht, hpol, InvTm.castHyps, InvTm.castTy]
      | some v =>
          obtain ⟨t', rfl, hp⟩ :=
            coprod_inrVal_shape (sig := sig) cert a hyps L R v hinr
          exact ⟨t', by simp [hpr, hinr], hp⟩

/-- Positive-polarity payload packing for `inl`. -/
theorem reconstructGoWF_invOf_coprod_inl_pos {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases) (i : Nat)
    (p : PosNeu (Ctx.ofHyps hyps) L)
    (hhyp : findHypVar (sig := sig) hyps (.coprod L R) = none)
    (hfind : σ.findTypeIdx (.coprod L R) = some i)
    (hsel : cert.selectNeutralLt i a = none)
    (ht : reconstructGoWF (sig := sig) cert a (.invOf hyps L) =
      some (.inv hyps L (.foc (.pos (.done p)))))
    (hpol : objectPolarity L = .pos) :
    ∃ t', reconstructGoWF (sig := sig) cert a (.invOf hyps (.coprod L R)) =
        some (.inv hyps (.coprod L R) t') ∧
      ∃ p', t' = .foc (.pos (.done p')) := by
  rw [reconstructGoWF_invOf_coprod_reduce cert a hyps L R i hhyp hfind hsel]
  cases hpr :
      ((match (σ.getCell i).witness with
        | some (Witness.inr _) => true
        | _ => false) : Bool) with
  | false =>
      simp [hpr, ht, hpol, InvTm.castHyps, InvTm.castTy, InvTm.castCtx]
  | true =>
      cases hinr :
          (match reconstructGoWF (sig := sig) cert a (.invOf hyps R) with
            | some (ReconstructVal.inv hyps' A' tR) =>
              if h : hyps' = hyps then
                if h_1 : A' = R then
                  if (objectPolarity R == Polarity.neg) = true then
                    some (ReconstructVal.inv hyps (L.coprod R)
                      (InvTm.foc (FocTm.pos (PosIntro.done
                        (PosNeu.inr (PosNeu.val
                          (InvTm.castTy h_1 (InvTm.castHyps h tR))))))))
                  else
                    match InvTm.castTy h_1 (InvTm.castHyps h tR) with
                    | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                      some (ReconstructVal.inv hyps (L.coprod R)
                        (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inr p)))))
                    | _ => none
                else none
              else none
            | _ => none) with
      | none =>
          simp [hpr, hinr, ht, hpol, InvTm.castHyps, InvTm.castTy, InvTm.castCtx]
      | some v =>
          obtain ⟨t', rfl, hp⟩ :=
            coprod_inrVal_shape (sig := sig) cert a hyps L R v hinr
          exact ⟨t', by simp [hpr, hinr], hp⟩

theorem reconstructGoWF_invOf_coprod_inr_neg {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases) (i : Nat)
    (t : InvTm (Ctx.ofHyps hyps) R)
    (hhyp : findHypVar (sig := sig) hyps (.coprod L R) = none)
    (hfind : σ.findTypeIdx (.coprod L R) = some i)
    (hsel : cert.selectNeutralLt i a = none)
    (ht : reconstructGoWF (sig := sig) cert a (.invOf hyps R) =
      some (.inv hyps R t))
    (hpol : objectPolarity R = .neg) :
    ∃ t', reconstructGoWF (sig := sig) cert a (.invOf hyps (.coprod L R)) =
        some (.inv hyps (.coprod L R) t') ∧
      ∃ p, t' = .foc (.pos (.done p)) := by
  rw [reconstructGoWF_invOf_coprod_reduce cert a hyps L R i hhyp hfind hsel]
  cases hpr :
      ((match (σ.getCell i).witness with
        | some (Witness.inr _) => true
        | _ => false) : Bool) with
  | true =>
      simp [hpr, ht, hpol, InvTm.castHyps, InvTm.castTy]
  | false =>
      cases hinl :
          (match reconstructGoWF (sig := sig) cert a (.invOf hyps L) with
            | some (ReconstructVal.inv hyps' A' tL) =>
              if h : hyps' = hyps then
                if h_1 : A' = L then
                  if (objectPolarity L == Polarity.neg) = true then
                    some (ReconstructVal.inv hyps (L.coprod R)
                      (InvTm.foc (FocTm.pos (PosIntro.done
                        (PosNeu.inl (PosNeu.val
                          (InvTm.castTy h_1 (InvTm.castHyps h tL))))))))
                  else
                    match InvTm.castTy h_1 (InvTm.castHyps h tL) with
                    | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                      some (ReconstructVal.inv hyps (L.coprod R)
                        (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inl p)))))
                    | _ => none
                else none
              else none
            | _ => none) with
      | none =>
          simp [hpr, hinl, ht, hpol, InvTm.castHyps, InvTm.castTy]
      | some v =>
          obtain ⟨t', rfl, hp⟩ :=
            coprod_inlVal_shape (sig := sig) cert a hyps L R v hinl
          exact ⟨t', by simp [hpr, hinl], hp⟩

theorem reconstructGoWF_invOf_coprod_inr_pos {sig : Signature}
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ) (a : Nat)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases) (i : Nat)
    (p : PosNeu (Ctx.ofHyps hyps) R)
    (hhyp : findHypVar (sig := sig) hyps (.coprod L R) = none)
    (hfind : σ.findTypeIdx (.coprod L R) = some i)
    (hsel : cert.selectNeutralLt i a = none)
    (ht : reconstructGoWF (sig := sig) cert a (.invOf hyps R) =
      some (.inv hyps R (.foc (.pos (.done p)))))
    (hpol : objectPolarity R = .pos) :
    ∃ t', reconstructGoWF (sig := sig) cert a (.invOf hyps (.coprod L R)) =
        some (.inv hyps (.coprod L R) t') ∧
      ∃ p', t' = .foc (.pos (.done p')) := by
  rw [reconstructGoWF_invOf_coprod_reduce cert a hyps L R i hhyp hfind hsel]
  cases hpr :
      ((match (σ.getCell i).witness with
        | some (Witness.inr _) => true
        | _ => false) : Bool) with
  | true =>
      simp [hpr, ht, hpol, InvTm.castHyps, InvTm.castTy, InvTm.castCtx]
  | false =>
      cases hinl :
          (match reconstructGoWF (sig := sig) cert a (.invOf hyps L) with
            | some (ReconstructVal.inv hyps' A' tL) =>
              if h : hyps' = hyps then
                if h_1 : A' = L then
                  if (objectPolarity L == Polarity.neg) = true then
                    some (ReconstructVal.inv hyps (L.coprod R)
                      (InvTm.foc (FocTm.pos (PosIntro.done
                        (PosNeu.inl (PosNeu.val
                          (InvTm.castTy h_1 (InvTm.castHyps h tL))))))))
                  else
                    match InvTm.castTy h_1 (InvTm.castHyps h tL) with
                    | InvTm.foc (FocTm.pos (PosIntro.done p)) =>
                      some (ReconstructVal.inv hyps (L.coprod R)
                        (InvTm.foc (FocTm.pos (PosIntro.done (PosNeu.inl p)))))
                    | _ => none
                else none
              else none
            | _ => none) with
      | none =>
          simp [hpr, hinl, ht, hpol, InvTm.castHyps, InvTm.castTy, InvTm.castCtx]
      | some v =>
          obtain ⟨t', rfl, hp⟩ :=
            coprod_inlVal_shape (sig := sig) cert a hyps L R v hinl
          exact ⟨t', by simp [hpr, hinl], hp⟩

/-! ## Master Dom ⇒ reconstructGoWF induction -/

variable {sig : Signature}

private def ReconstructGoSucceeds {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat) : ReconstructCmd sig → Prop
  | .neuOf hyps A =>
      ∃ n, reconstructGoWF (sig := sig) cert ambientRank (.neuOf hyps A) =
        some (.neu hyps A n)
  | .witness hyps w =>
      ∀ (A : Object sig.nBases),
        WitnessReconShape σ hyps A w →
          ∃ n, reconstructGoWF (sig := sig) cert ambientRank (.witness hyps w) =
            some (.wit hyps ⟨A, n⟩)
  | .invOf hyps A =>
      ∃ t, reconstructGoWF (sig := sig) cert ambientRank (.invOf hyps A) =
          some (.inv hyps A t) ∧
        (objectPolarity A = .pos → ∃ p, t = .foc (.pos (.done p)))

private def ReconstructGoDom {Γ : ReachCtx sig.nBases}
    {goal : Object sig.nBases} (C : CertifiedComplete (sig := sig) Γ goal)
    (ambientRank : Nat) : ReconstructCmd sig → Prop
  | .neuOf hyps A =>
      HypsExt (sig := sig) Γ hyps ∧
        ((findHypVar (sig := sig) hyps A).isSome = true ∨
          ∃ (i : Nat) (b : SlotNew) (w : Witness) (r : Nat),
            C.result.state.findTypeIdx A = some i ∧
              (C.result.state.getCell i).slotWitness b = some w ∧
                Witness.isNeutral w = true ∧
                  C.result.cert.rank i b = some r ∧
                    r ≤ ambientRank)
  | .witness hyps w =>
      HypsExt (sig := sig) Γ hyps ∧
        Witness.isNeutral w = true ∧
          ∃ (i : Nat) (b : SlotNew) (r : Nat) (A : Object sig.nBases),
            (C.result.state.getCell i).slotWitness b = some w ∧
              C.result.cert.rank i b = some r ∧
                r ≤ ambientRank ∧
                  C.result.state.typeAt i = some A ∧
                    WitnessReconShape C.result.state hyps A w
  | .invOf hyps A =>
      HypsExt (sig := sig) Γ hyps ∧
        InvertibleArgDomain C.result.cert ambientRank hyps A

theorem reconstructGoWF_of_dom {Γ : ReachCtx sig.nBases} {goal : Object sig.nBases}
    (C : CertifiedComplete (sig := sig) Γ goal) :
    ∀ (ambientRank : Nat) (cmd : ReconstructCmd sig),
      ReconstructGoDom C ambientRank cmd →
        ReconstructGoSucceeds C.result.cert ambientRank cmd := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a iha =>
    intro cmd0
    suffices
        ∀ (ph sz : Nat) (cmd : ReconstructCmd sig),
          (ReconstructCmd.phase (sig := sig) cmd).toNat = ph →
            ReconstructCmd.objSize (sig := sig) cmd = sz →
              ReconstructGoDom C a cmd →
                ReconstructGoSucceeds C.result.cert a cmd by
      exact this _ _ cmd0 rfl rfl
    intro ph
    induction ph using Nat.strong_induction_on with
    | h ph ihp =>
      intro sz
      induction sz using Nat.strong_induction_on with
      | h sz ihs =>
        intro cmd hph hsz hdom
        cases cmd with
        | neuOf hyps A =>
            obtain ⟨hext, hreq⟩ := hdom
            cases hhyp : findHypVar (sig := sig) hyps A with
            | some x =>
                refine ⟨.var x, ?_⟩
                simp [reconstructGoWF, hhyp]
            | none =>
                obtain hreq' | ⟨i, b, w, rNeu, hfind, hw, hne, hr, hle⟩ := hreq
                · simp [hhyp] at hreq'
                · obtain ⟨w', r', hsel⟩ :=
                    C.result.cert.selectNeutralLe_isSome_of_ranked_neutral i a
                      hw hne hr hle
                  obtain ⟨b', hw', hne', hr'⟩ :=
                    C.result.cert.selectNeutralLe_slot hsel
                  have hty := ReachState.typeAt_of_findTypeIdx hfind
                  have ⟨A₀, hA₀, hsΓ⟩ :=
                    StoredNeutralDomain.typeAt_reconOk C
                      ⟨hw', hne', by simp [hr']⟩
                  have hAeq : A₀ = A := ReachState.typeAt_inj hA₀ hty
                  have hshape : WitnessReconShape C.result.state hyps A w' :=
                    WitnessReconShape.of_hypsExt hext (hAeq ▸ hsΓ)
                  have hdomW : ReconstructGoDom C r' (.witness hyps w') :=
                    ⟨hext, hne', i, b', r', A, hw', hr', le_rfl, hty, hshape⟩
                  have ihW : ReconstructGoSucceeds C.result.cert r'
                      (.witness hyps w') := by
                    cases Nat.lt_or_eq_of_le
                        (C.result.cert.selectNeutralLe_rank_le i a hsel) with
                    | inl hlt => exact iha r' hlt (.witness hyps w') hdomW
                    | inr heq =>
                        subst heq
                        have hphW :
                            (ReconstructCmd.phase (sig := sig)
                              (.witness hyps w')).toNat < ph := by
                          simp [ReconstructCmd.phase, ReconPhase.toNat, ← hph]
                        exact ihp _ hphW _
                          (.witness hyps w') rfl rfl hdomW
                  obtain ⟨n, hn⟩ := ihW A hshape
                  refine ⟨n, ?_⟩
                  rw [reconstructGoWF.eq_1]
                  simp only [hhyp, hfind]
                  refine Eq.trans (congrArg
                      (fun o =>
                        match hsel : o with
                        | none => none
                        | some (w, rNeu) =>
                          match reconstructGoWF (sig := sig) C.result.cert rNeu
                              (.witness hyps w) with
                          | some (ReconstructVal.wit hyps' ⟨B, n⟩) =>
                            if hH : hyps' = hyps then
                              if hA : B = A then
                                some (ReconstructVal.neu hyps A
                                  (hA ▸ NegNeu.castHyps hH n))
                              else none
                            else none
                          | _ => none)
                      hsel) ?_
                  simp [hn, NegNeu.castHyps, NegNeu.cast, NegNeu.castCtx]

        | witness hyps w =>
            obtain ⟨hext, hne, i, b, r, A₀, hw, hr, hle, hty, hshape₀⟩ := hdom
            intro A hshape
            have hA : A = A₀ := by
              cases w with
              | ctxVar k =>
                  change hyps[k]? = some A at hshape
                  change hyps[k]? = some A₀ at hshape₀
                  exact Option.some.inj (hshape.symm.trans hshape₀)
              | fstHyp k =>
                  obtain ⟨L, R, hhyps, hA⟩ := hshape
                  obtain ⟨L', R', hhyps', hA₀⟩ := hshape₀
                  cases Option.some.inj (hhyps.symm.trans hhyps')
                  exact hA.trans hA₀.symm
              | sndHyp k =>
                  obtain ⟨L, R, hhyps, hA⟩ := hshape
                  obtain ⟨L', R', hhyps', hA₀⟩ := hshape₀
                  cases Option.some.inj (hhyps.symm.trans hhyps')
                  exact hA.trans hA₀.symm
              | fstType p =>
                  obtain ⟨L, R, htyP, hA⟩ := hshape
                  obtain ⟨L', R', htyP', hA₀⟩ := hshape₀
                  cases Option.some.inj (htyP.symm.trans htyP')
                  exact hA.trans hA₀.symm
              | sndType p =>
                  obtain ⟨L, R, htyP, hA⟩ := hshape
                  obtain ⟨L', R', htyP', hA₀⟩ := hshape₀
                  cases Option.some.inj (htyP.symm.trans htyP')
                  exact hA.trans hA₀.symm
              | app fn arg =>
                  obtain ⟨Arg, Ret, hfn, harg, hA⟩ := hshape
                  obtain ⟨Arg', Ret', hfn', harg', hA₀⟩ := hshape₀
                  cases Option.some.inj (hfn.symm.trans hfn')
                  exact hA.trans hA₀.symm
              | appTy fn arg =>
                  obtain ⟨Arg, Ret, hfn, harg, hA⟩ := hshape
                  obtain ⟨Arg', Ret', hfn', harg', hA₀⟩ := hshape₀
                  cases Option.some.inj (hfn.symm.trans hfn')
                  exact hA.trans hA₀.symm
              | unit | inl _ | inr _ | eta =>
                  simp [Witness.isNeutral] at hne
            subst hA
            cases w with
            | ctxVar k =>
                exact reconstructGoWF_ctxVar C.result.cert a hyps k hshape
            | fstHyp k =>
                exact reconstructGoWF_fstHyp C.result.cert a hyps k hshape
            | sndHyp k =>
                exact reconstructGoWF_sndHyp C.result.cert a hyps k hshape
            | fstType p =>
                obtain ⟨wP, rP, hsel⟩ :=
                  C.result.cert.selectNeutralLt_of_fstType i a hw hr hle
                refine reconstructGoWF_fstType C.result.cert a hyps p
                  hshape hsel ?_
                intro L R htyP hAL
                have hfindP :=
                  C.result.state.findTypeIdx_of_typeAt C.types_nodup htyP
                obtain ⟨bP, hwP, hneP, hrP⟩ :=
                  C.result.cert.selectNeutralLt_slot hsel
                exact iha rP
                  (C.result.cert.selectNeutralLt_rank_lt p a hsel)
                  (.neuOf hyps (.prod L R))
                  ⟨hext, Or.inr ⟨p, bP, wP, rP, hfindP, hwP, hneP, hrP, le_rfl⟩⟩
            | sndType p =>
                obtain ⟨wP, rP, hsel⟩ :=
                  C.result.cert.selectNeutralLt_of_sndType i a hw hr hle
                refine reconstructGoWF_sndType C.result.cert a hyps p
                  hshape hsel ?_
                intro L R htyP hAR
                have hfindP :=
                  C.result.state.findTypeIdx_of_typeAt C.types_nodup htyP
                obtain ⟨bP, hwP, hneP, hrP⟩ :=
                  C.result.cert.selectNeutralLt_slot hsel
                exact iha rP
                  (C.result.cert.selectNeutralLt_rank_lt p a hsel)
                  (.neuOf hyps (.prod L R))
                  ⟨hext, Or.inr ⟨p, bP, wP, rP, hfindP, hwP, hneP, hrP, le_rfl⟩⟩
            | app fnHyp argIdx =>
                refine reconstructGoWF_app C.result.cert a hyps fnHyp argIdx
                  hshape ?_
                intro Arg Ret hfn harg hA
                have hphI :
                    (ReconstructCmd.phase (sig := sig)
                      (.invOf hyps Arg)).toNat < ph := by
                  simp [ReconstructCmd.phase, ReconPhase.toNat, ← hph]
                have ihI := ihp _ hphI _ (.invOf hyps Arg) rfl rfl
                  ⟨hext, InvertibleArgDomain.of_app_arg (Ret := Ret)
                    C.result.cert a hyps C.types_nodup hw harg hr hle⟩
                obtain ⟨t, ht, _⟩ := ihI
                exact ⟨t, ht⟩
            | appTy fnIdx argIdx =>
                obtain ⟨wFn, rFn, hsel⟩ :=
                  C.result.cert.selectNeutralLt_of_appTy i a hw hr hle
                refine reconstructGoWF_appTy C.result.cert a hyps fnIdx argIdx
                  hshape hsel ?_ ?_
                · intro Arg Ret hfn harg hA
                  have hfindF :=
                    C.result.state.findTypeIdx_of_typeAt C.types_nodup hfn
                  obtain ⟨bF, hwF, hneF, hrF⟩ :=
                    C.result.cert.selectNeutralLt_slot hsel
                  exact iha rFn
                    (C.result.cert.selectNeutralLt_rank_lt fnIdx a hsel)
                    (.neuOf hyps (.exp Arg Ret))
                    ⟨hext, Or.inr ⟨fnIdx, bF, wFn, rFn, hfindF, hwF, hneF, hrF,
                      le_rfl⟩⟩
                · intro Arg Ret hfn harg hA
                  have hphI :
                      (ReconstructCmd.phase (sig := sig)
                        (.invOf hyps Arg)).toNat < ph := by
                    simp [ReconstructCmd.phase, ReconPhase.toNat, ← hph]
                  have ihI := ihp _ hphI _ (.invOf hyps Arg) rfl rfl
                    ⟨hext, InvertibleArgDomain.of_appTy_arg (Ret := Ret)
                      C.result.cert a hyps C.types_nodup hw harg hr hle⟩
                  obtain ⟨t, ht, _⟩ := ihI
                  exact ⟨t, ht⟩
            | unit | inl _ | inr _ | eta =>
                simp [Witness.isNeutral] at hne
        | invOf hyps A =>
            obtain ⟨hext, hinv⟩ := hdom
            cases hhyp : findHypVar (sig := sig) hyps A with
            | some x =>
                cases hpol : objectPolarity A with
                | pos =>
                    refine ⟨.foc (.pos (.done (.neu (.var x)))), ?_, ?_⟩
                    · cases A <;> simp [reconstructGoWF, hhyp, hpol]
                    · intro; exact ⟨_, rfl⟩
                | neg =>
                    refine ⟨.foc (.neg (.done (.var x))), ?_, ?_⟩
                    · cases A <;> simp [reconstructGoWF, hhyp, hpol]
                    · intro hpos; cases hpol.symm.trans hpos
            | none =>
                by_cases hAu : A = (.unit : Object sig.nBases)
                · subst hAu
                  cases hfind : C.result.state.findTypeIdx
                      (.unit : Object sig.nBases) with
                  | none =>
                      refine ⟨.unit,
                        reconstructGoWF_invOf_unit_structural
                          C.result.cert a hyps hhyp (by simp [hfind]),
                        fun hpos => by cases hpos⟩
                  | some i =>
                      cases hsel : C.result.cert.selectNeutralLt i a with
                      | none =>
                          refine ⟨.unit,
                            reconstructGoWF_invOf_unit_structural
                              C.result.cert a hyps hhyp ?_,
                            fun hpos => by cases hpos⟩
                          · simp only [hfind]
                            exact selectNeutralLt_tryNeu_eq_none
                              (A := .unit) C.result.cert i a hyps hsel
                      | some wr =>
                          obtain ⟨w, rNeu⟩ := wr
                          obtain ⟨bW, hwW, hneW, hrW⟩ :=
                            C.result.cert.selectNeutralLt_slot hsel
                          have htyU := ReachState.typeAt_of_findTypeIdx hfind
                          have ⟨A₀, hA₀, hsΓ⟩ :=
                            StoredNeutralDomain.typeAt_reconOk C
                              ⟨hwW, hneW, by simp [hrW]⟩
                          have hAeq : A₀ = .unit :=
                            ReachState.typeAt_inj hA₀ htyU
                          have hshape :
                              WitnessReconShape C.result.state hyps .unit w :=
                            WitnessReconShape.of_hypsExt hext (hAeq ▸ hsΓ)
                          have ihW :=
                            iha rNeu
                              (C.result.cert.selectNeutralLt_rank_lt i a hsel)
                              (.witness hyps w)
                              ⟨hext, hneW, i, bW, rNeu, .unit, hwW, hrW,
                                le_rfl, htyU, hshape⟩
                          obtain ⟨n, hn⟩ := ihW .unit hshape
                          refine ⟨.foc (.neg (.done n)),
                            reconstructGoWF_invOf_tryNeu_unit
                              C.result.cert a hyps i w rNeu n hhyp hfind hsel hn,
                            fun hpos => by cases hpos⟩
                · have hranked :
                      ∃ (i : Nat) (b : SlotNew) (r : Nat),
                        C.result.state.findTypeIdx A = some i ∧
                          C.result.cert.rank i b = some r ∧ r < a := by
                    rcases hinv with h | h | h
                    · simp [hhyp] at h
                    · exact (hAu h).elim
                    · exact h
                  obtain ⟨i, b, r, hfind, hr, hlt⟩ := hranked
                  cases hsel : C.result.cert.selectNeutralLt i a with
                  | some wr =>
                      obtain ⟨w, rNeu⟩ := wr
                      obtain ⟨bW, hwW, hneW, hrW⟩ :=
                        C.result.cert.selectNeutralLt_slot hsel
                      have hty := ReachState.typeAt_of_findTypeIdx hfind
                      have ⟨A₀, hA₀, hsΓ⟩ :=
                        StoredNeutralDomain.typeAt_reconOk C
                          ⟨hwW, hneW, by simp [hrW]⟩
                      have hAeq : A₀ = A := ReachState.typeAt_inj hA₀ hty
                      have hshape :
                          WitnessReconShape C.result.state hyps A w :=
                        WitnessReconShape.of_hypsExt hext (hAeq ▸ hsΓ)
                      have ihW :=
                        iha rNeu
                          (C.result.cert.selectNeutralLt_rank_lt i a hsel)
                          (.witness hyps w)
                          ⟨hext, hneW, i, bW, rNeu, A, hwW, hrW, le_rfl, hty,
                            hshape⟩
                      obtain ⟨n, hn⟩ := ihW A hshape
                      cases A with
                      | base q =>
                          refine ⟨.foc (.pos (.done (.neu n))),
                            reconstructGoWF_invOf_tryNeu_base
                              C.result.cert a hyps q i w rNeu n hhyp hfind
                              hsel hn,
                            fun _ => ⟨_, rfl⟩⟩
                      | never =>
                          refine ⟨.foc (.pos (.done (.neu n))),
                            reconstructGoWF_invOf_tryNeu_never
                              C.result.cert a hyps i w rNeu n hhyp hfind
                              hsel hn,
                            fun _ => ⟨_, rfl⟩⟩
                      | prod L R =>
                          refine ⟨.foc (.neg (.done n)),
                            reconstructGoWF_invOf_tryNeu_prod
                              C.result.cert a hyps L R i w rNeu n hhyp hfind
                              hsel hn,
                            fun hpos => by cases hpos⟩
                      | exp Arg Ret =>
                          refine ⟨.foc (.neg (.done n)),
                            reconstructGoWF_invOf_tryNeu_exp
                              C.result.cert a hyps Arg Ret i w rNeu n hhyp
                              hfind hsel hn,
                            fun hpos => by cases hpos⟩
                      | unit => exact (hAu rfl).elim
                      | coprod L R =>
                          refine ⟨.foc (.pos (.done (.neu n))),
                            reconstructGoWF_invOf_tryNeu_coprod
                              C.result.cert a hyps L R i w rNeu n hhyp hfind
                              hsel hn,
                            fun _ => ⟨_, rfl⟩⟩
                  | none =>
                      have hrs : (C.result.cert.rank i b).isSome = true := by
                        simp [hr]
                      have hw? :
                          ∃ w, (C.result.state.getCell i).slotWitness b =
                            some w := by
                        have : ((C.result.state.getCell i).slotWitness b).isSome =
                            true := by
                          simpa [hrs] using (C.result.cert.rank_iff i b).symm
                        exact Option.isSome_iff_exists.mp this
                      obtain ⟨w, hw⟩ := hw?
                      have hty := ReachState.typeAt_of_findTypeIdx hfind
                      have hneF : Witness.isNeutral w = false := by
                        by_contra hneT
                        have hneW : Witness.isNeutral w = true := by
                          cases h : Witness.isNeutral w with
                          | true => rfl
                          | false => exact absurd h hneT
                        obtain ⟨_, _, hsome⟩ :=
                          C.result.cert.selectNeutralLt_isSome_of_ranked_neutral
                            i a hw hneW hr hlt
                        simp [hsome] at hsel
                      have hfit : Witness.fits w A = true :=
                        C.sound.fitsOk i A w hty
                          (ReachCell.slotWitness_mem hw)
                      cases w with
                      | eta =>
                          cases A with
                          | prod L R =>
                              obtain ⟨hLdom, hRdom⟩ :=
                                InvertibleArgDomain.of_eta_prod_components
                                  C.result.cert a hyps C.types_nodup hw hty hr
                                  hlt
                              have hszL :
                                  ReconstructCmd.objSize (sig := sig)
                                    (.invOf hyps L) < sz := by
                                simpa [ReconstructCmd.objSize, ← hsz] using
                                  reconObjectSize_prod_left_lt L R
                              have hszR :
                                  ReconstructCmd.objSize (sig := sig)
                                    (.invOf hyps R) < sz := by
                                simpa [ReconstructCmd.objSize, ← hsz] using
                                  reconObjectSize_prod_right_lt L R
                              obtain ⟨tL, htL, _⟩ :=
                                ihs _ hszL (.invOf hyps L) hph rfl ⟨hext, hLdom⟩
                              obtain ⟨tR, htR, _⟩ :=
                                ihs _ hszR (.invOf hyps R) hph rfl ⟨hext, hRdom⟩
                              refine ⟨.pair tL tR,
                                reconstructGoWF_invOf_eta_prod
                                  C.result.cert a hyps L R i tL tR hhyp hfind
                                  hsel htL htR,
                                fun hpos => by cases hpos⟩
                          | exp Arg Ret =>
                              have hext' := HypsExt.push (sig := sig) hext Arg
                              have hRet :=
                                InvertibleArgDomain.of_eta_exp_ret
                                  C.result.cert a (hyps.push Arg)
                                  C.types_nodup hw hty hr hlt
                              have hszR :
                                  ReconstructCmd.objSize (sig := sig)
                                    (.invOf (hyps.push Arg) Ret) < sz := by
                                simpa [ReconstructCmd.objSize, ← hsz] using
                                  reconObjectSize_exp_ret_lt Arg Ret
                              obtain ⟨t, ht, _⟩ :=
                                ihs _ hszR (.invOf (hyps.push Arg) Ret) hph rfl
                                  ⟨hext', hRet⟩
                              refine
                                ⟨.lam (InvTm.castCtx (Ctx.ofHyps_push hyps Arg)
                                  t),
                                  reconstructGoWF_invOf_eta_exp
                                    C.result.cert a hyps Arg Ret i t hhyp hfind
                                    hsel ht,
                                  fun hpos => by cases hpos⟩
                          | _ => simp [Witness.fits] at hfit
                      | inl p =>
                          cases A with
                          | coprod L R =>
                              have hLdom :=
                                InvertibleArgDomain.of_inl_payload
                                  C.result.cert a hyps C.types_nodup hw hty hr
                                  hlt
                              have hszL :
                                  ReconstructCmd.objSize (sig := sig)
                                    (.invOf hyps L) < sz := by
                                simpa [ReconstructCmd.objSize, ← hsz] using
                                  reconObjectSize_coprod_left_lt L R
                              obtain ⟨t, ht, hposShape⟩ :=
                                ihs _ hszL (.invOf hyps L) hph rfl ⟨hext, hLdom⟩
                              cases hpol : objectPolarity L with
                              | neg =>
                                  obtain ⟨t', ht', hp⟩ :=
                                    reconstructGoWF_invOf_coprod_inl_neg
                                      C.result.cert a hyps L R i t hhyp hfind
                                      hsel ht hpol
                                  exact ⟨t', ht', fun _ => hp⟩
                              | pos =>
                                  obtain ⟨pL, hpL⟩ := hposShape hpol
                                  subst hpL
                                  obtain ⟨t', ht', hp⟩ :=
                                    reconstructGoWF_invOf_coprod_inl_pos
                                      C.result.cert a hyps L R i pL hhyp hfind
                                      hsel ht hpol
                                  exact ⟨t', ht', fun _ => hp⟩
                          | _ => simp [Witness.fits] at hfit
                      | inr p =>
                          cases A with
                          | coprod L R =>
                              have hRdom :=
                                InvertibleArgDomain.of_inr_payload
                                  C.result.cert a hyps C.types_nodup hw hty hr
                                  hlt
                              have hszR :
                                  ReconstructCmd.objSize (sig := sig)
                                    (.invOf hyps R) < sz := by
                                simpa [ReconstructCmd.objSize, ← hsz] using
                                  reconObjectSize_coprod_right_lt L R
                              obtain ⟨t, ht, hposShape⟩ :=
                                ihs _ hszR (.invOf hyps R) hph rfl ⟨hext, hRdom⟩
                              cases hpol : objectPolarity R with
                              | neg =>
                                  obtain ⟨t', ht', hp⟩ :=
                                    reconstructGoWF_invOf_coprod_inr_neg
                                      C.result.cert a hyps L R i t hhyp hfind
                                      hsel ht hpol
                                  exact ⟨t', ht', fun _ => hp⟩
                              | pos =>
                                  obtain ⟨pR, hpR⟩ := hposShape hpol
                                  subst hpR
                                  obtain ⟨t', ht', hp⟩ :=
                                    reconstructGoWF_invOf_coprod_inr_pos
                                      C.result.cert a hyps L R i pR hhyp hfind
                                      hsel ht hpol
                                  exact ⟨t', ht', fun _ => hp⟩
                          | _ => simp [Witness.fits] at hfit
                      | unit =>
                          cases A <;> simp [Witness.fits] at hfit
                          exact (hAu rfl).elim
                      | ctxVar _ | fstHyp _ | sndHyp _ | fstType _
                      | sndType _ | app _ _ | appTy _ _ =>
                          simp [Witness.isNeutral] at hneF

/-! ## Package specialization -/

theorem reconstructWitnessTotalWF_inst : ReconstructWitnessTotalWF sig := by
  dsimp [ReconstructWitnessTotalWF]
  intro Γ goal i b w hdom
  set C := certifiedComplete (sig := sig) Γ goal with hC
  obtain ⟨A, hty, hshape⟩ := StoredNeutralDomain.typeAt_reconOk C hdom
  obtain ⟨hw, hne, hrs⟩ := hdom
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hrs
  have hext := HypsExt.refl (sig := sig) Γ
  have hsucc := reconstructGoWF_of_dom C r (.witness Γ.hyps w)
    ⟨hext, hne, i, b, r, A, hw, hr, le_rfl, hty, hshape⟩
  obtain ⟨n, hn⟩ := hsucc A hshape
  refine ⟨A, n, hty, hne, ?_⟩
  simp [reconstructWitnessWF, hr, hn, NegNeu.castHyps, NegNeu.castCtx]

theorem invertibleArgTotalWF_inst : InvertibleArgTotalWF sig := by
  dsimp [InvertibleArgTotalWF]
  intro Γ goal ambient A hinv
  set C := certifiedComplete (sig := sig) Γ goal with hC
  have hext := HypsExt.refl (sig := sig) Γ
  obtain ⟨t, ht, _⟩ :=
    reconstructGoWF_of_dom C ambient (.invOf Γ.hyps A) ⟨hext, hinv⟩
  simp [invOfTypeWF, ht, InvTm.castHyps, InvTm.castTy, InvTm.castCtx]

theorem requestedNeutralTotalWF_inst : RequestedNeutralTotalWF sig := by
  dsimp [RequestedNeutralTotalWF]
  intro Γ goal A hreq
  set C := certifiedComplete (sig := sig) Γ goal with hC
  have hext := HypsExt.refl (sig := sig) Γ
  match hreq with
  | Or.inl hhyp =>
      cases hfind : C.result.state.findTypeIdx A with
      | none =>
          obtain ⟨n, hn⟩ :=
            reconstructGoWF_of_dom C 0 (.neuOf Γ.hyps A) ⟨hext, Or.inl hhyp⟩
          simp [neuOfTypeWF, hfind, hn, NegNeu.castHyps, NegNeu.cast, NegNeu.castCtx]
      | some i =>
          obtain ⟨n, hn⟩ :=
            reconstructGoWF_of_dom C
              ((C.result.cert.rankOfNeutralSlot i).getD 0) (.neuOf Γ.hyps A)
              ⟨hext, Or.inl hhyp⟩
          simp [neuOfTypeWF, hfind, hn, NegNeu.castHyps, NegNeu.cast, NegNeu.castCtx]
  | Or.inr hcell =>
      obtain ⟨i, hfind, hrs⟩ := hcell
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hrs
      have hAmb : (C.result.cert.rankOfNeutralSlot i).getD 0 = r := by
        simp [hr]
      have hle : r ≤ (C.result.cert.rankOfNeutralSlot i).getD 0 := by
        simp [hAmb]
      obtain ⟨w, r', hsel⟩ :=
        C.result.cert.selectNeutralLe_of_rankOfNeutralSlot i
          ((C.result.cert.rankOfNeutralSlot i).getD 0) hr hle
      obtain ⟨b, hw, hne, hr'⟩ := C.result.cert.selectNeutralLe_slot hsel
      have hle' : r' ≤ (C.result.cert.rankOfNeutralSlot i).getD 0 :=
        C.result.cert.selectNeutralLe_rank_le i _ hsel
      obtain ⟨n, hn⟩ :=
        reconstructGoWF_of_dom C
          ((C.result.cert.rankOfNeutralSlot i).getD 0) (.neuOf Γ.hyps A)
          ⟨hext, Or.inr ⟨i, b, w, r', hfind, hw, hne, hr', hle'⟩⟩
      simp [neuOfTypeWF, hfind, hn, NegNeu.castHyps, NegNeu.cast, NegNeu.castCtx]

private theorem neutralWitness_of_ranked_neutral {n : Nat} {σ : ReachState n}
    {i : Nat} {b : SlotNew} {w : Witness}
    (hw : (σ.getCell i).slotWitness b = some w)
    (hne : Witness.isNeutral w = true) :
    (σ.getCell i).neutralWitness.isSome = true := by
  cases b with
  | true =>
      have : (σ.getCell i).newWitness = some w := by
        simpa [ReachCell.slotWitness] using hw
      simp [ReachCell.neutralWitness, this, hne]
  | false =>
      have hold : (σ.getCell i).oldWitness = some w := by
        simpa [ReachCell.slotWitness] using hw
      cases hn : (σ.getCell i).newWitness with
      | some wN =>
          cases hneN : Witness.isNeutral wN with
          | true => simp [ReachCell.neutralWitness, hn, hneN]
          | false => simp [ReachCell.neutralWitness, hn, hneN, hold, hne]
      | none => simp [ReachCell.neutralWitness, hn, hold, hne]

theorem inconsistentNeverTotalWF_inst : InconsistentNeverTotalWF sig := by
  dsimp [InconsistentNeverTotalWF]
  intro Γ goal hinc
  set C := certifiedComplete (sig := sig) Γ goal with hC
  obtain ⟨i, hty, hsd⟩ := C.sound.inconsistentNever hinc
  obtain ⟨b, r, hr⟩ := C.result.cert.ranked_of_simplyDeducible i hsd
  have hrs : (C.result.cert.rank i b).isSome = true := by simp [hr]
  have hw? :
      ∃ w, (C.result.state.getCell i).slotWitness b = some w := by
    have : ((C.result.state.getCell i).slotWitness b).isSome = true := by
      simpa [hrs] using (C.result.cert.rank_iff i b).symm
    exact Option.isSome_iff_exists.mp this
  obtain ⟨w, hw⟩ := hw?
  have hwMem :
      (C.result.state.getCell i).oldWitness = some w ∨
        (C.result.state.getCell i).newWitness = some w := by
    cases b with
    | false => exact Or.inl (by simpa [ReachCell.slotWitness] using hw)
    | true => exact Or.inr (by simpa [ReachCell.slotWitness] using hw)
  have hfit : Witness.fits w (.never : Object sig.nBases) = true :=
    C.sound.fitsOk i (.never) w hty hwMem
  have hne : Witness.isNeutral w = true := by
    cases w <;> simp [Witness.fits, Witness.isNeutral] at hfit ⊢
  have hnw := neutralWitness_of_ranked_neutral hw hne
  obtain ⟨wN, hnw'⟩ := Option.isSome_iff_exists.mp hnw
  have hrsN : (C.result.cert.rankOfNeutralSlot i).isSome = true := by
    dsimp [ReachRankCert.rankOfNeutralSlot]
    simp only [hnw']
    rcases ReachCell.neutralWitness_slot hnw' with ⟨hnew, hwN⟩ | ⟨hnew, hwN⟩
    · simp [hnew]
      have : ((C.result.state.getCell i).slotWitness true).isSome = true := by
        simp [hwN]
      simpa [this] using (C.result.cert.rank_iff i true).symm
    · simp [hnew]
      have : ((C.result.state.getCell i).slotWitness false).isSome = true := by
        simp [hwN]
      simpa [this] using (C.result.cert.rank_iff i false).symm
  have hfind := C.result.state.findTypeIdx_of_typeAt C.types_nodup hty
  have hreq : RequestedNeutralDomain C.result.cert Γ.hyps
      (.never : Object sig.nBases) :=
    Or.inr ⟨i, hfind, hrsN⟩
  simpa [← hC, RequestedNeutralTotalWF] using
    requestedNeutralTotalWF_inst (sig := sig) Γ goal (.never) hreq

theorem consistencyWitnessTotalWF_inst : ConsistencyWitnessTotalWF sig := by
  dsimp [ConsistencyWitnessTotalWF]
  intro Γ goal P w hany
  set C := certifiedComplete (sig := sig) Γ goal with hC
  set σ := C.result.state with hσ
  have hmem : (P, w) ∈ (buildSchedule σ).entries := by
    obtain ⟨k, hk, hp⟩ :=
      (Array.any_eq_true
        (p := fun e : Object sig.nBases × Witness => e.1 == P && e.2 == w)).mp
        hany
    have h1 : (buildSchedule σ).entries[k].1 = P := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hp; exact hp.1
    have h2 : (buildSchedule σ).entries[k].2 = w := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hp; exact hp.2
    have heq : (buildSchedule σ).entries[k] = (P, w) := by
      revert h1 h2; cases (buildSchedule σ).entries[k]; intro h1 h2; simp_all
    exact (heq ▸ Array.getElem_mem hk)
  obtain ⟨i, hty, hw, hne, hrs⟩ := mem_buildSchedule_storedNeutral C.result.cert hmem
  have hdom : StoredNeutralDomain C.result.cert i true w := ⟨hw, hne, hrs⟩
  obtain ⟨A, n, htyA, _, hrec⟩ := by
    have h := reconstructWitnessTotalWF_inst (sig := sig)
    dsimp [ReconstructWitnessTotalWF] at h
    exact h Γ goal i true w hdom
  have hA : A = P := Option.some.inj (htyA.symm.trans hty)
  subst hA
  exact ⟨n, i, true, hty, hw, hrec⟩

theorem reconstructTotalityPackage : ReconstructTotalityPackage sig :=
  ⟨reconstructWitnessTotalWF_inst, consistencyWitnessTotalWF_inst,
    inconsistentNeverTotalWF_inst, invertibleArgTotalWF_inst,
    requestedNeutralTotalWF_inst⟩

end Equality
end Gimbal
