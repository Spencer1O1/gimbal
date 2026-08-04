/-
  Bounded design spike: proof-only reachability rank certificates.

  Goal: retain a well-founded discovery certificate *around* `runReachability`
  without adding observable `discoverGen` fields to `ReachCell` / `Witness`.
  Operational state, schedule identity, and fixed-point equality stay unchanged.

  **Spike scope:** parent relation, assign-once audit, `CertifiedReachResult`
  shape, certified `markHyp` + one `discover` rule, lex reconstruction measure,
  inconsistent-never obligation, migration-cost comparison.

  Does **not** resume the retained schedule adapter or EncodeTotal.
-/

import Gimbal.Equality.Reachability
import Gimbal.Equality.ReachComplete
import Gimbal.Equality.ReconstructTotal
import Gimbal.Equality.Polarized

namespace Gimbal
namespace Equality

/-! ## Assign-once audit

`ReachCell.record` keeps the **first** witness per provenance slot (`old` /
`new`). If the slot is already occupied, the call is a no-op.
Witnesses are never replaced.

**Rank validity under assign-once:** when a slot first receives witness `w` at
rank `r`, that pairing is permanent. Later `discover` / `markHyp` on the same
slot leave `w` and `r` unchanged. Dual-fire into the *other* provenance slot is
independent and does not disturb the first slot's rank.
-/

theorem ReachCell.record_keeps_old (c : ReachCell) (w w' : Witness)
    (h : c.oldWitness = some w) :
    (c.record false w').oldWitness = some w := by
  simp [ReachCell.record, h]

theorem ReachCell.record_keeps_new (c : ReachCell) (w w' : Witness)
    (h : c.newWitness = some w) :
    (c.record true w').newWitness = some w := by
  simp [ReachCell.record, h]

theorem ReachCell.record_sets_old_of_none (c : ReachCell) (w : Witness)
    (h : c.oldWitness = none) :
    (c.record false w).oldWitness = some w := by
  simp [ReachCell.record, h]

theorem ReachCell.record_sets_new_of_none (c : ReachCell) (w : Witness)
    (h : c.newWitness = none) :
    (c.record true w).newWitness = some w := by
  simp [ReachCell.record, h]

/-! ## Parent relation (reconstruction-relevant cell indices)

Parents are **type-table indices** that `reconstructGo` may follow via
`.neuOf` / cell witnesses. Hypothesis indices (`.ctxVar`, `.app`'s fn hyp) are
not cell parents — they resolve through `Ctx.varOldest` / hyps.
-/

/-- Cell indices that must already carry a ranked neutral before this witness
can reconstruct as a neutral (intro forms listed for completeness only). -/
def Witness.cellParents : Witness → List Nat
  | .ctxVar _ => []
  | .fst pIdx | .snd pIdx => [pIdx]
  | .app _argHypIdx argIdx => [argIdx]
  | .appTy fnIdx argIdx => [fnIdx, argIdx]
  | .inl pIdx | .inr pIdx => [pIdx]
  | .unit | .eta => []

theorem Witness.cellParents_fst (p : Nat) :
    Witness.cellParents (.fst p) = [p] :=
  rfl

theorem Witness.cellParents_snd (p : Nat) :
    Witness.cellParents (.snd p) = [p] :=
  rfl

theorem Witness.cellParents_app (fnHyp argIdx : Nat) :
    Witness.cellParents (.app fnHyp argIdx) = [argIdx] :=
  rfl

theorem Witness.cellParents_appTy (fnIdx argIdx : Nat) :
    Witness.cellParents (.appTy fnIdx argIdx) = [fnIdx, argIdx] :=
  rfl

theorem Witness.cellParents_ctxVar (i : Nat) :
    Witness.cellParents (.ctxVar i) = [] :=
  rfl

theorem Witness.isNeutral_fst (p : Nat) : Witness.isNeutral (.fst p) = true :=
  rfl

theorem Witness.isNeutral_ctxVar (i : Nat) :
    Witness.isNeutral (.ctxVar i) = true :=
  rfl

/-! ## Local object measure (intro / `invOf` decrease) -/

def reconObjectSize {n : Nat} : Object n → Nat
  | .base _ | .never | .unit => 1
  | .prod A B | .coprod A B | .exp A B =>
      reconObjectSize A + reconObjectSize B + 1

theorem reconObjectSize_pos {n : Nat} (A : Object n) : 0 < reconObjectSize A := by
  cases A <;> simp [reconObjectSize]

theorem reconObjectSize_prod_left_lt {n : Nat} (L R : Object n) :
    reconObjectSize L < reconObjectSize (.prod L R) := by
  simp [reconObjectSize]; omega

theorem reconObjectSize_prod_right_lt {n : Nat} (L R : Object n) :
    reconObjectSize R < reconObjectSize (.prod L R) := by
  simp [reconObjectSize]; omega

theorem reconObjectSize_exp_ret_lt {n : Nat} (Arg Ret : Object n) :
    reconObjectSize Ret < reconObjectSize (.exp Arg Ret) := by
  simp [reconObjectSize]; omega

/-! ## Reconstruction phase (lex component) -/

inductive ReconPhase where
  | neuOf
  | witness
  | invOf
  deriving DecidableEq, Repr

def ReconPhase.toNat : ReconPhase → Nat
  | .neuOf => 2
  | .witness => 1
  | .invOf => 0

/-! ## Lex reconstruction measure

` (witnessRank, phase, reconObjectSize) ` — lexicographic on `Nat × Nat × Nat`.

* **`.fst` / `.snd`:** type size *increases* toward the product; **witness rank
  decreases** (`parents_lt`). Measure drops on the first component.
* **`.app` / `.appTy`:** parent `neuOf` uses rank decrease; intro `invOf`
  branches use `reconObjectSize` under phase `invOf`.
-/

def ReconMeasure : Type := Nat × Nat × Nat

def reconMeasure (witnessRank : Nat) (phase : ReconPhase) {n : Nat}
    (A : Object n) : ReconMeasure :=
  (witnessRank, phase.toNat, reconObjectSize A)

/-- Lex order on the triple (without relying on `LT` instances). -/
def ReconMeasure.lt : ReconMeasure → ReconMeasure → Prop
  | (r₁, p₁, s₁), (r₂, p₂, s₂) =>
      r₁ < r₂ ∨ (r₁ = r₂ ∧ (p₁ < p₂ ∨ (p₁ = p₂ ∧ s₁ < s₂)))

/-- Hard case demo: reconstructing `.fst` at child rank calls `neuOf(prod)` at
parent rank — first component decreases even though `reconObjectSize` rises. -/
theorem reconMeasure_fst_parent_lt (childRank parentRank : Nat)
    (h : parentRank < childRank) {n : Nat} (L R : Object n) :
    ReconMeasure.lt
      (reconMeasure parentRank .neuOf (.prod L R : Object n))
      (reconMeasure childRank .witness L) := by
  dsimp [ReconMeasure.lt, reconMeasure, ReconPhase.toNat]
  exact Or.inl h

/-- Intro case demo: `invOf` on a product component decreases object size at
equal witness rank and phase. -/
theorem reconMeasure_invOf_prod_left_lt (r : Nat) {n : Nat} (L R : Object n) :
    ReconMeasure.lt
      (reconMeasure r .invOf L)
      (reconMeasure r .invOf (.prod L R)) := by
  dsimp [ReconMeasure.lt, reconMeasure, ReconPhase.toNat]
  refine Or.inr ⟨rfl, Or.inr ⟨rfl, reconObjectSize_prod_left_lt L R⟩⟩

/-- `.appTy` parent `neuOf(exp)` at smaller rank. -/
theorem reconMeasure_appTy_fn_lt (childRank parentRank : Nat)
    (h : parentRank < childRank) {n : Nat} (Arg Ret : Object n) :
    ReconMeasure.lt
      (reconMeasure parentRank .neuOf (.exp Arg Ret : Object n))
      (reconMeasure childRank .witness Ret) := by
  dsimp [ReconMeasure.lt, reconMeasure, ReconPhase.toNat]
  exact Or.inl h

/-! ## Proof-only rank certificate -/

/-- Provenance slot: `true` = uses-new, `false` = old-only. -/
abbrev SlotNew : Type := Bool

def ReachCell.slotWitness (c : ReachCell) (b : SlotNew) : Option Witness :=
  if b then c.newWitness else c.oldWitness

/--
Rank of a stored **neutral** witness. Absent for empty slots and intro-only
witnesses (not reconstructible via `neuOfType` / schedule consistency).
-/
structure ReachRankCert {n : Nat} (σ : ReachState n) where
  rank : Nat → SlotNew → Option Nat
  rank_iff :
    ∀ (i : Nat) (b : SlotNew),
      (rank i b).isSome =
        match (σ.getCell i).slotWitness b with
        | some w => Witness.isNeutral w
        | none => false
  parents_lt :
    ∀ (i : Nat) (b : SlotNew) (w : Witness) (r : Nat),
      (σ.getCell i).slotWitness b = some w →
        Witness.isNeutral w = true →
          rank i b = some r →
            ∀ p ∈ Witness.cellParents w,
              ∃ (bP : SlotNew) (rP : Nat),
                rank p bP = some rP ∧ rP < r

/-- Preferred-slot rank (new neutral first, else old). -/
def ReachRankCert.rankOfPreferred {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) : Option Nat :=
  match (σ.getCell i).newWitness with
  | some w =>
      if Witness.isNeutral w then cert.rank i true else cert.rank i false
  | none => cert.rank i false

/-- Empty certificate when no witnesses are stored. -/
def ReachRankCert.empty {n : Nat} (σ : ReachState n)
    (h : ∀ i, (σ.getCell i).oldWitness = none ∧ (σ.getCell i).newWitness = none) :
    ReachRankCert σ where
  rank := fun _ _ => none
  rank_iff := by
    intro i b
    have ⟨ho, hn⟩ := h i
    cases b <;> simp [ReachCell.slotWitness, ho, hn]
  parents_lt := by
    intro i b w r hw _ hr
    have ⟨ho, hn⟩ := h i
    cases b <;> simp [ReachCell.slotWitness, ho, hn] at hw

/-! ## Certified reachability result -/

/--
Proof-only wrapper. `project` drops the certificate so schedules / compare /
fixed-point equality see only the computational `ReachState`.
-/
structure CertifiedReachResult (n : Nat) where
  state : ReachState n
  cert : ReachRankCert state

def CertifiedReachResult.project (c : CertifiedReachResult n) : ReachState n :=
  c.state

/--
Spike target for the full runner: certificate whose state equals
`runReachability Γ goal`. Not constructed in this spike (needs every rule).
-/
def CertifiedReachResult.soundFor (c : CertifiedReachResult n)
    (Γ : ReachCtx n) (goal : Object n) : Prop :=
  c.state = runReachability Γ goal

/-! ## Certificate extension -/

/-- Every cell parent of `w` already carries a ranked neutral in `cert`. -/
def ParentsCertified {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (w : Witness) : Prop :=
  ∀ p ∈ Witness.cellParents w,
    ∃ (bP : SlotNew) (rP : Nat), cert.rank p bP = some rP

theorem ParentsCertified_ctxVar {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) :
    ParentsCertified cert (.ctxVar i) := by
  intro p hp
  simp [Witness.cellParents] at hp

/-- Strict upper bound: max of `(slotRank + 1)` over both slots of every parent. -/
def ParentsCertified.freshRank {n : Nat} {σ : ReachState n}
    {cert : ReachRankCert σ} {w : Witness}
    (_h : ParentsCertified cert w) : Nat :=
  (Witness.cellParents w).foldl
    (fun acc p =>
      Nat.max acc
        (Nat.max
          (match cert.rank p false with | some r => r + 1 | none => 0)
          (match cert.rank p true with | some r => r + 1 | none => 0)))
    0

private def slotBound {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (p : Nat) : Nat :=
  Nat.max
    (match cert.rank p false with | some r => r + 1 | none => 0)
    (match cert.rank p true with | some r => r + 1 | none => 0)

theorem ParentsCertified.lt_freshRank {n : Nat} {σ : ReachState n}
    {cert : ReachRankCert σ} {w : Witness}
    (h : ParentsCertified cert w) :
    ∀ p ∈ Witness.cellParents w, ∀ (b : SlotNew) (rP : Nat),
      cert.rank p b = some rP → rP < h.freshRank := by
  intro p hp b rP hr
  have hbound : rP + 1 ≤ slotBound cert p := by
    cases b <;> simp [slotBound, hr]
  have hfold_ge :
      ∀ (ps : List Nat) (acc : Nat),
        acc ≤ ps.foldl (fun a q => Nat.max a (slotBound cert q)) acc := by
    intro ps; induction ps with
    | nil => intro acc; simp
    | cons q qs ih =>
        intro acc
        simp [List.foldl]
        exact le_trans (Nat.le_max_left acc _) (ih _)
  have go :
      ∀ (ps : List Nat) (acc : Nat), p ∈ ps →
        rP + 1 ≤
          ps.foldl (fun a q => Nat.max a (slotBound cert q)) acc := by
    intro ps; induction ps with
    | nil => intro _ hmem; cases hmem
    | cons q qs ih =>
        intro acc hmem
        cases hmem with
        | head =>
            simp [List.foldl]
            exact le_trans (le_trans hbound (Nat.le_max_right _ _))
              (hfold_ge qs _)
        | tail _ hmem' =>
            simp [List.foldl]
            exact ih (Nat.max acc (slotBound cert q)) hmem'
  have := go (Witness.cellParents w) 0 hp
  simp only [ParentsCertified.freshRank, slotBound] at this ⊢
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self rP) this

/-! ### Record / setCell helpers -/

theorem ReachCell.record_eq_of_slot_isSome (c : ReachCell) (b : SlotNew) (w : Witness)
    (h : (c.slotWitness b).isSome = true) :
    c.record b w = c := by
  cases b <;> cases ho : c.oldWitness <;> cases hn : c.newWitness <;>
    simp [ReachCell.slotWitness, ReachCell.record, ho, hn] at h ⊢

theorem ReachState.setCell_same {σ : ReachState n} {i : Nat}
    (h : i < σ.cells.size) :
    σ.setCell i (σ.getCell i) = σ := by
  apply ReachState.ext
  · simp
  · simp only [ReachState.setCell, dif_pos h, ReachState.getCell,
      Array.getElem?_eq_getElem h]
    exact Array.set_getElem_self h
  · simp [ReachState.setCell, dif_pos h]

theorem ReachCell.slotWitness_record_fresh (c : ReachCell) (b : SlotNew) (w : Witness)
    (h : c.slotWitness b = none) :
    (c.record b w).slotWitness b = some w := by
  cases b
  · have ho : c.oldWitness = none := by simpa [ReachCell.slotWitness] using h
    simp [ReachCell.slotWitness, ReachCell.record, ho]
  · have hn : c.newWitness = none := by simpa [ReachCell.slotWitness] using h
    simp [ReachCell.slotWitness, ReachCell.record, hn]

theorem ReachCell.slotWitness_record_other (c : ReachCell) (b b' : SlotNew) (w : Witness)
    (hne : b' ≠ b) (h : c.slotWitness b = none) :
    (c.record b w).slotWitness b' = c.slotWitness b' := by
  cases b <;> cases b' <;> simp_all [ReachCell.slotWitness, ReachCell.record]

theorem ReachCell.slotWitness_recordHyp (c : ReachCell) (b : SlotNew) (w : Witness)
    (b' : SlotNew) :
    (c.recordHyp b w).slotWitness b' = (c.record b w).slotWitness b' := by
  cases b' <;> simp [ReachCell.recordHyp, ReachCell.slotWitness]

def ReachRankCert.castState {n : Nat} {σ τ : ReachState n}
    (h : σ = τ) (cert : ReachRankCert σ) : ReachRankCert τ :=
  h ▸ cert

/-- Occupied slot: assign-once no-op; cast certificate along state equality. -/
def ReachRankCert.extendOccupied {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (hocc : (σ.getCell i).slotWitness b ≠ none)
    (hi : i < σ.cells.size) :
    ReachRankCert (σ.setCell i ((σ.getCell i).record b w)) :=
  have hsome : ((σ.getCell i).slotWitness b).isSome = true := by
    cases h : (σ.getCell i).slotWitness b
    · exact (hocc h).elim
    · rfl
  have heq :
      σ.setCell i ((σ.getCell i).record b w) = σ := by
    rw [ReachCell.record_eq_of_slot_isSome _ b w hsome]
    exact ReachState.setCell_same hi
  cert.castState heq.symm

/-- Fresh non-neutral (intro) slot: store witness, ranks unchanged. -/
def ReachRankCert.extendFreshIntro {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (hwNeu : Witness.isNeutral w = false)
    (hfresh : (σ.getCell i).slotWitness b = none)
    (hi : i < σ.cells.size) :
    ReachRankCert (σ.setCell i ((σ.getCell i).record b w)) where
  rank := cert.rank
  rank_iff := by
    intro j b'
    by_cases hj : j = i
    · have hji : i = j := hj.symm; subst hji
      rw [ReachState.getCell_setCell_self hi]
      by_cases hb : b' = b
      · have hbb : b = b' := hb.symm; subst hbb
        rw [ReachCell.slotWitness_record_fresh _ _ _ hfresh]
        simp [hwNeu]
        have := cert.rank_iff i b
        simpa [hfresh] using this.symm
      · rw [ReachCell.slotWitness_record_other _ b b' w hb hfresh]
        exact cert.rank_iff i b'
    · rw [ReachState.getCell_setCell_ne (Ne.symm hj)]
      exact cert.rank_iff j b'
  parents_lt := by
    intro j b' w' r hw' hwNeu' hr p hp
    have hslot : (σ.getCell j).slotWitness b' = some w' := by
      by_cases hj : j = i
      · have hji : i = j := hj.symm; subst hji
        have hw'' := hw'
        rw [ReachState.getCell_setCell_self hi] at hw''
        by_cases hb : b' = b
        · have hbb : b = b' := hb.symm; subst hbb
          rw [ReachCell.slotWitness_record_fresh _ _ _ hfresh] at hw''
          cases hw''
          simp [hwNeu] at hwNeu'
        · rwa [ReachCell.slotWitness_record_other _ b b' w hb hfresh] at hw''
      · rwa [ReachState.getCell_setCell_ne (Ne.symm hj)] at hw'
    exact cert.parents_lt j b' w' r hslot hwNeu' hr p hp

/--
Fresh neutral slot: assign `freshRank` strictly above every certified parent.
Requires `ParentsCertified` — missing parents are an operational bug, not patched.
-/
def ReachRankCert.extendFreshNeutral {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (hwNeu : Witness.isNeutral w = true)
    (hfresh : (σ.getCell i).slotWitness b = none)
    (hp : ParentsCertified cert w)
    (hi : i < σ.cells.size) :
    ReachRankCert (σ.setCell i ((σ.getCell i).record b w)) where
  rank := fun j b' =>
    if j = i ∧ b' = b then some hp.freshRank else cert.rank j b'
  rank_iff := by
    intro j b'
    by_cases hj : j = i
    · have hji : i = j := hj.symm; subst hji
      by_cases hb : b' = b
      · have hbb : b = b' := hb.symm; subst hbb
        simp [ReachState.getCell_setCell_self hi,
          ReachCell.slotWitness_record_fresh _ _ _ hfresh, hwNeu]
      · have hne : ¬(i = i ∧ b' = b) := fun h => hb h.2
        rw [if_neg hne]
        rw [ReachState.getCell_setCell_self hi,
          ReachCell.slotWitness_record_other _ b b' w hb hfresh]
        exact cert.rank_iff i b'
    · simp [hj]
      rw [ReachState.getCell_setCell_ne (Ne.symm hj)]
      exact cert.rank_iff j b'
  parents_lt := by
    intro j b' w' r hw' hwNeu' hr p hpMem
    by_cases hnew : j = i ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := show i = j ∧ b = b' from ⟨hnew.1.symm, hnew.2.symm⟩
      have : w' = w := by
        have hw'' := hw'
        rw [ReachState.getCell_setCell_self hi,
          ReachCell.slotWitness_record_fresh _ _ _ hfresh] at hw''
        injection hw'' with heq
        exact heq.symm
      subst this
      have : r = hp.freshRank := by
        simp at hr
        exact hr.symm
      subst this
      obtain ⟨bP, rP, hrP⟩ := hp p hpMem
      have hne : ¬(p = i ∧ bP = b) := by
        intro h
        obtain ⟨rfl, rfl⟩ := show i = p ∧ b = bP from ⟨h.1.symm, h.2.symm⟩
        have hiff := cert.rank_iff i b
        rw [hfresh, hrP] at hiff
        cases hiff
      refine ⟨bP, rP, ?_, ParentsCertified.lt_freshRank hp p hpMem bP rP hrP⟩
      rw [if_neg hne]; exact hrP
    · have hneIF : ¬(j = i ∧ b' = b) := hnew
      rw [if_neg hneIF] at hr
      have hslot : (σ.getCell j).slotWitness b' = some w' := by
        by_cases hj : j = i
        · have hji : i = j := hj.symm; subst hji
          have hb : b' ≠ b := fun he => hnew ⟨rfl, he⟩
          have hw'' := hw'
          rw [ReachState.getCell_setCell_self hi,
            ReachCell.slotWitness_record_other _ b b' w hb hfresh] at hw''
          exact hw''
        · rwa [ReachState.getCell_setCell_ne (Ne.symm hj)] at hw'
      obtain ⟨bP, rP, hrP, hlt⟩ :=
        cert.parents_lt j b' w' r hslot hwNeu' hr p hpMem
      refine ⟨bP, rP, ?_, hlt⟩
      have hne : ¬(p = i ∧ bP = b) := by
        intro h
        obtain ⟨rfl, rfl⟩ := show i = p ∧ b = bP from ⟨h.1.symm, h.2.symm⟩
        have hiff := cert.rank_iff i b
        rw [hfresh, hrP] at hiff
        cases hiff
      rw [if_neg hne]; exact hrP

/-- Unified extend on `setCell ∘ record`. -/
def ReachRankCert.extend {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (hi : i < σ.cells.size)
    (hpar : Witness.isNeutral w = true → ParentsCertified cert w) :
    ReachRankCert (σ.setCell i ((σ.getCell i).record b w)) :=
  match hslot : (σ.getCell i).slotWitness b with
  | some _ =>
      ReachRankCert.extendOccupied cert i b w (by simp [hslot]) hi
  | none =>
      if hw : Witness.isNeutral w = true then
        ReachRankCert.extendFreshNeutral cert i b w hw hslot (hpar hw) hi
      else
        ReachRankCert.extendFreshIntro cert i b w
          (by cases h : Witness.isNeutral w <;> simp_all) hslot hi

/-- Lift certificate across `markInconsistentIf` (cells unchanged). -/
def ReachRankCert.ofMarkInconsistentIf {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (A : Object n) :
    ReachRankCert (σ.markInconsistentIf A) where
  rank := cert.rank
  rank_iff := by
    intro i b
    rw [ReachState.getCell_markInconsistentIf]
    exact cert.rank_iff i b
  parents_lt := by
    intro i b w r hw hwNeu hr p hp
    have hw' : (σ.getCell i).slotWitness b = some w := by
      rwa [ReachState.getCell_markInconsistentIf] at hw
    exact cert.parents_lt i b w r hw' hwNeu hr p hp

/-- Certificate depends only on witness slots, not `retrievable`. -/
def ReachRankCert.ofSameSlots {n : Nat} {σ τ : ReachState n}
    (cert : ReachRankCert σ)
    (h : ∀ i b, (τ.getCell i).slotWitness b = (σ.getCell i).slotWitness b) :
    ReachRankCert τ where
  rank := cert.rank
  rank_iff := by
    intro i b
    rw [h i b]
    exact cert.rank_iff i b
  parents_lt := by
    intro i b w r hw hwNeu hr p hp
    have hw' : (σ.getCell i).slotWitness b = some w := by
      simpa [h i b] using hw
    exact cert.parents_lt i b w r hw' hwNeu hr p hp

theorem ReachRankCert.castState_rank {n : Nat} {σ τ : ReachState n}
    (h : σ = τ) (cert : ReachRankCert σ) :
    (cert.castState h).rank = cert.rank := by
  cases h; rfl

theorem ReachRankCert.extend_preserves_rank {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (hi : i < σ.cells.size)
    (hpar : Witness.isNeutral w = true → ParentsCertified cert w)
    {j : Nat} {b' : SlotNew} {r : Nat}
    (hr : cert.rank j b' = some r) :
    (ReachRankCert.extend cert i b w hi hpar).rank j b' = some r := by
  unfold ReachRankCert.extend
  split
  · rename_i _ hslot
    simp only [ReachRankCert.extendOccupied]
    rw [ReachRankCert.castState_rank]
    exact hr
  · rename_i hfresh
    split
    · simp only [ReachRankCert.extendFreshNeutral]
      have hne : ¬(j = i ∧ b' = b) := by
        intro h
        obtain ⟨rfl, rfl⟩ := show i = j ∧ b = b' from ⟨h.1.symm, h.2.symm⟩
        have hiff := cert.rank_iff i b
        rw [hfresh, hr] at hiff
        cases hiff
      rw [if_neg hne]; exact hr
    · simp only [ReachRankCert.extendFreshIntro, hr]

theorem ParentsCertified.of_extend {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (hi : i < σ.cells.size)
    (hpar : Witness.isNeutral w = true → ParentsCertified cert w)
    (w' : Witness) (hp : ParentsCertified cert w') :
    ParentsCertified (ReachRankCert.extend cert i b w hi hpar) w' := by
  intro p hpMem
  obtain ⟨bP, rP, hrP⟩ := hp p hpMem
  exact ⟨bP, rP, ReachRankCert.extend_preserves_rank cert i b w hi hpar hrP⟩

theorem ParentsCertified.of_markInconsistentIf {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (A : Object n) (w : Witness)
    (hp : ParentsCertified cert w) :
    ParentsCertified (cert.ofMarkInconsistentIf A) w := by
  intro p hpMem
  obtain ⟨bP, rP, hrP⟩ := hp p hpMem
  exact ⟨bP, rP, hrP⟩

/-! ### Certified operations -/

/-- Certified discover. Neutrals require `ParentsCertified` via `h`. -/
def certifiedDiscover {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (i : Nat) (b : SlotNew) (w : Witness)
    (h : Witness.isNeutral w = true → ParentsCertified cert w) :
    CertifiedReachResult n :=
  match σ.typeAt i with
  | none => ⟨σ, cert⟩
  | some A =>
      if hi : i < σ.cells.size then
        let σ₁ := σ.setCell i ((σ.getCell i).record b w)
        let c₁ := ReachRankCert.extend cert i b w hi h
        ⟨σ₁.markInconsistentIf A, c₁.ofMarkInconsistentIf A⟩
      else
        ⟨σ.markInconsistentIf A, cert.ofMarkInconsistentIf A⟩

theorem certifiedDiscover_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (h : Witness.isNeutral w = true → ParentsCertified cert w) :
    (certifiedDiscover σ cert i b w h).project = σ.discover i b w := by
  dsimp only [certifiedDiscover, ReachState.discover, CertifiedReachResult.project]
  cases σ.typeAt i with
  | none => rfl
  | some A =>
      by_cases hi : i < σ.cells.size
      · simp [hi]
      · simp [hi, ReachState.setCell]

theorem ParentsCertified.of_certifiedDiscover {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (h : Witness.isNeutral w = true → ParentsCertified cert w)
    (w' : Witness) (hp : ParentsCertified cert w') :
    ParentsCertified (certifiedDiscover σ cert i b w h).cert w' := by
  simp only [certifiedDiscover]
  cases σ.typeAt i with
  | none => exact hp
  | some A =>
      change ParentsCertified
        ((if hi : i < σ.cells.size then
          ({ state := (σ.setCell i ((σ.getCell i).record b w)).markInconsistentIf A,
             cert := (ReachRankCert.extend cert i b w hi h).ofMarkInconsistentIf A } :
            CertifiedReachResult n)
        else
          ({ state := σ.markInconsistentIf A,
             cert := cert.ofMarkInconsistentIf A } :
            CertifiedReachResult n)).cert) w'
      by_cases hi : i < σ.cells.size
      · rw [dif_pos hi]
        exact ParentsCertified.of_markInconsistentIf
          (ReachRankCert.extend cert i b w hi h) A w'
          (ParentsCertified.of_extend cert i b w hi h w' hp)
      · rw [dif_neg hi]
        exact ParentsCertified.of_markInconsistentIf cert A w' hp

/-- Dual-fire composition. -/
def certifiedDiscoverDual {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (i : Nat) (oldOk newOk : Bool) (w : Witness)
    (h : Witness.isNeutral w = true → ParentsCertified cert w) :
    CertifiedReachResult n :=
  match oldOk, newOk with
  | true, true =>
      let c₁ := certifiedDiscover σ cert i false w h
      certifiedDiscover c₁.state c₁.cert i true w (fun hwNeu =>
        ParentsCertified.of_certifiedDiscover σ cert i false w h w (h hwNeu))
  | true, false =>
      certifiedDiscover σ cert i false w h
  | false, true =>
      certifiedDiscover σ cert i true w h
  | false, false =>
      ⟨σ, cert⟩

theorem certifiedDiscoverDual_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (oldOk newOk : Bool) (w : Witness)
    (h : Witness.isNeutral w = true → ParentsCertified cert w) :
    (certifiedDiscoverDual σ cert i oldOk newOk w h).project =
      σ.discoverDual i oldOk newOk w := by
  cases oldOk <;> cases newOk
  · rfl
  · exact certifiedDiscover_project σ cert i true w h
  · exact certifiedDiscover_project σ cert i false w h
  · simp only [certifiedDiscoverDual, ReachState.discoverDual,
      CertifiedReachResult.project]
    have h₁ := certifiedDiscover_project σ cert i false w h
    have h₂ := certifiedDiscover_project
      (certifiedDiscover σ cert i false w h).state
      (certifiedDiscover σ cert i false w h).cert i true w
      (fun hwNeu =>
        ParentsCertified.of_certifiedDiscover σ cert i false w h w (h hwNeu))
    simp only [CertifiedReachResult.project] at h₁ h₂
    rw [h₂, h₁]
    simp

/-- Certified markHyp via `record` ranks + `ofSameSlots` for `recordHyp`. -/
def certifiedMarkHyp {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) (hypIdx : Nat) :
    CertifiedReachResult n :=
  match hA : Γ.hyps[hypIdx]? with
  | none => ⟨σ, cert⟩
  | some A =>
      match hiIdx : σ.findTypeIdx A with
      | none => ⟨σ, cert⟩
      | some i =>
          if hi : i < σ.cells.size then
            let b := Γ.isNew hypIdx
            let w : Witness := .ctxVar hypIdx
            let hpar : Witness.isNeutral w = true → ParentsCertified cert w :=
              fun _ => ParentsCertified_ctxVar cert hypIdx
            let σRec := σ.setCell i ((σ.getCell i).record b w)
            let σHyp := σ.setCell i ((σ.getCell i).recordHyp b w)
            let certRec := ReachRankCert.extend cert i b w hi hpar
            have hslots :
                ∀ j b', (σHyp.getCell j).slotWitness b' =
                  (σRec.getCell j).slotWitness b' := by
              intro j b'
              by_cases hj : j = i
              · subst hj
                rw [ReachState.getCell_setCell_self hi,
                  ReachState.getCell_setCell_self hi]
                exact ReachCell.slotWitness_recordHyp _ b w b'
              · rw [ReachState.getCell_setCell_ne (Ne.symm hj),
                  ReachState.getCell_setCell_ne (Ne.symm hj)]
            ⟨σHyp.markInconsistentIf A,
              (certRec.ofSameSlots hslots).ofMarkInconsistentIf A⟩
          else
            ⟨σ.markInconsistentIf A, cert.ofMarkInconsistentIf A⟩

theorem certifiedMarkHyp_project {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) (hypIdx : Nat) :
    (certifiedMarkHyp Γ σ cert hypIdx).project = σ.markHyp Γ hypIdx := by
  dsimp only [certifiedMarkHyp, ReachState.markHyp, CertifiedReachResult.project]
  split
  · next hA => simp [hA]
  · next A hA =>
      split
      · next hiIdx => simp [hA, hiIdx]
      · next i hiIdx =>
          split
          · next hi => simp [hA, hiIdx]
          · next hi =>
              simp [hA, hiIdx, ReachState.setCell, dif_neg hi]

/-! ## Status

**Landed without `sorry`:** assign-once, parents, lex demos, `ParentsCertified` /
`freshRank` / `lt_freshRank`, generic `extend` (occupied / fresh intro / fresh
neutral), `ofSameSlots`, rank persistence + parent mono under extend,
`certifiedDiscover` / `certifiedDiscoverDual` / `certifiedMarkHyp` with
computational projections.

**Open:** sweep fold → `certifiedRunReachability`; WF reconstruction →
`ReconstructTotalityPackage`.

**Stop condition:** never invent ranks for missing parents — require
`ParentsCertified` before fresh neutral extend.
-/

/-! ## Totality scope (neutral only)

`ReconstructWitnessTotal` / `StoredWitnessReconstructs` already restrict to
`Witness.isNeutral`. Intro-only `.unit` / `.inl` / `.inr` / `.eta` must **not**
be over-quantified into `neuOfType` success — they justify invertible arguments
only (`Witness.isNeutral = false`).
-/

theorem Witness.not_neutral_unit : Witness.isNeutral .unit = false := rfl
theorem Witness.not_neutral_eta : Witness.isNeutral .eta = false := rfl
theorem Witness.not_neutral_inl (i : Nat) : Witness.isNeutral (.inl i) = false := rfl
theorem Witness.not_neutral_inr (i : Nat) : Witness.isNeutral (.inr i) = false := rfl

/-! ## Inconsistent completed state → reconstructible `.never` -/

theorem InconsistentNeverTotal_of_ranked_package {sig : Signature}
    (h : ReconstructTotalityPackage sig) : InconsistentNeverTotal sig :=
  h.2.2

/-! ## Migration-cost comparison (spike conclusion)

| Design | Pros | Cons | Verdict |
|---|---|---|---|
| **A. Proof-only `ReachRankCert` / certified runner** | No contamination of `ReachCell` equality, schedule identity, or observation identity; `project` = existing `runReachability` state | Must thread certificates through every `markHyp`/`discover` rule; `setCell` transport lemmas are sticky | **Preferred** if maintainable |
| **B. Runtime `discoverGen` on `ReachCell`/`Witness`** | Local measure at each record site; easy WF | Must exclude gen from semantic equality, canonical scheduling, `PairEntry`/`Witness` identity; risks leaking into compare | Use **only if A is unmaintainable** |
| **C. Structural derivation trees** | Intrinsic WF; no parallel rank map | Heavier than current parent-pointer witnesses; changes reconstruction API | Possible long-term; not needed if A works |

**Recommendation:** pursue **A**. Assign-once makes rank stable. Parent relation
is small and closed. Lex measure handles the `.fst`/`.snd` size increase.

Dependency once A lands:
`certified reachability → ranked witness graph → reconstruction totality →
retained schedule adapter → certified producer → EncodeTotal`.
-/

end Equality
end Gimbal
