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

/--
Proof-only reconstruction dependencies of a witness shape (index fields + the
cells `invOf` / `neuOf` must already have ranked).

This is **not** “immediate calls in `reconstructGo` only”:
* `.app` / `.appTy` recurse through `invOf Arg`, which may η-split a product and
  eventually `neuOf` component neutrals — so the **argument cell** is a parent.
* `.eta` carries no indices on `Witness`; product/function η parent lists are
  supplied **at the certified record site** (both components / return type) and
  stored in `ReachRankCert.deps`, not on the computational witness.

`cellParents` remains the static default derived from witness indices; richer
rule-specific lists override it when extending the certificate.
-/
def Witness.cellParents : Witness → List Nat
  | .ctxVar _ | .fstHyp _ | .sndHyp _ => []
  | .fstType pIdx | .sndType pIdx => [pIdx]
  | .app _argHypIdx argIdx => [argIdx]
  | .appTy fnIdx argIdx => [fnIdx, argIdx]
  | .inl pIdx | .inr pIdx => [pIdx]
  | .unit | .eta => []

theorem Witness.cellParents_fstHyp (i : Nat) :
    Witness.cellParents (.fstHyp i) = [] :=
  rfl

theorem Witness.cellParents_sndHyp (i : Nat) :
    Witness.cellParents (.sndHyp i) = [] :=
  rfl

theorem Witness.cellParents_fstType (p : Nat) :
    Witness.cellParents (.fstType p) = [p] :=
  rfl

theorem Witness.cellParents_sndType (p : Nat) :
    Witness.cellParents (.sndType p) = [p] :=
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

theorem Witness.isNeutral_fstHyp (i : Nat) :
    Witness.isNeutral (.fstHyp i) = true :=
  rfl

theorem Witness.isNeutral_fstType (p : Nat) :
    Witness.isNeutral (.fstType p) = true :=
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

* **`.fstType` / `.sndType`:** type size *increases* toward the product; **witness
  rank decreases** (`parents_lt`). Measure drops on the first component.
  Hypothesis projections (`.fstHyp` / `.sndHyp`) have no cell parents.
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

/-- Hard case demo: reconstructing `.fstType` at child rank calls `neuOf(prod)` at
parent rank — first component decreases even though `reconObjectSize` rises. -/
theorem reconMeasure_fstType_parent_lt (childRank parentRank : Nat)
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

/--
η-argument application path (strict decrease at each edge), assuming ranks
satisfy `r_comp < r_arg ≤ r_app` (argument cell ranked from its η/components;
application ranked above the argument):

* `witness(app)` → `invOf(Arg)` — phase drop at fixed app rank;
* `invOf(prod)` → `invOf(component)` — object-size drop;
* `invOf(component)` → `neuOf(component)` — rank drop to the component neutral.
-/
theorem reconMeasure_app_to_invOf_lt (rApp : Nat) {n : Nat} (Arg Ret : Object n) :
    ReconMeasure.lt
      (reconMeasure rApp .invOf Arg)
      (reconMeasure rApp .witness Ret) := by
  dsimp [ReconMeasure.lt, reconMeasure, ReconPhase.toNat]
  exact Or.inr ⟨rfl, Or.inl (by decide : (0 : Nat) < 1)⟩

theorem reconMeasure_invOf_to_neuOf_component_lt
    (rApp rComp : Nat) (h : rComp < rApp) {n : Nat} (X : Object n) :
    ReconMeasure.lt
      (reconMeasure rComp .neuOf X)
      (reconMeasure rApp .invOf X) := by
  dsimp [ReconMeasure.lt, reconMeasure, ReconPhase.toNat]
  exact Or.inl h

/-- Composite: app witness → invOf product → invOf component → neuOf component. -/
theorem reconMeasure_app_invOf_neuOf_chain
    (rApp rArg rComp : Nat)
    (hArg : rArg ≤ rApp) (hComp : rComp < rArg)
    {n : Nat} (X Y R : Object n) :
    ReconMeasure.lt
      (reconMeasure rApp .invOf (.prod X Y))
      (reconMeasure rApp .witness R) ∧
    ReconMeasure.lt
      (reconMeasure rApp .invOf X)
      (reconMeasure rApp .invOf (.prod X Y)) ∧
    ReconMeasure.lt
      (reconMeasure rComp .neuOf X)
      (reconMeasure rApp .invOf X) := by
  refine ⟨reconMeasure_app_to_invOf_lt rApp (.prod X Y) R,
    reconMeasure_invOf_prod_left_lt rApp X Y, ?_⟩
  exact reconMeasure_invOf_to_neuOf_component_lt rApp rComp
    (Nat.lt_of_lt_of_le hComp hArg) X

/-- `.appTy` parent `neuOf(exp)` at smaller rank. -/
theorem reconMeasure_appTy_fn_lt (childRank parentRank : Nat)
    (h : parentRank < childRank) {n : Nat} (Arg Ret : Object n) :
    ReconMeasure.lt
      (reconMeasure parentRank .neuOf (.exp Arg Ret : Object n))
      (reconMeasure childRank .witness Ret) := by
  dsimp [ReconMeasure.lt, reconMeasure, ReconPhase.toNat]
  exact Or.inl h

/-- `.appTy` also depends on the argument cell (same invOf path as `.app`). -/
theorem reconMeasure_appTy_arg_invOf_lt (rApp : Nat) {n : Nat}
    (Arg Ret : Object n) :
    ReconMeasure.lt
      (reconMeasure rApp .invOf Arg)
      (reconMeasure rApp .witness Ret) :=
  reconMeasure_app_to_invOf_lt rApp Arg Ret

/-! ## Proof-only rank certificate -/

/-- Provenance slot: `true` = uses-new, `false` = old-only. -/
abbrev SlotNew : Type := Bool

def ReachCell.slotWitness (c : ReachCell) (b : SlotNew) : Option Witness :=
  if b then c.newWitness else c.oldWitness

/--
Rank of every stored deducibility witness (neutral **and** intro).
Proof-only `deps` lists the cells that must already be ranked; these may be
richer than `Witness.cellParents` (e.g. product η → both components).
-/
structure ReachRankCert {n : Nat} (σ : ReachState n) where
  rank : Nat → SlotNew → Option Nat
  deps : Nat → SlotNew → List Nat
  rank_iff :
    ∀ (i : Nat) (b : SlotNew),
      (rank i b).isSome = ((σ.getCell i).slotWitness b).isSome
  deps_none :
    ∀ (i : Nat) (b : SlotNew),
      (σ.getCell i).slotWitness b = none → deps i b = []
  parents_lt :
    ∀ (i : Nat) (b : SlotNew) (r : Nat),
      rank i b = some r →
        ∀ p ∈ deps i b,
          ∃ (bP : SlotNew) (rP : Nat),
            rank p bP = some rP ∧ rP < r

/-- Preferred-slot rank via `neutralWitness` (new neutral, else old neutral). -/
def ReachRankCert.rankOfPreferred {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) : Option Nat :=
  match (σ.getCell i).neutralWitness with
  | some w =>
      if (σ.getCell i).newNeutral then cert.rank i true else cert.rank i false
  | none => none

/-- Empty certificate when no witnesses are stored. -/
def ReachRankCert.empty {n : Nat} (σ : ReachState n)
    (h : ∀ i, (σ.getCell i).oldWitness = none ∧ (σ.getCell i).newWitness = none) :
    ReachRankCert σ where
  rank := fun _ _ => none
  deps := fun _ _ => []
  rank_iff := by
    intro i b
    have ⟨ho, hn⟩ := h i
    cases b <;> simp [ReachCell.slotWitness, ho, hn]
  deps_none := fun _ _ _ => rfl
  parents_lt := by
    intro i b r hr
    have ⟨ho, hn⟩ := h i
    cases b <;> simp [hr] at *

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

/-- Every listed cell already carries some ranked witness in `cert`. -/
def RankedParents {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (ps : List Nat) : Prop :=
  ∀ p ∈ ps, ∃ (bP : SlotNew) (rP : Nat), cert.rank p bP = some rP

/-- Default parents from the witness's static index fields. -/
def ParentsCertified {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (w : Witness) : Prop :=
  RankedParents cert (Witness.cellParents w)

theorem ParentsCertified_ctxVar {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) :
    ParentsCertified cert (.ctxVar i) := by
  intro p hp
  simp [Witness.cellParents] at hp

theorem ParentsCertified_fstHyp {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) :
    ParentsCertified cert (.fstHyp i) := by
  intro p hp; simp [Witness.cellParents] at hp

theorem ParentsCertified_sndHyp {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) :
    ParentsCertified cert (.sndHyp i) := by
  intro p hp; simp [Witness.cellParents] at hp

theorem ParentsCertified_app {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (fnHyp argIdx : Nat)
    (hArg : ∃ (b : SlotNew) (r : Nat), cert.rank argIdx b = some r) :
    ParentsCertified cert (.app fnHyp argIdx) := by
  intro p hp
  simp only [Witness.cellParents, List.mem_singleton] at hp
  cases hp
  exact hArg

theorem ParentsCertified_appTy {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (fnIdx argIdx : Nat)
    (hFn : ∃ (b : SlotNew) (r : Nat), cert.rank fnIdx b = some r)
    (hArg : ∃ (b : SlotNew) (r : Nat), cert.rank argIdx b = some r) :
    ParentsCertified cert (.appTy fnIdx argIdx) := by
  intro p hp
  have : p = fnIdx ∨ p = argIdx := by simpa [Witness.cellParents] using hp
  rcases this with h | h
  · subst h; exact hFn
  · subst h; exact hArg

theorem RankedParents_nil {n : Nat} {σ : ReachState n} (cert : ReachRankCert σ) :
    RankedParents cert [] := by
  intro p hp; cases hp

/-- A cell with a neutral provenance slot already has a ranked witness. -/
theorem ReachRankCert.ranked_of_neutral {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (ti : Nat)
    (hNeu : (σ.getCell ti).oldNeutral = true ∨ (σ.getCell ti).newNeutral = true) :
    ∃ (b : SlotNew) (r : Nat), cert.rank ti b = some r := by
  cases hNeu with
  | inl ho =>
    cases hw : (σ.getCell ti).oldWitness with
    | none => simp [ReachCell.oldNeutral, hw] at ho
    | some w =>
      have hrs : (cert.rank ti false).isSome = true := by
        have hslot : ((σ.getCell ti).slotWitness false).isSome = true := by
          simp [ReachCell.slotWitness, hw]
        simpa [hslot] using (cert.rank_iff ti false).symm
      cases hr : cert.rank ti false with
      | none => simp [hr] at hrs
      | some r => exact ⟨false, r, hr⟩
  | inr hn =>
    cases hw : (σ.getCell ti).newWitness with
    | none => simp [ReachCell.newNeutral, hw] at hn
    | some w =>
      have hrs : (cert.rank ti true).isSome = true := by
        have hslot : ((σ.getCell ti).slotWitness true).isSome = true := by
          simp [ReachCell.slotWitness, hw]
        simpa [hslot] using (cert.rank_iff ti true).symm
      cases hr : cert.rank ti true with
      | none => simp [hr] at hrs
      | some r => exact ⟨true, r, hr⟩

/-- A cell with a neutral provenance slot is a certified parent of `fstType`/`sndType`. -/
theorem ParentsCertified_fstType_of_neutral {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (ti : Nat)
    (hNeu : (σ.getCell ti).oldNeutral = true ∨ (σ.getCell ti).newNeutral = true) :
    ParentsCertified cert (.fstType ti) := by
  intro p hp
  simp only [Witness.cellParents, List.mem_singleton] at hp
  cases hp
  exact cert.ranked_of_neutral ti hNeu

theorem ParentsCertified_sndType_of_neutral {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (ti : Nat)
    (hNeu : (σ.getCell ti).oldNeutral = true ∨ (σ.getCell ti).newNeutral = true) :
    ParentsCertified cert (.sndType ti) := by
  intro p hp
  simp only [Witness.cellParents, List.mem_singleton] at hp
  cases hp
  exact cert.ranked_of_neutral ti hNeu

/-- Strict upper bound: max of `(slotRank + 1)` over both slots of every parent. -/
def RankedParents.freshRank {n : Nat} {σ : ReachState n}
    {cert : ReachRankCert σ} {ps : List Nat}
    (_h : RankedParents cert ps) : Nat :=
  ps.foldl
    (fun acc p =>
      Nat.max acc
        (Nat.max
          (match cert.rank p false with | some r => r + 1 | none => 0)
          (match cert.rank p true with | some r => r + 1 | none => 0)))
    0

/-- Fresh rank from a witness's static `cellParents`. -/
def ParentsCertified.freshRank {n : Nat} {σ : ReachState n}
    {cert : ReachRankCert σ} {w : Witness}
    (h : ParentsCertified cert w) : Nat :=
  RankedParents.freshRank (ps := Witness.cellParents w) h

private def slotBound {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (p : Nat) : Nat :=
  Nat.max
    (match cert.rank p false with | some r => r + 1 | none => 0)
    (match cert.rank p true with | some r => r + 1 | none => 0)

theorem RankedParents.lt_freshRank {n : Nat} {σ : ReachState n}
    {cert : ReachRankCert σ} {ps : List Nat}
    (h : RankedParents cert ps) :
    ∀ p ∈ ps, ∀ (b : SlotNew) (rP : Nat),
      cert.rank p b = some rP → rP < h.freshRank := by
  intro p hp b rP hr
  have hbound : rP + 1 ≤ slotBound cert p := by
    cases b <;> simp [slotBound, hr]
  have hfold_ge :
      ∀ (qs : List Nat) (acc : Nat),
        acc ≤ qs.foldl (fun a q => Nat.max a (slotBound cert q)) acc := by
    intro qs; induction qs with
    | nil => intro acc; simp
    | cons q qs ih =>
        intro acc
        simp [List.foldl]
        exact le_trans (Nat.le_max_left acc _) (ih _)
  have go :
      ∀ (qs : List Nat) (acc : Nat), p ∈ qs →
        rP + 1 ≤
          qs.foldl (fun a q => Nat.max a (slotBound cert q)) acc := by
    intro qs; induction qs with
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
  have := go ps 0 hp
  simp only [RankedParents.freshRank, slotBound] at this ⊢
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self rP) this

theorem ParentsCertified.lt_freshRank {n : Nat} {σ : ReachState n}
    {cert : ReachRankCert σ} {w : Witness}
    (h : ParentsCertified cert w) :
    ∀ p ∈ Witness.cellParents w, ∀ (b : SlotNew) (rP : Nat),
      cert.rank p b = some rP → rP < h.freshRank :=
  RankedParents.lt_freshRank h

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

/--
Fresh slot (intro or neutral): assign `freshRank` above every listed parent and
store the proof-only `deps` list. Missing parents are an operational bug.
-/
def ReachRankCert.extendFresh {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat)
    (hfresh : (σ.getCell i).slotWitness b = none)
    (hp : RankedParents cert deps)
    (hi : i < σ.cells.size) :
    ReachRankCert (σ.setCell i ((σ.getCell i).record b w)) where
  rank := fun j b' =>
    if j = i ∧ b' = b then some hp.freshRank else cert.rank j b'
  deps := fun j b' =>
    if j = i ∧ b' = b then deps else cert.deps j b'
  rank_iff := by
    intro j b'
    by_cases hj : j = i
    · have hji : i = j := hj.symm; subst hji
      by_cases hb : b' = b
      · have hbb : b = b' := hb.symm; subst hbb
        simp [ReachState.getCell_setCell_self hi,
          ReachCell.slotWitness_record_fresh _ _ _ hfresh]
      · have hne : ¬(i = i ∧ b' = b) := fun h => hb h.2
        rw [if_neg hne]
        rw [ReachState.getCell_setCell_self hi,
          ReachCell.slotWitness_record_other _ b b' w hb hfresh]
        exact cert.rank_iff i b'
    · simp [hj]
      rw [ReachState.getCell_setCell_ne (Ne.symm hj)]
      exact cert.rank_iff j b'
  deps_none := by
    intro j b' hnone
    by_cases hj : j = i
    · have hji : i = j := hj.symm; subst hji
      by_cases hb : b' = b
      · have hbb : b = b' := hb.symm; subst hbb
        rw [ReachState.getCell_setCell_self hi,
          ReachCell.slotWitness_record_fresh _ _ _ hfresh] at hnone
        cases hnone
      · have hne : ¬(i = i ∧ b' = b) := fun h => hb h.2
        rw [if_neg hne]
        have hslot := hnone
        rw [ReachState.getCell_setCell_self hi,
          ReachCell.slotWitness_record_other _ b b' w hb hfresh] at hslot
        exact cert.deps_none i b' hslot
    · simp [hj]
      have hslot := hnone
      rw [ReachState.getCell_setCell_ne (Ne.symm hj)] at hslot
      exact cert.deps_none j b' hslot
  parents_lt := by
    intro j b' r hr p hpMem
    by_cases hnew : j = i ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := show i = j ∧ b = b' from ⟨hnew.1.symm, hnew.2.symm⟩
      have : r = hp.freshRank := by
        simp at hr
        exact hr.symm
      subst this
      have hpMem' : p ∈ deps := by
        simpa using hpMem
      obtain ⟨bP, rP, hrP⟩ := hp p hpMem'
      have hne : ¬(p = i ∧ bP = b) := by
        intro h
        obtain ⟨rfl, rfl⟩ := show i = p ∧ b = bP from ⟨h.1.symm, h.2.symm⟩
        have hiff := cert.rank_iff i b
        rw [hfresh, hrP] at hiff
        cases hiff
      refine ⟨bP, rP, ?_, RankedParents.lt_freshRank hp p hpMem' bP rP hrP⟩
      rw [if_neg hne]; exact hrP
    · have hneIF : ¬(j = i ∧ b' = b) := hnew
      rw [if_neg hneIF] at hr hpMem
      obtain ⟨bP, rP, hrP, hlt⟩ := cert.parents_lt j b' r hr p hpMem
      refine ⟨bP, rP, ?_, hlt⟩
      have hne : ¬(p = i ∧ bP = b) := by
        intro h
        obtain ⟨rfl, rfl⟩ := show i = p ∧ b = bP from ⟨h.1.symm, h.2.symm⟩
        have hiff := cert.rank_iff i b
        rw [hfresh, hrP] at hiff
        cases hiff
      rw [if_neg hne]; exact hrP

/-- Unified extend: occupied is a no-op; fresh records `deps` and a new rank. -/
def ReachRankCert.extend {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat)
    (hi : i < σ.cells.size)
    (hpar : RankedParents cert deps) :
    ReachRankCert (σ.setCell i ((σ.getCell i).record b w)) :=
  match hslot : (σ.getCell i).slotWitness b with
  | some _ =>
      ReachRankCert.extendOccupied cert i b w (by simp [hslot]) hi
  | none =>
      ReachRankCert.extendFresh cert i b w deps hslot hpar hi

/-- Lift certificate across `markInconsistentIf` (cells unchanged). -/
def ReachRankCert.ofMarkInconsistentIf {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (A : Object n) :
    ReachRankCert (σ.markInconsistentIf A) where
  rank := cert.rank
  deps := cert.deps
  rank_iff := by
    intro i b
    rw [ReachState.getCell_markInconsistentIf]
    exact cert.rank_iff i b
  deps_none := by
    intro i b hnone
    exact cert.deps_none i b (by rwa [← ReachState.getCell_markInconsistentIf])
  parents_lt := by
    intro i b r hr p hp
    exact cert.parents_lt i b r hr p hp

/-- Certificate depends only on witness slots, not `retrievable`. -/
def ReachRankCert.ofSameSlots {n : Nat} {σ τ : ReachState n}
    (cert : ReachRankCert σ)
    (h : ∀ i b, (τ.getCell i).slotWitness b = (σ.getCell i).slotWitness b) :
    ReachRankCert τ where
  rank := cert.rank
  deps := cert.deps
  rank_iff := by
    intro i b
    rw [h i b]
    exact cert.rank_iff i b
  deps_none := by
    intro i b hnone
    exact cert.deps_none i b (by simpa [h i b] using hnone)
  parents_lt := by
    intro i b r hr p hp
    exact cert.parents_lt i b r hr p hp

theorem ReachRankCert.castState_rank {n : Nat} {σ τ : ReachState n}
    (h : σ = τ) (cert : ReachRankCert σ) :
    (cert.castState h).rank = cert.rank := by
  cases h; rfl

theorem ReachRankCert.extend_preserves_rank {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat) (hi : i < σ.cells.size)
    (hpar : RankedParents cert deps)
    {j : Nat} {b' : SlotNew} {r : Nat}
    (hr : cert.rank j b' = some r) :
    (ReachRankCert.extend cert i b w deps hi hpar).rank j b' = some r := by
  unfold ReachRankCert.extend
  split
  · rename_i _ hslot
    simp only [ReachRankCert.extendOccupied]
    rw [ReachRankCert.castState_rank]
    exact hr
  · rename_i hfresh
    simp only [ReachRankCert.extendFresh]
    have hne : ¬(j = i ∧ b' = b) := by
      intro h
      obtain ⟨rfl, rfl⟩ := show i = j ∧ b = b' from ⟨h.1.symm, h.2.symm⟩
      have hiff := cert.rank_iff i b
      rw [hfresh, hr] at hiff
      cases hiff
    rw [if_neg hne]; exact hr

theorem RankedParents.of_extend {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat) (hi : i < σ.cells.size)
    (hpar : RankedParents cert deps)
    (ps : List Nat) (hp : RankedParents cert ps) :
    RankedParents (ReachRankCert.extend cert i b w deps hi hpar) ps := by
  intro p hpMem
  obtain ⟨bP, rP, hrP⟩ := hp p hpMem
  exact ⟨bP, rP, ReachRankCert.extend_preserves_rank cert i b w deps hi hpar hrP⟩

theorem ParentsCertified.of_extend {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat) (hi : i < σ.cells.size)
    (hpar : RankedParents cert deps)
    (w' : Witness) (hp : ParentsCertified cert w') :
    ParentsCertified (ReachRankCert.extend cert i b w deps hi hpar) w' :=
  RankedParents.of_extend cert i b w deps hi hpar _ hp

theorem ParentsCertified.of_markInconsistentIf {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (A : Object n) (w : Witness)
    (hp : ParentsCertified cert w) :
    ParentsCertified (cert.ofMarkInconsistentIf A) w := by
  intro p hpMem
  obtain ⟨bP, rP, hrP⟩ := hp p hpMem
  exact ⟨bP, rP, hrP⟩

theorem RankedParents.of_markInconsistentIf {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (A : Object n) (ps : List Nat)
    (hp : RankedParents cert ps) :
    RankedParents (cert.ofMarkInconsistentIf A) ps := by
  intro p hpMem
  obtain ⟨bP, rP, hrP⟩ := hp p hpMem
  exact ⟨bP, rP, hrP⟩

/-! ### Certified operations -/

/-- Certified discover with explicit proof-only dependency list. -/
def certifiedDiscover {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (i : Nat) (b : SlotNew) (w : Witness) (deps : List Nat)
    (h : RankedParents cert deps) :
    CertifiedReachResult n :=
  match σ.typeAt i with
  | none => ⟨σ, cert⟩
  | some A =>
      if hi : i < σ.cells.size then
        let σ₁ := σ.setCell i ((σ.getCell i).record b w)
        let c₁ := ReachRankCert.extend cert i b w deps hi h
        ⟨σ₁.markInconsistentIf A, c₁.ofMarkInconsistentIf A⟩
      else
        ⟨σ.markInconsistentIf A, cert.ofMarkInconsistentIf A⟩

/-- Default deps = `Witness.cellParents w`. -/
def certifiedDiscoverDefault {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (i : Nat) (b : SlotNew) (w : Witness)
    (h : ParentsCertified cert w) :
    CertifiedReachResult n :=
  certifiedDiscover σ cert i b w (Witness.cellParents w) h

theorem certifiedDiscover_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat) (h : RankedParents cert deps) :
    (certifiedDiscover σ cert i b w deps h).project = σ.discover i b w := by
  dsimp only [certifiedDiscover, ReachState.discover, CertifiedReachResult.project]
  cases σ.typeAt i with
  | none => rfl
  | some A =>
      by_cases hi : i < σ.cells.size
      · simp [hi]
      · simp [hi, ReachState.setCell]


theorem RankedParents.of_certifiedDiscover {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat) (h : RankedParents cert deps)
    (ps : List Nat) (hp : RankedParents cert ps) :
    RankedParents (certifiedDiscover σ cert i b w deps h).cert ps := by
  unfold certifiedDiscover
  cases σ.typeAt i with
  | none => exact hp
  | some A =>
      change RankedParents
        ((if hi : i < σ.cells.size then
          ({ state := (σ.setCell i ((σ.getCell i).record b w)).markInconsistentIf A,
             cert := (ReachRankCert.extend cert i b w deps hi h).ofMarkInconsistentIf A } :
            CertifiedReachResult n)
        else
          ({ state := σ.markInconsistentIf A,
             cert := cert.ofMarkInconsistentIf A } :
            CertifiedReachResult n)).cert) ps
      by_cases hi : i < σ.cells.size
      · rw [dif_pos hi]
        exact RankedParents.of_markInconsistentIf
          (ReachRankCert.extend cert i b w deps hi h) A ps
          (RankedParents.of_extend cert i b w deps hi h ps hp)
      · rw [dif_neg hi]
        exact RankedParents.of_markInconsistentIf cert A ps hp

/-- Dual-fire with explicit deps; parents required only when a slot fires. -/
def certifiedDiscoverDual {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (i : Nat) (oldOk newOk : Bool) (w : Witness) (deps : List Nat)
    (h : (oldOk = true ∨ newOk = true) → RankedParents cert deps) :
    CertifiedReachResult n :=
  match oldOk, newOk with
  | true, true =>
      let h₀ := h (Or.inl rfl)
      let c₁ := certifiedDiscover σ cert i false w deps h₀
      certifiedDiscover c₁.state c₁.cert i true w deps
        (RankedParents.of_certifiedDiscover σ cert i false w deps h₀ deps h₀)
  | true, false =>
      certifiedDiscover σ cert i false w deps (h (Or.inl rfl))
  | false, true =>
      certifiedDiscover σ cert i true w deps (h (Or.inr rfl))
  | false, false =>
      ⟨σ, cert⟩

theorem certifiedDiscoverDual_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (oldOk newOk : Bool) (w : Witness)
    (deps : List Nat)
    (h : (oldOk = true ∨ newOk = true) → RankedParents cert deps) :
    (certifiedDiscoverDual σ cert i oldOk newOk w deps h).project =
      σ.discoverDual i oldOk newOk w := by
  cases oldOk <;> cases newOk
  · rfl
  · exact certifiedDiscover_project σ cert i true w deps (h (Or.inr rfl))
  · exact certifiedDiscover_project σ cert i false w deps (h (Or.inl rfl))
  · have h₀ := h (Or.inl rfl)
    have h₁ := certifiedDiscover_project σ cert i false w deps h₀
    have h₂ := certifiedDiscover_project
      (certifiedDiscover σ cert i false w deps h₀).state
      (certifiedDiscover σ cert i false w deps h₀).cert i true w deps
      (RankedParents.of_certifiedDiscover σ cert i false w deps h₀ deps h₀)
    simp only [certifiedDiscoverDual, CertifiedReachResult.project] at h₁ h₂ ⊢
    rw [h₂, h₁]
    rfl

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
            let deps : List Nat := []
            let hpar : RankedParents cert deps := RankedParents_nil cert
            let σRec := σ.setCell i ((σ.getCell i).record b w)
            let σHyp := σ.setCell i ((σ.getCell i).recordHyp b w)
            let certRec := ReachRankCert.extend cert i b w deps hi hpar
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

**Landed without `sorry`:** assign-once; proof-only ranks for **all** stored
witnesses (intro and neutral) with stored `deps`; `RankedParents` /
`ParentsCertified`; `certifiedDiscover` / `Dual` / `MarkHyp` with explicit deps;
`ReachCell.neutralWitness` for `neuOf`; richer `cellParents` for `.app` /
`.appTy` (argument included); lex measure demos for
`app → invOf → neuOf` and `appTy`.

**Paused:** full `certifiedReachStep` / type-rule wrappers. Resume only after the
η-argument application fixture reconstructs under the measure above.

**Stop condition:** never invent ranks for missing parents — require
`RankedParents` before fresh extend; η/intro deps are rule-site lists stored in
`ReachRankCert.deps` (not on computational `Witness`).
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
