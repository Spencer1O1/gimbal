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
import Gimbal.Equality.Polarized
import Mathlib.Tactic

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

/-! ## Centralized rule dependency lists

Every certified wrapper must take deps from this table — do not invent ad-hoc
parent lists at call sites. Provenance still matters: a fired old/new slot
receives the deps for **that** derivation, not an unrelated ranked cell.
-/

namespace RuleDeps

/-- Hypothesis projections: no cell parent. -/
def hypProj : List Nat := []

/-- Context binding / seed: no cell parent. -/
def ctxVar : List Nat := []

/-- Unit η-intro: no cell parent. -/
def unit : List Nat := []

/-- Type projection from a neutral product cell. -/
def typeProj (prodIdx : Nat) : List Nat := [prodIdx]

/-- Hypothesis application: argument cell (covers η-built args via `invOf`). -/
def hypApp (argIdx : Nat) : List Nat := [argIdx]

/-- Type application: function and argument cells. -/
def typeApp (fnIdx argIdx : Nat) : List Nat := [fnIdx, argIdx]

/-- Coproduct introduction: selected payload. -/
def coprodIntro (payloadIdx : Nat) : List Nat := [payloadIdx]

/-- Product η: both components. -/
def productEta (lIdx rIdx : Nat) : List Nat := [lIdx, rIdx]

/-- Function η: return type. -/
def functionEta (retIdx : Nat) : List Nat := [retIdx]

theorem hypProj_eq_cellParents_fstHyp (i : Nat) :
    hypProj = Witness.cellParents (.fstHyp i) := rfl

theorem hypProj_eq_cellParents_sndHyp (i : Nat) :
    hypProj = Witness.cellParents (.sndHyp i) := rfl

theorem typeProj_eq_cellParents_fstType (p : Nat) :
    typeProj p = Witness.cellParents (.fstType p) := rfl

theorem typeProj_eq_cellParents_sndType (p : Nat) :
    typeProj p = Witness.cellParents (.sndType p) := rfl

theorem hypApp_eq_cellParents (fnHyp argIdx : Nat) :
    hypApp argIdx = Witness.cellParents (.app fnHyp argIdx) := rfl

theorem typeApp_eq_cellParents (fnIdx argIdx : Nat) :
    typeApp fnIdx argIdx = Witness.cellParents (.appTy fnIdx argIdx) := rfl

theorem coprodIntro_eq_cellParents_inl (p : Nat) :
    coprodIntro p = Witness.cellParents (.inl p) := rfl

theorem coprodIntro_eq_cellParents_inr (p : Nat) :
    coprodIntro p = Witness.cellParents (.inr p) := rfl

end RuleDeps

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
  simp [reconObjectSize]; try omega

theorem reconObjectSize_prod_right_lt {n : Nat} (L R : Object n) :
    reconObjectSize R < reconObjectSize (.prod L R) := by
  simp [reconObjectSize]; try omega

theorem reconObjectSize_exp_ret_lt {n : Nat} (Arg Ret : Object n) :
    reconObjectSize Ret < reconObjectSize (.exp Arg Ret) := by
  simp [reconObjectSize]; try omega

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

`retrievable_witnessed`: `markHyp` / `recordHyp` never leave a bare retrievable
slot, so `simplyDeducible` always implies a ranked witness under this cert.
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
  retrievable_witnessed :
    ∀ (i : Nat),
      (σ.getCell i).retrievable = true →
        (σ.getCell i).oldWitness.isSome = true ∨
          (σ.getCell i).newWitness.isSome = true

/-- Preferred-slot rank via `neutralWitness` (new neutral, else old neutral). -/
def ReachRankCert.rankOfPreferred {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) : Option Nat :=
  match (σ.getCell i).neutralWitness with
  | some w =>
      if (σ.getCell i).newNeutral then cert.rank i true else cert.rank i false
  | none => none

/-- Empty certificate when no witnesses are stored. -/
def ReachRankCert.empty {n : Nat} (σ : ReachState n)
    (h : ∀ i, (σ.getCell i).oldWitness = none ∧ (σ.getCell i).newWitness = none)
    (hret : ∀ i, (σ.getCell i).retrievable = false) :
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
  retrievable_witnessed := by
    intro i hr
    rw [hret i] at hr
    cases hr

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

/-- `simplyDeducible` implies a ranked witness under a sound certificate. -/
theorem ReachRankCert.ranked_of_simplyDeducible {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat)
    (h : (σ.getCell i).simplyDeducible = true) :
    ∃ (b : SlotNew) (r : Nat), cert.rank i b = some r := by
  have ranked_of_isSome (b : SlotNew)
      (hs : ((σ.getCell i).slotWitness b).isSome = true) :
      ∃ r, cert.rank i b = some r := by
    have hrs : (cert.rank i b).isSome = true := by
      simpa [hs] using (cert.rank_iff i b).symm
    cases hr : cert.rank i b with
    | none => simp [hr] at hrs
    | some r => exact ⟨r, rfl⟩
  match hr : (σ.getCell i).retrievable,
        ho : (σ.getCell i).oldWitness.isSome,
        hn : (σ.getCell i).newWitness.isSome with
  | true, _, _ =>
      rcases cert.retrievable_witnessed i hr with hOld | hNew
      · obtain ⟨r, hrk⟩ := ranked_of_isSome false (by simpa [ReachCell.slotWitness] using hOld)
        exact ⟨false, r, hrk⟩
      · obtain ⟨r, hrk⟩ := ranked_of_isSome true (by simpa [ReachCell.slotWitness] using hNew)
        exact ⟨true, r, hrk⟩
  | false, true, _ =>
      obtain ⟨r, hrk⟩ := ranked_of_isSome false (by simpa [ReachCell.slotWitness] using ho)
      exact ⟨false, r, hrk⟩
  | false, false, true =>
      obtain ⟨r, hrk⟩ := ranked_of_isSome true (by simpa [ReachCell.slotWitness] using hn)
      exact ⟨true, r, hrk⟩
  | false, false, false =>
      simp [ReachCell.simplyDeducible, hr, ho, hn] at h

theorem ReachRankCert.ranked_of_oldDeducible {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat)
    (h : (σ.getCell i).oldDeducible = true) :
    ∃ (r : Nat), cert.rank i false = some r := by
  have hs : ((σ.getCell i).slotWitness false).isSome = true := by
    simpa [ReachCell.oldDeducible, ReachCell.slotWitness] using h
  have hrs : (cert.rank i false).isSome = true := by
    simpa [hs] using (cert.rank_iff i false).symm
  cases hr : cert.rank i false with
  | none => simp [hr] at hrs
  | some r => exact ⟨r, rfl⟩

theorem RankedParents.singleton {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (p : Nat)
    (hp : ∃ (b : SlotNew) (r : Nat), cert.rank p b = some r) :
    RankedParents cert [p] := by
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  exact hp

theorem RankedParents.pair {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (p q : Nat)
    (hp : ∃ (b : SlotNew) (r : Nat), cert.rank p b = some r)
    (hq : ∃ (b : SlotNew) (r : Nat), cert.rank q b = some r) :
    RankedParents cert [p, q] := by
  intro r hr
  have : r = p ∨ r = q := by
    simpa [List.mem_cons, List.mem_nil_iff] using hr
  rcases this with rfl | rfl
  · exact hp
  · exact hq

theorem RankedParents.singleton_of_simplyDeducible {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (p : Nat)
    (hp : (σ.getCell p).simplyDeducible = true) :
    RankedParents cert [p] :=
  RankedParents.singleton cert p (cert.ranked_of_simplyDeducible p hp)

theorem RankedParents.pair_of_simplyDeducible {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (p q : Nat)
    (hp : (σ.getCell p).simplyDeducible = true)
    (hq : (σ.getCell q).simplyDeducible = true) :
    RankedParents cert [p, q] :=
  RankedParents.pair cert p q
    (cert.ranked_of_simplyDeducible p hp)
    (cert.ranked_of_simplyDeducible q hq)

theorem RankedParents.singleton_of_neutral {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (p : Nat)
    (hNeu : (σ.getCell p).oldNeutral = true ∨ (σ.getCell p).newNeutral = true) :
    RankedParents cert [p] :=
  RankedParents.singleton cert p (cert.ranked_of_neutral p hNeu)

/--
Proof-only: every stored `.fstType`/`.sndType` has a ranked **neutral** product
parent, and every stored `.appTy` has a ranked **neutral** function parent, each
strictly below the child rank. Stronger than `parents_lt`, which only yields some
ranked parent slot (possibly η).

To be installed as `ReachRankCert.neutralParent_lt` before package induction;
call sites may assume it as a hypothesis until the cert field is threaded.
-/
def NeutralParentLt {n : Nat} {σ : ReachState n} (cert : ReachRankCert σ)
    (childRank : Nat) : Witness → Prop
  | .fstType p =>
      ∃ (bP : SlotNew) (wP : Witness) (rP : Nat),
        (σ.getCell p).slotWitness bP = some wP ∧
          Witness.isNeutral wP = true ∧
          cert.rank p bP = some rP ∧ rP < childRank
  | .sndType p =>
      ∃ (bP : SlotNew) (wP : Witness) (rP : Nat),
        (σ.getCell p).slotWitness bP = some wP ∧
          Witness.isNeutral wP = true ∧
          cert.rank p bP = some rP ∧ rP < childRank
  | .appTy fn _arg =>
      ∃ (bP : SlotNew) (wP : Witness) (rP : Nat),
        (σ.getCell fn).slotWitness bP = some wP ∧
          Witness.isNeutral wP = true ∧
          cert.rank fn bP = some rP ∧ rP < childRank
  | .ctxVar _ | .fstHyp _ | .sndHyp _ | .app _ _ | .inl _ | .inr _ | .unit | .eta =>
      True

/-- A cell with a neutral provenance slot yields an explicit ranked neutral witness. -/
theorem ReachRankCert.exists_ranked_neutral {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (ti : Nat)
    (hNeu : (σ.getCell ti).oldNeutral = true ∨ (σ.getCell ti).newNeutral = true) :
    ∃ (b : SlotNew) (w : Witness) (r : Nat),
      (σ.getCell ti).slotWitness b = some w ∧
        Witness.isNeutral w = true ∧
        cert.rank ti b = some r := by
  cases hNeu with
  | inl ho =>
    cases hw : (σ.getCell ti).oldWitness with
    | none => simp [ReachCell.oldNeutral, hw] at ho
    | some w =>
      have hne : Witness.isNeutral w = true := by
        simpa [ReachCell.oldNeutral, hw] using ho
      have hrs : (cert.rank ti false).isSome = true := by
        have hslot : ((σ.getCell ti).slotWitness false).isSome = true := by
          simp [ReachCell.slotWitness, hw]
        simpa [hslot] using (cert.rank_iff ti false).symm
      cases hr : cert.rank ti false with
      | none => simp [hr] at hrs
      | some r => exact ⟨false, w, r, by simp [ReachCell.slotWitness, hw], hne, hr⟩
  | inr hn =>
    cases hw : (σ.getCell ti).newWitness with
    | none => simp [ReachCell.newNeutral, hw] at hn
    | some w =>
      have hne : Witness.isNeutral w = true := by
        simpa [ReachCell.newNeutral, hw] using hn
      have hrs : (cert.rank ti true).isSome = true := by
        have hslot : ((σ.getCell ti).slotWitness true).isSome = true := by
          simp [ReachCell.slotWitness, hw]
        simpa [hslot] using (cert.rank_iff ti true).symm
      cases hr : cert.rank ti true with
      | none => simp [hr] at hrs
      | some r => exact ⟨true, w, r, by simp [ReachCell.slotWitness, hw], hne, hr⟩

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

/-- `record` always occupies the targeted provenance slot. -/
theorem ReachCell.slotWitness_record_isSome (c : ReachCell) (b : SlotNew) (w : Witness) :
    ((c.record b w).slotWitness b).isSome = true := by
  cases b
  · cases ho : c.oldWitness <;> simp [ReachCell.slotWitness, ReachCell.record, ho]
  · cases hn : c.newWitness <;> simp [ReachCell.slotWitness, ReachCell.record, hn]

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
  retrievable_witnessed := by
    intro j hr
    by_cases hj : j = i
    · have hji : i = j := hj.symm; subst hji
      -- Fresh record into `b` occupies that slot.
      cases b
      · left
        have ho : (σ.getCell i).oldWitness = none := by
          simpa [ReachCell.slotWitness] using hfresh
        simp [ReachState.getCell_setCell_self hi, ReachCell.record, ho]
      · right
        have hn : (σ.getCell i).newWitness = none := by
          simpa [ReachCell.slotWitness] using hfresh
        simp [ReachState.getCell_setCell_self hi, ReachCell.record, hn]
    · rw [ReachState.getCell_setCell_ne (Ne.symm hj)] at hr ⊢
      exact cert.retrievable_witnessed j hr

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
  retrievable_witnessed := by
    intro i hr
    rw [ReachState.getCell_markInconsistentIf] at hr ⊢
    exact cert.retrievable_witnessed i hr

/-- Lift cert across `record` → `recordHyp` (slots identical; retrievable may become true). -/
def ReachRankCert.ofRecordHyp {n : Nat} {σ : ReachState n} {i : Nat} {b : SlotNew}
    {w : Witness}
    (cert : ReachRankCert (σ.setCell i ((σ.getCell i).record b w)))
    (hi : i < σ.cells.size) :
    ReachRankCert (σ.setCell i ((σ.getCell i).recordHyp b w)) where
  rank := cert.rank
  deps := cert.deps
  rank_iff := by
    intro j b'
    have hslots :
        ((σ.setCell i ((σ.getCell i).recordHyp b w)).getCell j).slotWitness b' =
          ((σ.setCell i ((σ.getCell i).record b w)).getCell j).slotWitness b' := by
      by_cases hj : j = i
      · subst hj
        rw [ReachState.getCell_setCell_self hi, ReachState.getCell_setCell_self hi]
        exact ReachCell.slotWitness_recordHyp _ b w b'
      · rw [ReachState.getCell_setCell_ne (Ne.symm hj),
          ReachState.getCell_setCell_ne (Ne.symm hj)]
    rw [hslots]
    exact cert.rank_iff j b'
  deps_none := by
    intro j b' hnone
    have hslots :
        ((σ.setCell i ((σ.getCell i).recordHyp b w)).getCell j).slotWitness b' =
          ((σ.setCell i ((σ.getCell i).record b w)).getCell j).slotWitness b' := by
      by_cases hj : j = i
      · subst hj
        rw [ReachState.getCell_setCell_self hi, ReachState.getCell_setCell_self hi]
        exact ReachCell.slotWitness_recordHyp _ b w b'
      · rw [ReachState.getCell_setCell_ne (Ne.symm hj),
          ReachState.getCell_setCell_ne (Ne.symm hj)]
    exact cert.deps_none j b' (hslots ▸ hnone)
  parents_lt := by
    intro j b' r hr p hp
    exact cert.parents_lt j b' r hr p hp
  retrievable_witnessed := by
    intro j hr
    by_cases hj : j = i
    · have hji : i = j := hj.symm; subst hji
      rw [ReachState.getCell_setCell_self hi]
      have hsome :
          (((σ.getCell i).record b w).slotWitness b).isSome = true :=
        ReachCell.slotWitness_record_isSome _ b w
      have hslot :
          ((σ.getCell i).recordHyp b w).slotWitness b =
            ((σ.getCell i).record b w).slotWitness b :=
        ReachCell.slotWitness_recordHyp _ b w b
      cases b
      · left
        simpa [ReachCell.slotWitness, hslot] using hsome
      · right
        simpa [ReachCell.slotWitness, hslot] using hsome
    · rw [ReachState.getCell_setCell_ne (Ne.symm hj)] at hr ⊢
      -- Other cells match the `record` state, which cert already covers.
      have hr' :
          ((σ.setCell i ((σ.getCell i).record b w)).getCell j).retrievable = true := by
        rwa [ReachState.getCell_setCell_ne (Ne.symm hj)]
      have hit := cert.retrievable_witnessed j hr'
      rw [ReachState.getCell_setCell_ne (Ne.symm hj)] at hit
      exact hit

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
            let deps : List Nat := RuleDeps.hypProj
            let hpar : RankedParents cert deps := RankedParents_nil cert
            let σHyp := σ.setCell i ((σ.getCell i).recordHyp b w)
            let certRec := ReachRankCert.extend cert i b w deps hi hpar
            ⟨σHyp.markInconsistentIf A,
              (certRec.ofRecordHyp hi).ofMarkInconsistentIf A⟩
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

theorem RankedParents.of_certifiedDiscoverDual {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (oldOk newOk : Bool) (w : Witness)
    (deps : List Nat)
    (h : (oldOk = true ∨ newOk = true) → RankedParents cert deps)
    (ps : List Nat) (hp : RankedParents cert ps) :
    RankedParents (certifiedDiscoverDual σ cert i oldOk newOk w deps h).cert ps := by
  cases oldOk <;> cases newOk
  · exact hp
  · exact RankedParents.of_certifiedDiscover σ cert i true w deps (h (Or.inr rfl)) ps hp
  · exact RankedParents.of_certifiedDiscover σ cert i false w deps (h (Or.inl rfl)) ps hp
  · have h₀ := h (Or.inl rfl)
    exact RankedParents.of_certifiedDiscover
      (certifiedDiscover σ cert i false w deps h₀).state
      (certifiedDiscover σ cert i false w deps h₀).cert i true w deps
      (RankedParents.of_certifiedDiscover σ cert i false w deps h₀ deps h₀) ps
      (RankedParents.of_certifiedDiscover σ cert i false w deps h₀ ps hp)

theorem CertifiedReachResult.project_ite {n : Nat} (b : Bool)
    (c₁ c₂ : CertifiedReachResult n) :
    (if b then c₁ else c₂).project = if b then c₁.project else c₂.project := by
  cases b <;> rfl

/-! ## Certified forward-chaining rules

Each wrapper mirrors the computational rule's control flow and records deps from
`RuleDeps`. A slot may fire only when `RankedParents` holds for **that**
derivation's dependency list — otherwise the certified term is uninhabited.
-/

private theorem bool_and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all

private theorem bool_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> simp_all

private theorem simplyDeducible_of_oldDeducible (c : ReachCell)
    (h : c.oldDeducible = true) : c.simplyDeducible = true := by
  simp only [ReachCell.simplyDeducible, ReachCell.oldDeducible] at h ⊢
  simp [h]

def certifiedSeedHypRule {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) : CertifiedReachResult n :=
  match Γ.hyps[i]? with
  | some A =>
      if objectPolarity A == .pos then certifiedMarkHyp Γ σ cert i else ⟨σ, cert⟩
  | none => ⟨σ, cert⟩

theorem certifiedSeedHypRule_project {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) :
    (certifiedSeedHypRule Γ σ cert i).project = seedHypRule Γ σ i := by
  unfold certifiedSeedHypRule seedHypRule
  cases Γ.hyps[i]? with
  | none => rfl
  | some A =>
      cases hpol : (objectPolarity A == Polarity.pos) with
      | false => simp [hpol, CertifiedReachResult.project]
      | true =>
          simp only [hpol, ↓reduceIte]
          exact certifiedMarkHyp_project Γ σ cert i

def certifiedUnitEtaRule {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ) :
    CertifiedReachResult n :=
  match σ.findTypeIdx (.unit : Object n) with
  | some uIdx =>
      certifiedDiscover σ cert uIdx false .unit RuleDeps.unit (RankedParents_nil cert)
  | none => ⟨σ, cert⟩

theorem certifiedUnitEtaRule_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) :
    (certifiedUnitEtaRule σ cert).project = unitEtaRule σ := by
  unfold certifiedUnitEtaRule unitEtaRule
  cases σ.findTypeIdx (.unit : Object n) with
  | none => rfl
  | some uIdx =>
      exact certifiedDiscover_project σ cert uIdx false .unit RuleDeps.unit
        (RankedParents_nil cert)

def certifiedHypProdRule {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (L R : Object n) :
    CertifiedReachResult n :=
  match σ.findTypeIdx (.prod L R), σ.findTypeIdx L, σ.findTypeIdx R with
  | some _pIdx, some lIdx, some rIdx =>
      let c₁ := certifiedDiscover σ cert lIdx (Γ.isNew i) (.fstHyp i)
        RuleDeps.hypProj (RankedParents_nil cert)
      certifiedDiscover c₁.state c₁.cert rIdx (Γ.isNew i) (.sndHyp i)
        RuleDeps.hypProj
        (RankedParents.of_certifiedDiscover σ cert lIdx (Γ.isNew i) (.fstHyp i)
          RuleDeps.hypProj (RankedParents_nil cert) RuleDeps.hypProj
          (RankedParents_nil cert))
  | _, _, _ => ⟨σ, cert⟩

theorem certifiedHypProdRule_project {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (L R : Object n) :
    (certifiedHypProdRule Γ σ cert i L R).project = hypProdRule Γ σ i L R := by
  unfold certifiedHypProdRule hypProdRule
  cases hP : σ.findTypeIdx (.prod L R) with
  | none => simp [hP, CertifiedReachResult.project]
  | some pIdx =>
    cases hL : σ.findTypeIdx L with
    | none => simp [hP, hL, CertifiedReachResult.project]
    | some lIdx =>
      cases hR : σ.findTypeIdx R with
      | none => simp [hP, hL, hR, CertifiedReachResult.project]
      | some rIdx =>
          simp only [hP, hL, hR]
          have h₁ := certifiedDiscover_project σ cert lIdx (Γ.isNew i) (.fstHyp i)
            RuleDeps.hypProj (RankedParents_nil cert)
          have h₂ := certifiedDiscover_project
            (certifiedDiscover σ cert lIdx (Γ.isNew i) (.fstHyp i)
              RuleDeps.hypProj (RankedParents_nil cert)).state
            (certifiedDiscover σ cert lIdx (Γ.isNew i) (.fstHyp i)
              RuleDeps.hypProj (RankedParents_nil cert)).cert
            rIdx (Γ.isNew i) (.sndHyp i) RuleDeps.hypProj
            (RankedParents.of_certifiedDiscover σ cert lIdx (Γ.isNew i) (.fstHyp i)
              RuleDeps.hypProj (RankedParents_nil cert) RuleDeps.hypProj
              (RankedParents_nil cert))
          simp only [CertifiedReachResult.project] at h₁ h₂ ⊢
          rw [h₂, h₁]

def certifiedHypAppRule {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (Arg Ret : Object n) :
    CertifiedReachResult n :=
  match σ.findTypeIdx Arg, σ.findTypeIdx Ret with
  | some aIdx, some rIdx =>
      certifiedDiscoverDual σ cert rIdx
        ((σ.getCell aIdx).oldDeducible && !Γ.isNew i)
        ((σ.getCell aIdx).simplyDeducible &&
          ((σ.getCell aIdx).usesNew || Γ.isNew i))
        (.app i aIdx) (RuleDeps.hypApp aIdx)
        (fun hfire => by
          have hsimp : (σ.getCell aIdx).simplyDeducible = true := by
            cases hfire with
            | inl ho =>
              exact simplyDeducible_of_oldDeducible _
                (bool_and_left ho)
            | inr hn =>
              exact bool_and_left hn
          exact RankedParents.singleton_of_simplyDeducible cert aIdx hsimp)
  | _, _ => ⟨σ, cert⟩

theorem certifiedHypAppRule_project {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (Arg Ret : Object n) :
    (certifiedHypAppRule Γ σ cert i Arg Ret).project = hypAppRule Γ σ i Arg Ret := by
  unfold certifiedHypAppRule hypAppRule
  cases ha : σ.findTypeIdx Arg with
  | none => simp [ha, CertifiedReachResult.project]
  | some aIdx =>
    cases hr : σ.findTypeIdx Ret with
    | none => simp [ha, hr, CertifiedReachResult.project]
    | some rIdx =>
        simp only [ha, hr]
        exact certifiedDiscoverDual_project σ cert rIdx
          ((σ.getCell aIdx).oldDeducible && !Γ.isNew i)
          ((σ.getCell aIdx).simplyDeducible &&
            ((σ.getCell aIdx).usesNew || Γ.isNew i))
          (.app i aIdx) (RuleDeps.hypApp aIdx) _

def certifiedHypRule {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) : CertifiedReachResult n :=
  match Γ.hyps[i]? with
  | some (.prod L R) => certifiedHypProdRule Γ σ cert i L R
  | some (.exp Arg Ret) => certifiedHypAppRule Γ σ cert i Arg Ret
  | _ => ⟨σ, cert⟩

theorem certifiedHypRule_project {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) :
    (certifiedHypRule Γ σ cert i).project = hypRule Γ σ i := by
  unfold certifiedHypRule hypRule
  cases Γ.hyps[i]? with
  | none => rfl
  | some A =>
      cases A with
      | prod L R => exact certifiedHypProdRule_project Γ σ cert i L R
      | exp Arg Ret => exact certifiedHypAppRule_project Γ σ cert i Arg Ret
      | _ => rfl

/-- Relate proof-carrying `dite` on a `Bool` to computational `ite`. -/
theorem CertifiedReachResult.project_dite_bool {n : Nat} (b : Bool)
    (t : b = true → CertifiedReachResult n) (e : CertifiedReachResult n)
    (sT sE : ReachState n)
    (ht : ∀ (h : b = true), (t h).project = sT)
    (he : e.project = sE) :
    (if h : b = true then t h else e).project = (if b then sT else sE) := by
  cases b with
  | false => simpa using he
  | true => simpa using ht rfl

/-- Computational core shared with `prodTypeRule` after index resolution. -/
def prodTypeRule.core {n : Nat} (σ : ReachState n) (ti lIdx rIdx : Nat) : ReachState n :=
  let σ₁ :=
    (σ.discoverDual lIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
      (.fstType ti)).discoverDual
      rIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.sndType ti)
  if (σ.getCell ti).simplyDeducible then σ₁
  else if (σ₁.getCell lIdx).simplyDeducible && (σ₁.getCell rIdx).simplyDeducible then
    σ₁.discoverDual ti
      ((σ₁.getCell lIdx).oldDeducible && (σ₁.getCell rIdx).oldDeducible)
      ((σ₁.getCell lIdx).usesNew || (σ₁.getCell rIdx).usesNew)
      .eta
  else σ₁

theorem prodTypeRule_eq_core {n : Nat} (σ : ReachState n) (ti : Nat) (L R : Object n)
    {lIdx rIdx : Nat}
    (hl : σ.findTypeIdx L = some lIdx) (hr : σ.findTypeIdx R = some rIdx) :
    prodTypeRule σ ti L R = prodTypeRule.core σ ti lIdx rIdx := by
  unfold prodTypeRule prodTypeRule.core
  simp only [hl, hr]
  cases (σ.getCell ti).simplyDeducible <;> rfl

def certifiedProdTypeRule.go {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (ti lIdx rIdx : Nat) : CertifiedReachResult n :=
  let c₁ := certifiedDiscoverDual σ cert lIdx
    (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
    (RuleDeps.typeProj ti)
    (fun h => RankedParents.singleton_of_neutral cert ti h)
  let c₂ := certifiedDiscoverDual c₁.state c₁.cert rIdx
    (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.sndType ti)
    (RuleDeps.typeProj ti)
    (fun h =>
      RankedParents.of_certifiedDiscoverDual σ cert lIdx
        (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
        (RuleDeps.typeProj ti)
        (fun h0 => RankedParents.singleton_of_neutral cert ti h0)
        (RuleDeps.typeProj ti)
        (RankedParents.singleton_of_neutral cert ti h))
  if (σ.getCell ti).simplyDeducible then c₂
  else if hcomp :
      ((c₂.state.getCell lIdx).simplyDeducible &&
        (c₂.state.getCell rIdx).simplyDeducible) = true then
    certifiedDiscoverDual c₂.state c₂.cert ti
      ((c₂.state.getCell lIdx).oldDeducible && (c₂.state.getCell rIdx).oldDeducible)
      ((c₂.state.getCell lIdx).usesNew || (c₂.state.getCell rIdx).usesNew)
      .eta (RuleDeps.productEta lIdx rIdx)
      (fun _ =>
        RankedParents.pair_of_simplyDeducible c₂.cert lIdx rIdx
          (bool_and_left hcomp) (bool_and_right hcomp))
  else
    c₂

def certifiedProdTypeRule {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (ti : Nat) (L R : Object n) : CertifiedReachResult n :=
  match σ.findTypeIdx L, σ.findTypeIdx R with
  | some lIdx, some rIdx => certifiedProdTypeRule.go σ cert ti lIdx rIdx
  | _, _ => ⟨σ, cert⟩

theorem certifiedProdTypeRule.go_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (ti lIdx rIdx : Nat) :
    (certifiedProdTypeRule.go σ cert ti lIdx rIdx).project =
      prodTypeRule.core σ ti lIdx rIdx := by
  unfold certifiedProdTypeRule.go prodTypeRule.core
  have h₁ := certifiedDiscoverDual_project σ cert lIdx
    (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
    (RuleDeps.typeProj ti)
    (fun h => RankedParents.singleton_of_neutral cert ti h)
  set c₁ := certifiedDiscoverDual σ cert lIdx
    (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
    (RuleDeps.typeProj ti)
    (fun h => RankedParents.singleton_of_neutral cert ti h)
  have h₂ := certifiedDiscoverDual_project c₁.state c₁.cert rIdx
    (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.sndType ti)
    (RuleDeps.typeProj ti)
    (fun h =>
      RankedParents.of_certifiedDiscoverDual σ cert lIdx
        (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
        (RuleDeps.typeProj ti)
        (fun h0 => RankedParents.singleton_of_neutral cert ti h0)
        (RuleDeps.typeProj ti)
        (RankedParents.singleton_of_neutral cert ti h))
  set c₂ := certifiedDiscoverDual c₁.state c₁.cert rIdx
    (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.sndType ti)
    (RuleDeps.typeProj ti)
    (fun h =>
      RankedParents.of_certifiedDiscoverDual σ cert lIdx
        (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
        (RuleDeps.typeProj ti)
        (fun h0 => RankedParents.singleton_of_neutral cert ti h0)
        (RuleDeps.typeProj ti)
        (RankedParents.singleton_of_neutral cert ti h))
  have hσ₁ : c₂.project =
      (σ.discoverDual lIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
        (.fstType ti)).discoverDual
        rIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.sndType ti) := by
    simp only [CertifiedReachResult.project] at h₁ h₂ ⊢
    rw [h₂, h₁]
  cases hsd : (σ.getCell ti).simplyDeducible with
  | true =>
      simp only [hsd, ↓reduceIte, CertifiedReachResult.project]
      exact hσ₁
  | false =>
      simp only [hsd, Bool.false_eq_true, ↓reduceIte]
      refine Eq.trans
        (CertifiedReachResult.project_dite_bool
          ((c₂.state.getCell lIdx).simplyDeducible &&
            (c₂.state.getCell rIdx).simplyDeducible)
          (fun hcomp =>
            certifiedDiscoverDual c₂.state c₂.cert ti
              ((c₂.state.getCell lIdx).oldDeducible &&
                (c₂.state.getCell rIdx).oldDeducible)
              ((c₂.state.getCell lIdx).usesNew || (c₂.state.getCell rIdx).usesNew)
              .eta (RuleDeps.productEta lIdx rIdx)
              (fun _ =>
                RankedParents.pair_of_simplyDeducible c₂.cert lIdx rIdx
                  (bool_and_left hcomp) (bool_and_right hcomp)))
          c₂
          (c₂.state.discoverDual ti
            ((c₂.state.getCell lIdx).oldDeducible &&
              (c₂.state.getCell rIdx).oldDeducible)
            ((c₂.state.getCell lIdx).usesNew || (c₂.state.getCell rIdx).usesNew)
            .eta)
          c₂.project
          (fun hcomp =>
            certifiedDiscoverDual_project c₂.state c₂.cert ti
              ((c₂.state.getCell lIdx).oldDeducible &&
                (c₂.state.getCell rIdx).oldDeducible)
              ((c₂.state.getCell lIdx).usesNew || (c₂.state.getCell rIdx).usesNew)
              .eta (RuleDeps.productEta lIdx rIdx) _)
          rfl) ?_
      set σ₁ :=
        (σ.discoverDual lIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
          (.fstType ti)).discoverDual
          rIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.sndType ti)
      have heq : c₂.state = σ₁ := hσ₁
      cases hcomp :
          ((c₂.state.getCell lIdx).simplyDeducible &&
            (c₂.state.getCell rIdx).simplyDeducible) with
      | false =>
          simp only [hcomp, ↓reduceIte, heq]
          have hcomp' :
              ((σ₁.getCell lIdx).simplyDeducible &&
                (σ₁.getCell rIdx).simplyDeducible) = false := by
            simpa [← heq] using hcomp
          simp only [hcomp', ↓reduceIte]
          exact hσ₁
      | true =>
          simp only [hcomp, ↓reduceIte, heq]
          have hcomp' :
              ((σ₁.getCell lIdx).simplyDeducible &&
                (σ₁.getCell rIdx).simplyDeducible) = true := by
            simpa [← heq] using hcomp
          simp only [hcomp', ↓reduceIte, heq]

theorem certifiedProdTypeRule_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (ti : Nat) (L R : Object n) :
    (certifiedProdTypeRule σ cert ti L R).project = prodTypeRule σ ti L R := by
  unfold certifiedProdTypeRule
  cases hl : σ.findTypeIdx L with
  | none => simp [hl, prodTypeRule, CertifiedReachResult.project]
  | some lIdx =>
    cases hr : σ.findTypeIdx R with
    | none => simp [hl, hr, prodTypeRule, CertifiedReachResult.project]
    | some rIdx =>
        simp only [hl, hr]
        rw [certifiedProdTypeRule.go_project, prodTypeRule_eq_core σ ti L R hl hr]

def certifiedExpEtaRule {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (ti : Nat) (Ret : Object n) : CertifiedReachResult n :=
  if (σ.getCell ti).simplyDeducible then ⟨σ, cert⟩
  else
    match σ.findTypeIdx Ret with
    | none => ⟨σ, cert⟩
    | some rIdx =>
        if hret : (σ.getCell rIdx).simplyDeducible = true then
          certifiedDiscoverDual σ cert ti
            (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew .eta
            (RuleDeps.functionEta rIdx)
            (fun _ => RankedParents.singleton_of_simplyDeducible cert rIdx hret)
        else
          ⟨σ, cert⟩

theorem certifiedExpEtaRule_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (ti : Nat) (Ret : Object n) :
    (certifiedExpEtaRule σ cert ti Ret).project = expEtaRule σ ti Ret := by
  simp only [certifiedExpEtaRule, expEtaRule]
  cases (σ.getCell ti).simplyDeducible with
  | true => simp [CertifiedReachResult.project]
  | false =>
      simp only [Bool.not_false, ↓reduceIte]
      cases hr : σ.findTypeIdx Ret with
      | none => simp [hr, CertifiedReachResult.project]
      | some rIdx =>
          simp only [hr]
          exact CertifiedReachResult.project_dite_bool
            (σ.getCell rIdx).simplyDeducible
            (fun hret =>
              certifiedDiscoverDual σ cert ti
                (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew .eta
                (RuleDeps.functionEta rIdx)
                (fun _ => RankedParents.singleton_of_simplyDeducible cert rIdx hret))
            ⟨σ, cert⟩
            (σ.discoverDual ti (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew .eta)
            σ
            (fun hret =>
              certifiedDiscoverDual_project σ cert ti
                (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew .eta
                (RuleDeps.functionEta rIdx) _)
            rfl

/-- Ranked parents for `.appTy` under the neutral-function fire condition. -/
theorem RankedParents_of_expApp_fire {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (ti aIdx : Nat)
    (hfire :
      ((σ.getCell ti).oldNeutral && (σ.getCell aIdx).oldDeducible) = true ∨
        (((σ.getCell ti).oldNeutral && (σ.getCell aIdx).usesNew) ||
          ((σ.getCell ti).newNeutral && (σ.getCell aIdx).simplyDeducible)) = true) :
    RankedParents cert (RuleDeps.typeApp ti aIdx) := by
  have hfn : (σ.getCell ti).oldNeutral = true ∨ (σ.getCell ti).newNeutral = true := by
    cases hfire with
    | inl ho => exact Or.inl (bool_and_left ho)
    | inr hn =>
      cases Bool.or_eq_true_iff.mp hn with
      | inl hOldArg => exact Or.inl (bool_and_left hOldArg)
      | inr hNewArg => exact Or.inr (bool_and_left hNewArg)
  have harg : (σ.getCell aIdx).simplyDeducible = true := by
    cases hfire with
    | inl ho => exact simplyDeducible_of_oldDeducible _ (bool_and_right ho)
    | inr hn =>
      cases Bool.or_eq_true_iff.mp hn with
      | inl hOldArg =>
          have hu : (σ.getCell aIdx).usesNew = true := bool_and_right hOldArg
          have hnew : (σ.getCell aIdx).newWitness.isSome = true := hu
          simp [ReachCell.simplyDeducible, hnew]
      | inr hNewArg => exact bool_and_right hNewArg
  exact RankedParents.pair cert ti aIdx
    (cert.ranked_of_neutral ti hfn)
    (cert.ranked_of_simplyDeducible aIdx harg)

def certifiedExpAppRule {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (ti : Nat) (Arg Ret : Object n) : CertifiedReachResult n :=
  match σ.findTypeIdx Arg, σ.findTypeIdx Ret with
  | some aIdx, some rIdx =>
      let oldOk := (σ.getCell ti).oldNeutral && (σ.getCell aIdx).oldDeducible
      let newOk :=
        ((σ.getCell ti).oldNeutral && (σ.getCell aIdx).usesNew) ||
          ((σ.getCell ti).newNeutral && (σ.getCell aIdx).simplyDeducible)
      certifiedDiscoverDual σ cert rIdx oldOk newOk
        (.appTy ti aIdx) (RuleDeps.typeApp ti aIdx)
        (fun hfire => RankedParents_of_expApp_fire cert ti aIdx hfire)
  | _, _ => ⟨σ, cert⟩

theorem certifiedExpAppRule_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (ti : Nat) (Arg Ret : Object n) :
    (certifiedExpAppRule σ cert ti Arg Ret).project = expAppRule σ ti Arg Ret := by
  unfold certifiedExpAppRule expAppRule
  cases ha : σ.findTypeIdx Arg with
  | none => simp [ha, CertifiedReachResult.project]
  | some aIdx =>
    cases hr : σ.findTypeIdx Ret with
    | none => simp [ha, hr, CertifiedReachResult.project]
    | some rIdx =>
        simp only [ha, hr]
        exact certifiedDiscoverDual_project σ cert rIdx
          ((σ.getCell ti).oldNeutral && (σ.getCell aIdx).oldDeducible)
          (((σ.getCell ti).oldNeutral && (σ.getCell aIdx).usesNew) ||
            ((σ.getCell ti).newNeutral && (σ.getCell aIdx).simplyDeducible))
          (.appTy ti aIdx) (RuleDeps.typeApp ti aIdx) _

def certifiedCoprodTypeRule {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (ti : Nat) (L R : Object n) : CertifiedReachResult n :=
  if (σ.getCell ti).simplyDeducible then ⟨σ, cert⟩
  else
    match σ.findTypeIdx L, σ.findTypeIdx R with
    | some lIdx, some rIdx =>
        if hL : (σ.getCell lIdx).simplyDeducible = true then
          certifiedDiscoverDual σ cert ti
            (σ.getCell lIdx).oldDeducible (σ.getCell lIdx).usesNew
            (.inl lIdx) (RuleDeps.coprodIntro lIdx)
            (fun _ => RankedParents.singleton_of_simplyDeducible cert lIdx hL)
        else if hR : (σ.getCell rIdx).simplyDeducible = true then
          certifiedDiscoverDual σ cert ti
            (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew
            (.inr rIdx) (RuleDeps.coprodIntro rIdx)
            (fun _ => RankedParents.singleton_of_simplyDeducible cert rIdx hR)
        else
          ⟨σ, cert⟩
    | _, _ => ⟨σ, cert⟩

theorem certifiedCoprodTypeRule_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (ti : Nat) (L R : Object n) :
    (certifiedCoprodTypeRule σ cert ti L R).project = coprodTypeRule σ ti L R := by
  simp only [certifiedCoprodTypeRule, coprodTypeRule]
  cases (σ.getCell ti).simplyDeducible with
  | true => simp [CertifiedReachResult.project]
  | false =>
      simp only [Bool.not_false, ↓reduceIte]
      cases hl : σ.findTypeIdx L with
      | none => simp [hl, CertifiedReachResult.project]
      | some lIdx =>
        cases hr : σ.findTypeIdx R with
        | none => simp [hl, hr, CertifiedReachResult.project]
        | some rIdx =>
            simp only [hl, hr]
            refine Eq.trans
              (CertifiedReachResult.project_dite_bool
                (σ.getCell lIdx).simplyDeducible
                (fun hL =>
                  certifiedDiscoverDual σ cert ti
                    (σ.getCell lIdx).oldDeducible (σ.getCell lIdx).usesNew
                    (.inl lIdx) (RuleDeps.coprodIntro lIdx)
                    (fun _ => RankedParents.singleton_of_simplyDeducible cert lIdx hL))
                (if hR : (σ.getCell rIdx).simplyDeducible = true then
                  certifiedDiscoverDual σ cert ti
                    (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew
                    (.inr rIdx) (RuleDeps.coprodIntro rIdx)
                    (fun _ => RankedParents.singleton_of_simplyDeducible cert rIdx hR)
                 else ⟨σ, cert⟩)
                (σ.discoverDual ti (σ.getCell lIdx).oldDeducible
                  (σ.getCell lIdx).usesNew (.inl lIdx))
                (if (σ.getCell rIdx).simplyDeducible then
                  σ.discoverDual ti (σ.getCell rIdx).oldDeducible
                    (σ.getCell rIdx).usesNew (.inr rIdx)
                 else σ)
                (fun hL =>
                  certifiedDiscoverDual_project σ cert ti
                    (σ.getCell lIdx).oldDeducible (σ.getCell lIdx).usesNew
                    (.inl lIdx) (RuleDeps.coprodIntro lIdx) _)
                (CertifiedReachResult.project_dite_bool
                  (σ.getCell rIdx).simplyDeducible
                  (fun hR =>
                    certifiedDiscoverDual σ cert ti
                      (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew
                      (.inr rIdx) (RuleDeps.coprodIntro rIdx)
                      (fun _ =>
                        RankedParents.singleton_of_simplyDeducible cert rIdx hR))
                  ⟨σ, cert⟩
                  (σ.discoverDual ti (σ.getCell rIdx).oldDeducible
                    (σ.getCell rIdx).usesNew (.inr rIdx))
                  σ
                  (fun hR =>
                    certifiedDiscoverDual_project σ cert ti
                      (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew
                      (.inr rIdx) (RuleDeps.coprodIntro rIdx) _)
                  rfl))
              rfl

def certifiedTypeRule {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (ti : Nat) : CertifiedReachResult n :=
  match σ.typeAt ti with
  | some (.prod L R) => certifiedProdTypeRule σ cert ti L R
  | some (.exp Arg Ret) =>
      let c₁ := certifiedExpEtaRule σ cert ti Ret
      certifiedExpAppRule c₁.state c₁.cert ti Arg Ret
  | some (.coprod L R) => certifiedCoprodTypeRule σ cert ti L R
  | _ => ⟨σ, cert⟩

theorem certifiedTypeRule_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (ti : Nat) :
    (certifiedTypeRule σ cert ti).project = typeRule σ ti := by
  unfold certifiedTypeRule typeRule
  cases hA : σ.typeAt ti with
  | none => rfl
  | some A =>
      cases A with
      | prod L R => exact certifiedProdTypeRule_project σ cert ti L R
      | exp Arg Ret =>
          have h₁ := certifiedExpEtaRule_project σ cert ti Ret
          have h₂ := certifiedExpAppRule_project
            (certifiedExpEtaRule σ cert ti Ret).state
            (certifiedExpEtaRule σ cert ti Ret).cert ti Arg Ret
          simp only [CertifiedReachResult.project] at h₁ h₂ ⊢
          rw [h₂, h₁]
      | coprod L R => exact certifiedCoprodTypeRule_project σ cert ti L R
      | _ => rfl

/-! ## Certified sweep / step / runner -/

def certifiedFoldl {n : Nat} {α : Type}
    (f : CertifiedReachResult n → α → CertifiedReachResult n)
    (l : List α) (c : CertifiedReachResult n) : CertifiedReachResult n :=
  l.foldl f c

theorem certifiedFoldl_project {n : Nat} {α : Type}
    (f : CertifiedReachResult n → α → CertifiedReachResult n)
    (g : ReachState n → α → ReachState n)
    (hg : ∀ (c : CertifiedReachResult n) (a : α), (f c a).project = g c.project a)
    (l : List α) (c : CertifiedReachResult n) :
    (certifiedFoldl f l c).project = l.foldl g c.project := by
  induction l generalizing c with
  | nil => rfl
  | cons a rest ih =>
      simp only [certifiedFoldl, List.foldl]
      rw [← hg c a]
      exact ih (f c a)

def certifiedReachSweep {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) : CertifiedReachResult n :=
  let c0 : CertifiedReachResult n := ⟨σ, cert⟩
  let cSeed := certifiedFoldl
    (fun c i => certifiedSeedHypRule Γ c.state c.cert i) (List.range Γ.hyps.size) c0
  let cUnit := certifiedUnitEtaRule cSeed.state cSeed.cert
  certifiedFoldl (fun c i => certifiedHypRule Γ c.state c.cert i)
    (List.range Γ.hyps.size) cUnit

theorem certifiedReachSweep_project {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) :
    (certifiedReachSweep Γ σ cert).project = reachSweep Γ σ := by
  unfold certifiedReachSweep reachSweep
  have hSeed := certifiedFoldl_project
    (fun c i => certifiedSeedHypRule Γ c.state c.cert i) (seedHypRule Γ)
    (fun c i => certifiedSeedHypRule_project Γ c.state c.cert i)
    (List.range Γ.hyps.size) (⟨σ, cert⟩ : CertifiedReachResult n)
  set cSeed := certifiedFoldl
    (fun c i => certifiedSeedHypRule Γ c.state c.cert i) (List.range Γ.hyps.size)
    (⟨σ, cert⟩ : CertifiedReachResult n)
  have hUnit := certifiedUnitEtaRule_project cSeed.state cSeed.cert
  set cUnit := certifiedUnitEtaRule cSeed.state cSeed.cert
  have hHyp := certifiedFoldl_project
    (fun c i => certifiedHypRule Γ c.state c.cert i) (hypRule Γ)
    (fun c i => certifiedHypRule_project Γ c.state c.cert i)
    (List.range Γ.hyps.size) cUnit
  simp only [CertifiedReachResult.project] at hSeed hUnit hHyp ⊢
  rw [hHyp, hUnit, hSeed]

def certifiedReachStep {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) : CertifiedReachResult n :=
  let cSweep := certifiedReachSweep Γ σ cert
  certifiedFoldl (fun c ti => certifiedTypeRule c.state c.cert ti)
    (List.range cSweep.state.types.size) cSweep

theorem certifiedReachStep_project {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) :
    (certifiedReachStep Γ σ cert).project = reachStep Γ σ := by
  unfold certifiedReachStep reachStep
  have hSweep := certifiedReachSweep_project Γ σ cert
  set cSweep := certifiedReachSweep Γ σ cert
  have hsize : cSweep.state.types.size = (reachSweep Γ σ).types.size := by
    simp only [← hSweep, CertifiedReachResult.project]
  have hType := certifiedFoldl_project
    (fun c ti => certifiedTypeRule c.state c.cert ti) typeRule
    (fun c ti => certifiedTypeRule_project c.state c.cert ti)
    (List.range cSweep.state.types.size) cSweep
  simp only [CertifiedReachResult.project] at hSweep hType ⊢
  rw [hType, hsize, hSweep]

/-- Empty certificate for a freshly allocated cell table. -/
def ReachRankCert.emptyTable {n : Nat} (types : Array (Object n)) :
    ReachRankCert
      ({ types := types
         cells := Array.replicate types.size ReachCell.empty
         inconsistent := false } : ReachState n) :=
  ReachRankCert.empty _
    (fun i => by
      simp only [ReachState.getCell, Array.getElem?_replicate]
      split_ifs <;> simp [Option.getD, ReachCell.empty])
    (fun i => by
      simp only [ReachState.getCell, Array.getElem?_replicate]
      split_ifs <;> simp [Option.getD, ReachCell.empty])

def certifiedMkReachState {n : Nat} (Γ : ReachCtx n) (goal : Object n) :
    CertifiedReachResult n :=
  let types := subformulaClosure (Γ.roots goal)
  let σ0 : ReachState n :=
    { types := types
      cells := Array.replicate types.size ReachCell.empty
      inconsistent := false }
  certifiedFoldl (fun c i => certifiedSeedHypRule Γ c.state c.cert i)
    (List.range Γ.hyps.size) ⟨σ0, ReachRankCert.emptyTable types⟩

theorem certifiedMkReachState_project {n : Nat} (Γ : ReachCtx n) (goal : Object n) :
    (certifiedMkReachState Γ goal).project = mkReachState Γ goal := by
  unfold certifiedMkReachState mkReachState
  exact certifiedFoldl_project
    (fun c i => certifiedSeedHypRule Γ c.state c.cert i) (seedHypRule Γ)
    (fun c i => certifiedSeedHypRule_project Γ c.state c.cert i) _ _

def certifiedRunReachabilityFrom {n : Nat} (Γ : ReachCtx n)
    (c : CertifiedReachResult n) : CertifiedReachResult n :=
  if c.state.weight < (certifiedReachStep Γ c.state c.cert).state.weight then
    certifiedRunReachabilityFrom Γ (certifiedReachStep Γ c.state c.cert)
  else
    certifiedReachStep Γ c.state c.cert
termination_by c.state.capacity - c.state.weight
decreasing_by
  rename_i hlt
  have hproj := certifiedReachStep_project Γ c.state c.cert
  have hcap :
      (certifiedReachStep Γ c.state c.cert).state.capacity = c.state.capacity := by
    have hs := (reachStep_le Γ c.state).size
    simp only [ReachState.capacity]
    have : (certifiedReachStep Γ c.state c.cert).state.cells.size = c.state.cells.size := by
      change (certifiedReachStep Γ c.state c.cert).project.cells.size = c.state.cells.size
      rw [hproj]; exact hs.symm
    simp [this]
  have hbound :=
    ReachState.weight_le_capacity (certifiedReachStep Γ c.state c.cert).state
  omega

theorem certifiedRunReachabilityFrom_project {n : Nat} (Γ : ReachCtx n)
    (c : CertifiedReachResult n) :
    (certifiedRunReachabilityFrom Γ c).project =
      runReachabilityFrom Γ c.project := by
  induction c using certifiedRunReachabilityFrom.induct (Γ := Γ) with
  | case1 c hlt ih =>
      have hstep := certifiedReachStep_project Γ c.state c.cert
      rw [certifiedRunReachabilityFrom, if_pos hlt, runReachabilityFrom]
      have hlt' : c.project.weight < (reachStep Γ c.project).weight := by
        simp only [CertifiedReachResult.project] at hlt hstep ⊢
        rwa [← hstep]
      rw [if_pos hlt']
      simpa [← hstep, CertifiedReachResult.project] using ih
  | case2 c hlt =>
      have hstep := certifiedReachStep_project Γ c.state c.cert
      rw [certifiedRunReachabilityFrom, if_neg hlt, runReachabilityFrom]
      have hlt' : ¬ c.project.weight < (reachStep Γ c.project).weight := by
        simp only [CertifiedReachResult.project] at hlt hstep ⊢
        rwa [← hstep]
      rw [if_neg hlt']
      simpa [← hstep, CertifiedReachResult.project] using hstep

/-- Fully certified reachability runner. Projects to `runReachability`. -/
def certifiedRunReachability {n : Nat} (Γ : ReachCtx n) (goal : Object n) :
    CertifiedReachResult n :=
  certifiedRunReachabilityFrom Γ (certifiedMkReachState Γ goal)

theorem certifiedRunReachability_project {n : Nat} (Γ : ReachCtx n)
    (goal : Object n) :
    (certifiedRunReachability Γ goal).project = runReachability Γ goal := by
  unfold certifiedRunReachability runReachability
  rw [certifiedRunReachabilityFrom_project, certifiedMkReachState_project]

theorem certifiedRunReachability_soundFor {n : Nat} (Γ : ReachCtx n)
    (goal : Object n) :
    (certifiedRunReachability Γ goal).soundFor Γ goal :=
  certifiedRunReachability_project Γ goal

/-! ## Status

**Landed:** proof-only full-rank certificates; centralized `RuleDeps`; certified
wrappers for every forward-chaining rule; `certifiedReachSweep` /
`certifiedReachStep` / `certifiedRunReachability` with
`project = runReachability`.

**Stop condition:** a fresh slot is ranked only under `RankedParents` for the
deps of **that** derivation (`RuleDeps`); missing parents make the certified
term uninhabited.

**Source of truth (intended final):** `certifiedRunReachability` is the retained
engine; computational `runReachability` stays as the projection reference until
the post-`ReconstructTotalityPackage` cleanup collapses the mirror.

**Next stage (not this pass):** well-founded reconstruction / totality package.
Afterwards: delete superseded measure demos, collapse duplicate wrappers, remove
fueled reconstruct once callers migrate — target a net-negative cleanup commit.
-/

/-! ## Totality scope (neutral only)

`ReconstructWitnessTotal` / `StoredWitnessReconstructs` restrict to
`Witness.isNeutral`. Intro-only `.unit` / `.inl` / `.inr` / `.eta` must **not**
be over-quantified into `neuOfType` success — they justify invertible arguments
only (`Witness.isNeutral = false`).
-/

theorem Witness.not_neutral_unit : Witness.isNeutral .unit = false := rfl
theorem Witness.not_neutral_eta : Witness.isNeutral .eta = false := rfl
theorem Witness.not_neutral_inl (i : Nat) : Witness.isNeutral (.inl i) = false := rfl
theorem Witness.not_neutral_inr (i : Nat) : Witness.isNeutral (.inr i) = false := rfl

/-! ## Migration-cost comparison (spike conclusion)

| Design | Pros | Cons | Verdict |
|---|---|---|---|
| **A. Proof-only `ReachRankCert` / certified runner** | No contamination of `ReachCell` equality; `project` = `runReachability` | Temporary control-flow mirror until cleanup | **Preferred** — now landed |
| **B. Runtime `discoverGen`** | Easy local WF | Contaminates equality | Rejected |
| **C. Structural derivation trees** | Intrinsic WF | Heavier API | Defer |

**Final source of truth:** `certifiedRunReachability`. After totality, collapse the
computational mirror so only one engine remains.
-/

end Equality
end Gimbal
