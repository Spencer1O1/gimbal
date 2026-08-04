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

/-! ## Certificate extension — intended API (unproved in this checkpoint)

Next sticky obligation (no `sorry` placeholder):

```
ParentsCertified cert w  :=
  ∀ p ∈ w.cellParents, ∃ bP rP, cert.rank p bP = some rP

ReachRankCert.extend :
  occupied slot → cert unchanged (state also unchanged by assign-once);
  fresh neutral slot → pick r > every parent rank, extend cert.

certifiedMarkHyp / certifiedDiscover / certifiedDiscoverDual
  project definitionally to markHyp / discover / discoverDual.
```

Individual reachability rules should delegate to `certifiedDiscover`, not
re-prove parent lookup per rule. Stop if a rule inserts a witness whose parents
are not already certified — that is an operational dependency bug.
-/

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

/-- Strict upper bound for a fresh rank given certified parents. -/
def ParentsCertified.freshRank {n : Nat} {σ : ReachState n}
    {cert : ReachRankCert σ} {w : Witness}
    (_h : ParentsCertified cert w) : Nat :=
  (Witness.cellParents w).foldl
    (fun acc p =>
      match cert.rankOfPreferred p with
      | some r => Nat.max acc (r + 1)
      | none => acc)
    0

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

/-! ## Inconsistent completed state → reconstructible `.never`

Soundness: `ReachSound` already ties `inconsistent` to a declarative deduction
of `0`. The certificate must additionally ensure a **neutral** stored witness
for `.never` (typically `.ctxVar` of a `never` hyp, or a neutral derivation).

Scoped Prop (same as `InconsistentNeverTotal` in `ReconstructTotal`):
-/

theorem InconsistentNeverTotal_of_ranked_package {sig : Signature}
    (h : ReconstructTotalityPackage sig) : InconsistentNeverTotal sig :=
  h.2.2

/-! ## Migration-cost comparison (spike conclusion)

| Design | Pros | Cons | Verdict |
|---|---|---|---|
| **A. Proof-only `ReachRankCert` / certified runner** | No contamination of `ReachCell` equality, schedule identity, or observation identity; `project` = existing `runReachability` state | Must thread certificates through every `markHyp`/`discover` rule; `setCell` transport lemmas are sticky | **Preferred** if maintainable |
| **B. Runtime `discoverGen` on `ReachCell`/`Witness`** | Local measure at each record site; easy WF | Must exclude gen from semantic equality, canonical scheduling, `PairEntry`/`Witness` identity; risks leaking into compare | Use **only if A is unmaintainable** |
| **C. Structural derivation trees** | Intrinsic WF; no parallel rank map | Heavier than current parent-pointer witnesses; changes reconstruction API | Possible long-term; not needed if A works |

**Spike recommendation:** pursue **A**. Assign-once makes rank stable. Parent
relation is small and closed. Lex measure handles the `.fst`/`.snd` size
increase. Next sticky work (not this spike): finish `extendFresh`, certify all
rules, build `certifiedRunReachability` with `soundFor`, then prove
`ReconstructTotalityPackage` by well-founded recursion on `reconMeasure`.

Dependency once A lands:
`certified reachability → ranked witness graph → reconstruction totality →
retained schedule adapter → certified producer → EncodeTotal`.
-/

/-! ## Spike status

**Landed (proved scaffolding, no `sorry`):**
* assign-once theorems (`record_keeps_*` / `record_sets_*`)
* `Witness.cellParents` for every constructor
* `ReachRankCert` / `CertifiedReachResult` / `project`
* `ParentsCertified` / `ParentsCertified_ctxVar` / `freshRank`
* lex `reconMeasure` with `.fst` and `.appTy` / `invOf` decrease demos
* neutral-only scope; intro forms excluded
* migration comparison → prefer proof-only runner

**Next (certificate extension, still before adapter/EncodeTotal):**
* generic `ReachRankCert.extend` (occupied vs fresh)
* `certifiedMarkHyp` / `certifiedDiscover` / dual-fire
* sweep preservation + `certifiedRunReachability`
* `ReconstructTotalityPackage` via WF on `reconMeasure`
-/

end Equality
end Gimbal
