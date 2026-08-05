/-
  Proof-only reachability rank certificates around `runReachability`.

  Retains a well-founded discovery certificate without adding observable
  `discoverGen` fields to `ReachCell` / `Witness`. Operational state, schedule
  identity, and fixed-point equality stay unchanged: `certifiedRunReachability`
  projects to `runReachability`.

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

/-! ## Parent relation (reconstruction-relevant cell indices)

Parents are **type-table indices** that `reconstructGoWF` may follow via
`.neuOf` / cell witnesses. Hypothesis indices (`.ctxVar`, `.app`'s fn hyp) are
not cell parents — they resolve through `Ctx.varOldest` / hyps.
-/

/--
Proof-only reconstruction dependencies of a witness shape (index fields + the
cells `invOf` / `neuOf` must already have ranked).

This is **not** “immediate calls in `reconstructGoWF` only”:
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

end RuleDeps

/-! ## Local object measure (intro / `invOf` decrease) -/

def reconObjectSize {n : Nat} : Object n → Nat
  | .base _ | .never | .unit => 1
  | .prod A B | .coprod A B | .exp A B =>
      reconObjectSize A + reconObjectSize B + 1

theorem reconObjectSize_prod_left_lt {n : Nat} (L R : Object n) :
    reconObjectSize L < reconObjectSize (.prod L R) := by
  simp [reconObjectSize]; try omega

theorem reconObjectSize_prod_right_lt {n : Nat} (L R : Object n) :
    reconObjectSize R < reconObjectSize (.prod L R) := by
  simp [reconObjectSize]; try omega

theorem reconObjectSize_exp_ret_lt {n : Nat} (Arg Ret : Object n) :
    reconObjectSize Ret < reconObjectSize (.exp Arg Ret) := by
  simp [reconObjectSize]; try omega

theorem reconObjectSize_coprod_left_lt {n : Nat} (L R : Object n) :
    reconObjectSize L < reconObjectSize (.coprod L R) := by
  simp [reconObjectSize]; try omega

theorem reconObjectSize_coprod_right_lt {n : Nat} (L R : Object n) :
    reconObjectSize R < reconObjectSize (.coprod L R) := by
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

/-! ## Proof-only rank certificate -/

/-- Provenance slot: `true` = uses-new, `false` = old-only. -/
abbrev SlotNew : Type := Bool

def ReachCell.slotWitness (c : ReachCell) (b : SlotNew) : Option Witness :=
  if b then c.newWitness else c.oldWitness

/--
Parameterized neutral-parent obligation (rank function + cell table).
Carried by certificates; stronger than `parents_lt` (which may name an η slot).
-/
def NeutralParentLtCore (rank : Nat → SlotNew → Option Nat)
    (getCell : Nat → ReachCell) (childRank : Nat) : Witness → Prop
  | .fstType p =>
      ∃ (bP : SlotNew) (wP : Witness) (rP : Nat),
        (getCell p).slotWitness bP = some wP ∧
          Witness.isNeutral wP = true ∧
          rank p bP = some rP ∧ rP < childRank
  | .sndType p =>
      ∃ (bP : SlotNew) (wP : Witness) (rP : Nat),
        (getCell p).slotWitness bP = some wP ∧
          Witness.isNeutral wP = true ∧
          rank p bP = some rP ∧ rP < childRank
  | .appTy fn _arg =>
      ∃ (bP : SlotNew) (wP : Witness) (rP : Nat),
        (getCell fn).slotWitness bP = some wP ∧
          Witness.isNeutral wP = true ∧
          rank fn bP = some rP ∧ rP < childRank
  | .ctxVar _ | .fstHyp _ | .sndHyp _ | .app _ _ | .inl _ | .inr _ | .unit | .eta =>
      True

theorem NeutralParentLtCore.trivial
    (rank : Nat → SlotNew → Option Nat) (getCell : Nat → ReachCell)
    (childRank : Nat) {w : Witness}
    (h : match w with
        | .fstType _ | .sndType _ | .appTy _ _ => False
        | _ => True) :
    NeutralParentLtCore rank getCell childRank w := by
  cases w with
  | fstType _ | sndType _ | appTy _ _ => exact False.elim h
  | ctxVar _ | fstHyp _ | sndHyp _ | app _ _ | inl _ | inr _ | unit | eta =>
      exact True.intro

/-- Fire-time: elim witnesses require a currently neutral parent cell. -/
def NeutralParentPremise {n : Nat} (σ : ReachState n) : Witness → Prop
  | .fstType p =>
      (σ.getCell p).oldNeutral = true ∨ (σ.getCell p).newNeutral = true
  | .sndType p =>
      (σ.getCell p).oldNeutral = true ∨ (σ.getCell p).newNeutral = true
  | .appTy fn _arg =>
      (σ.getCell fn).oldNeutral = true ∨ (σ.getCell fn).newNeutral = true
  | .ctxVar _ | .fstHyp _ | .sndHyp _ | .app _ _ | .inl _ | .inr _ | .unit | .eta =>
      True

theorem NeutralParentPremise.trivial {n : Nat} (σ : ReachState n) {w : Witness}
    (h : match w with
        | .fstType _ | .sndType _ | .appTy _ _ => False
        | _ => True) :
    NeutralParentPremise σ w := by
  cases w with
  | fstType _ | sndType _ | appTy _ _ => exact False.elim h
  | ctxVar _ | fstHyp _ | sndHyp _ | app _ _ | inl _ | inr _ | unit | eta =>
      exact True.intro

/-- Elim parent index must appear in the certified deps list. -/
def Witness.elimParent_mem (deps : List Nat) : Witness → Prop
  | .fstType p | .sndType p => p ∈ deps
  | .appTy fn _ => fn ∈ deps
  | .ctxVar _ | .fstHyp _ | .sndHyp _ | .app _ _ | .inl _ | .inr _ | .unit | .eta =>
      True

theorem Witness.elimParent_mem_trivial (deps : List Nat) {w : Witness}
    (h : match w with
        | .fstType _ | .sndType _ | .appTy _ _ => False
        | _ => True) :
    Witness.elimParent_mem deps w := by
  cases w with
  | fstType _ | sndType _ | appTy _ _ => exact False.elim h
  | ctxVar _ | fstHyp _ | sndHyp _ | app _ _ | inl _ | inr _ | unit | eta =>
      exact True.intro

theorem Witness.elimParent_mem_typeProj (p : Nat) :
    Witness.elimParent_mem (RuleDeps.typeProj p) (.fstType p) ∧
      Witness.elimParent_mem (RuleDeps.typeProj p) (.sndType p) := by
  simp [Witness.elimParent_mem, RuleDeps.typeProj]

theorem Witness.elimParent_mem_typeApp (fn arg : Nat) :
    Witness.elimParent_mem (RuleDeps.typeApp fn arg) (.appTy fn arg) := by
  simp [Witness.elimParent_mem, RuleDeps.typeApp]

/--
Centralized dependency-content invariant: a stored witness at cell `i` must carry
exactly the `RuleDeps` list for that rule, with η cases validated against
`σ.typeAt i` and component/return lookups.
-/
def WitnessDepsOk {n : Nat} (σ : ReachState n) (i : Nat) : Witness → List Nat → Prop
  | .ctxVar _, ps => ps = RuleDeps.ctxVar
  | .fstHyp _, ps | .sndHyp _, ps => ps = RuleDeps.hypProj
  | .fstType p, ps | .sndType p, ps => ps = RuleDeps.typeProj p
  | .app _argHyp arg, ps => ps = RuleDeps.hypApp arg
  | .appTy fn arg, ps => ps = RuleDeps.typeApp fn arg
  | .inl p, ps =>
      match σ.typeAt i with
      | some (.coprod L _R) =>
          ps = RuleDeps.coprodIntro p ∧ σ.typeAt p = some L
      | _ => False
  | .inr p, ps =>
      match σ.typeAt i with
      | some (.coprod _L R) =>
          ps = RuleDeps.coprodIntro p ∧ σ.typeAt p = some R
      | _ => False
  | .unit, ps => ps = RuleDeps.unit
  | .eta, ps =>
      match σ.typeAt i with
      | some (.prod L R) =>
          ∃ lIdx rIdx,
            ps = RuleDeps.productEta lIdx rIdx ∧
              σ.typeAt lIdx = some L ∧ σ.typeAt rIdx = some R
      | some (.exp _Arg Ret) =>
          ∃ retIdx, ps = RuleDeps.functionEta retIdx ∧ σ.typeAt retIdx = some Ret
      | _ => False

theorem WitnessDepsOk.elimParent_mem {n : Nat} {σ : ReachState n}
    {i : Nat} {w : Witness} {ps : List Nat}
    (h : WitnessDepsOk σ i w ps) : Witness.elimParent_mem ps w := by
  cases w with
  | ctxVar _ | fstHyp _ | sndHyp _ | app _ _ | inl _ | inr _ | unit | eta =>
      exact True.intro
  | fstType p =>
      change ps = RuleDeps.typeProj p at h
      simpa [Witness.elimParent_mem, h, RuleDeps.typeProj]
  | sndType p =>
      change ps = RuleDeps.typeProj p at h
      simpa [Witness.elimParent_mem, h, RuleDeps.typeProj]
  | appTy fn arg =>
      change ps = RuleDeps.typeApp fn arg at h
      simpa [Witness.elimParent_mem, h, RuleDeps.typeApp]

theorem WitnessDepsOk.unit {n : Nat} (σ : ReachState n) (i : Nat) :
    WitnessDepsOk σ i .unit RuleDeps.unit := rfl

theorem WitnessDepsOk.ctxVar {n : Nat} (σ : ReachState n) (i hypIdx : Nat) :
    WitnessDepsOk σ i (.ctxVar hypIdx) RuleDeps.ctxVar := rfl

theorem WitnessDepsOk.fstHyp {n : Nat} (σ : ReachState n) (i hypIdx : Nat) :
    WitnessDepsOk σ i (.fstHyp hypIdx) RuleDeps.hypProj := rfl

theorem WitnessDepsOk.sndHyp {n : Nat} (σ : ReachState n) (i hypIdx : Nat) :
    WitnessDepsOk σ i (.sndHyp hypIdx) RuleDeps.hypProj := rfl

theorem WitnessDepsOk.fstType {n : Nat} (σ : ReachState n) (i p : Nat) :
    WitnessDepsOk σ i (.fstType p) (RuleDeps.typeProj p) := rfl

theorem WitnessDepsOk.sndType {n : Nat} (σ : ReachState n) (i p : Nat) :
    WitnessDepsOk σ i (.sndType p) (RuleDeps.typeProj p) := rfl

theorem WitnessDepsOk.app {n : Nat} (σ : ReachState n) (i fnHyp arg : Nat) :
    WitnessDepsOk σ i (.app fnHyp arg) (RuleDeps.hypApp arg) := rfl

theorem WitnessDepsOk.appTy {n : Nat} (σ : ReachState n) (i fn arg : Nat) :
    WitnessDepsOk σ i (.appTy fn arg) (RuleDeps.typeApp fn arg) := rfl

theorem WitnessDepsOk.inl {n : Nat} {σ : ReachState n} {i p : Nat}
    {L R : Object n}
    (hty : σ.typeAt i = some (.coprod L R))
    (hL : σ.typeAt p = some L) :
    WitnessDepsOk σ i (.inl p) (RuleDeps.coprodIntro p) := by
  dsimp [WitnessDepsOk]
  simp [hty, hL]

theorem WitnessDepsOk.inr {n : Nat} {σ : ReachState n} {i p : Nat}
    {L R : Object n}
    (hty : σ.typeAt i = some (.coprod L R))
    (hR : σ.typeAt p = some R) :
    WitnessDepsOk σ i (.inr p) (RuleDeps.coprodIntro p) := by
  dsimp [WitnessDepsOk]
  simp [hty, hR]

theorem WitnessDepsOk.eta_prod {n : Nat} {σ : ReachState n} {i lIdx rIdx : Nat}
    {L R : Object n}
    (hty : σ.typeAt i = some (.prod L R))
    (hL : σ.typeAt lIdx = some L) (hR : σ.typeAt rIdx = some R) :
    WitnessDepsOk σ i .eta (RuleDeps.productEta lIdx rIdx) := by
  dsimp [WitnessDepsOk]
  simp only [hty]
  exact ⟨lIdx, rIdx, rfl, hL, hR⟩

theorem WitnessDepsOk.eta_exp {n : Nat} {σ : ReachState n} {i retIdx : Nat}
    {Arg Ret : Object n}
    (hty : σ.typeAt i = some (.exp Arg Ret))
    (hRet : σ.typeAt retIdx = some Ret) :
    WitnessDepsOk σ i .eta (RuleDeps.functionEta retIdx) := by
  dsimp [WitnessDepsOk]
  simp only [hty]
  exact ⟨retIdx, rfl, hRet⟩

theorem WitnessDepsOk.of_types_eq {n : Nat} {σ τ : ReachState n}
    (ht : ∀ j, τ.typeAt j = σ.typeAt j) {i : Nat} {w : Witness} {ps : List Nat}
    (h : WitnessDepsOk σ i w ps) : WitnessDepsOk τ i w ps := by
  cases w with
  | ctxVar _ | fstHyp _ | sndHyp _ | fstType _ | sndType _ | app _ _ | appTy _ _
    | unit => exact h
  | inl p =>
      dsimp [WitnessDepsOk] at h ⊢
      rw [ht i]
      cases hty : σ.typeAt i with
      | none => simp [hty] at h
      | some A =>
          simp only [hty] at h ⊢
          cases A with
          | coprod L R =>
              obtain ⟨hps, hL⟩ := h
              exact ⟨hps, (ht p).trans hL⟩
          | _ => exact h
  | inr p =>
      dsimp [WitnessDepsOk] at h ⊢
      rw [ht i]
      cases hty : σ.typeAt i with
      | none => simp [hty] at h
      | some A =>
          simp only [hty] at h ⊢
          cases A with
          | coprod L R =>
              obtain ⟨hps, hR⟩ := h
              exact ⟨hps, (ht p).trans hR⟩
          | _ => exact h
  | eta =>
      dsimp [WitnessDepsOk] at h ⊢
      rw [ht i]
      cases hty : σ.typeAt i with
      | none => simp [hty] at h
      | some A =>
          simp only [hty] at h ⊢
          cases A with
          | prod L R =>
              obtain ⟨lIdx, rIdx, hps, hL, hR⟩ := h
              exact ⟨lIdx, rIdx, hps, (ht lIdx).trans hL, (ht rIdx).trans hR⟩
          | exp Arg Ret =>
              obtain ⟨retIdx, hps, hRet⟩ := h
              exact ⟨retIdx, hps, (ht retIdx).trans hRet⟩
          | _ => exact h

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
  /-- Stored elim witnesses have an actual lower-ranked neutral parent. -/
  neutralParent_lt :
    ∀ (i : Nat) (b : SlotNew) (r : Nat) (w : Witness),
      rank i b = some r →
        (σ.getCell i).slotWitness b = some w →
          NeutralParentLtCore rank (fun j => (σ.getCell j)) r w
  /-- Occupied slots carry the centralized `RuleDeps` explanation for their witness. -/
  deps_sound :
    ∀ (i : Nat) (b : SlotNew) (w : Witness),
      (σ.getCell i).slotWitness b = some w →
        WitnessDepsOk σ i w (deps i b)
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
  neutralParent_lt := by
    intro i b r w hr hw
    have ⟨ho, hn⟩ := h i
    cases b <;> simp [ReachCell.slotWitness, ho, hn] at hw
  deps_sound := by
    intro i b w hw
    have ⟨ho, hn⟩ := h i
    cases b <;> simp [ReachCell.slotWitness, ho, hn] at hw
  retrievable_witnessed := by
    intro i hr
    rw [hret i] at hr
    cases hr

/-! ## Structural dependency content from `deps_sound`

Stored η / coprod-intro witnesses expose their component or payload indices in
`cert.deps`. Combined with `parents_lt`, each required structural recursive
call has a ranked parent strictly below the child rank.
-/

theorem ReachRankCert.deps_of_eta_prod {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) {i : Nat} {b : SlotNew} {L R : Object n}
    (hw : (σ.getCell i).slotWitness b = some .eta)
    (hty : σ.typeAt i = some (.prod L R)) :
    ∃ lIdx rIdx,
      cert.deps i b = RuleDeps.productEta lIdx rIdx ∧
        σ.typeAt lIdx = some L ∧ σ.typeAt rIdx = some R := by
  have h := cert.deps_sound i b .eta hw
  dsimp [WitnessDepsOk] at h
  simpa [hty] using h

theorem ReachRankCert.deps_of_eta_exp {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) {i : Nat} {b : SlotNew} {Arg Ret : Object n}
    (hw : (σ.getCell i).slotWitness b = some .eta)
    (hty : σ.typeAt i = some (.exp Arg Ret)) :
    ∃ retIdx,
      cert.deps i b = RuleDeps.functionEta retIdx ∧
        σ.typeAt retIdx = some Ret := by
  have h := cert.deps_sound i b .eta hw
  dsimp [WitnessDepsOk] at h
  simpa [hty] using h

theorem ReachRankCert.deps_of_inl {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) {i : Nat} {b : SlotNew} {p : Nat}
    {L R : Object n}
    (hw : (σ.getCell i).slotWitness b = some (.inl p))
    (hty : σ.typeAt i = some (.coprod L R)) :
    cert.deps i b = RuleDeps.coprodIntro p ∧ σ.typeAt p = some L := by
  have h := cert.deps_sound i b (.inl p) hw
  dsimp [WitnessDepsOk] at h
  simpa [hty] using h

theorem ReachRankCert.deps_of_inr {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) {i : Nat} {b : SlotNew} {p : Nat}
    {L R : Object n}
    (hw : (σ.getCell i).slotWitness b = some (.inr p))
    (hty : σ.typeAt i = some (.coprod L R)) :
    cert.deps i b = RuleDeps.coprodIntro p ∧ σ.typeAt p = some R := by
  have h := cert.deps_sound i b (.inr p) hw
  dsimp [WitnessDepsOk] at h
  simpa [hty] using h

theorem ReachRankCert.ranked_parents_of_eta_prod {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) {i : Nat} {b : SlotNew} {r : Nat} {L R : Object n}
    (hw : (σ.getCell i).slotWitness b = some .eta)
    (hty : σ.typeAt i = some (.prod L R))
    (hr : cert.rank i b = some r) :
    ∃ (lIdx rIdx : Nat) (bL : SlotNew) (rL : Nat) (bR : SlotNew) (rR : Nat),
      cert.deps i b = RuleDeps.productEta lIdx rIdx ∧
        σ.typeAt lIdx = some L ∧ σ.typeAt rIdx = some R ∧
          cert.rank lIdx bL = some rL ∧ rL < r ∧
            cert.rank rIdx bR = some rR ∧ rR < r := by
  obtain ⟨lIdx, rIdx, hdeps, hL, hR⟩ := cert.deps_of_eta_prod hw hty
  have hlMem : lIdx ∈ cert.deps i b := by simp [hdeps, RuleDeps.productEta]
  have hrMem : rIdx ∈ cert.deps i b := by simp [hdeps, RuleDeps.productEta]
  obtain ⟨bL, rL, hrL, hltL⟩ := cert.parents_lt i b r hr lIdx hlMem
  obtain ⟨bR, rR, hrR, hltR⟩ := cert.parents_lt i b r hr rIdx hrMem
  exact ⟨lIdx, rIdx, bL, rL, bR, rR, hdeps, hL, hR, hrL, hltL, hrR, hltR⟩

theorem ReachRankCert.ranked_parents_of_eta_exp {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) {i : Nat} {b : SlotNew} {r : Nat}
    {Arg Ret : Object n}
    (hw : (σ.getCell i).slotWitness b = some .eta)
    (hty : σ.typeAt i = some (.exp Arg Ret))
    (hr : cert.rank i b = some r) :
    ∃ (retIdx : Nat) (bRet : SlotNew) (rRet : Nat),
      cert.deps i b = RuleDeps.functionEta retIdx ∧
        σ.typeAt retIdx = some Ret ∧
          cert.rank retIdx bRet = some rRet ∧ rRet < r := by
  obtain ⟨retIdx, hdeps, hRet⟩ := cert.deps_of_eta_exp hw hty
  have hmem : retIdx ∈ cert.deps i b := by simp [hdeps, RuleDeps.functionEta]
  obtain ⟨bRet, rRet, hrRet, hlt⟩ := cert.parents_lt i b r hr retIdx hmem
  exact ⟨retIdx, bRet, rRet, hdeps, hRet, hrRet, hlt⟩

theorem ReachRankCert.ranked_parent_of_inl {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) {i : Nat} {b : SlotNew} {r p : Nat}
    {L R : Object n}
    (hw : (σ.getCell i).slotWitness b = some (.inl p))
    (hty : σ.typeAt i = some (.coprod L R))
    (hr : cert.rank i b = some r) :
    ∃ (bP : SlotNew) (rP : Nat),
      cert.deps i b = RuleDeps.coprodIntro p ∧
        σ.typeAt p = some L ∧
          cert.rank p bP = some rP ∧ rP < r := by
  obtain ⟨hdeps, hL⟩ := cert.deps_of_inl hw hty
  have hmem : p ∈ cert.deps i b := by simp [hdeps, RuleDeps.coprodIntro]
  obtain ⟨bP, rP, hrP, hlt⟩ := cert.parents_lt i b r hr p hmem
  exact ⟨bP, rP, hdeps, hL, hrP, hlt⟩

theorem ReachRankCert.ranked_parent_of_inr {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) {i : Nat} {b : SlotNew} {r p : Nat}
    {L R : Object n}
    (hw : (σ.getCell i).slotWitness b = some (.inr p))
    (hty : σ.typeAt i = some (.coprod L R))
    (hr : cert.rank i b = some r) :
    ∃ (bP : SlotNew) (rP : Nat),
      cert.deps i b = RuleDeps.coprodIntro p ∧
        σ.typeAt p = some R ∧
          cert.rank p bP = some rP ∧ rP < r := by
  obtain ⟨hdeps, hR⟩ := cert.deps_of_inr hw hty
  have hmem : p ∈ cert.deps i b := by simp [hdeps, RuleDeps.coprodIntro]
  obtain ⟨bP, rP, hrP, hlt⟩ := cert.parents_lt i b r hr p hmem
  exact ⟨bP, rP, hdeps, hR, hrP, hlt⟩

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

/-- Certificate whose state equals `runReachability Γ goal`. -/
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

/-- Certificate-based abbreviation of `NeutralParentLtCore`. -/
def NeutralParentLt {n : Nat} {σ : ReachState n} (cert : ReachRankCert σ)
    (childRank : Nat) (w : Witness) : Prop :=
  NeutralParentLtCore cert.rank (fun j => σ.getCell j) childRank w

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

/-- Build the ranked neutral-parent obligation from fire-time neutrality + deps. -/
theorem NeutralParentLtCore.of_premise_mem {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (deps : List Nat)
    (hp : RankedParents cert deps) {w : Witness}
    (hpre : NeutralParentPremise σ w)
    (hmem : Witness.elimParent_mem deps w) :
    NeutralParentLtCore cert.rank (fun j => σ.getCell j) hp.freshRank w := by
  cases w with
  | fstType p =>
      obtain ⟨bP, wP, rP, hwP, hne, hrP⟩ := cert.exists_ranked_neutral p hpre
      exact ⟨bP, wP, rP, hwP, hne, hrP,
        RankedParents.lt_freshRank hp p hmem bP rP hrP⟩
  | sndType p =>
      obtain ⟨bP, wP, rP, hwP, hne, hrP⟩ := cert.exists_ranked_neutral p hpre
      exact ⟨bP, wP, rP, hwP, hne, hrP,
        RankedParents.lt_freshRank hp p hmem bP rP hrP⟩
  | appTy fn arg =>
      obtain ⟨bP, wP, rP, hwP, hne, hrP⟩ := cert.exists_ranked_neutral fn hpre
      exact ⟨bP, wP, rP, hwP, hne, hrP,
        RankedParents.lt_freshRank hp fn hmem bP rP hrP⟩
  | ctxVar _ | fstHyp _ | sndHyp _ | app _ _ | inl _ | inr _ | unit | eta =>
      exact True.intro

/-- Neutrality flags are monotone under cell extension. -/
theorem NeutralParentPremise.of_le {n : Nat} {σ τ : ReachState n}
    (hle : ReachState.Le σ τ) {w : Witness}
    (h : NeutralParentPremise σ w) : NeutralParentPremise τ w := by
  cases w with
  | fstType p =>
      cases h with
      | inl ho =>
          cases hw : (σ.getCell p).oldWitness with
          | none => simp [ReachCell.oldNeutral, hw] at ho
          | some wP =>
              have hne : Witness.isNeutral wP = true := by
                simpa [ReachCell.oldNeutral, hw] using ho
              have hwτ : (τ.getCell p).oldWitness = some wP := (hle.cell p).old wP hw
              exact Or.inl (by simpa [ReachCell.oldNeutral, hwτ] using hne)
      | inr hn =>
          cases hw : (σ.getCell p).newWitness with
          | none => simp [ReachCell.newNeutral, hw] at hn
          | some wP =>
              have hne : Witness.isNeutral wP = true := by
                simpa [ReachCell.newNeutral, hw] using hn
              have hwτ : (τ.getCell p).newWitness = some wP := (hle.cell p).new wP hw
              exact Or.inr (by simpa [ReachCell.newNeutral, hwτ] using hne)
  | sndType p =>
      cases h with
      | inl ho =>
          cases hw : (σ.getCell p).oldWitness with
          | none => simp [ReachCell.oldNeutral, hw] at ho
          | some wP =>
              have hne : Witness.isNeutral wP = true := by
                simpa [ReachCell.oldNeutral, hw] using ho
              have hwτ : (τ.getCell p).oldWitness = some wP := (hle.cell p).old wP hw
              exact Or.inl (by simpa [ReachCell.oldNeutral, hwτ] using hne)
      | inr hn =>
          cases hw : (σ.getCell p).newWitness with
          | none => simp [ReachCell.newNeutral, hw] at hn
          | some wP =>
              have hne : Witness.isNeutral wP = true := by
                simpa [ReachCell.newNeutral, hw] using hn
              have hwτ : (τ.getCell p).newWitness = some wP := (hle.cell p).new wP hw
              exact Or.inr (by simpa [ReachCell.newNeutral, hwτ] using hne)
  | appTy fn arg =>
      cases h with
      | inl ho =>
          cases hw : (σ.getCell fn).oldWitness with
          | none => simp [ReachCell.oldNeutral, hw] at ho
          | some wP =>
              have hne : Witness.isNeutral wP = true := by
                simpa [ReachCell.oldNeutral, hw] using ho
              have hwτ : (τ.getCell fn).oldWitness = some wP := (hle.cell fn).old wP hw
              exact Or.inl (by simpa [ReachCell.oldNeutral, hwτ] using hne)
      | inr hn =>
          cases hw : (σ.getCell fn).newWitness with
          | none => simp [ReachCell.newNeutral, hw] at hn
          | some wP =>
              have hne : Witness.isNeutral wP = true := by
                simpa [ReachCell.newNeutral, hw] using hn
              have hwτ : (τ.getCell fn).newWitness = some wP := (hle.cell fn).new wP hw
              exact Or.inr (by simpa [ReachCell.newNeutral, hwτ] using hne)
  | ctxVar _ | fstHyp _ | sndHyp _ | app _ _ | inl _ | inr _ | unit | eta =>
      exact True.intro

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

/-- Parent slot after a fresh record: unchanged when it is not the written slot. -/
theorem ReachRankCert.extendFresh_parent_slot {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat) (hfresh : (σ.getCell i).slotWitness b = none)
    (hp : RankedParents cert deps) (hi : i < σ.cells.size)
    (p : Nat) (bP : SlotNew) (rP : Nat)
    (hrP : cert.rank p bP = some rP) :
    ¬(p = i ∧ bP = b) ∧
      ((σ.setCell i ((σ.getCell i).record b w)).getCell p).slotWitness bP =
        (σ.getCell p).slotWitness bP ∧
      (if p = i ∧ bP = b then some hp.freshRank else cert.rank p bP) =
        cert.rank p bP := by
  have hne : ¬(p = i ∧ bP = b) := by
    intro h
    obtain ⟨rfl, rfl⟩ := show i = p ∧ b = bP from ⟨h.1.symm, h.2.symm⟩
    have hiff := cert.rank_iff i b
    rw [hfresh, hrP] at hiff
    cases hiff
  refine ⟨hne, ?_, by rw [if_neg hne]⟩
  by_cases hpq : p = i
  · subst hpq
    have hbP : bP ≠ b := fun heq => hne ⟨rfl, heq⟩
    rw [ReachState.getCell_setCell_self hi]
    exact ReachCell.slotWitness_record_other _ b bP w hbP hfresh
  · rw [ReachState.getCell_setCell_ne (Ne.symm hpq)]

theorem NeutralParentLtCore.of_extendFresh_new {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat) (hfresh : (σ.getCell i).slotWitness b = none)
    (hp : RankedParents cert deps) (hi : i < σ.cells.size)
    (hnp : NeutralParentLtCore cert.rank (fun j => σ.getCell j) hp.freshRank w) :
    NeutralParentLtCore
      (fun j b' => if j = i ∧ b' = b then some hp.freshRank else cert.rank j b')
      (fun j => (σ.setCell i ((σ.getCell i).record b w)).getCell j)
      hp.freshRank w := by
  cases hw : w with
  | fstType p =>
      obtain ⟨bP, wP, rP, hwP, hne, hrP, hlt⟩ := hw ▸ hnp
      have hpar := ReachRankCert.extendFresh_parent_slot cert i b (.fstType p) deps hfresh hp hi p bP rP hrP
      refine ⟨bP, wP, rP, hpar.2.1 ▸ hwP, hne, ?_, hlt⟩
      convert hrP
      exact hpar.2.2
  | sndType p =>
      obtain ⟨bP, wP, rP, hwP, hne, hrP, hlt⟩ := hw ▸ hnp
      have hpar := ReachRankCert.extendFresh_parent_slot cert i b (.sndType p) deps hfresh hp hi p bP rP hrP
      refine ⟨bP, wP, rP, hpar.2.1 ▸ hwP, hne, ?_, hlt⟩
      convert hrP
      exact hpar.2.2
  | appTy fn arg =>
      obtain ⟨bP, wP, rP, hwP, hne, hrP, hlt⟩ := hw ▸ hnp
      have hpar := ReachRankCert.extendFresh_parent_slot cert i b (.appTy fn arg) deps hfresh hp hi fn bP rP hrP
      refine ⟨bP, wP, rP, hpar.2.1 ▸ hwP, hne, ?_, hlt⟩
      convert hrP
      exact hpar.2.2
  | ctxVar _ | fstHyp _ | sndHyp _ | app _ _ | inl _ | inr _ | unit | eta =>
      exact True.intro

theorem NeutralParentLtCore.of_extendFresh_old {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (wWrite : Witness)
    (deps : List Nat) (hfresh : (σ.getCell i).slotWitness b = none)
    (hp : RankedParents cert deps) (hi : i < σ.cells.size)
    {j : Nat} {b' : SlotNew} {r : Nat} {w' : Witness}
    (hne : ¬(j = i ∧ b' = b))
    (hr : cert.rank j b' = some r)
    (hw : (σ.getCell j).slotWitness b' = some w')
    (hnp0 : NeutralParentLtCore cert.rank (fun k => σ.getCell k) r w') :
    NeutralParentLtCore
      (fun k bk => if k = i ∧ bk = b then some hp.freshRank else cert.rank k bk)
      (fun k => (σ.setCell i ((σ.getCell i).record b wWrite)).getCell k)
      r w' := by
  cases hw' : w' with
  | fstType p =>
      obtain ⟨bP, wP, rP, hwP, hneP, hrP, hlt⟩ := hw' ▸ hnp0
      have hpar := ReachRankCert.extendFresh_parent_slot cert i b wWrite deps hfresh hp hi p bP rP hrP
      refine ⟨bP, wP, rP, hpar.2.1 ▸ hwP, hneP, ?_, hlt⟩
      convert hrP
      exact hpar.2.2
  | sndType p =>
      obtain ⟨bP, wP, rP, hwP, hneP, hrP, hlt⟩ := hw' ▸ hnp0
      have hpar := ReachRankCert.extendFresh_parent_slot cert i b wWrite deps hfresh hp hi p bP rP hrP
      refine ⟨bP, wP, rP, hpar.2.1 ▸ hwP, hneP, ?_, hlt⟩
      convert hrP
      exact hpar.2.2
  | appTy fn arg =>
      obtain ⟨bP, wP, rP, hwP, hneP, hrP, hlt⟩ := hw' ▸ hnp0
      have hpar := ReachRankCert.extendFresh_parent_slot cert i b wWrite deps hfresh hp hi fn bP rP hrP
      refine ⟨bP, wP, rP, hpar.2.1 ▸ hwP, hneP, ?_, hlt⟩
      convert hrP
      exact hpar.2.2
  | ctxVar _ | fstHyp _ | sndHyp _ | app _ _ | inl _ | inr _ | unit | eta =>
      exact True.intro

/--
Fresh slot: assign `freshRank`, store deps, and record the neutral-parent obligation
from fire-time provenance (not recovered from final shape).
-/
def ReachRankCert.extendFresh {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat)
    (hfresh : (σ.getCell i).slotWitness b = none)
    (hp : RankedParents cert deps)
    (hpre : NeutralParentPremise σ w)
    (hdeps : WitnessDepsOk σ i w deps)
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
  neutralParent_lt := by
    intro j b' r wStored hr hw
    have hmem := hdeps.elimParent_mem
    by_cases hnew : j = i ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := show i = j ∧ b = b' from ⟨hnew.1.symm, hnew.2.symm⟩
      have hr' : r = hp.freshRank := by
        simp at hr; exact hr.symm
      subst hr'
      have hw_eq : wStored = w := by
        rw [ReachState.getCell_setCell_self hi,
          ReachCell.slotWitness_record_fresh _ _ _ hfresh] at hw
        exact (Option.some.inj hw).symm
      cases hw_eq
      exact NeutralParentLtCore.of_extendFresh_new cert i b w deps hfresh hp hi
        (NeutralParentLtCore.of_premise_mem cert deps hp hpre hmem)
    · have hneIF : ¬(j = i ∧ b' = b) := hnew
      rw [if_neg hneIF] at hr
      have hw0 : (σ.getCell j).slotWitness b' = some wStored := by
        by_cases hj : j = i
        · subst hj
          have hb' : b' ≠ b := fun heq => hneIF ⟨rfl, heq⟩
          rw [ReachState.getCell_setCell_self hi,
            ReachCell.slotWitness_record_other _ b b' w hb' hfresh] at hw
          exact hw
        · rwa [ReachState.getCell_setCell_ne (Ne.symm hj)] at hw
      exact NeutralParentLtCore.of_extendFresh_old cert i b w deps hfresh hp hi
        hneIF hr hw0 (cert.neutralParent_lt j b' r wStored hr hw0)
  deps_sound := by
    intro j b' w' hw
    have htypes : ∀ k, (σ.setCell i ((σ.getCell i).record b w)).typeAt k = σ.typeAt k := by
      intro k; simp [ReachState.typeAt, ReachState.setCell_types]
    by_cases hnew : j = i ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := show i = j ∧ b = b' from ⟨hnew.1.symm, hnew.2.symm⟩
      have hw' : w' = w := by
        rw [ReachState.getCell_setCell_self hi,
          ReachCell.slotWitness_record_fresh _ _ _ hfresh] at hw
        exact (Option.some.inj hw).symm
      subst hw'
      simp only [↓reduceIte]
      exact WitnessDepsOk.of_types_eq htypes hdeps
    · have hneIF : ¬(j = i ∧ b' = b) := hnew
      rw [if_neg hneIF]
      have hw0 : (σ.getCell j).slotWitness b' = some w' := by
        by_cases hj : j = i
        · subst hj
          have hb' : b' ≠ b := fun heq => hneIF ⟨rfl, heq⟩
          rw [ReachState.getCell_setCell_self hi,
            ReachCell.slotWitness_record_other _ b b' w hb' hfresh] at hw
          exact hw
        · rwa [ReachState.getCell_setCell_ne (Ne.symm hj)] at hw
      exact WitnessDepsOk.of_types_eq htypes (cert.deps_sound j b' w' hw0)
  retrievable_witnessed := by
    intro j hr
    by_cases hj : j = i
    · have hji : i = j := hj.symm; subst hji
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

/-- Unified extend: occupied is a no-op; fresh records deps + neutral-parent obligation. -/
def ReachRankCert.extend {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat)
    (hi : i < σ.cells.size)
    (hpar : RankedParents cert deps)
    (hpre : NeutralParentPremise σ w)
    (hdeps : WitnessDepsOk σ i w deps) :
    ReachRankCert (σ.setCell i ((σ.getCell i).record b w)) :=
  match hslot : (σ.getCell i).slotWitness b with
  | some _ =>
      ReachRankCert.extendOccupied cert i b w (by simp [hslot]) hi
  | none =>
      ReachRankCert.extendFresh cert i b w deps hslot hpar hpre hdeps hi

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
  neutralParent_lt := by
    intro i b r w hr hw
    have hw0 : (σ.getCell i).slotWitness b = some w := by
      rwa [ReachState.getCell_markInconsistentIf] at hw
    simpa [ReachState.getCell_markInconsistentIf] using
      cert.neutralParent_lt i b r w hr hw0
  deps_sound := by
    intro i b w hw
    have hw0 : (σ.getCell i).slotWitness b = some w := by
      rwa [ReachState.getCell_markInconsistentIf] at hw
    have h0 := cert.deps_sound i b w hw0
    refine WitnessDepsOk.of_types_eq ?_ h0
    intro j
    simp [ReachState.typeAt, ReachState.types_markInconsistentIf]
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
  neutralParent_lt := by
    intro j b' r w' hr hw
    have hslots :
        ((σ.setCell i ((σ.getCell i).recordHyp b w)).getCell j).slotWitness b' =
          ((σ.setCell i ((σ.getCell i).record b w)).getCell j).slotWitness b' := by
      by_cases hj : j = i
      · subst hj
        rw [ReachState.getCell_setCell_self hi, ReachState.getCell_setCell_self hi]
        exact ReachCell.slotWitness_recordHyp _ b w b'
      · rw [ReachState.getCell_setCell_ne (Ne.symm hj),
          ReachState.getCell_setCell_ne (Ne.symm hj)]
    have hw0 := hslots ▸ hw
    have hnp0 := cert.neutralParent_lt j b' r w' hr hw0
    cases w' with
    | fstType p =>
        obtain ⟨bP, wP, rP, hwP, hne, hrP, hlt⟩ := hnp0
        refine ⟨bP, wP, rP, ?_, hne, hrP, hlt⟩
        have hps :
            ((σ.setCell i ((σ.getCell i).recordHyp b w)).getCell p).slotWitness bP =
              ((σ.setCell i ((σ.getCell i).record b w)).getCell p).slotWitness bP := by
          by_cases hp : p = i
          · subst hp
            rw [ReachState.getCell_setCell_self hi, ReachState.getCell_setCell_self hi]
            exact ReachCell.slotWitness_recordHyp _ b w bP
          · rw [ReachState.getCell_setCell_ne (Ne.symm hp),
              ReachState.getCell_setCell_ne (Ne.symm hp)]
        exact hps ▸ hwP
    | sndType p =>
        obtain ⟨bP, wP, rP, hwP, hne, hrP, hlt⟩ := hnp0
        refine ⟨bP, wP, rP, ?_, hne, hrP, hlt⟩
        have hps :
            ((σ.setCell i ((σ.getCell i).recordHyp b w)).getCell p).slotWitness bP =
              ((σ.setCell i ((σ.getCell i).record b w)).getCell p).slotWitness bP := by
          by_cases hp : p = i
          · subst hp
            rw [ReachState.getCell_setCell_self hi, ReachState.getCell_setCell_self hi]
            exact ReachCell.slotWitness_recordHyp _ b w bP
          · rw [ReachState.getCell_setCell_ne (Ne.symm hp),
              ReachState.getCell_setCell_ne (Ne.symm hp)]
        exact hps ▸ hwP
    | appTy fn arg =>
        obtain ⟨bP, wP, rP, hwP, hne, hrP, hlt⟩ := hnp0
        refine ⟨bP, wP, rP, ?_, hne, hrP, hlt⟩
        have hps :
            ((σ.setCell i ((σ.getCell i).recordHyp b w)).getCell fn).slotWitness bP =
              ((σ.setCell i ((σ.getCell i).record b w)).getCell fn).slotWitness bP := by
          by_cases hp : fn = i
          · subst hp
            rw [ReachState.getCell_setCell_self hi, ReachState.getCell_setCell_self hi]
            exact ReachCell.slotWitness_recordHyp _ b w bP
          · rw [ReachState.getCell_setCell_ne (Ne.symm hp),
              ReachState.getCell_setCell_ne (Ne.symm hp)]
        exact hps ▸ hwP
    | ctxVar _ | fstHyp _ | sndHyp _ | app _ _ | inl _ | inr _ | unit | eta =>
        exact True.intro
  deps_sound := by
    intro j b' w' hw
    have hslots :
        ((σ.setCell i ((σ.getCell i).recordHyp b w)).getCell j).slotWitness b' =
          ((σ.setCell i ((σ.getCell i).record b w)).getCell j).slotWitness b' := by
      by_cases hj : j = i
      · subst hj
        rw [ReachState.getCell_setCell_self hi, ReachState.getCell_setCell_self hi]
        exact ReachCell.slotWitness_recordHyp _ b w b'
      · rw [ReachState.getCell_setCell_ne (Ne.symm hj),
          ReachState.getCell_setCell_ne (Ne.symm hj)]
    have hw0 := hslots ▸ hw
    have h0 := cert.deps_sound j b' w' hw0
    refine WitnessDepsOk.of_types_eq ?_ h0
    intro k
    simp [ReachState.typeAt, ReachState.setCell_types]
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
    (hpre : NeutralParentPremise σ w)
    (hdeps : WitnessDepsOk σ i w deps)
    {j : Nat} {b' : SlotNew} {r : Nat}
    (hr : cert.rank j b' = some r) :
    (ReachRankCert.extend cert i b w deps hi hpar hpre hdeps).rank j b' = some r := by
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
    (hpre : NeutralParentPremise σ w)
    (hdeps : WitnessDepsOk σ i w deps)
    (ps : List Nat) (hp : RankedParents cert ps) :
    RankedParents (ReachRankCert.extend cert i b w deps hi hpar hpre hdeps) ps := by
  intro p hpMem
  obtain ⟨bP, rP, hrP⟩ := hp p hpMem
  exact ⟨bP, rP, ReachRankCert.extend_preserves_rank cert i b w deps hi hpar hpre hdeps hrP⟩

theorem ParentsCertified.of_extend {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat) (hi : i < σ.cells.size)
    (hpar : RankedParents cert deps)
    (hpre : NeutralParentPremise σ w)
    (hdeps : WitnessDepsOk σ i w deps)
    (w' : Witness) (hp : ParentsCertified cert w') :
    ParentsCertified (ReachRankCert.extend cert i b w deps hi hpar hpre hdeps) w' :=
  RankedParents.of_extend cert i b w deps hi hpar hpre hdeps _ hp

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
    (h : RankedParents cert deps)
    (hpre : NeutralParentPremise σ w)
    (hdeps : WitnessDepsOk σ i w deps) :
    CertifiedReachResult n :=
  match σ.typeAt i with
  | none => ⟨σ, cert⟩
  | some A =>
      if hi : i < σ.cells.size then
        let σ₁ := σ.setCell i ((σ.getCell i).record b w)
        let c₁ := ReachRankCert.extend cert i b w deps hi h hpre hdeps
        ⟨σ₁.markInconsistentIf A, c₁.ofMarkInconsistentIf A⟩
      else
        ⟨σ.markInconsistentIf A, cert.ofMarkInconsistentIf A⟩

theorem certifiedDiscover_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat) (h : RankedParents cert deps)
    (hpre : NeutralParentPremise σ w)
    (hdeps : WitnessDepsOk σ i w deps) :
    (certifiedDiscover σ cert i b w deps h hpre hdeps).project = σ.discover i b w := by
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
    (hpre : NeutralParentPremise σ w)
    (hdeps : WitnessDepsOk σ i w deps)
    (ps : List Nat) (hp : RankedParents cert ps) :
    RankedParents (certifiedDiscover σ cert i b w deps h hpre hdeps).cert ps := by
  unfold certifiedDiscover
  cases σ.typeAt i with
  | none => exact hp
  | some A =>
      change RankedParents
        ((if hi : i < σ.cells.size then
          ({ state := (σ.setCell i ((σ.getCell i).record b w)).markInconsistentIf A,
             cert := (ReachRankCert.extend cert i b w deps hi h hpre hdeps).ofMarkInconsistentIf A } :
            CertifiedReachResult n)
        else
          ({ state := σ.markInconsistentIf A,
             cert := cert.ofMarkInconsistentIf A } :
            CertifiedReachResult n)).cert) ps
      by_cases hi : i < σ.cells.size
      · rw [dif_pos hi]
        exact RankedParents.of_markInconsistentIf
          (ReachRankCert.extend cert i b w deps hi h hpre hdeps) A ps
          (RankedParents.of_extend cert i b w deps hi h hpre hdeps ps hp)
      · rw [dif_neg hi]
        exact RankedParents.of_markInconsistentIf cert A ps hp

theorem NeutralParentPremise.of_certifiedDiscover {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness)
    (deps : List Nat) (h : RankedParents cert deps)
    (hpre : NeutralParentPremise σ w)
    (hdeps : WitnessDepsOk σ i w deps)
    {w' : Witness} (hp' : NeutralParentPremise σ w') :
    NeutralParentPremise (certifiedDiscover σ cert i b w deps h hpre hdeps).state w' := by
  have hproj := certifiedDiscover_project σ cert i b w deps h hpre hdeps
  have hle : ReachState.Le σ (certifiedDiscover σ cert i b w deps h hpre hdeps).state := by
    rw [show (certifiedDiscover σ cert i b w deps h hpre hdeps).state = σ.discover i b w
        from hproj]
    exact σ.le_discover i b w
  exact NeutralParentPremise.of_le hle hp'

/-- Dual-fire; parents + neutral-parent premise required only when a slot fires. -/
def certifiedDiscoverDual {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (i : Nat) (oldOk newOk : Bool) (w : Witness) (deps : List Nat)
    (h : (oldOk = true ∨ newOk = true) → RankedParents cert deps)
    (hpre : (oldOk = true ∨ newOk = true) → NeutralParentPremise σ w)
    (hdeps : WitnessDepsOk σ i w deps) :
    CertifiedReachResult n :=
  match oldOk, newOk with
  | true, true =>
      let h₀ := h (Or.inl rfl)
      let hpre₀ := hpre (Or.inl rfl)
      let c₁ := certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps
      let h₁ := RankedParents.of_certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps deps h₀
      let hpre₁ := NeutralParentPremise.of_certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps hpre₀
      let hdeps₁ : WitnessDepsOk c₁.state i w deps := by
        have hproj := certifiedDiscover_project σ cert i false w deps h₀ hpre₀ hdeps
        refine WitnessDepsOk.of_types_eq ?_ hdeps
        intro j
        rw [show c₁.state = σ.discover i false w from hproj]
        simp [ReachState.typeAt, ← (σ.le_discover i false w).types]
      certifiedDiscover c₁.state c₁.cert i true w deps h₁ hpre₁ hdeps₁
  | true, false =>
      certifiedDiscover σ cert i false w deps (h (Or.inl rfl)) (hpre (Or.inl rfl)) hdeps
  | false, true =>
      certifiedDiscover σ cert i true w deps (h (Or.inr rfl)) (hpre (Or.inr rfl)) hdeps
  | false, false =>
      ⟨σ, cert⟩

theorem certifiedDiscoverDual_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (oldOk newOk : Bool) (w : Witness)
    (deps : List Nat)
    (h : (oldOk = true ∨ newOk = true) → RankedParents cert deps)
    (hpre : (oldOk = true ∨ newOk = true) → NeutralParentPremise σ w)
    (hdeps : WitnessDepsOk σ i w deps) :
    (certifiedDiscoverDual σ cert i oldOk newOk w deps h hpre hdeps).project =
      σ.discoverDual i oldOk newOk w := by
  cases oldOk <;> cases newOk
  · rfl
  · exact certifiedDiscover_project σ cert i true w deps (h (Or.inr rfl)) (hpre (Or.inr rfl)) hdeps
  · exact certifiedDiscover_project σ cert i false w deps (h (Or.inl rfl)) (hpre (Or.inl rfl)) hdeps
  · have h₀ := h (Or.inl rfl)
    have hpre₀ := hpre (Or.inl rfl)
    have h₁ := certifiedDiscover_project σ cert i false w deps h₀ hpre₀ hdeps
    have hdeps₁ : WitnessDepsOk
        (certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps).state i w deps := by
      refine WitnessDepsOk.of_types_eq ?_ hdeps
      intro j
      rw [show (certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps).state =
          σ.discover i false w from h₁]
      simp [ReachState.typeAt, ← (σ.le_discover i false w).types]
    have h₂ := certifiedDiscover_project
      (certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps).state
      (certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps).cert i true w deps
      (RankedParents.of_certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps deps h₀)
      (NeutralParentPremise.of_certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps hpre₀)
      hdeps₁
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
            let deps : List Nat := RuleDeps.ctxVar
            let hpar : RankedParents cert deps := RankedParents_nil cert
            let hpre : NeutralParentPremise σ w := NeutralParentPremise.trivial σ True.intro
            let hdeps : WitnessDepsOk σ i w deps := rfl
            let σHyp := σ.setCell i ((σ.getCell i).recordHyp b w)
            let certRec := ReachRankCert.extend cert i b w deps hi hpar hpre hdeps
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
    (hpre : (oldOk = true ∨ newOk = true) → NeutralParentPremise σ w)
    (hdeps : WitnessDepsOk σ i w deps)
    (ps : List Nat) (hp : RankedParents cert ps) :
    RankedParents (certifiedDiscoverDual σ cert i oldOk newOk w deps h hpre hdeps).cert ps := by
  cases oldOk <;> cases newOk
  · exact hp
  · exact RankedParents.of_certifiedDiscover σ cert i true w deps (h (Or.inr rfl))
      (hpre (Or.inr rfl)) hdeps ps hp
  · exact RankedParents.of_certifiedDiscover σ cert i false w deps (h (Or.inl rfl))
      (hpre (Or.inl rfl)) hdeps ps hp
  · have h₀ := h (Or.inl rfl)
    have hpre₀ := hpre (Or.inl rfl)
    have hproj := certifiedDiscover_project σ cert i false w deps h₀ hpre₀ hdeps
    have hdeps₁ : WitnessDepsOk
        (certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps).state i w deps := by
      refine WitnessDepsOk.of_types_eq ?_ hdeps
      intro j
      rw [show (certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps).state =
          σ.discover i false w from hproj]
      simp [ReachState.typeAt, ← (σ.le_discover i false w).types]
    exact RankedParents.of_certifiedDiscover
      (certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps).state
      (certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps).cert i true w deps
      (RankedParents.of_certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps deps h₀)
      (NeutralParentPremise.of_certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps hpre₀)
      hdeps₁ ps
      (RankedParents.of_certifiedDiscover σ cert i false w deps h₀ hpre₀ hdeps ps hp)

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
        True.intro (WitnessDepsOk.unit σ uIdx)
  | none => ⟨σ, cert⟩

theorem certifiedUnitEtaRule_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) :
    (certifiedUnitEtaRule σ cert).project = unitEtaRule σ := by
  unfold certifiedUnitEtaRule unitEtaRule
  cases σ.findTypeIdx (.unit : Object n) with
  | none => rfl
  | some uIdx =>
      exact certifiedDiscover_project σ cert uIdx false .unit RuleDeps.unit
        (RankedParents_nil cert) True.intro (WitnessDepsOk.unit σ uIdx)

def certifiedHypProdRule {n : Nat} (Γ : ReachCtx n) (σ : ReachState n)
    (cert : ReachRankCert σ) (i : Nat) (L R : Object n) :
    CertifiedReachResult n :=
  match σ.findTypeIdx (.prod L R), σ.findTypeIdx L, σ.findTypeIdx R with
  | some _pIdx, some lIdx, some rIdx =>
      let c₁ := certifiedDiscover σ cert lIdx (Γ.isNew i) (.fstHyp i)
        RuleDeps.hypProj (RankedParents_nil cert) True.intro (WitnessDepsOk.fstHyp σ lIdx i)
      certifiedDiscover c₁.state c₁.cert rIdx (Γ.isNew i) (.sndHyp i)
        RuleDeps.hypProj
        (RankedParents.of_certifiedDiscover σ cert lIdx (Γ.isNew i) (.fstHyp i)
          RuleDeps.hypProj (RankedParents_nil cert) True.intro (WitnessDepsOk.fstHyp σ lIdx i)
          RuleDeps.hypProj (RankedParents_nil cert))
        True.intro (WitnessDepsOk.sndHyp c₁.state rIdx i)
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
            RuleDeps.hypProj (RankedParents_nil cert) True.intro
            (WitnessDepsOk.fstHyp σ lIdx i)
          have h₂ := certifiedDiscover_project
            (certifiedDiscover σ cert lIdx (Γ.isNew i) (.fstHyp i)
              RuleDeps.hypProj (RankedParents_nil cert) True.intro
              (WitnessDepsOk.fstHyp σ lIdx i)).state
            (certifiedDiscover σ cert lIdx (Γ.isNew i) (.fstHyp i)
              RuleDeps.hypProj (RankedParents_nil cert) True.intro
              (WitnessDepsOk.fstHyp σ lIdx i)).cert
            rIdx (Γ.isNew i) (.sndHyp i) RuleDeps.hypProj
            (RankedParents.of_certifiedDiscover σ cert lIdx (Γ.isNew i) (.fstHyp i)
              RuleDeps.hypProj (RankedParents_nil cert) True.intro
              (WitnessDepsOk.fstHyp σ lIdx i)
              RuleDeps.hypProj (RankedParents_nil cert))
            True.intro
            (WitnessDepsOk.sndHyp
              (certifiedDiscover σ cert lIdx (Γ.isNew i) (.fstHyp i)
                RuleDeps.hypProj (RankedParents_nil cert) True.intro
                (WitnessDepsOk.fstHyp σ lIdx i)).state
              rIdx i)
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
        (fun _ => True.intro) (WitnessDepsOk.app σ rIdx i aIdx)
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
          (.app i aIdx) (RuleDeps.hypApp aIdx) _ (fun _ => True.intro)
          (WitnessDepsOk.app σ rIdx i aIdx)

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
    (ti lIdx rIdx : Nat) (L R : Object n)
    (hti : σ.typeAt ti = some (.prod L R))
    (hL : σ.typeAt lIdx = some L) (hR : σ.typeAt rIdx = some R) :
    CertifiedReachResult n :=
  let hdepsFst := WitnessDepsOk.fstType σ lIdx ti
  let hdepsSnd0 := WitnessDepsOk.sndType σ rIdx ti
  let c₁ := certifiedDiscoverDual σ cert lIdx
    (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
    (RuleDeps.typeProj ti)
    (fun h => RankedParents.singleton_of_neutral cert ti h)
    (fun h => h) hdepsFst
  let c₂ := certifiedDiscoverDual c₁.state c₁.cert rIdx
    (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.sndType ti)
    (RuleDeps.typeProj ti)
    (fun h =>
      RankedParents.of_certifiedDiscoverDual σ cert lIdx
        (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
        (RuleDeps.typeProj ti)
        (fun h0 => RankedParents.singleton_of_neutral cert ti h0)
        (fun h0 => h0) hdepsFst
        (RuleDeps.typeProj ti)
        (RankedParents.singleton_of_neutral cert ti h))
    (fun h =>
      NeutralParentPremise.of_le
        (by
          have hproj := certifiedDiscoverDual_project σ cert lIdx
            (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
            (RuleDeps.typeProj ti)
            (fun h0 => RankedParents.singleton_of_neutral cert ti h0)
            (fun h0 => h0) hdepsFst
          rw [show c₁.state = σ.discoverDual lIdx (σ.getCell ti).oldNeutral
              (σ.getCell ti).newNeutral (.fstType ti) from hproj]
          exact σ.le_discoverDual lIdx (σ.getCell ti).oldNeutral
            (σ.getCell ti).newNeutral (.fstType ti))
        (show NeutralParentPremise σ (.sndType ti) from h))
    (by
      refine WitnessDepsOk.of_types_eq ?_ hdepsSnd0
      intro j
      have hproj := certifiedDiscoverDual_project σ cert lIdx
        (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
        (RuleDeps.typeProj ti)
        (fun h0 => RankedParents.singleton_of_neutral cert ti h0)
        (fun h0 => h0) hdepsFst
      rw [show c₁.state = σ.discoverDual lIdx (σ.getCell ti).oldNeutral
          (σ.getCell ti).newNeutral (.fstType ti) from hproj]
      simp [ReachState.typeAt, ← (σ.le_discoverDual lIdx (σ.getCell ti).oldNeutral
        (σ.getCell ti).newNeutral (.fstType ti)).types])
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
      (fun _ => True.intro)
      (by
        have hproj₁ := certifiedDiscoverDual_project σ cert lIdx
          (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
          (RuleDeps.typeProj ti)
          (fun h0 => RankedParents.singleton_of_neutral cert ti h0)
          (fun h0 => h0) hdepsFst
        have hdepsSnd : WitnessDepsOk c₁.state rIdx (.sndType ti) (RuleDeps.typeProj ti) := by
          refine WitnessDepsOk.of_types_eq ?_ hdepsSnd0
          intro j
          rw [show c₁.state = σ.discoverDual lIdx (σ.getCell ti).oldNeutral
              (σ.getCell ti).newNeutral (.fstType ti) from hproj₁]
          simp [ReachState.typeAt, ← (σ.le_discoverDual lIdx (σ.getCell ti).oldNeutral
            (σ.getCell ti).newNeutral (.fstType ti)).types]
        have hproj₂ := certifiedDiscoverDual_project c₁.state c₁.cert rIdx
          (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.sndType ti)
          (RuleDeps.typeProj ti)
          (fun h =>
            RankedParents.of_certifiedDiscoverDual σ cert lIdx
              (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
              (RuleDeps.typeProj ti)
              (fun h0 => RankedParents.singleton_of_neutral cert ti h0)
              (fun h0 => h0) hdepsFst
              (RuleDeps.typeProj ti)
              (RankedParents.singleton_of_neutral cert ti h))
          (fun h =>
            NeutralParentPremise.of_le
              (by
                rw [show c₁.state = σ.discoverDual lIdx (σ.getCell ti).oldNeutral
                    (σ.getCell ti).newNeutral (.fstType ti) from hproj₁]
                exact σ.le_discoverDual lIdx (σ.getCell ti).oldNeutral
                  (σ.getCell ti).newNeutral (.fstType ti))
              (show NeutralParentPremise σ (.sndType ti) from h))
          hdepsSnd
        refine WitnessDepsOk.of_types_eq ?_
          (WitnessDepsOk.eta_prod hti hL hR)
        intro j
        rw [show c₂.state =
            (σ.discoverDual lIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
              (.fstType ti)).discoverDual
              rIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.sndType ti)
            from by
              simp only [CertifiedReachResult.project] at hproj₁ hproj₂ ⊢
              rw [hproj₂, hproj₁]]
        simp [ReachState.typeAt,
          ← (σ.le_discoverDual lIdx (σ.getCell ti).oldNeutral
            (σ.getCell ti).newNeutral (.fstType ti)).types,
          ← ((σ.discoverDual lIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
              (.fstType ti)).le_discoverDual rIdx (σ.getCell ti).oldNeutral
            (σ.getCell ti).newNeutral (.sndType ti)).types])
  else
    c₂

def certifiedProdTypeRule {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (ti : Nat) (L R : Object n) (hti : σ.typeAt ti = some (.prod L R)) :
    CertifiedReachResult n :=
  match hl : σ.findTypeIdx L, hr : σ.findTypeIdx R with
  | some lIdx, some rIdx =>
      certifiedProdTypeRule.go σ cert ti lIdx rIdx L R hti
        (ReachState.typeAt_of_findTypeIdx hl) (ReachState.typeAt_of_findTypeIdx hr)
  | _, _ => ⟨σ, cert⟩

theorem certifiedProdTypeRule.go_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (ti lIdx rIdx : Nat) (L R : Object n)
    (hti : σ.typeAt ti = some (.prod L R))
    (hL : σ.typeAt lIdx = some L) (hR : σ.typeAt rIdx = some R) :
    (certifiedProdTypeRule.go σ cert ti lIdx rIdx L R hti hL hR).project =
      prodTypeRule.core σ ti lIdx rIdx := by
  unfold certifiedProdTypeRule.go prodTypeRule.core
  set hdepsFst := WitnessDepsOk.fstType σ lIdx ti
  set hdepsSnd0 := WitnessDepsOk.sndType σ rIdx ti
  have h₁ := certifiedDiscoverDual_project σ cert lIdx
    (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
    (RuleDeps.typeProj ti)
    (fun h => RankedParents.singleton_of_neutral cert ti h)
    (fun h => h) hdepsFst
  set c₁ := certifiedDiscoverDual σ cert lIdx
    (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
    (RuleDeps.typeProj ti)
    (fun h => RankedParents.singleton_of_neutral cert ti h)
    (fun h => h) hdepsFst
  have hdepsSnd : WitnessDepsOk c₁.state rIdx (.sndType ti) (RuleDeps.typeProj ti) := by
    refine WitnessDepsOk.of_types_eq ?_ hdepsSnd0
    intro j
    rw [show c₁.state = σ.discoverDual lIdx (σ.getCell ti).oldNeutral
        (σ.getCell ti).newNeutral (.fstType ti) from h₁]
    simp [ReachState.typeAt, ← (σ.le_discoverDual lIdx (σ.getCell ti).oldNeutral
      (σ.getCell ti).newNeutral (.fstType ti)).types]
  have h₂ := certifiedDiscoverDual_project c₁.state c₁.cert rIdx
    (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.sndType ti)
    (RuleDeps.typeProj ti)
    (fun h =>
      RankedParents.of_certifiedDiscoverDual σ cert lIdx
        (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
        (RuleDeps.typeProj ti)
        (fun h0 => RankedParents.singleton_of_neutral cert ti h0)
        (fun h0 => h0) hdepsFst
        (RuleDeps.typeProj ti)
        (RankedParents.singleton_of_neutral cert ti h))
    (fun h =>
      NeutralParentPremise.of_le
        (by
          rw [show c₁.state = σ.discoverDual lIdx (σ.getCell ti).oldNeutral
              (σ.getCell ti).newNeutral (.fstType ti) from h₁]
          exact σ.le_discoverDual lIdx (σ.getCell ti).oldNeutral
            (σ.getCell ti).newNeutral (.fstType ti))
        (show NeutralParentPremise σ (.sndType ti) from h))
    hdepsSnd
  set c₂ := certifiedDiscoverDual c₁.state c₁.cert rIdx
    (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.sndType ti)
    (RuleDeps.typeProj ti)
    (fun h =>
      RankedParents.of_certifiedDiscoverDual σ cert lIdx
        (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)
        (RuleDeps.typeProj ti)
        (fun h0 => RankedParents.singleton_of_neutral cert ti h0)
        (fun h0 => h0) hdepsFst
        (RuleDeps.typeProj ti)
        (RankedParents.singleton_of_neutral cert ti h))
    (fun h =>
      NeutralParentPremise.of_le
        (by
          rw [show c₁.state = σ.discoverDual lIdx (σ.getCell ti).oldNeutral
              (σ.getCell ti).newNeutral (.fstType ti) from h₁]
          exact σ.le_discoverDual lIdx (σ.getCell ti).oldNeutral
            (σ.getCell ti).newNeutral (.fstType ti))
        (show NeutralParentPremise σ (.sndType ti) from h))
    hdepsSnd
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
      have heta : WitnessDepsOk c₂.state ti .eta (RuleDeps.productEta lIdx rIdx) := by
        refine WitnessDepsOk.of_types_eq ?_ (WitnessDepsOk.eta_prod hti hL hR)
        intro j
        rw [show c₂.state =
            (σ.discoverDual lIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
              (.fstType ti)).discoverDual
              rIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.sndType ti)
            from hσ₁]
        simp [ReachState.typeAt,
          ← (σ.le_discoverDual lIdx (σ.getCell ti).oldNeutral
            (σ.getCell ti).newNeutral (.fstType ti)).types,
          ← ((σ.discoverDual lIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
              (.fstType ti)).le_discoverDual rIdx (σ.getCell ti).oldNeutral
            (σ.getCell ti).newNeutral (.sndType ti)).types]
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
                  (bool_and_left hcomp) (bool_and_right hcomp))
              (fun _ => True.intro) heta)
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
              .eta (RuleDeps.productEta lIdx rIdx) _
              (fun _ => True.intro) heta)
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
    (cert : ReachRankCert σ) (ti : Nat) (L R : Object n)
    (hti : σ.typeAt ti = some (.prod L R)) :
    (certifiedProdTypeRule σ cert ti L R hti).project = prodTypeRule σ ti L R := by
  dsimp only [certifiedProdTypeRule]
  split
  · next lIdx rIdx hl hr =>
      rw [certifiedProdTypeRule.go_project σ cert ti lIdx rIdx L R hti
        (ReachState.typeAt_of_findTypeIdx hl) (ReachState.typeAt_of_findTypeIdx hr),
        prodTypeRule_eq_core σ ti L R hl hr]
  · rename_i hnomatch
    dsimp only [CertifiedReachResult.project]
    unfold prodTypeRule
    cases hL : σ.findTypeIdx L with
    | none => rfl
    | some lIdx =>
      cases hR : σ.findTypeIdx R with
      | none => rfl
      | some rIdx =>
          exact (hnomatch lIdx rIdx hL hR).elim

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

theorem NeutralParentPremise_of_expApp_fire {n : Nat} {σ : ReachState n}
    (ti aIdx : Nat)
    (hfire :
      ((σ.getCell ti).oldNeutral && (σ.getCell aIdx).oldDeducible) = true ∨
        (((σ.getCell ti).oldNeutral && (σ.getCell aIdx).usesNew) ||
          ((σ.getCell ti).newNeutral && (σ.getCell aIdx).simplyDeducible)) = true) :
    NeutralParentPremise σ (.appTy ti aIdx) := by
  cases hfire with
  | inl ho => exact Or.inl (bool_and_left ho)
  | inr hn =>
    cases Bool.or_eq_true_iff.mp hn with
    | inl hOldArg => exact Or.inl (bool_and_left hOldArg)
    | inr hNewArg => exact Or.inr (bool_and_left hNewArg)

def certifiedExpEtaRule {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (ti : Nat) (Arg Ret : Object n) (hti : σ.typeAt ti = some (.exp Arg Ret)) :
    CertifiedReachResult n :=
  if !(σ.getCell ti).simplyDeducible then
    match hr : σ.findTypeIdx Ret with
    | some rIdx =>
        if hret : (σ.getCell rIdx).simplyDeducible = true then
          certifiedDiscoverDual σ cert ti
            (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew .eta
            (RuleDeps.functionEta rIdx)
            (fun _ => RankedParents.singleton_of_simplyDeducible cert rIdx hret)
            (fun _ => True.intro)
            (WitnessDepsOk.eta_exp hti (ReachState.typeAt_of_findTypeIdx hr))
        else
          ⟨σ, cert⟩
    | none => ⟨σ, cert⟩
  else
    ⟨σ, cert⟩

theorem certifiedExpEtaRule_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (ti : Nat) (Arg Ret : Object n)
    (hti : σ.typeAt ti = some (.exp Arg Ret)) :
    (certifiedExpEtaRule σ cert ti Arg Ret hti).project = expEtaRule σ ti Ret := by
  simp only [certifiedExpEtaRule, expEtaRule]
  split
  · rename_i hfire
    split
    · next rIdx hr =>
        simp only [hr]
        exact CertifiedReachResult.project_dite_bool
          (σ.getCell rIdx).simplyDeducible
          (fun hret =>
            certifiedDiscoverDual σ cert ti
              (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew .eta
              (RuleDeps.functionEta rIdx)
              (fun _ => RankedParents.singleton_of_simplyDeducible cert rIdx hret)
              (fun _ => True.intro)
              (WitnessDepsOk.eta_exp hti (ReachState.typeAt_of_findTypeIdx hr)))
          ⟨σ, cert⟩
          (σ.discoverDual ti (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew .eta)
          σ
          (fun hret =>
            certifiedDiscoverDual_project σ cert ti
              (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew .eta
              (RuleDeps.functionEta rIdx) _
              (fun _ => True.intro)
              (WitnessDepsOk.eta_exp hti (ReachState.typeAt_of_findTypeIdx hr)))
          rfl
    · next hr =>
        simp only [CertifiedReachResult.project, hr]
  · rename_i hskip
    simp only [CertifiedReachResult.project]

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
        (fun hfire => NeutralParentPremise_of_expApp_fire ti aIdx hfire)
        (WitnessDepsOk.appTy σ rIdx ti aIdx)
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
          (fun hfire => NeutralParentPremise_of_expApp_fire ti aIdx hfire)
          (WitnessDepsOk.appTy σ rIdx ti aIdx)

private def certifiedCoprodTypeRule.go {n : Nat}
    (σ : ReachState n) (cert : ReachRankCert σ) (ti : Nat)
    (L R : Object n) (hti : σ.typeAt ti = some (.coprod L R))
    (lIdx rIdx : Nat)
    (hLty : σ.typeAt lIdx = some L) (hRty : σ.typeAt rIdx = some R) :
    CertifiedReachResult n :=
  if (σ.getCell ti).simplyDeducible then ⟨σ, cert⟩
  else if hL : (σ.getCell lIdx).simplyDeducible = true then
    certifiedDiscoverDual σ cert ti
      (σ.getCell lIdx).oldDeducible (σ.getCell lIdx).usesNew
      (.inl lIdx) (RuleDeps.coprodIntro lIdx)
      (fun _ => RankedParents.singleton_of_simplyDeducible cert lIdx hL)
      (fun _ => True.intro)
      (WitnessDepsOk.inl hti hLty)
  else if hR : (σ.getCell rIdx).simplyDeducible = true then
    certifiedDiscoverDual σ cert ti
      (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew
      (.inr rIdx) (RuleDeps.coprodIntro rIdx)
      (fun _ => RankedParents.singleton_of_simplyDeducible cert rIdx hR)
      (fun _ => True.intro)
      (WitnessDepsOk.inr hti hRty)
  else
    ⟨σ, cert⟩

def certifiedCoprodTypeRule {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (ti : Nat) (L R : Object n) (hti : σ.typeAt ti = some (.coprod L R)) :
    CertifiedReachResult n :=
  match hl : σ.findTypeIdx L, hr : σ.findTypeIdx R with
  | some lIdx, some rIdx =>
      certifiedCoprodTypeRule.go σ cert ti L R hti lIdx rIdx
        (ReachState.typeAt_of_findTypeIdx hl)
        (ReachState.typeAt_of_findTypeIdx hr)
  | _, _ => ⟨σ, cert⟩

private theorem certifiedCoprodTypeRule.go_project {n : Nat}
    (σ : ReachState n) (cert : ReachRankCert σ) (ti : Nat)
    (L R : Object n) (hti : σ.typeAt ti = some (.coprod L R))
    (lIdx rIdx : Nat)
    (hLty : σ.typeAt lIdx = some L) (hRty : σ.typeAt rIdx = some R) :
    (certifiedCoprodTypeRule.go σ cert ti L R hti lIdx rIdx hLty hRty).project =
      (if (σ.getCell ti).simplyDeducible then σ
       else if (σ.getCell lIdx).simplyDeducible then
         σ.discoverDual ti (σ.getCell lIdx).oldDeducible
           (σ.getCell lIdx).usesNew (.inl lIdx)
       else if (σ.getCell rIdx).simplyDeducible then
         σ.discoverDual ti (σ.getCell rIdx).oldDeducible
           (σ.getCell rIdx).usesNew (.inr rIdx)
       else σ) := by
  dsimp only [certifiedCoprodTypeRule.go]
  split
  · rfl
  · split
    · next hL =>
        exact certifiedDiscoverDual_project σ cert ti
          (σ.getCell lIdx).oldDeducible (σ.getCell lIdx).usesNew
          (.inl lIdx) (RuleDeps.coprodIntro lIdx) _ _ _
    · split
      · next hR =>
          exact certifiedDiscoverDual_project σ cert ti
            (σ.getCell rIdx).oldDeducible (σ.getCell rIdx).usesNew
            (.inr rIdx) (RuleDeps.coprodIntro rIdx) _ _ _
      · rfl

theorem certifiedCoprodTypeRule_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (ti : Nat) (L R : Object n)
    (hti : σ.typeAt ti = some (.coprod L R)) :
    (certifiedCoprodTypeRule σ cert ti L R hti).project =
      coprodTypeRule σ ti L R := by
  dsimp only [certifiedCoprodTypeRule]
  split
  · next lIdx rIdx hl hr =>
      rw [certifiedCoprodTypeRule.go_project σ cert ti L R hti lIdx rIdx
        (ReachState.typeAt_of_findTypeIdx hl)
        (ReachState.typeAt_of_findTypeIdx hr)]
      -- Align with computational `coprodTypeRule`.
      unfold coprodTypeRule
      cases hsd : (σ.getCell ti).simplyDeducible with
      | true => simp [hsd]
      | false =>
          simp [hsd, hl, hr]
  · rename_i hnomatch
    dsimp only [CertifiedReachResult.project]
    unfold coprodTypeRule
    cases (σ.getCell ti).simplyDeducible with
    | true => rfl
    | false =>
        cases hL : σ.findTypeIdx L with
        | none => rfl
        | some lIdx =>
          cases hR : σ.findTypeIdx R with
          | none => rfl
          | some rIdx =>
              exact (hnomatch lIdx rIdx hL hR).elim

/-- Computational counterpart of `certifiedTypeRule.ofType`. -/
def typeRule.ofType {n : Nat} (σ : ReachState n) (ti : Nat) (o : Option (Object n)) :
    ReachState n :=
  match o with
  | none => σ
  | some A =>
      Object.casesOn (motive := fun _ => ReachState n) A
        (fun _ => σ) σ σ
        (fun L R => prodTypeRule σ ti L R)
        (fun L R => coprodTypeRule σ ti L R)
        (fun Arg Ret => expAppRule (expEtaRule σ ti Ret) ti Arg Ret)

theorem typeRule_eq_ofType {n : Nat} (σ : ReachState n) (ti : Nat) :
    typeRule σ ti = typeRule.ofType σ ti (σ.typeAt ti) := by
  simp only [typeRule, typeRule.ofType]
  cases σ.typeAt ti with
  | none => rfl
  | some A => cases A <;> rfl

def certifiedTypeRule.ofType {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (ti : Nat) (o : Option (Object n)) (h : σ.typeAt ti = o) : CertifiedReachResult n :=
  match o with
  | none => ⟨σ, cert⟩
  | some A =>
      Object.casesOn (motive := fun A' => σ.typeAt ti = some A' → CertifiedReachResult n) A
        (fun _ _ => ⟨σ, cert⟩)
        (fun _ => ⟨σ, cert⟩)
        (fun _ => ⟨σ, cert⟩)
        (fun L R hti => certifiedProdTypeRule σ cert ti L R hti)
        (fun L R hti => certifiedCoprodTypeRule σ cert ti L R hti)
        (fun Arg Ret hti =>
          let c₁ := certifiedExpEtaRule σ cert ti Arg Ret hti
          certifiedExpAppRule c₁.state c₁.cert ti Arg Ret)
        h

def certifiedTypeRule {n : Nat} (σ : ReachState n) (cert : ReachRankCert σ)
    (ti : Nat) : CertifiedReachResult n :=
  certifiedTypeRule.ofType σ cert ti (σ.typeAt ti) rfl

theorem certifiedTypeRule_project {n : Nat} (σ : ReachState n)
    (cert : ReachRankCert σ) (ti : Nat) :
    (certifiedTypeRule σ cert ti).project = typeRule σ ti := by
  have hgo :
      ∀ (o : Option (Object n)) (h : σ.typeAt ti = o),
        (certifiedTypeRule.ofType σ cert ti o h).project = typeRule.ofType σ ti o := by
    intro o h
    cases o with
    | none => rfl
    | some A =>
        cases A with
        | base _ => rfl
        | unit => rfl
        | never => rfl
        | prod L R =>
            exact certifiedProdTypeRule_project σ cert ti L R h
        | coprod L R =>
            exact certifiedCoprodTypeRule_project σ cert ti L R h
        | exp Arg Ret =>
            change (certifiedExpAppRule
              (certifiedExpEtaRule σ cert ti Arg Ret h).state
              (certifiedExpEtaRule σ cert ti Arg Ret h).cert ti Arg Ret).project =
              expAppRule (expEtaRule σ ti Ret) ti Arg Ret
            have h₁ := certifiedExpEtaRule_project σ cert ti Arg Ret h
            have h₂ := certifiedExpAppRule_project
              (certifiedExpEtaRule σ cert ti Arg Ret h).state
              (certifiedExpEtaRule σ cert ti Arg Ret h).cert ti Arg Ret
            simp only [CertifiedReachResult.project] at h₁ h₂ ⊢
            rw [h₂, h₁]
  rw [typeRule_eq_ofType]
  simpa [certifiedTypeRule] using hgo (σ.typeAt ti) rfl

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

/-! ## Totality scope (neutral only)

Stored-neutral reconstruction restricts to `Witness.isNeutral`. Intro-only
`.unit` / `.inl` / `.inr` / `.eta` must **not** be over-quantified into
`neuOfType` / `neuOfTypeWF` success — they justify invertible arguments only.
-/

end Equality
end Gimbal
