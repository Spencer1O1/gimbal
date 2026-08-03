/-
  Finite positive-type reachability closure (Milestone 7 spike).

  Computes a least fixed point over the finite subformula universe of a root
  judgment. Does **not** enumerate concrete neutrals: contexts such as
  `x : X, s : X → X` stay finite because only types are tracked.
  Each type keeps separate old-only and uses-new witnesses (provenance lattice).
-/

import Gimbal.Equality.LambdaSyntax
import Gimbal.Equality.Polarized
import Gimbal.Equality.Subformula

namespace Gimbal
namespace Equality

/-! ### Witness parent pointers -/

/--
First-discovery derivation for a reachable type.
`hypIdx` indexes `ReachCtx.hyps`; `ofTypeIdx` / `argTypeIdx` / `fnTypeIdx`
index the subformula table.
-/
inductive Witness where
  | ctxVar (hypIdx : Nat)
  | fst (ofTypeIdx : Nat)
  | snd (ofTypeIdx : Nat)
  | app (fnHypIdx : Nat) (argTypeIdx : Nat)
  | appTy (fnTypeIdx : Nat) (argTypeIdx : Nat)
  | unit
  /-- Coproduct introduction from a deducible left payload (`ofTypeIdx` → `L`). -/
  | inl (ofTypeIdx : Nat)
  /-- Coproduct introduction from a deducible right payload (`ofTypeIdx` → `R`). -/
  | inr (ofTypeIdx : Nat)
  /-- Product η-availability (no neutral; not scheduled). -/
  | eta
  deriving DecidableEq, Repr

/--
Witnesses that reconstruct to a negative neutral (schedulable observations).
Introduction / η forms only justify invertible arguments.
-/
def Witness.isNeutral : Witness → Bool
  | .ctxVar _ | .fst _ | .snd _ | .app _ _ | .appTy _ _ => true
  | .unit | .inl _ | .inr _ | .eta => false

/--
Per-type reachability cell with a provenance lattice:
unreachable / old-only / uses-new (the latter two may both be inhabited).
-/
structure ReachCell where
  retrievable : Bool := false
  oldWitness : Option Witness := none
  newWitness : Option Witness := none
  deriving DecidableEq, Repr

def ReachCell.empty : ReachCell := {}

/-- Simply deducible from old hypotheses, new hypotheses, or a context hyp. -/
def ReachCell.simplyDeducible (c : ReachCell) : Bool :=
  c.retrievable || c.oldWitness.isSome || c.newWitness.isSome

/-- At least one recorded derivation uses `Γnew`. -/
def ReachCell.usesNew (c : ReachCell) : Bool :=
  c.newWitness.isSome

/-- Preferred witness: uses-new if present, otherwise old-only. -/
def ReachCell.witness (c : ReachCell) : Option Witness :=
  match c.newWitness with
  | some w => some w
  | none => c.oldWitness

/-! ### Provenance lattice order

Facts are only ever added and never revised, so cells grow along an extension
order. The number of facts still missing from the finite table is the measure
that makes the worklist terminate without fuel.
-/

/-- Extension order: `d` records every fact `c` records, with the same witness. -/
structure ReachCell.Le (c d : ReachCell) : Prop where
  retrievable : c.retrievable = true → d.retrievable = true
  old : ∀ w, c.oldWitness = some w → d.oldWitness = some w
  new : ∀ w, c.newWitness = some w → d.newWitness = some w

theorem ReachCell.Le.refl (c : ReachCell) : ReachCell.Le c c :=
  ⟨fun h => h, fun _ h => h, fun _ h => h⟩

theorem ReachCell.Le.trans {c d e : ReachCell}
    (h₁ : ReachCell.Le c d) (h₂ : ReachCell.Le d e) : ReachCell.Le c e :=
  ⟨fun h => h₂.retrievable (h₁.retrievable h),
   fun w h => h₂.old w (h₁.old w h),
   fun w h => h₂.new w (h₁.new w h)⟩

/-- Number of facts recorded in a cell (at most three). -/
def ReachCell.weight (c : ReachCell) : Nat :=
  c.retrievable.toNat + c.oldWitness.isSome.toNat + c.newWitness.isSome.toNat

theorem ReachCell.weight_le_three (c : ReachCell) : c.weight ≤ 3 := by
  obtain ⟨r, o, w⟩ := c
  cases r <;> cases o <;> cases w <;> simp [ReachCell.weight]

theorem ReachCell.Le.toNat_retrievable {c d : ReachCell} (h : ReachCell.Le c d) :
    c.retrievable.toNat ≤ d.retrievable.toNat := by
  cases hc : c.retrievable
  · simp
  · simp [h.retrievable hc]

theorem ReachCell.Le.toNat_old {c d : ReachCell} (h : ReachCell.Le c d) :
    c.oldWitness.isSome.toNat ≤ d.oldWitness.isSome.toNat := by
  cases hc : c.oldWitness
  · simp
  · rename_i w; simp [h.old w hc]

theorem ReachCell.Le.toNat_new {c d : ReachCell} (h : ReachCell.Le c d) :
    c.newWitness.isSome.toNat ≤ d.newWitness.isSome.toNat := by
  cases hc : c.newWitness
  · simp
  · rename_i w; simp [h.new w hc]

theorem ReachCell.weight_le_of_le {c d : ReachCell} (h : ReachCell.Le c d) :
    c.weight ≤ d.weight := by
  have h1 := h.toNat_retrievable
  have h2 := h.toNat_old
  have h3 := h.toNat_new
  simp only [ReachCell.weight]
  omega

private theorem option_eq_of_isSome_eq {α : Type} {a b : Option α}
    (hi : a.isSome = b.isSome) (h : ∀ w, a = some w → b = some w) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem bool_eq_of_toNat_eq {a b : Bool} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

/-- An extension that records no new fact is the identity. -/
theorem ReachCell.eq_of_le_of_weight_le {c d : ReachCell}
    (h : ReachCell.Le c d) (hw : d.weight ≤ c.weight) : c = d := by
  have h1 := h.toNat_retrievable
  have h2 := h.toNat_old
  have h3 := h.toNat_new
  have hwc : c.weight = c.retrievable.toNat + c.oldWitness.isSome.toNat +
      c.newWitness.isSome.toNat := rfl
  have hwd : d.weight = d.retrievable.toNat + d.oldWitness.isSome.toNat +
      d.newWitness.isSome.toNat := rfl
  have hre : c.retrievable = d.retrievable := bool_eq_of_toNat_eq (by omega)
  have hoe : c.oldWitness.isSome = d.oldWitness.isSome := bool_eq_of_toNat_eq (by omega)
  have hne : c.newWitness.isSome = d.newWitness.isSome := bool_eq_of_toNat_eq (by omega)
  obtain ⟨cr, co, cn⟩ := c
  obtain ⟨dr, do', dn⟩ := d
  simp only at hre hoe hne h ⊢
  have e1 : cr = dr := hre
  have e2 : co = do' := option_eq_of_isSome_eq hoe h.old
  have e3 : cn = dn := option_eq_of_isSome_eq hne h.new
  subst e1; subst e2; subst e3; rfl

/-! ### Context fragment -/

/--
Context as an array of hypothesis types (oldest at index 0).
`newFrom` is the first index belonging to `Γnew`.
-/
structure ReachCtx (n : Nat) where
  hyps : Array (Object n)
  newFrom : Nat := 0
  deriving Repr

def ReachCtx.isNew {n : Nat} (Γ : ReachCtx n) (hypIdx : Nat) : Bool :=
  decide (Γ.newFrom ≤ hypIdx)

def ReachCtx.roots {n : Nat} (Γ : ReachCtx n) (goal : Object n) : List (Object n) :=
  goal :: Γ.hyps.toList

/-! ### Fixed-point state -/

structure ReachState (n : Nat) where
  types : Array (Object n)
  cells : Array ReachCell
  inconsistent : Bool := false
  deriving Repr

def ReachState.findTypeIdx {n : Nat} (σ : ReachState n) (A : Object n) : Option Nat :=
  σ.types.findIdx? (· == A)

def ReachState.getCell {n : Nat} (σ : ReachState n) (i : Nat) : ReachCell :=
  match σ.cells[i]? with
  | some c => c
  | none => ReachCell.empty

def ReachState.setCell {n : Nat} (σ : ReachState n) (i : Nat) (c : ReachCell) : ReachState n :=
  if h : i < σ.cells.size then
    { σ with cells := σ.cells.set i c }
  else
    σ

def ReachState.typeAt {n : Nat} (σ : ReachState n) (i : Nat) : Option (Object n) :=
  σ.types[i]?

/-! ### State extension order and the missing-facts measure -/

variable {n : Nat}

theorem ReachState.ext {σ τ : ReachState n} (ht : σ.types = τ.types)
    (hc : σ.cells = τ.cells) (hi : σ.inconsistent = τ.inconsistent) : σ = τ := by
  cases σ; cases τ
  simp only [ReachState.mk.injEq]
  exact ⟨ht, hc, hi⟩

/-- Same type table, no fact ever withdrawn. -/
structure ReachState.Le (σ τ : ReachState n) : Prop where
  types : σ.types = τ.types
  size : σ.cells.size = τ.cells.size
  cell : ∀ i, ReachCell.Le (σ.getCell i) (τ.getCell i)
  inconsistent : σ.inconsistent = true → τ.inconsistent = true

theorem ReachState.Le.refl (σ : ReachState n) : ReachState.Le σ σ :=
  ⟨rfl, rfl, fun _ => ReachCell.Le.refl _, fun h => h⟩

theorem ReachState.Le.trans {σ τ υ : ReachState n}
    (h₁ : ReachState.Le σ τ) (h₂ : ReachState.Le τ υ) : ReachState.Le σ υ :=
  ⟨h₁.types.trans h₂.types, h₁.size.trans h₂.size,
   fun i => (h₁.cell i).trans (h₂.cell i),
   fun h => h₂.inconsistent (h₁.inconsistent h)⟩

@[simp] theorem ReachState.setCell_types (σ : ReachState n) (i : Nat) (c : ReachCell) :
    (σ.setCell i c).types = σ.types := by
  unfold ReachState.setCell; split <;> rfl

@[simp] theorem ReachState.setCell_inconsistent (σ : ReachState n) (i : Nat)
    (c : ReachCell) : (σ.setCell i c).inconsistent = σ.inconsistent := by
  unfold ReachState.setCell; split <;> rfl

@[simp] theorem ReachState.setCell_size (σ : ReachState n) (i : Nat) (c : ReachCell) :
    (σ.setCell i c).cells.size = σ.cells.size := by
  unfold ReachState.setCell; split
  · simp
  · rfl

theorem ReachState.getCell_setCell_self {σ : ReachState n} {i : Nat} {c : ReachCell}
    (h : i < σ.cells.size) : (σ.setCell i c).getCell i = c := by
  simp [ReachState.setCell, dif_pos h, ReachState.getCell,
    Array.getElem?_set_self h]

theorem ReachState.getCell_setCell_ne {σ : ReachState n} {i j : Nat} {c : ReachCell}
    (h : i ≠ j) : (σ.setCell i c).getCell j = σ.getCell j := by
  unfold ReachState.setCell
  split
  · rename_i hlt
    simp [ReachState.getCell, Array.getElem?_set_ne hlt h]
  · rfl

theorem ReachState.le_setCell {σ : ReachState n} {i : Nat} {c : ReachCell}
    (h : ReachCell.Le (σ.getCell i) c) : ReachState.Le σ (σ.setCell i c) := by
  by_cases hlt : i < σ.cells.size
  · refine ⟨by simp, by simp, ?_, by simp⟩
    intro j
    by_cases hj : i = j
    · subst hj; rw [ReachState.getCell_setCell_self hlt]; exact h
    · rw [ReachState.getCell_setCell_ne hj]; exact ReachCell.Le.refl _
  · have : σ.setCell i c = σ := by simp [ReachState.setCell, dif_neg hlt]
    rw [this]; exact ReachState.Le.refl σ

theorem ReachState.le_inconsistent (σ : ReachState n) :
    ReachState.Le σ { σ with inconsistent := true } :=
  ⟨rfl, rfl, fun _ => ReachCell.Le.refl _, fun _ => rfl⟩


/--
Extend a cell with one derivation at provenance `usesNew`.
Old-only and uses-new slots are independent: recording one never erases the other,
and the first witness found for a slot is kept.
-/
def ReachCell.record (c : ReachCell) (usesNew : Bool) (w : Witness) : ReachCell :=
  if usesNew then
    match c.newWitness with
    | some _ => c
    | none => { c with newWitness := some w }
  else
    match c.oldWitness with
    | some _ => c
    | none => { c with oldWitness := some w }

/-- `record` together with direct retrievability from a context binding. -/
def ReachCell.recordHyp (c : ReachCell) (usesNew : Bool) (w : Witness) : ReachCell :=
  { c.record usesNew w with retrievable := true }

theorem ReachCell.le_record (c : ReachCell) (b : Bool) (w : Witness) :
    ReachCell.Le c (c.record b w) := by
  unfold ReachCell.record
  split
  · split
    · exact ReachCell.Le.refl _
    · exact ⟨fun h => h, fun _ h => h, fun _ h => by rename_i he _; simp [he] at h⟩
  · split
    · exact ReachCell.Le.refl _
    · exact ⟨fun h => h, fun _ h => by rename_i he _; simp [he] at h, fun _ h => h⟩

theorem ReachCell.le_recordHyp (c : ReachCell) (b : Bool) (w : Witness) :
    ReachCell.Le c (c.recordHyp b w) :=
  ⟨fun _ => rfl, fun v h => (c.le_record b w).old v h,
   fun v h => (c.le_record b w).new v h⟩

/-- Flag inconsistency when the discovered type is `0`. -/
def ReachState.markInconsistentIf {n : Nat} (σ : ReachState n) (A : Object n) :
    ReachState n :=
  if A == (.never : Object n) then { σ with inconsistent := true } else σ

/-- Record a derivation of the type at table index `i`. -/
def ReachState.discover {n : Nat} (σ : ReachState n) (i : Nat) (usesNew : Bool)
    (w : Witness) : ReachState n :=
  match σ.typeAt i with
  | none => σ
  | some A => (σ.setCell i ((σ.getCell i).record usesNew w)).markInconsistentIf A

/-- Mark a context hypothesis as retrievable (and deducible) at its provenance. -/
def ReachState.markHyp {n : Nat} (σ : ReachState n) (Γ : ReachCtx n) (hypIdx : Nat) :
    ReachState n :=
  match Γ.hyps[hypIdx]? with
  | none => σ
  | some A =>
    match σ.findTypeIdx A with
    | none => σ
    | some i =>
      (σ.setCell i
        ((σ.getCell i).recordHyp (Γ.isNew hypIdx) (.ctxVar hypIdx))).markInconsistentIf A

/-! ### Forward-chaining rules

The sweep is a left fold over individually monotone rules. Each rule only ever
calls `discover` or `markHyp`, which add facts and never remove them.
-/

/-- Seed a positive hypothesis: it is directly retrievable. -/
def seedHypRule (Γ : ReachCtx n) (σ : ReachState n) (i : Nat) : ReachState n :=
  match Γ.hyps[i]? with
  | some A => if objectPolarity A == .pos then σ.markHyp Γ i else σ
  | none => σ

/-- η-available unit (negative; supports applications with unit domain). -/
def unitEtaRule (σ : ReachState n) : ReachState n :=
  match σ.findTypeIdx (.unit : Object n) with
  | some uIdx => σ.discover uIdx false .unit
  | none => σ

/-- Project a product hypothesis; the binding itself justifies both projections. -/
def hypProdRule (Γ : ReachCtx n) (σ : ReachState n) (i : Nat) (L R : Object n) :
    ReachState n :=
  match σ.findTypeIdx (.prod L R), σ.findTypeIdx L, σ.findTypeIdx R with
  | some pIdx, some lIdx, some rIdx =>
      (σ.discover lIdx (Γ.isNew i) (.fst pIdx)).discover rIdx (Γ.isNew i) (.snd pIdx)
  | _, _, _ => σ

/-- Apply a function hypothesis once its argument type is deducible. -/
def hypAppRule (Γ : ReachCtx n) (σ : ReachState n) (i : Nat) (Arg Ret : Object n) :
    ReachState n :=
  match σ.findTypeIdx Arg, σ.findTypeIdx Ret with
  | some aIdx, some rIdx =>
      if (σ.getCell aIdx).simplyDeducible then
        σ.discover rIdx ((σ.getCell aIdx).usesNew || Γ.isNew i) (.app i aIdx)
      else σ
  | _, _ => σ

/-- Close under the hypothesis at index `i`. -/
def hypRule (Γ : ReachCtx n) (σ : ReachState n) (i : Nat) : ReachState n :=
  match Γ.hyps[i]? with
  | some (.prod L R) => hypProdRule Γ σ i L R
  | some (.exp Arg Ret) => hypAppRule Γ σ i Arg Ret
  | _ => σ

/-- Project a deducible product type, or make it η-available from its components. -/
def prodTypeRule (σ : ReachState n) (ti : Nat) (L R : Object n) : ReachState n :=
  if (σ.getCell ti).simplyDeducible then
    match σ.findTypeIdx L, σ.findTypeIdx R with
    | some lIdx, some rIdx =>
        (σ.discover lIdx (σ.getCell ti).usesNew (.fst ti)).discover rIdx
          (σ.getCell ti).usesNew (.snd ti)
    | _, _ => σ
  else
    match σ.findTypeIdx L, σ.findTypeIdx R with
    | some lIdx, some rIdx =>
        if (σ.getCell lIdx).simplyDeducible && (σ.getCell rIdx).simplyDeducible then
          σ.discover ti ((σ.getCell lIdx).usesNew || (σ.getCell rIdx).usesNew) .eta
        else σ
    | _, _ => σ

/-- Function η / identity expansion: `Ret` deducible makes `Arg → Ret` available. -/
def expEtaRule (σ : ReachState n) (ti : Nat) (Ret : Object n) : ReachState n :=
  if !(σ.getCell ti).simplyDeducible then
    match σ.findTypeIdx Ret with
    | some rIdx =>
        if (σ.getCell rIdx).simplyDeducible then
          σ.discover ti (σ.getCell rIdx).usesNew .eta
        else σ
    | none => σ
  else σ

/-- Fire a deducible function type once its argument type is deducible. -/
def expAppRule (σ : ReachState n) (ti : Nat) (Arg Ret : Object n) : ReachState n :=
  if (σ.getCell ti).simplyDeducible then
    match σ.findTypeIdx Arg, σ.findTypeIdx Ret with
    | some aIdx, some rIdx =>
        if (σ.getCell aIdx).simplyDeducible then
          σ.discover rIdx ((σ.getCell ti).usesNew || (σ.getCell aIdx).usesNew)
            (.appTy ti aIdx)
        else σ
    | _, _ => σ
  else σ

/-- Synthesize a coproduct from whichever injection has a deducible payload. -/
def coprodTypeRule (σ : ReachState n) (ti : Nat) (L R : Object n) : ReachState n :=
  if !(σ.getCell ti).simplyDeducible then
    match σ.findTypeIdx L, σ.findTypeIdx R with
    | some lIdx, some rIdx =>
        if (σ.getCell lIdx).simplyDeducible then
          σ.discover ti (σ.getCell lIdx).usesNew (.inl lIdx)
        else if (σ.getCell rIdx).simplyDeducible then
          σ.discover ti (σ.getCell rIdx).usesNew (.inr rIdx)
        else σ
    | _, _ => σ
  else σ

/-- Close under the subformula-table entry at index `ti`. -/
def typeRule (σ : ReachState n) (ti : Nat) : ReachState n :=
  match σ.typeAt ti with
  | some (.prod L R) => prodTypeRule σ ti L R
  | some (.exp Arg Ret) => expAppRule (expEtaRule σ ti Ret) ti Arg Ret
  | some (.coprod L R) => coprodTypeRule σ ti L R
  | _ => σ

/-- One forward-chaining sweep. -/
def reachSweep (Γ : ReachCtx n) (σ : ReachState n) : ReachState n :=
  (List.range Γ.hyps.size).foldl (hypRule Γ)
    (unitEtaRule ((List.range Γ.hyps.size).foldl (seedHypRule Γ) σ))

def reachStep (Γ : ReachCtx n) (σ : ReachState n) : ReachState n :=
  (List.range (reachSweep Γ σ).types.size).foldl typeRule (reachSweep Γ σ)

/-- Initialize cells for the subformula universe and seed `Γ`. -/
def mkReachState (Γ : ReachCtx n) (goal : Object n) : ReachState n :=
  (List.range Γ.hyps.size).foldl (seedHypRule Γ)
    { types := subformulaClosure (Γ.roots goal)
      cells := Array.replicate (subformulaClosure (Γ.roots goal)).size ReachCell.empty }

/-! ### Monotonicity of the sweep -/

theorem ReachState.le_markInconsistentIf (σ : ReachState n) (A : Object n) :
    ReachState.Le σ (σ.markInconsistentIf A) := by
  unfold ReachState.markInconsistentIf
  split
  · exact ReachState.le_inconsistent σ
  · exact ReachState.Le.refl σ

theorem ReachState.le_discover (σ : ReachState n) (i : Nat) (b : Bool) (w : Witness) :
    ReachState.Le σ (σ.discover i b w) := by
  unfold ReachState.discover
  split
  · exact ReachState.Le.refl σ
  · exact (ReachState.le_setCell (ReachCell.le_record _ b w)).trans
      (ReachState.le_markInconsistentIf _ _)

theorem ReachState.le_markHyp (σ : ReachState n) (Γ : ReachCtx n) (i : Nat) :
    ReachState.Le σ (σ.markHyp Γ i) := by
  unfold ReachState.markHyp
  split
  · exact ReachState.Le.refl σ
  · split
    · exact ReachState.Le.refl σ
    · exact (ReachState.le_setCell (ReachCell.le_recordHyp _ _ _)).trans
        (ReachState.le_markInconsistentIf _ _)

theorem seedHypRule_le (Γ : ReachCtx n) (σ : ReachState n) (i : Nat) :
    ReachState.Le σ (seedHypRule Γ σ i) := by
  unfold seedHypRule
  split
  · split
    · exact ReachState.le_markHyp σ Γ i
    · exact ReachState.Le.refl σ
  · exact ReachState.Le.refl σ

local macro "reach_mono" : tactic =>
  `(tactic| repeat' first
      | exact ReachState.Le.refl _
      | exact ReachState.le_discover _ _ _ _
      | exact (ReachState.le_discover _ _ _ _).trans (ReachState.le_discover _ _ _ _)
      | split)

theorem unitEtaRule_le (σ : ReachState n) : ReachState.Le σ (unitEtaRule σ) := by
  unfold unitEtaRule; reach_mono

theorem hypProdRule_le (Γ : ReachCtx n) (σ : ReachState n) (i : Nat) (L R : Object n) :
    ReachState.Le σ (hypProdRule Γ σ i L R) := by
  unfold hypProdRule; reach_mono

theorem hypAppRule_le (Γ : ReachCtx n) (σ : ReachState n) (i : Nat) (Arg Ret : Object n) :
    ReachState.Le σ (hypAppRule Γ σ i Arg Ret) := by
  unfold hypAppRule; reach_mono

theorem hypRule_le (Γ : ReachCtx n) (σ : ReachState n) (i : Nat) :
    ReachState.Le σ (hypRule Γ σ i) := by
  unfold hypRule
  split
  · exact hypProdRule_le Γ σ i _ _
  · exact hypAppRule_le Γ σ i _ _
  · exact ReachState.Le.refl σ

theorem prodTypeRule_le (σ : ReachState n) (ti : Nat) (L R : Object n) :
    ReachState.Le σ (prodTypeRule σ ti L R) := by
  unfold prodTypeRule; reach_mono

theorem expEtaRule_le (σ : ReachState n) (ti : Nat) (Ret : Object n) :
    ReachState.Le σ (expEtaRule σ ti Ret) := by
  unfold expEtaRule; reach_mono

theorem expAppRule_le (σ : ReachState n) (ti : Nat) (Arg Ret : Object n) :
    ReachState.Le σ (expAppRule σ ti Arg Ret) := by
  unfold expAppRule; reach_mono

theorem coprodTypeRule_le (σ : ReachState n) (ti : Nat) (L R : Object n) :
    ReachState.Le σ (coprodTypeRule σ ti L R) := by
  unfold coprodTypeRule; reach_mono

theorem typeRule_le (σ : ReachState n) (ti : Nat) :
    ReachState.Le σ (typeRule σ ti) := by
  unfold typeRule
  split
  · exact prodTypeRule_le σ ti _ _
  · exact (expEtaRule_le σ ti _).trans (expAppRule_le _ ti _ _)
  · exact coprodTypeRule_le σ ti _ _
  · exact ReachState.Le.refl σ

theorem foldl_le {α : Type} (f : ReachState n → α → ReachState n)
    (hf : ∀ σ a, ReachState.Le σ (f σ a)) :
    ∀ (l : List α) (σ : ReachState n), ReachState.Le σ (l.foldl f σ)
  | [], σ => ReachState.Le.refl σ
  | a :: l, σ => (hf σ a).trans (foldl_le f hf l (f σ a))

theorem reachSweep_le (Γ : ReachCtx n) (σ : ReachState n) :
    ReachState.Le σ (reachSweep Γ σ) :=
  ((foldl_le (seedHypRule Γ) (fun σ i => seedHypRule_le Γ σ i) _ σ).trans
      (unitEtaRule_le _)).trans
    (foldl_le (hypRule Γ) (fun σ i => hypRule_le Γ σ i) _ _)

theorem reachStep_le (Γ : ReachCtx n) (σ : ReachState n) :
    ReachState.Le σ (reachStep Γ σ) :=
  (reachSweep_le Γ σ).trans (foldl_le typeRule (fun σ i => typeRule_le σ i) _ _)

/-! ### The missing-facts measure -/

private def natSum : List Nat → Nat
  | [] => 0
  | a :: l => a + natSum l

private theorem natSum_map_le {α : Type} {f g : α → Nat} :
    ∀ (l : List α), (∀ a ∈ l, f a ≤ g a) → natSum (l.map f) ≤ natSum (l.map g)
  | [], _ => Nat.le_refl _
  | a :: l, h => by
      have hd := h a (List.mem_cons_self ..)
      have tl := natSum_map_le l fun b hb => h b (List.mem_cons_of_mem _ hb)
      simp only [List.map_cons, natSum]
      omega

private theorem natSum_map_eq_of_le {α : Type} {f g : α → Nat} :
    ∀ (l : List α), (∀ a ∈ l, f a ≤ g a) →
      natSum (l.map g) ≤ natSum (l.map f) → ∀ a ∈ l, f a = g a
  | [], _, _ => by simp
  | a :: l, h, hs => by
      have hd := h a (List.mem_cons_self ..)
      have hle := natSum_map_le l fun b hb => h b (List.mem_cons_of_mem _ hb)
      simp only [List.map_cons, natSum] at hs
      have hfa : f a = g a := by omega
      have htail := natSum_map_eq_of_le l
        (fun b hb => h b (List.mem_cons_of_mem _ hb)) (by omega)
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hfa
      · exact htail b hb

private theorem natSum_map_le_const {α : Type} {f : α → Nat} {k : Nat} :
    ∀ (l : List α), (∀ a ∈ l, f a ≤ k) → natSum (l.map f) ≤ k * l.length
  | [], _ => by simp [natSum]
  | a :: l, h => by
      have hd := h a (List.mem_cons_self ..)
      have tl := natSum_map_le_const l fun b hb => h b (List.mem_cons_of_mem _ hb)
      simp only [List.map_cons, natSum, List.length_cons]
      have hmul : k * (l.length + 1) = k * l.length + k := Nat.mul_succ k l.length
      omega

/-- Facts recorded so far: one bit for inconsistency plus three per cell. -/
def ReachState.weight (σ : ReachState n) : Nat :=
  σ.inconsistent.toNat +
    natSum ((List.range σ.cells.size).map fun i => (σ.getCell i).weight)

/-- Total number of facts the finite table can hold. -/
def ReachState.capacity (σ : ReachState n) : Nat :=
  1 + 3 * σ.cells.size

theorem ReachState.weight_le_capacity (σ : ReachState n) :
    σ.weight ≤ σ.capacity := by
  have h := natSum_map_le_const (f := fun i => (σ.getCell i).weight) (k := 3)
    (List.range σ.cells.size) (fun i _ => ReachCell.weight_le_three _)
  simp only [List.length_range] at h
  have hb : σ.inconsistent.toNat ≤ 1 := by cases σ.inconsistent <;> simp
  simp only [ReachState.weight, ReachState.capacity]
  omega

theorem ReachState.weight_le_of_le {σ τ : ReachState n} (h : ReachState.Le σ τ) :
    σ.weight ≤ τ.weight := by
  have hcells : natSum ((List.range σ.cells.size).map fun i => (σ.getCell i).weight) ≤
      natSum ((List.range τ.cells.size).map fun i => (τ.getCell i).weight) := by
    rw [← h.size]
    exact natSum_map_le _ fun i _ => ReachCell.weight_le_of_le (h.cell i)
  have hb : σ.inconsistent.toNat ≤ τ.inconsistent.toNat := by
    cases hi : σ.inconsistent
    · simp
    · simp [h.inconsistent hi]
  simp only [ReachState.weight]
  omega

/-- A sweep that records no new fact has reached the fixed point. -/
theorem ReachState.eq_of_le_of_weight_le {σ τ : ReachState n}
    (h : ReachState.Le σ τ) (hw : τ.weight ≤ σ.weight) : σ = τ := by
  have hsize := h.size
  have hcells : natSum ((List.range σ.cells.size).map fun i => (σ.getCell i).weight) ≤
      natSum ((List.range τ.cells.size).map fun i => (τ.getCell i).weight) := by
    rw [← hsize]
    exact natSum_map_le _ fun i _ => ReachCell.weight_le_of_le (h.cell i)
  have hb : σ.inconsistent.toNat ≤ τ.inconsistent.toNat := by
    cases hi : σ.inconsistent
    · simp
    · simp [h.inconsistent hi]
  have hwσ : σ.weight = σ.inconsistent.toNat +
      natSum ((List.range σ.cells.size).map fun i => (σ.getCell i).weight) := rfl
  have hwτ : τ.weight = τ.inconsistent.toNat +
      natSum ((List.range τ.cells.size).map fun i => (τ.getCell i).weight) := rfl
  have hbEq : σ.inconsistent.toNat = τ.inconsistent.toNat := by omega
  have hsumEq : natSum ((List.range τ.cells.size).map fun i => (τ.getCell i).weight) ≤
      natSum ((List.range σ.cells.size).map fun i => (σ.getCell i).weight) := by omega
  have hpoint : ∀ i ∈ List.range σ.cells.size,
      (σ.getCell i).weight = (τ.getCell i).weight :=
    natSum_map_eq_of_le (f := fun i => (σ.getCell i).weight)
      (g := fun i => (τ.getCell i).weight) _
      (fun i _ => ReachCell.weight_le_of_le (h.cell i))
      (by rw [← hsize] at hsumEq; exact hsumEq)
  have hcellEq : ∀ i, i < σ.cells.size → σ.getCell i = τ.getCell i := fun i hi =>
    ReachCell.eq_of_le_of_weight_le (h.cell i)
      (Nat.le_of_eq (hpoint i (List.mem_range.mpr hi)).symm)
  have harr : σ.cells = τ.cells := by
    refine Array.ext hsize ?_
    intro i hi₁ hi₂
    have := hcellEq i hi₁
    simpa [ReachState.getCell, Array.getElem?_eq_getElem hi₁,
      Array.getElem?_eq_getElem hi₂] using this
  exact ReachState.ext h.types harr (bool_eq_of_toNat_eq hbEq)

/-! ### Fuel-free least fixed point -/

/--
Iterate the sweep until it records nothing new. Each iteration that recurses
strictly increases the number of recorded facts, which is bounded by the
capacity of the finite table, so no fuel parameter is needed.
-/
def runReachabilityFrom (Γ : ReachCtx n) (σ : ReachState n) : ReachState n :=
  if σ.weight < (reachStep Γ σ).weight then
    runReachabilityFrom Γ (reachStep Γ σ)
  else
    reachStep Γ σ
termination_by σ.capacity - σ.weight
decreasing_by
  rename_i hlt
  have hcap : (reachStep Γ σ).capacity = σ.capacity := by
    simp [ReachState.capacity, (reachStep_le Γ σ).size]
  have hle := ReachState.weight_le_capacity (reachStep Γ σ)
  omega

/-- Least fixed point of simple positive reachability. -/
def runReachability (Γ : ReachCtx n) (goal : Object n) : ReachState n :=
  runReachabilityFrom Γ (mkReachState Γ goal)

/-- The result really is a fixed point of the sweep. -/
theorem reachStep_runReachabilityFrom (Γ : ReachCtx n) (σ : ReachState n) :
    reachStep Γ (runReachabilityFrom Γ σ) = runReachabilityFrom Γ σ := by
  induction σ using runReachabilityFrom.induct (Γ := Γ) with
  | case1 σ hlt ih => rw [runReachabilityFrom, if_pos hlt]; exact ih
  | case2 σ hlt =>
      have hle := reachStep_le Γ σ
      have hstep : σ = reachStep Γ σ :=
        ReachState.eq_of_le_of_weight_le hle (Nat.le_of_not_lt hlt)
      rw [runReachabilityFrom, if_neg hlt]
      exact congrArg (reachStep Γ) hstep.symm

theorem reachStep_runReachability (Γ : ReachCtx n) (goal : Object n) :
    reachStep Γ (runReachability Γ goal) = runReachability Γ goal :=
  reachStep_runReachabilityFrom Γ _

theorem le_runReachabilityFrom (Γ : ReachCtx n) (σ : ReachState n) :
    ReachState.Le σ (runReachabilityFrom Γ σ) := by
  induction σ using runReachabilityFrom.induct (Γ := Γ) with
  | case1 σ hlt ih =>
      rw [runReachabilityFrom, if_pos hlt]
      exact (reachStep_le Γ σ).trans ih
  | case2 σ hlt =>
      rw [runReachabilityFrom, if_neg hlt]
      exact reachStep_le Γ σ

/-- Types simply deducible but not yet retrievable (schedule candidates). -/
def pendingWitnesses {n : Nat} (σ : ReachState n) : Array (Object n × Witness) :=
  Id.run do
    let mut out : Array (Object n × Witness) := #[]
    for i in [:σ.types.size] do
      match σ.typeAt i, σ.getCell i with
      | some A, c =>
        if !c.retrievable && objectPolarity A == .pos then
          match c.witness with
          | some w =>
            if w.isNeutral then out := out.push (A, w) else pure ()
          | none => pure ()
      | _, _ => pure ()
    pure out

/-- Helper: is this object simply deducible in the result? -/
def isSimplyDeducible {n : Nat} (σ : ReachState n) (A : Object n) : Bool :=
  match σ.findTypeIdx A with
  | some i => (σ.getCell i).simplyDeducible
  | none => false

/-- Helper: is this object retrievable in the result? -/
def isRetrievable {n : Nat} (σ : ReachState n) (A : Object n) : Bool :=
  match σ.findTypeIdx A with
  | some i => (σ.getCell i).retrievable
  | none => false

/-- Helper: does the recorded derivation use `Γnew`? -/
def usesNew {n : Nat} (σ : ReachState n) (A : Object n) : Bool :=
  match σ.findTypeIdx A with
  | some i => (σ.getCell i).usesNew
  | none => false

/--
Saturation schedule: ordered positive types to observe, each with its first
deterministic witness. Built from reachability; exact term-demanded neutrals
are unioned later by pair-directed saturation.
-/
structure Schedule (n : Nat) where
  entries : Array (Object n × Witness)
  deriving DecidableEq, Repr

def Schedule.empty {n : Nat} : Schedule n :=
  ⟨#[]⟩

def Schedule.size {n : Nat} (s : Schedule n) : Nat :=
  s.entries.size

/--
Consistency schedule: pending positive types whose witness uses `Γnew`,
in subformula-table order (already deterministic; deduped by type index).
-/
def scheduleEntryAt {n : Nat} (σ : ReachState n) (i : Nat) :
    Option (Object n × Witness) :=
  match σ.typeAt i, σ.getCell i with
  | some A, c =>
    if !c.retrievable && objectPolarity A == .pos then
      match c.newWitness with
      | some w => if w.isNeutral then some (A, w) else none
      | none => none
    else none
  | _, _ => none

def buildSchedule {n : Nat} (σ : ReachState n) : Schedule n :=
  ⟨(Array.range σ.types.size).filterMap (scheduleEntryAt σ)⟩

/-- Consistency observations are scheduled at positive types only. -/
theorem objectPolarity_of_mem_buildSchedule {n : Nat} {σ : ReachState n}
    {e : Object n × Witness} (h : e ∈ (buildSchedule σ).entries) :
    objectPolarity e.1 = .pos := by
  rw [buildSchedule, Array.mem_filterMap] at h
  obtain ⟨i, _, hi⟩ := h
  rw [scheduleEntryAt] at hi
  split at hi
  · split at hi
    · rename_i hpol
      split at hi
      · split at hi
        · cases hi
          simp only [Bool.and_eq_true, beq_iff_eq] at hpol
          exact hpol.2
        · exact absurd hi (by simp)
      · exact absurd hi (by simp)
    · exact absurd hi (by simp)
  · exact absurd hi (by simp)

end Equality
end Gimbal
