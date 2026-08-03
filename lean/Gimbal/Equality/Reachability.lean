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

/--
Record a derivation at provenance `usesNew`.
Old-only and uses-new slots are independent: discovering one does not erase the other.
-/
def ReachState.discover {n : Nat} (σ : ReachState n) (i : Nat) (usesNew : Bool)
    (w : Witness) : ReachState n :=
  match σ.typeAt i with
  | none => σ
  | some A =>
    let c := σ.getCell i
    let c' :=
      if usesNew then
        match c.newWitness with
        | some _ => c
        | none => { c with newWitness := some w }
      else
        match c.oldWitness with
        | some _ => c
        | none => { c with oldWitness := some w }
    let σ := σ.setCell i c'
    if A == (.never : Object n) then { σ with inconsistent := true } else σ

/-- Mark a context hypothesis as retrievable (and deducible) at its provenance. -/
def ReachState.markHyp {n : Nat} (σ : ReachState n) (Γ : ReachCtx n) (hypIdx : Nat) :
    ReachState n :=
  match Γ.hyps[hypIdx]? with
  | none => σ
  | some A =>
    match σ.findTypeIdx A with
    | none => σ
    | some i =>
      let usesNew := Γ.isNew hypIdx
      let c := σ.getCell i
      let w : Witness := .ctxVar hypIdx
      let c' :=
        if usesNew then
          { c with
            retrievable := true
            newWitness := match c.newWitness with
              | some w0 => some w0
              | none => some w }
        else
          { c with
            retrievable := true
            oldWitness := match c.oldWitness with
              | some w0 => some w0
              | none => some w }
      let σ := σ.setCell i c'
      if A == (.never : Object n) then { σ with inconsistent := true } else σ

/-- One forward-chaining sweep. -/
def reachStep {n : Nat} (Γ : ReachCtx n) (σ : ReachState n) : ReachState n :=
  Id.run do
    let mut σ := σ
    -- Seed positive hypotheses.
    for i in [:Γ.hyps.size] do
      match Γ.hyps[i]? with
      | some A =>
        if objectPolarity A == .pos then
          σ := σ.markHyp Γ i
      | none => pure ()
    -- η-available unit (negative; supports apps with unit domain).
    match σ.findTypeIdx (.unit : Object n) with
    | some uIdx =>
      σ := σ.discover uIdx false .unit
    | none => pure ()
    -- Close under hyp products / functions.
    for i in [:Γ.hyps.size] do
      match Γ.hyps[i]? with
      | some (.prod L R) =>
        -- Product hypotheses are negative; the binding itself is enough to project.
        match σ.findTypeIdx (.prod L R), σ.findTypeIdx L, σ.findTypeIdx R with
        | some pIdx, some lIdx, some rIdx =>
          let uses := Γ.isNew i
          σ := σ.discover lIdx uses (.fst pIdx)
          σ := σ.discover rIdx uses (.snd pIdx)
        | _, _, _ => pure ()
      | some (.exp Arg Ret) =>
        -- Function hypotheses are negative; fire when the argument type is known.
        match σ.findTypeIdx Arg, σ.findTypeIdx Ret with
        | some aIdx, some rIdx =>
          let ac := σ.getCell aIdx
          if ac.simplyDeducible then
            let uses := ac.usesNew || Γ.isNew i
            σ := σ.discover rIdx uses (.app i aIdx)
          else
            pure ()
        | _, _ => pure ()
      | _ => pure ()
    -- Project reachable product types; form η-available products.
    for ti in [:σ.types.size] do
      match σ.typeAt ti with
      | some (.prod L R) =>
        let pc := σ.getCell ti
        if pc.simplyDeducible then
          match σ.findTypeIdx L, σ.findTypeIdx R with
          | some lIdx, some rIdx =>
            σ := σ.discover lIdx pc.usesNew (.fst ti)
            σ := σ.discover rIdx pc.usesNew (.snd ti)
          | _, _ => pure ()
        else
          match σ.findTypeIdx L, σ.findTypeIdx R with
          | some lIdx, some rIdx =>
            let lc := σ.getCell lIdx
            let rc := σ.getCell rIdx
            if lc.simplyDeducible && rc.simplyDeducible then
              -- Product is η-available from components (not scheduled; neg).
              let uses := lc.usesNew || rc.usesNew
              σ := σ.discover ti uses .eta
          | _, _ => pure ()
      | some (.exp Arg Ret) =>
        -- Function η / identity expansion: Ret ⇒ Arg → Ret (negative; not scheduled).
        let fc := σ.getCell ti
        if !fc.simplyDeducible then
          match σ.findTypeIdx Ret with
          | some rIdx =>
            let rc := σ.getCell rIdx
            if rc.simplyDeducible then
              σ := σ.discover ti rc.usesNew .eta
            else
              pure ()
          | none => pure ()
        -- Fire deduced function types when the argument is known.
        let fc := σ.getCell ti
        if fc.simplyDeducible then
          match σ.findTypeIdx Arg, σ.findTypeIdx Ret with
          | some aIdx, some rIdx =>
            let ac := σ.getCell aIdx
            if ac.simplyDeducible then
              let uses := fc.usesNew || ac.usesNew
              σ := σ.discover rIdx uses (.appTy ti aIdx)
            else
              pure ()
          | _, _ => pure ()
      | some (.coprod L R) =>
        -- Synthesize a coproduct from either injection when a payload is known.
        let cc := σ.getCell ti
        if !cc.simplyDeducible then
          match σ.findTypeIdx L, σ.findTypeIdx R with
          | some lIdx, some rIdx =>
            let lc := σ.getCell lIdx
            let rc := σ.getCell rIdx
            if lc.simplyDeducible then
              σ := σ.discover ti lc.usesNew (.inl lIdx)
            else if rc.simplyDeducible then
              σ := σ.discover ti rc.usesNew (.inr rIdx)
            else
              pure ()
          | _, _ => pure ()
      | _ => pure ()
    pure σ

/-- Initialize cells for the subformula universe and seed `Γ`. -/
def mkReachState {n : Nat} (Γ : ReachCtx n) (goal : Object n) : ReachState n :=
  Id.run do
    let types := subformulaClosure (Γ.roots goal)
    let cells := Array.replicate types.size ReachCell.empty
    let mut σ : ReachState n := { types, cells }
    for i in [:Γ.hyps.size] do
      match Γ.hyps[i]? with
      | some A =>
        if objectPolarity A == .pos then
          σ := σ.markHyp Γ i
      | none => pure ()
    pure σ

/-- Least fixed point of simple positive reachability. -/
def runReachability {n : Nat} (Γ : ReachCtx n) (goal : Object n) (fuel : Nat := 256) :
    ReachState n :=
  Id.run do
    let mut σ := mkReachState Γ goal
    for _ in [:fuel] do
      let σ' := reachStep Γ σ
      if σ'.cells == σ.cells && σ'.inconsistent == σ.inconsistent then
        return σ'
      σ := σ'
    pure σ

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
def buildSchedule {n : Nat} (σ : ReachState n) : Schedule n :=
  Id.run do
    let mut entries : Array (Object n × Witness) := #[]
    for i in [:σ.types.size] do
      match σ.typeAt i, σ.getCell i with
      | some A, c =>
        if !c.retrievable && objectPolarity A == .pos then
          match c.newWitness with
          | some w =>
            if w.isNeutral then entries := entries.push (A, w) else pure ()
          | none => pure ()
      | _, _ => pure ()
    pure ⟨entries⟩

end Equality
end Gimbal
