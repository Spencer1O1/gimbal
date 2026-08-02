/-
  Finite positive-type reachability closure (Milestone 7 spike).

  Computes a least fixed point over the finite subformula universe of a root
  judgment. Does **not** enumerate concrete neutrals: contexts such as
  `x : X, s : X → X` stay finite because only types are tracked, with a single
  first-discovery witness (parent pointer) per type.
-/

import Gimbal.Equality.LambdaSyntax
import Gimbal.Equality.Polarized

namespace Gimbal
namespace Equality

/-! ### Subformula universe -/

/-- Immediate subformulas of an object. -/
def subformulaStep {n : Nat} : Object n → List (Object n)
  | .base _ | .unit | .never => []
  | .prod A B | .coprod A B | .exp A B => [A, B]

/-- Finite subformula closure of a list of roots (deduplicated, stable order). -/
def subformulaClosure {n : Nat} (roots : List (Object n)) (fuel : Nat := 4096) :
    Array (Object n) :=
  let rec go (fuel : Nat) (pending : List (Object n)) (acc : Array (Object n)) :
      Array (Object n) :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      match pending with
      | [] => acc
      | A :: rest =>
        if acc.contains A then
          go fuel rest acc
        else
          go fuel (subformulaStep A ++ rest) (acc.push A)
  go fuel roots #[]

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
  deriving DecidableEq, Repr

/-- Per-type reachability cell. -/
structure ReachCell where
  retrievable : Bool := false
  simplyDeducible : Bool := false
  usesNew : Bool := false
  witness : Option Witness := none
  deriving DecidableEq, Repr

def ReachCell.empty : ReachCell := {}

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

/-- Discover `i` as simply deducible with the given witness (first wins). -/
def ReachState.discover {n : Nat} (σ : ReachState n) (i : Nat) (usesNew : Bool)
    (w : Witness) : ReachState n :=
  match σ.typeAt i with
  | none => σ
  | some A =>
    let c := σ.getCell i
    let c' :=
      if c.simplyDeducible then c
      else { c with simplyDeducible := true, usesNew := usesNew, witness := some w }
    let σ := σ.setCell i c'
    if A == (.never : Object n) then { σ with inconsistent := true } else σ

/-- Mark a context hypothesis as retrievable (and deducible). -/
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
      let c' :=
        { c with
          retrievable := true
          simplyDeducible := true
          usesNew := c.usesNew || usesNew
          witness := match c.witness with
            | some w => some w
            | none => some (.ctxVar hypIdx) }
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
              let c := σ.getCell ti
              if !c.simplyDeducible then
                σ := σ.setCell ti
                  { c with simplyDeducible := true, usesNew := uses }
          | _, _ => pure ()
      | some (.exp Arg Ret) =>
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
        if c.simplyDeducible && !c.retrievable && objectPolarity A == .pos then
          match c.witness with
          | some w => out := out.push (A, w)
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
        if c.simplyDeducible && !c.retrievable && c.usesNew &&
            objectPolarity A == .pos then
          match c.witness with
          | some w => entries := entries.push (A, w)
          | none => pure ()
      | _, _ => pure ()
    pure ⟨entries⟩

end Equality
end Gimbal
