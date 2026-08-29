/-
  Finite count-two state for the Scherer-style selector.

  This module contains no proof search.  Actual representatives may first be
  collected in `Plur`; the recurrence key sees only their capped multiplicity
  in `Ctx2`.  Thus support and origin remain available to later selection code
  without becoming part of the recurrence identity.

  Visits are immutable and branch-local.  Only an empty `New` context spends
  the 0/1/2 allowance for a `(Ctx2, Goal)` key.
-/

import Mathlib.Data.Fintype.BigOperators
import Gimbal.Equality.Scherer.UPlus
import Gimbal.Equality.Scherer.TypeSelectionSpec

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### At most two distinct representatives -/

/-- A canonical finite set containing at most two distinct representatives. -/
abbrev Plur (α : Type) [DecidableEq α] :=
  {s : Finset α // s.card ≤ 2}

namespace Plur

variable {α : Type} [DecidableEq α]

def empty : Plur α := ⟨∅, by simp⟩

def singleton (a : α) : Plur α := ⟨{a}, by simp⟩

/-- Insert while there is room; an already full plural is left unchanged. -/
def insert (a : α) (p : Plur α) : Plur α :=
  if ha : a ∈ p.1 then p
  else if hc : p.1.card < 2 then
    ⟨p.1.cons a ha, by
      rw [Finset.card_cons ha]
      omega⟩
  else p

@[simp] theorem coe_empty : (empty : Plur α).1 = ∅ := rfl

@[simp] theorem coe_singleton (a : α) : (singleton a).1 = {a} := rfl

@[simp] theorem insert_of_mem {a : α} {p : Plur α} (h : a ∈ p.1) :
    insert a p = p := by
  simp [insert, h]

theorem insert_of_notMem_of_card_lt {a : α} {p : Plur α}
    (ha : a ∉ p.1) (hc : p.1.card < 2) :
    (insert a p).1 = p.1.cons a ha := by
  simp [insert, ha, hc]

theorem insert_of_card_eq_two {a : α} {p : Plur α}
    (hc : p.1.card = 2) : insert a p = p := by
  by_cases ha : a ∈ p.1
  · exact insert_of_mem ha
  · simp [insert, ha, hc]

@[simp] theorem card_le_two (p : Plur α) : p.1.card ≤ 2 := p.2

theorem mem_insert_of_mem {a b : α} {p : Plur α} (h : b ∈ p.1) :
    b ∈ (insert a p).1 := by
  unfold insert
  split
  · exact h
  · split
    · simp only [Finset.mem_cons]
      exact Or.inr h
    · exact h

theorem mem_insert_self_of_room {a : α} {p : Plur α}
    (h : p.1.card < 2) : a ∈ (insert a p).1 := by
  by_cases ha : a ∈ p.1
  · simp [insert, ha]
  · simp [insert, ha, h]

@[simp] theorem insert_duplicate (a : α) :
    insert a (singleton a) = singleton a := by
  apply Subtype.ext
  simp [insert]

theorem insert_two_distinct {a b : α} (h : b ≠ a) :
    (insert b (singleton a)).1 = {a, b} := by
  ext x
  simp [insert, h, eq_comm, or_comm]

theorem insert_third_capped {a b c : α} (hab : b ≠ a) :
    insert c (insert b (singleton a)) = insert b (singleton a) := by
  apply insert_of_card_eq_two
  rw [insert_two_distinct hab]
  exact Finset.card_pair (Ne.symm hab)

/-- Explicit finite enumeration for later executable source collection. -/
def all [Fintype α] : Finset (Plur α) := Finset.univ

@[simp] theorem mem_all [Fintype α] (p : Plur α) : p ∈ all :=
  Finset.mem_univ p

end Plur

/-! ### Finite type universe and capped stable contexts -/

/-- Supplied finite positive (`U+`) and stable-formula universes. -/
structure TypeUniverse (sig : Signature) where
  positive : Finset (Pos sig.nBases)
  stable : Finset (StableTy sig.nBases)

deriving instance DecidableEq for Goal

namespace TypeUniverse

/-- The finite goal universe induced by `U+` and the negative stable entries. -/
def goals (U : TypeUniverse sig) : Finset (Goal sig.nBases) :=
  U.positive.image Goal.pos ∪
    U.stable.biUnion fun S =>
      match S with
      | .neg N => {Goal.neg N}
      | .atom _ => ∅

@[simp] theorem pos_mem_goals {U : TypeUniverse sig} {P : Pos sig.nBases}
    (h : P ∈ U.positive) : Goal.pos P ∈ U.goals := by
  simp [goals, h]

@[simp] theorem neg_mem_goals {U : TypeUniverse sig} {N : Neg sig.nBases}
    (h : StableTy.neg N ∈ U.stable) : Goal.neg N ∈ U.goals := by
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨.neg N, h, by simp⟩

end TypeUniverse

/-- An actual goal together with its membership in the supplied finite universe. -/
abbrev BoundedGoal (U : TypeUniverse sig) := {G // G ∈ U.goals}

/-- The canonical three-valued multiplicity used by contexts and visits. -/
inductive Count2 where
  | zero
  | one
  | two
  deriving DecidableEq, Repr

instance : Fintype Count2 where
  elems := {.zero, .one, .two}
  complete c := by cases c <;> simp

namespace Count2

def bump : Count2 → Count2
  | .zero => .one
  | .one => .two
  | .two => .two

/-- Spending a visit fails exactly on the third occurrence. -/
def spend : Count2 → Option Count2
  | .zero => some .one
  | .one => some .two
  | .two => none

@[simp] theorem bump_zero : bump .zero = .one := rfl
@[simp] theorem bump_one : bump .one = .two := rfl
@[simp] theorem bump_two : bump .two = .two := rfl

@[simp] theorem spend_zero : spend .zero = some .one := rfl
@[simp] theorem spend_one : spend .one = some .two := rfl
@[simp] theorem spend_two : spend .two = none := rfl

def ofNatCap : Nat → Count2
  | 0 => .zero
  | 1 => .one
  | _ => .two

def toNat : Count2 → Nat
  | .zero => 0
  | .one => 1
  | .two => 2

@[simp] theorem toNat_le_two (c : Count2) : c.toNat ≤ 2 := by cases c <;> decide

@[simp] theorem card : Fintype.card Count2 = 3 := by native_decide

end Count2

/--
Type-level stable context: one capped multiplicity for each supplied stable
formula.  There is no support, origin, or term identity in this recurrence
state.
-/
abbrev Ctx2 (U : TypeUniverse sig) := (S : ↥U.stable) → Count2

namespace Ctx2

variable {U : TypeUniverse sig}

def empty : Ctx2 U := fun _ => .zero

def insert (Γ : Ctx2 U) (S : ↥U.stable) : Ctx2 U :=
  Function.update Γ S (Γ S).bump

def count (Γ : Ctx2 U) (S : ↥U.stable) : Nat := (Γ S).toNat

@[simp] theorem empty_apply (S : ↥U.stable) : empty S = .zero := rfl

@[simp] theorem insert_same (Γ : Ctx2 U) (S : ↥U.stable) :
    insert Γ S S = (Γ S).bump := by
  simp [insert]

@[simp] theorem insert_other (Γ : Ctx2 U) {S T : ↥U.stable} (h : T ≠ S) :
    insert Γ S T = Γ T := by
  simp [insert, h]

@[simp] theorem count_le_two (Γ : Ctx2 U) (S : ↥U.stable) :
    Γ.count S ≤ 2 := Count2.toNat_le_two _

/-- Project proof-relevant representative buckets to the type-only context. -/
def ofPlur {Rep : Type} [DecidableEq Rep]
    (bucket : (S : ↥U.stable) → Plur Rep) : Ctx2 U :=
  fun S => Count2.ofNatCap (bucket S).1.card

/-- Explicit finite enumeration of all capped type-level contexts. -/
def all : Finset (Ctx2 U) := Finset.univ

@[simp] theorem mem_all (Γ : Ctx2 U) : Γ ∈ all := Finset.mem_univ Γ

theorem card_eq : Fintype.card (Ctx2 U) = 3 ^ U.stable.card := by
  simp [Ctx2, Fintype.card_pi]

end Ctx2

/-! ### Concrete finite recurrence keys -/

structure MemoryKey (U : TypeUniverse sig) where
  context : Ctx2 U
  goal : BoundedGoal U
  deriving DecidableEq

instance (U : TypeUniverse sig) : Fintype (MemoryKey U) :=
  Fintype.ofEquiv (Ctx2 U × BoundedGoal U)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun k => (k.context, k.goal)
      left_inv := by intro p; cases p; rfl
      right_inv := by intro k; cases k; rfl }

namespace MemoryKey

/-- Explicit finite enumeration required by a later executable search. -/
def all (U : TypeUniverse sig) : Finset (MemoryKey U) := Finset.univ

@[simp] theorem mem_all {U : TypeUniverse sig} (k : MemoryKey U) :
    k ∈ all U := Finset.mem_univ k

end MemoryKey

/-! ### Immutable branch-local count-two memory -/

/-- A finite immutable table assigning 0/1/2 visits to every recurrence key. -/
abbrev VisitMemory (U : TypeUniverse sig) := MemoryKey U → Count2

namespace VisitMemory

variable {U : TypeUniverse sig}

def empty : VisitMemory U := fun _ => .zero

def set (m : VisitMemory U) (k : MemoryKey U) (c : Count2) : VisitMemory U :=
  Function.update m k c

/-- Spend one empty-`New` occurrence at `k`; reject its third occurrence. -/
def visitEmpty (m : VisitMemory U) (k : MemoryKey U) : Option (VisitMemory U) :=
  (m k).spend.map fun c => m.set k c

/--
Visit a search state.  A nonempty `New` context represents strict context
growth and does not spend the empty-new repetition allowance.
-/
def visit (New : StableCtx sig) (m : VisitMemory U)
    (k : MemoryKey U) : Option (VisitMemory U) :=
  if New.length = 0 then visitEmpty m k else some m

@[simp] theorem set_same (m : VisitMemory U) (k : MemoryKey U) (c : Count2) :
    m.set k c k = c := by simp [set]

@[simp] theorem set_other (m : VisitMemory U) {k j : MemoryKey U}
    (h : j ≠ k) (c : Count2) : m.set k c j = m j := by
  simp [set, h]

@[simp] theorem empty_apply (k : MemoryKey U) : empty k = .zero := rfl

theorem visitEmpty_eq_none_iff (m : VisitMemory U) (k : MemoryKey U) :
    visitEmpty m k = none ↔ m k = .two := by
  cases h : m k <;> simp [visitEmpty, h]

theorem visitEmpty_zero (m : VisitMemory U) (k : MemoryKey U)
    (h : m k = .zero) : visitEmpty m k = some (m.set k .one) := by
  simp [visitEmpty, h]

theorem visitEmpty_one (m : VisitMemory U) (k : MemoryKey U)
    (h : m k = .one) : visitEmpty m k = some (m.set k .two) := by
  simp [visitEmpty, h]

theorem visit_empty_new (m : VisitMemory U) (k : MemoryKey U) :
    visit (.empty : StableCtx sig) m k = visitEmpty m k := by
  simp [visit, StableCtx.length]

theorem visit_nonempty_new {New : StableCtx sig} (hne : New.length ≠ 0)
    (m : VisitMemory U) (k : MemoryKey U) : visit New m k = some m := by
  simp [visit, hne]

theorem third_empty_new_rejected (m : VisitMemory U) (k : MemoryKey U)
    (h : m k = .two) :
    visit (.empty : StableCtx sig) m k = none := by
  simp [visit_empty_new, visitEmpty_eq_none_iff, h]

theorem nonempty_growth_does_not_spend {New : StableCtx sig}
    (hne : New.length ≠ 0) (m : VisitMemory U) (k : MemoryKey U) :
    visit New m k = some m := visit_nonempty_new hne m k

/-- Forking is copying an immutable incoming table, not sharing mutable state. -/
def fork (m : VisitMemory U) : VisitMemory U × VisitMemory U := (m, m)

@[simp] theorem fork_fst (m : VisitMemory U) : (fork m).1 = m := rfl
@[simp] theorem fork_snd (m : VisitMemory U) : (fork m).2 = m := rfl

theorem sibling_visits_independent {NewL NewR : StableCtx sig}
    {m mL mR : VisitMemory U} {kL kR : MemoryKey U}
    (hL : visit NewL m kL = some mL)
    (hR : visit NewR m kR = some mR) :
    visit NewL (fork m).1 kL = some mL ∧
      visit NewR (fork m).2 kR = some mR := by
  exact ⟨hL, hR⟩

end VisitMemory

/-! ### Boundary fixtures -/

namespace CountTwoFixtures

theorem duplicate_same_representative_remains_one :
    Plur.insert (1 : Fin 3) (Plur.singleton 1) = Plur.singleton 1 :=
  Plur.insert_duplicate 1

def twoRepresentatives : Plur (Fin 3) :=
  Plur.insert 1 (Plur.singleton 0)

theorem two_distinct_same_type_representatives_retained :
    twoRepresentatives.1 = ({0, 1} : Finset (Fin 3)) := by
  simp [twoRepresentatives, Plur.insert_two_distinct]

theorem third_distinct_same_type_representative_capped :
    Plur.insert 2 twoRepresentatives = twoRepresentatives := by
  exact Plur.insert_third_capped (by decide)

abbrev sig1 : Signature := ⟨1, #[]⟩
abbrev q : Fin sig1.nBases := ⟨0, Nat.zero_lt_one⟩
abbrev X : Pos sig1.nBases := .atom q
abbrev AtomS : StableTy sig1.nBases := .atom q
abbrev OneS : StableTy sig1.nBases := .neg .one

def U : TypeUniverse sig1 where
  positive := {X}
  stable := {AtomS, OneS}

theorem atomMem : AtomS ∈ U.stable := by simp [U]
theorem oneMem : OneS ∈ U.stable := by simp [U]
theorem posMem : X ∈ U.positive := by simp [U]

def atomSlot : ↥U.stable := ⟨AtomS, atomMem⟩
def oneSlot : ↥U.stable := ⟨OneS, oneMem⟩

def emptyCtx : Ctx2 U := Ctx2.empty
def oneAtomCtx : Ctx2 U := Ctx2.insert emptyCtx atomSlot

def posGoal : BoundedGoal U :=
  ⟨.pos X, TypeUniverse.pos_mem_goals posMem⟩

def negGoal : BoundedGoal U :=
  ⟨.neg .one, TypeUniverse.neg_mem_goals oneMem⟩

def posKey : MemoryKey U := ⟨emptyCtx, posGoal⟩
def posKeyWithAtom : MemoryKey U := ⟨oneAtomCtx, posGoal⟩
def negKey : MemoryKey U := ⟨emptyCtx, negGoal⟩

theorem different_goals_different_keys : posKey ≠ negKey := by decide

theorem different_context_shapes_different_keys : posKey ≠ posKeyWithAtom := by
  intro h
  have hc := congrArg (fun k : MemoryKey U => k.context atomSlot) h
  simp [posKey, posKeyWithAtom, emptyCtx, oneAtomCtx, Ctx2.empty,
    Ctx2.insert] at hc

def seenOnce : VisitMemory U := VisitMemory.set VisitMemory.empty posKey .one
def seenTwice : VisitMemory U := VisitMemory.set VisitMemory.empty posKey .two

theorem third_empty_repeat_rejected :
    VisitMemory.visit (.empty : StableCtx sig1) seenTwice posKey = none := by
  apply VisitMemory.third_empty_new_rejected
  simp [seenTwice]

def grownNew : StableCtx sig1 := .snoc .empty AtomS

theorem nonempty_new_growth_keeps_memory :
    VisitMemory.visit grownNew seenOnce posKey = some seenOnce := by
  apply VisitMemory.nonempty_growth_does_not_spend
  simp [grownNew, StableCtx.length]

theorem two_siblings_each_accept_second_occurrence :
    ∃ left right,
      VisitMemory.visit (.empty : StableCtx sig1)
          (VisitMemory.fork seenOnce).1 posKey = some left ∧
        VisitMemory.visit (.empty : StableCtx sig1)
          (VisitMemory.fork seenOnce).2 posKey = some right := by
  let next := VisitMemory.set seenOnce posKey .two
  refine ⟨next, next, ?_, ?_⟩
  all_goals
    simp [VisitMemory.visit, VisitMemory.visitEmpty, seenOnce, next,
      VisitMemory.set, StableCtx.length]

end CountTwoFixtures

end Gimbal.Equality.Scherer
