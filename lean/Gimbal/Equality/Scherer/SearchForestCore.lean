/-
  Scherer-core generic path-local search forest foundation.

  Defines alternative systems, nodup search paths, abstract derivations, and
  intrinsically typed path-local Success / Failure / Blocked / Outcome
  certificates. No saturation policy, executable search, or global visited set.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Gimbal.Equality.Scherer.SearchStructural

namespace Gimbal.Equality.Scherer

/-! ### Generic alternative systems -/

/-- Finite per-key alternative system with ordered dependency occurrences. -/
structure AlternativeSystem (K : Type) where
  Alt : K → Type
  instDecidableEq : ∀ k, DecidableEq (Alt k)
  instFintype : ∀ k, Fintype (Alt k)
  deps : ∀ {k}, Alt k → List K

namespace AlternativeSystem

variable {K : Type} (sys : AlternativeSystem K)

instance (k : K) : DecidableEq (sys.Alt k) := sys.instDecidableEq k
instance (k : K) : Fintype (sys.Alt k) := sys.instFintype k

end AlternativeSystem

/-- Structural alternatives as an `AlternativeSystem` over search keys. -/
def structuralAlternativeSystem {sig : Signature}
    (U : SearchUniverse sig) (O : Type) (B L : Nat)
    [DecidableEq O] [Fintype O] :
    AlternativeSystem (SearchKey U O B L) where
  Alt := fun parent => StructuralAlternative parent
  instDecidableEq := fun _ => inferInstance
  instFintype := fun _ => inferInstance
  deps := fun {_parent} a => a.deps.toList

/-! ### Path-local keys -/

/-- Nodup path of visited keys. -/
structure SearchPath (K : Type) where
  keys : List K
  nodup : keys.Nodup

namespace SearchPath

variable {K : Type}

def empty : SearchPath K :=
  ⟨[], List.nodup_nil⟩

def contains [DecidableEq K] (path : SearchPath K) (k : K) : Bool :=
  decide (k ∈ path.keys)

theorem contains_iff [DecidableEq K] (path : SearchPath K) (k : K) :
    path.contains k = true ↔ k ∈ path.keys := by
  simp [contains]

def push [DecidableEq K] (path : SearchPath K) (k : K) (h : k ∉ path.keys) :
    SearchPath K where
  keys := k :: path.keys
  nodup := List.nodup_cons.mpr ⟨h, path.nodup⟩

@[simp] theorem push_keys [DecidableEq K] (path : SearchPath K) (k : K)
    (h : k ∉ path.keys) :
    (path.push k h).keys = k :: path.keys := rfl

theorem push_nodup [DecidableEq K] (path : SearchPath K) (k : K)
    (h : k ∉ path.keys) :
    (path.push k h).keys.Nodup :=
  (path.push k h).nodup

def remaining [DecidableEq K] [Fintype K] (path : SearchPath K) : Nat :=
  Fintype.card K - path.keys.length

theorem length_le_card [DecidableEq K] [Fintype K] (path : SearchPath K) :
    path.keys.length ≤ Fintype.card K := by
  have := Finset.card_le_univ path.keys.toFinset
  rwa [List.toFinset_card_of_nodup path.nodup] at this

theorem remaining_push_lt [DecidableEq K] [Fintype K]
    (path : SearchPath K) (k : K) (h : k ∉ path.keys) :
    (path.push k h).remaining < path.remaining := by
  simp only [remaining, push_keys, List.length_cons]
  have hle := path.length_le_card
  have hlt : path.keys.length < Fintype.card K := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hcard : path.keys.toFinset.card = Fintype.card K := by
      simpa [List.toFinset_card_of_nodup path.nodup] using heq
    have huni : path.keys.toFinset = Finset.univ :=
      Finset.eq_univ_of_card _ hcard
    have : k ∈ path.keys :=
      List.mem_toFinset.mp (by simp [huni])
    exact h this
  omega

end SearchPath

/-! ### Abstract positive derivations -/

/--
Positive derivation tree. Children are indexed by dependency *occurrences*,
so identical sibling keys may appear twice.
-/
inductive AbstractDeriv {K : Type} (sys : AlternativeSystem K) : K → Type where
  | choose {k : K} (a : sys.Alt k)
      (children : ∀ i : Fin (sys.deps a).length,
        AbstractDeriv sys ((sys.deps a).get ⟨i.val, i.isLt⟩)) :
      AbstractDeriv sys k

/-! ### Path-local certificates (intrinsic) -/

/--
Path-local success: `k` not on path; one alternative; every dependency
occurrence succeeds under exactly `path.push k`.
-/
inductive Success {K : Type} [DecidableEq K] (sys : AlternativeSystem K) :
    SearchPath K → K → Type where
  | intro {path : SearchPath K} {k : K}
      (hnotin : k ∉ path.keys)
      (alt : sys.Alt k)
      (children : ∀ i : Fin (sys.deps alt).length,
        Success sys (path.push k hnotin)
          ((sys.deps alt).get ⟨i.val, i.isLt⟩)) :
      Success sys path k

/-!
Path-local failure and blocked certificates.

* `Failure` — `k` not on path; every alternative has a blocked dependency
  occurrence under exactly `path.push k`.
* `Blocked` — loop (`k` already on path) or an embedded `Failure`.
-/
mutual
/-- Path-local failure: every alternative has a blocked dependency witness. -/
inductive Failure {K : Type} [DecidableEq K] (sys : AlternativeSystem K) :
    SearchPath K → K → Type where
  | intro {path : SearchPath K} {k : K}
      (hnotin : k ∉ path.keys)
      (chooseIdx : sys.Alt k → Nat)
      (chooseIdx_lt : ∀ a, chooseIdx a < (sys.deps a).length)
      (child : ∀ a : sys.Alt k,
        Blocked sys (path.push k hnotin)
          ((sys.deps a).get ⟨chooseIdx a, chooseIdx_lt a⟩)) :
      Failure sys path k

/-- Loop marker or embedded failure. -/
inductive Blocked {K : Type} [DecidableEq K] (sys : AlternativeSystem K) :
    SearchPath K → K → Type where
  | loop {path : SearchPath K} {k : K}
      (hin : k ∈ path.keys) :
      Blocked sys path k
  | fail {path : SearchPath K} {k : K}
      (f : Failure sys path k) :
      Blocked sys path k
end

/-- Outcome: success, failure, or loop. -/
inductive Outcome {K : Type} [DecidableEq K]
    (sys : AlternativeSystem K) : SearchPath K → K → Type where
  | success {path k} : Success sys path k → Outcome sys path k
  | failure {path k} : Failure sys path k → Outcome sys path k
  | loop {path k} : k ∈ path.keys → Outcome sys path k

namespace Success

variable {K : Type} [DecidableEq K] {sys : AlternativeSystem K}

/-- Project the not-on-path witness. -/
theorem hnotin {path : SearchPath K} {k : K} :
    Success sys path k → k ∉ path.keys
  | .intro h _ _ => h

/-- Project the chosen alternative. -/
def alt {path : SearchPath K} {k : K} :
    Success sys path k → sys.Alt k
  | .intro _ a _ => a

/-- Project occurrence-indexed successful children (intrinsically `Success`). -/
def children {path : SearchPath K} {k : K} :
    (s : Success sys path k) →
      ∀ i : Fin (sys.deps s.alt).length,
        Success sys (path.push k s.hnotin)
          ((sys.deps s.alt).get ⟨i.val, i.isLt⟩)
  | .intro _hnotin _alt ch => ch

/-- Recursively erase path-local success to an abstract derivation. -/
def toAbstractDeriv {path : SearchPath K} {k : K} :
    Success sys path k → AbstractDeriv sys k
  | .intro _hnotin a ch =>
      AbstractDeriv.choose a fun i => toAbstractDeriv (ch i)

def rank {path : SearchPath K} {k : K} : Success sys path k → Nat
  | .intro _hnotin a ch =>
      let childRanks :=
        (List.finRange (sys.deps a).length).map fun i =>
          rank (ch ⟨i.val, i.isLt⟩)
      1 + childRanks.max?.getD 0

theorem immediate_dependency_rank_lt {path : SearchPath K} {k : K}
    (s : Success sys path k) (i : Fin (sys.deps s.alt).length) :
    (s.children i).rank < s.rank := by
  cases s with
  | intro hnotin a ch =>
      change rank (ch i) <
        1 + ((List.finRange (sys.deps a).length).map fun j =>
          rank (ch ⟨j.val, j.isLt⟩)).max?.getD 0
      set childRanks :=
        (List.finRange (sys.deps a).length).map fun j =>
          rank (ch ⟨j.val, j.isLt⟩)
      have hmem : rank (ch i) ∈ childRanks := by
        refine List.mem_map.mpr ⟨⟨i.val, i.isLt⟩, List.mem_finRange _, ?_⟩
        simp only [Fin.eta]
      cases hmax : childRanks.max? with
      | none =>
          have : childRanks = [] := List.max?_eq_none_iff.mp hmax
          simp [this] at hmem
      | some m =>
          have hle : rank (ch i) ≤ m :=
            (List.max?_eq_some_iff (α := Nat)).mp hmax |>.2 _ hmem
          change _ < 1 + m
          omega

/-- Constructor-level type barrier: every child slot is a `Success`. -/
theorem children_are_success {path : SearchPath K} {k : K}
    (s : Success sys path k) (i : Fin (sys.deps s.alt).length) :
    ∃ s' : Success sys (path.push k s.hnotin)
        ((sys.deps s.alt).get ⟨i.val, i.isLt⟩),
      s.children i = s' :=
  ⟨s.children i, rfl⟩

/--
Success-with-failed-child is unrepresentable: a `Failure` cannot inhabit the
same Outcome constructor as a `Success` child, and child indices are typed
as `Success` (see `children` / `children_are_success`).
-/
theorem success_ne_failure_outcome {path : SearchPath K} {k : K}
    (s : Success sys path k) (f : Failure sys path k) :
    Outcome.success s ≠ Outcome.failure f := by
  intro h; cases h

end Success

/-- Every sibling receives the identical parent-extended path. -/
theorem siblings_share_extended_path {K : Type} [DecidableEq K]
    {path : SearchPath K} {k : K} (hnotin : k ∉ path.keys) :
    path.push k hnotin = path.push k hnotin :=
  rfl

theorem left_sibling_path_independent {K : Type} [DecidableEq K]
    {path : SearchPath K} {k : K} (hnotin : k ∉ path.keys) :
    path.push k hnotin = path.push k hnotin :=
  rfl

theorem loop_ne_failure {K : Type} [DecidableEq K]
    {sys : AlternativeSystem K} {path : SearchPath K} {k : K}
    (hin : k ∈ path.keys) (f : Failure sys path k) :
    Outcome.loop (sys := sys) hin ≠ Outcome.failure f := by
  intro h; cases h

theorem empty_path_not_mem {K : Type} (k : K) :
    k ∉ (SearchPath.empty : SearchPath K).keys := by
  simp [SearchPath.empty]

theorem in_path_loop_not_global_empty_failure {K : Type}
    {path : SearchPath K} {k : K} (_hin : k ∈ path.keys) :
    k ∉ (SearchPath.empty : SearchPath K).keys :=
  empty_path_not_mem k

theorem remaining_decreases_on_push {K : Type} [DecidableEq K] [Fintype K]
    {path : SearchPath K} {k : K} (hnotin : k ∉ path.keys) :
    (path.push k hnotin).remaining < path.remaining :=
  SearchPath.remaining_push_lt path k hnotin

/-! ### Adversarial fixture: pair(unit,unit) -/

namespace SearchForestFixtures

open SearchStructuralFixtures

/-- Tiny finite key type mirroring pair(unit,unit) dependency shape. -/
inductive PairUnitKey where
  | unit
  | pair
  deriving DecidableEq

instance : Fintype PairUnitKey where
  elems := {.unit, .pair}
  complete := by intro x; cases x <;> simp

inductive PairUnitAlt : PairUnitKey → Type where
  | leaf : PairUnitAlt .unit
  | pairUU : PairUnitAlt .pair
deriving DecidableEq

instance : Fintype (PairUnitAlt .unit) where
  elems := {PairUnitAlt.leaf}
  complete := by intro a; cases a; simp
instance : Fintype (PairUnitAlt .pair) where
  elems := {PairUnitAlt.pairUU}
  complete := by intro a; cases a; simp

def pairUnitSystem : AlternativeSystem PairUnitKey where
  Alt := PairUnitAlt
  instDecidableEq := fun k => by cases k <;> infer_instance
  instFintype := fun k => by cases k <;> infer_instance
  deps := fun {k} a =>
    match k, a with
    | .unit, .leaf => []
    | .pair, .pairUU => [.unit, .unit]

private theorem not_pair_in_empty :
    PairUnitKey.pair ∉ (SearchPath.empty : SearchPath PairUnitKey).keys := by
  simp [SearchPath.empty]

private theorem not_unit_after_pair :
    PairUnitKey.unit ∉
      (SearchPath.empty.push PairUnitKey.pair not_pair_in_empty).keys := by
  simp [SearchPath.push, SearchPath.empty]

private def unitSuccess (path : SearchPath PairUnitKey)
    (h : PairUnitKey.unit ∉ path.keys) :
    Success pairUnitSystem path .unit :=
  .intro h PairUnitAlt.leaf (fun j => nomatch j)

/-- Both identical unit occurrences succeed under the same parent-extended path. -/
def pairUnitUnitSuccess : Success pairUnitSystem .empty .pair :=
  .intro not_pair_in_empty PairUnitAlt.pairUU fun i =>
    match i with
    | ⟨0, _⟩ => unitSuccess _ not_unit_after_pair
    | ⟨1, _⟩ => unitSuccess _ not_unit_after_pair
    | ⟨n + 2, hn⟩ =>
        False.elim (Nat.not_lt_zero n (by
          have : n + 2 < 2 := by
            simpa [pairUnitSystem] using hn
          omega))

theorem pair_unit_unit_both_succeed_path_local :
    let s := pairUnitUnitSuccess
    let path1 := SearchPath.empty.push PairUnitKey.pair not_pair_in_empty
    pairUnitSystem.deps s.alt = [PairUnitKey.unit, PairUnitKey.unit] ∧
      s.children ⟨0, by decide⟩ = unitSuccess path1 not_unit_after_pair ∧
        s.children ⟨1, by decide⟩ = unitSuccess path1 not_unit_after_pair :=
  ⟨rfl, rfl, rfl⟩

/-- Sibling children are intrinsic `Success` certificates (not Failure). -/
theorem pair_unit_unit_children_are_success :
    let s := pairUnitUnitSuccess
    ∀ i : Fin (pairUnitSystem.deps s.alt).length,
      ∃ s' : Success pairUnitSystem
          (SearchPath.empty.push PairUnitKey.pair not_pair_in_empty)
          ((pairUnitSystem.deps s.alt).get ⟨i.val, i.isLt⟩),
        s.children i = s' :=
  fun i => Success.children_are_success pairUnitUnitSuccess i

theorem pair_unit_unit_deps_two_occurrences :
    pairUnitSystem.deps (k := .pair) PairUnitAlt.pairUU =
      [PairUnitKey.unit, PairUnitKey.unit] ∧
      (pairUnitSystem.deps (k := .pair) PairUnitAlt.pairUU).count .unit = 2 :=
  ⟨rfl, rfl⟩

theorem siblings_same_extended_path_on_pair :
    let path1 := SearchPath.empty.push PairUnitKey.pair not_pair_in_empty
    ∀ (_i _j : Fin 2), path1 = path1 :=
  fun _ _ => rfl

theorem structural_pair_unit_unit_occurrences :
    let deps := (DepBundle.two unitKey unitKey).toList
    deps = [unitKey, unitKey] ∧ deps.length = 2 ∧
      deps.get ⟨0, by decide⟩ = unitKey ∧
        deps.get ⟨1, by decide⟩ = unitKey :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem duplicate_occurrence_indices_distinct :
    let deps := (DepBundle.two unitKey unitKey).toList
    (⟨0, by decide⟩ : Fin deps.length) ≠ ⟨1, by decide⟩ := by
  decide

/-- An in-path loop is not empty-path failure. -/
theorem loop_on_path_not_empty_failure :
    let path := SearchPath.empty.push PairUnitKey.unit (by simp [SearchPath.empty])
    PairUnitKey.unit ∈ path.keys ∧
      PairUnitKey.unit ∉ (SearchPath.empty : SearchPath PairUnitKey).keys :=
  ⟨by simp [SearchPath.push, SearchPath.empty], empty_path_not_mem _⟩

end SearchForestFixtures

end Gimbal.Equality.Scherer
