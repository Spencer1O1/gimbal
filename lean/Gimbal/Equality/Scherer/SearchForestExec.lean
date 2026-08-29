/-
  Constructively enumerated path-local forest search.

  This module keeps the existing `Fintype`-based search as a proof oracle, but
  gives executable code an explicit exhaustive list of keys and alternatives.
  No ordering is manufactured from a `Finset`: list order is input data.
-/

import Gimbal.Equality.Scherer.SearchForestRun

namespace Gimbal.Equality.Scherer

/-! ### Explicit finite enumerations -/

/-- An explicit duplicate-free list containing every value of `α`. -/
structure CanonicalEnum (α : Type) where
  elems : List α
  nodup : elems.Nodup
  complete : ∀ x : α, x ∈ elems

namespace CanonicalEnum

variable {α : Type}

/-- Constructive `Fintype` data derived from the explicit list. -/
@[reducible] def toFintype [DecidableEq α] (e : CanonicalEnum α) : Fintype α where
  elems := e.elems.toFinset
  complete x := List.mem_toFinset.mpr (e.complete x)

@[simp] theorem card_toFintype [DecidableEq α] (e : CanonicalEnum α) :
    @Fintype.card α e.toFintype = e.elems.length := by
  change e.elems.toFinset.card = e.elems.length
  exact List.toFinset_card_of_nodup e.nodup

end CanonicalEnum

/--
An alternative system whose runtime enumeration is explicit. Dependency lists
retain occurrences and their order; in particular, duplicate sibling keys are
not contracted.
-/
structure EffectiveAlternativeSystem (K : Type) [DecidableEq K] where
  Alt : K → Type
  altDecidableEq : ∀ k, DecidableEq (Alt k)
  keys : CanonicalEnum K
  alternatives : ∀ k, CanonicalEnum (Alt k)
  deps : ∀ {k}, Alt k → List K

namespace EffectiveAlternativeSystem

variable {K : Type} [DecidableEq K]

instance (sys : EffectiveAlternativeSystem K) (k : K) : DecidableEq (sys.Alt k) :=
  sys.altDecidableEq k

/-- Forget explicit enumeration while retaining a constructive `Fintype`. -/
def toAlternativeSystem (sys : EffectiveAlternativeSystem K) : AlternativeSystem K where
  Alt := sys.Alt
  instDecidableEq := sys.altDecidableEq
  instFintype := fun k => (sys.alternatives k).toFintype
  deps := sys.deps

@[simp] theorem toAlternativeSystem_deps (sys : EffectiveAlternativeSystem K)
    {k : K} (a : sys.Alt k) :
    sys.toAlternativeSystem.deps a = sys.deps a :=
  rfl

end EffectiveAlternativeSystem

/-! ### Constructive remaining-key measure -/

namespace SearchPath

variable {K : Type} [DecidableEq K]

def remainingE (keys : CanonicalEnum K) (path : SearchPath K) : Nat :=
  keys.elems.length - path.keys.length

theorem length_le_enum (keys : CanonicalEnum K) (path : SearchPath K) :
    path.keys.length ≤ keys.elems.length := by
  have hsub : path.keys.toFinset ⊆ keys.elems.toFinset := by
    intro x hx
    exact List.mem_toFinset.mpr (keys.complete x)
  have hcard := Finset.card_le_card hsub
  simpa [List.toFinset_card_of_nodup path.nodup,
    List.toFinset_card_of_nodup keys.nodup] using hcard

theorem remainingE_push_lt (keys : CanonicalEnum K)
    (path : SearchPath K) (k : K) (h : k ∉ path.keys) :
    remainingE keys (path.push k h) < remainingE keys path := by
  simp only [remainingE, push_keys, List.length_cons]
  have hle := length_le_enum keys path
  have hlt : path.keys.length < keys.elems.length := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hsub : path.keys.toFinset ⊆ keys.elems.toFinset := by
      intro x hx
      exact List.mem_toFinset.mpr (keys.complete x)
    have hcard : path.keys.toFinset.card = keys.elems.toFinset.card := by
      simpa [List.toFinset_card_of_nodup path.nodup,
        List.toFinset_card_of_nodup keys.nodup] using heq
    have heqFin : path.keys.toFinset = keys.elems.toFinset :=
      Finset.eq_of_subset_of_card_le hsub hcard.ge
    have hk : k ∈ path.keys.toFinset := by
      rw [heqFin]
      exact List.mem_toFinset.mpr (keys.complete k)
    exact h (List.mem_toFinset.mp hk)
  omega

end SearchPath

/-! ### Executable forest search -/

namespace RunForestExec

variable {K : Type} [DecidableEq K] (sys : EffectiveAlternativeSystem K)

abbrev Oracle : AlternativeSystem K := sys.toAlternativeSystem

/-- Explicit alternative enumeration is exhaustive. -/
theorem mem_alternatives (k : K) (a : sys.Alt k) :
    a ∈ (sys.alternatives k).elems :=
  (sys.alternatives k).complete a

end RunForestExec

/--
Executable path-local AND/OR forest search. The only enumerations inspected at
runtime are the explicit lists in `EffectiveAlternativeSystem`.
-/
def runForestExec {K : Type} [DecidableEq K]
    (sys : EffectiveAlternativeSystem K) (path : SearchPath K) (k : K) :
    Outcome sys.toAlternativeSystem path k :=
  if hin : k ∈ path.keys then
    Outcome.loop hin
  else
    let run := fun k' : K => runForestExec sys (path.push k hin) k'
    match RunForest.searchAlts hin run (sys.alternatives k).elems with
    | .inl s => Outcome.success s
    | .inr blocked =>
        Outcome.failure <|
          RunForest.failureOfBlocked hin fun a =>
            blocked a ((sys.alternatives k).complete a)
termination_by SearchPath.remainingE sys.keys path
decreasing_by
  all_goals
    simpa using SearchPath.remainingE_push_lt sys.keys path k hin

/-! ### Executable completeness and soundness -/

namespace RunForestExec

variable {K : Type} [DecidableEq K] {sys : EffectiveAlternativeSystem K}

theorem success_not_blocked {path : SearchPath K} {k : K}
    (s : Success sys.toAlternativeSystem path k)
    (b : Blocked sys.toAlternativeSystem path k) : False := by
  induction s with
  | intro hnotin a ch ih =>
      cases b with
      | loop hin => exact hnotin hin
      | fail f =>
          cases f with
          | intro _choosePath chooseIdx chooseIdx_lt child =>
              exact ih ⟨chooseIdx a, chooseIdx_lt a⟩ (child a)

theorem success_not_failure {path : SearchPath K} {k : K}
    (s : Success sys.toAlternativeSystem path k)
    (f : Failure sys.toAlternativeSystem path k) : False :=
  success_not_blocked s (.fail f)

theorem runForestExec_eq_success_of {path : SearchPath K} {k : K}
    (s : Success sys.toAlternativeSystem path k) :
    ∃ s' : Success sys.toAlternativeSystem path k,
      runForestExec sys path k = .success s' := by
  match h : runForestExec sys path k with
  | .success s' => exact ⟨s', rfl⟩
  | .failure f => exact (success_not_failure s f).elim
  | .loop hin => exact (s.hnotin hin).elim

theorem success_toAbstractDeriv {path : SearchPath K} {k : K}
    (s : Success sys.toAlternativeSystem path k) :
    Nonempty (AbstractDeriv sys.toAlternativeSystem k) :=
  ⟨s.toAbstractDeriv⟩

theorem avoiding_runForestExec_success {path : SearchPath K} {k : K}
    (d : AbstractDeriv sys.toAlternativeSystem k)
    (hav : AbstractDeriv.Avoiding (sys := sys.toAlternativeSystem) path.keys d) :
    ∃ s : Success sys.toAlternativeSystem path k,
      runForestExec sys path k = .success s :=
  runForestExec_eq_success_of (RunForest.Success.ofAvoiding d hav)

theorem branchSimple_runForestExec_empty_success {k : K}
    (d : AbstractDeriv sys.toAlternativeSystem k)
    (h : AbstractDeriv.BranchSimple (sys := sys.toAlternativeSystem) d) :
    ∃ s : Success sys.toAlternativeSystem SearchPath.empty k,
      runForestExec sys SearchPath.empty k = .success s :=
  avoiding_runForestExec_success d <| by
    simpa [AbstractDeriv.BranchSimple, SearchPath.empty] using h

theorem failure_empty_no_abstractDeriv {k : K}
    (f : Failure sys.toAlternativeSystem SearchPath.empty k) :
    ¬ Nonempty (AbstractDeriv sys.toAlternativeSystem k) := by
  intro ⟨d⟩
  obtain ⟨⟨d', hbr⟩⟩ :=
    AbstractDeriv.exists_branchSimple (sys := sys.toAlternativeSystem) ⟨d⟩
  exact success_not_failure
    (RunForest.Success.ofAvoiding d' (by
      simpa [AbstractDeriv.BranchSimple, SearchPath.empty] using hbr)) f

theorem runForestExec_empty_failure_no_abstractDeriv {k : K}
    (f : Failure sys.toAlternativeSystem SearchPath.empty k)
    (_h : runForestExec sys SearchPath.empty k = .failure f) :
    ¬ Nonempty (AbstractDeriv sys.toAlternativeSystem k) :=
  failure_empty_no_abstractDeriv f

theorem nonempty_iff_runForestExec_empty_success {k : K} :
    Nonempty (AbstractDeriv sys.toAlternativeSystem k) ↔
      ∃ s : Success sys.toAlternativeSystem SearchPath.empty k,
        runForestExec sys SearchPath.empty k = .success s := by
  constructor
  · intro ⟨d⟩
    obtain ⟨⟨d', hbr⟩⟩ :=
      AbstractDeriv.exists_branchSimple (sys := sys.toAlternativeSystem) ⟨d⟩
    exact branchSimple_runForestExec_empty_success d' hbr
  · rintro ⟨s, _hs⟩
    exact success_toAbstractDeriv s

theorem runForestExec_loop_of_mem {path : SearchPath K} {k : K}
    (hin : k ∈ path.keys) :
    runForestExec sys path k = .loop hin := by
  unfold runForestExec
  simp [hin]

end RunForestExec

/-! ### Native executable regressions -/

namespace SearchForestExecFixtures

inductive PairKey where
  | unit
  | pair
  deriving DecidableEq, Repr

inductive PairAlt : PairKey → Type where
  | leaf : PairAlt .unit
  | pairUU : PairAlt .pair
  deriving DecidableEq

def pairSystem : EffectiveAlternativeSystem PairKey where
  Alt := PairAlt
  altDecidableEq := fun k => by cases k <;> infer_instance
  keys :=
    { elems := [.unit, .pair]
      nodup := by decide
      complete := by intro k; cases k <;> simp }
  alternatives := fun k =>
    match k with
    | .unit =>
        { elems := [.leaf]
          nodup := by simp
          complete := by intro a; cases a; simp }
    | .pair =>
        { elems := [.pairUU]
          nodup := by simp
          complete := by intro a; cases a; simp }
  deps := fun {k} a =>
    match k, a with
    | .unit, .leaf => []
    | .pair, .pairUU => [.unit, .unit]

inductive LoopKey where
  | root
  deriving DecidableEq, Repr

inductive LoopAlt : LoopKey → Type where
  | self : LoopAlt .root
  deriving DecidableEq

def loopSystem : EffectiveAlternativeSystem LoopKey where
  Alt := LoopAlt
  altDecidableEq := fun _ => inferInstance
  keys :=
    { elems := [.root]
      nodup := by simp
      complete := by intro k; cases k; simp }
  alternatives := fun k => by
    cases k
    exact
      { elems := [.self]
        nodup := by simp
        complete := by intro a; cases a; simp }
  deps := fun {k} a => by cases k; cases a; exact [.root]

inductive OrderKey where
  | leaf
  | root
  deriving DecidableEq, Repr

inductive OrderAlt : OrderKey → Type where
  | leaf : OrderAlt .leaf
  | bad : OrderAlt .root
  | good : OrderAlt .root
  deriving DecidableEq

def orderSystem : EffectiveAlternativeSystem OrderKey where
  Alt := OrderAlt
  altDecidableEq := fun k => by cases k <;> infer_instance
  keys :=
    { elems := [.leaf, .root]
      nodup := by decide
      complete := by intro k; cases k <;> simp }
  alternatives := fun k =>
    match k with
    | .leaf =>
        { elems := [.leaf]
          nodup := by simp
          complete := by intro a; cases a; simp }
    | .root =>
        { elems := [.bad, .good]
          nodup := by simp
          complete := by intro a; cases a <;> simp }
  deps := fun {k} a =>
    match k, a with
    | .leaf, .leaf => []
    | .root, .bad => [.root]
    | .root, .good => [.leaf]

/-- Runtime-visible outcome tag: success `0`, failure `1`, loop `2`. -/
def outcomeTag {K : Type} [DecidableEq K] {sys : AlternativeSystem K}
    {path : SearchPath K} {k : K} : Outcome sys path k → Nat
  | .success _ => 0
  | .failure _ => 1
  | .loop _ => 2

def pairTag : Nat :=
  outcomeTag (runForestExec pairSystem SearchPath.empty .pair)

def loopEmptyTag : Nat :=
  outcomeTag (runForestExec loopSystem SearchPath.empty .root)

private theorem root_not_empty :
    LoopKey.root ∉ (SearchPath.empty : SearchPath LoopKey).keys :=
  empty_path_not_mem _

def loopNestedTag : Nat :=
  outcomeTag <|
    runForestExec loopSystem
      (SearchPath.empty.push LoopKey.root root_not_empty) .root

def orderTag : Nat :=
  outcomeTag (runForestExec orderSystem SearchPath.empty .root)

#eval pairTag
#eval loopEmptyTag
#eval loopNestedTag
#eval orderTag

theorem pair_exec_success : pairTag = 0 := by native_decide

theorem pair_duplicate_siblings_preserved :
    pairSystem.deps (k := .pair) PairAlt.pairUU = [.unit, .unit] ∧
      (pairSystem.deps (k := .pair) PairAlt.pairUU).count .unit = 2 := by
  native_decide

theorem loop_empty_is_completed_failure : loopEmptyTag = 1 := by native_decide

theorem nested_loop_is_not_failure : loopNestedTag = 2 := by native_decide

theorem bad_then_good_succeeds : orderTag = 0 := by native_decide

theorem bad_is_enumerated_before_good :
    (orderSystem.alternatives .root).elems = [OrderAlt.bad, OrderAlt.good] :=
  rfl

end SearchForestExecFixtures

end Gimbal.Equality.Scherer
