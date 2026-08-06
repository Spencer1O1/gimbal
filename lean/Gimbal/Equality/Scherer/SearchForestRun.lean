/-
  Scherer-core executable path-local forest search.

  Full (structural ∪ sat-plan) alternative systems, policy embedding, and a
  fuel-free well-founded `runForest` on `SearchPath.remaining`. Intrinsic
  Success / Failure / Blocked / Outcome certificates are produced; no global
  visited set, sat certification, Sat materialization, or S4.
-/

import Gimbal.Equality.Scherer.SearchLoopElim
import Gimbal.Equality.Scherer.SearchSatPolicy

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Part A — Full alternative system -/

section FullAlt

variable {U : SearchUniverse sig} {O : Type} {B L : Nat}
variable [DecidableEq O] [Fintype O]

/-- All structural and all valid sat-plan alternatives at a search key. -/
inductive AllAlt : SearchKey U O B L → Type where
  | structural {k} (h : ¬ isSaturated k) (a : StructuralAlternative k) : AllAlt k
  | satPlan {k} (h : isSaturated k) (p : SatPlan k) : AllAlt k

namespace AllAlt

def deps {k : SearchKey U O B L} : AllAlt k → List (SearchKey U O B L)
  | .structural _ a => a.deps.toList
  | .satPlan _ p => p.deps

instance (k : SearchKey U O B L) : DecidableEq (AllAlt k) := fun a b =>
  match a, b with
  | .structural _ a₁, .structural _ a₂ =>
      if h : a₁ = a₂ then isTrue (by cases h; rfl)
      else isFalse fun heq => by cases heq; exact h rfl
  | .satPlan _ p₁, .satPlan _ p₂ =>
      if h : p₁ = p₂ then isTrue (by cases h; rfl)
      else isFalse fun heq => by cases heq; exact h rfl
  | .structural _ _, .satPlan _ _ | .satPlan _ _, .structural _ _ =>
      isFalse fun heq => nomatch heq

instance (k : SearchKey U O B L) : Fintype (AllAlt k) := by
  classical
  if hsat : isSaturated k then
    exact Fintype.ofBijective
      (fun p : SatPlan k => AllAlt.satPlan hsat p)
      ⟨fun _ _ h => by cases h; rfl, fun a => by
        cases a with
        | structural hn _ => exact (hn hsat).elim
        | satPlan _ p => exact ⟨p, rfl⟩⟩
  else
    exact Fintype.ofBijective
      (fun a : StructuralAlternative k => AllAlt.structural hsat a)
      ⟨fun _ _ h => by cases h; rfl, fun a => by
        cases a with
        | structural _ a => exact ⟨a, rfl⟩
        | satPlan hs _ => exact (hsat hs).elim⟩

end AllAlt

/-- Full alternative system: every structural alt and every valid sat plan. -/
def fullAlternativeSystem : AlternativeSystem (SearchKey U O B L) where
  Alt := AllAlt
  instDecidableEq := fun _ => inferInstance
  instFintype := fun _ => inferInstance
  deps := fun {_} a => AllAlt.deps a

namespace PolicyAlt

/-- Embed a fixed-policy alternative into the full alternative system. -/
def toAllAlt {π : SatPolicy U O B L} {k : SearchKey U O B L} :
    PolicyAlt π k → AllAlt k
  | .structural h a => .structural h a
  | .saturation P hj =>
      .satPlan ⟨P, hj⟩ (π.choose k P hj)

theorem policy_embed_deps {π : SatPolicy U O B L} {k : SearchKey U O B L}
    (a : PolicyAlt π k) :
    AllAlt.deps (toAllAlt a) = PolicyAlt.deps a := by
  cases a <;> rfl

end PolicyAlt

end FullAlt

/-! ### Part B — Generic executable path-local search -/

namespace RunForest

variable {K : Type} [DecidableEq K] [Fintype K] {sys : AlternativeSystem K}

/-- Map an outcome at a dependency key to a child success / blocked certificate. -/
def outcomeToChild {path : SearchPath K} {k : K} :
    Outcome sys path k →
      Sum (Success sys path k) (Blocked sys path k)
  | .success s => .inl s
  | .failure f => .inr (.fail f)
  | .loop hin => .inr (.loop hin)

/--
Evaluate every dependency occurrence of one alternative under a fixed extended
path. Returns either occurrence-indexed successes, or a blocked witness index.
-/
def evalDeps {path : SearchPath K}
    (run : ∀ k', Outcome sys path k') :
    (deps : List K) →
      Sum
        (∀ i : Fin deps.length, Success sys path (deps.get i))
        (Σ i : Fin deps.length, Blocked sys path (deps.get i))
  | [] => Sum.inl fun i => nomatch i
  | d :: ds =>
      match outcomeToChild (run d) with
      | .inl s =>
          match evalDeps run ds with
          | .inl rest =>
              Sum.inl fun i => Fin.cases s (fun j => rest j) i
          | .inr ⟨i, b⟩ =>
              Sum.inr ⟨i.succ, b⟩
      | .inr b =>
          Sum.inr ⟨⟨0, Nat.succ_pos _⟩, b⟩

/-- Evaluate one alternative's children under `path.push k`. -/
def evalAltChildren {path : SearchPath K} {k : K} (hnotin : k ∉ path.keys)
    (run : ∀ k', Outcome sys (path.push k hnotin) k')
    (a : sys.Alt k) :
    Sum
      (∀ i : Fin (sys.deps a).length,
        Success sys (path.push k hnotin)
          ((sys.deps a).get ⟨i.val, i.isLt⟩))
      (Σ i : Fin (sys.deps a).length,
        Blocked sys (path.push k hnotin)
          ((sys.deps a).get ⟨i.val, i.isLt⟩)) :=
  match evalDeps run (sys.deps a) with
  | .inl ch =>
      Sum.inl fun i => ch ⟨i.val, i.isLt⟩
  | .inr ⟨i, b⟩ =>
      Sum.inr ⟨⟨i.val, i.isLt⟩, b⟩

/--
Search a concrete list of alternatives. First successful alt wins; otherwise
every listed alt contributes a blocked dependency witness.
-/
def searchAlts {path : SearchPath K} {k : K} (hnotin : k ∉ path.keys)
    (run : ∀ k', Outcome sys (path.push k hnotin) k') :
    (alts : List (sys.Alt k)) →
      Sum (Success sys path k)
        (∀ a : sys.Alt k, a ∈ alts →
          Σ i : Fin (sys.deps a).length,
            Blocked sys (path.push k hnotin)
              ((sys.deps a).get ⟨i.val, i.isLt⟩))
  | [] =>
      Sum.inr fun _ h => nomatch h
  | a :: rest =>
      match evalAltChildren hnotin run a with
      | .inl ch =>
          Sum.inl (.intro hnotin a ch)
      | .inr blocked =>
          match searchAlts hnotin run rest with
          | .inl s => Sum.inl s
          | .inr blockedRest =>
              Sum.inr fun b hb =>
                if heq : b = a then
                  heq ▸ blocked
                else
                  blockedRest b <| by
                    rcases List.mem_cons.mp hb with hba | hrest
                    · exact (heq hba).elim
                    · exact hrest

/-- Package a total blocked-family into a path-local `Failure`. -/
def failureOfBlocked {path : SearchPath K} {k : K} (hnotin : k ∉ path.keys)
    (blocked : ∀ a : sys.Alt k,
      Σ i : Fin (sys.deps a).length,
        Blocked sys (path.push k hnotin)
          ((sys.deps a).get ⟨i.val, i.isLt⟩)) :
    Failure sys path k :=
  Failure.intro hnotin
    (fun a => (blocked a).1.val)
    (fun a => (blocked a).1.isLt)
    (fun a => (blocked a).2)

/-- Fintype enumeration of alternatives (noncomputable via Finset.toList). -/
noncomputable def altList (k : K) : List (sys.Alt k) :=
  (Finset.univ : Finset (sys.Alt k)).toList

theorem mem_altList (k : K) (a : sys.Alt k) : a ∈ altList (sys := sys) k :=
  Finset.mem_toList.mpr (Finset.mem_univ a)

end RunForest

/--
Path-local forest search. Terminates by `SearchPath.remaining` (no fuel).
Sibling dependency occurrences share exactly `path.push k`.

Enumeration of alternatives uses `Finset.toList`, so this definition is
`noncomputable`; the algorithm itself is fuel-free and path-local.
-/
noncomputable def runForest {K : Type} [DecidableEq K] [Fintype K]
    (sys : AlternativeSystem K) (path : SearchPath K) (k : K) :
    Outcome sys path k :=
  if hin : k ∈ path.keys then
    Outcome.loop hin
  else
    let run := fun k' : K => runForest sys (path.push k hin) k'
    match RunForest.searchAlts hin run (RunForest.altList (sys := sys) k) with
    | .inl s => Outcome.success s
    | .inr blocked =>
        Outcome.failure <|
          RunForest.failureOfBlocked hin fun a =>
            blocked a (RunForest.mem_altList (sys := sys) k a)
termination_by path.remaining
decreasing_by
  all_goals
    simpa using SearchPath.remaining_push_lt path k hin

/-! ### Part C — Theorems -/

namespace RunForest

variable {K : Type} [DecidableEq K] [Fintype K] {sys : AlternativeSystem K}

/-- Success and blocked certificates at the same path/key are incompatible. -/
theorem success_not_blocked {path : SearchPath K} {k : K}
    (s : Success sys path k) (b : Blocked sys path k) : False := by
  induction s with
  | intro hnotin a ch ih =>
      cases b with
      | loop hin => exact hnotin hin
      | fail f =>
          cases f with
          | intro _choosePath chooseIdx chooseIdx_lt child =>
              exact ih ⟨chooseIdx a, chooseIdx_lt a⟩ (child a)

theorem success_not_failure {path : SearchPath K} {k : K}
    (s : Success sys path k) (f : Failure sys path k) : False :=
  success_not_blocked s (.fail f)

/-- Recursively erase an Avoiding abstract derivation to a path-local Success. -/
def Success.ofAvoiding {path : SearchPath K} {k : K} :
    (d : AbstractDeriv sys k) →
      AbstractDeriv.Avoiding (sys := sys) path.keys d →
        Success sys path k
  | .choose a children, h => by
      have hpair : k ∉ path.keys ∧
          ∀ i, AbstractDeriv.Avoiding (sys := sys) (k :: path.keys) (children i) := by
        cases h with
        | mk hroot hchildren => exact ⟨hroot, hchildren⟩
      exact .intro hpair.1 a fun i => ofAvoiding (children i) (hpair.2 i)

/-- Presence of any Success certificate forces `runForest` to return success. -/
theorem runForest_eq_success_of {path : SearchPath K} {k : K}
    (s : Success sys path k) :
    ∃ s' : Success sys path k, runForest sys path k = .success s' := by
  match h : runForest sys path k with
  | .success s' => exact ⟨s', rfl⟩
  | .failure f => exact (success_not_failure s f).elim
  | .loop hin => exact (s.hnotin hin).elim

/-- `runForest` success projects to a nonempty abstract derivation. -/
theorem runForest_success_toAbstractDeriv {path : SearchPath K} {k : K}
    (s : Success sys path k)
    (_h : runForest sys path k = .success s) :
    Nonempty (AbstractDeriv sys k) :=
  ⟨s.toAbstractDeriv⟩

theorem success_toAbstractDeriv_nonempty {path : SearchPath K} {k : K}
    (s : Success sys path k) :
    Nonempty (AbstractDeriv sys k) :=
  ⟨s.toAbstractDeriv⟩

/-- Path-local Success yields an Avoiding abstract derivation along the path. -/
theorem Success.toAvoiding {path : SearchPath K} {k : K} :
    (s : Success sys path k) →
      AbstractDeriv.Avoiding (sys := sys) path.keys (s.toAbstractDeriv)
  | .intro hnotin a ch =>
      AbstractDeriv.Avoiding.mk hnotin fun i =>
        toAvoiding (ch i)

/-- Avoiding derivations imply `runForest` returns success at that path. -/
theorem avoiding_runForest_success {path : SearchPath K} {k : K}
    (d : AbstractDeriv sys k)
    (hav : AbstractDeriv.Avoiding (sys := sys) path.keys d) :
    ∃ s : Success sys path k, runForest sys path k = .success s :=
  runForest_eq_success_of (Success.ofAvoiding d hav)

/-- Branch-simple implies empty-path Avoiding (definitional on empty keys). -/
theorem branchSimple_avoiding_empty {k : K} {d : AbstractDeriv sys k}
    (h : AbstractDeriv.BranchSimple (sys := sys) d) :
    AbstractDeriv.Avoiding (sys := sys) SearchPath.empty.keys d := by
  simpa [AbstractDeriv.BranchSimple, SearchPath.empty] using h

/-- Branch-simple (empty-forbidden Avoiding) implies empty-path success. -/
theorem branchSimple_runForest_empty_success {k : K}
    (d : AbstractDeriv sys k)
    (h : AbstractDeriv.BranchSimple (sys := sys) d) :
    ∃ s : Success sys SearchPath.empty k,
      runForest sys SearchPath.empty k = .success s :=
  avoiding_runForest_success d (branchSimple_avoiding_empty h)

/-- Empty-path failure rules out any abstract derivation. -/
theorem failure_empty_no_abstractDeriv {k : K}
    (f : Failure sys SearchPath.empty k) :
    ¬ Nonempty (AbstractDeriv sys k) := by
  intro ⟨d⟩
  obtain ⟨⟨d', hbr⟩⟩ := AbstractDeriv.exists_branchSimple (sys := sys) ⟨d⟩
  exact success_not_failure (Success.ofAvoiding d' (branchSimple_avoiding_empty hbr)) f

/-- Empty-path `runForest` failure implies no abstract derivation. -/
theorem runForest_empty_failure_no_abstractDeriv {k : K}
    (f : Failure sys SearchPath.empty k)
    (_h : runForest sys SearchPath.empty k = .failure f) :
    ¬ Nonempty (AbstractDeriv sys k) :=
  failure_empty_no_abstractDeriv f

/-- At the empty path, nonempty abstract derivations ↔ `runForest` success. -/
theorem nonempty_iff_runForest_empty_success {k : K} :
    Nonempty (AbstractDeriv sys k) ↔
      ∃ s : Success sys SearchPath.empty k,
        runForest sys SearchPath.empty k = .success s := by
  constructor
  · intro ⟨d⟩
    obtain ⟨⟨d', hbr⟩⟩ := AbstractDeriv.exists_branchSimple (sys := sys) ⟨d⟩
    exact branchSimple_runForest_empty_success d' hbr
  · rintro ⟨s, hs⟩
    exact runForest_success_toAbstractDeriv s hs

/-- An in-path loop witness is not membership on the empty path. -/
theorem in_path_loop_not_empty_mem {path : SearchPath K} {k : K}
    (_hin : k ∈ path.keys) :
    k ∉ (SearchPath.empty : SearchPath K).keys :=
  empty_path_not_mem k

/-- Same-path loop and failure outcomes are distinct constructors. -/
theorem loop_ne_failure_outcome {path : SearchPath K} {k : K}
    (hin : k ∈ path.keys) (f : Failure sys path k) :
    Outcome.loop (sys := sys) hin ≠ Outcome.failure f :=
  loop_ne_failure hin f

/-- Unfolding: membership on the path yields an immediate loop outcome. -/
theorem runForest_loop_of_mem {path : SearchPath K} {k : K}
    (hin : k ∈ path.keys) :
    runForest sys path k = .loop hin := by
  unfold runForest
  simp [hin]

end RunForest

/-! ### Part D — Fixtures -/

namespace SearchForestRunFixtures

open SearchForestFixtures SearchLoopElimFixtures RunForest

/- PairUnitKey already has Fintype; LoopKey needs one for `runForest`. -/
instance : Fintype LoopKey where
  elems := {LoopKey.root}
  complete := by intro x; cases x; simp

/-! #### 1. pair(unit,unit) succeeds with two sibling successes -/

theorem pair_unit_unit_runForest_succeeds :
    ∃ s : Success pairUnitSystem SearchPath.empty PairUnitKey.pair,
      runForest pairUnitSystem SearchPath.empty PairUnitKey.pair = .success s :=
  runForest_eq_success_of pairUnitUnitSuccess

theorem pair_unit_unit_runForest_two_siblings :
    ∃ s : Success pairUnitSystem SearchPath.empty PairUnitKey.pair,
      runForest pairUnitSystem SearchPath.empty PairUnitKey.pair = .success s ∧
        pairUnitSystem.deps s.alt = [PairUnitKey.unit, PairUnitKey.unit] ∧
          (∀ i : Fin (pairUnitSystem.deps s.alt).length,
            ∃ s' : Success pairUnitSystem
                (SearchPath.empty.push PairUnitKey.pair s.hnotin)
                ((pairUnitSystem.deps s.alt).get ⟨i.val, i.isLt⟩),
              s.children i = s') := by
  obtain ⟨s, hs⟩ := pair_unit_unit_runForest_succeeds
  refine ⟨s, hs, ?_, fun i => Success.children_are_success s i⟩
  cases s with
  | intro _h a _ch =>
      cases a with
      | pairUU => rfl

/-! #### 2. Loop-key: loop alt blocks path-locally; leaf still succeeds -/

theorem loop_leaf_runForest_succeeds :
    ∃ s : Success loopSystem SearchPath.empty LoopKey.root,
      runForest loopSystem SearchPath.empty LoopKey.root = .success s :=
  runForest_eq_success_of
    (.intro (empty_path_not_mem LoopKey.root) LoopAlt.leaf fun j => nomatch j)

theorem loop_alt_blocked_after_push :
    let path := SearchPath.empty.push LoopKey.root (empty_path_not_mem LoopKey.root)
    LoopKey.root ∈ path.keys ∧
      runForest loopSystem path LoopKey.root =
        Outcome.loop (sys := loopSystem) (List.mem_cons_self) :=
  ⟨List.mem_cons_self,
    runForest_loop_of_mem (sys := loopSystem) (List.mem_cons_self)⟩

theorem loop_system_nonempty_deriv :
    Nonempty (AbstractDeriv loopSystem LoopKey.root) :=
  ⟨loopLeaf⟩

theorem loop_system_empty_iff :
    Nonempty (AbstractDeriv loopSystem LoopKey.root) ↔
      ∃ s, runForest loopSystem SearchPath.empty LoopKey.root = .success s :=
  nonempty_iff_runForest_empty_success (sys := loopSystem)

/-! #### 3. Failed earlier alt does not prevent later success -/

inductive OrderKey where
  | leaf
  | root
  deriving DecidableEq

instance : Fintype OrderKey where
  elems := {OrderKey.leaf, OrderKey.root}
  complete := by intro x; cases x <;> simp

inductive OrderAlt : OrderKey → Type where
  | leaf : OrderAlt .leaf
  | bad : OrderAlt .root
  | good : OrderAlt .root
  deriving DecidableEq

instance : Fintype (OrderAlt .leaf) where
  elems := {OrderAlt.leaf}
  complete := by intro a; cases a; simp

/-- Enumerate `bad` before `good` so the failing alt is tried first when possible. -/
instance : Fintype (OrderAlt .root) where
  elems := {OrderAlt.bad, OrderAlt.good}
  complete := by intro a; cases a <;> simp

def orderSystem : AlternativeSystem OrderKey where
  Alt := OrderAlt
  instDecidableEq := fun k => by cases k <;> infer_instance
  instFintype := fun k => by cases k <;> infer_instance
  deps := fun {k} a =>
    match k, a with
    | .leaf, .leaf => []
    | .root, .bad => [OrderKey.root]
    | .root, .good => [OrderKey.leaf]

private def orderLeafSuccess (path : SearchPath OrderKey)
    (h : OrderKey.leaf ∉ path.keys) :
    Success orderSystem path OrderKey.leaf :=
  .intro h OrderAlt.leaf fun j => nomatch j

private def orderGoodSuccess :
    Success orderSystem SearchPath.empty OrderKey.root :=
  .intro (empty_path_not_mem OrderKey.root) OrderAlt.good fun i =>
    match i with
    | ⟨0, _⟩ =>
        orderLeafSuccess _
          (by simp [SearchPath.push, SearchPath.empty])
    | ⟨n + 1, hn⟩ =>
        False.elim (Nat.not_lt_zero n (by
          change n + 1 < 1 at hn
          omega))

theorem order_bad_then_good_runForest_succeeds :
    ∃ s : Success orderSystem SearchPath.empty OrderKey.root,
      runForest orderSystem SearchPath.empty OrderKey.root = .success s :=
  runForest_eq_success_of orderGoodSuccess

private theorem order_not_leaf_after_root :
    OrderKey.leaf ∉
      (SearchPath.empty.push OrderKey.root (empty_path_not_mem OrderKey.root)).keys := by
  intro h
  simp [SearchPath.push, SearchPath.empty] at h

/-- Bad alt is blocked path-locally (self-loop under push). -/
theorem order_bad_child_loops :
    let path := SearchPath.empty.push OrderKey.root (empty_path_not_mem OrderKey.root)
    orderSystem.deps (k := .root) OrderAlt.bad = [OrderKey.root] ∧
      runForest orderSystem path OrderKey.root = Outcome.loop List.mem_cons_self :=
  ⟨rfl, runForest_loop_of_mem (sys := orderSystem) List.mem_cons_self⟩

/-- Good alt has a leaf dependency that succeeds under the extended path. -/
theorem order_good_child_succeeds :
    let path := SearchPath.empty.push OrderKey.root (empty_path_not_mem OrderKey.root)
    orderSystem.deps (k := .root) OrderAlt.good = [OrderKey.leaf] ∧
      ∃ s : Success orderSystem path OrderKey.leaf,
        runForest orderSystem path OrderKey.leaf = .success s :=
  ⟨rfl, runForest_eq_success_of (orderLeafSuccess _ order_not_leaf_after_root)⟩

/--
Failed earlier alt does not prevent later success: the system has a looping `bad`
alt and a succeeding `good` alt; empty-path search still succeeds, while the
self-loop under push is a path-local loop (not empty-path failure).
-/
theorem order_failed_earlier_does_not_block_later :
    orderSystem.deps (k := .root) OrderAlt.bad = [OrderKey.root] ∧
      orderSystem.deps (k := .root) OrderAlt.good = [OrderKey.leaf] ∧
        (∃ s, runForest orderSystem SearchPath.empty OrderKey.root = .success s) ∧
          runForest orderSystem
              (SearchPath.empty.push OrderKey.root (empty_path_not_mem OrderKey.root))
              OrderKey.root =
            Outcome.loop List.mem_cons_self :=
  ⟨rfl, rfl, order_bad_then_good_runForest_succeeds,
    runForest_loop_of_mem (sys := orderSystem) List.mem_cons_self⟩

/--
Explicit enumeration order `[bad, good]`: because a Success certificate for the
`good` alt exists under the empty path, the ordered search cannot return a
total blocked family (Success and Blocked are incompatible on each dependency).
-/
theorem order_explicit_bad_then_good_search :
    ∃ s : Success orderSystem SearchPath.empty OrderKey.root,
      RunForest.searchAlts
          (sys := orderSystem) (empty_path_not_mem OrderKey.root)
          (fun k' =>
            runForest orderSystem
              (SearchPath.empty.push OrderKey.root (empty_path_not_mem OrderKey.root))
              k')
          [OrderAlt.bad, OrderAlt.good] =
        Sum.inl s := by
  let path := SearchPath.empty.push OrderKey.root (empty_path_not_mem OrderKey.root)
  have hleafS := orderLeafSuccess path order_not_leaf_after_root
  obtain ⟨sLeaf, _⟩ := runForest_eq_success_of (sys := orderSystem) hleafS
  let sGood : Success orderSystem SearchPath.empty OrderKey.root :=
    .intro (empty_path_not_mem OrderKey.root) OrderAlt.good fun i =>
      match i with
      | ⟨0, _⟩ => sLeaf
      | ⟨n + 1, hn⟩ =>
          False.elim (Nat.not_lt_zero n (by change n + 1 < 1 at hn; omega))
  match h : RunForest.searchAlts
      (sys := orderSystem) (empty_path_not_mem OrderKey.root)
      (fun k' => runForest orderSystem path k')
      [OrderAlt.bad, OrderAlt.good] with
  | .inl s => exact ⟨s, rfl⟩
  | .inr blocked =>
      obtain ⟨i, b⟩ := blocked OrderAlt.good
        (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
      -- `good` has a single leaf dependency; Success at that leaf contradicts Blocked.
      have sch : Success orderSystem path
          ((orderSystem.deps (k := .root) OrderAlt.good).get ⟨i.val, i.isLt⟩) :=
        sGood.children ⟨i.val, i.isLt⟩
      exact (success_not_blocked sch b).elim

/-! #### 4. System with no successful alt → empty-path failure -/

inductive FailKey where
  | only
  deriving DecidableEq

instance : Fintype FailKey where
  elems := {FailKey.only}
  complete := by intro x; cases x; simp

inductive FailAlt : FailKey → Type where
  | loopSelf : FailAlt .only
  deriving DecidableEq

instance : Fintype (FailAlt .only) where
  elems := {FailAlt.loopSelf}
  complete := by intro a; cases a; simp

def failSystem : AlternativeSystem FailKey where
  Alt := FailAlt
  instDecidableEq := fun k => by cases k; infer_instance
  instFintype := fun k => by cases k; infer_instance
  deps := fun {k} a =>
    match k, a with
    | .only, .loopSelf => [FailKey.only]

theorem fail_system_runForest_empty_failure :
    ∃ f : Failure failSystem SearchPath.empty FailKey.only,
      runForest failSystem SearchPath.empty FailKey.only = .failure f := by
  match h : runForest failSystem SearchPath.empty FailKey.only with
  | .success s =>
      cases s with
      | intro hnotin a ch =>
          cases a
          have hchild := ch ⟨0, by decide⟩
          have hin :
              FailKey.only ∈
                (SearchPath.empty.push FailKey.only hnotin).keys := by
            simp [SearchPath.push, SearchPath.empty]
          exact (hchild.hnotin hin).elim
  | .failure f => exact ⟨f, rfl⟩
  | .loop hin =>
      simp [SearchPath.empty] at hin

theorem fail_system_no_abstractDeriv :
    ¬ Nonempty (AbstractDeriv failSystem FailKey.only) := by
  obtain ⟨f, hf⟩ := fail_system_runForest_empty_failure
  exact runForest_empty_failure_no_abstractDeriv f hf

/-! #### 5. No global sibling-visited (pair unit unit) -/

theorem pair_no_global_sibling_visited :
    (pairUnitSystem.deps (k := .pair) PairUnitAlt.pairUU =
      [PairUnitKey.unit, PairUnitKey.unit]) ∧
      (∃ s', runForest pairUnitSystem SearchPath.empty PairUnitKey.pair =
        Outcome.success s') ∧
      (∀ (_i _j : Fin 2),
        SearchPath.empty.push PairUnitKey.pair (empty_path_not_mem PairUnitKey.pair) =
          SearchPath.empty.push PairUnitKey.pair (empty_path_not_mem PairUnitKey.pair)) :=
  ⟨rfl, pair_unit_unit_runForest_succeeds, fun _ _ => rfl⟩

theorem loop_ne_failure_fixture :
    let path :=
      SearchPath.empty.push PairUnitKey.unit (empty_path_not_mem PairUnitKey.unit)
    PairUnitKey.unit ∈ path.keys ∧
      PairUnitKey.unit ∉ (SearchPath.empty : SearchPath PairUnitKey).keys ∧
      runForest pairUnitSystem path PairUnitKey.unit =
        Outcome.loop (List.mem_cons_self) :=
  ⟨List.mem_cons_self,
    empty_path_not_mem _,
    runForest_loop_of_mem (sys := pairUnitSystem) (List.mem_cons_self)⟩

open SearchKeyFixtures

theorem policy_embed_deps_fixture (π : SatPolicy Uz O1 1 1)
    (k : SearchKey Uz O1 1 1) (h : ¬ isSaturated k)
    (a : StructuralAlternative k) :
    AllAlt.deps (PolicyAlt.toAllAlt (.structural (π := π) h a)) =
      PolicyAlt.deps (.structural (π := π) h a) :=
  PolicyAlt.policy_embed_deps _

end SearchForestRunFixtures

end Gimbal.Equality.Scherer
