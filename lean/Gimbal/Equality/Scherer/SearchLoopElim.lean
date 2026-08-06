/-
  Scherer-core generic branch-simple derivation normalization.

  Size-minimal abstract derivations are branch-simple: no key repeats along any
  root-to-leaf branch. Sibling duplicate keys remain legal. No executable
  normalizer, global visited set, sat-policy certification, or S4.
-/

import Mathlib.Data.List.Nodup
import Gimbal.Equality.Scherer.SearchForestCore

namespace Gimbal.Equality.Scherer

variable {K : Type} {sys : AlternativeSystem K}

/-! ### Occurrence-indexed size -/

namespace AbstractDeriv

/-- Sum of a `Fin n`-indexed family of naturals. -/
def sumFin : ∀ {n : Nat}, (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 + sumFin fun i : Fin n => f i.succ

/-- Occurrence-indexed derivation size: `1 +` sum of child sizes. -/
def size {k : K} : AbstractDeriv sys k → Nat
  | AbstractDeriv.choose _a children =>
      1 + sumFin fun i => size (children i)

@[simp] theorem size_choose {k : K} (a : sys.Alt k)
    (children : ∀ i : Fin (sys.deps a).length,
      AbstractDeriv sys ((sys.deps a).get ⟨i.val, i.isLt⟩)) :
    size (AbstractDeriv.choose a children) =
      1 + sumFin fun i => size (children i) :=
  rfl

@[simp] theorem sumFin_zero (f : Fin 0 → Nat) : sumFin f = 0 := rfl

@[simp] theorem sumFin_succ {n : Nat} (f : Fin (n + 1) → Nat) :
    sumFin f = f 0 + sumFin fun i : Fin n => f i.succ :=
  rfl

theorem sumFin_le {n : Nat} {f g : Fin n → Nat}
    (hle : ∀ i, f i ≤ g i) : sumFin f ≤ sumFin g := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [sumFin_succ]
      exact Nat.add_le_add (hle 0) (ih fun i => hle i.succ)

theorem sumFin_lt_of_lt {n : Nat} {f g : Fin n → Nat} (i : Fin n)
    (hle : ∀ j, f j ≤ g j) (hlt : f i < g i) :
    sumFin f < sumFin g := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      simp only [sumFin_succ]
      cases i using Fin.cases with
      | zero =>
          have hrest :
              sumFin (fun j : Fin n => f j.succ) ≤
                sumFin (fun j : Fin n => g j.succ) :=
            sumFin_le fun j => hle j.succ
          exact Nat.add_lt_add_of_lt_of_le hlt hrest
      | succ i =>
          have h0 : f 0 ≤ g 0 := hle 0
          have hrest :
              sumFin (fun j : Fin n => f j.succ) <
                sumFin (fun j : Fin n => g j.succ) :=
            ih i (fun j => hle j.succ) hlt
          exact Nat.add_lt_add_of_le_of_lt h0 hrest

theorem sumFin_term_le {n : Nat} (f : Fin n → Nat) (i : Fin n) :
    f i ≤ sumFin f := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          simp only [sumFin_succ]
          exact Nat.le_add_right _ _
      | succ i =>
          simp only [sumFin_succ]
          exact Nat.le_trans (ih (fun j => f j.succ) i) (Nat.le_add_left _ _)

theorem size_pos {k : K} (d : AbstractDeriv sys k) : 0 < d.size := by
  cases d with
  | choose _a _children =>
      simp only [size_choose]
      omega

theorem size_eq_cast {k k' : K} (h : k = k') (d : AbstractDeriv sys k) :
    size (h ▸ d) = size d := by
  cases h; rfl

/-! ### Child replacement (same parent key / alternative) -/

/-- Replace one dependency-occurrence child, keeping the parent alternative. -/
def replaceChild {k : K} {a : sys.Alt k}
    (children : ∀ i : Fin (sys.deps a).length,
      AbstractDeriv sys ((sys.deps a).get ⟨i.val, i.isLt⟩))
    (i : Fin (sys.deps a).length)
    (d' : AbstractDeriv sys ((sys.deps a).get ⟨i.val, i.isLt⟩)) :
    AbstractDeriv sys k :=
  AbstractDeriv.choose a fun j => if h : j = i then h ▸ d' else children j

theorem replaceChild_size_lt {k : K} {a : sys.Alt k}
    (children : ∀ i : Fin (sys.deps a).length,
      AbstractDeriv sys ((sys.deps a).get ⟨i.val, i.isLt⟩))
    (i : Fin (sys.deps a).length)
    (d' : AbstractDeriv sys ((sys.deps a).get ⟨i.val, i.isLt⟩))
    (hlt : d'.size < (children i).size) :
    (replaceChild children i d').size <
      (AbstractDeriv.choose a children).size := by
  simp only [replaceChild, size_choose]
  refine Nat.add_lt_add_left ?_ 1
  refine sumFin_lt_of_lt i ?_ ?_
  · intro j
    by_cases h : j = i
    · subst h; simpa using hlt.le
    · simp [h]
  · simpa using hlt

/-! ### Proper subderivations -/

/--
Proper (strict) subderivation relation. Occurrences are distinguished by
dependency indices, so sibling duplicate keys remain distinct premises.
-/
inductive ProperSubderiv :
    ∀ {k k' : K}, AbstractDeriv sys k' → AbstractDeriv sys k → Prop
  | imm {k : K} {a : sys.Alt k}
      {children : ∀ i : Fin (sys.deps a).length,
        AbstractDeriv sys ((sys.deps a).get ⟨i.val, i.isLt⟩)}
      (i : Fin (sys.deps a).length) :
      ProperSubderiv (children i) (AbstractDeriv.choose a children)
  | step {k : K} {a : sys.Alt k}
      {children : ∀ i : Fin (sys.deps a).length,
        AbstractDeriv sys ((sys.deps a).get ⟨i.val, i.isLt⟩)}
      {k' : K} {d' : AbstractDeriv sys k'}
      (i : Fin (sys.deps a).length)
      (h : ProperSubderiv d' (children i)) :
      ProperSubderiv d' (AbstractDeriv.choose a children)

theorem size_child_lt {k : K} {a : sys.Alt k}
    (children : ∀ i : Fin (sys.deps a).length,
      AbstractDeriv sys ((sys.deps a).get ⟨i.val, i.isLt⟩))
    (i : Fin (sys.deps a).length) :
    (children i).size < (AbstractDeriv.choose a children).size := by
  simp only [size_choose]
  have := sumFin_term_le (fun j => size (children j)) i
  omega

theorem properSubderiv_size_lt {k k' : K}
    {d' : AbstractDeriv sys k'} {d : AbstractDeriv sys k}
    (h : ProperSubderiv d' d) : d'.size < d.size := by
  induction h with
  | imm i => exact size_child_lt _ i
  | step i _ ih => exact Nat.lt_trans ih (size_child_lt _ i)

/-! ### Size minimality -/

/-- Minimal size among all abstract derivations of the same root key. -/
def IsSizeMinimal {k : K} (d : AbstractDeriv sys k) : Prop :=
  ∀ d' : AbstractDeriv sys k, d.size ≤ d'.size

theorem exists_sizeMinimal {k : K} (hne : Nonempty (AbstractDeriv sys k)) :
    ∃ d : AbstractDeriv sys k, IsSizeMinimal d := by
  classical
  obtain ⟨d0⟩ := hne
  let P : Nat → Prop := fun n => ∃ d : AbstractDeriv sys k, d.size = n
  have hP : ∃ n, P n := ⟨d0.size, d0, rfl⟩
  obtain ⟨d, hd⟩ := Nat.find_spec hP
  refine ⟨d, fun d' => ?_⟩
  have hle : Nat.find hP ≤ d'.size := Nat.find_min' hP ⟨d', rfl⟩
  exact hd ▸ hle

theorem child_sizeMinimal {k : K} {a : sys.Alt k}
    (children : ∀ i : Fin (sys.deps a).length,
      AbstractDeriv sys ((sys.deps a).get ⟨i.val, i.isLt⟩))
    (hmin : IsSizeMinimal (AbstractDeriv.choose a children))
    (i : Fin (sys.deps a).length) :
    IsSizeMinimal (children i) := by
  intro c'
  refine le_of_not_gt fun hlt => ?_
  have hpar := hmin (replaceChild children i c')
  have := replaceChild_size_lt children i c' hlt
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hpar this)

/--
A proper descendant with the same key as an ancestor yields a strictly smaller
derivation of that ancestor key.
-/
theorem same_key_proper_descendant_smaller {k : K}
    {d d' : AbstractDeriv sys k} (h : ProperSubderiv d' d) :
    d'.size < d.size :=
  properSubderiv_size_lt h

theorem sizeMinimal_no_same_key_proper {k : K} {d : AbstractDeriv sys k}
    (hmin : IsSizeMinimal d) {d' : AbstractDeriv sys k}
    (h : ProperSubderiv d' d) : False :=
  Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (hmin d') (properSubderiv_size_lt h))

theorem sizeMinimal_no_proper_key {k k' : K} {d : AbstractDeriv sys k}
    (hmin : IsSizeMinimal d) {d' : AbstractDeriv sys k'}
    (h : ProperSubderiv d' d) (hk : k' = k) : False := by
  cases hk
  exact sizeMinimal_no_same_key_proper hmin h

/-! ### Branch keys / branch-simplicity -/

/--
Path-local branch discipline: the current key is not among the ancestor keys
`forbidden`, and every occurrence-child is branch-simple under the extended
ancestor list. Sibling duplicate keys are legal (each child is checked on its
own root-to-leaf branches).
-/
inductive Avoiding : ∀ {k : K}, List K → AbstractDeriv sys k → Prop
  | mk {k : K} {a : sys.Alt k}
      {children : ∀ i : Fin (sys.deps a).length,
        AbstractDeriv sys ((sys.deps a).get ⟨i.val, i.isLt⟩)}
      {forbidden : List K}
      (hroot : k ∉ forbidden)
      (hchildren : ∀ i, Avoiding (k :: forbidden) (children i)) :
      Avoiding forbidden (AbstractDeriv.choose a children)

/-- No key repeats along any root-to-leaf branch. -/
def BranchSimple {k : K} (d : AbstractDeriv sys k) : Prop :=
  Avoiding ([] : List K) d

theorem sizeMinimal_avoiding {k : K} (d : AbstractDeriv sys k)
    (hmin : IsSizeMinimal d) (forbidden : List K)
    (hroot : k ∉ forbidden)
    (hforbid : ∀ x ∈ forbidden, ∀ {dx : AbstractDeriv sys x},
      ProperSubderiv dx d → False) :
    Avoiding forbidden d := by
  induction hn : d.size using Nat.strong_induction_on generalizing k d forbidden with
  | h n ih =>
      subst hn
      cases d with
      | choose a children =>
          refine Avoiding.mk hroot ?_
          intro i
          have hmin_i := child_sizeMinimal children hmin i
          have hsz : (children i).size < size (AbstractDeriv.choose a children) :=
            size_child_lt children i
          refine ih (children i).size hsz (children i) hmin_i (k :: forbidden) ?_ ?_ rfl
          · intro hin
            rcases List.mem_cons.mp hin with hk | hx
            · exact sizeMinimal_no_proper_key hmin (.imm i) hk
            · exact hforbid _ hx (.imm i)
          · intro x hx dx hprop
            rcases List.mem_cons.mp hx with hk | hxin
            · exact sizeMinimal_no_proper_key hmin (.step i hprop) hk
            · exact hforbid x hxin (.step i hprop)

theorem sizeMinimal_branchSimple {k : K} {d : AbstractDeriv sys k}
    (hmin : IsSizeMinimal d) : BranchSimple d :=
  sizeMinimal_avoiding d hmin [] (by simp) (by intro x hx; cases hx)

theorem exists_branchSimple {k : K} (hne : Nonempty (AbstractDeriv sys k)) :
    Nonempty { d : AbstractDeriv sys k // BranchSimple d } := by
  obtain ⟨d, hmin⟩ := exists_sizeMinimal hne
  exact ⟨⟨d, sizeMinimal_branchSimple hmin⟩⟩

end AbstractDeriv

/-! ### Fixtures -/

namespace SearchLoopElimFixtures

open SearchForestFixtures
open AbstractDeriv

/-- Leaf unit derivation. -/
def unitLeaf : AbstractDeriv pairUnitSystem PairUnitKey.unit :=
  AbstractDeriv.choose PairUnitAlt.leaf fun j => nomatch j

/-- Pair(unit,unit) with two identical sibling unit leaves. -/
def pairUnitUnit : AbstractDeriv pairUnitSystem PairUnitKey.pair :=
  AbstractDeriv.choose PairUnitAlt.pairUU fun i =>
    match i with
    | ⟨0, _⟩ => unitLeaf
    | ⟨1, _⟩ => unitLeaf
    | ⟨n + 2, hn⟩ =>
        False.elim (Nat.not_lt_zero n (by
          change n + 2 < 2 at hn
          omega))

theorem unit_deriv_size_eq_one (d : AbstractDeriv pairUnitSystem .unit) :
    d.size = 1 := by
  cases d with
  | choose a children =>
      cases a
      simp [size_choose, pairUnitSystem, sumFin_zero]

theorem pairUnitUnit_size : pairUnitUnit.size = 3 := by
  simp [pairUnitUnit, unitLeaf, size, sumFin, pairUnitSystem]

theorem pair_deriv_size_eq_three (d : AbstractDeriv pairUnitSystem .pair) :
    d.size = 3 := by
  cases d with
  | choose a children =>
      cases a
      have h0 := unit_deriv_size_eq_one (children ⟨0, by decide⟩)
      have h1 := unit_deriv_size_eq_one (children ⟨1, by decide⟩)
      simp only [size_choose]
      have hs :
          (children ⟨0, by decide⟩).size + (children ⟨1, by decide⟩).size = 2 :=
        congrArg₂ (· + ·) h0 h1
      have hs' :
          sumFin (fun i => size (children i)) =
            (children ⟨0, by decide⟩).size + (children ⟨1, by decide⟩).size := by
        simp only []; rfl
      calc
        1 + sumFin (fun i => size (children i))
            = 1 + ((children ⟨0, by decide⟩).size +
                (children ⟨1, by decide⟩).size) := by rw [hs']
        _ = 1 + 2 := by rw [hs]
        _ = 3 := rfl

theorem pairUnitUnit_branchSimple : BranchSimple pairUnitUnit := by
  refine Avoiding.mk (by simp) ?_
  intro i
  match i with
  | ⟨0, _⟩ =>
      exact Avoiding.mk (by simp [pairUnitSystem]) fun j => nomatch j
  | ⟨1, _⟩ =>
      exact Avoiding.mk (by simp [pairUnitSystem]) fun j => nomatch j
  | ⟨n + 2, hn⟩ =>
      exact False.elim (Nat.not_lt_zero n (by
        change n + 2 < 2 at hn
        omega))

theorem pairUnitUnit_sibling_keys_not_globally_unique :
    pairUnitSystem.deps (k := .pair) PairUnitAlt.pairUU =
      [PairUnitKey.unit, PairUnitKey.unit] ∧
      BranchSimple pairUnitUnit :=
  ⟨rfl, pairUnitUnit_branchSimple⟩

theorem pairUnitUnit_is_sizeMinimal : IsSizeMinimal pairUnitUnit := by
  intro d'
  rw [pairUnitUnit_size, pair_deriv_size_eq_three d']

theorem pairUnitUnit_minimal_branchSimple :
    IsSizeMinimal pairUnitUnit ∧ BranchSimple pairUnitUnit :=
  ⟨pairUnitUnit_is_sizeMinimal, pairUnitUnit_branchSimple⟩

/-! #### Ancestor/descendant repeated-key fixture -/

inductive LoopKey where
  | root
  deriving DecidableEq

inductive LoopAlt : LoopKey → Type where
  | leaf : LoopAlt .root
  | loop : LoopAlt .root
deriving DecidableEq

instance : Fintype (LoopAlt .root) where
  elems := {LoopAlt.leaf, LoopAlt.loop}
  complete := by intro a; cases a <;> simp

def loopSystem : AlternativeSystem LoopKey where
  Alt := LoopAlt
  instDecidableEq := fun k => by cases k; infer_instance
  instFintype := fun k => by cases k; infer_instance
  deps := fun {k} a =>
    match k, a with
    | .root, .leaf => []
    | .root, .loop => [.root]

def loopLeaf : AbstractDeriv loopSystem .root :=
  AbstractDeriv.choose LoopAlt.leaf fun j => nomatch j

/-- Non-branch-simple derivation: root loops once into a leaf of the same key. -/
def loopOnce : AbstractDeriv loopSystem .root :=
  AbstractDeriv.choose LoopAlt.loop fun i =>
    match i with
    | ⟨0, _⟩ => loopLeaf
    | ⟨n + 1, hn⟩ =>
        False.elim (Nat.not_lt_zero n (by
          change n + 1 < 1 at hn
          omega))

theorem loopLeaf_size : loopLeaf.size = 1 := by
  simp [loopLeaf, size_choose, loopSystem, sumFin_zero]

theorem loopOnce_size : loopOnce.size = 2 := by
  change 1 + sumFin (fun i : Fin 1 =>
      size (match (i : Fin 1) with
        | ⟨0, _⟩ => loopLeaf)) = 2
  simp only [sumFin_succ, sumFin_zero]
  simp [loopLeaf_size]

theorem loopOnce_has_smaller_same_root :
    ∃ d' : AbstractDeriv loopSystem .root, d'.size < loopOnce.size :=
  ⟨loopLeaf, by simp [loopLeaf_size, loopOnce_size]⟩

theorem loopOnce_proper_descendant_same_key :
    ProperSubderiv loopLeaf loopOnce ∧ loopLeaf.size < loopOnce.size := by
  refine ⟨?_, by simp [loopLeaf_size, loopOnce_size]⟩
  -- imm at occurrence 0: children 0 = loopLeaf
  have h := ProperSubderiv.imm (sys := loopSystem) (a := LoopAlt.loop)
      (children := fun i =>
        match i with
        | ⟨0, _⟩ => loopLeaf
        | ⟨n + 1, hn⟩ =>
            False.elim (Nat.not_lt_zero n (by
              change n + 1 < 1 at hn; omega)))
      ⟨0, by decide⟩
  simpa [loopOnce] using h

theorem loopLeaf_branchSimple : BranchSimple loopLeaf :=
  Avoiding.mk (by simp) fun j => nomatch j

theorem loopLeaf_sizeMinimal : IsSizeMinimal loopLeaf := by
  intro d'
  cases d' with
  | choose a children =>
      cases a with
      | leaf =>
          rw [loopLeaf_size]
          simp [size_choose, loopSystem, sumFin_zero]
      | loop =>
          rw [loopLeaf_size]
          simp only [size_choose, loopSystem, sumFin_succ, sumFin_zero]
          have := size_pos (children ⟨0, by decide⟩)
          omega

theorem loopLeaf_minimal_branchSimple :
    IsSizeMinimal loopLeaf ∧ BranchSimple loopLeaf :=
  ⟨loopLeaf_sizeMinimal, loopLeaf_branchSimple⟩

/-- Branch-simplicity does not imply global uniqueness of sibling keys. -/
theorem branchSimple_not_global_sibling_unique :
    BranchSimple pairUnitUnit ∧
      (pairUnitSystem.deps (k := .pair) PairUnitAlt.pairUU).count .unit = 2 :=
  ⟨pairUnitUnit_branchSimple, rfl⟩

end SearchLoopElimFixtures

end Gimbal.Equality.Scherer
