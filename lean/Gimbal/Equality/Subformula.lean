/-
  Finite subformula universe for reachability (Milestone 8D).

  The closure is structural: no fuel and no fixpoint loop. `subformulaPre`
  lists the subformulas of one object in pre-order; the closure flattens the
  roots and keeps first occurrences. That is exactly the sequence the previous
  depth-first worklist emitted, so subformula-table indices are unchanged.
-/

import Gimbal.Object

namespace Gimbal
namespace Equality

variable {n : Nat}

/-- Immediate subformulas of an object. -/
def subformulaStep : Object n → List (Object n)
  | .base _ | .unit | .never => []
  | .prod A B | .coprod A B | .exp A B => [A, B]

/-- Every subformula of `A`: root first, left subtree before right. -/
def subformulaPre : Object n → List (Object n)
  | .base q => [.base q]
  | .unit => [(.unit : Object n)]
  | .never => [(.never : Object n)]
  | .prod A B => .prod A B :: (subformulaPre A ++ subformulaPre B)
  | .coprod A B => .coprod A B :: (subformulaPre A ++ subformulaPre B)
  | .exp A B => .exp A B :: (subformulaPre A ++ subformulaPre B)

@[simp] theorem mem_subformulaPre_self (A : Object n) : A ∈ subformulaPre A := by
  cases A <;> simp [subformulaPre]

theorem subformulaPre_ne_nil (A : Object n) : subformulaPre A ≠ [] := by
  cases A <;> simp [subformulaPre]

/-- Subformulas of an immediate subformula are subformulas. -/
theorem subformulaPre_subset_of_step {A B : Object n} (h : B ∈ subformulaStep A) :
    subformulaPre B ⊆ subformulaPre A := by
  intro C hC
  cases A with
  | base q => simp [subformulaStep] at h
  | unit => simp [subformulaStep] at h
  | never => simp [subformulaStep] at h
  | prod A₁ A₂ =>
      simp only [subformulaStep, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp [subformulaPre, hC]
  | coprod A₁ A₂ =>
      simp only [subformulaStep, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp [subformulaPre, hC]
  | exp A₁ A₂ =>
      simp only [subformulaStep, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp [subformulaPre, hC]

/-- `subformulaPre` is transitively closed under `subformulaStep`. -/
theorem mem_subformulaPre_of_step {A B C : Object n}
    (hB : B ∈ subformulaPre A) (hC : C ∈ subformulaStep B) :
    C ∈ subformulaPre A := by
  induction A with
  | base q => simp [subformulaPre] at hB; subst hB; simp [subformulaStep] at hC
  | unit => simp [subformulaPre] at hB; subst hB; simp [subformulaStep] at hC
  | never => simp [subformulaPre] at hB; subst hB; simp [subformulaStep] at hC
  | prod A₁ A₂ ih₁ ih₂ =>
      simp only [subformulaPre, List.mem_cons, List.mem_append] at hB
      rcases hB with rfl | hB | hB
      · exact subformulaPre_subset_of_step hC (mem_subformulaPre_self _)
      · simp [subformulaPre, ih₁ hB]
      · simp [subformulaPre, ih₂ hB]
  | coprod A₁ A₂ ih₁ ih₂ =>
      simp only [subformulaPre, List.mem_cons, List.mem_append] at hB
      rcases hB with rfl | hB | hB
      · exact subformulaPre_subset_of_step hC (mem_subformulaPre_self _)
      · simp [subformulaPre, ih₁ hB]
      · simp [subformulaPre, ih₂ hB]
  | exp A₁ A₂ ih₁ ih₂ =>
      simp only [subformulaPre, List.mem_cons, List.mem_append] at hB
      rcases hB with rfl | hB | hB
      · exact subformulaPre_subset_of_step hC (mem_subformulaPre_self _)
      · simp [subformulaPre, ih₁ hB]
      · simp [subformulaPre, ih₂ hB]

/-! ### First-occurrence deduplication -/

/-- Drop every element already present in `seen` or earlier in the list. -/
def dedupFirst : List (Object n) → List (Object n) → List (Object n)
  | _, [] => []
  | seen, a :: rest =>
      if a ∈ seen then dedupFirst seen rest else a :: dedupFirst (a :: seen) rest

@[simp] theorem mem_dedupFirst {x : Object n} :
    ∀ (seen l : List (Object n)),
      x ∈ dedupFirst seen l ↔ x ∈ l ∧ x ∉ seen
  | _, [] => by simp [dedupFirst]
  | seen, a :: rest => by
      by_cases h : a ∈ seen
      · simp only [dedupFirst, if_pos h, mem_dedupFirst seen rest, List.mem_cons]
        constructor
        · rintro ⟨hx, hs⟩; exact ⟨Or.inr hx, hs⟩
        · rintro ⟨hx | hx, hs⟩
          · exact absurd (hx ▸ h) hs
          · exact ⟨hx, hs⟩
      · simp only [dedupFirst, if_neg h, List.mem_cons,
          mem_dedupFirst (a :: seen) rest]
        constructor
        · rintro (rfl | ⟨hx, hs⟩)
          · exact ⟨Or.inl rfl, h⟩
          · exact ⟨Or.inr hx, fun hc => hs (Or.inr hc)⟩
        · rintro ⟨hx | hx, hs⟩
          · exact Or.inl hx
          · by_cases hax : x = a
            · exact Or.inl hax
            · exact Or.inr ⟨hx, by simp [hax, hs]⟩

theorem nodup_dedupFirst :
    ∀ (seen l : List (Object n)), (dedupFirst seen l).Nodup
  | _, [] => by simp [dedupFirst]
  | seen, a :: rest => by
      by_cases h : a ∈ seen
      · simpa [dedupFirst, if_pos h] using nodup_dedupFirst seen rest
      · simp only [dedupFirst, if_neg h, List.nodup_cons]
        exact ⟨by simp, nodup_dedupFirst (a :: seen) rest⟩

theorem length_dedupFirst_le :
    ∀ (seen l : List (Object n)), (dedupFirst seen l).length ≤ l.length
  | _, [] => by simp [dedupFirst]
  | seen, a :: rest => by
      by_cases h : a ∈ seen
      · simpa [dedupFirst, if_pos h] using
          Nat.le_succ_of_le (length_dedupFirst_le seen rest)
      · simpa [dedupFirst, if_neg h] using length_dedupFirst_le (a :: seen) rest

/-! ### The closure -/

/-- Subformula universe of a list of roots, deduplicated in first-seen order. -/
def subformulaClosureList (roots : List (Object n)) : List (Object n) :=
  dedupFirst [] (roots.flatMap subformulaPre)

/-- Array view of the subformula universe (the reachability type table). -/
def subformulaClosure (roots : List (Object n)) : Array (Object n) :=
  (subformulaClosureList roots).toArray

@[simp] theorem mem_subformulaClosureList {roots : List (Object n)} {A : Object n} :
    A ∈ subformulaClosureList roots ↔ ∃ r ∈ roots, A ∈ subformulaPre r := by
  simp [subformulaClosureList, List.mem_flatMap]

@[simp] theorem mem_subformulaClosure {roots : List (Object n)} {A : Object n} :
    A ∈ subformulaClosure roots ↔ ∃ r ∈ roots, A ∈ subformulaPre r := by
  simp [subformulaClosure]

/-- Every root is in its own closure. -/
theorem mem_subformulaClosure_of_mem_roots {roots : List (Object n)} {A : Object n}
    (h : A ∈ roots) : A ∈ subformulaClosure roots :=
  mem_subformulaClosure.mpr ⟨A, h, mem_subformulaPre_self A⟩

/--
Closure completeness: any immediate subformula of a member is a member.
This is what makes every type the worklist rules query present in the table.
-/
theorem mem_subformulaClosure_of_step {roots : List (Object n)} {A B : Object n}
    (hA : A ∈ subformulaClosure roots) (hB : B ∈ subformulaStep A) :
    B ∈ subformulaClosure roots := by
  obtain ⟨r, hr, hAr⟩ := mem_subformulaClosure.mp hA
  exact mem_subformulaClosure.mpr ⟨r, hr, mem_subformulaPre_of_step hAr hB⟩

theorem subformulaClosureList_nodup (roots : List (Object n)) :
    (subformulaClosureList roots).Nodup :=
  nodup_dedupFirst _ _

/-- Finiteness with an explicit bound: the table never exceeds the flattened roots. -/
theorem subformulaClosure_size_le (roots : List (Object n)) :
    (subformulaClosure roots).size ≤ (roots.flatMap subformulaPre).length := by
  simpa [subformulaClosure, subformulaClosureList] using
    length_dedupFirst_le ([] : List (Object n)) (roots.flatMap subformulaPre)

/-! ### Table lookup -/

/-- Index lookup in a `DecidableEq` table by `BEq`-search. -/
theorem findIdx?_isSome_of_mem {A : Object n} {types : Array (Object n)}
    (h : A ∈ types) : (types.findIdx? (· == A)).isSome := by
  cases hfind : types.findIdx? (· == A) with
  | some _ => rfl
  | none =>
      have := Array.findIdx?_eq_none_iff.mp hfind A h
      simp at this

/-- The index returned by a table search really holds the searched object. -/
theorem getElem?_of_findIdx? {A : Object n} {types : Array (Object n)} {i : Nat}
    (h : types.findIdx? (· == A) = some i) : types[i]? = some A := by
  obtain ⟨hlt, hsat, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  have hAi : types[i] = A := by simpa using hsat
  simp [Array.getElem?_eq_getElem hlt, hAi]

end Equality
end Gimbal
