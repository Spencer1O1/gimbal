/-
  Constructive canonical enumerations and their basic combinators.

  This is a leaf utility module: it contains no search-system definitions.
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup

namespace Gimbal.Equality.Scherer

/-- An explicit duplicate-free list containing every value of `α`. -/
structure CanonicalEnum (α : Type) where
  elems : List α
  nodup : elems.Nodup
  complete : ∀ x : α, x ∈ elems

namespace CanonicalEnum

variable {α β : Type}

/-- Constructive `Fintype` data derived from the explicit list. -/
@[reducible] def toFintype [DecidableEq α] (e : CanonicalEnum α) : Fintype α where
  elems := e.elems.toFinset
  complete x := List.mem_toFinset.mpr (e.complete x)

@[simp] theorem card_toFintype [DecidableEq α] (e : CanonicalEnum α) :
    @Fintype.card α e.toFintype = e.elems.length := by
  change e.elems.toFinset.card = e.elems.length
  exact List.toFinset_card_of_nodup e.nodup

/-- Constructively enumerate a product from two explicit enumerations. -/
def prod [DecidableEq α] [DecidableEq β]
    (ea : CanonicalEnum α) (eb : CanonicalEnum β) :
    CanonicalEnum (α × β) where
  elems := ea.elems.product eb.elems
  nodup := ea.nodup.product eb.nodup
  complete x := by
    exact List.mem_product.mpr ⟨ea.complete x.1, eb.complete x.2⟩

@[simp] theorem prod_length [DecidableEq α] [DecidableEq β]
    (ea : CanonicalEnum α) (eb : CanonicalEnum β) :
    (prod ea eb).elems.length = ea.elems.length * eb.elems.length := by
  exact List.length_product ea.elems eb.elems

/-- Runtime powerset enumeration, retaining the source-list order. -/
def finsetsList [DecidableEq α] : List α → List (Finset α)
  | [] => [∅]
  | a :: rest =>
      let tail := finsetsList rest
      tail ++ tail.map (insert a)

theorem mem_finsetsList_iff [DecidableEq α] (s : Finset α) :
    ∀ xs : List α, s ∈ finsetsList xs ↔ s ⊆ xs.toFinset
  | [] => by simp [finsetsList]
  | a :: rest => by
      rw [show (a :: rest).toFinset = insert a rest.toFinset by simp]
      constructor
      · intro hs
        rcases List.mem_append.mp hs with hs | hs
        · exact Finset.Subset.trans ((mem_finsetsList_iff s rest).mp hs)
            (Finset.subset_insert _ _)
        · rcases List.mem_map.mp hs with ⟨t, ht, rfl⟩
          exact Finset.insert_subset_insert a ((mem_finsetsList_iff t rest).mp ht)
      · intro hs
        by_cases ha : a ∈ s
        · apply List.mem_append.mpr
          right
          apply List.mem_map.mpr
          refine ⟨s.erase a, ?_, Finset.insert_erase ha⟩
          apply (mem_finsetsList_iff (s.erase a) rest).mpr
          exact Finset.subset_insert_iff.mp hs
        · apply List.mem_append.mpr
          left
          apply (mem_finsetsList_iff s rest).mpr
          rw [← Finset.erase_eq_self.mpr ha]
          exact Finset.subset_insert_iff.mp hs

theorem nodup_finsetsList [DecidableEq α] {xs : List α} (hxs : xs.Nodup) :
    (finsetsList xs).Nodup := by
  induction xs with
  | nil => simp [finsetsList]
  | cons a rest ih =>
      have ha : a ∉ rest := (List.nodup_cons.mp hxs).1
      have hrest : rest.Nodup := (List.nodup_cons.mp hxs).2
      have iht := ih hrest
      rw [finsetsList, List.nodup_append]
      refine ⟨iht, ?_, ?_⟩
      · apply iht.map_on
        intro s hs t ht heq
        have has : a ∉ s := by
          intro hmem
          have hsub := (mem_finsetsList_iff s rest).mp hs hmem
          exact ha (List.mem_toFinset.mp hsub)
        have hat : a ∉ t := by
          intro hmem
          have hsub := (mem_finsetsList_iff t rest).mp ht hmem
          exact ha (List.mem_toFinset.mp hsub)
        have := congrArg (fun u : Finset α => u.erase a) heq
        simpa [has, hat] using this
      · intro s hs t ht hEq
        rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
        have has : a ∉ s := by
          intro hmem
          have hsub := (mem_finsetsList_iff s rest).mp hs hmem
          exact ha (List.mem_toFinset.mp hsub)
        apply has
        rw [hEq]
        exact Finset.mem_insert_self a u

/-- Constructively enumerate every finite subset of an explicit carrier. -/
def finsets [DecidableEq α] (e : CanonicalEnum α) :
    CanonicalEnum (Finset α) where
  elems := finsetsList e.elems
  nodup := nodup_finsetsList e.nodup
  complete s := by
    apply (mem_finsetsList_iff s e.elems).mpr
    intro x _hx
    exact List.mem_toFinset.mpr (e.complete x)

@[simp] theorem finsets_length [DecidableEq α] (e : CanonicalEnum α) :
    (finsets e).elems.length = 2 ^ e.elems.length := by
  change (finsetsList e.elems).length = 2 ^ e.elems.length
  induction e.elems with
  | nil => rfl
  | cons a rest ih =>
      simp only [finsetsList, List.length_append, List.length_map,
        List.length_cons, ih, pow_succ]
      omega

/-- Transport an explicit enumeration across an equivalence. -/
def mapEquiv [DecidableEq α] [DecidableEq β]
    (e : CanonicalEnum α) (f : α ≃ β) : CanonicalEnum β where
  elems := e.elems.map f
  nodup := e.nodup.map f.injective
  complete y := by
    apply List.mem_map.mpr
    exact ⟨f.symm y, e.complete (f.symm y), f.apply_symm_apply y⟩

@[simp] theorem mapEquiv_length [DecidableEq α] [DecidableEq β]
    (e : CanonicalEnum α) (f : α ≃ β) :
    (mapEquiv e f).elems.length = e.elems.length := by
  simp [mapEquiv]

/-- A duplicate-free list of values cannot exceed a complete enumeration. -/
theorem nodup_length_le (e : CanonicalEnum α) {xs : List α}
    (hxs : xs.Nodup) : xs.length ≤ e.elems.length := by
  classical
  have hsub : xs.toFinset ⊆ e.elems.toFinset := by
    intro x _hx
    exact List.mem_toFinset.mpr (e.complete x)
  have hcard := Finset.card_le_card hsub
  simpa [List.toFinset_card_of_nodup hxs,
    List.toFinset_card_of_nodup e.nodup] using hcard

end CanonicalEnum

end Gimbal.Equality.Scherer
