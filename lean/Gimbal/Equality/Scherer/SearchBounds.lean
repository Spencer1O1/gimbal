/-
  Scherer-core finite search obligations and candidate live-depth bounds.

  Defines the finite `(P,K)` obligation space, structural formula sizes, and
  arithmetic candidate bounds. Does **not** prove `liveDepth ≤ maxLive`; that
  requires checked grammar, batch progress, and exact-support strong cut later.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.OfFn
import Gimbal.Equality.Scherer.ResolvedSupport

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Finite resolved obligations -/

/-- Exact resolved search obligation: result type paired with dependency support. -/
structure Obligation (U : SearchUniverse sig) (O : Type) where
  result : UPos U
  support : DepSupport O
  deriving DecidableEq

namespace Obligation

variable {U : SearchUniverse sig} {O : Type}

theorem ext {o₁ o₂ : Obligation U O}
    (hP : o₁.result = o₂.result) (hK : o₁.support = o₂.support) : o₁ = o₂ := by
  cases o₁; cases o₂; cases hP; cases hK; rfl

/-- Canonical equivalence with the product of finite carriers. -/
def equivProd : Obligation U O ≃ UPos U × DepSupport O where
  toFun o := (o.result, o.support)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [DecidableEq O] [Fintype O] : Fintype (Obligation U O) :=
  Fintype.ofEquiv _ equivProd.symm

instance [Fintype O] : Finite (Obligation U O) := by
  letI := Fintype.ofFinite O
  letI : DecidableEq O := Classical.decEq O
  infer_instance

end Obligation

/-- Full finite obligation space (executable when `O` is finite). -/
def allObligations (U : SearchUniverse sig) (O : Type) [DecidableEq O] [Fintype O] :
    Finset (Obligation U O) :=
  Finset.univ

@[simp] theorem mem_allObligations {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] [Fintype O] (o : Obligation U O) :
    o ∈ allObligations U O :=
  Finset.mem_univ _

theorem allObligations_card {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] [Fintype O] :
    (allObligations U O).card = U.pos.card * 2 ^ Fintype.card O := by
  simp only [allObligations, Finset.card_univ]
  rw [Fintype.card_congr (Obligation.equivProd (U := U) (O := O)),
    Fintype.card_prod, Fintype.card_coe U.pos, Fintype.card_finset]

theorem obligation_same_P_distinct_K {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] (P : UPos U) (K₁ K₂ : DepSupport O) (hne : K₁ ≠ K₂) :
    (⟨P, K₁⟩ : Obligation U O) ≠ ⟨P, K₂⟩ := by
  intro h
  exact hne (congrArg Obligation.support h)

theorem obligation_proj_P_not_injective {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] [Nonempty O] (P : UPos U) :
    ∃ o₁ o₂ : Obligation U O, o₁.result = o₂.result ∧ o₁ ≠ o₂ := by
  let o : O := Classical.choice ‹Nonempty O›
  refine ⟨⟨P, ∅⟩, ⟨P, {o}⟩, rfl, ?_⟩
  intro h
  have : (∅ : DepSupport O) = {o} := congrArg Obligation.support h
  exact Finset.singleton_ne_empty o this.symm

end Gimbal.Equality.Scherer

/-! ### Structural search sizes (on polarized types in `Gimbal.Equality`) -/

namespace Gimbal.Equality

mutual
/-- Structural size of a positive formula (1 + child sizes). -/
def Pos.searchSize {n : Nat} : Pos n → Nat
  | .atom _ => 1
  | .zero => 1
  | .sum A B => 1 + Pos.searchSize A + Pos.searchSize B
  | .shift N => 1 + Neg.searchSize N

/-- Structural size of a negative formula (1 + child sizes). -/
def Neg.searchSize {n : Nat} : Neg n → Nat
  | .one => 1
  | .prod N₁ N₂ => 1 + Neg.searchSize N₁ + Neg.searchSize N₂
  | .arr A N => 1 + Pos.searchSize A + Neg.searchSize N
  | .shift P => 1 + Pos.searchSize P
end

@[simp] theorem Pos.searchSize_atom {n : Nat} (q : Fin n) :
    (Pos.atom q).searchSize = 1 := rfl
@[simp] theorem Pos.searchSize_zero {n : Nat} :
    (Pos.zero : Pos n).searchSize = 1 := rfl
@[simp] theorem Pos.searchSize_sum {n : Nat} (A B : Pos n) :
    (Pos.sum A B).searchSize = 1 + A.searchSize + B.searchSize := rfl
@[simp] theorem Pos.searchSize_shift {n : Nat} (N : Neg n) :
    (Pos.shift N).searchSize = 1 + N.searchSize := rfl

@[simp] theorem Neg.searchSize_one {n : Nat} :
    (Neg.one : Neg n).searchSize = 1 := rfl
@[simp] theorem Neg.searchSize_prod {n : Nat} (N₁ N₂ : Neg n) :
    (Neg.prod N₁ N₂).searchSize = 1 + N₁.searchSize + N₂.searchSize := rfl
@[simp] theorem Neg.searchSize_arr {n : Nat} (A : Pos n) (N : Neg n) :
    (Neg.arr A N).searchSize = 1 + A.searchSize + N.searchSize := rfl
@[simp] theorem Neg.searchSize_shift {n : Nat} (P : Pos n) :
    (Neg.shift P).searchSize = 1 + P.searchSize := rfl

theorem Pos.searchSize_pos {n : Nat} (P : Pos n) : 0 < P.searchSize := by
  cases P <;> simp [Pos.searchSize] <;> omega
theorem Neg.searchSize_pos {n : Nat} (N : Neg n) : 0 < N.searchSize := by
  cases N <;> simp [Neg.searchSize] <;> omega

end Gimbal.Equality

namespace Gimbal.Equality.Scherer

namespace SearchBounds

variable {U : SearchUniverse sig}

/-- One plus the maximum structural size among members of `U`. -/
def formulaBound (U : SearchUniverse sig) : Nat :=
  1 + max (U.pos.sup Pos.searchSize) (U.neg.sup Neg.searchSize)

theorem formulaBound_pos {P : Pos sig.nBases} (hP : P ∈ U.pos) :
    P.searchSize ≤ formulaBound U := by
  have : P.searchSize ≤ U.pos.sup Pos.searchSize := Finset.le_sup (f := Pos.searchSize) hP
  exact Nat.le_trans this (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_left _ 1))

theorem formulaBound_neg {N : Neg sig.nBases} (hN : N ∈ U.neg) :
    N.searchSize ≤ formulaBound U := by
  have : N.searchSize ≤ U.neg.sup Neg.searchSize := Finset.le_sup (f := Neg.searchSize) hN
  exact Nat.le_trans this (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_left _ 1))

theorem formulaBound_pos_positive (h : U.pos.Nonempty) : 0 < formulaBound U := by
  rcases h with ⟨P, hP⟩
  have hsz : 0 < P.searchSize := Pos.searchSize_pos P
  have : 0 < U.pos.sup Pos.searchSize :=
    Nat.lt_of_lt_of_le hsz (Finset.le_sup (f := Pos.searchSize) hP)
  exact Nat.lt_of_lt_of_le this (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_left _ 1))

theorem formulaBound_neg_positive (h : U.neg.Nonempty) : 0 < formulaBound U := by
  rcases h with ⟨N, hN⟩
  have hsz : 0 < N.searchSize := Neg.searchSize_pos N
  have : 0 < U.neg.sup Neg.searchSize :=
    Nat.lt_of_lt_of_le hsz (Finset.le_sup (f := Neg.searchSize) hN)
  exact Nat.lt_of_lt_of_le this (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_left _ 1))

end SearchBounds

namespace ResolvedPending

variable {U : SearchUniverse sig} {O : Type}

/-- Pending weight: sum of structural sizes of pending result types. -/
def searchWeight : ResolvedPending U O → Nat
  | [] => 0
  | c :: rest => c.ty.val.searchSize + searchWeight rest

@[simp] theorem searchWeight_nil : searchWeight ([] : ResolvedPending U O) = 0 := rfl

@[simp] theorem searchWeight_cons (c : PendingCell U O) (rest : ResolvedPending U O) :
    searchWeight (c :: rest) = c.ty.val.searchSize + searchWeight rest := rfl

end ResolvedPending

namespace SearchBounds

variable {U : SearchUniverse sig} {O : Type}

/-- One more than the number of finite obligations (round index room). -/
def roundBound (U : SearchUniverse sig) (O : Type) [DecidableEq O] [Fintype O] : Nat :=
  (allObligations U O).card + 1

/-- Length capacity covering any initial pending and a full obligation batch. -/
def pendingLengthBound (U : SearchUniverse sig) (O : Type) [DecidableEq O] [Fintype O]
    (initial : ResolvedPending U O) : Nat :=
  max 1 (max initial.length (allObligations U O).card)

/--
Candidate live-depth bound from root depth, pending weight, and finite round room.

Honesty: sufficiency for actual search (`liveDepth ≤ maxLive`) is **not** claimed here.
-/
def maxLive (U : SearchUniverse sig) (O : Type) [DecidableEq O] [Fintype O]
    (rootDepth : Nat) (initial : ResolvedPending U O) : Nat :=
  rootDepth +
    initial.searchWeight +
    formulaBound U * formulaBound U *
      roundBound U O * roundBound U O

theorem rootDepth_le_maxLive [DecidableEq O] [Fintype O]
    (rootDepth : Nat) (initial : ResolvedPending U O) :
    rootDepth ≤ maxLive U O rootDepth initial := by
  simp only [maxLive]
  omega

theorem pendingWeight_le_maxLive [DecidableEq O] [Fintype O]
    (rootDepth : Nat) (initial : ResolvedPending U O) :
    initial.searchWeight ≤ maxLive U O rootDepth initial := by
  simp only [maxLive]
  omega

theorem obligation_card_lt_roundBound [DecidableEq O] [Fintype O] :
    (allObligations U O).card < roundBound U O := by
  simp [roundBound]

theorem pendingLength_le_pendingLengthBound [DecidableEq O] [Fintype O]
    (initial : ResolvedPending U O) :
    initial.length ≤ pendingLengthBound U O initial := by
  simp only [pendingLengthBound]
  exact le_max_of_le_right (le_max_left _ _)

theorem obligation_card_le_pendingLengthBound [DecidableEq O] [Fintype O]
    (initial : ResolvedPending U O) :
    (allObligations U O).card ≤ pendingLengthBound U O initial := by
  simp only [pendingLengthBound]
  exact le_max_of_le_right (le_max_right _ _)

theorem maxLive_positive [DecidableEq O] [Fintype O]
    (rootDepth : Nat) (initial : ResolvedPending U O)
    (h : rootDepth ≠ 0 ∨ U.pos.Nonempty ∨ U.neg.Nonempty) :
    0 < maxLive U O rootDepth initial := by
  simp only [maxLive]
  have hRound : 0 < roundBound U O := by simp only [roundBound]; omega
  rcases h with hr | hp | hn
  · omega
  · have hf : 0 < formulaBound U := formulaBound_pos_positive hp
    have : 0 < formulaBound U * formulaBound U * roundBound U O * roundBound U O := by
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hf hf) hRound) hRound
    omega
  · have hf : 0 < formulaBound U := formulaBound_neg_positive hn
    have : 0 < formulaBound U * formulaBound U * roundBound U O * roundBound U O := by
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hf hf) hRound) hRound
    omega

end SearchBounds

/-! ### Length-bounded pending -/

/-- Pending list with an explicit length ceiling `L`. -/
structure BoundedPending (U : SearchUniverse sig) (O : Type) (L : Nat) where
  val : ResolvedPending U O
  length_le : val.length ≤ L

namespace BoundedPending

variable {U : SearchUniverse sig} {O : Type} {L : Nat}

/-- Forget the length bound. -/
def erase (bp : BoundedPending U O L) : ResolvedPending U O :=
  bp.val

theorem ext {bp₁ bp₂ : BoundedPending U O L} (h : bp₁.val = bp₂.val) : bp₁ = bp₂ := by
  cases bp₁; cases bp₂; cases h; rfl

theorem eq_iff_val_eq (bp₁ bp₂ : BoundedPending U O L) :
    bp₁ = bp₂ ↔ bp₁.val = bp₂.val :=
  ⟨congrArg erase, ext⟩

instance [DecidableEq O] : DecidableEq (BoundedPending U O L) := fun a b =>
  if h : a.val = b.val then isTrue (ext h)
  else isFalse fun heq => h (congrArg erase heq)

/-- Empty pending (always length-ok). -/
def empty (U : SearchUniverse sig) (O : Type) (L : Nat) : BoundedPending U O L where
  val := []
  length_le := Nat.zero_le _

/-- Cons when the resulting length stays within `L`. -/
def cons (c : PendingCell U O) (rest : BoundedPending U O L)
    (h : rest.val.length + 1 ≤ L) : BoundedPending U O L where
  val := c :: rest.val
  length_le := by simpa using h

/-- Lambda pending under `1 ≤ L`. -/
def lambdaPending (P : UPos U) (h : 1 ≤ L) : BoundedPending U O L where
  val := ResolvedPending.lambdaPending P
  length_le := by simp [ResolvedPending.lambdaPending]; exact h

/-- Encoding as a length-indexed tuple (executable Fintype carrier). -/
abbrev Code (U : SearchUniverse sig) (O : Type) (L : Nat) : Type :=
  Σ n : Fin (L + 1), Fin n.val → PendingCell U O

private def pendingCellEquiv [DecidableEq O] :
    PendingCell U O ≃ UPos U × DepSupport O where
  toFun c := (c.ty, c.support)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [DecidableEq O] [Fintype O] : Fintype (PendingCell U O) :=
  Fintype.ofEquiv _ (pendingCellEquiv (U := U) (O := O)).symm

def ofCode [DecidableEq O] (c : Code U O L) : BoundedPending U O L where
  val := List.ofFn c.2
  length_le := by
    simpa [List.length_ofFn] using Nat.le_of_lt_succ c.1.isLt

def toCode [DecidableEq O] (bp : BoundedPending U O L) : Code U O L :=
  ⟨⟨bp.val.length, Nat.lt_succ_of_le bp.length_le⟩,
    fun i => bp.val.get ⟨i.val, i.isLt⟩⟩

theorem ofCode_toCode [DecidableEq O] (bp : BoundedPending U O L) :
    ofCode (toCode bp) = bp := by
  apply ext
  change List.ofFn (fun i : Fin bp.val.length => bp.val.get i) = bp.val
  exact List.ofFn_get bp.val

instance [DecidableEq O] [Fintype O] : Fintype (Code U O L) := by
  classical
  infer_instance

instance [DecidableEq O] [Fintype O] : Fintype (BoundedPending U O L) :=
  Fintype.ofSurjective ofCode fun bp => ⟨toCode bp, ofCode_toCode bp⟩

instance [Fintype O] : Finite (BoundedPending U O L) := by
  letI := Fintype.ofFinite O
  letI : DecidableEq O := Classical.decEq O
  infer_instance

@[simp] theorem erase_empty : erase (empty U O L) = ([] : ResolvedPending U O) := rfl

@[simp] theorem erase_lambdaPending (P : UPos U) (h : 1 ≤ L) :
    erase (lambdaPending (O := O) P h) = ResolvedPending.lambdaPending P := rfl

end BoundedPending

/-! ### Fixtures -/

namespace SearchBoundsFixtures

open SearchUniverseFixtures SearchBounds

def O1 : Type := Fin 1
instance : DecidableEq O1 := inferInstanceAs (DecidableEq (Fin 1))
instance : Fintype O1 := inferInstanceAs (Fintype (Fin 1))

def P0 : UPos Uz := ⟨X, by native_decide⟩
def o0 : O1 := ⟨0, by omega⟩

/-- Fixture 1: one positive type and one base origin → two support obligations. -/
theorem two_support_obligations :
    ((allObligations Uz O1).filter (fun o => o.result = P0)).card = 2 := by
  native_decide

/-- Fixture 2: same `P` with `∅` and `{o}` are distinct. -/
theorem same_P_empty_vs_singleton_distinct :
    (⟨P0, ∅⟩ : Obligation Uz O1) ≠ ⟨P0, {o0}⟩ :=
  obligation_same_P_distinct_K P0 ∅ {o0} (by native_decide)

/-- Fixture 3: duplicate `P` obligations are both retained in pending. -/
theorem duplicate_P_retained :
    let ps := ResolvedPending.pendingFromObligations
      (O := O1) [(P0, (∅ : DepSupport O1)), (P0, {o0})]
    ps.length = 2 ∧ ps.map (·.ty) = [P0, P0] := by
  native_decide

/-- Fixture 4: `pendingLengthBound` accommodates a full obligation batch. -/
theorem pendingLengthBound_covers_batch :
    (allObligations Uz O1).card ≤ pendingLengthBound Uz O1 ([] : ResolvedPending Uz O1) :=
  obligation_card_le_pendingLengthBound ([] : ResolvedPending Uz O1)

/-- Fixture 5: `maxLive` is at least `rootDepth` and initial pending weight. -/
theorem maxLive_covers_root_and_weight :
    let initial : ResolvedPending Uz O1 := ResolvedPending.lambdaPending P0
    (3 ≤ maxLive Uz O1 3 initial) ∧
      (initial.searchWeight ≤ maxLive Uz O1 3 initial) :=
  ⟨rootDepth_le_maxLive 3 _, pendingWeight_le_maxLive 3 _⟩

theorem allObligations_card_matches :
    (allObligations Uz O1).card = Uz.pos.card * 2 ^ Fintype.card O1 :=
  allObligations_card

theorem formulaBound_gates :
    (∀ P ∈ Uz.pos, P.searchSize ≤ formulaBound Uz) ∧
      (∀ N ∈ Uz.neg, N.searchSize ≤ formulaBound Uz) ∧
      0 < formulaBound Uz := by
  refine ⟨fun _ h => formulaBound_pos h, fun _ h => formulaBound_neg h, ?_⟩
  exact formulaBound_pos_positive ⟨X, by native_decide⟩

end SearchBoundsFixtures

end Gimbal.Equality.Scherer
