/-
  Scherer-core finite polarized positive-subformula universe `U+` (S3).

  `PosOccurs` / `NegOccurs` are the exact occurrence judgments. `Pos.uPlus` /
  `Neg.uPlus` are the duplicate-free Finset enumerations. `U+` bounds possible
  result types only — membership never fabricates an observation.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Gimbal.Equality.Scherer.Syntax

namespace Gimbal.Equality

/-! ### Duplicate-free Finset enumerations (on polarized types) -/

mutual
/-- Positive subformulas of a positive polarized type, including the root. -/
def Pos.uPlus {n : Nat} : Pos n → Finset (Pos n)
  | .atom q => ({.atom q} : Finset (Pos n))
  | .zero => ({.zero} : Finset (Pos n))
  | .sum A B => insert (.sum A B) (Pos.uPlus A ∪ Pos.uPlus B)
  | .shift N => insert (.shift N) (Neg.uPlus N)

/-- Positive subformulas occurring under a negative polarized type. -/
def Neg.uPlus {n : Nat} : Neg n → Finset (Pos n)
  | .one => (∅ : Finset (Pos n))
  | .prod A B => Neg.uPlus A ∪ Neg.uPlus B
  | .arr P N => Pos.uPlus P ∪ Neg.uPlus N
  | .shift P => Pos.uPlus P
end

@[simp] theorem Pos.uPlus_atom {n : Nat} (q : Fin n) :
    (Pos.atom q).uPlus = ({.atom q} : Finset (Pos n)) := rfl
@[simp] theorem Pos.uPlus_zero {n : Nat} :
    (Pos.zero : Pos n).uPlus = ({.zero} : Finset (Pos n)) := rfl
@[simp] theorem Pos.uPlus_sum {n : Nat} (A B : Pos n) :
    (Pos.sum A B).uPlus = insert (.sum A B) (A.uPlus ∪ B.uPlus) := rfl
@[simp] theorem Pos.uPlus_shift {n : Nat} (N : Neg n) :
    (Pos.shift N).uPlus = insert (.shift N) N.uPlus := rfl

@[simp] theorem Neg.uPlus_one {n : Nat} :
    (Neg.one : Neg n).uPlus = (∅ : Finset (Pos n)) := rfl
@[simp] theorem Neg.uPlus_prod {n : Nat} (A B : Neg n) :
    (Neg.prod A B).uPlus = A.uPlus ∪ B.uPlus := rfl
@[simp] theorem Neg.uPlus_arr {n : Nat} (P : Pos n) (N : Neg n) :
    (Neg.arr P N).uPlus = P.uPlus ∪ N.uPlus := rfl
@[simp] theorem Neg.uPlus_shift {n : Nat} (P : Pos n) :
    (Neg.shift P).uPlus = P.uPlus := rfl

end Gimbal.Equality

namespace Gimbal.Equality.Scherer

variable {n : Nat}

/-! ### Occurrence judgments -/

mutual
/-- Positive `Q` occurs in positive `P`. -/
inductive PosOccurs : Pos n → Pos n → Prop where
  | root {P} : PosOccurs P P
  | sum_left {Q A B} : PosOccurs Q A → PosOccurs Q (.sum A B)
  | sum_right {Q A B} : PosOccurs Q B → PosOccurs Q (.sum A B)
  | shift {Q N} : NegOccurs Q N → PosOccurs Q (.shift N)

/-- Positive `Q` occurs inside negative `N`. `Neg.one` contributes nothing. -/
inductive NegOccurs : Pos n → Neg n → Prop where
  | prod_left {Q A B} : NegOccurs Q A → NegOccurs Q (.prod A B)
  | prod_right {Q A B} : NegOccurs Q B → NegOccurs Q (.prod A B)
  | arr_dom {Q P N} : PosOccurs Q P → NegOccurs Q (.arr P N)
  | arr_cod {Q P N} : NegOccurs Q N → NegOccurs Q (.arr P N)
  | shift {Q P} : PosOccurs Q P → NegOccurs Q (.shift P)
end

/-! ### Occurrence ↔ Finset membership -/

mutual
theorem Pos.mem_uPlus_of_occurs {Q : Pos n} :
    ∀ {P}, PosOccurs Q P → Q ∈ P.uPlus
  | _, .root => by
      cases Q with
      | atom q => simp [Pos.uPlus]
      | zero => simp [Pos.uPlus]
      | sum A B => simp [Pos.uPlus]
      | shift N => simp [Pos.uPlus]
  | _, .sum_left h =>
      Finset.mem_insert_of_mem (Finset.mem_union_left _ (Pos.mem_uPlus_of_occurs h))
  | _, .sum_right h =>
      Finset.mem_insert_of_mem (Finset.mem_union_right _ (Pos.mem_uPlus_of_occurs h))
  | _, .shift h =>
      Finset.mem_insert_of_mem (Neg.mem_uPlus_of_occurs h)

theorem Neg.mem_uPlus_of_occurs {Q : Pos n} :
    ∀ {N}, NegOccurs Q N → Q ∈ N.uPlus
  | _, .prod_left h => Finset.mem_union_left _ (Neg.mem_uPlus_of_occurs h)
  | _, .prod_right h => Finset.mem_union_right _ (Neg.mem_uPlus_of_occurs h)
  | _, .arr_dom h => Finset.mem_union_left _ (Pos.mem_uPlus_of_occurs h)
  | _, .arr_cod h => Finset.mem_union_right _ (Neg.mem_uPlus_of_occurs h)
  | _, .shift h => Pos.mem_uPlus_of_occurs h
end

mutual
theorem Pos.occurs_of_mem_uPlus {Q : Pos n} :
    ∀ P, Q ∈ P.uPlus → PosOccurs Q P
  | .atom q, h => by
      simp only [Pos.uPlus, Finset.mem_singleton] at h
      subst h; exact .root
  | .zero, h => by
      simp only [Pos.uPlus, Finset.mem_singleton] at h
      subst h; exact .root
  | .sum A B, h => by
      simp only [Pos.uPlus, Finset.mem_insert, Finset.mem_union] at h
      rcases h with rfl | hA | hB
      · exact .root
      · exact .sum_left (Pos.occurs_of_mem_uPlus A hA)
      · exact .sum_right (Pos.occurs_of_mem_uPlus B hB)
  | .shift N, h => by
      simp only [Pos.uPlus, Finset.mem_insert] at h
      rcases h with rfl | hN
      · exact .root
      · exact .shift (Neg.occurs_of_mem_uPlus N hN)

theorem Neg.occurs_of_mem_uPlus {Q : Pos n} :
    ∀ N, Q ∈ N.uPlus → NegOccurs Q N
  | .one, h => by
      simp only [Neg.uPlus, Finset.notMem_empty] at h
  | .prod A B, h => by
      simp only [Neg.uPlus, Finset.mem_union] at h
      rcases h with hA | hB
      · exact .prod_left (Neg.occurs_of_mem_uPlus A hA)
      · exact .prod_right (Neg.occurs_of_mem_uPlus B hB)
  | .arr P N, h => by
      simp only [Neg.uPlus, Finset.mem_union] at h
      rcases h with hP | hN
      · exact .arr_dom (Pos.occurs_of_mem_uPlus P hP)
      · exact .arr_cod (Neg.occurs_of_mem_uPlus N hN)
  | .shift P, h => by
      simp only [Neg.uPlus] at h
      exact .shift (Pos.occurs_of_mem_uPlus P h)
end

/-- Gate: Finset membership ↔ positive occurrence. -/
theorem Pos.mem_uPlus_iff {Q P : Pos n} : Q ∈ P.uPlus ↔ PosOccurs Q P :=
  ⟨Pos.occurs_of_mem_uPlus P, Pos.mem_uPlus_of_occurs⟩

/-- Gate: Finset membership ↔ occurrence under a negative. -/
theorem Neg.mem_uPlus_iff {Q : Pos n} {N : Neg n} : Q ∈ N.uPlus ↔ NegOccurs Q N :=
  ⟨Neg.occurs_of_mem_uPlus N, Neg.mem_uPlus_of_occurs⟩

/-! ### Stable / pending / goal / endpoint unions -/

variable {sig : Signature}

/-- Positive subformulas of one stable formula. -/
def StableTy.uPlus : StableTy sig.nBases → Finset (Pos sig.nBases)
  | .neg N => N.uPlus
  | .atom q => (Pos.atom q).uPlus

@[simp] theorem StableTy.uPlus_neg (N : Neg sig.nBases) :
    StableTy.uPlus (.neg N) = N.uPlus := rfl

@[simp] theorem StableTy.uPlus_atom (q : Fin sig.nBases) :
    StableTy.uPlus (.atom q) = (Pos.atom q).uPlus := rfl

theorem StableTy.mem_uPlus_neg {Q : Pos sig.nBases} {N : Neg sig.nBases} :
    Q ∈ StableTy.uPlus (.neg N) ↔ NegOccurs Q N := by
  simp [StableTy.uPlus, Neg.mem_uPlus_iff]

theorem StableTy.mem_uPlus_atom {Q : Pos sig.nBases} {q : Fin sig.nBases} :
    Q ∈ StableTy.uPlus (.atom q) ↔ PosOccurs Q (.atom q) := by
  change Q ∈ (Pos.atom q).uPlus ↔ PosOccurs Q (.atom q)
  exact Pos.mem_uPlus_iff

/-- Union of positive subformulas over a stable context. -/
def StableCtx.uPlus : StableCtx sig → Finset (Pos sig.nBases)
  | .empty => ∅
  | .snoc Γ S => Γ.uPlus ∪ S.uPlus

@[simp] theorem StableCtx.uPlus_empty :
    (StableCtx.empty : StableCtx sig).uPlus = ∅ := rfl

@[simp] theorem StableCtx.uPlus_snoc (Γ : StableCtx sig) (S : StableTy sig.nBases) :
    (Γ.snoc S).uPlus = Γ.uPlus ∪ S.uPlus := rfl

theorem StableCtx.mem_uPlus_snoc {Q : Pos sig.nBases}
    {Γ : StableCtx sig} {S : StableTy sig.nBases} :
    Q ∈ (Γ.snoc S).uPlus ↔ Q ∈ Γ.uPlus ∨ Q ∈ S.uPlus := by
  simp [StableCtx.uPlus]

/-- Union of positive subformulas over a pending worklist. -/
def Pending.uPlus : Pending sig → Finset (Pos sig.nBases)
  | .empty => ∅
  | .cons P ps => P.uPlus ∪ ps.uPlus

@[simp] theorem Pending.uPlus_empty :
    (Pending.empty : Pending sig).uPlus = ∅ := rfl

@[simp] theorem Pending.uPlus_cons (P : Pos sig.nBases) (ps : Pending sig) :
    (Pending.cons P ps).uPlus = P.uPlus ∪ ps.uPlus := rfl

theorem Pending.mem_uPlus_cons {Q : Pos sig.nBases}
    {P : Pos sig.nBases} {ps : Pending sig} :
    Q ∈ (Pending.cons P ps).uPlus ↔ Q ∈ P.uPlus ∨ Q ∈ ps.uPlus := by
  simp [Pending.uPlus]

/-- Positive subformulas of a goal. -/
def Goal.uPlus {m : Nat} : Goal m → Finset (Pos m)
  | .neg N => N.uPlus
  | .pos P => P.uPlus

@[simp] theorem Goal.uPlus_neg {m : Nat} (N : Neg m) :
    Goal.uPlus (.neg N) = N.uPlus := rfl

@[simp] theorem Goal.uPlus_pos {m : Nat} (P : Pos m) :
    Goal.uPlus (.pos P) = P.uPlus := rfl

theorem Goal.mem_uPlus_neg {m : Nat} {Q : Pos m} {N : Neg m} :
    Q ∈ Goal.uPlus (.neg N) ↔ NegOccurs Q N := by
  simp [Goal.uPlus, Neg.mem_uPlus_iff]

theorem Goal.mem_uPlus_pos {m : Nat} {Q P : Pos m} :
    Q ∈ Goal.uPlus (.pos P) ↔ PosOccurs Q P := by
  simp [Goal.uPlus, Pos.mem_uPlus_iff]

/-- Union of positive subformulas of a list of endpoint result types. -/
def endpointsUPlus : List (Pos n) → Finset (Pos n)
  | [] => ∅
  | P :: rest => P.uPlus ∪ endpointsUPlus rest

@[simp] theorem endpointsUPlus_nil : endpointsUPlus ([] : List (Pos n)) = ∅ := rfl

@[simp] theorem endpointsUPlus_cons (P : Pos n) (rest : List (Pos n)) :
    endpointsUPlus (P :: rest) = P.uPlus ∪ endpointsUPlus rest := rfl

theorem mem_endpointsUPlus {Q : Pos n} :
    ∀ {rs : List (Pos n)}, Q ∈ endpointsUPlus rs ↔ ∃ P ∈ rs, PosOccurs Q P
  | [] => by
      constructor
      · intro h; exact absurd h (Finset.notMem_empty _)
      · intro ⟨_, hMem, _⟩; cases hMem
  | P :: rest => by
      simp only [endpointsUPlus, Finset.mem_union, Pos.mem_uPlus_iff, List.mem_cons,
        mem_endpointsUPlus (rs := rest)]
      constructor
      · intro h
        rcases h with hP | ⟨P', hMem, hOcc⟩
        · exact ⟨P, Or.inl rfl, hP⟩
        · exact ⟨P', Or.inr hMem, hOcc⟩
      · intro ⟨P', hMem, hOcc⟩
        rcases hMem with rfl | hMem
        · exact Or.inl hOcc
        · exact Or.inr ⟨P', hMem, hOcc⟩

/-! ### Input-assembled universe -/

namespace UPlus

/--
Finite `U+` assembled from stable context, pending, goal, and endpoint results.
Membership is type-level only — never an observation witness.
-/
def fromInputs (Γ : StableCtx sig) (ps : Pending sig) (G : Goal sig.nBases)
    (endpointResults : List (Pos sig.nBases)) : Finset (Pos sig.nBases) :=
  Γ.uPlus ∪ ps.uPlus ∪ G.uPlus ∪ endpointsUPlus endpointResults

/-- Gate: membership in the assembled universe. -/
theorem mem_fromInputs_iff {Q : Pos sig.nBases}
    {Γ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
    {endpointResults : List (Pos sig.nBases)} :
    Q ∈ fromInputs Γ ps G endpointResults ↔
      Q ∈ Γ.uPlus ∨
        Q ∈ ps.uPlus ∨
          Q ∈ G.uPlus ∨
            ∃ P ∈ endpointResults, PosOccurs Q P := by
  unfold fromInputs
  simp only [Finset.mem_union, mem_endpointsUPlus]
  constructor
  · intro h
    rcases h with ((hΓ | hps) | hG) | hep
    · exact Or.inl hΓ
    · exact Or.inr (Or.inl hps)
    · exact Or.inr (Or.inr (Or.inl hG))
    · exact Or.inr (Or.inr (Or.inr hep))
  · intro h
    rcases h with hΓ | hps | hG | hep
    · exact Or.inl (Or.inl (Or.inl hΓ))
    · exact Or.inl (Or.inl (Or.inr hps))
    · exact Or.inl (Or.inr hG)
    · exact Or.inr hep

end UPlus

/-! ### Adversarial fixtures -/

namespace UPlusFixtures

def sig0 : Signature := ⟨0, #[]⟩

def X : Pos 0 := .zero
def Y : Pos 0 := .shift .one
def Z : Pos 0 := .shift (.shift .zero)

/-- Stable negative `arr (sum X Y) (shift Z)` includes `sum X Y`, `X`, `Y`, and `Z`. -/
def stableNeg : Neg 0 := .arr (.sum X Y) (.shift Z)

theorem stableNeg_includes_sum_and_leaves :
    (Pos.sum X Y ∈ stableNeg.uPlus) ∧
      (X ∈ stableNeg.uPlus) ∧
      (Y ∈ stableNeg.uPlus) ∧
      (Z ∈ stableNeg.uPlus) := by
  native_decide

/-- `Neg.one` contributes no positive type. -/
theorem one_contributes_nothing :
    (Neg.one : Neg 0).uPlus = (∅ : Finset (Pos 0)) := rfl

/-- Duplicate occurrences of the same positive type produce cardinality one. -/
theorem duplicate_occurrence_card_one :
    let N : Neg 0 := .arr X (.shift X)
    N.uPlus.card = 1 ∧ X ∈ N.uPlus := by
  native_decide

/-- An endpoint result contributes its root and nested positive subformulas. -/
theorem endpoint_contributes_root_and_nested :
    let ep : List (Pos 0) := [.sum X Y]
    (Pos.sum X Y ∈ endpointsUPlus ep) ∧
      (X ∈ endpointsUPlus ep) ∧
      (Y ∈ endpointsUPlus ep) := by
  native_decide

/--
`U+` membership returns only a type-membership proof (`∈ Finset (Pos _)`).
It is not an `SNegNeu`, `FreshObs`, `SelectedBatch`, or fabricated observation.
-/
theorem membership_is_type_only :
    ∃ (_ : X ∈ stableNeg.uPlus), True :=
  ⟨by native_decide, trivial⟩

/-- Assembled `fromInputs` sees context, pending, goal, and endpoints. -/
theorem fromInputs_sees_all_sources :
    let Γ : StableCtx sig0 := .snoc .empty (.neg (.shift X))
    let ps : Pending sig0 := .cons Y .empty
    let G : Goal 0 := .pos Z
    let ep : List (Pos 0) := [.sum X Y]
    let U := UPlus.fromInputs Γ ps G ep
    (X ∈ U) ∧ (Y ∈ U) ∧ (Z ∈ U) ∧ (Pos.sum X Y ∈ U) := by
  native_decide

end UPlusFixtures

end Gimbal.Equality.Scherer
