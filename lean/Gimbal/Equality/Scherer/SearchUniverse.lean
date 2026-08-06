/-
  Scherer-core signed finite polarized search universe (S3 post-foundation).

  Extends `U+` with negative-node and stable-wrapper enumerations so search keys
  can be drawn from finite membership subtypes. No origin support, SearchKey,
  rank, forest, coverage, or S4 work.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Gimbal.Equality.Scherer.UPlus
import Gimbal.Equality.Scherer.SearchState

namespace Gimbal.Equality

mutual
def Pos.uNeg {n : Nat} : Pos n → Finset (Neg n)
  | .atom _ => (∅ : Finset (Neg n))
  | .zero => (∅ : Finset (Neg n))
  | .sum A B => Pos.uNeg A ∪ Pos.uNeg B
  | .shift N => Neg.uNeg N

def Neg.uNeg {n : Nat} : Neg n → Finset (Neg n)
  | .one => ({.one} : Finset (Neg n))
  | .prod A B => insert (.prod A B) (Neg.uNeg A ∪ Neg.uNeg B)
  | .arr P N => insert (.arr P N) (Pos.uNeg P ∪ Neg.uNeg N)
  | .shift P => insert (.shift P) (Pos.uNeg P)
end

@[simp] theorem Pos.uNeg_atom {n} (q : Fin n) :
    (Pos.atom q).uNeg = (∅ : Finset (Neg n)) := rfl
@[simp] theorem Pos.uNeg_zero {n} :
    (Pos.zero : Pos n).uNeg = (∅ : Finset (Neg n)) := rfl
@[simp] theorem Pos.uNeg_sum {n} (A B : Pos n) :
    (Pos.sum A B).uNeg = A.uNeg ∪ B.uNeg := rfl
@[simp] theorem Pos.uNeg_shift {n} (N : Neg n) :
    (Pos.shift N).uNeg = N.uNeg := rfl
@[simp] theorem Neg.uNeg_one {n} :
    (Neg.one : Neg n).uNeg = ({.one} : Finset (Neg n)) := rfl
@[simp] theorem Neg.uNeg_prod {n} (A B : Neg n) :
    (Neg.prod A B).uNeg = insert (.prod A B) (A.uNeg ∪ B.uNeg) := rfl
@[simp] theorem Neg.uNeg_arr {n} (P : Pos n) (N : Neg n) :
    (Neg.arr P N).uNeg = insert (.arr P N) (P.uNeg ∪ N.uNeg) := rfl
@[simp] theorem Neg.uNeg_shift {n} (P : Pos n) :
    (Neg.shift P).uNeg = insert (.shift P) P.uNeg := rfl

end Gimbal.Equality

namespace Gimbal.Equality.Scherer

variable {n : Nat}

mutual
inductive NegOccursInPos : Neg n → Pos n → Prop where
  | sum_left {N A B} : NegOccursInPos N A → NegOccursInPos N (.sum A B)
  | sum_right {N A B} : NegOccursInPos N B → NegOccursInPos N (.sum A B)
  | shift {N M} : NegOccursInNeg N M → NegOccursInPos N (.shift M)

inductive NegOccursInNeg : Neg n → Neg n → Prop where
  | root {N} : NegOccursInNeg N N
  | prod_left {N A B} : NegOccursInNeg N A → NegOccursInNeg N (.prod A B)
  | prod_right {N A B} : NegOccursInNeg N B → NegOccursInNeg N (.prod A B)
  | arr_dom {N P M} : NegOccursInPos N P → NegOccursInNeg N (.arr P M)
  | arr_cod {N P M} : NegOccursInNeg N M → NegOccursInNeg N (.arr P M)
  | shift {N P} : NegOccursInPos N P → NegOccursInNeg N (.shift P)
end

mutual
theorem Pos.mem_uNeg_of_occurs {N : Neg n} :
    ∀ {P}, NegOccursInPos N P → N ∈ P.uNeg
  | _, .sum_left h => Finset.mem_union_left _ (Pos.mem_uNeg_of_occurs h)
  | _, .sum_right h => Finset.mem_union_right _ (Pos.mem_uNeg_of_occurs h)
  | _, .shift h => Neg.mem_uNeg_of_occurs h

theorem Neg.mem_uNeg_of_occurs {N : Neg n} :
    ∀ {M}, NegOccursInNeg N M → N ∈ M.uNeg
  | _, .root => by cases N <;> simp [Neg.uNeg]
  | _, .prod_left h =>
      Finset.mem_insert_of_mem (Finset.mem_union_left _ (Neg.mem_uNeg_of_occurs h))
  | _, .prod_right h =>
      Finset.mem_insert_of_mem (Finset.mem_union_right _ (Neg.mem_uNeg_of_occurs h))
  | _, .arr_dom h =>
      Finset.mem_insert_of_mem (Finset.mem_union_left _ (Pos.mem_uNeg_of_occurs h))
  | _, .arr_cod h =>
      Finset.mem_insert_of_mem (Finset.mem_union_right _ (Neg.mem_uNeg_of_occurs h))
  | _, .shift h =>
      Finset.mem_insert_of_mem (Pos.mem_uNeg_of_occurs h)
end

mutual
theorem Pos.occurs_of_mem_uNeg {N : Neg n} :
    ∀ P, N ∈ P.uNeg → NegOccursInPos N P
  | .atom _, h => by simp [Pos.uNeg] at h
  | .zero, h => by simp [Pos.uNeg] at h
  | .sum A B, h => by
      simp only [Pos.uNeg, Finset.mem_union] at h
      rcases h with hA | hB
      · exact .sum_left (Pos.occurs_of_mem_uNeg A hA)
      · exact .sum_right (Pos.occurs_of_mem_uNeg B hB)
  | .shift M, h => .shift (Neg.occurs_of_mem_uNeg M h)

theorem Neg.occurs_of_mem_uNeg {N : Neg n} :
    ∀ M, N ∈ M.uNeg → NegOccursInNeg N M
  | .one, h => by simp only [Neg.uNeg, Finset.mem_singleton] at h; subst h; exact .root
  | .prod A B, h => by
      simp only [Neg.uNeg, Finset.mem_insert, Finset.mem_union] at h
      rcases h with rfl | hA | hB
      · exact .root
      · exact .prod_left (Neg.occurs_of_mem_uNeg A hA)
      · exact .prod_right (Neg.occurs_of_mem_uNeg B hB)
  | .arr P M, h => by
      simp only [Neg.uNeg, Finset.mem_insert, Finset.mem_union] at h
      rcases h with rfl | hP | hM
      · exact .root
      · exact .arr_dom (Pos.occurs_of_mem_uNeg P hP)
      · exact .arr_cod (Neg.occurs_of_mem_uNeg M hM)
  | .shift P, h => by
      simp only [Neg.uNeg, Finset.mem_insert] at h
      rcases h with rfl | hP
      · exact .root
      · exact .shift (Pos.occurs_of_mem_uNeg P hP)
end

theorem Pos.mem_uNeg_iff {N : Neg n} {P : Pos n} :
    N ∈ P.uNeg ↔ NegOccursInPos N P :=
  ⟨Pos.occurs_of_mem_uNeg P, Pos.mem_uNeg_of_occurs⟩

theorem Neg.mem_uNeg_iff {N M : Neg n} :
    N ∈ M.uNeg ↔ NegOccursInNeg N M :=
  ⟨Neg.occurs_of_mem_uNeg M, Neg.mem_uNeg_of_occurs⟩

/-! ### Child extraction -/

mutual
theorem PosOccurs.sum_left_child {A B Q : Pos n} :
    PosOccurs (.sum A B) Q → PosOccurs A Q
  | .root => .sum_left .root
  | .sum_left h => .sum_left (PosOccurs.sum_left_child h)
  | .sum_right h => .sum_right (PosOccurs.sum_left_child h)
  | .shift h => .shift (NegOccurs.sum_left_child h)
theorem NegOccurs.sum_left_child {A B : Pos n} {N : Neg n} :
    NegOccurs (.sum A B) N → NegOccurs A N
  | .prod_left h => .prod_left (NegOccurs.sum_left_child h)
  | .prod_right h => .prod_right (NegOccurs.sum_left_child h)
  | .arr_dom h => .arr_dom (PosOccurs.sum_left_child h)
  | .arr_cod h => .arr_cod (NegOccurs.sum_left_child h)
  | .shift h => .shift (PosOccurs.sum_left_child h)
end

mutual
theorem PosOccurs.sum_right_child {A B Q : Pos n} :
    PosOccurs (.sum A B) Q → PosOccurs B Q
  | .root => .sum_right .root
  | .sum_left h => .sum_left (PosOccurs.sum_right_child h)
  | .sum_right h => .sum_right (PosOccurs.sum_right_child h)
  | .shift h => .shift (NegOccurs.sum_right_child h)
theorem NegOccurs.sum_right_child {A B : Pos n} {N : Neg n} :
    NegOccurs (.sum A B) N → NegOccurs B N
  | .prod_left h => .prod_left (NegOccurs.sum_right_child h)
  | .prod_right h => .prod_right (NegOccurs.sum_right_child h)
  | .arr_dom h => .arr_dom (PosOccurs.sum_right_child h)
  | .arr_cod h => .arr_cod (NegOccurs.sum_right_child h)
  | .shift h => .shift (PosOccurs.sum_right_child h)
end

mutual
theorem PosOccurs.shift_child_neg {M : Neg n} {Q : Pos n} :
    PosOccurs (.shift M) Q → NegOccursInPos M Q
  | .root => .shift .root
  | .sum_left h => .sum_left (PosOccurs.shift_child_neg h)
  | .sum_right h => .sum_right (PosOccurs.shift_child_neg h)
  | .shift h => .shift (NegOccurs.shift_child_neg h)
theorem NegOccurs.shift_child_neg {M N : Neg n} :
    NegOccurs (.shift M) N → NegOccursInNeg M N
  | .prod_left h => .prod_left (NegOccurs.shift_child_neg h)
  | .prod_right h => .prod_right (NegOccurs.shift_child_neg h)
  | .arr_dom h => .arr_dom (PosOccurs.shift_child_neg h)
  | .arr_cod h => .arr_cod (NegOccurs.shift_child_neg h)
  | .shift h => .shift (PosOccurs.shift_child_neg h)
end

mutual
theorem NegOccursInNeg.prod_left_child {A B M : Neg n} :
    NegOccursInNeg (.prod A B) M → NegOccursInNeg A M
  | .root => .prod_left .root
  | .prod_left h => .prod_left (NegOccursInNeg.prod_left_child h)
  | .prod_right h => .prod_right (NegOccursInNeg.prod_left_child h)
  | .arr_dom h => .arr_dom (NegOccursInPos.prod_left_child h)
  | .arr_cod h => .arr_cod (NegOccursInNeg.prod_left_child h)
  | .shift h => .shift (NegOccursInPos.prod_left_child h)
theorem NegOccursInPos.prod_left_child {A B : Neg n} {P : Pos n} :
    NegOccursInPos (.prod A B) P → NegOccursInPos A P
  | .sum_left h => .sum_left (NegOccursInPos.prod_left_child h)
  | .sum_right h => .sum_right (NegOccursInPos.prod_left_child h)
  | .shift h => .shift (NegOccursInNeg.prod_left_child h)
end

mutual
theorem NegOccursInNeg.prod_right_child {A B M : Neg n} :
    NegOccursInNeg (.prod A B) M → NegOccursInNeg B M
  | .root => .prod_right .root
  | .prod_left h => .prod_left (NegOccursInNeg.prod_right_child h)
  | .prod_right h => .prod_right (NegOccursInNeg.prod_right_child h)
  | .arr_dom h => .arr_dom (NegOccursInPos.prod_right_child h)
  | .arr_cod h => .arr_cod (NegOccursInNeg.prod_right_child h)
  | .shift h => .shift (NegOccursInPos.prod_right_child h)
theorem NegOccursInPos.prod_right_child {A B : Neg n} {P : Pos n} :
    NegOccursInPos (.prod A B) P → NegOccursInPos B P
  | .sum_left h => .sum_left (NegOccursInPos.prod_right_child h)
  | .sum_right h => .sum_right (NegOccursInPos.prod_right_child h)
  | .shift h => .shift (NegOccursInNeg.prod_right_child h)
end

mutual
theorem NegOccursInNeg.arr_cod_child {P : Pos n} {Cod M : Neg n} :
    NegOccursInNeg (.arr P Cod) M → NegOccursInNeg Cod M
  | .root => .arr_cod .root
  | .prod_left h => .prod_left (NegOccursInNeg.arr_cod_child h)
  | .prod_right h => .prod_right (NegOccursInNeg.arr_cod_child h)
  | .arr_dom h => .arr_dom (NegOccursInPos.arr_cod_child h)
  | .arr_cod h => .arr_cod (NegOccursInNeg.arr_cod_child h)
  | .shift h => .shift (NegOccursInPos.arr_cod_child h)
theorem NegOccursInPos.arr_cod_child {P : Pos n} {Cod : Neg n} {Q : Pos n} :
    NegOccursInPos (.arr P Cod) Q → NegOccursInPos Cod Q
  | .sum_left h => .sum_left (NegOccursInPos.arr_cod_child h)
  | .sum_right h => .sum_right (NegOccursInPos.arr_cod_child h)
  | .shift h => .shift (NegOccursInNeg.arr_cod_child h)
end

mutual
theorem NegOccursInNeg.arr_dom_mem_uPlus {P : Pos n} {Cod M : Neg n} :
    NegOccursInNeg (.arr P Cod) M → P ∈ M.uPlus
  | .root => Finset.mem_union_left _ ((Pos.mem_uPlus_iff).mpr .root)
  | .prod_left h => Finset.mem_union_left _ (NegOccursInNeg.arr_dom_mem_uPlus h)
  | .prod_right h => Finset.mem_union_right _ (NegOccursInNeg.arr_dom_mem_uPlus h)
  | .arr_dom h => Finset.mem_union_left _ (NegOccursInPos.arr_dom_mem_uPlus h)
  | .arr_cod h => Finset.mem_union_right _ (NegOccursInNeg.arr_dom_mem_uPlus h)
  | .shift h => NegOccursInPos.arr_dom_mem_uPlus h
theorem NegOccursInPos.arr_dom_mem_uPlus {P : Pos n} {Cod : Neg n} {Q : Pos n} :
    NegOccursInPos (.arr P Cod) Q → P ∈ Q.uPlus
  | .sum_left h =>
      Finset.mem_insert_of_mem (Finset.mem_union_left _ (NegOccursInPos.arr_dom_mem_uPlus h))
  | .sum_right h =>
      Finset.mem_insert_of_mem (Finset.mem_union_right _ (NegOccursInPos.arr_dom_mem_uPlus h))
  | .shift h => Finset.mem_insert_of_mem (NegOccursInNeg.arr_dom_mem_uPlus h)
end

mutual
theorem NegOccursInNeg.shift_mem_uPlus {P : Pos n} {M : Neg n} :
    NegOccursInNeg (.shift P) M → P ∈ M.uPlus
  | .root => (Pos.mem_uPlus_iff).mpr .root
  | .prod_left h => Finset.mem_union_left _ (NegOccursInNeg.shift_mem_uPlus h)
  | .prod_right h => Finset.mem_union_right _ (NegOccursInNeg.shift_mem_uPlus h)
  | .arr_dom h => Finset.mem_union_left _ (NegOccursInPos.shift_mem_uPlus h)
  | .arr_cod h => Finset.mem_union_right _ (NegOccursInNeg.shift_mem_uPlus h)
  | .shift h => NegOccursInPos.shift_mem_uPlus h
theorem NegOccursInPos.shift_mem_uPlus {P Q : Pos n} :
    NegOccursInPos (.shift P) Q → P ∈ Q.uPlus
  | .sum_left h =>
      Finset.mem_insert_of_mem (Finset.mem_union_left _ (NegOccursInPos.shift_mem_uPlus h))
  | .sum_right h =>
      Finset.mem_insert_of_mem (Finset.mem_union_right _ (NegOccursInPos.shift_mem_uPlus h))
  | .shift h => Finset.mem_insert_of_mem (NegOccursInNeg.shift_mem_uPlus h)
end

/-! ### Formula-level closure (transition interface) -/

theorem mem_uPlus_sum_left {Q A B : Pos n} (h : Pos.sum A B ∈ Q.uPlus) :
    A ∈ Q.uPlus :=
  (Pos.mem_uPlus_iff).mpr (PosOccurs.sum_left_child ((Pos.mem_uPlus_iff).mp h))

theorem mem_uPlus_sum_right {Q A B : Pos n} (h : Pos.sum A B ∈ Q.uPlus) :
    B ∈ Q.uPlus :=
  (Pos.mem_uPlus_iff).mpr (PosOccurs.sum_right_child ((Pos.mem_uPlus_iff).mp h))

theorem mem_uPlus_shift_neg {Q : Pos n} {M : Neg n} (h : Pos.shift M ∈ Q.uPlus) :
    M ∈ Q.uNeg :=
  (Pos.mem_uNeg_iff).mpr (PosOccurs.shift_child_neg ((Pos.mem_uPlus_iff).mp h))

theorem mem_uNeg_prod_left {M A B : Neg n} (h : Neg.prod A B ∈ M.uNeg) :
    A ∈ M.uNeg :=
  (Neg.mem_uNeg_iff).mpr (NegOccursInNeg.prod_left_child ((Neg.mem_uNeg_iff).mp h))

theorem mem_uNeg_prod_right {M A B : Neg n} (h : Neg.prod A B ∈ M.uNeg) :
    B ∈ M.uNeg :=
  (Neg.mem_uNeg_iff).mpr (NegOccursInNeg.prod_right_child ((Neg.mem_uNeg_iff).mp h))

theorem mem_uNeg_arr_cod {M : Neg n} {P : Pos n} {Cod : Neg n}
    (h : Neg.arr P Cod ∈ M.uNeg) : Cod ∈ M.uNeg :=
  (Neg.mem_uNeg_iff).mpr (NegOccursInNeg.arr_cod_child ((Neg.mem_uNeg_iff).mp h))

theorem mem_uNeg_arr_dom {M : Neg n} {P : Pos n} {Cod : Neg n}
    (h : Neg.arr P Cod ∈ M.uNeg) : P ∈ M.uPlus :=
  NegOccursInNeg.arr_dom_mem_uPlus ((Neg.mem_uNeg_iff).mp h)

theorem mem_uNeg_shift_pos {M : Neg n} {P : Pos n} (h : Neg.shift P ∈ M.uNeg) :
    P ∈ M.uPlus :=
  NegOccursInNeg.shift_mem_uPlus ((Neg.mem_uNeg_iff).mp h)

/-! ### Input-side unions -/

variable {sig : Signature}

def StableTy.uNeg : StableTy sig.nBases → Finset (Neg sig.nBases)
  | .neg N => N.uNeg
  | .atom _ => ∅

@[simp] theorem StableTy.uNeg_neg (N : Neg sig.nBases) :
    StableTy.uNeg (.neg N) = N.uNeg := rfl
@[simp] theorem StableTy.uNeg_atom (q : Fin sig.nBases) :
    StableTy.uNeg (.atom q) = (∅ : Finset (Neg sig.nBases)) := rfl

def StableCtx.uNeg : StableCtx sig → Finset (Neg sig.nBases)
  | .empty => ∅
  | .snoc Γ S => Γ.uNeg ∪ S.uNeg

@[simp] theorem StableCtx.uNeg_empty :
    (StableCtx.empty : StableCtx sig).uNeg = ∅ := rfl
@[simp] theorem StableCtx.uNeg_snoc (Γ : StableCtx sig) (S : StableTy sig.nBases) :
    (Γ.snoc S).uNeg = Γ.uNeg ∪ S.uNeg := rfl

def Pending.uNeg : Pending sig → Finset (Neg sig.nBases)
  | .empty => ∅
  | .cons P ps => P.uNeg ∪ ps.uNeg

@[simp] theorem Pending.uNeg_empty :
    (Pending.empty : Pending sig).uNeg = ∅ := rfl
@[simp] theorem Pending.uNeg_cons (P : Pos sig.nBases) (ps : Pending sig) :
    (Pending.cons P ps).uNeg = P.uNeg ∪ ps.uNeg := rfl

def Goal.uNeg {m : Nat} : Goal m → Finset (Neg m)
  | .neg N => N.uNeg
  | .pos P => P.uNeg

@[simp] theorem Goal.uNeg_neg {m} (N : Neg m) : Goal.uNeg (.neg N) = N.uNeg := rfl
@[simp] theorem Goal.uNeg_pos {m} (P : Pos m) : Goal.uNeg (.pos P) = P.uNeg := rfl

def endpointResultsUNeg : List (Pos n) → Finset (Neg n)
  | [] => ∅
  | P :: rest => P.uNeg ∪ endpointResultsUNeg rest

@[simp] theorem endpointResultsUNeg_nil :
    endpointResultsUNeg ([] : List (Pos n)) = ∅ := rfl
@[simp] theorem endpointResultsUNeg_cons (P : Pos n) (rest : List (Pos n)) :
    endpointResultsUNeg (P :: rest) = P.uNeg ∪ endpointResultsUNeg rest := rfl

theorem mem_endpointResultsUNeg {N : Neg n} :
    ∀ {rs : List (Pos n)},
      N ∈ endpointResultsUNeg rs ↔ ∃ P ∈ rs, NegOccursInPos N P
  | [] => by
      constructor
      · intro h; exact absurd h (Finset.notMem_empty _)
      · intro ⟨_, hMem, _⟩; cases hMem
  | P :: rest => by
      simp only [endpointResultsUNeg, Finset.mem_union, Pos.mem_uNeg_iff, List.mem_cons,
        mem_endpointResultsUNeg (rs := rest)]
      constructor
      · intro h
        rcases h with hP | ⟨P', hMem, hOcc⟩
        · exact ⟨P, Or.inl rfl, hP⟩
        · exact ⟨P', Or.inr hMem, hOcc⟩
      · intro ⟨P', hMem, hOcc⟩
        rcases hMem with rfl | hMem
        · exact Or.inl hOcc
        · exact Or.inr ⟨P', hMem, hOcc⟩

def StableCtx.types : StableCtx sig → Finset (StableTy sig.nBases)
  | .empty => ∅
  | .snoc Γ S => insert S (Γ.types)

@[simp] theorem StableCtx.types_empty :
    (StableCtx.empty : StableCtx sig).types = ∅ := rfl
@[simp] theorem StableCtx.types_snoc (Γ : StableCtx sig) (S : StableTy sig.nBases) :
    (Γ.snoc S).types = insert S Γ.types := rfl

theorem StableCtx.mem_types_iff {S : StableTy sig.nBases} :
    ∀ {Γ : StableCtx sig}, S ∈ Γ.types ↔ Nonempty (StableVar Γ S)
  | .empty => by
      constructor
      · intro h; exact absurd h (Finset.notMem_empty _)
      · intro ⟨x⟩; cases x
  | .snoc Γ S' => by
      simp only [StableCtx.types, Finset.mem_insert, StableCtx.mem_types_iff (Γ := Γ)]
      constructor
      · intro h
        rcases h with rfl | hΓ
        · exact ⟨.here⟩
        · obtain ⟨x⟩ := hΓ
          exact ⟨.there x⟩
      · intro ⟨x⟩
        cases x with
        | here => exact Or.inl rfl
        | there x => exact Or.inr ⟨x⟩

/-! ### Search universe -/

structure SearchUniverse (sig : Signature) where
  pos : Finset (Pos sig.nBases)
  neg : Finset (Neg sig.nBases)
  stable : Finset (StableTy sig.nBases)

namespace SearchUniverse

def stableAtoms (pos : Finset (Pos sig.nBases)) : Finset (StableTy sig.nBases) :=
  pos.biUnion fun
    | .atom q => ({.atom q} : Finset (StableTy sig.nBases))
    | _ => ∅

def stableNegs (neg : Finset (Neg sig.nBases)) : Finset (StableTy sig.nBases) :=
  neg.image (.neg ·)

def fromInputs (Γ : StableCtx sig) (ps : Pending sig) (G : Goal sig.nBases)
    (endpointResults : List (Pos sig.nBases)) : SearchUniverse sig :=
  let pos := UPlus.fromInputs Γ ps G endpointResults
  let neg := Γ.uNeg ∪ ps.uNeg ∪ G.uNeg ∪ endpointResultsUNeg endpointResults
  ⟨pos, neg, Γ.types ∪ stableAtoms pos ∪ stableNegs neg⟩

variable (Γ : StableCtx sig) (ps : Pending sig) (G : Goal sig.nBases)
  (endpointResults : List (Pos sig.nBases))

theorem pos_fromInputs :
    (fromInputs Γ ps G endpointResults).pos =
      UPlus.fromInputs Γ ps G endpointResults := rfl

theorem mem_neg_fromInputs_iff {N : Neg sig.nBases} :
    N ∈ (fromInputs Γ ps G endpointResults).neg ↔
      N ∈ Γ.uNeg ∨
        N ∈ ps.uNeg ∨
          N ∈ G.uNeg ∨
            ∃ P ∈ endpointResults, NegOccursInPos N P := by
  simp only [fromInputs, Finset.mem_union, mem_endpointResultsUNeg]
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

theorem stable_of_context {S : StableTy sig.nBases}
    (h : Nonempty (StableVar Γ S)) :
    S ∈ (fromInputs Γ ps G endpointResults).stable := by
  simp only [fromInputs, Finset.mem_union]
  exact Or.inl (Or.inl ((StableCtx.mem_types_iff).mpr h))

theorem mem_stableAtoms_atom {pos : Finset (Pos sig.nBases)} {q : Fin sig.nBases}
    (h : Pos.atom q ∈ pos) : StableTy.atom q ∈ stableAtoms pos := by
  refine Finset.mem_biUnion.mpr ⟨.atom q, h, ?_⟩; simp

theorem stable_atom {q : Fin sig.nBases}
    (h : Pos.atom q ∈ (fromInputs Γ ps G endpointResults).pos) :
    StableTy.atom q ∈ (fromInputs Γ ps G endpointResults).stable := by
  simp only [fromInputs, Finset.mem_union]
  exact Or.inl (Or.inr (mem_stableAtoms_atom
    (pos := UPlus.fromInputs Γ ps G endpointResults) h))

theorem stable_neg {N : Neg sig.nBases}
    (h : N ∈ (fromInputs Γ ps G endpointResults).neg) :
    StableTy.neg N ∈ (fromInputs Γ ps G endpointResults).stable := by
  simp only [fromInputs] at h ⊢
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_image_of_mem _ h

end SearchUniverse

/-! ### Bounded finite membership types -/

abbrev UPos (U : SearchUniverse sig) := { P : Pos sig.nBases // P ∈ U.pos }
abbrev UNeg (U : SearchUniverse sig) := { N : Neg sig.nBases // N ∈ U.neg }
abbrev UStable (U : SearchUniverse sig) := { S : StableTy sig.nBases // S ∈ U.stable }

instance (U : SearchUniverse sig) : DecidableEq (UPos U) := inferInstance
instance (U : SearchUniverse sig) : DecidableEq (UNeg U) := inferInstance
instance (U : SearchUniverse sig) : DecidableEq (UStable U) := inferInstance

instance (U : SearchUniverse sig) : Fintype (UPos U) :=
  inferInstanceAs (Fintype { P // P ∈ U.pos })
instance (U : SearchUniverse sig) : Fintype (UNeg U) :=
  inferInstanceAs (Fintype { N // N ∈ U.neg })
instance (U : SearchUniverse sig) : Fintype (UStable U) :=
  inferInstanceAs (Fintype { S // S ∈ U.stable })

instance (U : SearchUniverse sig) : Finite (UPos U) := inferInstance
instance (U : SearchUniverse sig) : Finite (UNeg U) := inferInstance
instance (U : SearchUniverse sig) : Finite (UStable U) := inferInstance

abbrev BoundedSearchCtx (U : SearchUniverse sig) : Type :=
  Finset (UStable U × SearchProv)

instance : Fintype SearchProv :=
  Fintype.ofEquiv (Bool × Bool)
    { toFun := fun ⟨o, c⟩ => ⟨o, c⟩
      invFun := fun p => (p.outerNew, p.currentNew)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance (U : SearchUniverse sig) : DecidableEq (BoundedSearchCtx U) := inferInstance
instance (U : SearchUniverse sig) : Fintype (BoundedSearchCtx U) := inferInstance
instance (U : SearchUniverse sig) : Finite (BoundedSearchCtx U) := inferInstance

/-! ### Fixtures -/

namespace SearchUniverseFixtures

def sig0 : Signature := ⟨0, #[]⟩
def X : Pos 0 := .zero
def zTy : StableTy 0 := .neg (.prod (.shift X) (.shift X))
def Γz : StableCtx sig0 := .snoc .empty zTy
def Uz : SearchUniverse sig0 :=
  SearchUniverse.fromInputs Γz .empty (.pos (.zero : Pos 0)) []

theorem prod_shift_puts_X_and_negs :
    (X ∈ Uz.pos) ∧
      (Neg.prod (.shift X) (.shift X) ∈ Uz.neg) ∧
      (Neg.shift X ∈ Uz.neg) := by
  native_decide

theorem original_stable_retained : zTy ∈ Uz.stable := by
  native_decide

def arrTy : Neg 0 := .arr (.sum X (.shift .one)) (.shift X)
def Uarr : SearchUniverse sig0 :=
  SearchUniverse.fromInputs .empty .empty (.neg arrTy) []

theorem function_closure_includes_dom_cod :
    (Pos.sum X (.shift .one) ∈ Uarr.pos) ∧
      (Neg.shift X ∈ Uarr.neg) ∧
      (arrTy ∈ Uarr.neg) := by
  native_decide

theorem duplicate_dedup : Uz.neg.card = 2 := by
  native_decide

theorem finite_instances_executable :
    Fintype.card (UPos Uz) = Uz.pos.card ∧
      Fintype.card (UNeg Uz) = Uz.neg.card ∧
      Fintype.card (UStable Uz) = Uz.stable.card := by
  native_decide

theorem bounded_ctx_fintype_executable :
    Fintype.card (BoundedSearchCtx Uz) =
      2 ^ (Uz.stable.card * Fintype.card SearchProv) := by
  native_decide

theorem pos_eq_uplus :
    Uz.pos = UPlus.fromInputs Γz .empty (.pos (.zero : Pos 0)) [] :=
  SearchUniverse.pos_fromInputs Γz .empty (.pos (.zero : Pos 0)) []

theorem closure_sum_children :
    X ∈ (Pos.sum X (.shift .one)).uPlus ∧
      Pos.shift (.one) ∈ (Pos.sum X (.shift .one)).uPlus := by
  constructor
  · exact mem_uPlus_sum_left (Q := .sum X (.shift .one)) (A := X) (B := .shift .one)
      (by native_decide)
  · exact mem_uPlus_sum_right (Q := .sum X (.shift .one)) (A := X) (B := .shift .one)
      (by native_decide)

theorem closure_pos_shift_neg :
    Neg.shift X ∈ (Pos.shift (.shift X)).uNeg :=
  mem_uPlus_shift_neg (Q := .shift (.shift X)) (M := .shift X) (by native_decide)

theorem closure_neg_prod_children :
    Neg.shift X ∈ (Neg.prod (.shift X) (.shift X)).uNeg :=
  mem_uNeg_prod_left (M := .prod (.shift X) (.shift X)) (A := .shift X) (B := .shift X)
    (by native_decide)

theorem closure_neg_arr_dom_cod :
    Pos.sum X (.shift .one) ∈ arrTy.uPlus ∧ Neg.shift X ∈ arrTy.uNeg := by
  constructor
  · exact mem_uNeg_arr_dom (M := arrTy) (P := .sum X (.shift .one)) (Cod := .shift X)
      (by native_decide)
  · exact mem_uNeg_arr_cod (M := arrTy) (P := .sum X (.shift .one)) (Cod := .shift X)
      (by native_decide)

theorem closure_neg_shift_pos :
    X ∈ (Neg.shift X).uPlus :=
  mem_uNeg_shift_pos (M := .shift X) (P := X) (by native_decide)

end SearchUniverseFixtures

end Gimbal.Equality.Scherer
