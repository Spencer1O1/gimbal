/-
  Effective context growth and branch-local recurrence boundaries.

  The boundary decision is made after proof-relevant representatives have
  already been capped into `Ctx2`: only strict retained growth resets the
  recurrence allowance.  Equal retained contexts spend one visit at the
  shared positive boundary key and reject its third occurrence.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Gimbal.Equality.Scherer.CountTwo

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Pointwise context growth -/

namespace Count2

/-- Remaining room in one capped counter. -/
def room : Count2 → Nat
  | .zero => 2
  | .one => 1
  | .two => 0

@[simp] theorem room_zero : room .zero = 2 := rfl
@[simp] theorem room_one : room .one = 1 := rfl
@[simp] theorem room_two : room .two = 0 := rfl

theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  cases a <;> cases b <;> simp_all [toNat]

theorem room_le_room_of_toNat_le {a b : Count2}
    (h : a.toNat ≤ b.toNat) : b.room ≤ a.room := by
  cases a <;> cases b <;> simp_all [toNat, room]

theorem room_lt_room_of_toNat_lt {a b : Count2}
    (h : a.toNat < b.toNat) : b.room < a.room := by
  cases a <;> cases b <;> simp_all [toNat, room]

end Count2

namespace Ctx2

variable {U : TypeUniverse sig}

/-- Pointwise monotonicity of retained type multiplicities. -/
def LE (before after : Ctx2 U) : Prop :=
  ∀ S, (before S).toNat ≤ (after S).toNat

/-- A genuine change after capping, not merely a nonempty raw delta. -/
def StrictGrow (before after : Ctx2 U) : Prop :=
  before.LE after ∧ before ≠ after

theorem le_refl (G : Ctx2 U) : G.LE G := fun _ => Nat.le_refl _

theorem le_trans {A B C : Ctx2 U} (hAB : A.LE B) (hBC : B.LE C) : A.LE C :=
  fun S => Nat.le_trans (hAB S) (hBC S)

theorem le_antisymm {A B : Ctx2 U} (hAB : A.LE B) (hBA : B.LE A) : A = B := by
  funext S
  apply Count2.toNat_injective
  exact Nat.le_antisymm (hAB S) (hBA S)

theorem le_insert (G : Ctx2 U) (S : ↥U.stable) : G.LE (G.insert S) := by
  intro T
  by_cases h : T = S
  · subst T
    cases hG : G S <;>
      simp [Ctx2.insert, hG, Count2.toNat, Count2.bump]
  · simp [insert_other G h]

theorem strictGrow_iff_exists_lt {before after : Ctx2 U}
    (mono : before.LE after) :
    before.StrictGrow after ↔
      ∃ S, (before S).toNat < (after S).toNat := by
  constructor
  · rintro ⟨_, hne⟩
    by_contra h
    apply hne
    apply le_antisymm mono
    intro S
    apply Nat.le_of_not_gt
    intro hlt
    exact h ⟨S, hlt⟩
  · rintro ⟨S, hlt⟩
    refine ⟨mono, ?_⟩
    intro heq
    subst after
    exact (Nat.lt_irrefl _ hlt)

end Ctx2

/-! ### Finite room potentials -/

/-- Total unfilled multiplicity slots in a capped context. -/
def ctxRoom {U : TypeUniverse sig} (G : Ctx2 U) : Nat :=
  ∑ S : ↥U.stable, (G S).room

/-- Total unspent recurrence visits over the finite key space. -/
def memoryRoom {U : TypeUniverse sig} (memo : VisitMemory U) : Nat :=
  ∑ k : MemoryKey U, (memo k).room

theorem ctxRoom_le_of_mono {U : TypeUniverse sig} {before after : Ctx2 U}
    (mono : before.LE after) : ctxRoom after ≤ ctxRoom before := by
  apply Finset.sum_le_sum
  intro S _
  exact Count2.room_le_room_of_toNat_le (mono S)

theorem ctxRoom_lt_of_grow {U : TypeUniverse sig} {before after : Ctx2 U}
    (grow : before.StrictGrow after) : ctxRoom after < ctxRoom before := by
  apply Finset.sum_lt_sum
  · intro S _
    exact Count2.room_le_room_of_toNat_le (grow.1 S)
  · obtain ⟨S, hS⟩ := (Ctx2.strictGrow_iff_exists_lt grow.1).mp grow
    exact ⟨S, Finset.mem_univ S,
      Count2.room_lt_room_of_toNat_lt hS⟩

theorem ctxRoom_insert_le {U : TypeUniverse sig} (G : Ctx2 U)
    (S : ↥U.stable) : ctxRoom (G.insert S) ≤ ctxRoom G :=
  ctxRoom_le_of_mono (Ctx2.le_insert G S)

theorem ctxRoom_insert_lt_of_not_two {U : TypeUniverse sig} (G : Ctx2 U)
    (S : ↥U.stable) (h : G S ≠ .two) :
    ctxRoom (G.insert S) < ctxRoom G := by
  apply ctxRoom_lt_of_grow
  refine ⟨Ctx2.le_insert G S, ?_⟩
  intro heq
  have hs := congrFun heq S
  cases hG : G S <;> simp [Ctx2.insert, hG, Count2.bump] at hs h

theorem memoryRoom_set_le {U : TypeUniverse sig} (memo : VisitMemory U)
    (k : MemoryKey U) (c : Count2)
    (h : (memo k).toNat ≤ c.toNat) :
    memoryRoom (memo.set k c) ≤ memoryRoom memo := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j = k
  · subst j
    simp only [VisitMemory.set_same]
    exact Count2.room_le_room_of_toNat_le h
  · rw [VisitMemory.set_other memo hj]

theorem memoryRoom_set_lt {U : TypeUniverse sig} (memo : VisitMemory U)
    (k : MemoryKey U) (c : Count2)
    (h : (memo k).toNat < c.toNat) :
    memoryRoom (memo.set k c) < memoryRoom memo := by
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : j = k
    · subst j
      simp only [VisitMemory.set_same]
      exact Count2.room_le_room_of_toNat_le (Nat.le_of_lt h)
    · rw [VisitMemory.set_other memo hj]
  · exact ⟨k, Finset.mem_univ k, by
      simp only [VisitMemory.set_same]
      exact Count2.room_lt_room_of_toNat_lt h⟩

theorem memoryRoom_lt_of_visitEmpty {U : TypeUniverse sig}
    {memo memo' : VisitMemory U} {k : MemoryKey U}
    (h : memo.visitEmpty k = some memo') :
    memoryRoom memo' < memoryRoom memo := by
  cases hk : memo k with
  | zero =>
      simp [VisitMemory.visitEmpty, hk] at h
      subst memo'
      apply memoryRoom_set_lt
      simp [hk, Count2.toNat]
  | one =>
      simp [VisitMemory.visitEmpty, hk] at h
      subst memo'
      apply memoryRoom_set_lt
      simp [hk, Count2.toNat]
  | two => simp [VisitMemory.visitEmpty, hk] at h

/-! ### Effective boundary entry -/

/-- A positive formula certified to lie in the supplied finite universe. -/
abbrev BoundedPos (U : TypeUniverse sig) := {P // P ∈ U.positive}

namespace MemoryKey

def ofPos {U : TypeUniverse sig} (G : Ctx2 U) (P : BoundedPos U) :
    MemoryKey U :=
  ⟨G, ⟨.pos P.1, TypeUniverse.pos_mem_goals P.2⟩⟩

end MemoryKey

/--
Enter a positive saturation boundary after capping representatives into
`after`. Strict effective growth leaves branch-local memory untouched; equal
retained contexts spend one count-two visit at `(after, pos P)`.
-/
def enterBoundary {U : TypeUniverse sig}
    (before after : Ctx2 U) (_mono : before.LE after)
    (P : BoundedPos U) (memo : VisitMemory U) : Option (VisitMemory U) :=
  if before = after then
    memo.visitEmpty (MemoryKey.ofPos after P)
  else
    some memo

theorem enterBoundary_of_strictGrow {U : TypeUniverse sig}
    {before after : Ctx2 U} (grow : before.StrictGrow after)
    (P : BoundedPos U) (memo : VisitMemory U) :
    enterBoundary before after grow.1 P memo = some memo := by
  simp [enterBoundary, grow.2]

theorem enterBoundary_eq_zero {U : TypeUniverse sig}
    {before after : Ctx2 U} (mono : before.LE after) (P : BoundedPos U)
    (memo : VisitMemory U) (heq : before = after)
    (hzero : memo (MemoryKey.ofPos after P) = .zero) :
    enterBoundary before after mono P memo =
      some (memo.set (MemoryKey.ofPos after P) .one) := by
  simp [enterBoundary, heq, VisitMemory.visitEmpty, hzero]

theorem enterBoundary_eq_one {U : TypeUniverse sig}
    {before after : Ctx2 U} (mono : before.LE after) (P : BoundedPos U)
    (memo : VisitMemory U) (heq : before = after)
    (hone : memo (MemoryKey.ofPos after P) = .one) :
    enterBoundary before after mono P memo =
      some (memo.set (MemoryKey.ofPos after P) .two) := by
  simp [enterBoundary, heq, VisitMemory.visitEmpty, hone]

theorem enterBoundary_eq_two {U : TypeUniverse sig}
    {before after : Ctx2 U} (mono : before.LE after) (P : BoundedPos U)
    (memo : VisitMemory U) (heq : before = after)
    (htwo : memo (MemoryKey.ofPos after P) = .two) :
    enterBoundary before after mono P memo = none := by
  simp [enterBoundary, heq, VisitMemory.visitEmpty, htwo]

theorem enterBoundary_eq_none_iff {U : TypeUniverse sig}
    {before after : Ctx2 U} (mono : before.LE after) (P : BoundedPos U)
    (memo : VisitMemory U) :
    enterBoundary before after mono P memo = none ↔
      before = after ∧ memo (MemoryKey.ofPos after P) = .two := by
  by_cases heq : before = after
  · simp [enterBoundary, heq, VisitMemory.visitEmpty_eq_none_iff]
  · simp [enterBoundary, heq]

theorem enterBoundary_preserves_other_keys {U : TypeUniverse sig}
    {before after : Ctx2 U} (mono : before.LE after) (P : BoundedPos U)
    {memo memo' : VisitMemory U}
    (henter : enterBoundary before after mono P memo = some memo')
    {j : MemoryKey U} (hne : j ≠ MemoryKey.ofPos after P) :
    memo' j = memo j := by
  by_cases heq : before = after
  · cases hk : memo (MemoryKey.ofPos after P) with
    | zero =>
        simp [enterBoundary, heq, VisitMemory.visitEmpty, hk] at henter
        subst memo'
        exact VisitMemory.set_other memo hne .one
    | one =>
        simp [enterBoundary, heq, VisitMemory.visitEmpty, hk] at henter
        subst memo'
        exact VisitMemory.set_other memo hne .two
    | two => simp [enterBoundary, heq, VisitMemory.visitEmpty, hk] at henter
  · simp [enterBoundary, heq] at henter
    subst memo'
    rfl

theorem memoryRoom_lt_of_eq {U : TypeUniverse sig}
    {before after : Ctx2 U} (mono : before.LE after) (P : BoundedPos U)
    {memo memo' : VisitMemory U} (heq : before = after)
    (henter : enterBoundary before after mono P memo = some memo') :
    memoryRoom memo' < memoryRoom memo := by
  subst before
  simp only [enterBoundary] at henter
  exact memoryRoom_lt_of_visitEmpty henter

def boundaryMeasure {U : TypeUniverse sig} (G : Ctx2 U)
    (memo : VisitMemory U) : Nat × Nat :=
  (ctxRoom G, memoryRoom memo)

theorem enterBoundary_decreases {U : TypeUniverse sig}
    {before after : Ctx2 U} (mono : before.LE after) (P : BoundedPos U)
    {memo memo' : VisitMemory U}
    (henter : enterBoundary before after mono P memo = some memo') :
    Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (boundaryMeasure after memo') (boundaryMeasure before memo) := by
  by_cases heq : before = after
  · subst before
    apply Prod.Lex.right
    exact memoryRoom_lt_of_eq mono P rfl henter
  · apply Prod.Lex.left
    exact ctxRoom_lt_of_grow ⟨mono, heq⟩

/-! ### Boundary regressions -/

namespace SearchBoundaryFixtures

abbrev sig1 : Signature := ⟨1, #[]⟩
abbrev q : Fin sig1.nBases := ⟨0, Nat.zero_lt_one⟩
abbrev X : Pos sig1.nBases := .atom q
abbrev AtomS : StableTy sig1.nBases := .atom q

def U : TypeUniverse sig1 where
  positive := {X}
  stable := {AtomS}

theorem atomMem : AtomS ∈ U.stable := by simp [U]
theorem posMem : X ∈ U.positive := by simp [U]
def atomSlot : ↥U.stable := ⟨AtomS, atomMem⟩
def pos : BoundedPos U := ⟨X, posMem⟩

theorem uniqueSlot (S : ↥U.stable) : S = atomSlot := by
  have hmem := S.2
  change S.1 ∈ ({AtomS} : Finset (StableTy sig1.nBases)) at hmem
  apply Subtype.ext
  exact Finset.mem_singleton.mp hmem

abbrev Rep := Fin 3

def oneBucket : (S : ↥U.stable) → Plur Rep :=
  fun _ => Plur.singleton 0

def twoBucket : (S : ↥U.stable) → Plur Rep :=
  fun _ => Plur.insert 1 (Plur.singleton 0)

def thirdRawBucket : (S : ↥U.stable) → Plur Rep :=
  fun _ => Plur.insert 2 (Plur.insert 1 (Plur.singleton 0))

def duplicateBucket : (S : ↥U.stable) → Plur Rep :=
  fun _ => Plur.insert 0 (Plur.singleton 0)

def oneCtx : Ctx2 U := Ctx2.ofPlur oneBucket
def twoCtx : Ctx2 U := Ctx2.ofPlur twoBucket
def thirdRawCtx : Ctx2 U := Ctx2.ofPlur thirdRawBucket
def duplicateCtx : Ctx2 U := Ctx2.ofPlur duplicateBucket

theorem third_raw_capped_context_eq : thirdRawCtx = twoCtx := by native_decide
theorem duplicate_context_eq : duplicateCtx = oneCtx := by native_decide
theorem one_le_two : oneCtx.LE twoCtx := by
  intro S
  rw [uniqueSlot S]
  native_decide

theorem one_strictGrow_two : oneCtx.StrictGrow twoCtx := by
  refine ⟨one_le_two, ?_⟩
  intro h
  have hs := congrFun h atomSlot
  have hne : oneCtx atomSlot ≠ twoCtx atomSlot := by native_decide
  exact hne hs

theorem two_le_thirdRaw : twoCtx.LE thirdRawCtx := by
  rw [third_raw_capped_context_eq]
  exact Ctx2.le_refl _

theorem one_le_duplicate : oneCtx.LE duplicateCtx := by
  rw [duplicate_context_eq]
  exact Ctx2.le_refl _

def twoKey : MemoryKey U := MemoryKey.ofPos twoCtx pos
def oneKey : MemoryKey U := MemoryKey.ofPos oneCtx pos
def seenOnceTwo : VisitMemory U := VisitMemory.set VisitMemory.empty twoKey .one
def seenOnceOne : VisitMemory U := VisitMemory.set VisitMemory.empty oneKey .one
def seenTwiceTwo : VisitMemory U := VisitMemory.set VisitMemory.empty twoKey .two

/-- A raw third representative is capped away, so equality spends a visit. -/
theorem raw_nonempty_third_capped_visits :
    enterBoundary twoCtx thirdRawCtx two_le_thirdRaw pos seenOnceTwo =
      some (seenOnceTwo.set (MemoryKey.ofPos thirdRawCtx pos) .two) := by
  apply enterBoundary_eq_one
  · exact Eq.symm third_raw_capped_context_eq
  · native_decide

/-- A retained second representative is strict growth and spends nothing. -/
theorem second_distinct_grows_without_visit :
    enterBoundary oneCtx twoCtx one_le_two pos seenTwiceTwo = some seenTwiceTwo :=
  enterBoundary_of_strictGrow one_strictGrow_two pos seenTwiceTwo

/-- Re-inserting the same representative leaves `Ctx2` equal and spends. -/
theorem duplicate_same_representative_visits :
    enterBoundary oneCtx duplicateCtx one_le_duplicate pos seenOnceOne =
      some (seenOnceOne.set (MemoryKey.ofPos duplicateCtx pos) .two) := by
  apply enterBoundary_eq_one
  · exact duplicate_context_eq.symm
  · native_decide

theorem sibling_boundaries_independent :
    ∃ left right,
      enterBoundary oneCtx duplicateCtx one_le_duplicate pos seenOnceOne = some left ∧
      enterBoundary oneCtx duplicateCtx one_le_duplicate pos seenOnceOne = some right := by
  let next := seenOnceOne.set (MemoryKey.ofPos duplicateCtx pos) .two
  exact ⟨next, next, duplicate_same_representative_visits,
    duplicate_same_representative_visits⟩

def satPosKey : MemoryKey U := MemoryKey.ofPos twoCtx pos
def satShiftKey : MemoryKey U := MemoryKey.ofPos twoCtx pos

theorem satPos_satShift_share_pos_key : satPosKey = satShiftKey := rfl

end SearchBoundaryFixtures

end Gimbal.Equality.Scherer
