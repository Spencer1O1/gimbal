/-
  Finite normalized queries for the Scherer-core search.

  A normalized frame contracts only identical full labels. Stable type,
  resolved dependency support, and both provenance bits remain observable.
  `ResolvedState` does not remember outer-new provenance, so projection takes
  that information explicitly rather than reconstructing it heuristically.

  This module proves only finite enumeration and branch counting. It makes no
  contraction/splice, materialization, capacity-adequacy, selection-policy, or
  S4 claim.
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Nodup
import Gimbal.Equality.Scherer.CanonicalEnum
import Gimbal.Equality.Scherer.SearchObligation
import Gimbal.Equality.Scherer.SaturatedRenameFacts

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Finite frame labels -/

/-- Exact stable type, resolved support, and outer/current provenance. -/
abbrev FrameLabel (U : SearchUniverse sig) (O : Type) : Type :=
  UStable U × DepSupport O × SearchProv

instance {U : SearchUniverse sig} {O : Type} [DecidableEq O] :
    DecidableEq (FrameLabel U O) := inferInstance

/-- A normalized frame contracts duplicates of the complete label only. -/
abbrev ContractedFrame (U : SearchUniverse sig) (O : Type) : Type :=
  Finset (FrameLabel U O)

/--
Explicit carrier order required for runtime enumeration. `SearchUniverse`
stores finsets, whose quotient representation has no executable `toList`, so
the order is supplied rather than recovered noncomputably.
-/
structure QueryCarrierEnum (U : SearchUniverse sig) (O : Type) where
  stable : CanonicalEnum (UStable U)
  positive : CanonicalEnum (UPos U)
  origins : CanonicalEnum O

/-- The canonical four two-bit provenance labels. -/
def searchProvEnum : CanonicalEnum SearchProv where
  elems := [⟨false, false⟩, ⟨false, true⟩, ⟨true, false⟩, ⟨true, true⟩]
  nodup := by decide
  complete p := by
    rcases p with ⟨o, c⟩
    cases o <;> cases c <;> simp

@[simp] theorem searchProvEnum_length : searchProvEnum.elems.length = 4 := rfl

/-- Explicit powerset enumeration of resolved supports. -/
def depSupportEnum {O : Type} [DecidableEq O]
    (origins : CanonicalEnum O) : CanonicalEnum (DepSupport O) :=
  CanonicalEnum.finsets origins

@[simp] theorem depSupportEnum_length {O : Type} [DecidableEq O]
    (origins : CanonicalEnum O) :
    (depSupportEnum origins).elems.length = 2 ^ origins.elems.length := by
  simp [depSupportEnum]

/-- Explicit componentwise enumeration of exact frame labels. -/
def frameLabelEnum {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    (carriers : QueryCarrierEnum U O) : CanonicalEnum (FrameLabel U O) :=
  CanonicalEnum.prod carriers.stable
    (CanonicalEnum.prod (depSupportEnum carriers.origins) searchProvEnum)

/-- Exact number of possible frame labels. -/
def frameLabelCard {U : SearchUniverse sig} {O : Type}
    (carriers : QueryCarrierEnum U O) : Nat :=
  carriers.stable.elems.length * 2 ^ carriers.origins.elems.length * 4

@[simp] theorem frameLabelEnum_length {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] (carriers : QueryCarrierEnum U O) :
    (frameLabelEnum carriers).elems.length = frameLabelCard carriers := by
  simp [frameLabelEnum, frameLabelCard, Nat.mul_assoc]

/-- The finite carrier of all exact frame labels. -/
def allFrameLabels {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    (carriers : QueryCarrierEnum U O) : Finset (FrameLabel U O) :=
  (frameLabelEnum carriers).elems.toFinset

@[simp] theorem mem_allFrameLabels {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] (carriers : QueryCarrierEnum U O) (label : FrameLabel U O) :
    label ∈ allFrameLabels carriers := by
  simp [allFrameLabels, CanonicalEnum.complete]

@[simp] theorem allFrameLabels_card {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] (carriers : QueryCarrierEnum U O) :
    (allFrameLabels carriers).card = frameLabelCard carriers := by
  rw [allFrameLabels, List.toFinset_card_of_nodup (frameLabelEnum carriers).nodup]
  exact frameLabelEnum_length carriers

/-- Explicit enumeration of every contracted frame. -/
def contractedFrameEnum {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    (carriers : QueryCarrierEnum U O) : CanonicalEnum (ContractedFrame U O) :=
  CanonicalEnum.finsets (frameLabelEnum carriers)

@[simp] theorem contractedFrameEnum_length {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] (carriers : QueryCarrierEnum U O) :
    (contractedFrameEnum carriers).elems.length =
      2 ^ frameLabelCard carriers := by
  simp [contractedFrameEnum]

/-! ### Exact state projection with explicit outer provenance -/

/-- Outer provenance absent from `ResolvedState`, supplied explicitly. -/
structure RealizedFrameInput {U : SearchUniverse sig} {O : Type} {B : Nat}
    (st : ResolvedState U O B) where
  outerNewAt : Fin st.depth → Bool

namespace ResolvedState

variable {U : SearchUniverse sig} {O : Type} {B : Nat}

/-- Exact label of one live level under an explicit outer-provenance input. -/
def frameLabelAt (st : ResolvedState U O B) (input : RealizedFrameInput st)
    (i : Fin st.depth) : FrameLabel U O :=
  (st.tyAt i, st.depAt i,
    ⟨input.outerNewAt i, decide (i ∈ st.currentRaw)⟩)

/-- Contract the finite live levels by equality of their complete labels. -/
def contractedFrame (st : ResolvedState U O B)
    [DecidableEq O]
    (input : RealizedFrameInput st) : ContractedFrame U O :=
  Finset.univ.image (st.frameLabelAt input)

theorem mem_contractedFrame_iff (st : ResolvedState U O B)
    [DecidableEq O]
    (input : RealizedFrameInput st) (label : FrameLabel U O) :
    label ∈ st.contractedFrame input ↔
      ∃ i : Fin st.depth, st.frameLabelAt input i = label := by
  simp [contractedFrame]

theorem contractedFrame_current_exact (st : ResolvedState U O B)
    (input : RealizedFrameInput st) (i : Fin st.depth) :
    (st.frameLabelAt input i).2.2.currentNew = decide (i ∈ st.currentRaw) := rfl

theorem contractedFrame_outer_exact (st : ResolvedState U O B)
    (input : RealizedFrameInput st) (i : Fin st.depth) :
    (st.frameLabelAt input i).2.2.outerNew = input.outerNewAt i := rfl

end ResolvedState

/-! ### Normal queries and their explicit finite enumeration -/

/-- The canonical four result-usage signatures. -/
def useSigEnum : CanonicalEnum UseSig where
  elems := [⟨false, false⟩, ⟨false, true⟩, ⟨true, false⟩, ⟨true, true⟩]
  nodup := by decide
  complete u := by
    rcases u with ⟨o, c⟩
    cases o <;> cases c <;> simp

@[simp] theorem useSigEnum_length : useSigEnum.elems.length = 4 := rfl

/-- Normalized availability, exact consumed obligations, and target obligation. -/
structure NormalQuery (U : SearchUniverse sig) (O : Type) where
  frame : ContractedFrame U O
  coverage : Finset (Obligation U O)
  target : Obligation U O
  useSig : UseSig
  deriving DecidableEq

namespace NormalQuery

variable {U : SearchUniverse sig} {O : Type}

abbrev Code (U : SearchUniverse sig) (O : Type) :=
  ContractedFrame U O × Finset (Obligation U O) × Obligation U O × UseSig

def equivCode [DecidableEq O] : NormalQuery U O ≃ Code U O where
  toFun q := (q.frame, q.coverage, q.target, q.useSig)
  invFun c := ⟨c.1, c.2.1, c.2.2.1, c.2.2.2⟩
  left_inv q := by cases q; rfl
  right_inv c := by cases c; rfl

end NormalQuery

/-- Explicit exact-obligation enumeration. -/
def obligationEnum {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    (carriers : QueryCarrierEnum U O) : CanonicalEnum (Obligation U O) :=
  CanonicalEnum.mapEquiv
    (CanonicalEnum.prod carriers.positive (depSupportEnum carriers.origins))
    Obligation.equivProd.symm

/-- Exact number of obligations under the explicit origin carrier. -/
def obligationCard {U : SearchUniverse sig} {O : Type}
    (carriers : QueryCarrierEnum U O) : Nat :=
  carriers.positive.elems.length * 2 ^ carriers.origins.elems.length

@[simp] theorem obligationEnum_length {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] (carriers : QueryCarrierEnum U O) :
    (obligationEnum carriers).elems.length = obligationCard carriers := by
  simp [obligationEnum, obligationCard]

/-- Explicit enumeration of all normalized queries; no `Fintype.toList`. -/
def normalQueryEnum {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    (carriers : QueryCarrierEnum U O) : CanonicalEnum (NormalQuery U O) :=
  CanonicalEnum.mapEquiv
    (CanonicalEnum.prod (contractedFrameEnum carriers)
      (CanonicalEnum.prod
        (CanonicalEnum.finsets (obligationEnum carriers))
        (CanonicalEnum.prod (obligationEnum carriers) useSigEnum)))
    NormalQuery.equivCode.symm

/-- Exact finite bound (indeed cardinality) for normalized queries. -/
def normalQueryBound {U : SearchUniverse sig} {O : Type}
    (carriers : QueryCarrierEnum U O) : Nat :=
  obligationCard carriers *
    2 ^ (frameLabelCard carriers + obligationCard carriers) * 4

/-- The constructive enumeration has exactly the advertised bound. -/
@[simp] theorem normalQueryEnum_length {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] (carriers : QueryCarrierEnum U O) :
    (normalQueryEnum carriers).elems.length = normalQueryBound carriers := by
  simp [normalQueryEnum, normalQueryBound, Nat.pow_add, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc]

/-- Constructive enumeration completeness. -/
theorem normalQueryEnum_complete {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] (carriers : QueryCarrierEnum U O) (q : NormalQuery U O) :
    q ∈ (normalQueryEnum carriers).elems :=
  (normalQueryEnum carriers).complete q

/-- Constructive enumeration has no duplicate normalized queries. -/
theorem normalQueryEnum_nodup {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] (carriers : QueryCarrierEnum U O) :
    (normalQueryEnum carriers).elems.Nodup :=
  (normalQueryEnum carriers).nodup

/-- The explicit normal-query list as a computable finite set. -/
def allNormalQueries {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    (carriers : QueryCarrierEnum U O) : Finset (NormalQuery U O) :=
  (normalQueryEnum carriers).elems.toFinset

@[simp] theorem mem_allNormalQueries {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] (carriers : QueryCarrierEnum U O) (q : NormalQuery U O) :
    q ∈ allNormalQueries carriers := by
  exact List.mem_toFinset.mpr (normalQueryEnum_complete carriers q)

/-- Exact cardinality, hence the requested upper bound as an equality. -/
theorem allNormalQueries_card {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] (carriers : QueryCarrierEnum U O) :
    (allNormalQueries carriers).card = normalQueryBound carriers := by
  rw [allNormalQueries, List.toFinset_card_of_nodup
    (normalQueryEnum_nodup carriers)]
  exact normalQueryEnum_length carriers

theorem allNormalQueries_card_le {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] (carriers : QueryCarrierEnum U O) :
    (allNormalQueries carriers).card ≤ normalQueryBound carriers :=
  (allNormalQueries_card carriers).le

/--
A resolved query with explicit outer-provenance realization, which the state
does not itself retain.
-/
structure ResolvedQuery (U : SearchUniverse sig) (O : Type) (B : Nat) where
  state : ResolvedState U O B
  realizedFrame : RealizedFrameInput state
  coverage : Finset (Obligation U O)
  target : Obligation U O
  useSig : UseSig

/-- Exact computable projection from a realized resolved query. -/
def ResolvedQuery.normalize {U : SearchUniverse sig} {O : Type} {B : Nat}
    [DecidableEq O] (q : ResolvedQuery U O B) : NormalQuery U O :=
  ⟨q.state.contractedFrame q.realizedFrame, q.coverage, q.target, q.useSig⟩

@[simp] theorem ResolvedQuery.normalize_frame {U : SearchUniverse sig}
    {O : Type} {B : Nat} [DecidableEq O] (q : ResolvedQuery U O B) :
    q.normalize.frame = q.state.contractedFrame q.realizedFrame := rfl

@[simp] theorem ResolvedQuery.normalize_coverage {U : SearchUniverse sig}
    {O : Type} {B : Nat} [DecidableEq O] (q : ResolvedQuery U O B) :
    q.normalize.coverage = q.coverage := rfl

@[simp] theorem ResolvedQuery.normalize_target {U : SearchUniverse sig}
    {O : Type} {B : Nat} [DecidableEq O] (q : ResolvedQuery U O B) :
    q.normalize.target = q.target := rfl

@[simp] theorem ResolvedQuery.normalize_useSig {U : SearchUniverse sig}
    {O : Type} {B : Nat} [DecidableEq O] (q : ResolvedQuery U O B) :
    q.normalize.useSig = q.useSig := rfl

/-! ### Regression fixtures -/

namespace SearchNormalQueryFixtures

open SearchUniverseFixtures

abbrev O3 := Fin 3
instance : DecidableEq O3 := inferInstanceAs (DecidableEq (Fin 3))

def fOrigin : O3 := ⟨0, by decide⟩
def gOrigin : O3 := ⟨1, by decide⟩
def zOrigin : O3 := ⟨2, by decide⟩

def origins3 : CanonicalEnum O3 where
  elems := [fOrigin, gOrigin, zOrigin]
  nodup := by decide
  complete x := by
    rcases x with ⟨n, hn⟩
    have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp [fOrigin, gOrigin, zOrigin]

def P0 : UPos Uz := ⟨X, by native_decide⟩
def S0 : UStable Uz := ⟨zTy, by native_decide⟩

def oldLabel : FrameLabel Uz O3 :=
  (S0, {fOrigin}, ⟨false, false⟩)

def newLabel : FrameLabel Uz O3 :=
  (S0, {fOrigin}, ⟨true, true⟩)

def resetLabel : FrameLabel Uz O3 :=
  (S0, {fOrigin}, ⟨true, false⟩)

theorem old_new_same_type_remain_distinct : oldLabel ≠ newLabel := by
  decide

theorem same_type_support_different_current_distinct :
    newLabel ≠ resetLabel := by
  decide

theorem identical_labels_contract :
    ({oldLabel, oldLabel} : ContractedFrame Uz O3) = {oldLabel} := by
  simp

def target0 : Obligation Uz O3 := ⟨P0, {fOrigin}⟩

def queryCurrentOnly : NormalQuery Uz O3 :=
  ⟨{oldLabel}, ∅, target0, ⟨false, true⟩⟩

def queryOuterCurrent : NormalQuery Uz O3 :=
  ⟨{oldLabel}, ∅, target0, ⟨true, true⟩⟩

/-- Same frame/coverage/target does not contract different result usage. -/
theorem same_shape_different_useSig_distinct :
    queryCurrentOnly ≠ queryOuterCurrent := by
  decide

/-- Named outer/inner shapes from the `f/g/z` counterexample remain distinct. -/
def fOuter : FrameLabel Uz O3 :=
  (S0, {fOrigin}, ⟨true, false⟩)
def gInner : FrameLabel Uz O3 :=
  (S0, {fOrigin, gOrigin}, ⟨false, true⟩)
def zInner : FrameLabel Uz O3 :=
  (S0, {zOrigin}, ⟨false, true⟩)

theorem fgz_outer_inner_shapes_distinct :
    fOuter ≠ gInner ∧ fOuter ≠ zInner ∧ gInner ≠ zInner := by
  decide

/-- One repeated identical live occurrence contracts to the stabilized frame. -/
def stOne : ResolvedState Uz O3 2 :=
  (ResolvedState.empty Uz O3 2).pushResolved (by decide) S0 {fOrigin}

def stTwo : ResolvedState Uz O3 2 :=
  stOne.pushResolved (by decide) S0 {fOrigin}

def realizedOne : RealizedFrameInput stOne := ⟨fun _ => true⟩
def realizedTwo : RealizedFrameInput stTwo := ⟨fun _ => true⟩

theorem stabilized_repeated_frame_projects_equal :
    stOne.contractedFrame realizedOne = stTwo.contractedFrame realizedTwo := by
  native_decide

theorem pair_common_frame_union_commutative
    (left right : ContractedFrame Uz O3) :
    left ∪ right = right ∪ left :=
  Finset.union_comm _ _

end SearchNormalQueryFixtures

end Gimbal.Equality.Scherer
