/-
  Scherer-core structural search alternatives (support-aware).

  Enumerates exact finite structural dependency alternatives for non-saturation
  search keys. Saturation parents have an empty structural alternative set;
  batch/empty certificates are deferred.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Gimbal.Equality.Scherer.SearchKey

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Finite dependency bundles -/

/-- At most two ordered dependency occurrences (siblings may be identical). -/
inductive DepBundle (K : Type) where
  | none
  | one : K → DepBundle K
  | two : K → K → DepBundle K
  deriving DecidableEq

namespace DepBundle

variable {K : Type}

def toList : DepBundle K → List K
  | .none => []
  | .one k => [k]
  | .two k₁ k₂ => [k₁, k₂]

@[simp] theorem toList_none : toList (.none : DepBundle K) = [] := rfl
@[simp] theorem toList_one (k : K) : toList (.one k) = [k] := rfl
@[simp] theorem toList_two (k₁ k₂ : K) : toList (.two k₁ k₂) = [k₁, k₂] := rfl

theorem length_le_two (d : DepBundle K) : d.toList.length ≤ 2 := by
  cases d <;> simp [toList]

abbrev Code (K : Type) : Type := PUnit ⊕ K ⊕ (K × K)

def ofCode : Code K → DepBundle K
  | .inl _ => .none
  | .inr (.inl k) => .one k
  | .inr (.inr ⟨k₁, k₂⟩) => .two k₁ k₂

def toCode : DepBundle K → Code K
  | .none => .inl ⟨⟩
  | .one k => .inr (.inl k)
  | .two k₁ k₂ => .inr (.inr ⟨k₁, k₂⟩)

@[simp] theorem ofCode_toCode (d : DepBundle K) : ofCode (toCode d) = d := by
  cases d <;> rfl

instance [Fintype K] [DecidableEq K] : Fintype (DepBundle K) :=
  Fintype.ofSurjective ofCode fun d => ⟨toCode d, ofCode_toCode d⟩

instance [Finite K] : Finite (DepBundle K) := by
  letI := Fintype.ofFinite K
  letI : DecidableEq K := Classical.decEq K
  infer_instance

end DepBundle

/-! ### Structural tags (no Sat.done / Sat.batch) -/

inductive StructuralTag where
  | var | fst | snd | app
  | atom | inl | inr | shift
  | caseSum | abort | storeAtom | storeShift
  | unit | pair | lam | satShift | satPos
  deriving DecidableEq, Repr

def StructuralTag.enum : List StructuralTag :=
  [.var, .fst, .snd, .app, .atom, .inl, .inr, .shift,
   .caseSum, .abort, .storeAtom, .storeShift,
   .unit, .pair, .lam, .satShift, .satPos]

instance : Fintype StructuralTag where
  elems :=
    {.var, .fst, .snd, .app, .atom, .inl, .inr, .shift,
     .caseSum, .abort, .storeAtom, .storeShift,
     .unit, .pair, .lam, .satShift, .satPos}
  complete := by intro x; cases x <;> simp

instance : Finite StructuralTag := inferInstance

/-! ### Raw helpers -/

namespace ResolvedState

variable {U : SearchUniverse sig} {O : Type} {B : Nat}

def popRaw (st : ResolvedState U O B) (_h : st.depth < B)
    (raw : Finset (Fin (st.depth + 1))) : Finset (Fin st.depth) :=
  (Finset.univ : Finset (Fin st.depth)).filter fun i => i.castSucc ∈ raw

@[simp] theorem mem_popRaw (st : ResolvedState U O B) (h : st.depth < B)
    (raw : Finset (Fin (st.depth + 1))) (i : Fin st.depth) :
    i ∈ st.popRaw h raw ↔ i.castSucc ∈ raw := by
  simp [popRaw]

end ResolvedState

namespace Structural

variable {U : SearchUniverse sig} {O : Type} {B L : Nat}
variable [DecidableEq O]

def sameStateCoverage (p c : SearchKey U O B L) : Bool :=
  decide (c.state = p.state) && decide (c.coverage = p.coverage)

def sameFrame (p c : SearchKey U O B L) : Bool :=
  sameStateCoverage p c &&
    decide (rawVals c.rawSupport = rawVals p.rawSupport) &&
      decide (c.depSupport = p.depSupport)

def unionRaw (p c₁ c₂ : SearchKey U O B L) : Bool :=
  decide (rawVals p.rawSupport = rawVals c₁.rawSupport ∪ rawVals c₂.rawSupport)

def unionDep (p c₁ c₂ : SearchKey U O B L) : Bool :=
  decide (p.depSupport = c₁.depSupport ∪ c₂.depSupport)

/-- Exact structural validity (executable Bool). -/
def structuralValidB (parent : SearchKey U O B L)
    (tag : StructuralTag) (deps : DepBundle (SearchKey U O B L)) : Bool :=
  match parent.judgment with
  | .sat _ => false
  | j =>
    match tag, deps with
    | .var, .none =>
        match j with
        | .sNeg N =>
            decide (∃ i : Fin parent.state.depth,
              (parent.state.tyAt i).val = .neg N.val ∧
                parent.rawSupport = ({i} : Finset _) ∧
                  parent.depSupport = parent.state.depAt i)
        | _ => false
    | .fst, .one c =>
        match j, c.judgment with
        | .sNeg A, .sNeg P =>
            (match P.val with
             | .prod A' _ => decide (A' = A.val)
             | _ => false) && sameFrame parent c
        | _, _ => false
    | .snd, .one c =>
        match j, c.judgment with
        | .sNeg B, .sNeg P =>
            (match P.val with
             | .prod _ B' => decide (B' = B.val)
             | _ => false) && sameFrame parent c
        | _, _ => false
    | .app, .two c₁ c₂ =>
        match j, c₁.judgment, c₂.judgment with
        | .sNeg N, .sNeg Arr, .sPos P =>
            (match Arr.val with
             | .arr P' N' => decide (P' = P.val ∧ N' = N.val)
             | _ => false) &&
              sameStateCoverage parent c₁ && sameStateCoverage parent c₂ &&
                unionRaw parent c₁ c₂ && unionDep parent c₁ c₂
        | _, _, _ => false
    | .atom, .none =>
        match j with
        | .sPos P =>
            match P.val with
            | .atom q =>
                decide (∃ i : Fin parent.state.depth,
                  (parent.state.tyAt i).val = .atom q ∧
                    parent.rawSupport = ({i} : Finset _) ∧
                      parent.depSupport = parent.state.depAt i)
            | _ => false
        | _ => false
    | .inl, .one c =>
        match j, c.judgment with
        | .sPos S, .sPos A =>
            (match S.val with
             | .sum A' _ => decide (A' = A.val)
             | _ => false) && sameFrame parent c
        | _, _ => false
    | .inr, .one c =>
        match j, c.judgment with
        | .sPos S, .sPos B =>
            (match S.val with
             | .sum _ B' => decide (B' = B.val)
             | _ => false) && sameFrame parent c
        | _, _ => false
    | .shift, .one c =>
        match j, c.judgment with
        | .sPos Sp, .sInv bp g =>
            match Sp.val, g with
            | .shift N, .neg Ng =>
                decide (Ng.val = N) &&
                  decide (bp.val = ([] : ResolvedPending U O)) &&
                    decide (c.state = parent.state.resetRound) &&
                      decide (c.coverage = parent.coverage) &&
                        decide (rawVals c.rawSupport = rawVals parent.rawSupport) &&
                          decide (c.depSupport = parent.depSupport)
            | _, _ => false
        | _, _ => false
    | .caseSum, .two cL cR =>
        match j, cL.judgment, cR.judgment with
        | .sInv bp g, .sInv bpL gL, .sInv bpR gR =>
            decide (gL = g ∧ gR = g) &&
              sameStateCoverage parent cL && sameStateCoverage parent cR &&
                unionRaw parent cL cR && unionDep parent cL cR &&
                  match bp.val with
                  | ⟨⟨.sum A B, _⟩, K⟩ :: _ =>
                      if hA : A ∈ U.pos then
                        if hB : B ∈ U.pos then
                          decide (ResolvedPending.sumLeft A B hA bp.val =
                            some bpL.val) &&
                            decide (ResolvedPending.sumRight A B hB bp.val =
                              some bpR.val) &&
                              match bpL.val, bpR.val with
                              | ⟨_, KL⟩ :: _, ⟨_, KR⟩ :: _ =>
                                  decide (KL = K ∧ KR = K)
                              | _, _ => false
                        else false
                      else false
                  | _ => false
        | _, _, _ => false
    | .abort, .none =>
        match j with
        | .sInv bp _ =>
            match bp.val with
            | ⟨⟨.zero, _⟩, _⟩ :: _ =>
                decide (parent.rawSupport = ∅) && decide (parent.depSupport = ∅)
            | _ => false
        | _ => false
    | .storeAtom, .one c =>
        match j, c.judgment with
        | .sInv bp g, .sInv bp' g' =>
            decide (g' = g) && decide (c.coverage = parent.coverage) &&
              match bp.val with
              | ⟨⟨.atom q, _⟩, K⟩ :: rest =>
                  if hCap : parent.state.depth < B then
                    if hS : StableTy.atom q ∈ U.stable then
                      let S : UStable U := ⟨.atom q, hS⟩
                      decide (c.state = parent.state.pushResolved hCap S K) &&
                        decide (bp'.val = rest) &&
                          decide (c.depSupport = parent.depSupport) &&
                            decide (rawVals parent.rawSupport =
                              (rawVals c.rawSupport).filter
                                (fun n => n < parent.state.depth))
                    else false
                  else false
              | _ => false
        | _, _ => false
    | .storeShift, .one c =>
        match j, c.judgment with
        | .sInv bp g, .sInv bp' g' =>
            decide (g' = g) && decide (c.coverage = parent.coverage) &&
              match bp.val with
              | ⟨⟨.shift N, _⟩, K⟩ :: rest =>
                  if hCap : parent.state.depth < B then
                    if hS : StableTy.neg N ∈ U.stable then
                      let S : UStable U := ⟨.neg N, hS⟩
                      decide (c.state = parent.state.pushResolved hCap S K) &&
                        decide (bp'.val = rest) &&
                          decide (c.depSupport = parent.depSupport) &&
                            decide (rawVals parent.rawSupport =
                              (rawVals c.rawSupport).filter
                                (fun n => n < parent.state.depth))
                    else false
                  else false
              | _ => false
        | _, _ => false
    | .unit, .none =>
        match j with
        | .sInv bp g =>
            decide (bp.val = ([] : ResolvedPending U O)) &&
              match g with
              | .neg N =>
                  decide (N.val = (Neg.one : Neg sig.nBases)) &&
                    decide (parent.rawSupport = ∅) &&
                      decide (parent.depSupport = ∅)
              | _ => false
        | _ => false
    | .pair, .two c₁ c₂ =>
        match j, c₁.judgment, c₂.judgment with
        | .sInv bp g, .sInv bp₁ g₁, .sInv bp₂ g₂ =>
            decide (bp.val = ([] : ResolvedPending U O)) &&
              decide (bp₁.val = ([] : ResolvedPending U O)) &&
                decide (bp₂.val = ([] : ResolvedPending U O)) &&
                  match g, g₁, g₂ with
                  | .neg P, .neg A, .neg B =>
                      (match P.val with
                       | .prod A' B' => decide (A' = A.val ∧ B' = B.val)
                       | _ => false) &&
                        sameStateCoverage parent c₁ &&
                          sameStateCoverage parent c₂ &&
                            unionRaw parent c₁ c₂ && unionDep parent c₁ c₂
                  | _, _, _ => false
        | _, _, _ => false
    | .lam, .one c =>
        match j, c.judgment with
        | .sInv bp g, .sInv bp' g' =>
            decide (bp.val = ([] : ResolvedPending U O)) &&
              match g, g' with
              | .neg Arr, .neg N =>
                  match Arr.val with
                  | .arr P N' =>
                      decide (N' = N.val) &&
                        (if hP : P ∈ U.pos then
                          if hL : 1 ≤ L then
                            decide (bp' =
                              BoundedPending.lambdaPending ⟨P, hP⟩ hL) &&
                              (match bp'.val with
                               | cell :: _ => decide (cell.support = ∅)
                               | [] => false) &&
                                sameFrame parent c
                          else false
                        else false)
                  | _ => false
              | _, _ => false
        | _, _ => false
    | .satShift, .one c =>
        match j, c.judgment with
        | .sInv bp g, .sat P =>
            decide (bp.val = ([] : ResolvedPending U O)) &&
              match g with
              | .neg N =>
                  decide (N.val = .shift P.val) && sameFrame parent c
              | _ => false
        | _, _ => false
    | .satPos, .one c =>
        match j, c.judgment with
        | .sInv bp g, .sat P =>
            decide (bp.val = ([] : ResolvedPending U O)) &&
              match g with
              | .pos Pg => decide (Pg = P) && sameFrame parent c
              | _ => false
        | _, _ => false
    | _, _ => false

def StructuralValid (parent : SearchKey U O B L)
    (tag : StructuralTag) (deps : DepBundle (SearchKey U O B L)) : Prop :=
  structuralValidB parent tag deps = true

instance (parent : SearchKey U O B L) (tag : StructuralTag)
    (deps : DepBundle (SearchKey U O B L)) :
    Decidable (StructuralValid parent tag deps) :=
  inferInstanceAs (Decidable (_ = true))

end Structural

open Structural

/-! ### Structural alternatives -/

structure StructuralAlternative {U : SearchUniverse sig} {O : Type} {B L : Nat}
    [DecidableEq O] (parent : SearchKey U O B L) where
  tag : StructuralTag
  deps : DepBundle (SearchKey U O B L)
  valid : StructuralValid parent tag deps

namespace StructuralAlternative

variable {U : SearchUniverse sig} {O : Type} {B L : Nat} [DecidableEq O]
variable {parent : SearchKey U O B L}

theorem ext {a b : StructuralAlternative parent}
    (ht : a.tag = b.tag) (hd : a.deps = b.deps) : a = b := by
  cases a; cases b; cases ht; cases hd; rfl

instance : DecidableEq (StructuralAlternative parent) := fun a b =>
  if h : a.tag = b.tag ∧ a.deps = b.deps then isTrue (ext h.1 h.2)
  else isFalse fun heq => by cases heq; exact h ⟨rfl, rfl⟩

abbrev Code (parent : SearchKey U O B L) : Type :=
  { td : StructuralTag × DepBundle (SearchKey U O B L) //
      StructuralValid parent td.1 td.2 }

def ofCode (c : Code parent) : StructuralAlternative parent :=
  ⟨c.1.1, c.1.2, c.2⟩

def toCode (a : StructuralAlternative parent) : Code parent :=
  ⟨⟨a.tag, a.deps⟩, a.valid⟩

@[simp] theorem ofCode_toCode (a : StructuralAlternative parent) :
    ofCode (toCode a) = a := rfl

instance [Fintype O] : Fintype (Code parent) := by
  classical
  infer_instance

instance [Fintype O] : Fintype (StructuralAlternative parent) :=
  Fintype.ofSurjective ofCode fun a => ⟨toCode a, ofCode_toCode a⟩

instance [Finite O] : Finite (StructuralAlternative parent) := by
  letI := Fintype.ofFinite O
  letI : DecidableEq O := Classical.decEq O
  infer_instance

end StructuralAlternative

def allStructuralAlternatives {U : SearchUniverse sig} {O : Type} {B L : Nat}
    [DecidableEq O] [Fintype O] (parent : SearchKey U O B L) :
    Finset (StructuralAlternative parent) :=
  Finset.univ

@[simp] theorem mem_allStructuralAlternatives
    {U : SearchUniverse sig} {O : Type} {B L : Nat}
    [DecidableEq O] [Fintype O] {parent : SearchKey U O B L}
    (a : StructuralAlternative parent) :
    a ∈ allStructuralAlternatives parent :=
  Finset.mem_univ _

theorem mem_allStructuralAlternatives_iff
    {U : SearchUniverse sig} {O : Type} {B L : Nat}
    [DecidableEq O] [Fintype O] {parent : SearchKey U O B L}
    (tag : StructuralTag) (deps : DepBundle (SearchKey U O B L)) :
    (∃ h : StructuralValid parent tag deps,
        ⟨tag, deps, h⟩ ∈ allStructuralAlternatives parent) ↔
      StructuralValid parent tag deps :=
  ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, Finset.mem_univ _⟩⟩

theorem structural_alternatives_finite
    {U : SearchUniverse sig} {O : Type} {B L : Nat}
    [DecidableEq O] [Fintype O] (parent : SearchKey U O B L) :
    Finite (StructuralAlternative parent) :=
  inferInstance

theorem deps_length_le_two
    {U : SearchUniverse sig} {O : Type} {B L : Nat}
    [DecidableEq O] (parent : SearchKey U O B L)
    (a : StructuralAlternative parent) :
    a.deps.toList.length ≤ 2 :=
  DepBundle.length_le_two _

theorem structural_dependency_mem_allSearchKeys
    {U : SearchUniverse sig} {O : Type} {B L : Nat}
    [DecidableEq O] [Fintype O] (parent : SearchKey U O B L)
    (a : StructuralAlternative parent) :
    ∀ c ∈ a.deps.toList, c ∈ allSearchKeys U O B L := by
  intro c _; exact allSearchKeys_complete _

theorem no_sat_structural_alternative
    {U : SearchUniverse sig} {O : Type} {B L : Nat}
    [DecidableEq O] [Fintype O] (parent : SearchKey U O B L)
    {P : UPos U} (hj : parent.judgment = .sat P) :
    allStructuralAlternatives parent = ∅ := by
  refine Finset.univ_eq_empty_iff.mpr ⟨fun a => ?_⟩
  have hb : structuralValidB parent a.tag a.deps = false := by
    cases a.tag <;> simp [structuralValidB, hj]
  have hv : StructuralValid parent a.tag a.deps := a.valid
  simp [StructuralValid, hb] at hv

/-- Store alternatives require spare capacity `depth < B`. -/
theorem store_requires_capacity
    {U : SearchUniverse sig} {O : Type} {B L : Nat}
    [DecidableEq O] {parent : SearchKey U O B L}
    (c : SearchKey U O B L)
    (h : StructuralValid parent .storeAtom (.one c) ∨
      StructuralValid parent .storeShift (.one c)) :
    parent.state.depth < B := by
  by_cases hCap : parent.state.depth < B
  · exact hCap
  · exfalso
    rcases h with hv | hv
    · change structuralValidB parent .storeAtom (.one c) = true at hv
      cases hJ : parent.judgment with
      | sNeg _ => simp [structuralValidB, hJ] at hv
      | sPos _ => simp [structuralValidB, hJ] at hv
      | sat _ => simp [structuralValidB, hJ] at hv
      | sInv bp g =>
          cases hC : c.judgment with
          | sNeg _ => simp [structuralValidB, hJ, hC] at hv
          | sPos _ => simp [structuralValidB, hJ, hC] at hv
          | sat _ => simp [structuralValidB, hJ, hC] at hv
          | sInv bp' g' =>
              simp [structuralValidB, hJ, hC, Bool.and_eq_true, decide_eq_true_eq] at hv
              obtain ⟨_, hMatch⟩ := hv
              split at hMatch <;> simp [hCap] at hMatch
    · change structuralValidB parent .storeShift (.one c) = true at hv
      cases hJ : parent.judgment with
      | sNeg _ => simp [structuralValidB, hJ] at hv
      | sPos _ => simp [structuralValidB, hJ] at hv
      | sat _ => simp [structuralValidB, hJ] at hv
      | sInv bp g =>
          cases hC : c.judgment with
          | sNeg _ => simp [structuralValidB, hJ, hC] at hv
          | sPos _ => simp [structuralValidB, hJ, hC] at hv
          | sat _ => simp [structuralValidB, hJ, hC] at hv
          | sInv bp' g' =>
              simp [structuralValidB, hJ, hC, Bool.and_eq_true, decide_eq_true_eq] at hv
              obtain ⟨_, hMatch⟩ := hv
              split at hMatch <;> simp [hCap] at hMatch

theorem structural_coverage_preserved
    {U : SearchUniverse sig} {O : Type} {B L : Nat}
    [DecidableEq O] {parent c : SearchKey U O B L}
    (h : sameStateCoverage parent c = true) :
    c.coverage = parent.coverage := by
  simp [sameStateCoverage, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem structural_support_equations
    {U : SearchUniverse sig} {O : Type} {B L : Nat}
    [DecidableEq O] {parent c₁ c₂ : SearchKey U O B L}
    (hUnion : unionRaw parent c₁ c₂ = true)
    (hDep : unionDep parent c₁ c₂ = true) :
    rawVals parent.rawSupport = rawVals c₁.rawSupport ∪ rawVals c₂.rawSupport ∧
      parent.depSupport = c₁.depSupport ∪ c₂.depSupport := by
  simp [unionRaw, unionDep, decide_eq_true_eq] at hUnion hDep
  exact ⟨hUnion, hDep⟩

/-! ### Fixtures -/

namespace SearchStructuralFixtures

open SearchUniverseFixtures

abbrev O1 := Fin 1
instance : DecidableEq O1 := inferInstanceAs (DecidableEq (Fin 1))
instance : Fintype O1 := inferInstanceAs (Fintype (Fin 1))

def Nshift : UNeg Uz := ⟨Neg.shift X, by native_decide⟩
def Sshift : UStable Uz := ⟨.neg (.shift X), by native_decide⟩

def stVar : ResolvedState Uz O1 1 :=
  (ResolvedState.empty Uz O1 1).pushLexical (by decide) Sshift

def parentVar : SearchKey Uz O1 1 1 where
  state := stVar
  coverage := ∅
  judgment := .sNeg Nshift
  rawSupport := ({⟨0, by decide⟩} : Finset (Fin stVar.depth))
  depSupport := ∅

/-- Fixture 1: variable leaf has exact raw and resolved support. -/
theorem var_exact_supports :
    StructuralValid parentVar .var (.none : DepBundle (SearchKey Uz O1 1 1)) ∧
      parentVar.rawSupport = ({⟨0, by decide⟩} : Finset _) ∧
        parentVar.depSupport = parentVar.state.depAt ⟨0, by decide⟩ := by
  refine ⟨by native_decide, rfl, ?_⟩
  change (∅ : DepSupport O1) = stVar.depAt ⟨0, by decide⟩
  exact (ResolvedState.pushLexical_new_support_empty
    (ResolvedState.empty Uz O1 1) (by decide) Sshift).symm

/-- Fixture 2: application unions both supports (gate). -/
theorem app_unions_gate
    {parent c₁ c₂ : SearchKey Uz O1 1 1}
    (hR : unionRaw parent c₁ c₂ = true) (hD : unionDep parent c₁ c₂ = true) :
    rawVals parent.rawSupport = rawVals c₁.rawSupport ∪ rawVals c₂.rawSupport ∧
      parent.depSupport = c₁.depSupport ∪ c₂.depSupport :=
  structural_support_equations hR hD

/-- Fixture 3: caseSum preserves K. -/
theorem caseSum_preserves_K
    (A B : Pos 0) (hA : A ∈ Uz.pos) (hB : B ∈ Uz.pos)
    (K : DepSupport O1) (rest : ResolvedPending Uz O1)
    (hSum : Pos.sum A B ∈ Uz.pos) :
    ResolvedPending.sumLeft A B hA (⟨⟨.sum A B, hSum⟩, K⟩ :: rest) =
      some (⟨⟨A, hA⟩, K⟩ :: rest) ∧
      ResolvedPending.sumRight A B hB (⟨⟨.sum A B, hSum⟩, K⟩ :: rest) =
        some (⟨⟨B, hB⟩, K⟩ :: rest) :=
  ⟨ResolvedPending.sumLeft_preserves_support (U := Uz) (O := O1) A B hA (hSum := hSum),
    ResolvedPending.sumRight_preserves_support (U := Uz) (O := O1) A B hB (hSum := hSum)⟩

/-- Fixture 4: store pops only raw; pushResolved preserves K at new level. -/
theorem store_pop_preserves_dep
    (st : ResolvedState Uz O1 1) (h : st.depth < 1)
    (S : UStable Uz) (K : DepSupport O1)
    (raw : Finset (Fin (st.depth + 1))) :
    st.popRaw h raw =
      (Finset.univ : Finset (Fin st.depth)).filter (fun i => i.castSucc ∈ raw) ∧
      (st.pushResolved h S K).depAt (Fin.last st.depth) = K :=
  ⟨rfl, ResolvedState.pushResolved_new_support st h S K⟩

/-- Fixture 5: lambda pending carries empty resolved support. -/
theorem lambda_pending_empty_support (P : UPos Uz) :
    (ResolvedPending.lambdaPending (O := O1) P).head?.map (·.support) =
      some (∅ : DepSupport O1) :=
  rfl

/-- Fixture 6: pair(unit,unit) retains two identical sibling occurrences. -/
def unitKey : SearchKey Uz O1 1 1 where
  state := ResolvedState.empty Uz O1 1
  coverage := ∅
  judgment := .sPos ⟨X, by native_decide⟩
  rawSupport := ∅
  depSupport := ∅

theorem pair_unit_unit_duplicate_siblings :
    let d : DepBundle (SearchKey Uz O1 1 1) := .two unitKey unitKey
    d.toList = [unitKey, unitKey] ∧ d.toList.length = 2 :=
  ⟨rfl, rfl⟩

def satParent : SearchKey Uz O1 1 1 where
  state := ResolvedState.empty Uz O1 1
  coverage := ∅
  judgment := .sat ⟨X, by native_decide⟩
  rawSupport := ∅
  depSupport := ∅

/-- Fixture 7: saturation parent has zero structural alternatives. -/
theorem sat_parent_no_structural :
    allStructuralAlternatives satParent = ∅ :=
  no_sat_structural_alternative satParent rfl

theorem coverage_gate
    {p c : SearchKey Uz O1 1 1} (h : sameStateCoverage p c = true) :
    c.coverage = p.coverage :=
  structural_coverage_preserved h

end SearchStructuralFixtures

end Gimbal.Equality.Scherer
