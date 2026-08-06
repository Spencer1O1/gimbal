/-
  Scherer-core enumerable support-aware search keys.

  A search key packages bounded resolved state, exact obligation coverage,
  judgment tag (with bounded pending / goal), exact raw fact-support, and
  resolved dependency support. Raw and resolved supports remain separate.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Gimbal.Equality.Scherer.SearchBounds

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Bounded goals -/

/-- Universe-bounded goal (negative or positive). -/
inductive UGoal (U : SearchUniverse sig) where
  | neg : UNeg U → UGoal U
  | pos : UPos U → UGoal U
  deriving DecidableEq

namespace UGoal

variable {U : SearchUniverse sig}

/-- Erase to intrinsic polarized `Goal`. -/
def erase : UGoal U → Goal sig.nBases
  | .neg N => .neg N.val
  | .pos P => .pos P.val

@[simp] theorem erase_neg (N : UNeg U) : erase (.neg N) = .neg N.val := rfl
@[simp] theorem erase_pos (P : UPos U) : erase (.pos P) = .pos P.val := rfl

abbrev Code (U : SearchUniverse sig) : Type := UNeg U ⊕ UPos U

def ofCode : Code U → UGoal U
  | .inl N => .neg N
  | .inr P => .pos P

def toCode : UGoal U → Code U
  | .neg N => .inl N
  | .pos P => .inr P

@[simp] theorem ofCode_toCode (g : UGoal U) : ofCode (toCode g) = g := by
  cases g <;> rfl

instance : Fintype (UGoal U) :=
  Fintype.ofSurjective ofCode fun g => ⟨toCode g, ofCode_toCode g⟩

instance : Finite (UGoal U) := inferInstance

end UGoal

/-! ### Search judgments -/

/--
Tagged search judgment under length bound `L`.

* `sNeg` / `sPos`: neutral focus
* `sInv`: inversion with bounded pending and goal
* `sat`: saturation focus on a positive type
-/
inductive SearchJudgment (U : SearchUniverse sig) (O : Type) (L : Nat) where
  | sNeg : UNeg U → SearchJudgment U O L
  | sPos : UPos U → SearchJudgment U O L
  | sInv : BoundedPending U O L → UGoal U → SearchJudgment U O L
  | sat : UPos U → SearchJudgment U O L

namespace SearchJudgment

variable {U : SearchUniverse sig} {O : Type} {L : Nat}

abbrev Code (U : SearchUniverse sig) (O : Type) (L : Nat) : Type :=
  UNeg U ⊕ UPos U ⊕ (BoundedPending U O L × UGoal U) ⊕ UPos U

def ofCode [DecidableEq O] : Code U O L → SearchJudgment U O L
  | .inl N => .sNeg N
  | .inr (.inl P) => .sPos P
  | .inr (.inr (.inl ⟨bp, g⟩)) => .sInv bp g
  | .inr (.inr (.inr P)) => .sat P

def toCode [DecidableEq O] : SearchJudgment U O L → Code U O L
  | .sNeg N => .inl N
  | .sPos P => .inr (.inl P)
  | .sInv bp g => .inr (.inr (.inl ⟨bp, g⟩))
  | .sat P => .inr (.inr (.inr P))

@[simp] theorem ofCode_toCode [DecidableEq O] (j : SearchJudgment U O L) :
    ofCode (toCode j) = j := by
  cases j <;> rfl

instance [DecidableEq O] : DecidableEq (Code U O L) := inferInstance

instance [DecidableEq O] : DecidableEq (SearchJudgment U O L) := fun a b =>
  if h : toCode a = toCode b then
    isTrue (by
      have := congrArg ofCode h
      simpa [ofCode_toCode] using this)
  else
    isFalse fun heq => h (by cases heq; rfl)

instance [DecidableEq O] [Fintype O] : Fintype (SearchJudgment U O L) :=
  Fintype.ofSurjective ofCode fun j => ⟨toCode j, ofCode_toCode j⟩

instance [Fintype O] : Finite (SearchJudgment U O L) := by
  letI := Fintype.ofFinite O
  letI : DecidableEq O := Classical.decEq O
  infer_instance

end SearchJudgment

/-! ### Exact raw fact-support -/

/-- Exact raw fact-support at a resolved state: finite set of live levels. -/
abbrev RawFactSupport {U : SearchUniverse sig} {O : Type} {B : Nat}
    (st : ResolvedState U O B) : Type :=
  Finset (Fin st.depth)

/-! ### Search keys -/

/--
Finite support-aware search key.

Identity includes state, coverage, judgment (pending/goal/tag), exact raw
support, and exact resolved dependency support — none may be collapsed.
-/
structure SearchKey (U : SearchUniverse sig) (O : Type) (B L : Nat) where
  state : ResolvedState U O B
  coverage : Finset (Obligation U O)
  judgment : SearchJudgment U O L
  rawSupport : RawFactSupport state
  depSupport : DepSupport O

namespace SearchKey

variable {U : SearchUniverse sig} {O : Type} {B L : Nat}

theorem ext {k₁ k₂ : SearchKey U O B L}
    (hState : k₁.state = k₂.state)
    (hCov : k₁.coverage = k₂.coverage)
    (hJ : k₁.judgment = k₂.judgment)
    (hRaw : HEq k₁.rawSupport k₂.rawSupport)
    (hDep : k₁.depSupport = k₂.depSupport) : k₁ = k₂ := by
  cases k₁; cases k₂
  cases hState; cases hCov; cases hJ; cases hDep
  cases hRaw
  rfl

/-- Exactness: equal keys share state. -/
theorem eq_state {k₁ k₂ : SearchKey U O B L} (h : k₁ = k₂) :
    k₁.state = k₂.state := h ▸ rfl

/-- Exactness: equal keys share coverage. -/
theorem eq_coverage {k₁ k₂ : SearchKey U O B L} (h : k₁ = k₂) :
    k₁.coverage = k₂.coverage := h ▸ rfl

/-- Exactness: equal keys share judgment. -/
theorem eq_judgment {k₁ k₂ : SearchKey U O B L} (h : k₁ = k₂) :
    k₁.judgment = k₂.judgment := h ▸ rfl

/-- Exactness: equal keys share exact raw support (`HEq` across possibly rewritten depth). -/
theorem eq_rawSupport {k₁ k₂ : SearchKey U O B L} (h : k₁ = k₂) :
    HEq k₁.rawSupport k₂.rawSupport := h ▸ HEq.rfl

/--
Cast theorem: when states are propositionally equal, raw supports compare after
`cast` along the induced `RawFactSupport` equality (no unsafe identity smuggling).
-/
theorem rawSupport_cast {k₁ k₂ : SearchKey U O B L}
    (hs : k₁.state = k₂.state) :
    RawFactSupport k₁.state = RawFactSupport k₂.state :=
  congrArg RawFactSupport hs

theorem eq_rawSupport_cast {k₁ k₂ : SearchKey U O B L} (h : k₁ = k₂) :
    k₁.rawSupport =
      cast (rawSupport_cast (eq_state h)).symm k₂.rawSupport := by
  cases h; rfl

/-- Exactness: equal keys share resolved dependency support. -/
theorem eq_depSupport {k₁ k₂ : SearchKey U O B L} (h : k₁ = k₂) :
    k₁.depSupport = k₂.depSupport := h ▸ rfl

/-- Sigma encoding (executable Fintype / DecidableEq carrier). -/
abbrev Code (U : SearchUniverse sig) (O : Type) (B L : Nat) : Type :=
  Σ st : ResolvedState U O B,
    Finset (Obligation U O) ×
      SearchJudgment U O L ×
        Finset (Fin st.depth) ×
          DepSupport O

def ofCode [DecidableEq O] (c : Code U O B L) : SearchKey U O B L where
  state := c.1
  coverage := c.2.1
  judgment := c.2.2.1
  rawSupport := c.2.2.2.1
  depSupport := c.2.2.2.2

def toCode [DecidableEq O] (k : SearchKey U O B L) : Code U O B L :=
  ⟨k.state, k.coverage, k.judgment, k.rawSupport, k.depSupport⟩

@[simp] theorem ofCode_toCode [DecidableEq O] (k : SearchKey U O B L) :
    ofCode (toCode k) = k := rfl

instance [DecidableEq O] : DecidableEq (Code U O B L) := by
  classical
  infer_instance

instance [DecidableEq O] : DecidableEq (SearchKey U O B L)
  | ⟨st₁, c₁, j₁, r₁, d₁⟩, ⟨st₂, c₂, j₂, r₂, d₂⟩ =>
    if hs : st₁ = st₂ then by
      subst hs
      exact
        if hc : c₁ = c₂ then
          if hj : j₁ = j₂ then
            if hd : d₁ = d₂ then
              if hr : r₁ = r₂ then
                isTrue (by subst hc; subst hj; subst hd; subst hr; rfl)
              else
                isFalse fun heq => by cases heq; exact hr rfl
            else
              isFalse fun heq => by cases heq; exact hd rfl
          else
            isFalse fun heq => by cases heq; exact hj rfl
        else
          isFalse fun heq => by cases heq; exact hc rfl
    else
      isFalse fun heq => by cases heq; exact hs rfl

instance [DecidableEq O] [Fintype O] : Fintype (Code U O B L) := by
  classical
  infer_instance

instance [DecidableEq O] [Fintype O] : Fintype (SearchKey U O B L) :=
  Fintype.ofSurjective ofCode fun k => ⟨toCode k, ofCode_toCode k⟩

instance [Fintype O] : Finite (SearchKey U O B L) := by
  letI := Fintype.ofFinite O
  letI : DecidableEq O := Classical.decEq O
  infer_instance

/-- Whether exact raw support intersects the state's current-raw mask. -/
def usesCurrent (k : SearchKey U O B L) : Bool :=
  decide (k.rawSupport ∩ k.state.currentRaw).Nonempty

theorem usesCurrent_iff (k : SearchKey U O B L) :
    k.usesCurrent = true ↔ (k.rawSupport ∩ k.state.currentRaw).Nonempty := by
  simp [usesCurrent]

end SearchKey

/-- Full finite search-key space. -/
def allSearchKeys (U : SearchUniverse sig) (O : Type) (B L : Nat)
    [DecidableEq O] [Fintype O] : Finset (SearchKey U O B L) :=
  Finset.univ

@[simp] theorem allSearchKeys_complete {U : SearchUniverse sig} {O : Type}
    {B L : Nat} [DecidableEq O] [Fintype O] (k : SearchKey U O B L) :
    k ∈ allSearchKeys U O B L :=
  Finset.mem_univ _

theorem allSearchKeys_card_positive {U : SearchUniverse sig} {O : Type}
    {B L : Nat} [DecidableEq O] [Fintype O]
    (h : U.pos.Nonempty ∨ U.neg.Nonempty) :
    0 < (allSearchKeys U O B L).card := by
  simp only [allSearchKeys, Finset.card_univ]
  refine Fintype.card_pos_iff.mpr ⟨?_⟩
  if hp : U.pos.Nonempty then
    let P := Classical.choose hp
    have hP : P ∈ U.pos := Classical.choose_spec hp
    exact ⟨ResolvedState.empty U O B, ∅, .sPos ⟨P, hP⟩, ∅, ∅⟩
  else
    have hn : U.neg.Nonempty := Or.resolve_left h hp
    let N := Classical.choose hn
    have hN : N ∈ U.neg := Classical.choose_spec hn
    exact ⟨ResolvedState.empty U O B, ∅, .sNeg ⟨N, hN⟩, ∅, ∅⟩

/-! ### Adversarial fixtures -/

namespace SearchKeyFixtures

open SearchUniverseFixtures

abbrev O1 := Fin 1
instance : DecidableEq O1 := inferInstanceAs (DecidableEq (Fin 1))
instance : Fintype O1 := inferInstanceAs (Fintype (Fin 1))
def o0 : O1 := ⟨0, by decide⟩

def P0 : UPos Uz := ⟨SearchUniverseFixtures.X, by native_decide⟩
def Nshift : UNeg Uz :=
  ⟨Neg.shift SearchUniverseFixtures.X, by native_decide⟩
def Sz : UStable Uz := ⟨zTy, by native_decide⟩

def st0 : ResolvedState Uz O1 1 := ResolvedState.empty Uz O1 1
def stLex : ResolvedState Uz O1 1 := st0.pushLexical (by decide) Sz
def stProm : ResolvedState Uz O1 1 :=
  st0.pushResolved (by decide) Sz ({o0} : DepSupport O1)

def rawAt0 (st : ResolvedState Uz O1 1) (_h : st.depth = 1) : RawFactSupport st :=
  ({⟨0, by omega⟩} : Finset (Fin st.depth))

def cov0 : Finset (Obligation Uz O1) := ∅
def cov1 : Finset (Obligation Uz O1) := {⟨P0, ∅⟩}

def jPos : SearchJudgment Uz O1 1 := .sPos P0
def jNeg : SearchJudgment Uz O1 1 := .sNeg Nshift
def jSat : SearchJudgment Uz O1 1 := .sat P0
def jInvEmpty : SearchJudgment Uz O1 1 :=
  .sInv (BoundedPending.empty Uz O1 1) (.pos P0)
def jInvZero : SearchJudgment Uz O1 1 :=
  .sInv (BoundedPending.lambdaPending P0 (by decide)) (.pos P0)
def jInvNegGoal : SearchJudgment Uz O1 1 :=
  .sInv (BoundedPending.empty Uz O1 1) (.neg Nshift)

def mk (st : ResolvedState Uz O1 1) (cov : Finset (Obligation Uz O1))
    (j : SearchJudgment Uz O1 1) (raw : RawFactSupport st) (dep : DepSupport O1) :
    SearchKey Uz O1 1 1 :=
  ⟨st, cov, j, raw, dep⟩

theorem stLex_depth : stLex.depth = 1 := rfl
theorem stProm_depth : stProm.depth = 1 := rfl

/-- Fixture 1: different rawSupport ⇒ distinct keys. -/
theorem distinct_rawSupport :
    mk stLex cov0 jPos ∅ ∅ ≠ mk stLex cov0 jPos (rawAt0 stLex stLex_depth) ∅ := by
  intro h
  have hr : HEq
      (mk stLex cov0 jPos ∅ ∅).rawSupport
      (mk stLex cov0 jPos (rawAt0 stLex stLex_depth) ∅).rawSupport :=
    SearchKey.eq_rawSupport h
  have hEq : (∅ : RawFactSupport stLex) = rawAt0 stLex stLex_depth := eq_of_heq hr
  have hne : (∅ : RawFactSupport stLex) ≠ rawAt0 stLex stLex_depth := by decide
  exact hne hEq

/-- Fixture 2: different depSupport ⇒ distinct keys. -/
theorem distinct_depSupport :
    mk st0 cov0 jPos ∅ ∅ ≠ mk st0 cov0 jPos ∅ {o0} := by
  intro h
  have hd := SearchKey.eq_depSupport h
  have hne : (∅ : DepSupport O1) ≠ {o0} := by decide
  exact hne hd

/-- Fixture 3: different coverage ⇒ distinct keys. -/
theorem distinct_coverage :
    mk st0 cov0 jPos ∅ ∅ ≠ mk st0 cov1 jPos ∅ ∅ := by
  intro h
  have hc := SearchKey.eq_coverage h
  have hne : cov0 ≠ cov1 := by decide
  exact hne hc

/-- Fixture 4: empty pending vs pending `[zero]` inversion judgments distinct. -/
theorem distinct_pending_inv : jInvEmpty ≠ jInvZero := by
  intro h
  cases h

/-- Fixture 5: judgment tags are distinct. -/
theorem distinct_judgment_tags :
    jNeg ≠ jPos ∧ jPos ≠ jInvEmpty ∧ jInvEmpty ≠ jSat ∧ jNeg ≠ jSat := by
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

/-- Fixture 6: different goals under same pending are distinct. -/
theorem distinct_goals : jInvEmpty ≠ jInvNegGoal := by
  intro h
  injection h with _ hg
  cases hg

/-- Fixture 7: enumeration contains every fixture key. -/
theorem allSearchKeys_contains_fixtures :
    mk stLex cov0 jPos (rawAt0 stLex stLex_depth) ∅ ∈ allSearchKeys Uz O1 1 1 :=
  allSearchKeys_complete _

theorem allSearchKeys_contains_fixtures' :
    mk st0 cov0 jPos ∅ {o0} ∈ allSearchKeys Uz O1 1 1 ∧
      mk st0 cov1 jPos ∅ ∅ ∈ allSearchKeys Uz O1 1 1 ∧
        mk st0 cov0 jInvEmpty ∅ ∅ ∈ allSearchKeys Uz O1 1 1 ∧
          mk st0 cov0 jInvZero ∅ ∅ ∈ allSearchKeys Uz O1 1 1 ∧
            mk st0 cov0 jNeg ∅ ∅ ∈ allSearchKeys Uz O1 1 1 ∧
              mk st0 cov0 jSat ∅ ∅ ∈ allSearchKeys Uz O1 1 1 ∧
                mk stProm cov0 jPos (rawAt0 stProm stProm_depth) {o0} ∈
                  allSearchKeys Uz O1 1 1 :=
  ⟨allSearchKeys_complete _, allSearchKeys_complete _, allSearchKeys_complete _,
    allSearchKeys_complete _, allSearchKeys_complete _, allSearchKeys_complete _,
    allSearchKeys_complete _⟩

theorem stLex_mem_current0 :
    (⟨0, by decide⟩ : Fin stLex.depth) ∈ stLex.currentRaw := by
  unfold stLex st0
  exact ResolvedState.push_new_current _ (by decide) Sz (∅ : DepSupport O1)

theorem stProm_mem_current0 :
    (⟨0, by decide⟩ : Fin stProm.depth) ∈ stProm.currentRaw := by
  unfold stProm st0
  exact ResolvedState.push_new_current _ (by decide) Sz ({o0} : DepSupport O1)

theorem stProm_dep0 :
    stProm.depAt ⟨0, by decide⟩ = ({o0} : DepSupport O1) := by
  unfold stProm st0
  exact ResolvedState.pushResolved_new_support _ (by decide) Sz ({o0} : DepSupport O1)

/-- Fixture 8: raw-current lexical binder ⇒ `usesCurrent`, empty depSupport. -/
theorem lexical_usesCurrent_empty_dep :
    let k := mk stLex cov0 jPos (rawAt0 stLex stLex_depth) ∅
    k.usesCurrent = true ∧ k.depSupport = ∅ := by
  intro k
  constructor
  · rw [SearchKey.usesCurrent_iff]
    exact ⟨⟨0, by decide⟩, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, stLex_mem_current0⟩⟩
  · rfl

theorem lexical_usesCurrent_iff :
    let k := mk stLex cov0 jPos (rawAt0 stLex stLex_depth) ∅
    (k.rawSupport ∩ k.state.currentRaw).Nonempty :=
  (SearchKey.usesCurrent_iff _).mp lexical_usesCurrent_empty_dep.1

/-- Fixture 9: promoted result — fresh raw current, inherited nonempty depSupport. -/
theorem promoted_fresh_raw_inherited_dep :
    let k := mk stProm cov0 jPos (rawAt0 stProm stProm_depth) {o0}
    k.depSupport = {o0} ∧
      k.usesCurrent = true ∧
        k.state.depAt ⟨0, by decide⟩ = ({o0} : DepSupport O1) := by
  intro k
  refine ⟨rfl, ?_, stProm_dep0⟩
  · rw [SearchKey.usesCurrent_iff]
    exact ⟨⟨0, by decide⟩,
      Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, stProm_mem_current0⟩⟩

theorem card_positive_fixture :
    0 < (allSearchKeys Uz O1 1 1).card :=
  allSearchKeys_card_positive (Or.inl ⟨P0.val, P0.property⟩)

end SearchKeyFixtures

end Gimbal.Equality.Scherer
