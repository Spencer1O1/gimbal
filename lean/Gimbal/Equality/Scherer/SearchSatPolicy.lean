/-
  Scherer-core fixed-policy saturation plans.

  Finite support-exact provisional `inconsistent` / `done` / `batch` plans for
  saturated search keys. Arbitrary `SatPolicy` is not certified, sound,
  canonical, or complete.
  No intrinsic Sat materialization, checked-empty claims, executable search,
  global visited sets, canonical selection, or S4.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Gimbal.Equality.Scherer.SearchForestCore

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Executable exact-support strong retrieval -/

namespace StrongAt

variable {U : SearchUniverse sig} {O : Type} {B : Nat} [DecidableEq O]

def decideB (st : ResolvedState U O B) : Pos sig.nBases → DepSupport O → Bool
  | .shift N, K =>
      decide (∃ i : Fin st.depth,
        (st.tyAt i).val = .neg N ∧ st.depAt i = K)
  | .atom q, K =>
      decide (∃ i : Fin st.depth,
        (st.tyAt i).val = .atom q ∧ st.depAt i = K)
  | .sum A B, K => decideB st A K || decideB st B K
  | .zero, _ => false

theorem decideB_of_strong (st : ResolvedState U O B) {P : Pos sig.nBases}
    {K : DepSupport O} (h : StrongAt st P K) : decideB st P K = true := by
  rcases h with ⟨⟨sp, hsl⟩⟩
  induction sp generalizing K with
  | atomVar i hty => subst hsl; exact decide_eq_true ⟨i, hty, rfl⟩
  | negVar i hty => subst hsl; exact decide_eq_true ⟨i, hty, rfl⟩
  | inl sp ih => simp only [decideB, Bool.or_eq_true]; exact Or.inl (ih hsl)
  | inr sp ih => simp only [decideB, Bool.or_eq_true]; exact Or.inr (ih hsl)

theorem strong_of_decideB (st : ResolvedState U O B) :
    ∀ (P : Pos sig.nBases) (K : DepSupport O),
      decideB st P K = true → StrongAt st P K
  | .atom q, K, h => by
      obtain ⟨i, hty, hdep⟩ := of_decide_eq_true h
      exact (of_atomVar i hty).exact hdep
  | .zero, _, h => by cases h
  | .sum A B, K, h => by
      simp only [decideB, Bool.or_eq_true] at h
      cases h with
      | inl hA => exact of_inl (strong_of_decideB st A K hA)
      | inr hB => exact of_inr (strong_of_decideB st B K hB)
  | .shift N, K, h => by
      obtain ⟨i, hty, hdep⟩ := of_decide_eq_true h
      exact (of_negVar i hty).exact hdep

theorem decideB_iff (st : ResolvedState U O B) (P : Pos sig.nBases)
    (K : DepSupport O) :
    decideB st P K = true ↔ StrongAt st P K :=
  ⟨strong_of_decideB st P K, decideB_of_strong st⟩

@[simp] theorem decideB_zero (st : ResolvedState U O B) (K : DepSupport O) :
    decideB st (.zero : Pos sig.nBases) K = false :=
  rfl

theorem not_zero (st : ResolvedState U O B) (K : DepSupport O) :
    ¬ StrongAt st (.zero : Pos sig.nBases) K := by
  rw [← decideB_iff]
  exact Bool.false_ne_true

instance (st : ResolvedState U O B) (P : Pos sig.nBases) (K : DepSupport O) :
    Decidable (StrongAt st P K) :=
  decidable_of_iff _ (decideB_iff st P K)

end StrongAt

/-! ### Saturated parents -/

variable {U : SearchUniverse sig} {O : Type} {B L : Nat}
variable [DecidableEq O] [Fintype O]

def isSaturated (k : SearchKey U O B L) : Prop :=
  ∃ P : UPos U, k.judgment = .sat P

def isSaturatedB (k : SearchKey U O B L) : Bool :=
  match k.judgment with | .sat _ => true | _ => false

theorem isSaturatedB_iff (k : SearchKey U O B L) :
    isSaturatedB k = true ↔ isSaturated k := by
  constructor
  · intro h
    cases hk : k.judgment with
    | sat P => exact ⟨P, hk⟩
    | sNeg _ | sPos _ | sInv _ _ => simp [isSaturatedB, hk] at h
  · rintro ⟨P, hP⟩; simp [isSaturatedB, hP]

instance (k : SearchKey U O B L) : Decidable (isSaturated k) :=
  decidable_of_iff _ (isSaturatedB_iff k)

abbrev SaturatedKey (U : SearchUniverse sig) (O : Type) (B L : Nat) : Type :=
  { k : SearchKey U O B L // isSaturated k }

def SaturatedKey.focus (k : SaturatedKey U O B L) : UPos U :=
  match hk : k.1.judgment with
  | .sat P => P
  | .sNeg _ | .sPos _ | .sInv _ _ =>
      False.elim (by
        have hB : isSaturatedB k.1 = true := (isSaturatedB_iff _).mpr k.2
        simp [isSaturatedB, hk] at hB)

/-! ### Finite plan carriers -/

inductive SatPlanData (U : SearchUniverse sig) (O : Type) (B L : Nat) where
  | inconsistent : SearchKey U O B L → SatPlanData U O B L
  | done : SearchKey U O B L → SatPlanData U O B L
  | batch {n : Nat} (hn : n < L)
      (obs : Fin (n + 1) → SearchKey U O B L)
      (body : SearchKey U O B L) :
      SatPlanData U O B L

namespace SatPlanData

abbrev Code (U : SearchUniverse sig) (O : Type) (B L : Nat) : Type :=
  SearchKey U O B L ⊕ SearchKey U O B L ⊕
    (Σ n : Fin L, (Fin (n.val + 1) → SearchKey U O B L) × SearchKey U O B L)

def ofCode : Code U O B L → SatPlanData U O B L
  | .inl child => .inconsistent child
  | .inr (.inl child) => .done child
  | .inr (.inr ⟨n, obs, body⟩) => .batch n.isLt obs body

def toCode : SatPlanData U O B L → Code U O B L
  | .inconsistent child => .inl child
  | .done child => .inr (.inl child)
  | .batch hn obs body => .inr (.inr ⟨⟨_, hn⟩, obs, body⟩)

@[simp] theorem ofCode_toCode (d : SatPlanData U O B L) : ofCode (toCode d) = d := by
  cases d <;> rfl

instance : DecidableEq (SatPlanData U O B L) := fun a b =>
  if h : toCode a = toCode b then
    isTrue (by have := congrArg ofCode h; simpa [ofCode_toCode] using this)
  else
    isFalse fun heq => h (by cases heq; rfl)

instance : Fintype (SatPlanData U O B L) :=
  Fintype.ofSurjective ofCode fun d => ⟨toCode d, ofCode_toCode d⟩

instance : Finite (SatPlanData U O B L) := inferInstance

def deps : SatPlanData U O B L → List (SearchKey U O B L)
  | .inconsistent child => [child]
  | .done child => [child]
  | .batch _ obs body => List.ofFn obs ++ [body]

@[simp] theorem deps_done (c : SearchKey U O B L) :
    (done c : SatPlanData U O B L).deps = [c] := rfl

@[simp] theorem deps_inconsistent (c : SearchKey U O B L) :
    (inconsistent c : SatPlanData U O B L).deps = [c] := rfl

end SatPlanData

/-! ### Plan validity -/

namespace SatPlan

def sameSupports (p c : SearchKey U O B L) : Bool :=
  decide (c.state = p.state) &&
    decide (c.coverage = p.coverage) &&
      decide (rawVals c.rawSupport = rawVals p.rawSupport) &&
        decide (c.depSupport = p.depSupport)

def obsObligation? (obs : SearchKey U O B L) : Option (Obligation U O) :=
  match obs.judgment with
  | .sNeg N =>
      match N.val with
      | .shift Q => if hQ : Q ∈ U.pos then some ⟨⟨Q, hQ⟩, obs.depSupport⟩ else none
      | .one | .prod _ _ | .arr _ _ => none
  | .sPos _ | .sInv _ _ | .sat _ => none

def obsValidB (parent obs : SearchKey U O B L) : Bool :=
  match obs.judgment with
  | .sNeg N =>
      match N.val with
      | .shift Q =>
          if hQ : Q ∈ U.pos then
            let obl : Obligation U O := ⟨⟨Q, hQ⟩, obs.depSupport⟩
            decide (Q ≠ .zero) &&
              decide (obs.state = parent.state) &&
              decide (obs.coverage = parent.coverage) &&
                obs.usesCurrent &&
                  decide (obl ∉ parent.coverage) &&
                    !StrongAt.decideB parent.state Q obs.depSupport
          else false
      | .one | .prod _ _ | .arr _ _ => false
  | .sPos _ | .sInv _ _ | .sat _ => false

theorem obsValid_no_fabricate {parent obs : SearchKey U O B L}
    (h : obsValidB parent obs = true) :
    ∃ Q : Pos sig.nBases, Q ∈ U.pos ∧ Neg.shift Q ∈ U.neg := by
  cases hj : obs.judgment with
  | sNeg N =>
      cases hN : N.val with
      | shift Q =>
          if hQ : Q ∈ U.pos then
            refine ⟨Q, hQ, ?_⟩
            have : N.val = Neg.shift Q := by simp [hN]
            simpa [← this] using N.property
          else
            simp [obsValidB, hj, hN, hQ] at h
      | one | prod _ _ | arr _ _ =>
          simp [obsValidB, hj, hN] at h
  | sPos _ | sInv _ _ | sat _ =>
      simp [obsValidB, hj] at h

def obsObligationList {n : Nat} (obs : Fin (n + 1) → SearchKey U O B L) :
    List (Option (Obligation U O)) :=
  List.ofFn fun i => obsObligation? (obs i)

def obligationsReady {n : Nat} (obs : Fin (n + 1) → SearchKey U O B L) : Bool :=
  (obsObligationList obs).all Option.isSome

def obligationsGet {n : Nat} (obs : Fin (n + 1) → SearchKey U O B L) :
    List (Obligation U O) :=
  (obsObligationList obs).filterMap id

def unionObsRaw {n : Nat} (obs : Fin (n + 1) → SearchKey U O B L) : Finset Nat :=
  (Finset.univ : Finset (Fin (n + 1))).sup fun i => rawVals (obs i).rawSupport

def unionObsDep {n : Nat} (obs : Fin (n + 1) → SearchKey U O B L) : DepSupport O :=
  (Finset.univ : Finset (Fin (n + 1))).sup fun i => (obs i).depSupport

def bodyValidB {n : Nat} (parent : SearchKey U O B L) (P : UPos U)
    (obs : Fin (n + 1) → SearchKey U O B L) (body : SearchKey U O B L) : Bool :=
  let obls := obligationsGet obs
  let pending := ResolvedPending.pendingFromObligations
    (obls.map fun o => (o.result, o.support))
  decide (body.state = parent.state.resetRound) &&
    decide (body.coverage = parent.coverage ∪ obls.toFinset) &&
      match body.judgment with
      | .sInv bp g =>
          decide (bp.val = pending) &&
            decide (g = UGoal.pos P) &&
              decide (rawVals parent.rawSupport =
                unionObsRaw obs ∪ rawVals body.rawSupport) &&
                decide (parent.depSupport =
                  unionObsDep obs ∪ body.depSupport)
      | .sNeg _ | .sPos _ | .sat _ => false

def doneValidB (parent child : SearchKey U O B L) : Bool :=
  match parent.judgment, child.judgment with
  | .sat P, .sPos P' => decide (P = P') && sameSupports parent child
  | _, _ => false

def inconsistentValidB (parent child : SearchKey U O B L) : Bool :=
  match parent.judgment, child.judgment with
  | .sat _, .sNeg N =>
      decide (N.val = Neg.shift (.zero : Pos sig.nBases)) && sameSupports parent child
  | _, _ => false

def allObsValidB {n : Nat} (parent : SearchKey U O B L)
    (obs : Fin (n + 1) → SearchKey U O B L) : Bool :=
  decide (∀ i : Fin (n + 1), obsValidB parent (obs i) = true)

def validB (parent : SearchKey U O B L) : SatPlanData U O B L → Bool
  | .inconsistent child =>
      match parent.judgment with
      | .sat _ => inconsistentValidB parent child
      | .sNeg _ | .sPos _ | .sInv _ _ => false
  | .done child =>
      match parent.judgment with
      | .sat _ => doneValidB parent child
      | .sNeg _ | .sPos _ | .sInv _ _ => false
  | .batch _ obs body =>
      match parent.judgment with
      | .sat P =>
          allObsValidB parent obs &&
            obligationsReady obs &&
              decide (obligationsGet obs).Nodup &&
                bodyValidB parent P obs body
      | .sNeg _ | .sPos _ | .sInv _ _ => false

end SatPlan

structure SatPlan (parent : SearchKey U O B L) where
  data : SatPlanData U O B L
  valid : SatPlan.validB parent data = true

namespace SatPlan

variable {parent : SearchKey U O B L}

theorem ext {a b : SatPlan parent} (h : a.data = b.data) : a = b := by
  cases a; cases b; cases h; rfl

instance : DecidableEq (SatPlan parent) := fun a b =>
  if h : a.data = b.data then isTrue (ext h)
  else isFalse fun heq => h (congrArg SatPlan.data heq)

def deps (p : SatPlan parent) : List (SearchKey U O B L) := p.data.deps

abbrev Code (parent : SearchKey U O B L) : Type :=
  { d : SatPlanData U O B L // SatPlan.validB parent d = true }

def ofCode (c : Code parent) : SatPlan parent := ⟨c.1, c.2⟩
def toCode (p : SatPlan parent) : Code parent := ⟨p.data, p.valid⟩

@[simp] theorem ofCode_toCode (p : SatPlan parent) : ofCode (toCode p) = p := rfl

instance : Fintype (Code parent) := by
  classical
  infer_instance

instance : Fintype (SatPlan parent) :=
  Fintype.ofSurjective ofCode fun p => ⟨toCode p, ofCode_toCode p⟩

instance : Finite (SatPlan parent) := inferInstance

theorem done_one_pos_dep (child : SearchKey U O B L)
    (hv : validB parent (.done child) = true) :
    (SatPlanData.done child : SatPlanData U O B L).deps = [child] ∧
      ∃ P : UPos U, parent.judgment = .sat P ∧ child.judgment = .sPos P := by
  cases hp : parent.judgment with
  | sat P =>
      cases hc : child.judgment with
      | sPos P' =>
          have heq : P = P' := by
            simp [validB, doneValidB, hp, hc, Bool.and_eq_true] at hv
            exact hv.1
          -- `cases` rewrites judgment equalities in the goal.
          exact ⟨rfl, ⟨P, rfl, congrArg SearchJudgment.sPos heq.symm⟩⟩
      | sNeg _ | sInv _ _ | sat _ =>
          simp [validB, doneValidB, hp, hc] at hv
  | sNeg _ | sPos _ | sInv _ _ =>
      simp [validB, hp] at hv

end SatPlan

/-! ### Fixed policies -/

structure SatPolicy (U : SearchUniverse sig) (O : Type) (B L : Nat)
    [DecidableEq O] [Fintype O] where
  choose : ∀ (parent : SearchKey U O B L) (P : UPos U),
    parent.judgment = .sat P → SatPlan parent

inductive PolicyAlt (π : SatPolicy U O B L) : SearchKey U O B L → Type where
  | structural {k} (h : ¬ isSaturated k) (a : StructuralAlternative k) : PolicyAlt π k
  | saturation {k} (P : UPos U) (h : k.judgment = .sat P) : PolicyAlt π k

namespace PolicyAlt

variable {π : SatPolicy U O B L}

def deps {k : SearchKey U O B L} : PolicyAlt π k → List (SearchKey U O B L)
  | .structural _ a => a.deps.toList
  | .saturation P h => (π.choose k P h).deps

instance (k : SearchKey U O B L) : DecidableEq (PolicyAlt π k) := fun a b =>
  match a, b with
  | .structural _ a₁, .structural _ a₂ =>
      if h : a₁ = a₂ then isTrue (by cases h; rfl)
      else isFalse fun heq => by cases heq; exact h rfl
  | .saturation P₁ h₁, .saturation P₂ h₂ =>
      isTrue (by
        have : P₁ = P₂ := by cases h₁.symm.trans h₂; rfl
        cases this; rfl)
  | .structural _ _, .saturation _ _ | .saturation _ _, .structural _ _ =>
      isFalse fun heq => nomatch heq

instance (k : SearchKey U O B L) : Fintype (PolicyAlt π k) := by
  classical
  match hk : k.judgment with
  | .sat P =>
      letI : Unique (PolicyAlt π k) :=
        { default := .saturation (π := π) P hk
          uniq := by
            intro a
            cases a with
            | structural hn _ => exact (hn ⟨P, hk⟩).elim
            | saturation P' h' =>
                have : P' = P := by cases h'.symm.trans hk; rfl
                cases this; rfl }
      infer_instance
  | .sNeg _ | .sPos _ | .sInv _ _ =>
      have hn : ¬ isSaturated k := by
        intro ⟨_, h⟩; simp [hk] at h
      exact Fintype.ofBijective
        (fun a : StructuralAlternative k => .structural (π := π) hn a)
        ⟨fun _ _ h => by cases h; rfl, fun a => by
          cases a with
          | structural _ a => exact ⟨a, rfl⟩
          | saturation _ h => simp [hk] at h⟩

end PolicyAlt

def policyAlternativeSystem (π : SatPolicy U O B L) :
    AlternativeSystem (SearchKey U O B L) where
  Alt := PolicyAlt π
  instDecidableEq := fun _ => inferInstance
  instFintype := fun _ => inferInstance
  deps := fun {_} a => PolicyAlt.deps a

/-! ### Regression gates -/

namespace SatPlanGates

open SatPlan

theorem done_one_positive_dependency {parent child : SearchKey U O B L}
    (hv : validB parent (.done child) = true) :
    (SatPlanData.done child : SatPlanData U O B L).deps = [child] ∧
      ∃ P, parent.judgment = .sat P ∧ child.judgment = .sPos P :=
  SatPlan.done_one_pos_dep (parent := parent) child hv

theorem same_Q_distinct_K_permitted (Q : UPos U) (K₁ K₂ : DepSupport O)
    (hne : K₁ ≠ K₂) :
    (⟨Q, K₁⟩ : Obligation U O) ≠ ⟨Q, K₂⟩ :=
  obligation_same_P_distinct_K Q K₁ K₂ hne

theorem duplicate_exact_list {n : Nat}
    (obs : Fin (n + 1) → SearchKey U O B L) (o : Obligation U O)
    (h : ∀ i, obsObligation? (obs i) = some o) :
    obligationsGet obs = List.replicate (n + 1) o := by
  simp only [obligationsGet, obsObligationList]
  have hfun : (fun i : Fin (n + 1) => obsObligation? (obs i)) = fun _ => some o :=
    funext h
  rw [hfun, List.ofFn_const]
  exact List.filterMap_replicate_of_some (f := id) rfl

theorem duplicate_rejected_when_n_ge_one {n : Nat} (hn : 0 < n)
    (obs : Fin (n + 1) → SearchKey U O B L) (o : Obligation U O)
    (h : ∀ i, obsObligation? (obs i) = some o) :
    ¬ (obligationsGet obs).Nodup := by
  rw [duplicate_exact_list obs o h, List.nodup_replicate]
  omega

theorem old_strong_distinct_K (x₀ z : O)
    (hne : ({x₀} : DepSupport O) ≠ ({z} : DepSupport O)) :
    ({x₀} : DepSupport O) ≠ ({z} : DepSupport O) :=
  hne

theorem exact_strong_blocks (st : ResolvedState U O B)
    (X : Pos sig.nBases) (K : DepSupport O) (h : StrongAt st X K) :
    StrongAt.decideB st X K = true :=
  StrongAt.decideB_of_strong st h

theorem exact_strong_blocks_obs {parent obs : SearchKey U O B L}
    {Q : Pos sig.nBases} {K : DepSupport O}
    (hStrong : StrongAt parent.state Q K)
    (hDep : obs.depSupport = K)
    (_hJudg : ∃ N : UNeg U, obs.judgment = .sNeg N ∧ N.val = .shift Q)
    (_hQ : Q ∈ U.pos) :
    obsValidB parent obs = false ∨ StrongAt.decideB parent.state Q obs.depSupport = true := by
  right
  simpa [hDep] using StrongAt.decideB_of_strong parent.state hStrong

/--
Old `StrongAt` at a distinct support does not block: `obsValidB` tests
exact candidate support `Knew`, not a prior `Kold`.
-/
theorem obsValidB_of_exact_candidate_support {parent obs : SearchKey U O B L}
    {Q : Pos sig.nBases} {N : UNeg U} {Kold Knew : DepSupport O}
    (_hOld : StrongAt parent.state Q Kold)
    (_hne : Kold ≠ Knew)
    (hDep : obs.depSupport = Knew)
    (hJudg : obs.judgment = .sNeg N)
    (hN : N.val = .shift Q)
    (hQ : Q ∈ U.pos)
    (hQ0 : Q ≠ .zero)
    (hState : obs.state = parent.state)
    (hCov : obs.coverage = parent.coverage)
    (hUses : obs.usesCurrent = true)
    (hObl : (⟨⟨Q, hQ⟩, Knew⟩ : Obligation U O) ∉ parent.coverage)
    (hNotStrong : ¬ StrongAt parent.state Q Knew) :
    obsValidB parent obs = true := by
  have hDec : StrongAt.decideB parent.state Q Knew = false := by
    rw [Bool.eq_false_iff, Ne, StrongAt.decideB_iff]
    exact hNotStrong
  unfold obsValidB
  simp only [hJudg, hN, hQ, dite_true, hDep]
  have hNz : decide (Q ≠ .zero) = true := decide_eq_true hQ0
  have hSt : decide (obs.state = parent.state) = true := decide_eq_true hState
  have hCv : decide (obs.coverage = parent.coverage) = true := decide_eq_true hCov
  have hOb : decide
      ((⟨⟨Q, hQ⟩, Knew⟩ : Obligation U O) ∉ parent.coverage) = true :=
    decide_eq_true hObl
  simp only [hNz, hSt, hCv, hUses, hOb, hDec, Bool.not_false, Bool.and_self]

theorem obsValidB_result_ne_zero {parent obs : SearchKey U O B L}
    (h : obsValidB parent obs = true) :
    ∃ Q : Pos sig.nBases, Q ∈ U.pos ∧ Q ≠ .zero ∧
      ∃ N : UNeg U, obs.judgment = .sNeg N ∧ N.val = .shift Q := by
  cases hj : obs.judgment with
  | sNeg N =>
      cases hN : N.val with
      | shift Q =>
          if hQ : Q ∈ U.pos then
            have hall := h
            simp [obsValidB, hj, hN, hQ, Bool.and_eq_true,
              decide_eq_true_eq] at hall
            exact ⟨Q, hQ, hall.1.1.1.1.1, N, rfl, hN⟩
          else
            simp [obsValidB, hj, hN, hQ] at h
      | one | prod _ _ | arr _ _ =>
          simp [obsValidB, hj, hN] at h
  | sPos _ | sInv _ _ | sat _ =>
      simp [obsValidB, hj] at h

theorem inconsistent_one_zero_dependency {parent child : SearchKey U O B L}
    (hv : validB parent (.inconsistent child) = true) :
    (SatPlanData.inconsistent child : SatPlanData U O B L).deps = [child] ∧
      (∃ P : UPos U, parent.judgment = .sat P) ∧
      (∃ N : UNeg U, child.judgment = .sNeg N ∧
        N.val = .shift (.zero : Pos sig.nBases)) ∧
      sameSupports parent child = true := by
  cases hp : parent.judgment with
  | sat P =>
      cases hc : child.judgment with
      | sNeg N =>
          simp [validB, inconsistentValidB, hp, hc, Bool.and_eq_true] at hv
          exact ⟨rfl, ⟨P, rfl⟩, ⟨N, rfl, hv.1⟩, hv.2⟩
      | sPos _ | sInv _ _ | sat _ =>
          simp [validB, inconsistentValidB, hp, hc] at hv
  | sNeg _ | sPos _ | sInv _ _ =>
      simp [validB, hp] at hv

theorem zero_observation_rejected {parent obs : SearchKey U O B L}
    {N : UNeg U}
    (hJudg : obs.judgment = .sNeg N)
    (hN : N.val = .shift (.zero : Pos sig.nBases)) :
    obsValidB parent obs = false := by
  simp [obsValidB, hJudg, hN]

theorem inconsistent_same_frame {parent child : SearchKey U O B L}
    (hv : validB parent (.inconsistent child) = true) :
    child.state = parent.state ∧
      child.coverage = parent.coverage ∧
      rawVals child.rawSupport = rawVals parent.rawSupport ∧
      child.depSupport = parent.depSupport := by
  obtain ⟨_, _, _, hsame⟩ := inconsistent_one_zero_dependency hv
  simp [sameSupports, Bool.and_eq_true, decide_eq_true_eq] at hsame
  exact ⟨hsame.1.1.1, hsame.1.1.2, hsame.1.2, hsame.2⟩

theorem batch_body_reset {n : Nat} {parent : SearchKey U O B L} {P : UPos U}
    {obs : Fin (n + 1) → SearchKey U O B L} {body : SearchKey U O B L}
    (hb : bodyValidB parent P obs body = true) :
    body.state = parent.state.resetRound ∧
      body.coverage = parent.coverage ∪ (obligationsGet obs).toFinset := by
  have h := hb
  simp only [bodyValidB, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1, of_decide_eq_true h.1.2⟩

theorem no_fabricate_missing_shift {parent obs : SearchKey U O B L}
    (h : obsValidB parent obs = true) :
    ∃ Q : Pos sig.nBases, Q ∈ U.pos ∧ Neg.shift Q ∈ U.neg :=
  SatPlan.obsValid_no_fabricate (parent := parent) h

theorem nonsat_policy_agrees_structural (π : SatPolicy U O B L)
    (k : SearchKey U O B L) (h : ¬ isSaturated k)
    (a : StructuralAlternative k) :
    PolicyAlt.deps (.structural (π := π) h a) = a.deps.toList :=
  rfl

theorem saturated_exposes_policy_plan (π : SatPolicy U O B L)
    (k : SearchKey U O B L) (P : UPos U) (h : k.judgment = .sat P) :
    PolicyAlt.deps (.saturation (π := π) P h) = (π.choose k P h).deps :=
  rfl

theorem saturated_alt_unique (π : SatPolicy U O B L)
    (k : SearchKey U O B L) (P : UPos U) (h : k.judgment = .sat P)
    (a : PolicyAlt π k) :
    a = .saturation P h := by
  cases a with
  | structural hn _ => exact (hn ⟨P, h⟩).elim
  | saturation P' h' =>
      cases show P' = P by cases h'.symm.trans h; rfl
      rfl

end SatPlanGates

/-! ### Fixtures -/

namespace SearchSatPolicyFixtures

open SearchUniverseFixtures SearchKeyFixtures SatPlan

abbrev O2 := Fin 2
instance : DecidableEq O2 := inferInstanceAs (DecidableEq (Fin 2))
instance : Fintype O2 := inferInstanceAs (Fintype (Fin 2))
def x₀ : O2 := ⟨0, by decide⟩
def z : O2 := ⟨1, by decide⟩

theorem fixture_same_Q_distinct_K :
    (⟨P0, ({x₀} : DepSupport O2)⟩ : Obligation Uz O2) ≠
      ⟨P0, ({z} : DepSupport O2)⟩ :=
  SatPlanGates.same_Q_distinct_K_permitted (U := Uz) (O := O2) P0 {x₀} {z} (by decide)

theorem fixture_old_strong_does_not_identify_K :
    ({x₀} : DepSupport O2) ≠ ({z} : DepSupport O2) := by
  decide

theorem fixture_exact_strong_blocks :
    ∀ (st : ResolvedState Uz O2 2),
      StrongAt st P0.val ({z} : DepSupport O2) →
        StrongAt.decideB st P0.val ({z} : DepSupport O2) = true :=
  fun _ h => SatPlanGates.exact_strong_blocks _ _ _ h

theorem fixture_strong_zero_impossible (st : ResolvedState Uz O2 2)
    (K : DepSupport O2) :
    ¬ StrongAt st (.zero : Pos 0) K :=
  StrongAt.not_zero st K

theorem fixture_done_shape (parent child : SearchKey Uz O1 1 1)
    (hv : validB parent (.done child) = true) :
    (SatPlanData.done child : SatPlanData Uz O1 1 1).deps = [child] ∧
      ∃ P, parent.judgment = .sat P ∧ child.judgment = .sPos P :=
  SatPlanGates.done_one_positive_dependency (parent := parent) hv

theorem fixture_inconsistent_shape (parent child : SearchKey Uz O1 1 1)
    (hv : validB parent (.inconsistent child) = true) :
    (SatPlanData.inconsistent child : SatPlanData Uz O1 1 1).deps = [child] ∧
      (∃ P, parent.judgment = .sat P) ∧
      (∃ N, child.judgment = .sNeg N ∧ N.val = .shift (.zero : Pos 0)) ∧
      child.state = parent.state ∧
      child.coverage = parent.coverage ∧
      rawVals child.rawSupport = rawVals parent.rawSupport ∧
      child.depSupport = parent.depSupport := by
  obtain ⟨hdeps, hparent, hchild, _⟩ :=
    SatPlanGates.inconsistent_one_zero_dependency hv
  exact ⟨hdeps, hparent, hchild, SatPlanGates.inconsistent_same_frame hv⟩

theorem fixture_no_zero_batch_observation {parent obs : SearchKey Uz O1 1 1}
    {N : UNeg Uz}
    (hJudg : obs.judgment = .sNeg N)
    (hN : N.val = .shift (.zero : Pos 0)) :
    obsValidB parent obs = false :=
  SatPlanGates.zero_observation_rejected hJudg hN

theorem fixture_no_fabricate {parent obs : SearchKey Uz O1 1 1}
    (h : obsValidB parent obs = true) :
    ∃ Q, Q ∈ Uz.pos ∧ Neg.shift Q ∈ Uz.neg :=
  SatPlanGates.no_fabricate_missing_shift (parent := parent) h

theorem fixture_duplicate_rejected
    (obs₀ obs₁ : SearchKey Uz O2 2 2) (o : Obligation Uz O2)
    (h₀ : obsObligation? obs₀ = some o) (h₁ : obsObligation? obs₁ = some o) :
    ¬ (obligationsGet (n := 1) (fun i : Fin 2 =>
        match i with | ⟨0, _⟩ => obs₀ | ⟨1, _⟩ => obs₁)).Nodup := by
  refine SatPlanGates.duplicate_rejected_when_n_ge_one (n := 1) (by decide) _ o ?_
  intro i
  match i with
  | ⟨0, _⟩ => exact h₀
  | ⟨1, _⟩ => exact h₁

theorem nonsat_agrees (π : SatPolicy Uz O1 1 1)
    (k : SearchKey Uz O1 1 1) (h : ¬ isSaturated k)
    (a : StructuralAlternative k) :
    PolicyAlt.deps (.structural (π := π) h a) = a.deps.toList :=
  SatPlanGates.nonsat_policy_agrees_structural π k h a

theorem sat_exposes (π : SatPolicy Uz O1 1 1)
    (k : SearchKey Uz O1 1 1) (P : UPos Uz) (h : k.judgment = .sat P) :
    PolicyAlt.deps (.saturation (π := π) P h) = (π.choose k P h).deps ∧
      ∀ a : PolicyAlt π k, a = .saturation P h :=
  ⟨SatPlanGates.saturated_exposes_policy_plan π k P h,
    SatPlanGates.saturated_alt_unique π k P h⟩

end SearchSatPolicyFixtures

end Gimbal.Equality.Scherer
