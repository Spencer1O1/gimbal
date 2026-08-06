/-
  Scherer-core resolved dependency support state.

  Raw levels remain oldest-first `Fin depth` indices. Resolved support ranges
  over a fixed finite origin type `O` and is independent of raw current-New
  eligibility. Batch-result binders get a fresh raw level but inherit resolved
  support; lexical/local binders push with empty resolved support.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fin.Tuple.Basic
import Gimbal.Equality.Scherer.SearchUniverse
import Gimbal.Equality.Scherer.StrongRetrieval

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Dependency support -/

/-- Finite set of resolved dependency origins. -/
abbrev DepSupport (O : Type) : Type :=
  Finset O

instance {O : Type} [DecidableEq O] : DecidableEq (DepSupport O) :=
  inferInstance

instance {O : Type} [DecidableEq O] [Fintype O] : Fintype (DepSupport O) :=
  inferInstanceAs (Fintype (Finset O))

instance {O : Type} [Fintype O] : Finite (DepSupport O) :=
  inferInstanceAs (Finite (Finset O))

/-- When only `Finite O` is known, finiteness of `DepSupport` is available
(noncomputable via `Fintype.ofFinite`). Unbounded contexts are not claimed finite. -/
noncomputable instance {O : Type} [Finite O] : Finite (DepSupport O) := by
  letI := Fintype.ofFinite O
  infer_instance

/-! ### Bounded resolved state -/

/--
Bounded abstract context carrying resolved dependency support.

* Levels are oldest-first: `0` is oldest, `depth - 1` is newest.
* `currentRaw` is the suffix of levels with index `≥ roundStart`.
* Bound `B` is hard capacity; states with unlimited depth are not finite.
-/
structure ResolvedState (U : SearchUniverse sig) (O : Type) (B : Nat) where
  depth : Nat
  depth_le : depth ≤ B
  tyAt : Fin depth → UStable U
  depAt : Fin depth → DepSupport O
  roundStart : Nat
  round_le : roundStart ≤ depth

namespace ResolvedState

variable {U : SearchUniverse sig} {O : Type} {B : Nat}

/-- Empty root state. -/
def empty (U : SearchUniverse sig) (O : Type) (B : Nat) : ResolvedState U O B where
  depth := 0
  depth_le := Nat.zero_le _
  tyAt := Fin.elim0
  depAt := Fin.elim0
  roundStart := 0
  round_le := le_rfl

/-- Raw levels at or after `roundStart` (current-round suffix). -/
def currentRaw (st : ResolvedState U O B) : Finset (Fin st.depth) :=
  (Finset.univ : Finset (Fin st.depth)).filter fun i => st.roundStart ≤ (i : Nat)

/-- Keep depth/types/supports; clear current-raw via `roundStart := depth`. -/
def resetRound (st : ResolvedState U O B) : ResolvedState U O B where
  depth := st.depth
  depth_le := st.depth_le
  tyAt := st.tyAt
  depAt := st.depAt
  roundStart := st.depth
  round_le := le_rfl

/-- Append one binder with resolved support `K` (requires spare capacity). -/
def push (st : ResolvedState U O B) (h : st.depth < B)
    (S : UStable U) (K : DepSupport O) : ResolvedState U O B where
  depth := st.depth + 1
  depth_le := Nat.succ_le_of_lt h
  tyAt := Fin.snoc st.tyAt S
  depAt := Fin.snoc st.depAt K
  roundStart := st.roundStart
  round_le := Nat.le_succ_of_le st.round_le

/-- Lexical / lambda / local binder: fresh raw level, empty resolved support. -/
def pushLexical (st : ResolvedState U O B) (h : st.depth < B) (S : UStable U) :
    ResolvedState U O B :=
  st.push h S ∅

/-- Batch-result binder: fresh raw level, inherited resolved support `K`. -/
def pushResolved (st : ResolvedState U O B) (h : st.depth < B)
    (S : UStable U) (K : DepSupport O) : ResolvedState U O B :=
  st.push h S K

/-! ### Push / reset gates -/

@[simp] theorem resetRound_depth (st : ResolvedState U O B) :
    (st.resetRound).depth = st.depth := rfl

@[simp] theorem resetRound_depAt (st : ResolvedState U O B) :
    (st.resetRound).depAt = st.depAt := rfl

@[simp] theorem resetRound_tyAt (st : ResolvedState U O B) :
    (st.resetRound).tyAt = st.tyAt := rfl

theorem currentRaw_resetRound_empty (st : ResolvedState U O B) :
    (st.resetRound).currentRaw = ∅ := by
  ext i
  constructor
  · intro hi
    have := (Finset.mem_filter.mp hi).2
    exact (not_le_of_gt i.isLt this).elim
  · intro hi
    exact (Finset.notMem_empty i hi).elim

@[simp] theorem push_depth (st : ResolvedState U O B) (h : st.depth < B)
    (S : UStable U) (K : DepSupport O) :
    (st.push h S K).depth = st.depth + 1 := rfl

@[simp] theorem push_roundStart (st : ResolvedState U O B) (h : st.depth < B)
    (S : UStable U) (K : DepSupport O) :
    (st.push h S K).roundStart = st.roundStart := rfl

theorem push_old_type (st : ResolvedState U O B) (h : st.depth < B)
    (S : UStable U) (K : DepSupport O) (i : Fin st.depth) :
    (st.push h S K).tyAt i.castSucc = st.tyAt i := by
  simp [push]

theorem push_old_support (st : ResolvedState U O B) (h : st.depth < B)
    (S : UStable U) (K : DepSupport O) (i : Fin st.depth) :
    (st.push h S K).depAt i.castSucc = st.depAt i := by
  simp [push]

theorem push_new_type (st : ResolvedState U O B) (h : st.depth < B)
    (S : UStable U) (K : DepSupport O) :
    (st.push h S K).tyAt (Fin.last st.depth) = S := by
  simp [push]

theorem push_new_support (st : ResolvedState U O B) (h : st.depth < B)
    (S : UStable U) (K : DepSupport O) :
    (st.push h S K).depAt (Fin.last st.depth) = K := by
  simp [push]

theorem push_new_current (st : ResolvedState U O B) (h : st.depth < B)
    (S : UStable U) (K : DepSupport O) :
    Fin.last st.depth ∈ (st.push h S K).currentRaw := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  simp only [push, Fin.val_last]
  exact st.round_le

@[simp] theorem pushLexical_new_support_empty (st : ResolvedState U O B)
    (h : st.depth < B) (S : UStable U) :
    (st.pushLexical h S).depAt (Fin.last st.depth) = ∅ :=
  push_new_support st h S ∅

@[simp] theorem pushResolved_new_support (st : ResolvedState U O B)
    (h : st.depth < B) (S : UStable U) (K : DepSupport O) :
    (st.pushResolved h S K).depAt (Fin.last st.depth) = K :=
  push_new_support st h S K

end ResolvedState

/-! ### DecidableEq / Fintype for bounded states -/

/-- Proof-erased code for decidable equality and finiteness. -/
abbrev ResolvedStateCode (U : SearchUniverse sig) (O : Type) (B : Nat) : Type :=
  Σ d : Fin (B + 1), (Fin d.val → UStable U × DepSupport O) × Fin (d.val + 1)

namespace ResolvedStateCode

variable {U : SearchUniverse sig} {O : Type} {B : Nat}

def ofState (st : ResolvedState U O B) : ResolvedStateCode U O B :=
  ⟨⟨st.depth, Nat.lt_succ_of_le st.depth_le⟩,
    fun i => (st.tyAt i, st.depAt i),
    ⟨st.roundStart, Nat.lt_succ_of_le st.round_le⟩⟩

def toState (c : ResolvedStateCode U O B) : ResolvedState U O B where
  depth := c.1.val
  depth_le := Nat.le_of_lt_succ c.1.isLt
  tyAt := fun i => (c.2.1 i).1
  depAt := fun i => (c.2.1 i).2
  roundStart := c.2.2.val
  round_le := Nat.le_of_lt_succ c.2.2.isLt

@[simp] theorem toState_ofState (st : ResolvedState U O B) :
    toState (ofState st) = st := by
  cases st
  rfl

end ResolvedStateCode

instance {U : SearchUniverse sig} {O : Type} {B : Nat} [DecidableEq O] :
    DecidableEq (ResolvedStateCode U O B) :=
  inferInstance

instance {U : SearchUniverse sig} {O : Type} {B : Nat} [DecidableEq O] :
    DecidableEq (ResolvedState U O B) := fun a b =>
  if h : ResolvedStateCode.ofState a = ResolvedStateCode.ofState b then
    isTrue (by
      have := congrArg ResolvedStateCode.toState h
      simpa [ResolvedStateCode.toState_ofState] using this)
  else
    isFalse fun heq => h (by cases heq; rfl)

instance {U : SearchUniverse sig} {O : Type} {B : Nat}
    [DecidableEq O] [Fintype O] : Fintype (ResolvedStateCode U O B) := by
  classical
  infer_instance

instance {U : SearchUniverse sig} {O : Type} {B : Nat}
    [DecidableEq O] [Fintype O] : Fintype (ResolvedState U O B) :=
  Fintype.ofSurjective ResolvedStateCode.toState fun st =>
    ⟨ResolvedStateCode.ofState st, ResolvedStateCode.toState_ofState st⟩

instance {U : SearchUniverse sig} {O : Type} {B : Nat}
    [DecidableEq O] [Fintype O] : Finite (ResolvedState U O B) :=
  inferInstance

/-- Finite when `O` is merely `Finite` (via `Fintype.ofFinite`; not a claim that
unbounded contexts are finite). -/
noncomputable instance {U : SearchUniverse sig} {O : Type} {B : Nat}
    [Finite O] : Finite (ResolvedState U O B) := by
  letI := Fintype.ofFinite O
  letI : DecidableEq O := Classical.decEq O
  infer_instance

/-! ### Resolved pending -/

/-- Pending entry annotated with resolved dependency support. -/
structure PendingCell (U : SearchUniverse sig) (O : Type) where
  ty : UPos U
  support : DepSupport O
  deriving DecidableEq

/-- Ordered pending telescope (list head = oldest pending). -/
abbrev ResolvedPending (U : SearchUniverse sig) (O : Type) : Type :=
  List (PendingCell U O)

namespace ResolvedPending

variable {U : SearchUniverse sig} {O : Type}

/-- Erase resolved annotations to intrinsic `Pending`. -/
def erase : ResolvedPending U O → Pending sig
  | [] => .empty
  | c :: rest => .cons c.ty.val (erase rest)

@[simp] theorem erase_nil :
    erase ([] : ResolvedPending U O) = .empty := rfl

@[simp] theorem erase_cons (c : PendingCell U O) (rest : ResolvedPending U O) :
    erase (c :: rest) = .cons c.ty.val (erase rest) := rfl

/-- Lambda pending: single obligation with empty resolved support. -/
def lambdaPending (P : UPos U) : ResolvedPending U O :=
  [⟨P, ∅⟩]

@[simp] theorem erase_lambdaPending (P : UPos U) :
    erase (lambdaPending (O := O) P) = .cons P.val .empty := rfl

theorem lambdaPending_support_empty (P : UPos U) :
    ∃ c, lambdaPending (O := O) P = [c] ∧ c.ty = P ∧ c.support = ∅ :=
  ⟨⟨P, ∅⟩, rfl, rfl, rfl⟩

/-- Replace pending-head sum by left component; preserve head support `K`. -/
def sumLeft (A B : Pos sig.nBases) (hA : A ∈ U.pos) :
    ResolvedPending U O → Option (ResolvedPending U O)
  | ⟨⟨.sum A' B', _⟩, K⟩ :: rest =>
      if _hEq : A' = A ∧ B' = B then
        some (⟨⟨A, hA⟩, K⟩ :: rest)
      else none
  | _ => none

/-- Replace pending-head sum by right component; preserve head support `K`. -/
def sumRight (A B : Pos sig.nBases) (hB : B ∈ U.pos) :
    ResolvedPending U O → Option (ResolvedPending U O)
  | ⟨⟨.sum A' B', _⟩, K⟩ :: rest =>
      if _hEq : A' = A ∧ B' = B then
        some (⟨⟨B, hB⟩, K⟩ :: rest)
      else none
  | _ => none

theorem sumLeft_preserves_support (A B : Pos sig.nBases) (hA : A ∈ U.pos)
    {K : DepSupport O} {rest : ResolvedPending U O}
    {hSum : Pos.sum A B ∈ U.pos} :
    sumLeft A B hA (⟨⟨.sum A B, hSum⟩, K⟩ :: rest) =
      some (⟨⟨A, hA⟩, K⟩ :: rest) := by
  simp [sumLeft]

theorem sumRight_preserves_support (A B : Pos sig.nBases) (hB : B ∈ U.pos)
    {K : DepSupport O} {rest : ResolvedPending U O}
    {hSum : Pos.sum A B ∈ U.pos} :
    sumRight A B hB (⟨⟨.sum A B, hSum⟩, K⟩ :: rest) =
      some (⟨⟨B, hB⟩, K⟩ :: rest) := by
  simp [sumRight]

/-- Build pending from exact `(P,K)` obligations; duplicate `P` with distinct `K` ok. -/
def pendingFromObligations :
    List (UPos U × DepSupport O) → ResolvedPending U O
  | [] => []
  | (P, K) :: rest => ⟨P, K⟩ :: pendingFromObligations rest

@[simp] theorem erase_pendingFromObligations :
    ∀ (obs : List (UPos U × DepSupport O)),
      erase (pendingFromObligations obs) =
        obs.foldr (fun pk acc => .cons pk.1.val acc) .empty
  | [] => rfl
  | _ :: rest => by
      simp only [pendingFromObligations, erase_cons, List.foldr,
        erase_pendingFromObligations rest]

theorem pendingFromObligations_supports :
    ∀ (obs : List (UPos U × DepSupport O)),
      (pendingFromObligations obs).map (·.support) = obs.map Prod.snd
  | [] => rfl
  | _ :: rest => by
      simp [pendingFromObligations, pendingFromObligations_supports rest]

theorem pendingFromObligations_allows_dup_P
    (P : UPos U) (K₁ K₂ : DepSupport O) (hne : K₁ ≠ K₂) :
    let ps := pendingFromObligations [(P, K₁), (P, K₂)]
    ps.length = 2 ∧ ps.map (·.ty) = [P, P] ∧
      ps.map (·.support) = [K₁, K₂] ∧ K₁ ≠ K₂ :=
  ⟨rfl, rfl, rfl, hne⟩

end ResolvedPending

/-! ### Abstract strong positive -/

/--
Abstract strong-positive pattern over a resolved state.
Leaves read `depAt`; injections preserve support. No zero / invertible shift.
-/
inductive RStrongPos {U : SearchUniverse sig} {O : Type} {B : Nat}
    (st : ResolvedState U O B) : Pos sig.nBases → Type where
  | negVar {N : Neg sig.nBases} (i : Fin st.depth)
      (hty : (st.tyAt i).val = .neg N) :
      RStrongPos st (.shift N)
  | atomVar {q : Fin sig.nBases} (i : Fin st.depth)
      (hty : (st.tyAt i).val = .atom q) :
      RStrongPos st (.atom q)
  | inl {P Q : Pos sig.nBases} : RStrongPos st P → RStrongPos st (.sum P Q)
  | inr {P Q : Pos sig.nBases} : RStrongPos st Q → RStrongPos st (.sum P Q)

namespace RStrongPos

variable {U : SearchUniverse sig} {O : Type} {B : Nat}
  {st : ResolvedState U O B}

/-- Resolved dependency support carried by an abstract strong pattern. -/
def depSupport {P : Pos sig.nBases} : RStrongPos st P → DepSupport O
  | .negVar i _ => st.depAt i
  | .atomVar i _ => st.depAt i
  | .inl sp => depSupport sp
  | .inr sp => depSupport sp

@[simp] theorem depSupport_negVar {N} (i : Fin st.depth)
    (hty : (st.tyAt i).val = .neg N) :
    (negVar (st := st) i hty).depSupport = st.depAt i := rfl

@[simp] theorem depSupport_atomVar {q} (i : Fin st.depth)
    (hty : (st.tyAt i).val = .atom q) :
    (atomVar (st := st) i hty).depSupport = st.depAt i := rfl

@[simp] theorem depSupport_inl {P Q} (sp : RStrongPos st P) :
    (inl (Q := Q) sp).depSupport = sp.depSupport := rfl

@[simp] theorem depSupport_inr {P Q} (sp : RStrongPos st Q) :
    (inr (P := P) sp).depSupport = sp.depSupport := rfl

end RStrongPos

/-- Exact-support strong retrieval at abstract state. -/
def StrongAt {U : SearchUniverse sig} {O : Type} {B : Nat}
    (st : ResolvedState U O B) (P : Pos sig.nBases) (K : DepSupport O) : Prop :=
  Nonempty { sp : RStrongPos st P // sp.depSupport = K }

namespace StrongAt

variable {U : SearchUniverse sig} {O : Type} {B : Nat}
  {st : ResolvedState U O B}

theorem of_negVar {N} (i : Fin st.depth)
    (hty : (st.tyAt i).val = .neg N) :
    StrongAt st (.shift N) (st.depAt i) :=
  ⟨⟨.negVar i hty, rfl⟩⟩

theorem of_atomVar {q} (i : Fin st.depth)
    (hty : (st.tyAt i).val = .atom q) :
    StrongAt st (.atom q) (st.depAt i) :=
  ⟨⟨.atomVar i hty, rfl⟩⟩

theorem of_inl {P Q K} (h : StrongAt st P K) : StrongAt st (.sum P Q) K := by
  rcases h with ⟨⟨sp, hsl⟩⟩
  exact ⟨⟨.inl sp, by simp [hsl]⟩⟩

theorem of_inr {P Q K} (h : StrongAt st Q K) : StrongAt st (.sum P Q) K := by
  rcases h with ⟨⟨sp, hsl⟩⟩
  exact ⟨⟨.inr sp, by simp [hsl]⟩⟩

/-- Exactness in `K`: rewriting the support label. -/
theorem exact {P K K'} (h : StrongAt st P K) (heq : K = K') :
    StrongAt st P K' :=
  heq ▸ h

/-- Distinct supports for the same `P` are not merged. -/
theorem distinct_supports {P : Pos sig.nBases} {K₁ K₂ : DepSupport O}
    (h₁ : StrongAt st P K₁) (h₂ : StrongAt st P K₂) (hne : K₁ ≠ K₂) :
    ∃ sp₁ : RStrongPos st P, ∃ sp₂ : RStrongPos st P,
      sp₁.depSupport = K₁ ∧ sp₂.depSupport = K₂ ∧
        sp₁.depSupport ≠ sp₂.depSupport := by
  rcases h₁ with ⟨⟨sp₁, hsl₁⟩⟩
  rcases h₂ with ⟨⟨sp₂, hsl₂⟩⟩
  exact ⟨sp₁, sp₂, hsl₁, hsl₂, by simp [hsl₁, hsl₂, hne]⟩

end StrongAt

/-! ### Regressions -/

namespace ResolvedSupportFixtures

def sig0 : Signature := ⟨0, #[]⟩
abbrev O1 := Fin 1
def xOrigin : O1 := ⟨0, Nat.zero_lt_one⟩

def U0 : SearchUniverse sig0 :=
  SearchUniverse.fromInputs
    (StableCtx.snoc (.empty : StableCtx sig0) (.neg (.shift .zero)))
    .empty (.pos (.shift .one)) []

def Sneg0 : UStable U0 :=
  ⟨.neg (.shift .zero),
    SearchUniverse.stable_of_context
      (Γ := StableCtx.snoc (.empty : StableCtx sig0) (.neg (.shift .zero)))
      .empty (.pos (.shift .one)) [] ⟨.here⟩⟩

/-- `resetRound` clears `currentRaw` but preserves every `depAt`. -/
theorem resetRound_clears_current_preserves_dep :
    let st0 := (ResolvedState.empty U0 O1 2).pushLexical (by decide) Sneg0
    let st1 := st0.pushResolved (by decide) Sneg0 ({xOrigin} : DepSupport O1)
    let stR := st1.resetRound
    stR.currentRaw = ∅ ∧ stR.depAt = st1.depAt :=
  ⟨ResolvedState.currentRaw_resetRound_empty _, ResolvedState.resetRound_depAt _⟩

/-- `pushLexical` has a fresh raw current level and resolved support `∅`. -/
theorem pushLexical_fresh_raw_empty_resolved :
    let st := (ResolvedState.empty U0 O1 1).pushLexical (by decide) Sneg0
    Fin.last 0 ∈ st.currentRaw ∧ st.depAt (Fin.last 0) = ∅ :=
  ⟨ResolvedState.push_new_current _ _ _ _,
    ResolvedState.pushLexical_new_support_empty _ _ _⟩

/-- `pushResolved K` has a fresh raw current level and resolved support `K`. -/
theorem pushResolved_fresh_raw_inherits_K :
    let K : DepSupport O1 := {xOrigin}
    let st := (ResolvedState.empty U0 O1 1).pushResolved (by decide) Sneg0 K
    Fin.last 0 ∈ st.currentRaw ∧ st.depAt (Fin.last 0) = K :=
  ⟨ResolvedState.push_new_current _ _ _ _,
    ResolvedState.pushResolved_new_support _ _ _ _⟩

def Kx : DepSupport O1 := {xOrigin}

def stLex : ResolvedState U0 O1 2 :=
  (ResolvedState.empty U0 O1 2).pushLexical (by decide) Sneg0

def stLexRes : ResolvedState U0 O1 2 :=
  stLex.pushResolved (by decide) Sneg0 Kx

/-- Same type with different resolved supports remains distinguishable. -/
theorem same_type_different_support_distinct :
    stLexRes.tyAt (0 : Fin 2) = Sneg0 ∧
      stLexRes.tyAt (1 : Fin 2) = Sneg0 ∧
      stLexRes.depAt (0 : Fin 2) = ∅ ∧
      stLexRes.depAt (1 : Fin 2) = Kx := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- level 0 is the lexical push
    have hL := ResolvedState.push_new_type
      (ResolvedState.empty U0 O1 2) (by decide) Sneg0 (∅ : DepSupport O1)
    have h0 := ResolvedState.push_old_type stLex (by decide) Sneg0 Kx (0 : Fin 1)
    simp only [stLexRes, stLex, ResolvedState.pushLexical, ResolvedState.pushResolved]
      at hL h0 ⊢
    exact h0.trans hL
  · exact ResolvedState.push_new_type stLex (by decide) Sneg0 Kx
  · have h := ResolvedState.push_old_support stLex (by decide) Sneg0 Kx (0 : Fin 1)
    have hL := ResolvedState.pushLexical_new_support_empty
      (ResolvedState.empty U0 O1 2) (by decide) Sneg0
    simp only [stLexRes, stLex, ResolvedState.pushLexical, ResolvedState.pushResolved]
      at h hL ⊢
    exact h.trans hL
  · exact ResolvedState.pushResolved_new_support stLex (by decide) Sneg0 Kx

def stX : ResolvedState U0 O1 3 :=
  (ResolvedState.empty U0 O1 3).pushResolved (by decide) Sneg0 Kx

def stXQ : ResolvedState U0 O1 3 :=
  stX.pushResolved (by decide) Sneg0 Kx

/--
Abstract `X → Q → X`: a `Q` result inheriting `{x}` later supplies
`StrongAt ↓(¬↓0)` `{x}` from the original binder; no new resolved origin appears.
-/
theorem x_to_q_to_x_inherits_no_new_origin :
    StrongAt stXQ (Pos.shift (Neg.shift (.zero : Pos 0))) Kx ∧
      stXQ.depAt ⟨0, by decide⟩ = Kx ∧
      stXQ.depAt ⟨1, by decide⟩ = Kx := by
  refine ⟨?_, ?_, ?_⟩
  · have hty : (stXQ.tyAt ⟨0, by decide⟩).val =
        StableTy.neg (Neg.shift (.zero : Pos 0)) := by
      have h0 := ResolvedState.push_old_type stX (by decide) Sneg0 Kx ⟨0, by decide⟩
      have hL := ResolvedState.push_new_type
        (ResolvedState.empty U0 O1 3) (by decide) Sneg0 Kx
      simp only [stXQ, stX, ResolvedState.pushResolved, Sneg0] at h0 hL ⊢
      exact congrArg Subtype.val (h0.trans hL)
    have h := StrongAt.of_negVar (st := stXQ) ⟨0, by decide⟩ hty
    have hdep : stXQ.depAt ⟨0, by decide⟩ = Kx := by
      have h0 := ResolvedState.push_old_support stX (by decide) Sneg0 Kx ⟨0, by decide⟩
      have hL := ResolvedState.pushResolved_new_support
        (ResolvedState.empty U0 O1 3) (by decide) Sneg0 Kx
      simp only [stXQ, stX, ResolvedState.pushResolved] at h0 hL ⊢
      exact h0.trans hL
    rw [hdep] at h
    exact h
  · have h0 := ResolvedState.push_old_support stX (by decide) Sneg0 Kx ⟨0, by decide⟩
    have hL := ResolvedState.pushResolved_new_support
      (ResolvedState.empty U0 O1 3) (by decide) Sneg0 Kx
    simp only [stXQ, stX, ResolvedState.pushResolved] at h0 hL ⊢
    exact h0.trans hL
  · exact ResolvedState.pushResolved_new_support stX (by decide) Sneg0 Kx

end ResolvedSupportFixtures

end Gimbal.Equality.Scherer
