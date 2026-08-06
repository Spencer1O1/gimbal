/-
  Scherer-core contracted provenance-context foundation (S3 architecture gate).

  Each available occurrence is a `(StableTy × SearchProv)` pair. Equal stable
  types with distinct provenance labels are retained separately: componentwise
  Boolean OR is forbidden. `resetRound` clears only `currentNew`; `addLocal`
  unions the exact local label `⟨false, true⟩`.

  No search recursion, coverage, `Sat.done` choice, source scheduling, or
  legacy-engine bridge.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Gimbal.Equality.Scherer.Syntax

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Provenance labels -/

/--
Two-bit provenance for one available occurrence.

* `outerNew` — satisfies the caller's freshness obligation
* `currentNew` — eligible as current-round / current-batch new
-/
structure SearchProv where
  outerNew : Bool
  currentNew : Bool
  deriving DecidableEq, Repr

namespace SearchProv

/-- Entering a shift round: keep outer-new, clear current-round new. -/
def resetRound (p : SearchProv) : SearchProv :=
  ⟨p.outerNew, false⟩

/-- Locally stored binder: current-round new without outer-new. -/
def «local» : SearchProv :=
  ⟨false, true⟩

@[simp] theorem resetRound_mk (o c : Bool) :
    resetRound ⟨o, c⟩ = ⟨o, false⟩ := rfl

@[simp] theorem local_outerNew : «local».outerNew = false := rfl

@[simp] theorem local_currentNew : «local».currentNew = true := rfl

end SearchProv

/-! ### Contracted search context -/

/--
Normalized availability: finite set of exact `(type, provenance)` pairs.
Duplicate exact pairs are impossible; distinct provenance on equal types is kept.
-/
abbrev SearchCtx (sig : Signature) : Type :=
  Finset (StableTy sig.nBases × SearchProv)

namespace SearchCtx

/-- Extensional membership of a typed provenance occurrence. -/
def Has (C : SearchCtx sig) (S : StableTy sig.nBases) (p : SearchProv) : Prop :=
  (S, p) ∈ C

instance (C : SearchCtx sig) (S : StableTy sig.nBases) (p : SearchProv) :
    Decidable (Has C S p) :=
  inferInstanceAs (Decidable ((S, p) ∈ C))

/-- Map every label through `SearchProv.resetRound` (dedup after mapping). -/
def resetRound (C : SearchCtx sig) : SearchCtx sig :=
  C.image fun sp => (sp.1, SearchProv.resetRound sp.2)

/-- Union the exact local label for binder type `S`. -/
def addLocal (C : SearchCtx sig) (S : StableTy sig.nBases) : SearchCtx sig :=
  insert (S, SearchProv.«local») C

end SearchCtx

/-! ### Root contraction -/

/--
Root provenance of a variable in `Old.append New`.

* Old occurrence → `(false, false)`
* New occurrence → `(true, true)`
-/
def rootProv (Old : StableCtx sig) :
    (New : StableCtx sig) → {S : StableTy sig.nBases} →
      StableVar (Old.append New) S → SearchProv
  | .empty, _, _ => ⟨false, false⟩
  | .snoc _ _, _, .here => ⟨true, true⟩
  | .snoc Δ _, _, .there x => rootProv Old Δ x

/-- All Old-side root labels `(S, (false, false))`. -/
def contractOld : StableCtx sig → SearchCtx sig
  | .empty => ∅
  | .snoc Γ S => insert (S, (⟨false, false⟩ : SearchProv)) (contractOld Γ)

/--
Contract `Old.append New` into a finite provenance context.

New binders contribute `(true, true)`; Old binders contribute `(false, false)`.
Equal types from both sides retain both labels.
-/
def contractRoot (Old : StableCtx sig) : StableCtx sig → SearchCtx sig
  | .empty => contractOld Old
  | .snoc Δ S => insert (S, (⟨true, true⟩ : SearchProv)) (contractRoot Old Δ)

/-! ### Membership characterizations -/

theorem mem_contractOld_iff {Γ : StableCtx sig} {S : StableTy sig.nBases}
    {p : SearchProv} :
    (S, p) ∈ contractOld Γ ↔ p = ⟨false, false⟩ ∧ Nonempty (StableVar Γ S) := by
  induction Γ with
  | empty =>
    constructor
    · intro h
      exact absurd h (Finset.notMem_empty _)
    · intro ⟨_, ⟨x⟩⟩
      cases x
  | snoc Γ S' ih =>
    simp only [contractOld, Finset.mem_insert, Prod.mk.injEq]
    constructor
    · intro h
      cases h with
      | inl h =>
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, ⟨StableVar.here⟩⟩
      | inr h =>
        obtain ⟨hp, ⟨x⟩⟩ := ih.mp h
        exact ⟨hp, ⟨StableVar.there x⟩⟩
    · intro ⟨hp, ⟨x⟩⟩
      cases x with
      | here =>
        exact Or.inl ⟨rfl, hp⟩
      | there x =>
        exact Or.inr (ih.mpr ⟨hp, ⟨x⟩⟩)

/-- Gate: contraction membership ↔ some root variable with that provenance. -/
theorem contractRoot_has_iff {Old New : StableCtx sig} {S : StableTy sig.nBases}
    {p : SearchProv} :
    SearchCtx.Has (contractRoot Old New) S p ↔
      ∃ x : StableVar (Old.append New) S, rootProv Old New x = p := by
  induction New with
  | empty =>
    simp only [SearchCtx.Has, StableCtx.append_empty]
    change (S, p) ∈ contractOld Old ↔ _
    constructor
    · intro h
      obtain ⟨hp, ⟨x⟩⟩ := (mem_contractOld_iff (Γ := Old)).mp h
      refine ⟨x, ?_⟩
      simp only [rootProv]
      exact hp.symm
    · intro ⟨x, hx⟩
      have hx' : rootProv Old (.empty : StableCtx sig) x = ⟨false, false⟩ := rfl
      rw [hx'] at hx
      exact (mem_contractOld_iff (Γ := Old)).mpr ⟨hx.symm, ⟨x⟩⟩
  | snoc Δ T ih =>
    simp only [SearchCtx.Has, StableCtx.append_snoc]
    change (S, p) ∈ insert (T, (⟨true, true⟩ : SearchProv)) (contractRoot Old Δ) ↔ _
    simp only [Finset.mem_insert, Prod.mk.injEq]
    constructor
    · intro h
      cases h with
      | inl h =>
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨StableVar.here, rfl⟩
      | inr h =>
        obtain ⟨x, hx⟩ := ih.mp h
        refine ⟨StableVar.there x, ?_⟩
        simpa [rootProv] using hx
    · intro ⟨x, hx⟩
      cases x with
      | here =>
        simp only [rootProv] at hx
        exact Or.inl ⟨rfl, hx.symm⟩
      | there x =>
        refine Or.inr (ih.mpr ⟨x, ?_⟩)
        simpa [rootProv] using hx

/-- Gate: reset-round membership ↔ some prior label that resets to `p`. -/
theorem resetRound_has_iff {C : SearchCtx sig} {S : StableTy sig.nBases}
    {p : SearchProv} :
    SearchCtx.Has (SearchCtx.resetRound C) S p ↔
      ∃ q, SearchCtx.Has C S q ∧ q.resetRound = p := by
  simp only [SearchCtx.Has, SearchCtx.resetRound, Finset.mem_image]
  constructor
  · rintro ⟨⟨T, q⟩, hq, hEq⟩
    injection hEq with hT hp
    subst hT
    exact ⟨q, hq, hp⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨(S, q), hq, rfl⟩

/-- Gate: add-local membership is prior membership or the exact local label. -/
theorem addLocal_has_iff {C : SearchCtx sig} {S T : StableTy sig.nBases}
    {p : SearchProv} :
    SearchCtx.Has (SearchCtx.addLocal C S) T p ↔
      SearchCtx.Has C T p ∨ (T = S ∧ p = SearchProv.«local») := by
  simp only [SearchCtx.Has, SearchCtx.addLocal, Finset.mem_insert, Prod.mk.injEq]
  exact Or.comm

/-! ### Adversarial fixtures -/

namespace SearchStateFixtures

def sig0 : Signature := ⟨0, #[]⟩

/-- Shared stable type appearing in both Old and New. -/
def Sdup : StableTy 0 := .neg (.shift (.zero : Pos 0))

def Old_dup : StableCtx sig0 := StableCtx.snoc .empty Sdup
def New_dup : StableCtx sig0 := StableCtx.snoc .empty Sdup

def C_dup : SearchCtx sig0 := contractRoot Old_dup New_dup

/-- Equal `S` in Old and New retains both `(false,false)` and `(true,true)`. -/
theorem contract_retains_both_provenances :
    SearchCtx.Has C_dup Sdup ⟨false, false⟩ ∧
      SearchCtx.Has C_dup Sdup ⟨true, true⟩ := by
  native_decide

/--
`resetRound` keeps `(false,false)` and `(true,false)`, drops `(true,true)`.
-/
theorem resetRound_retains_outer_clears_current :
    let C := SearchCtx.resetRound C_dup
    SearchCtx.Has C Sdup ⟨false, false⟩ ∧
      SearchCtx.Has C Sdup ⟨true, false⟩ ∧
      ¬ SearchCtx.Has C Sdup ⟨true, true⟩ := by
  native_decide

/--
`addLocal` of the same `S` additionally retains `(false,true)`.
-/
theorem addLocal_retains_local_label :
    let C := SearchCtx.addLocal (SearchCtx.resetRound C_dup) Sdup
    SearchCtx.Has C Sdup ⟨false, false⟩ ∧
      SearchCtx.Has C Sdup ⟨true, false⟩ ∧
      SearchCtx.Has C Sdup ⟨false, true⟩ := by
  native_decide

/-- The local label is never outer-new. -/
theorem local_not_outer_new :
    SearchProv.«local».outerNew = false := rfl

/--
Componentwise OR would collapse `(false,false)` and `(true,true)` to
`(true,true)` and lose the Old occurrence. Contraction keeps both.
-/
theorem no_boolean_or_collapse :
    SearchCtx.Has C_dup Sdup ⟨false, false⟩ ∧
      SearchCtx.Has C_dup Sdup ⟨true, true⟩ ∧
      ⟨false, false⟩ ≠ (⟨true, true⟩ : SearchProv) := by
  refine ⟨?_, ?_, by decide⟩
  · exact contract_retains_both_provenances.1
  · exact contract_retains_both_provenances.2

end SearchStateFixtures

end Gimbal.Equality.Scherer
