/-
  Resolver-owned typed origins for pair-selected Scherer comparison.

  This module is deliberately below exact observation codes.  It provides the
  bridge from intrinsic stable/pending variables to terminal representatives
  of a decreasing `AliasResolver`, and records raw batch-result origins before
  resolving them.  Stores reuse the pending source representative.
-/

import Gimbal.Equality.Scherer.PairTrace
import Gimbal.Equality.Scherer.Syntax

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Terminal representatives -/

/-- A typed origin already normalized to a terminal resolver representative. -/
structure ResolvedRef (R : AliasResolver sig) (A : Object sig.nBases) where
  origin : TypedOrigin sig A
  terminal : R.target origin.raw = none

namespace ResolvedRef

variable {R : AliasResolver sig} {A : Object sig.nBases}

@[ext] theorem ext {x y : ResolvedRef R A} (h : x.origin = y.origin) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance : DecidableEq (ResolvedRef R A) := fun x y =>
  decidable_of_iff (x.origin = y.origin) ⟨ext, congrArg origin⟩

/-- Resolve a typed origin before exposing it to later structural codes. -/
def of (R : AliasResolver sig) (x : TypedOrigin sig A) : ResolvedRef R A :=
  ⟨R.resolveTyped x, R.target_resolve_eq_none x.raw⟩

@[simp] theorem of_origin (R : AliasResolver sig) (x : TypedOrigin sig A) :
    (of R x).origin = R.resolveTyped x := rfl

@[simp] theorem of_raw (R : AliasResolver sig) (x : TypedOrigin sig A) :
    (of R x).origin.raw = R.resolve x.raw := rfl

@[simp] theorem of_terminal (R : AliasResolver sig) (x : TypedOrigin sig A) :
    R.target (of R x).origin.raw = none :=
  (of R x).terminal

/-- Resolver equivalence is exactly equality of normalized typed references. -/
theorem of_eq_iff (R : AliasResolver sig) (x y : TypedOrigin sig A) :
    of R x = of R y ↔ R.Equivalent x.raw y.raw := by
  constructor
  · intro h
    have hraw := congrArg (fun z : ResolvedRef R A => z.origin.raw) h
    exact hraw
  · intro h
    apply ext
    apply TypedOrigin.ext
    exact h

/-- Resolving an already resolved typed origin does not change its reference. -/
@[simp] theorem of_resolveTyped (R : AliasResolver sig)
    (x : TypedOrigin sig A) :
    of R (R.resolveTyped x) = of R x := by
  rw [of_eq_iff]
  unfold AliasResolver.Equivalent
  exact R.resolve_idempotent x.raw

/-- A terminal typed origin is represented by itself. -/
theorem of_eq_self (R : AliasResolver sig) (x : TypedOrigin sig A)
    (hx : R.target x.raw = none) :
    (of R x).origin = x := by
  apply TypedOrigin.ext
  exact R.resolve_eq_self_of_target_eq_none hx

end ResolvedRef

/-! ### Stable and pending assignments -/

/-- A typed position in the ordered pending-positive worklist. -/
inductive PendingVar {sig : Signature} :
    Pending sig → Pos sig.nBases → Type where
  | here {P ps} : PendingVar (.cons P ps) P
  | there {P Q ps} : PendingVar ps Q → PendingVar (.cons P ps) Q

/-- Every stable variable has one common terminal origin representative. -/
structure OriginAssignment (R : AliasResolver sig) (Γ : StableCtx sig) where
  ref : ∀ {S}, StableVar Γ S → ResolvedRef R S.erase

namespace OriginAssignment

variable {R : AliasResolver sig} {Γ : StableCtx sig}

/-- Empty stable context has the unique empty assignment. -/
def empty (R : AliasResolver sig) :
    OriginAssignment R (StableCtx.empty : StableCtx sig) where
  ref := fun x => nomatch x

/--
Append a stable binder using an existing resolved source.  This is the
operation used by both `storeAtom` and `storeShift`: the store adds no new
origin identity.
-/
def snoc (E : OriginAssignment R Γ) {S : StableTy sig.nBases}
    (source : ResolvedRef R S.erase) : OriginAssignment R (Γ.snoc S) where
  ref := by
    intro T x
    cases x with
    | here => exact source
    | there x => exact E.ref x

@[simp] theorem snoc_here (E : OriginAssignment R Γ)
    {S : StableTy sig.nBases} (source : ResolvedRef R S.erase) :
    (E.snoc source).ref (.here : StableVar (Γ.snoc S) S) = source := rfl

@[simp] theorem snoc_there (E : OriginAssignment R Γ)
    {S T : StableTy sig.nBases} (source : ResolvedRef R S.erase)
    (x : StableVar Γ T) :
    (E.snoc source).ref (.there x : StableVar (Γ.snoc S) T) = E.ref x := rfl

end OriginAssignment

/-- Common terminal representatives for every pending occurrence. -/
structure PendingAssignment (R : AliasResolver sig) (ps : Pending sig) where
  ref : ∀ {P}, PendingVar ps P → ResolvedRef R P.erase

namespace PendingAssignment

variable {R : AliasResolver sig} {ps : Pending sig}

def empty (R : AliasResolver sig) :
    PendingAssignment R (Pending.empty : Pending sig) where
  ref := fun x => nomatch x

/-- Extend the pending worklist at its forced head. -/
def cons {P : Pos sig.nBases} (source : ResolvedRef R P.erase)
    (rest : PendingAssignment R ps) : PendingAssignment R (.cons P ps) where
  ref := by
    intro Q x
    cases x with
    | here => exact source
    | there x => exact rest.ref x

@[simp] theorem cons_here {P : Pos sig.nBases}
    (source : ResolvedRef R P.erase) (rest : PendingAssignment R ps) :
    (cons source rest).ref (.here : PendingVar (.cons P ps) P) = source := rfl

@[simp] theorem cons_there {P Q : Pos sig.nBases}
    (source : ResolvedRef R P.erase) (rest : PendingAssignment R ps)
    (x : PendingVar ps Q) :
    (cons source rest).ref (.there x : PendingVar (.cons P ps) Q) = rest.ref x := rfl

end PendingAssignment

/-! ### Store reuse -/

/-- Store an atomic pending head by reusing its resolved source reference. -/
def OriginAssignment.storeAtom (E : OriginAssignment R Γ)
    (pending : PendingAssignment R (.cons (.atom q) ps)) :
    OriginAssignment R (Γ.snoc (.atom q)) :=
  E.snoc (pending.ref (.here : PendingVar (.cons (.atom q) ps) (.atom q)))

/-- Store a shifted pending head by reusing its resolved source reference. -/
def OriginAssignment.storeShift (E : OriginAssignment R Γ)
    (pending : PendingAssignment R (.cons (.shift N) ps)) :
    OriginAssignment R (Γ.snoc (.neg N)) :=
  E.snoc (pending.ref (.here : PendingVar (.cons (.shift N) ps) (.shift N)))

@[simp] theorem OriginAssignment.storeAtom_here
    (E : OriginAssignment R Γ)
    (pending : PendingAssignment R (.cons (.atom q) ps)) :
    (E.storeAtom pending).ref
        (.here : StableVar (Γ.snoc (.atom q)) (.atom q)) =
      pending.ref (.here : PendingVar (.cons (.atom q) ps) (.atom q)) := rfl

@[simp] theorem OriginAssignment.storeShift_here
    (E : OriginAssignment R Γ)
    (pending : PendingAssignment R (.cons (.shift N) ps)) :
    (E.storeShift pending).ref
        (.here : StableVar (Γ.snoc (.neg N)) (.neg N)) =
      pending.ref (.here : PendingVar (.cons (.shift N) ps) (.shift N)) := rfl

/-! ### Raw batch-result origins -/

/--
Raw typed origins allocated for one selected batch.  Resolving the origins
produces the common pending assignment used by both paired bodies; duplicate
exact observations may therefore share a representative without losing their
distinct raw sites.
-/
structure BatchResultAssignment (R : AliasResolver sig) (selected : Pending sig) where
  origin : ∀ {P}, PendingVar selected P → TypedOrigin sig P.erase

namespace BatchResultAssignment

variable {R : AliasResolver sig} {selected : Pending sig}

/-- Resolve every raw batch-result origin before it enters a body assignment. -/
def resolved (B : BatchResultAssignment R selected) :
    PendingAssignment R selected where
  ref x := ResolvedRef.of R (B.origin x)

@[simp] theorem resolved_ref (B : BatchResultAssignment R selected)
    {P : Pos sig.nBases} (x : PendingVar selected P) :
    B.resolved.ref x = ResolvedRef.of R (B.origin x) := rfl

end BatchResultAssignment

/-! ### Adversarial boundary fixtures -/

namespace PairOriginFixtures

open PairTraceFixtures

/-- A two-step store chain has one terminal reference. -/
theorem alias_chain_collapses :
    ResolvedRef.of chainResolver store2 = ResolvedRef.of chainResolver store1 ∧
      ResolvedRef.of chainResolver store1 = ResolvedRef.of chainResolver atom0 := by
  constructor <;> rw [ResolvedRef.of_eq_iff]
  · unfold AliasResolver.Equivalent
    apply AliasResolver.resolve_eq_resolve_of_target_eq_some
    simp [chainResolver]
  · unfold AliasResolver.Equivalent
    apply AliasResolver.resolve_eq_resolve_of_target_eq_some
    have h12 : store1.raw ≠ store2.raw := by decide
    simp [chainResolver, h12]

def terminalA : TypedOrigin TwoGenSig Q := rootOrigin TwoGenSig Q 80 0
def terminalB : TypedOrigin TwoGenSig Q := rootOrigin TwoGenSig Q 81 0

/-- Equal types do not collapse distinct terminal origins. -/
theorem distinct_terminal_same_type :
    ResolvedRef.of (AliasResolver.identity TwoGenSig) terminalA ≠
      ResolvedRef.of (AliasResolver.identity TwoGenSig) terminalB := by
  intro h
  have heq := (ResolvedRef.of_eq_iff _ _ _).mp h
  unfold AliasResolver.Equivalent at heq
  rw [AliasResolver.resolve_eq_self_of_target_eq_none,
    AliasResolver.resolve_eq_self_of_target_eq_none] at heq
  · exact (by decide : terminalA.raw ≠ terminalB.raw) heq
  · rfl
  · rfl

def siteA : TypedOrigin TwoGenSig Q :=
  observationOrigin TwoGenSig Q 11 0 90 1

def siteB : TypedOrigin TwoGenSig Q :=
  observationOrigin TwoGenSig Q 12 0 91 1

/--
The same result type and scheduler support token do not silently identify
observations from different terminal sites.
-/
theorem same_type_support_different_sites_not_equal :
    let supportA : Nat := 7
    let supportB : Nat := 7
    supportA = supportB ∧
      ResolvedRef.of (AliasResolver.identity TwoGenSig) siteA ≠
        ResolvedRef.of (AliasResolver.identity TwoGenSig) siteB := by
  dsimp
  constructor
  · rfl
  · intro h
    have heq := (ResolvedRef.of_eq_iff _ _ _).mp h
    unfold AliasResolver.Equivalent at heq
    rw [AliasResolver.resolve_eq_self_of_target_eq_none,
      AliasResolver.resolve_eq_self_of_target_eq_none] at heq
    · exact (by decide : siteA.raw ≠ siteB.raw) heq
    · rfl
    · rfl

abbrev AtomS : StableTy TwoGenSig.nBases := .atom q0
abbrev AtomP : Pos TwoGenSig.nBases := .atom q0
abbrev OneStable : StableCtx TwoGenSig :=
  (StableCtx.empty : StableCtx TwoGenSig).snoc AtomS
abbrev OnePending : Pending TwoGenSig := .cons AtomP .empty

def atomRef : ResolvedRef (AliasResolver.identity TwoGenSig) Q :=
  ResolvedRef.of _ terminalA

def stableOne : OriginAssignment (AliasResolver.identity TwoGenSig) OneStable :=
  (OriginAssignment.empty _).snoc atomRef

def pendingOne : PendingAssignment (AliasResolver.identity TwoGenSig) OnePending :=
  PendingAssignment.cons atomRef (PendingAssignment.empty _)

theorem stable_assignment_type_correct :
    stableOne.ref (.here : StableVar OneStable AtomS) = atomRef := rfl

theorem pending_assignment_type_correct :
    pendingOne.ref (.here : PendingVar OnePending AtomP) = atomRef := rfl

def batchOne : BatchResultAssignment (AliasResolver.identity TwoGenSig) OnePending where
  origin := by
    intro P x
    cases x with
    | here => exact terminalA
    | there x => nomatch x

theorem batch_result_assignment_type_correct :
    batchOne.resolved.ref (.here : PendingVar OnePending AtomP) = atomRef := rfl

/-- The store bridge reuses the pending reference exactly. -/
theorem store_reuses_pending_source :
    ((OriginAssignment.empty _).storeAtom pendingOne).ref
        (.here : StableVar (StableCtx.empty.snoc AtomS) AtomS) = atomRef := rfl

end PairOriginFixtures

end Gimbal.Equality.Scherer
