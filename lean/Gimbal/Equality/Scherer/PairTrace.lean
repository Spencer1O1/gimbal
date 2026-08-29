/-
  Typed origin, alias, and constraint-trace foundation for pair-selected
  Scherer normalization.

  Observation syntax is abstracted by a typed key family.  A future pair
  scheduler may instantiate that family with exact resolved neutral keys
  without importing selected forms, codes, or semantic models here.
-/

import Gimbal.Signature

namespace Gimbal.Equality.Scherer

universe u

/-! ### Typed origins -/

/-- Why a value origin exists.  Types live on `Origin`, not in this tag. -/
inductive OriginKind (sig : Signature) where
  | generator (q : Fin sig.nGens)
  | root (slot : Nat)
  | stable (slot : Nat)
  | store (slot sourceId : Nat)
  | observation (site entry : Nat)
  | split (parentId : Nat) (right : Bool)
  deriving DecidableEq, Repr

/-- A globally named, typed value origin with an explicit introduction rank. -/
structure Origin (sig : Signature) where
  ty : Object sig.nBases
  id : Nat
  introRank : Nat
  kind : OriginKind sig
  deriving DecidableEq, Repr

/-- Intrinsic view of an origin at a fixed object. -/
structure TypedOrigin (sig : Signature) (A : Object sig.nBases) where
  raw : Origin sig
  type_eq : raw.ty = A

namespace TypedOrigin

variable {sig : Signature} {A B : Object sig.nBases}

@[ext] theorem ext {x y : TypedOrigin sig A} (h : x.raw = y.raw) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Raw-origin equality is the equality used by resolvers and traces. -/
def rawEq (x : TypedOrigin sig A) (y : TypedOrigin sig B) : Prop :=
  x.raw = y.raw

instance : DecidableEq (TypedOrigin sig A) := fun x y =>
  decidable_of_iff (x.raw = y.raw) ⟨fun h => ext h, congrArg raw⟩

end TypedOrigin

/-- The canonical rigid origin for an opaque generator declaration. -/
def generatorOrigin (sig : Signature) (q : Fin sig.nGens) :
    TypedOrigin sig (.exp (sig.gen q).source (sig.gen q).target) :=
  ⟨⟨.exp (sig.gen q).source (sig.gen q).target, q.val, 0, .generator q⟩, rfl⟩

/-- A root input or root-context value. -/
def rootOrigin (sig : Signature) (A : Object sig.nBases)
    (slot rank : Nat) : TypedOrigin sig A :=
  ⟨⟨A, slot, rank, .root slot⟩, rfl⟩

/-- A stable value introduced independently of a store alias. -/
def stableOrigin (sig : Signature) (A : Object sig.nBases)
    (slot rank : Nat) : TypedOrigin sig A :=
  ⟨⟨A, slot, rank, .stable slot⟩, rfl⟩

/-- Stable name produced by storing an already existing pending value. -/
def storeOrigin (source : TypedOrigin sig A) (slot id rank : Nat) :
    TypedOrigin sig A :=
  ⟨⟨A, id, rank, .store slot source.raw.id⟩, rfl⟩

/-- Fresh result origin of one batch observation. -/
def observationOrigin (sig : Signature) (A : Object sig.nBases)
    (site entry id rank : Nat) : TypedOrigin sig A :=
  ⟨⟨A, id, rank, .observation site entry⟩, rfl⟩

/-- Payload exposed by choosing the left branch of a sum origin. -/
def splitLeftOrigin (parent : TypedOrigin sig (.coprod A B))
    (id rank : Nat) : TypedOrigin sig A :=
  ⟨⟨A, id, rank, .split parent.raw.id false⟩, rfl⟩

/-- Payload exposed by choosing the right branch of a sum origin. -/
def splitRightOrigin (parent : TypedOrigin sig (.coprod A B))
    (id rank : Nat) : TypedOrigin sig B :=
  ⟨⟨B, id, rank, .split parent.raw.id true⟩, rfl⟩

/-! ### Scopes and abstract typed observation keys -/

/-- Origins of rank below `nextRank` are available in this scope. -/
structure OriginScope where
  nextRank : Nat
  deriving DecidableEq, Repr

def OriginScope.Contains (s : OriginScope) (o : Origin sig) : Prop :=
  o.introRank < s.nextRank

/--
Abstract exact observation keys. `code` is injective at a fixed result type;
`deps` exposes all origins mentioned by the key for pre-batch scope checks.
-/
structure TypedKeyFamily (sig : Signature) where
  Key : Object sig.nBases → Type u
  code : {A : Object sig.nBases} → Key A → Nat
  code_injective : ∀ {A} {x y : Key A}, code x = code y → x = y
  deps : {A : Object sig.nBases} → Key A → List (Origin sig)

namespace TypedKeyFamily

variable {sig : Signature} (K : TypedKeyFamily sig)

def Scoped {A : Object sig.nBases} (pre : OriginScope) (key : K.Key A) : Prop :=
  ∀ o ∈ K.deps key, pre.Contains o

end TypedKeyFamily

/-! ### Decreasing alias resolution -/

/-- One-step aliases preserve their object and point strictly backwards. -/
structure AliasResolver (sig : Signature) where
  target : Origin sig → Option (Origin sig)
  target_type : ∀ {x y}, target x = some y → y.ty = x.ty
  target_rank : ∀ {x y}, target x = some y → y.introRank < x.introRank

namespace AliasResolver

variable {sig : Signature}

/-- Resolver with no aliases. -/
def identity (sig : Signature) : AliasResolver sig where
  target := fun _ => none
  target_type := by simp
  target_rank := by simp

/-- One certified backwards alias. -/
def single (src dst : Origin sig) (hty : dst.ty = src.ty)
    (hrank : dst.introRank < src.introRank) : AliasResolver sig where
  target := fun x => if x = src then some dst else none
  target_type := by
    intro x y h
    by_cases hx : x = src
    · subst x
      simp at h
      subst y
      exact hty
    · simp [hx] at h
  target_rank := by
    intro x y h
    by_cases hx : x = src
    · subst x
      simp at h
      subst y
      exact hrank
    · simp [hx] at h

/-- Follow aliases to their unique terminal representative. -/
def resolve (R : AliasResolver sig) (x : Origin sig) : Origin sig :=
  match _h : R.target x with
  | none => x
  | some y => R.resolve y
termination_by x.introRank
decreasing_by exact R.target_rank _h

theorem resolve_eq_self_of_target_eq_none (R : AliasResolver sig)
    {x : Origin sig} (h : R.target x = none) : R.resolve x = x := by
  rw [resolve.eq_1, h]

theorem resolve_eq_resolve_of_target_eq_some (R : AliasResolver sig)
    {x y : Origin sig} (h : R.target x = some y) : R.resolve x = R.resolve y := by
  rw [resolve.eq_1, h]

theorem resolve_type (R : AliasResolver sig) (x : Origin sig) :
    (R.resolve x).ty = x.ty := by
  induction x using resolve.induct R with
  | case1 x hx =>
      rw [resolve.eq_1, hx]
  | case2 x y hxy ih =>
      rw [resolve.eq_1, hxy]
      exact ih.trans (R.target_type hxy)

theorem resolve_rank_le (R : AliasResolver sig) (x : Origin sig) :
    (R.resolve x).introRank ≤ x.introRank := by
  induction x using resolve.induct R with
  | case1 x hx =>
      rw [resolve.eq_1, hx]
      exact Nat.le_refl _
  | case2 x y hxy ih =>
      rw [resolve.eq_1, hxy]
      exact Nat.le_trans ih (Nat.le_of_lt (R.target_rank hxy))

theorem target_resolve_eq_none (R : AliasResolver sig) (x : Origin sig) :
    R.target (R.resolve x) = none := by
  induction x using resolve.induct R with
  | case1 x hx =>
      rw [resolve.eq_1, hx]
      exact hx
  | case2 x y hxy ih =>
      rw [resolve.eq_1, hxy]
      exact ih

theorem resolve_idempotent (R : AliasResolver sig) (x : Origin sig) :
    R.resolve (R.resolve x) = R.resolve x := by
  exact R.resolve_eq_self_of_target_eq_none (R.target_resolve_eq_none x)

def resolveTyped (R : AliasResolver sig) (x : TypedOrigin sig A) :
    TypedOrigin sig A :=
  ⟨R.resolve x.raw, (R.resolve_type x.raw).trans x.type_eq⟩

@[simp] theorem resolveTyped_raw (R : AliasResolver sig) (x : TypedOrigin sig A) :
    (R.resolveTyped x).raw = R.resolve x.raw := rfl

theorem resolveTyped_idempotent (R : AliasResolver sig)
    (x : TypedOrigin sig A) :
    R.resolveTyped (R.resolveTyped x) = R.resolveTyped x := by
  apply TypedOrigin.ext
  exact R.resolve_idempotent x.raw

def Equivalent (R : AliasResolver sig) (x y : Origin sig) : Prop :=
  R.resolve x = R.resolve y

instance (R : AliasResolver sig) (x y : Origin sig) : Decidable (R.Equivalent x y) :=
  by unfold Equivalent; infer_instance

theorem equivalent_refl (R : AliasResolver sig) (x : Origin sig) :
    R.Equivalent x x := rfl

theorem equivalent_symm (R : AliasResolver sig) {x y : Origin sig}
    (h : R.Equivalent x y) : R.Equivalent y x := h.symm

theorem equivalent_trans (R : AliasResolver sig) {x y z : Origin sig}
    (hxy : R.Equivalent x y) (hyz : R.Equivalent y z) :
    R.Equivalent x z := hxy.trans hyz

end AliasResolver

/-! ### Typed split and observation traces -/

/--
`support` is scheduler data and intentionally absent from exact-key equality:
different support obligations may denote the same exact observation.
-/
inductive TraceStep {sig : Signature} (K : TypedKeyFamily sig) where
  | splitL {A B} :
      TypedOrigin sig (.coprod A B) → TypedOrigin sig A → TraceStep K
  | splitR {A B} :
      TypedOrigin sig (.coprod A B) → TypedOrigin sig B → TraceStep K
  | observe {A} :
      (site support : Nat) → OriginScope → K.Key A → TypedOrigin sig A → TraceStep K

namespace TraceStep

variable {sig : Signature} {K : TypedKeyFamily sig}

def parent? : TraceStep K → Option (Origin sig)
  | .splitL p _ | .splitR p _ => some p.raw
  | .observe .. => none

def payload? : TraceStep K → Option (Origin sig)
  | .splitL _ p | .splitR _ p => some p.raw
  | .observe .. => none

def splitTag? : TraceStep K → Option Bool
  | .splitL .. => some false
  | .splitR .. => some true
  | .observe .. => none

def result? : TraceStep K → Option (Origin sig)
  | .observe _ _ _ _ r => some r.raw
  | _ => none

def keySig? : TraceStep K → Option (Object sig.nBases × Nat)
  | .observe (A := A) _ _ _ key _ => some (A, K.code key)
  | _ => none

def support? : TraceStep K → Option Nat
  | .observe _ support _ _ _ => some support
  | _ => none

def Scoped : TraceStep K → Prop
  | .splitL parent payload => parent.raw.introRank < payload.raw.introRank
  | .splitR parent payload => parent.raw.introRank < payload.raw.introRank
  | .observe _ _ pre key result =>
      K.Scoped pre key ∧ pre.nextRank ≤ result.raw.introRank

end TraceStep

/-- A finite typed constraint trace under one alias resolver. -/
structure TypedTrace {sig : Signature} (K : TypedKeyFamily sig) where
  resolver : AliasResolver sig
  steps : List (TraceStep K)

namespace TypedTrace

variable {sig : Signature} {K : TypedKeyFamily sig}

def splitConflict (T : TypedTrace K) (s t : TraceStep K) : Prop :=
  ∃ p q a b,
    s.parent? = some p ∧ t.parent? = some q ∧
    s.splitTag? = some a ∧ t.splitTag? = some b ∧
    a ≠ b ∧ T.resolver.Equivalent p q

def IsDead (T : TypedTrace K) : Prop :=
  ∃ s ∈ T.steps, ∃ t ∈ T.steps, T.splitConflict s t

/-- Repeated same-tag splits are functional modulo aliases. -/
def SplitsFunctional (T : TypedTrace K) : Prop :=
  ∀ s ∈ T.steps, ∀ t ∈ T.steps,
    s.splitTag? = t.splitTag? → s.splitTag? ≠ none →
    (∃ p q, s.parent? = some p ∧ t.parent? = some q ∧
      T.resolver.Equivalent p q) →
    ∃ x y, s.payload? = some x ∧ t.payload? = some y ∧
      T.resolver.Equivalent x y

/-- Observation results are the exact quotient of typed structural keys. -/
def ObservationsQuotiented (T : TypedTrace K) : Prop :=
  ∀ s ∈ T.steps, ∀ t ∈ T.steps,
    ∀ ks kt, s.keySig? = some ks → t.keySig? = some kt →
    ((ks = kt) ↔
      (∃ x y, s.result? = some x ∧ t.result? = some y ∧
        T.resolver.Equivalent x y))

/-- Structural trace well-formedness; dead traces remain representable. -/
structure WellFormed (T : TypedTrace K) : Prop where
  stepsScoped : ∀ s ∈ T.steps, s.Scoped
  splitsFunctional : T.SplitsFunctional
  observationsQuotiented : T.ObservationsQuotiented

theorem WellFormed.sameSplit_payloadEquivalent {T : TypedTrace K}
    (hT : T.WellFormed) {s t : TraceStep K}
    (hs : s ∈ T.steps) (ht : t ∈ T.steps)
    (htag : s.splitTag? = t.splitTag?) (hsplit : s.splitTag? ≠ none)
    {p q : Origin sig} (hp : s.parent? = some p) (hq : t.parent? = some q)
    (hparent : T.resolver.Equivalent p q) :
    ∃ x y, s.payload? = some x ∧ t.payload? = some y ∧
      T.resolver.Equivalent x y :=
  hT.splitsFunctional s hs t ht htag hsplit ⟨p, q, hp, hq, hparent⟩

theorem WellFormed.sameObservation_resultEquivalent {T : TypedTrace K}
    (hT : T.WellFormed) {s t : TraceStep K}
    (hs : s ∈ T.steps) (ht : t ∈ T.steps)
    {key : Object sig.nBases × Nat}
    (hsig : s.keySig? = some key) (htig : t.keySig? = some key) :
    ∃ x y, s.result? = some x ∧ t.result? = some y ∧
      T.resolver.Equivalent x y :=
  (hT.observationsQuotiented s hs t ht key key hsig htig).mp rfl

theorem WellFormed.observationKey_eq_of_resultEquivalent {T : TypedTrace K}
    (hT : T.WellFormed) {s t : TraceStep K}
    (hs : s ∈ T.steps) (ht : t ∈ T.steps)
    {ks kt : Object sig.nBases × Nat}
    (hsig : s.keySig? = some ks) (htig : t.keySig? = some kt)
    (hresult : ∃ x y, s.result? = some x ∧ t.result? = some y ∧
      T.resolver.Equivalent x y) : ks = kt :=
  (hT.observationsQuotiented s hs t ht ks kt hsig htig).mpr hresult

theorem dead_of_oppositeSplits (T : TypedTrace K) {s t : TraceStep K}
    (hs : s ∈ T.steps) (ht : t ∈ T.steps)
    {p q : Origin sig} {a b : Bool}
    (hp : s.parent? = some p) (hq : t.parent? = some q)
    (ha : s.splitTag? = some a) (hb : t.splitTag? = some b)
    (htag : a ≠ b) (hparent : T.resolver.Equivalent p q) : T.IsDead :=
  ⟨s, hs, t, ht, p, q, a, b, hp, hq, ha, hb, htag, hparent⟩

def IsLive (T : TypedTrace K) : Prop := ¬T.IsDead

/-! ### Resolved terminal sources -/

inductive ResolvedSource (sig : Signature) where
  | atom (q : Fin sig.nBases) (origin : TypedOrigin sig (.base q))
  | tag (sumTy : Object sig.nBases) (right : Bool)

inductive ResolvedSourceApart (T : TypedTrace K) :
    ResolvedSource sig → ResolvedSource sig → Prop where
  | atom {q} {x y : TypedOrigin sig (.base q)}
      (hne : T.resolver.resolve x.raw ≠ T.resolver.resolve y.raw) :
      ResolvedSourceApart T (.atom q x) (.atom q y)
  | tag {sumTy} {a b : Bool} (hne : a ≠ b) :
      ResolvedSourceApart T (.tag sumTy a) (.tag sumTy b)

end TypedTrace

/-! ### Boundary fixtures -/

namespace PairTraceFixtures

def TwoGenSig : Signature where
  nBases := 1
  generators := #[
    ⟨.unit, .base ⟨0, by decide⟩⟩,
    ⟨.unit, .base ⟨0, by decide⟩⟩
  ]

abbrev q0 : Fin TwoGenSig.nBases := ⟨0, by decide⟩
abbrev Q : Object TwoGenSig.nBases := .base q0

theorem same_generator_occurrences_share_root :
    generatorOrigin TwoGenSig ⟨0, by decide⟩ =
    generatorOrigin TwoGenSig ⟨0, by decide⟩ := rfl

theorem different_generator_declarations_do_not_share_root :
    (generatorOrigin TwoGenSig ⟨0, by decide⟩).raw ≠
      (generatorOrigin TwoGenSig ⟨1, by decide⟩).raw := by
  decide

def KeyFamily : TypedKeyFamily TwoGenSig where
  Key := fun _ => Nat
  code := id
  code_injective := by intros; assumption
  deps := fun _ => []

def key100 : KeyFamily.Key Q := by change Nat; exact 100
def key101 : KeyFamily.Key Q := by change Nat; exact 101

def atom0 : TypedOrigin TwoGenSig Q := rootOrigin TwoGenSig Q 10 0
def obsA : TypedOrigin TwoGenSig Q := observationOrigin TwoGenSig Q 3 0 20 2
def obsADuplicate : TypedOrigin TwoGenSig Q := observationOrigin TwoGenSig Q 4 0 21 3
def obsB : TypedOrigin TwoGenSig Q := observationOrigin TwoGenSig Q 4 1 22 3

def duplicateResolver : AliasResolver TwoGenSig where
  target := (AliasResolver.single obsADuplicate.raw obsA.raw
    (obsA.type_eq.trans obsADuplicate.type_eq.symm) (by decide)).target
  target_type := (AliasResolver.single obsADuplicate.raw obsA.raw
    (obsA.type_eq.trans obsADuplicate.type_eq.symm) (by decide)).target_type
  target_rank := (AliasResolver.single obsADuplicate.raw obsA.raw
    (obsA.type_eq.trans obsADuplicate.type_eq.symm) (by decide)).target_rank

theorem alias_chain_terminates :
    duplicateResolver.resolve obsADuplicate.raw = obsA.raw := by
  rw [AliasResolver.resolve_eq_resolve_of_target_eq_some]
  · apply AliasResolver.resolve_eq_self_of_target_eq_none
    have hne : obsA.raw ≠ obsADuplicate.raw := by decide
    simp [duplicateResolver, AliasResolver.single, hne]
  · simp [duplicateResolver, AliasResolver.single]

theorem duplicate_identical_keys_share_representative :
    duplicateResolver.resolve obsA.raw = duplicateResolver.resolve obsADuplicate.raw := by
  rw [alias_chain_terminates]
  apply AliasResolver.resolve_eq_self_of_target_eq_none
  have hne : obsA.raw ≠ obsADuplicate.raw := by decide
  simp [duplicateResolver, AliasResolver.single, hne]

def duplicateStep1 : TraceStep KeyFamily :=
  .observe (A := Q) 3 7 ⟨1⟩ key100 obsA

def duplicateStep2 : TraceStep KeyFamily :=
  .observe (A := Q) 4 9 ⟨2⟩ key100 obsADuplicate

def duplicateTrace : TypedTrace KeyFamily where
  resolver := duplicateResolver
  steps := [duplicateStep1, duplicateStep2]

example : duplicateStep1.support? ≠ duplicateStep2.support? := by
  simp [duplicateStep1, duplicateStep2, TraceStep.support?]

example : duplicateStep1.keySig? = duplicateStep2.keySig? := by
  rfl

def distinctStep1 : TraceStep KeyFamily :=
  .observe (A := Q) 3 7 ⟨1⟩ key100 obsA

def distinctStep2 : TraceStep KeyFamily :=
  .observe (A := Q) 4 9 ⟨2⟩ key101 obsB

def distinctKeyTrace : TypedTrace KeyFamily where
  resolver := AliasResolver.identity TwoGenSig
  steps := [distinctStep1, distinctStep2]

theorem same_type_different_support_distinct_unless_full_key_equal :
    distinctStep1.keySig? ≠ distinctStep2.keySig? ∧
    distinctKeyTrace.resolver.resolve obsA.raw ≠
      distinctKeyTrace.resolver.resolve obsB.raw := by
  constructor
  · simp [distinctStep1, distinctStep2, TraceStep.keySig?, key100, key101,
      KeyFamily]
  · rw [AliasResolver.resolve_eq_self_of_target_eq_none,
      AliasResolver.resolve_eq_self_of_target_eq_none]
    · decide
    · rfl
    · rfl

def sumParent : TypedOrigin TwoGenSig (.coprod Q Q) :=
  rootOrigin TwoGenSig (.coprod Q Q) 30 0
def leftPayload : TypedOrigin TwoGenSig Q := splitLeftOrigin sumParent 31 1
def rightPayload : TypedOrigin TwoGenSig Q := splitRightOrigin sumParent 32 1

def oppositeSplitTrace : TypedTrace KeyFamily where
  resolver := AliasResolver.identity TwoGenSig
  steps := [.splitL sumParent leftPayload, .splitR sumParent rightPayload]

theorem opposite_splits_mark_dead : oppositeSplitTrace.IsDead := by
  refine ⟨.splitL sumParent leftPayload, by simp [oppositeSplitTrace],
    .splitR sumParent rightPayload, by simp [oppositeSplitTrace], ?_⟩
  refine ⟨sumParent.raw, sumParent.raw, false, true, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, by decide, ?_⟩
  unfold AliasResolver.Equivalent
  rfl

def store1 : TypedOrigin TwoGenSig Q := storeOrigin atom0 0 40 1
def store2 : TypedOrigin TwoGenSig Q := storeOrigin store1 1 41 2

def chainResolver : AliasResolver TwoGenSig where
  target := fun x =>
    if x = store2.raw then some store1.raw
    else if x = store1.raw then some atom0.raw
    else none
  target_type := by
    intro x y h
    by_cases h2 : x = store2.raw
    · subst x
      simp at h
      subst y
      exact store1.type_eq.trans store2.type_eq.symm
    · by_cases h1 : x = store1.raw
      · subst x
        simp [h2] at h
        subst y
        exact atom0.type_eq.trans store1.type_eq.symm
      · simp [h2, h1] at h
  target_rank := by
    intro x y h
    by_cases h2 : x = store2.raw
    · subst x
      simp at h
      subst y
      decide
    · by_cases h1 : x = store1.raw
      · subst x
        simp [h2] at h
        subst y
        decide
      · simp [h2, h1] at h

theorem alias_chain_two_steps_terminates :
    chainResolver.resolve store2.raw = atom0.raw := by
  calc
    chainResolver.resolve store2.raw = chainResolver.resolve store1.raw := by
      apply AliasResolver.resolve_eq_resolve_of_target_eq_some
      simp [chainResolver]
    _ = chainResolver.resolve atom0.raw := by
      apply AliasResolver.resolve_eq_resolve_of_target_eq_some
      have h12 : store1.raw ≠ store2.raw := by decide
      simp [chainResolver, h12]
    _ = atom0.raw := by
      apply AliasResolver.resolve_eq_self_of_target_eq_none
      have h02 : atom0.raw ≠ store2.raw := by decide
      have h01 : atom0.raw ≠ store1.raw := by decide
      simp [chainResolver, h02, h01]

theorem alias_chain_representative_idempotent :
    chainResolver.resolve (chainResolver.resolve store2.raw) =
      chainResolver.resolve store2.raw :=
  chainResolver.resolve_idempotent _

end PairTraceFixtures

end Gimbal.Equality.Scherer
