/-
  Finite, resolver-local provenance certificates for paired Scherer search.

  This layer records why each allocated origin exists and restricts resolver
  edges to syntactic alias classes.  It deliberately carries no denotation or
  equality theorem: later selector soundness must connect these certificates
  to erasure.
-/

import Gimbal.Equality.Scherer.LocalSourceTree

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Alias classes and introductions -/

/-- The only origin classes in which the resolver may add an edge. -/
inductive AliasClassKey (R : AliasResolver sig) where
  | observation {A : Object sig.nBases} : ExactObsKey R A → AliasClassKey R
  | splitL {A B : Object sig.nBases} :
      ResolvedRef R (.coprod A B) → AliasClassKey R
  | splitR {A B : Object sig.nBases} :
      ResolvedRef R (.coprod A B) → AliasClassKey R

/-- A finite-ledger explanation for one allocated origin and its alias class. -/
inductive OriginIntro (R : AliasResolver sig) :
    Origin sig → Option (AliasClassKey R) → Prop
  | root {A : Object sig.nBases} (slot rank : Nat)
      (terminal : R.target (rootOrigin sig A slot rank).raw = none) :
      OriginIntro R (rootOrigin sig A slot rank).raw none
  | lambda {A : Object sig.nBases} (addr : LocalAddr) (pre : OriginScope)
      (rank : Nat) (fresh : pre.nextRank ≤ rank)
      (terminal : R.target (stableOrigin sig A addr.code rank).raw = none) :
      OriginIntro R (stableOrigin sig A addr.code rank).raw none
  | splitL {A B : Object sig.nBases} (addr : LocalAddr)
      (pre : OriginScope) (parent : ResolvedRef R (.coprod A B))
      (id rank : Nat) (fresh : pre.nextRank ≤ rank)
      (parent_lt : parent.origin.raw.introRank < rank) :
      OriginIntro R (splitLeftOrigin parent.origin id rank).raw
        (some (.splitL parent))
  | splitR {A B : Object sig.nBases} (addr : LocalAddr)
      (pre : OriginScope) (parent : ResolvedRef R (.coprod A B))
      (id rank : Nat) (fresh : pre.nextRank ≤ rank)
      (parent_lt : parent.origin.raw.introRank < rank) :
      OriginIntro R (splitRightOrigin parent.origin id rank).raw
        (some (.splitR parent))
  | observation {A : Object sig.nBases} (addr : LocalAddr) (entry : Nat)
      (pre : OriginScope) (key : ExactObsKey R A)
      (id rank : Nat) (fresh : pre.nextRank ≤ rank)
      (deps_lt : ∀ o ∈ key.deps, o.introRank < rank) :
      OriginIntro R (observationOrigin sig A addr.code entry id rank).raw
        (some (.observation key))

namespace OriginIntro

/-- The only introductions with no alias class are rigid and terminal. -/
theorem rigid_terminal {R : AliasResolver sig} {o : Origin sig}
    (h : OriginIntro R o none) : R.target o = none := by
  cases h with
  | root _ _ terminal | lambda _ _ _ _ terminal => exact terminal

end OriginIntro

/-! ### Finite ledger -/

/-- A finite allocation table closed under every resolver edge. -/
structure OriginLedger (R : AliasResolver sig) where
  allocated : Finset (Origin sig)
  introClass : Origin sig → Option (AliasClassKey R)
  intro : ∀ o, o ∈ allocated → OriginIntro R o (introClass o)
  target_source : ∀ {x y}, R.target x = some y → x ∈ allocated
  target_target : ∀ {x y}, R.target x = some y → y ∈ allocated
  target_sameClass : ∀ {x y} (_h : R.target x = some y),
    ∃ k, introClass x = some k ∧ introClass y = some k

namespace OriginLedger

variable {R : AliasResolver sig} (L : OriginLedger R)

/-- Reflexive-transitive, path-local traversal of resolver edges. -/
inductive Follows : Origin sig → Origin sig → Prop
  | refl (x) : Follows x x
  | step {x y z} : R.target x = some y → Follows y z → Follows x z

theorem target_has_common_class {x y : Origin sig}
    (h : R.target x = some y) :
    ∃ k, L.introClass x = some k ∧ L.introClass y = some k :=
  L.target_sameClass h

/-- A resolver chain never crosses an alias class. -/
theorem follows_preserves_class {x z : Origin sig}
    (h : Follows (R := R) x z)
    (hx : x ∈ L.allocated) {k : AliasClassKey R}
    (hclass : L.introClass x = some k) :
    ∃ _hz : z ∈ L.allocated, L.introClass z = some k := by
  induction h with
  | refl x => exact ⟨hx, hclass⟩
  | @step x y z hxy _ ih =>
      obtain ⟨c, hxc, hyc⟩ := L.target_sameClass hxy
      have hkc : k = c := Option.some.inj (hclass.symm.trans hxc)
      subst c
      exact ih (L.target_target hxy) hyc

/-- Any two allocated endpoints reached from one classified origin agree. -/
theorem class_eq_of_follows {x y z : Origin sig}
    (hxy : Follows (R := R) x y) (hxz : Follows (R := R) x z)
    (hx : x ∈ L.allocated) {ky kz : AliasClassKey R}
    (hy : ∀ _hy : y ∈ L.allocated,
      L.introClass y = some ky)
    (hz : ∀ _hz : z ∈ L.allocated,
      L.introClass z = some kz)
    (hstart : ∃ k, L.introClass x = some k) : ky = kz := by
  obtain ⟨k, hk⟩ := hstart
  obtain ⟨hym, hymc⟩ := L.follows_preserves_class hxy hx hk
  obtain ⟨hzm, hzmc⟩ := L.follows_preserves_class hxz hx hk
  exact Option.some.inj ((hy hym).symm.trans (hymc.trans (hzmc.symm.trans (hz hzm))))

/-- A rigid introduction can never be the source of a resolver edge. -/
theorem target_eq_none_of_aliasClass_none {x : Origin sig}
    (_hx : x ∈ L.allocated)
    (hnone : L.introClass x = none) : R.target x = none := by
  cases htarget : R.target x with
  | none => rfl
  | some y =>
      obtain ⟨k, hk, _⟩ := L.target_sameClass htarget
      rw [hnone] at hk
      contradiction

/-- In particular every recorded root or lambda introduction is terminal. -/
theorem rigid_terminal {x : Origin sig} (hx : x ∈ L.allocated)
    (hnone : L.introClass x = none) : R.target x = none :=
  L.target_eq_none_of_aliasClass_none hx hnone

/-- One resolver edge preserves its exact declared class. -/
theorem target_class_eq {x y : Origin sig} (h : R.target x = some y)
    {kx ky : AliasClassKey R}
    (hx : L.introClass x = some kx)
    (hy : L.introClass y = some ky) : kx = ky := by
  obtain ⟨k, hs, ht⟩ := L.target_sameClass h
  exact (Option.some.inj (hx.symm.trans hs)).trans
    (Option.some.inj (hy.symm.trans ht)).symm

theorem observation_key_eq_of_target {x y : Origin sig}
    (h : R.target x = some y) {A : Object sig.nBases}
    {left right : ExactObsKey R A}
    (hx : L.introClass x = some (.observation left))
    (hy : L.introClass y = some (.observation right)) : left = right := by
  have hc := L.target_class_eq h hx hy
  cases hc
  rfl

theorem splitL_parent_eq_of_target {x y : Origin sig}
    (h : R.target x = some y) {A B : Object sig.nBases}
    {left right : ResolvedRef R (.coprod A B)}
    (hx : L.introClass x = some (.splitL left))
    (hy : L.introClass y = some (.splitL right)) :
    left = right := by
  have hc := L.target_class_eq h hx hy
  cases hc
  rfl

theorem splitR_parent_eq_of_target {x y : Origin sig}
    (h : R.target x = some y) {A B : Object sig.nBases}
    {left right : ResolvedRef R (.coprod A B)}
    (hx : L.introClass x = some (.splitR left))
    (hy : L.introClass y = some (.splitR right)) :
    left = right := by
  have hc := L.target_class_eq h hx hy
  cases hc
  rfl

/-- Observation aliases cannot target a root, binder, or differently keyed result. -/
theorem no_target_of_class_ne {x y : Origin sig} (h : R.target x = some y)
    {kx ky : AliasClassKey R}
    (hx : L.introClass x = some kx)
    (hy : L.introClass y = some ky)
    (hne : kx ≠ ky) : False :=
  hne (L.target_class_eq h hx hy)

theorem no_target_to_rigid {x y : Origin sig} (h : R.target x = some y)
    {kx : AliasClassKey R}
    (_hx : L.introClass x = some kx)
    (hy : L.introClass y = none) : False := by
  obtain ⟨k, _, htarget⟩ := L.target_sameClass h
  rw [hy] at htarget
  contradiction

/-- Following `target` computes a path in the finite edge relation. -/
theorem follows_resolve (x : Origin sig) :
    Follows (R := R) x (R.resolve x) := by
  induction x using AliasResolver.resolve.induct R with
  | case1 x hx =>
      rw [AliasResolver.resolve.eq_1, hx]
      exact .refl x
  | case2 x y hxy ih =>
      rw [AliasResolver.resolve.eq_1, hxy]
      exact .step hxy ih

/-- Distinct declared classes cannot acquire a common terminal representative. -/
theorem not_equivalent_of_class_ne {x y : Origin sig}
    (hx : x ∈ L.allocated) (hy : y ∈ L.allocated)
    {kx ky : AliasClassKey R}
    (hcx : L.introClass x = some kx)
    (hcy : L.introClass y = some ky)
    (hne : kx ≠ ky) : ¬ R.Equivalent x y := by
  intro heq
  obtain ⟨hrx, hrcx⟩ := L.follows_preserves_class
    (follows_resolve (R := R) x) hx hcx
  obtain ⟨hry, hrcy⟩ := L.follows_preserves_class
    (follows_resolve (R := R) y) hy hcy
  unfold AliasResolver.Equivalent at heq
  have hyAt : R.resolve x ∈ L.allocated ∧
      L.introClass (R.resolve x) = some ky :=
    heq.symm ▸ ⟨hry, hrcy⟩
  obtain ⟨hry, hrcy⟩ := hyAt
  exact hne (Option.some.inj (hrcx.symm.trans hrcy))

/-- In particular, left and right split payloads never alias. -/
theorem opposite_splits_not_equivalent {x y : Origin sig}
    (hx : x ∈ L.allocated) (hy : y ∈ L.allocated)
    {A B C D : Object sig.nBases}
    (left : ResolvedRef R (.coprod A B))
    (right : ResolvedRef R (.coprod C D))
    (hleft : L.introClass x = some (.splitL left))
    (hright : L.introClass y = some (.splitR right)) :
    ¬ R.Equivalent x y :=
  L.not_equivalent_of_class_ne hx hy hleft hright (by intro h; cases h)

end OriginLedger

/-! ### Canonical roots and freshness gates -/

/-- An injective typed table of root representatives. -/
structure RootAllocation (R : AliasResolver sig) (n : Nat)
    (ty : Fin n → Object sig.nBases) where
  ref : ∀ i, ResolvedRef R (ty i)
  injective : Function.Injective (fun i => (ref i).origin.raw)

namespace RootAllocation

/-- Canonical roots for the identity resolver use their finite slot as id. -/
def canonical (sig : Signature) (n rank : Nat)
    (ty : Fin n → Object sig.nBases) :
    RootAllocation (AliasResolver.identity sig) n ty where
  ref i := ⟨rootOrigin sig (ty i) i.val rank, rfl⟩
  injective := by
    intro i j h
    apply Fin.ext
    exact congrArg Origin.id h

end RootAllocation

/-- Origins already accessible before an introduction. -/
def AccessibleAt (pre : OriginScope) (xs : Finset (Origin sig)) : Prop :=
  ∀ o ∈ xs, pre.Contains o

/-- A fresh lambda/split allocation cannot reuse an accessible pre-origin. -/
theorem fresh_not_accessible (pre : OriginScope) (xs : Finset (Origin sig))
    (hxs : AccessibleAt pre xs) (o : Origin sig)
    (hfresh : pre.nextRank ≤ o.introRank) : o ∉ xs := by
  intro ho
  exact (Nat.not_lt_of_ge hfresh) (hxs o ho)

/-- Store steps are aliases in assignments, not origin-allocation events. -/
theorem store_reuses_pending_atom (E : OriginAssignment R Γ)
    (pending : PendingAssignment R (.cons (.atom q) ps)) :
    (E.storeAtom pending).ref
        (.here : StableVar (Γ.snoc (.atom q)) (.atom q)) =
      pending.ref (.here : PendingVar (.cons (.atom q) ps) (.atom q)) := rfl

theorem store_reuses_pending_shift (E : OriginAssignment R Γ)
    (pending : PendingAssignment R (.cons (.shift N) ps)) :
    (E.storeShift pending).ref
        (.here : StableVar (Γ.snoc (.neg N)) (.neg N)) =
      pending.ref (.here : PendingVar (.cons (.shift N) ps) (.shift N)) := rfl

/-! ### Boundary regressions -/

namespace OriginLedgerFixtures

open PairTraceFixtures

abbrev AtomP : Pos TwoGenSig.nBases := .atom q0

def rootTy (_ : Fin 2) : Object TwoGenSig.nBases := Q

def roots : RootAllocation (AliasResolver.identity TwoGenSig) 2 rootTy :=
  RootAllocation.canonical TwoGenSig 2 0 rootTy

/-- Canonical root slots are injective and cannot resolve together. -/
theorem distinct_root_slots_cannot_resolve :
    ¬ (AliasResolver.identity TwoGenSig).Equivalent
      (roots.ref ⟨0, by decide⟩).origin.raw
      (roots.ref ⟨1, by decide⟩).origin.raw := by native_decide

def oldRoot : TypedOrigin TwoGenSig Q := rootOrigin TwoGenSig Q 0 0
def lambdaFresh : TypedOrigin TwoGenSig Q :=
  stableOrigin TwoGenSig Q (LocalAddr.code []) 1
def preOne : OriginScope := ⟨1⟩
def oldOnly : Finset (Origin TwoGenSig) := {oldRoot.raw}

theorem oldOnly_accessible : AccessibleAt preOne oldOnly := by
  intro o ho
  have hoeq : o = oldRoot.raw := Finset.mem_singleton.mp ho
  rw [hoeq]
  show oldRoot.raw.introRank < preOne.nextRank
  decide

/-- A fresh lambda binder cannot silently reuse an accessible root. -/
theorem lambda_binder_cannot_reuse_old_root : lambdaFresh.raw ∉ oldOnly :=
  fresh_not_accessible preOne oldOnly oldOnly_accessible lambdaFresh.raw (by decide)

theorem lambdaIntro :
    OriginIntro (AliasResolver.identity TwoGenSig) lambdaFresh.raw none :=
  .lambda [] preOne 1 (by decide) rfl

theorem lambda_binder_is_terminal :
    (AliasResolver.identity TwoGenSig).target lambdaFresh.raw = none :=
  lambdaIntro.rigid_terminal

def sumParent : TypedOrigin TwoGenSig (.coprod Q Q) :=
  rootOrigin TwoGenSig (.coprod Q Q) 10 0
def leftOld : TypedOrigin TwoGenSig Q := splitLeftOrigin sumParent 11 1
def leftNew : TypedOrigin TwoGenSig Q := splitLeftOrigin sumParent 12 2
def rightNew : TypedOrigin TwoGenSig Q := splitRightOrigin sumParent 13 2

def splitResolver : AliasResolver TwoGenSig :=
  AliasResolver.single leftNew.raw leftOld.raw rfl (by decide)

def splitParentRef : ResolvedRef splitResolver (.coprod Q Q) :=
  ⟨sumParent, by native_decide⟩

theorem same_parent_same_tag_may_alias :
    splitResolver.Equivalent leftNew.raw leftOld.raw := by native_decide

theorem split_payload_fresh_against_old_root : leftOld.raw ∉ oldOnly :=
  fresh_not_accessible preOne oldOnly oldOnly_accessible leftOld.raw (by decide)

/-- A split payload cannot resolve to an unrelated accessible atom. -/
theorem split_payload_not_unrelated_outer_atom :
    splitResolver.resolve leftNew.raw ≠ splitResolver.resolve oldRoot.raw := by
  native_decide

theorem opposite_split_classes_distinct :
    AliasClassKey.splitL splitParentRef ≠ AliasClassKey.splitR splitParentRef := by
  intro h
  cases h

theorem opposite_tags_never_resolve_together :
    ¬ splitResolver.Equivalent leftNew.raw rightNew.raw := by native_decide

def obsRoot : TypedOrigin TwoGenSig Q := rootOrigin TwoGenSig Q 20 0
def obsA : TypedOrigin TwoGenSig Q :=
  observationOrigin TwoGenSig Q (LocalAddr.code []) 0 31 2
def obsADup : TypedOrigin TwoGenSig Q :=
  observationOrigin TwoGenSig Q (LocalAddr.code []) 1 32 3

def observationResolver : AliasResolver TwoGenSig :=
  AliasResolver.single obsADup.raw obsA.raw rfl (by decide)

def obsRootRef : ResolvedRef observationResolver Q :=
  ⟨obsRoot, by native_decide⟩

def observationKey : ExactObsKey observationResolver Q :=
  ExactObsKey.ofStructural
    (.var (.free obsRootRef) : SNegCode observationResolver .empty (.shift AtomP))

def observationAllocated : Finset (Origin TwoGenSig) :=
  {obsRoot.raw, obsA.raw, obsADup.raw}

/-- The duplicate quotient is accepted by an actual finite ledger. -/
def observationLedger : OriginLedger observationResolver where
  allocated := observationAllocated
  introClass o := if o = obsRoot.raw then none else some (.observation observationKey)
  intro := by
    intro o ho
    simp only [observationAllocated, Finset.mem_insert,
      Finset.mem_singleton] at ho
    rcases ho with h | h | h
    · subst o
      exact OriginIntro.root 20 0 (by native_decide)
    · subst o
      have hne : obsA.raw ≠ obsRoot.raw := by native_decide
      rw [if_neg hne]
      exact OriginIntro.observation [] 0 preOne observationKey 31 2
        (by decide) (by
        intro o ho
        simp [observationKey, ExactObsKey.ofStructural, SNegCode.freeDeps,
          CanonRef.freeDeps, obsRootRef] at ho
        subst o
        decide)
    · subst o
      have hne : obsADup.raw ≠ obsRoot.raw := by native_decide
      rw [if_neg hne]
      exact OriginIntro.observation [] 1 preOne observationKey 32 3
        (by decide) (by
        intro o ho
        simp [observationKey, ExactObsKey.ofStructural, SNegCode.freeDeps,
          CanonRef.freeDeps, obsRootRef] at ho
        subst o
        decide)
  target_source := by
    intro x y h
    have hx : x = obsADup.raw := by
      by_contra hne
      simp [observationResolver, AliasResolver.single, hne] at h
    subst x
    simp [observationResolver, AliasResolver.single] at h
    subst y
    simp [observationAllocated]
  target_target := by
    intro x y h
    have hx : x = obsADup.raw := by
      by_contra hne
      simp [observationResolver, AliasResolver.single, hne] at h
    subst x
    simp [observationResolver, AliasResolver.single] at h
    subst y
    simp [observationAllocated]
  target_sameClass := by
    intro x y h
    have hx : x = obsADup.raw := by
      by_contra hne
      simp [observationResolver, AliasResolver.single, hne] at h
    subst x
    simp [observationResolver, AliasResolver.single] at h
    subst y
    exact ⟨.observation observationKey, by
      rw [if_neg (by native_decide : obsADup.raw ≠ obsRoot.raw)], by
      rw [if_neg (by native_decide : obsA.raw ≠ obsRoot.raw)]⟩

/-- Equal-key duplicate observations may alias; both literal occurrences remain. -/
theorem equal_key_duplicate_observations_may_alias :
    observationResolver.Equivalent obsADup.raw obsA.raw ∧
      [obsA.raw, obsADup.raw].length = 2 := by native_decide

theorem duplicate_edge_has_exact_key_class :
    ∃ k, observationLedger.introClass obsADup.raw = some k ∧
      observationLedger.introClass obsA.raw = some k := by
  exact observationLedger.target_sameClass (by
    simp [observationResolver, AliasResolver.single])

/-- Even a one-entry observation edge cannot target an unrelated root. -/
theorem one_entry_observation_not_unrelated_root :
    observationResolver.target obsADup.raw ≠ some obsRoot.raw := by native_decide

/-- Store syntax introduces no identity: its stable cell is the pending ref. -/
theorem stores_introduce_no_identity :
    ((OriginAssignment.empty _).storeAtom PairOriginFixtures.pendingOne).ref
        (.here : StableVar
          ((StableCtx.empty : StableCtx TwoGenSig).snoc (.atom q0)) (.atom q0)) =
      PairOriginFixtures.pendingOne.ref
        (.here : PendingVar PairOriginFixtures.OnePending (.atom q0)) := rfl

end OriginLedgerFixtures

end Gimbal.Equality.Scherer
