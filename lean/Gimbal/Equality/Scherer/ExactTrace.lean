/-
  Resolver-owned exact traces and the literal selected-batch bridge.

  A trace stores its resolver before its exact-key family, so a resolver/key
  mismatch is not representable.  Batch construction keeps literal order and
  multiplicity; quotient evidence is local to the allocated batch results.
-/

import Gimbal.Equality.Scherer.ExactObsKey

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Resolver-owned traces -/

/-- An exact trace whose key family is definitionally owned by its resolver. -/
structure ExactTrace (sig : Signature) where
  resolver : AliasResolver sig
  steps : List (TraceStep (exactObsKeys resolver))
  isWellFormed :
    ({ resolver := resolver, steps := steps } :
      TypedTrace (exactObsKeys resolver)).WellFormed

namespace ExactTrace

def toTypedTrace (T : ExactTrace sig) :
    TypedTrace (exactObsKeys T.resolver) where
  resolver := T.resolver
  steps := T.steps

@[simp] theorem toTypedTrace_resolver (T : ExactTrace sig) :
    T.toTypedTrace.resolver = T.resolver := rfl

@[simp] theorem toTypedTrace_steps (T : ExactTrace sig) :
    T.toTypedTrace.steps = T.steps := rfl

theorem wellFormed (T : ExactTrace sig) : T.toTypedTrace.WellFormed :=
  T.isWellFormed

end ExactTrace

/-! ### Literal batch positions and fresh result plans -/

def PendingVar.index : PendingVar selected P → Nat
  | .here => 0
  | .there x => x.index + 1

/--
Per-occurrence metadata for a literal selected batch.  No site or result is
looked up globally and no two occurrences are deduplicated.
-/
structure BatchObservationPlan (pre : OriginScope) (selected : Pending sig) where
  site : ∀ {P}, PendingVar selected P → Nat
  support : ∀ {P}, PendingVar selected P → Nat
  entry : ∀ {P}, PendingVar selected P → Nat
  ident : ∀ {P}, PendingVar selected P → Nat
  rank : ∀ {P}, PendingVar selected P → Nat
  fresh : ∀ {P} (x : PendingVar selected P), pre.nextRank ≤ rank x

namespace BatchObservationPlan

def result (plan : BatchObservationPlan pre selected)
    {P : Pos sig.nBases} (x : PendingVar selected P) :
    TypedOrigin sig P.erase :=
  observationOrigin sig P.erase (plan.site x) (plan.entry x)
    (plan.ident x) (plan.rank x)

@[simp] theorem result_rank (plan : BatchObservationPlan pre selected)
    {P : Pos sig.nBases} (x : PendingVar selected P) :
    (plan.result x).raw.introRank = plan.rank x := rfl

@[simp] theorem result_kind (plan : BatchObservationPlan pre selected)
    {P : Pos sig.nBases} (x : PendingVar selected P) :
    (plan.result x).raw.kind = .observation (plan.site x) (plan.entry x) := rfl

theorem result_fresh (plan : BatchObservationPlan pre selected)
    {P : Pos sig.nBases} (x : PendingVar selected P) :
    pre.nextRank ≤ (plan.result x).raw.introRank :=
  plan.fresh x

def tail (plan : BatchObservationPlan pre (.cons Q ps)) :
    BatchObservationPlan pre ps where
  site x := plan.site (.there x)
  support x := plan.support (.there x)
  entry x := plan.entry (.there x)
  ident x := plan.ident (.there x)
  rank x := plan.rank (.there x)
  fresh x := plan.fresh (.there x)

end BatchObservationPlan

/-! ### Entrywise normalization and observation steps -/

def NonemptyBatchObs.neutralAt (obs : NonemptyBatchObs Γ selected) :
    ∀ {P}, PendingVar selected P → SNegNeu Γ (.shift P) :=
  match obs with
  | .one n => fun x => match x with
      | .here => n
  | .cons n rest => fun x => match x with
      | .here => n
      | .there x => rest.neutralAt x

def NonemptyBatchObs.exactKeyAt (obs : NonemptyBatchObs Γ selected)
    (supply : BatchResultSupply R) (E : OriginAssignment R Γ)
    {P : Pos sig.nBases} (x : PendingVar selected P) :
    ExactObsKey R P.erase :=
  ExactObsKey.ofNeutral supply E (obs.neutralAt x)

def NonemptyBatchObs.observeAt (obs : NonemptyBatchObs Γ selected)
    (supply : BatchResultSupply R) (E : OriginAssignment R Γ)
    (plan : BatchObservationPlan pre selected)
    {P : Pos sig.nBases} (x : PendingVar selected P) :
    TraceStep (exactObsKeys R) :=
  .observe (plan.site x) (plan.support x) pre
    (obs.exactKeyAt supply E x) (plan.result x)

def TraceStep.exactCode? {R : AliasResolver sig} :
    TraceStep (exactObsKeys R) → Option Nat
  | .observe _ _ _ key _ => some (ExactObsKey.code key)
  | _ => none

def NonemptyBatchObs.observationSteps
    (obs : NonemptyBatchObs Γ selected)
    (supply : BatchResultSupply R) (E : OriginAssignment R Γ)
    (plan : BatchObservationPlan pre selected) :
    List (TraceStep (exactObsKeys R)) :=
  match obs with
  | .one n =>
      [TraceStep.observe (plan.site (.here : PendingVar (.cons _ .empty) _))
        (plan.support (.here : PendingVar (.cons _ .empty) _)) pre
        (ExactObsKey.ofNeutral supply E n)
        (plan.result (.here : PendingVar (.cons _ .empty) _))]
  | .cons n rest =>
      TraceStep.observe (plan.site (.here : PendingVar (.cons _ _) _))
        (plan.support (.here : PendingVar (.cons _ _) _)) pre
        (ExactObsKey.ofNeutral supply E n)
        (plan.result (.here : PendingVar (.cons _ _) _)) ::
          rest.observationSteps supply E plan.tail

@[simp] theorem NonemptyBatchObs.observationSteps_one
    (n : SNegNeu Γ (.shift Q)) (supply : BatchResultSupply R)
    (E : OriginAssignment R Γ)
    (plan : BatchObservationPlan pre (.cons Q .empty)) :
    (NonemptyBatchObs.one n).observationSteps supply E plan =
      [(NonemptyBatchObs.one n).observeAt supply E plan .here] := rfl

@[simp] theorem NonemptyBatchObs.observationSteps_cons
    (n : SNegNeu Γ (.shift Q)) (rest : NonemptyBatchObs Γ ps)
    (supply : BatchResultSupply R) (E : OriginAssignment R Γ)
    (plan : BatchObservationPlan pre (.cons Q ps)) :
    (NonemptyBatchObs.cons n rest).observationSteps supply E plan =
      (NonemptyBatchObs.cons n rest).observeAt supply E plan .here ::
        rest.observationSteps supply E plan.tail := rfl

def NonemptyBatchObs.length : NonemptyBatchObs Γ selected → Nat
  | .one _ => 1
  | .cons _ rest => rest.length + 1

@[simp] theorem NonemptyBatchObs.observationSteps_length
    (obs : NonemptyBatchObs Γ selected) (supply : BatchResultSupply R)
    (E : OriginAssignment R Γ) (plan : BatchObservationPlan pre selected) :
    (obs.observationSteps supply E plan).length = obs.length := by
  cases obs with
  | one => rfl
  | cons n rest =>
      simp [NonemptyBatchObs.observationSteps, NonemptyBatchObs.length,
        NonemptyBatchObs.observationSteps_length rest supply E plan.tail]
termination_by selected.length
decreasing_by simp_all [Pending.length]

theorem NonemptyBatchObs.observeAt_mem_observationSteps
    (obs : NonemptyBatchObs Γ selected) (supply : BatchResultSupply R)
    (E : OriginAssignment R Γ) (plan : BatchObservationPlan pre selected)
    {P : Pos sig.nBases} (x : PendingVar selected P) :
    obs.observeAt supply E plan x ∈ obs.observationSteps supply E plan := by
  cases obs with
  | one n =>
      cases x with
      | here => simp
      | there x => nomatch x
  | cons n rest =>
      cases x with
      | here => simp
      | there x =>
          simp only [observationSteps_cons, List.mem_cons]
          right
          exact rest.observeAt_mem_observationSteps supply E plan.tail x
termination_by selected.length
decreasing_by simp_all [Pending.length]

theorem NonemptyBatchObs.exists_observeAt_of_mem_observationSteps
    (obs : NonemptyBatchObs Γ selected) (supply : BatchResultSupply R)
    (E : OriginAssignment R Γ) (plan : BatchObservationPlan pre selected)
    {s : TraceStep (exactObsKeys R)}
    (hs : s ∈ obs.observationSteps supply E plan) :
    ∃ (P : Pos sig.nBases) (x : PendingVar selected P),
      s = obs.observeAt supply E plan x := by
  cases obs with
  | one n =>
      simp only [observationSteps_one, List.mem_singleton] at hs
      exact ⟨_, .here, hs⟩
  | cons n rest =>
      simp only [observationSteps_cons, List.mem_cons] at hs
      rcases hs with hs | hs
      · exact ⟨_, .here, hs⟩
      · obtain ⟨P, x, hx⟩ :=
          rest.exists_observeAt_of_mem_observationSteps supply E plan.tail hs
        exact ⟨P, .there x, hx⟩
termination_by selected.length
decreasing_by simp_all [Pending.length]

/-! ### Certified exact batch packages -/

/--
A literal batch together with scoped inputs, fresh result allocation, and the
local exact quotient law required of its result origins.
-/
structure ExactBatch (R : AliasResolver sig) (supply : BatchResultSupply R)
    (E : OriginAssignment R Γ) (obs : NonemptyBatchObs Γ selected) where
  pre : OriginScope
  plan : BatchObservationPlan pre selected
  assignmentScoped : (CodeOriginAssignment.ofOrigin E).Scoped pre
  resultsQuotiented :
    ∀ {P Q : Pos sig.nBases} (x : PendingVar selected P)
      (y : PendingVar selected Q),
      (P.erase, ExactObsKey.code (obs.exactKeyAt supply E x)) =
          (Q.erase, ExactObsKey.code (obs.exactKeyAt supply E y)) ↔
        R.Equivalent (plan.result x).raw (plan.result y).raw

namespace ExactBatch

variable {R : AliasResolver sig} {Γ : StableCtx sig}
  {selected : Pending sig} {supply : BatchResultSupply R}
  {E : OriginAssignment R Γ} {obs : NonemptyBatchObs Γ selected}

def keyPackage (_B : ExactBatch R supply E obs) : OrderedBatchKeys R selected :=
  obs.toExactKeys supply E

def steps (B : ExactBatch R supply E obs) :
    List (TraceStep (exactObsKeys R)) :=
  obs.observationSteps supply E B.plan

theorem pairedLiteral_same_packages (_B : ExactBatch R supply E obs) :
    _B.keyPackage = _B.keyPackage ∧ _B.steps = _B.steps :=
  ⟨rfl, rfl⟩

theorem dependency_precedes_result (B : ExactBatch R supply E obs)
    {P : Pos sig.nBases} (x : PendingVar selected P)
    (o : Origin sig) (ho : o ∈ (obs.exactKeyAt supply E x).deps) :
    o.introRank < (B.plan.result x).raw.introRank := by
  have hpre : o.introRank < B.pre.nextRank :=
    ExactObsKey.ofNeutral_scoped supply E (obs.neutralAt x)
      B.assignmentScoped o ho
  exact Nat.lt_of_lt_of_le hpre (B.plan.result_fresh x)

theorem observeAt_scoped (B : ExactBatch R supply E obs)
    {P : Pos sig.nBases} (x : PendingVar selected P) :
    (obs.observeAt supply E B.plan x).Scoped := by
  constructor
  · exact ExactObsKey.ofNeutral_scoped supply E (obs.neutralAt x)
      B.assignmentScoped
  · exact B.plan.result_fresh x

theorem stepsScoped (B : ExactBatch R supply E obs) :
    ∀ s ∈ B.steps, s.Scoped := by
  intro s hs
  obtain ⟨P, x, rfl⟩ :=
    obs.exists_observeAt_of_mem_observationSteps supply E B.plan hs
  exact B.observeAt_scoped x

theorem splitsFunctional (B : ExactBatch R supply E obs) :
    ({ resolver := R, steps := B.steps } :
      TypedTrace (exactObsKeys R)).SplitsFunctional := by
  intro s hs t ht htag hsome _
  obtain ⟨P, x, rfl⟩ :=
    obs.exists_observeAt_of_mem_observationSteps supply E B.plan hs
  simp [NonemptyBatchObs.observeAt, TraceStep.splitTag?] at hsome

theorem observationsQuotiented (B : ExactBatch R supply E obs) :
    ({ resolver := R, steps := B.steps } :
      TypedTrace (exactObsKeys R)).ObservationsQuotiented := by
  intro s hs t ht ks kt hsig htig
  obtain ⟨P, x, rfl⟩ :=
    obs.exists_observeAt_of_mem_observationSteps supply E B.plan hs
  obtain ⟨Q, y, rfl⟩ :=
    obs.exists_observeAt_of_mem_observationSteps supply E B.plan ht
  simp only [NonemptyBatchObs.observeAt, TraceStep.keySig?,
    Option.some.injEq] at hsig htig
  subst ks
  subst kt
  constructor
  · intro hkey
    refine ⟨(B.plan.result x).raw, (B.plan.result y).raw, rfl, rfl, ?_⟩
    exact (B.resultsQuotiented x y).mp hkey
  · rintro ⟨left, right, hleft, hright, heq⟩
    simp only [NonemptyBatchObs.observeAt, TraceStep.result?,
      Option.some.injEq] at hleft hright
    subst left
    subst right
    exact (B.resultsQuotiented x y).mpr heq

theorem wellFormed (B : ExactBatch R supply E obs) :
    ({ resolver := R, steps := B.steps } :
      TypedTrace (exactObsKeys R)).WellFormed where
  stepsScoped := B.stepsScoped
  splitsFunctional := B.splitsFunctional
  observationsQuotiented := B.observationsQuotiented

def toExactTrace (B : ExactBatch R supply E obs) : ExactTrace sig where
  resolver := R
  steps := B.steps
  isWellFormed := B.wellFormed

end ExactBatch

/-! ### Adversarial fixtures -/

namespace ExactTraceFixtures

open PairTraceFixtures
open PairStructuralCodeFixtures
open ExactObsKeyFixtures

/-- One resolver used only by the alias-chain fixture: it resolves both the
two-step stored source and the second raw observation result. -/
def traceResolver : AliasResolver TwoGenSig where
  target := fun x =>
    if x = store2.raw then some store1.raw
    else if x = store1.raw then some atom0.raw
    else if x = obsADuplicate.raw then some obsA.raw
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
      · by_cases hd : x = obsADuplicate.raw
        · subst x
          simp [h2, h1] at h
          subst y
          exact obsA.type_eq.trans obsADuplicate.type_eq.symm
        · simp [h2, h1, hd] at h
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
      · by_cases hd : x = obsADuplicate.raw
        · subst x
          simp [h2, h1] at h
          subst y
          decide
        · simp [h2, h1, hd] at h

theorem traceResolver_store2 :
    traceResolver.resolve store2.raw = atom0.raw := by
  calc
    _ = traceResolver.resolve store1.raw := by
      apply AliasResolver.resolve_eq_resolve_of_target_eq_some
      simp [traceResolver]
    _ = traceResolver.resolve atom0.raw := by
      apply AliasResolver.resolve_eq_resolve_of_target_eq_some
      have h12 : store1.raw ≠ store2.raw := by decide
      simp [traceResolver, h12]
    _ = atom0.raw := by
      apply AliasResolver.resolve_eq_self_of_target_eq_none
      have h02 : atom0.raw ≠ store2.raw := by decide
      have h01 : atom0.raw ≠ store1.raw := by decide
      have h0d : atom0.raw ≠ obsADuplicate.raw := by decide
      simp [traceResolver, h02, h01, h0d]

theorem traceResolver_atom0 :
    traceResolver.resolve atom0.raw = atom0.raw := by
  apply AliasResolver.resolve_eq_self_of_target_eq_none
  have h02 : atom0.raw ≠ store2.raw := by decide
  have h01 : atom0.raw ≠ store1.raw := by decide
  have h0d : atom0.raw ≠ obsADuplicate.raw := by decide
  simp [traceResolver, h02, h01, h0d]

theorem traceResolver_obsDuplicate :
    traceResolver.resolve obsADuplicate.raw = obsA.raw := by
  rw [AliasResolver.resolve_eq_resolve_of_target_eq_some]
  · apply AliasResolver.resolve_eq_self_of_target_eq_none
    have ha2 : obsA.raw ≠ store2.raw := by decide
    have ha1 : obsA.raw ≠ store1.raw := by decide
    have had : obsA.raw ≠ obsADuplicate.raw := by decide
    simp [traceResolver, ha2, ha1, had]
  · have hd2 : obsADuplicate.raw ≠ store2.raw := by decide
    have hd1 : obsADuplicate.raw ≠ store1.raw := by decide
    simp [traceResolver, hd2, hd1]

theorem traceResolver_obsA :
    traceResolver.resolve obsA.raw = obsA.raw := by
  apply AliasResolver.resolve_eq_self_of_target_eq_none
  have ha2 : obsA.raw ≠ store2.raw := by decide
  have ha1 : obsA.raw ≠ store1.raw := by decide
  have had : obsA.raw ≠ obsADuplicate.raw := by decide
  simp [traceResolver, ha2, ha1, had]

abbrev TwoSelected : Pending TwoGenSig := .cons P (.cons P .empty)

def twoValue (head tail : Nat) :
    ∀ {Q}, PendingVar TwoSelected Q → Nat
  | _, .here => head
  | _, .there .here => tail

def tracePre : OriginScope := ⟨1⟩

def distinctPlan : BatchObservationPlan tracePre TwoSelected where
  site := twoValue 3 4
  support := twoValue 7 9
  entry := twoValue 0 1
  ident := twoValue 20 22
  rank := twoValue 2 3
  fresh := by
    intro Q x
    cases x with
    | here => decide
    | there x =>
        cases x with
        | here => decide
        | there x => nomatch x

@[simp] theorem distinctPlan_result_here :
    distinctPlan.result (.here : PendingVar TwoSelected P) = obsA := rfl

@[simp] theorem distinctPlan_result_older :
    distinctPlan.result (.there .here : PendingVar TwoSelected P) = obsB := rfl

theorem obsAssignment_scoped :
    (CodeOriginAssignment.ofOrigin obsAssignment).Scoped tracePre := by
  intro S x
  cases x with
  | here =>
      change (ResolvedRef.of idR originB).origin.raw.introRank <
        tracePre.nextRank
      rw [ResolvedRef.of_raw,
        AliasResolver.resolve_eq_self_of_target_eq_none idR (by rfl)]
      decide
  | there x =>
      cases x with
      | here =>
          change (ResolvedRef.of idR originA).origin.raw.introRank <
            tracePre.nextRank
          rw [ResolvedRef.of_raw,
            AliasResolver.resolve_eq_self_of_target_eq_none idR (by rfl)]
          decide
      | there x => nomatch x

@[simp] theorem batchAB_key_here :
    batchAB.exactKeyAt (supply idR) obsAssignment
        (.here : PendingVar TwoSelected P) = newestKey := rfl

@[simp] theorem batchAB_key_older :
    batchAB.exactKeyAt (supply idR) obsAssignment
        (.there .here : PendingVar TwoSelected P) = olderKey := rfl

theorem newest_older_signature_ne :
    (P.erase, ExactObsKey.code newestKey) ≠
      (P.erase, ExactObsKey.code olderKey) := by
  intro h
  apply newest_older_key_distinct
  exact ExactObsKey.code_injective (Prod.mk.inj h).2

theorem obsA_obsB_not_equivalent :
    ¬idR.Equivalent obsA.raw obsB.raw := by
  unfold AliasResolver.Equivalent
  rw [AliasResolver.resolve_eq_self_of_target_eq_none,
    AliasResolver.resolve_eq_self_of_target_eq_none]
  · decide
  · rfl
  · rfl

def distinctBatch : ExactBatch idR (supply idR) obsAssignment batchAB where
  pre := tracePre
  plan := distinctPlan
  assignmentScoped := obsAssignment_scoped
  resultsQuotiented := by
    intro Q T x y
    cases x with
    | here =>
        cases y with
        | here => exact ⟨fun _ => rfl, fun _ => rfl⟩
        | there y =>
            cases y with
            | here =>
                exact ⟨fun h => (newest_older_signature_ne h).elim,
                  fun h => (obsA_obsB_not_equivalent h).elim⟩
            | there y => nomatch y
    | there x =>
        cases x with
        | here =>
            cases y with
            | here =>
                exact ⟨fun h => (newest_older_signature_ne h.symm).elim,
                  fun h => (obsA_obsB_not_equivalent
                    (idR.equivalent_symm h)).elim⟩
            | there y =>
                cases y with
                | here => exact ⟨fun _ => rfl, fun _ => rfl⟩
                | there y => nomatch y
        | there x => nomatch x

theorem distinctBatch_wellFormed :
    distinctBatch.toExactTrace.toTypedTrace.WellFormed :=
  distinctBatch.toExactTrace.wellFormed

/-- Equal result types do not merge distinct exact keys or result sources. -/
theorem same_type_different_keys_remain_separate :
    newestKey ≠ olderKey ∧ ¬idR.Equivalent obsA.raw obsB.raw :=
  ⟨newest_older_key_distinct, obsA_obsB_not_equivalent⟩

abbrev AliasPairCtx : StableCtx TwoGenSig :=
  ((StableCtx.empty : StableCtx TwoGenSig).snoc (.neg ShiftP)).snoc
    (.neg ShiftP)

def traceAliasAssignment : OriginAssignment traceResolver AliasPairCtx :=
  ((OriginAssignment.empty traceResolver).snoc (S := .neg ShiftP)
    (ResolvedRef.of traceResolver store2)).snoc (S := .neg ShiftP)
      (ResolvedRef.of traceResolver atom0)

def aliasNewest : SNegNeu AliasPairCtx ShiftP := .var .here
def aliasOlder : SNegNeu AliasPairCtx ShiftP := .var (.there .here)
def aliasBatch : NonemptyBatchObs AliasPairCtx TwoSelected :=
  .cons aliasNewest (.one aliasOlder)

def aliasPlan : BatchObservationPlan tracePre TwoSelected where
  site := twoValue 3 4
  support := twoValue 7 9
  entry := twoValue 0 0
  ident := twoValue 20 21
  rank := twoValue 2 3
  fresh := by
    intro Q x
    cases x with
    | here => decide
    | there x =>
        cases x with
        | here => decide
        | there x => nomatch x

@[simp] theorem aliasPlan_result_here :
    aliasPlan.result (.here : PendingVar TwoSelected P) = obsA := rfl

@[simp] theorem aliasPlan_result_older :
    aliasPlan.result (.there .here : PendingVar TwoSelected P) =
      obsADuplicate := rfl

theorem traceAliasAssignment_scoped :
    (CodeOriginAssignment.ofOrigin traceAliasAssignment).Scoped tracePre := by
  intro S x
  cases x with
  | here =>
      change (ResolvedRef.of traceResolver atom0).origin.raw.introRank <
        tracePre.nextRank
      rw [ResolvedRef.of_raw, traceResolver_atom0]
      decide
  | there x =>
      cases x with
      | here =>
          change (ResolvedRef.of traceResolver store2).origin.raw.introRank <
            tracePre.nextRank
          rw [ResolvedRef.of_raw, traceResolver_store2]
          decide
      | there x => nomatch x

theorem alias_keyAt_eq :
    aliasBatch.exactKeyAt (supply traceResolver) traceAliasAssignment
        (.here : PendingVar TwoSelected P) =
      aliasBatch.exactKeyAt (supply traceResolver) traceAliasAssignment
        (.there .here : PendingVar TwoSelected P) := by
  have href :
      traceAliasAssignment.ref
          (.here : StableVar AliasPairCtx (.neg ShiftP)) =
        traceAliasAssignment.ref
          (.there .here : StableVar AliasPairCtx (.neg ShiftP)) := by
    change ResolvedRef.of traceResolver (asShiftOrigin atom0) =
      ResolvedRef.of traceResolver (asShiftOrigin store2)
    rw [ResolvedRef.of_eq_iff]
    unfold AliasResolver.Equivalent
    change traceResolver.resolve atom0.raw = traceResolver.resolve store2.raw
    rw [traceResolver_atom0, traceResolver_store2]
  have hcode :
      aliasNewest.toStructuralCode (supply traceResolver)
          (CodeOriginAssignment.ofOrigin traceAliasAssignment) =
        aliasOlder.toStructuralCode (supply traceResolver)
          (CodeOriginAssignment.ofOrigin traceAliasAssignment) := by
    change SNegCode.var
        (CanonRef.free (traceAliasAssignment.ref
          (.here : StableVar AliasPairCtx (.neg ShiftP)))) =
      SNegCode.var
        (CanonRef.free (traceAliasAssignment.ref
          (.there .here : StableVar AliasPairCtx (.neg ShiftP))))
    rw [href]
  apply ExactObsKey.ext
  · exact congrArg SNegCode.toStructuralNatTree hcode
  · exact congrArg SNegCode.freeDeps hcode

theorem alias_keySig_eq
    {Q T : Pos TwoGenSig.nBases} (x : PendingVar TwoSelected Q)
    (y : PendingVar TwoSelected T) :
    (Q.erase, ExactObsKey.code
        (aliasBatch.exactKeyAt (supply traceResolver) traceAliasAssignment x)) =
      (T.erase, ExactObsKey.code
        (aliasBatch.exactKeyAt (supply traceResolver) traceAliasAssignment y)) := by
  cases x with
  | here =>
      cases y with
      | here => rfl
      | there y =>
          cases y with
          | here =>
              exact congrArg
                (fun k : ExactObsKey traceResolver P.erase =>
                  (P.erase, ExactObsKey.code k)) alias_keyAt_eq
          | there y => nomatch y
  | there x =>
      cases x with
      | here =>
          cases y with
          | here =>
              exact (congrArg
                (fun k : ExactObsKey traceResolver P.erase =>
                  (P.erase, ExactObsKey.code k)) alias_keyAt_eq).symm
          | there y =>
              cases y with
              | here => rfl
              | there y => nomatch y
      | there x => nomatch x

theorem alias_results_equivalent
    {Q T : Pos TwoGenSig.nBases} (x : PendingVar TwoSelected Q)
    (y : PendingVar TwoSelected T) :
    traceResolver.Equivalent (aliasPlan.result x).raw
      (aliasPlan.result y).raw := by
  cases x with
  | here =>
      cases y with
      | here => rfl
      | there y =>
          cases y with
          | here =>
              unfold AliasResolver.Equivalent
              rw [aliasPlan_result_here, aliasPlan_result_older,
                traceResolver_obsA, traceResolver_obsDuplicate]
          | there y => nomatch y
  | there x =>
      cases x with
      | here =>
          cases y with
          | here =>
              unfold AliasResolver.Equivalent
              rw [aliasPlan_result_older, aliasPlan_result_here,
                traceResolver_obsDuplicate, traceResolver_obsA]
          | there y =>
              cases y with
              | here => rfl
              | there y => nomatch y
      | there x => nomatch x

def aliasExactBatch :
    ExactBatch traceResolver (supply traceResolver)
      traceAliasAssignment aliasBatch where
  pre := tracePre
  plan := aliasPlan
  assignmentScoped := traceAliasAssignment_scoped
  resultsQuotiented := fun x y =>
    ⟨fun _ => alias_results_equivalent x y, fun _ => alias_keySig_eq x y⟩

/-- Alias-normalized keys receive result origins with one representative. -/
theorem alias_chain_keys_share_representative :
    aliasBatch.exactKeyAt (supply traceResolver) traceAliasAssignment
        (.here : PendingVar TwoSelected P) =
      aliasBatch.exactKeyAt (supply traceResolver) traceAliasAssignment
          (.there .here : PendingVar TwoSelected P) ∧
      traceResolver.Equivalent obsA.raw obsADuplicate.raw := by
  constructor
  · exact alias_keyAt_eq
  · unfold AliasResolver.Equivalent
    rw [traceResolver_obsA, traceResolver_obsDuplicate]

theorem aliasExactBatch_wellFormed :
    aliasExactBatch.toExactTrace.toTypedTrace.WellFormed :=
  aliasExactBatch.toExactTrace.wellFormed

@[simp] theorem batchBA_key_here :
    batchBA.exactKeyAt (supply idR) obsAssignment
        (.here : PendingVar TwoSelected P) = olderKey := rfl

/-- Literal order is visible in the generated observation-step list. -/
theorem AB_BA_step_lists_differ :
    batchAB.observationSteps (supply idR) obsAssignment distinctPlan ≠
      batchBA.observationSteps (supply idR) obsAssignment distinctPlan := by
  intro h
  have hhead := congrArg List.head? h
  have hcode := congrArg (Option.map TraceStep.exactCode?) hhead
  simp [batchAB, batchBA, NonemptyBatchObs.observationSteps,
    NonemptyBatchObs.observeAt, TraceStep.exactCode?] at hcode
  change ExactObsKey.code newestKey = ExactObsKey.code olderKey at hcode
  exact newest_older_key_distinct (ExactObsKey.code_injective hcode)

/-- A duplicate literal batch remains two observation occurrences. -/
theorem duplicate_AA_retains_two_observations :
    ∃ first second,
      batchAA.observationSteps (supply idR) obsAssignment distinctPlan =
        [first, second] := by
  exact ⟨batchAA.observeAt (supply idR) obsAssignment distinctPlan .here,
    batchAA.observeAt (supply idR) obsAssignment distinctPlan (.there .here),
    rfl⟩

/-- Both paired consumers of one literal batch receive definitionally equal
ordered keys and equationally equal observation steps. -/
theorem paired_literal_batch_identical :
    aliasExactBatch.keyPackage = aliasExactBatch.keyPackage ∧
      aliasExactBatch.steps = aliasExactBatch.steps :=
  aliasExactBatch.pairedLiteral_same_packages

/-- The public batch bridge exposes the rank separation used by scoped traces. -/
theorem alias_dependency_precedes_result
    (x : PendingVar TwoSelected P) (o : Origin TwoGenSig)
    (ho : o ∈ (aliasBatch.exactKeyAt (supply traceResolver)
      traceAliasAssignment x).deps) :
    o.introRank < (aliasPlan.result x).raw.introRank :=
  aliasExactBatch.dependency_precedes_result x o ho

end ExactTraceFixtures

end Gimbal.Equality.Scherer
