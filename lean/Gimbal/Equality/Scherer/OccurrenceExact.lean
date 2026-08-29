/-
  Occurrence-local exact batches.

  Exact keys and result origins are supplied only for the literal batch being
  certified. This layer never manufactures a total `BatchResultSupply` for
  unrelated or unreachable nested batches.
-/

import Gimbal.Equality.Scherer.PairTraceExtension
import Gimbal.Equality.Scherer.SearchLocalFoundation

namespace Gimbal.Equality.Scherer

variable {sig : Signature} {Γ : StableCtx sig} {selected : Pending sig}
  {Δ : Ctx sig}

/-! ### Injective local occurrence addresses -/

inductive LocalEdge where
  | eval (edge : EvalEdge)
  | splitChoice (index : Nat)
  | lambdaChoice (index : Nat)
  | positiveChoice (index : Nat)
  | saturationChoice (index : Nat)
  | batchBody
  | batchEntry (index : Nat)
  deriving DecidableEq, Repr

abbrev LocalAddr := List LocalEdge

namespace LocalEdge

private def evalCode : EvalEdge → Nat
  | .posInl => 0
  | .posInr => 1
  | .posShift => 2
  | .caseLeft => 3
  | .caseRight => 4
  | .storeTail => 5
  | .pairLeft => 6
  | .pairRight => 7
  | .lamBody => 8
  | .satShift => 9
  | .satPos => 10
  | .elimArg => 11

private theorem evalCode_injective : Function.Injective evalCode := by
  intro a b h
  cases a <;> cases b <;> simp [evalCode] at h ⊢

def tree : LocalEdge → StructuralNatTree
  | .eval edge => .node 100 [.atom (evalCode edge)]
  | .splitChoice i => .node 101 [.atom i]
  | .lambdaChoice i => .node 102 [.atom i]
  | .positiveChoice i => .node 103 [.atom i]
  | .saturationChoice i => .node 104 [.atom i]
  | .batchBody => .node 105 []
  | .batchEntry i => .node 106 [.atom i]

theorem tree_injective : Function.Injective tree := by
  intro a b h
  cases a <;> cases b <;> simp [tree, evalCode] at h ⊢
  all_goals first | exact evalCode_injective h | exact h

theorem tree_list_injective : Function.Injective (List.map tree) := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys <;> simp at h ⊢
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp at h
          exact congrArg₂ List.cons (tree_injective h.1) (ih h.2)

end LocalEdge

namespace LocalAddr

def tree (addr : LocalAddr) : StructuralNatTree :=
  .node 107 (addr.map LocalEdge.tree)

def code (addr : LocalAddr) : Nat := addr.tree.natCode

theorem tree_injective : Function.Injective tree := by
  intro left right h
  have h' : StructuralNatTree.ofList (left.map LocalEdge.tree) =
      StructuralNatTree.ofList (right.map LocalEdge.tree) := by
    injection h
  exact LocalEdge.tree_list_injective (StructuralNatTree.ofList_injective h')

theorem code_injective : Function.Injective code := by
  intro left right h
  exact tree_injective (StructuralNatTree.natCode_injective h)

end LocalAddr

/-! ### Literal occurrence-local keys and steps -/

structure BatchExactKeys (R : AliasResolver sig) (selected : Pending sig) where
  keyAt : ∀ {P}, PendingVar selected P → ExactObsKey R P.erase

namespace BatchExactKeys

def tail (keys : BatchExactKeys R (.cons Q ps)) : BatchExactKeys R ps where
  keyAt x := keys.keyAt (.there x)

end BatchExactKeys

def NonemptyBatchObs.observeAtWith (_obs : NonemptyBatchObs Γ selected)
    (keys : BatchExactKeys R selected) (plan : BatchObservationPlan pre selected)
    {P : Pos sig.nBases} (x : PendingVar selected P) :
    TraceStep (exactObsKeys R) :=
  .observe (plan.site x) (plan.support x) pre (keys.keyAt x) (plan.result x)

def NonemptyBatchObs.observationStepsWith :
    ∀ {selected : Pending sig},
    (obs : NonemptyBatchObs Γ selected) → BatchExactKeys R selected →
      (plan : BatchObservationPlan pre selected) →
      List (TraceStep (exactObsKeys R))
  | _, .one _, keys, plan =>
      [TraceStep.observe (plan.site .here) (plan.support .here) pre
        (keys.keyAt .here) (plan.result .here)]
  | _, .cons _ rest, keys, plan =>
      TraceStep.observe (plan.site .here) (plan.support .here) pre
        (keys.keyAt .here) (plan.result .here) ::
        rest.observationStepsWith keys.tail plan.tail

@[simp] theorem NonemptyBatchObs.observationStepsWith_length :
    ∀ {selected : Pending sig} (obs : NonemptyBatchObs Γ selected)
      (keys : BatchExactKeys R selected)
      (plan : BatchObservationPlan pre selected),
      (obs.observationStepsWith keys plan).length = obs.length
  | _, .one _, _, _ => rfl
  | _, .cons _ rest, keys, plan => by
      simp [NonemptyBatchObs.observationStepsWith, NonemptyBatchObs.length,
        NonemptyBatchObs.observationStepsWith_length rest keys.tail plan.tail]
termination_by selected _ _ _ => selected.length
decreasing_by simp_all [Pending.length]

theorem NonemptyBatchObs.observeAtWith_mem :
    ∀ {selected : Pending sig} (obs : NonemptyBatchObs Γ selected)
      (keys : BatchExactKeys R selected)
      (plan : BatchObservationPlan pre selected)
      {P : Pos sig.nBases} (x : PendingVar selected P),
      obs.observeAtWith keys plan x ∈ obs.observationStepsWith keys plan
  | _, .one _, _, _, _, .here => by
      simp [observeAtWith, observationStepsWith]
  | _, .cons _ _, _, _, _, .here => by
      simp [observeAtWith, observationStepsWith]
  | _, .cons _ rest, keys, plan, _, .there x => by
      simp only [observationStepsWith, List.mem_cons]
      exact Or.inr (NonemptyBatchObs.observeAtWith_mem rest
        keys.tail plan.tail x)
termination_by selected _ _ _ _ _ => selected.length
decreasing_by simp_all [Pending.length]

theorem NonemptyBatchObs.exists_observeAtWith_of_mem :
    ∀ {selected : Pending sig} (obs : NonemptyBatchObs Γ selected)
      (keys : BatchExactKeys R selected)
      (plan : BatchObservationPlan pre selected)
      {s : TraceStep (exactObsKeys R)},
      s ∈ obs.observationStepsWith keys plan →
        ∃ (P : Pos sig.nBases) (x : PendingVar selected P),
          s = obs.observeAtWith keys plan x
  | _, .one _, _, _, _, hs => by
      simp only [observationStepsWith, List.mem_singleton] at hs
      exact ⟨_, .here, hs⟩
  | _, .cons _ rest, keys, plan, _, hs => by
      simp only [observationStepsWith, List.mem_cons] at hs
      rcases hs with hs | hs
      · exact ⟨_, .here, hs⟩
      · obtain ⟨P, x, hx⟩ :=
          NonemptyBatchObs.exists_observeAtWith_of_mem rest
            keys.tail plan.tail hs
        exact ⟨P, .there x, hx⟩
termination_by selected _ _ _ _ _ => selected.length
decreasing_by simp_all [Pending.length]

/-! ### Occurrence-local exact batches -/

structure LocalExactBatch (R : AliasResolver sig)
    (obs : NonemptyBatchObs Γ selected) (keys : BatchExactKeys R selected) where
  pre : OriginScope
  plan : BatchObservationPlan pre selected
  keysScoped : ∀ {P} (x : PendingVar selected P) o,
    o ∈ (keys.keyAt x).deps → pre.Contains o
  resultsQuotiented :
    ∀ {P Q : Pos sig.nBases} (x : PendingVar selected P)
      (y : PendingVar selected Q),
      (P.erase, ExactObsKey.code (keys.keyAt x)) =
          (Q.erase, ExactObsKey.code (keys.keyAt y)) ↔
        R.Equivalent (plan.result x).raw (plan.result y).raw

namespace LocalExactBatch

variable {R : AliasResolver sig} {obs : NonemptyBatchObs Γ selected}
  {keys : BatchExactKeys R selected}

def steps (B : LocalExactBatch R obs keys) :
    List (TraceStep (exactObsKeys R)) :=
  obs.observationStepsWith keys B.plan

theorem dependency_precedes_result (B : LocalExactBatch R obs keys)
    {P : Pos sig.nBases} (x : PendingVar selected P)
    (o : Origin sig) (ho : o ∈ (keys.keyAt x).deps) :
    o.introRank < (B.plan.result x).raw.introRank :=
  Nat.lt_of_lt_of_le (B.keysScoped x o ho) (B.plan.result_fresh x)

theorem observeAt_scoped (B : LocalExactBatch R obs keys)
    {P : Pos sig.nBases} (x : PendingVar selected P) :
    (obs.observeAtWith keys B.plan x).Scoped :=
  ⟨B.keysScoped x, B.plan.result_fresh x⟩

theorem stepsScoped (B : LocalExactBatch R obs keys) :
    ∀ s ∈ B.steps, s.Scoped := by
  intro s hs
  obtain ⟨P, x, rfl⟩ := obs.exists_observeAtWith_of_mem keys B.plan hs
  exact B.observeAt_scoped x

theorem splitsFunctional (B : LocalExactBatch R obs keys) :
    ({ resolver := R, steps := B.steps } :
      TypedTrace (exactObsKeys R)).SplitsFunctional := by
  intro s hs t ht htag hsome _
  obtain ⟨P, x, rfl⟩ := obs.exists_observeAtWith_of_mem keys B.plan hs
  simp [NonemptyBatchObs.observeAtWith, TraceStep.splitTag?] at hsome

theorem observationsQuotiented (B : LocalExactBatch R obs keys) :
    ({ resolver := R, steps := B.steps } :
      TypedTrace (exactObsKeys R)).ObservationsQuotiented := by
  intro s hs t ht ks kt hsig htig
  obtain ⟨P, x, rfl⟩ := obs.exists_observeAtWith_of_mem keys B.plan hs
  obtain ⟨Q, y, rfl⟩ := obs.exists_observeAtWith_of_mem keys B.plan ht
  simp only [NonemptyBatchObs.observeAtWith, TraceStep.keySig?,
    Option.some.injEq] at hsig htig
  subst ks
  subst kt
  constructor
  · intro hkey
    exact ⟨(B.plan.result x).raw, (B.plan.result y).raw, rfl, rfl,
      (B.resultsQuotiented x y).mp hkey⟩
  · rintro ⟨left, right, hleft, hright, heq⟩
    simp only [NonemptyBatchObs.observeAtWith, TraceStep.result?,
      Option.some.injEq] at hleft hright
    subst left
    subst right
    exact (B.resultsQuotiented x y).mpr heq

theorem wellFormed (B : LocalExactBatch R obs keys) :
    ({ resolver := R, steps := B.steps } :
      TypedTrace (exactObsKeys R)).WellFormed :=
  ⟨B.stepsScoped, B.splitsFunctional, B.observationsQuotiented⟩

def toExactTrace (B : LocalExactBatch R obs keys) : ExactTrace sig :=
  ⟨R, B.steps, B.wellFormed⟩

structure Addressed (B : LocalExactBatch R obs keys) (addr : LocalAddr) : Prop where
  site_eq : ∀ {P} (x : PendingVar selected P), B.plan.site x = addr.code
  entry_eq : ∀ {P} (x : PendingVar selected P), B.plan.entry x = x.index

structure Extension (B : LocalExactBatch R obs keys)
    (base : ExactTraceAt R) where
  results : BatchResultAssignment R selected
  next : ExactTraceAt R
  steps_eq : next.steps = B.steps ++ base.steps
  alignment : ∀ {P} (x : PendingVar selected P),
    results.origin x = B.plan.result x

namespace Extension

variable {B : LocalExactBatch R obs keys} {base : ExactTraceAt R}

theorem toTraceExtension (X : B.Extension base) :
    TraceExtension base X.next B.steps := ⟨X.steps_eq⟩

theorem batchStep_mem (X : B.Extension base) {s}
    (hs : s ∈ B.steps) : s ∈ X.next.steps := X.toTraceExtension.added_mem hs

theorem oldStep_mem (X : B.Extension base) {s}
    (hs : s ∈ base.steps) : s ∈ X.next.steps := X.toTraceExtension.base_mem hs

theorem batchStep_scoped (X : B.Extension base) {s}
    (hs : s ∈ B.steps) : s.Scoped := X.toTraceExtension.added_scoped hs

theorem wellFormed (X : B.Extension base) : X.next.toTypedTrace.WellFormed :=
  X.next.wellFormed

theorem splitsFunctional (X : B.Extension base) :
    X.next.toTypedTrace.SplitsFunctional := X.next.wellFormed.splitsFunctional

theorem observationsQuotiented (X : B.Extension base) :
    X.next.toTypedTrace.ObservationsQuotiented :=
  X.next.wellFormed.observationsQuotiented

theorem dependency_precedes_result (_X : B.Extension base)
    {P : Pos sig.nBases} (x : PendingVar selected P)
    (o : Origin sig) (ho : o ∈ (keys.keyAt x).deps) :
    o.introRank < (B.plan.result x).raw.introRank :=
  B.dependency_precedes_result x o ho

theorem bodyOrigin (X : B.Extension base) (D : BoundOrigins R Δ)
    {P : Pos sig.nBases} (x : PendingVar selected P) :
    (D.pushPending X.results.resolved).ref (PendingVar.eraseAux Δ x) =
      ResolvedRef.of R (B.plan.result x) := by
  rw [BoundOrigins.pushPending_entry, BatchResultAssignment.resolved_ref,
    X.alignment x]

end Extension

end LocalExactBatch

/-! ### One-way compatibility with the legacy total-supply interface -/

def BatchExactKeys.ofLegacy (obs : NonemptyBatchObs Γ selected)
    (supply : BatchResultSupply R) (E : OriginAssignment R Γ) :
    BatchExactKeys R selected := ⟨obs.exactKeyAt supply E⟩

theorem NonemptyBatchObs.observationStepsWith_ofLegacy :
    ∀ {selected : Pending sig} (obs : NonemptyBatchObs Γ selected)
      (supply : BatchResultSupply R) (E : OriginAssignment R Γ)
      (plan : BatchObservationPlan pre selected),
      obs.observationStepsWith (BatchExactKeys.ofLegacy obs supply E) plan =
        obs.observationSteps supply E plan
  | _, .one _, _, _, _ => rfl
  | _, .cons n rest, supply, E, plan => by
      simp only [observationStepsWith, observationSteps_cons, List.cons.injEq,
        NonemptyBatchObs.observeAt]
      constructor
      · rfl
      · have hkeys :
            (BatchExactKeys.ofLegacy (.cons n rest) supply E).tail =
              BatchExactKeys.ofLegacy rest supply E := rfl
        rw [hkeys]
        exact NonemptyBatchObs.observationStepsWith_ofLegacy rest supply E plan.tail
termination_by selected _ _ _ _ => selected.length
decreasing_by simp_all [Pending.length]

def ExactBatch.toLocal (B : ExactBatch R supply E obs) :
    LocalExactBatch R obs (BatchExactKeys.ofLegacy obs supply E) where
  pre := B.pre
  plan := B.plan
  keysScoped := fun x o ho =>
    ExactObsKey.ofNeutral_scoped supply E (obs.neutralAt x)
      B.assignmentScoped o ho
  resultsQuotiented := B.resultsQuotiented

theorem ExactBatch.toLocal_steps (B : ExactBatch R supply E obs) :
    B.toLocal.steps = B.steps :=
  obs.observationStepsWith_ofLegacy supply E B.plan

def ExactBatch.Extension.toLocal {B : ExactBatch R supply E obs}
    {base : ExactTraceAt R} (X : B.Extension base) :
    B.toLocal.Extension base where
  results := supply.results obs
  next := X.next
  steps_eq := by rw [ExactBatch.toLocal_steps]; exact X.steps_eq
  alignment := X.alignment.results_eq

/-! ### Boundary fixtures -/

namespace OccurrenceExactFixtures

open PairTraceFixtures PairStructuralCodeFixtures ExactObsKeyFixtures
  ExactTraceFixtures PairTraceExtensionFixtures

theorem alternative_codes_distinct :
    LocalAddr.code [.splitChoice 0] ≠ LocalAddr.code [.splitChoice 1] := by
  intro h
  have := LocalAddr.code_injective h
  simp at this

theorem batch_entry_codes_distinct :
    LocalAddr.code [.batchEntry 0] ≠ LocalAddr.code [.batchEntry 1] := by
  intro h
  have := LocalAddr.code_injective h
  simp at this

theorem saturation_codes_distinct :
    LocalAddr.code [.saturationChoice 0] ≠
      LocalAddr.code [.saturationChoice 1] := by
  intro h
  have := LocalAddr.code_injective h
  simp at this

def alignedLocal := alignedBatch.toLocal
def alignedLocalExtension := alignedExtension.toLocal

theorem equal_result_types_keep_ordered_entries :
    alignedLocal.steps.length = 2 ∧
      alignedLocal.plan.entry (.here : PendingVar TwoSelected P) = 0 ∧
      alignedLocal.plan.entry (.there .here : PendingVar TwoSelected P) = 1 := by
  constructor
  · rw [show alignedLocal.steps = alignedBatch.steps from
      ExactBatch.toLocal_steps alignedBatch]
    rfl
  · exact ⟨rfl, rfl⟩

def aliasLocal := aliasAlignedBatch.toLocal
def aliasLegacyExtension :
    aliasAlignedBatch.Extension (ExactTraceAt.empty traceResolver) where
  next := aliasAlignedBatch.toExactTrace.asAt
  steps_eq := rfl
  alignment := aliasAlignedBatch_alignment

def aliasLocalExtension := ExactBatch.Extension.toLocal aliasLegacyExtension

theorem equal_keys_alias_without_dedup :
    aliasLocal.steps.length = 2 ∧
      traceResolver.Equivalent
        (aliasLocalExtension.results.origin
          (.here : PendingVar TwoSelected P)).raw
        (aliasLocalExtension.results.origin
          (.there .here : PendingVar TwoSelected P)).raw := by
  refine ⟨rfl, ?_⟩
  rw [aliasLocalExtension.alignment, aliasLocalExtension.alignment]
  exact alias_results_equivalent _ _

abbrev OneSelected : Pending TwoGenSig := .cons P .empty
def oneObs : NonemptyBatchObs ObsCtx OneSelected := .one newestObs
def oneKeys : BatchExactKeys idR OneSelected where
  keyAt := by
    intro Q x
    cases x with
    | here => exact newestKey
    | there x => nomatch x

def onePlan (addr : LocalAddr) : BatchObservationPlan tracePre OneSelected where
  site _ := addr.code
  support _ := 17
  entry x := x.index
  ident _ := addr.code + 100
  rank _ := 2
  fresh _ := by decide

def oneBatch (addr : LocalAddr) : LocalExactBatch idR oneObs oneKeys where
  pre := tracePre
  plan := onePlan addr
  keysScoped := by
    intro Q x o ho
    cases x with
    | here =>
        exact ExactObsKey.ofNeutral_scoped (supply idR) obsAssignment newestObs
          obsAssignment_scoped o ho
    | there x => nomatch x
  resultsQuotiented := by
    intro Q T x y
    cases x with
    | here =>
        cases y with
        | here => exact ⟨fun _ => rfl, fun _ => rfl⟩
        | there y => nomatch y
    | there x => nomatch x

theorem oneBatch_addressed (addr : LocalAddr) :
    (oneBatch addr).Addressed addr := by
  constructor <;> intro Q x <;> cases x <;> rfl

def oneResults (addr : LocalAddr) : BatchResultAssignment idR OneSelected where
  origin := by
    intro Q x
    cases x with
    | here => exact (oneBatch addr).plan.result .here
    | there x => nomatch x

def oneExtension (addr : LocalAddr) :
    (oneBatch addr).Extension (ExactTraceAt.empty idR) where
  results := oneResults addr
  next := (oneBatch addr).toExactTrace.asAt
  steps_eq := by
    change (oneBatch addr).steps = (oneBatch addr).steps ++ []
    simp
  alignment x := by
    cases x with
    | here => rfl
    | there x => nomatch x

def siteAAddr : LocalAddr := [.saturationChoice 0]
def siteBAddr : LocalAddr := [.saturationChoice 1]

theorem same_raw_batch_distinct_local_sites :
    oneObs = oneObs ∧
      (oneExtension siteAAddr).results.origin
          (.here : PendingVar OneSelected P) ≠
        (oneExtension siteBAddr).results.origin .here := by
  refine ⟨rfl, ?_⟩
  intro h
  rw [(oneExtension siteAAddr).alignment,
    (oneExtension siteBAddr).alignment] at h
  have hk := congrArg (fun o => o.raw.kind) h
  change OriginKind.observation siteAAddr.code 0 =
    OriginKind.observation siteBAddr.code 0 at hk
  injection hk with hs _
  exact saturation_codes_distinct hs

/-- A total supply sees only `obs`, so aligning that one result with two local
site plans forces the sites to be equal. This is the precise obstruction;
the local extensions above avoid it by owning their assignments. -/
theorem legacy_shared_result_forces_site_eq (legacy : BatchResultSupply idR)
    (left right : LocalAddr)
    (hl : (legacy.results oneObs).origin
        (.here : PendingVar OneSelected P) = (oneBatch left).plan.result .here)
    (hr : (legacy.results oneObs).origin
        (.here : PendingVar OneSelected P) = (oneBatch right).plan.result .here) :
    left.code = right.code := by
  have h := hl.symm.trans hr
  have hk := congrArg (fun o => o.raw.kind) h
  simp [oneBatch, onePlan, BatchObservationPlan.result] at hk
  injection hk with hs _

theorem no_legacy_alignment_at_both_fixture_sites
    (legacy : BatchResultSupply idR) :
    ¬((legacy.results oneObs).origin (.here : PendingVar OneSelected P) =
          (oneBatch siteAAddr).plan.result .here ∧
       (legacy.results oneObs).origin (.here : PendingVar OneSelected P) =
          (oneBatch siteBAddr).plan.result .here) := by
  rintro ⟨hl, hr⟩
  exact saturation_codes_distinct
    (legacy_shared_result_forces_site_eq legacy siteAAddr siteBAddr hl hr)

end OccurrenceExactFixtures

end Gimbal.Equality.Scherer
