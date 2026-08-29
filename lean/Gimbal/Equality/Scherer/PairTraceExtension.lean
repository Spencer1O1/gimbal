/-
  Path-local exact-trace extensions for paired structural comparison.
  Extension certificates own all cross-step well-formedness; this module does
  not allocate sites, select observations, or merge sibling paths.
-/

import Gimbal.Equality.Scherer.PairRealize
import Gimbal.Equality.Scherer.PairedSelected

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Exact path extensions -/

/-- `next` is exactly `added` prepended to the existing path trace. -/
structure TraceExtension (base next : ExactTraceAt R)
    (added : List (TraceStep (exactObsKeys R))) : Prop where
  steps_eq : next.steps = added ++ base.steps

namespace TraceExtension

variable {R : AliasResolver sig} {base next : ExactTraceAt R}
  {added : List (TraceStep (exactObsKeys R))}

theorem added_mem (h : TraceExtension base next added)
    {s : TraceStep (exactObsKeys R)} (hs : s ∈ added) : s ∈ next.steps := by
  rw [h.steps_eq]
  exact List.mem_append_left _ hs

theorem base_mem (h : TraceExtension base next added)
    {s : TraceStep (exactObsKeys R)} (hs : s ∈ base.steps) : s ∈ next.steps := by
  rw [h.steps_eq]
  exact List.mem_append_right _ hs

theorem added_scoped (h : TraceExtension base next added)
    {s : TraceStep (exactObsKeys R)} (hs : s ∈ added) : s.Scoped :=
  next.wellFormed.stepsScoped s (h.added_mem hs)

theorem base_scoped (h : TraceExtension base next added)
    {s : TraceStep (exactObsKeys R)} (hs : s ∈ base.steps) : s.Scoped :=
  next.wellFormed.stepsScoped s (h.base_mem hs)

theorem next_splitsFunctional (_h : TraceExtension base next added) :
    next.toTypedTrace.SplitsFunctional :=
  next.wellFormed.splitsFunctional

theorem next_observationsQuotiented (_h : TraceExtension base next added) :
    next.toTypedTrace.ObservationsQuotiented :=
  next.wellFormed.observationsQuotiented

end TraceExtension

namespace ExactTraceAt

variable {R : AliasResolver sig}

def empty (R : AliasResolver sig) : ExactTraceAt R where
  steps := []
  isWellFormed := by
    constructor
    · simp
    · intro s hs
      simp at hs
    · intro s hs
      simp at hs

/-- A one-step left path, used only when its payload rank is fresh. -/
def singleSplitL (parent : ResolvedRef R (.coprod A B))
    (payload : TypedOrigin sig A)
    (hrank : parent.origin.raw.introRank < payload.raw.introRank) :
    ExactTraceAt R where
  steps := [.splitL parent.origin payload]
  isWellFormed := by
    constructor
    · intro s hs
      simp only [List.mem_singleton] at hs
      subst s
      exact hrank
    · intro s hs t ht _ _ _
      simp only [List.mem_singleton] at hs ht
      subst s
      subst t
      refine ⟨payload.raw, payload.raw, rfl, rfl, ?_⟩
      rfl
    · intro s hs t ht ks kt hsig _
      simp only [List.mem_singleton] at hs ht
      subst s
      simp [TraceStep.keySig?] at hsig

/-- A one-step right path, used only when its payload rank is fresh. -/
def singleSplitR (parent : ResolvedRef R (.coprod A B))
    (payload : TypedOrigin sig B)
    (hrank : parent.origin.raw.introRank < payload.raw.introRank) :
    ExactTraceAt R where
  steps := [.splitR parent.origin payload]
  isWellFormed := by
    constructor
    · intro s hs
      simp only [List.mem_singleton] at hs
      subst s
      exact hrank
    · intro s hs t ht _ _ _
      simp only [List.mem_singleton] at hs ht
      subst s
      subst t
      refine ⟨payload.raw, payload.raw, rfl, rfl, ?_⟩
      rfl
    · intro s hs t ht ks kt hsig _
      simp only [List.mem_singleton] at hs ht
      subst s
      simp [TraceStep.keySig?] at hsig

end ExactTraceAt

/-! ### Path-local coproduct forks -/

/--
A split creates two independent child traces.  They share the old base but
never contain each other's split step.
-/
structure SplitFork {sig : Signature} {R : AliasResolver sig}
    (base : ExactTraceAt R) {A B : Object sig.nBases}
    (parent : ResolvedRef R (.coprod A B)) where
  leftPayload : TypedOrigin sig A
  rightPayload : TypedOrigin sig B
  leftTrace : ExactTraceAt R
  rightTrace : ExactTraceAt R
  left_steps :
    leftTrace.steps =
      TraceStep.splitL parent.origin leftPayload :: base.steps
  right_steps :
    rightTrace.steps =
      TraceStep.splitR parent.origin rightPayload :: base.steps

namespace SplitFork

variable {R : AliasResolver sig} {base : ExactTraceAt R}
  {A B : Object sig.nBases}
  {parent : ResolvedRef R (.coprod A B)}

def leftStep (F : SplitFork base parent) : TraceStep (exactObsKeys R) :=
  .splitL parent.origin F.leftPayload

def rightStep (F : SplitFork base parent) : TraceStep (exactObsKeys R) :=
  .splitR parent.origin F.rightPayload

theorem leftExtension (F : SplitFork base parent) :
    TraceExtension base F.leftTrace [F.leftStep] where
  steps_eq := by simpa [leftStep] using F.left_steps

theorem rightExtension (F : SplitFork base parent) :
    TraceExtension base F.rightTrace [F.rightStep] where
  steps_eq := by simpa [rightStep] using F.right_steps

theorem parent_before_left (F : SplitFork base parent) :
    parent.origin.raw.introRank < F.leftPayload.raw.introRank := by
  have hs := F.leftExtension.added_scoped (by simp : F.leftStep ∈ [F.leftStep])
  exact hs

theorem parent_before_right (F : SplitFork base parent) :
    parent.origin.raw.introRank < F.rightPayload.raw.introRank := by
  have hs := F.rightExtension.added_scoped (by simp : F.rightStep ∈ [F.rightStep])
  exact hs

/-- A diagnostic merge witnesses contradiction; neither child trace is merged. -/
def oppositePath (F : SplitFork base parent) :
    TypedTrace (exactObsKeys R) where
  resolver := R
  steps := [F.leftStep, F.rightStep] ++ base.steps

theorem oppositePath_dead (F : SplitFork base parent) : F.oppositePath.IsDead := by
  apply F.oppositePath.dead_of_oppositeSplits
      (s := F.leftStep) (t := F.rightStep)
  · simp [oppositePath]
  · simp [oppositePath]
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
  · unfold AliasResolver.Equivalent
    rfl

end SplitFork

/-! ### Literal batch alignment and extension -/

namespace ExactBatch

variable {R : AliasResolver sig} {Γ : StableCtx sig}
  {selected : Pending sig} {supply : BatchResultSupply R}
  {E : OriginAssignment R Γ} {obs : NonemptyBatchObs Γ selected}

/-- The structural-code supply and observation trace use identical origins. -/
structure Alignment (B : ExactBatch R supply E obs) : Prop where
  results_eq : ∀ {P : Pos sig.nBases} (x : PendingVar selected P),
    (supply.results obs).origin x = B.plan.result x

/--
An externally certified extension.  `next.isWellFormed` carries every
cross-step scope, split-functionality, and observation-quotient obligation.
-/
structure Extension (base : ExactTraceAt R)
    (B : ExactBatch R supply E obs) where
  next : ExactTraceAt R
  steps_eq : next.steps = B.steps ++ base.steps
  alignment : B.Alignment

namespace Extension

variable {base : ExactTraceAt R} {B : ExactBatch R supply E obs}

theorem toTraceExtension (X : B.Extension base) :
    TraceExtension base X.next B.steps where
  steps_eq := X.steps_eq

theorem batchStep_mem (X : B.Extension base)
    {s : TraceStep (exactObsKeys R)} (hs : s ∈ B.steps) : s ∈ X.next.steps :=
  X.toTraceExtension.added_mem hs

theorem oldStep_mem (X : B.Extension base)
    {s : TraceStep (exactObsKeys R)} (hs : s ∈ base.steps) : s ∈ X.next.steps :=
  X.toTraceExtension.base_mem hs

theorem batchStep_scoped (X : B.Extension base)
    {s : TraceStep (exactObsKeys R)} (hs : s ∈ B.steps) : s.Scoped :=
  X.toTraceExtension.added_scoped hs

theorem wellFormed (X : B.Extension base) : X.next.toTypedTrace.WellFormed :=
  X.next.wellFormed

theorem splitsFunctional (X : B.Extension base) :
    X.next.toTypedTrace.SplitsFunctional :=
  X.next.wellFormed.splitsFunctional

theorem observationsQuotiented (X : B.Extension base) :
    X.next.toTypedTrace.ObservationsQuotiented :=
  X.next.wellFormed.observationsQuotiented

theorem dependency_precedes_result (_X : B.Extension base)
    {P : Pos sig.nBases} (x : PendingVar selected P)
    (o : Origin sig) (ho : o ∈ (obs.exactKeyAt supply E x).deps) :
    o.introRank < (B.plan.result x).raw.introRank :=
  B.dependency_precedes_result x o ho

/-- The body binder for occurrence `x` denotes its observe-step result. -/
theorem bodyOrigin (X : B.Extension base) (D : BoundOrigins R Δ)
    {P : Pos sig.nBases} (x : PendingVar selected P) :
    (D.pushPending (supply.results obs).resolved).ref
        (PendingVar.eraseAux Δ x) = ResolvedRef.of R (B.plan.result x) := by
  rw [BoundOrigins.pushPending_entry, BatchResultAssignment.resolved_ref,
    X.alignment.results_eq x]

end Extension

/--
The paired constructor and both consumers reuse one literal `obs`, one exact
batch `B`, and one extension `X`; no second allocation can appear.
-/
theorem pairedLiteral_reuses
    {Old New : StableCtx sig} {selected : Pending sig}
    {supply : BatchResultSupply R}
    {E : OriginAssignment R (Old.append New)}
    {obs : NonemptyBatchObs (Old.append New) selected}
    (B : ExactBatch R supply E obs) (base : ExactTraceAt R)
    (X : B.Extension base) {P : Pos sig.nBases}
    {left right : SInv (Old.append New) .empty selected (.pos P)}
    (h : PairedNormal left right) :
    PairedSelected (.batch obs left) (.batch obs right) ∧
      B.keyPackage = B.keyPackage ∧ X = X :=
  ⟨.batch obs h, rfl, rfl⟩

end ExactBatch

/-! ### Boundary fixtures -/

namespace PairTraceExtensionFixtures

open PairTraceFixtures PairStructuralCodeFixtures ExactTraceFixtures

def emptyTrace : ExactTraceAt idR := ExactTraceAt.empty idR

def sumRef : ResolvedRef idR (.coprod Q Q) := ResolvedRef.of idR sumParent

def siblingFork : SplitFork emptyTrace sumRef where
  leftPayload := leftPayload
  rightPayload := rightPayload
  leftTrace := ExactTraceAt.singleSplitL sumRef leftPayload (by
    rw [show sumRef.origin = sumParent from
      ResolvedRef.of_eq_self idR sumParent (by rfl)]
    decide)
  rightTrace := ExactTraceAt.singleSplitR sumRef rightPayload (by
    rw [show sumRef.origin = sumParent from
      ResolvedRef.of_eq_self idR sumParent (by rfl)]
    decide)
  left_steps := rfl
  right_steps := rfl

theorem left_sibling_live : siblingFork.leftTrace.toTypedTrace.IsLive := by
  simp [TypedTrace.IsLive, TypedTrace.IsDead, TypedTrace.splitConflict,
    siblingFork, ExactTraceAt.singleSplitL, ExactTraceAt.toTypedTrace,
    TraceStep.parent?, TraceStep.splitTag?]

theorem right_sibling_live : siblingFork.rightTrace.toTypedTrace.IsLive := by
  simp [TypedTrace.IsLive, TypedTrace.IsDead, TypedTrace.splitConflict,
    siblingFork, ExactTraceAt.singleSplitR, ExactTraceAt.toTypedTrace,
    TraceStep.parent?, TraceStep.splitTag?]

theorem diagnostic_opposite_path_dead : siblingFork.oppositePath.IsDead :=
  siblingFork.oppositePath_dead

def occurrenceSupply (R : AliasResolver TwoGenSig) : BatchResultSupply R where
  results := fun {_ _} _ =>
    { origin := fun {Q} x => observationOrigin TwoGenSig Q.erase
        (3 + x.index) x.index (20 + 2 * x.index) (2 + x.index) }

def alignedPlan : BatchObservationPlan tracePre TwoSelected where
  site x := 3 + x.index
  support x := 7 + x.index
  entry x := x.index
  ident x := 20 + 2 * x.index
  rank x := 2 + x.index
  fresh := by
    intro Q x
    cases x with
    | here => decide
    | there x =>
        cases x with
        | here => decide
        | there x => nomatch x

@[simp] theorem alignedPlan_result_here :
    alignedPlan.result (.here : PendingVar TwoSelected P) = obsA := rfl

@[simp] theorem alignedPlan_result_older :
    alignedPlan.result (.there .here : PendingVar TwoSelected P) = obsB := rfl

def alignedBatch : ExactBatch idR (occurrenceSupply idR) obsAssignment batchAB where
  pre := tracePre
  plan := alignedPlan
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

theorem alignedBatch_alignment : alignedBatch.Alignment := by
  constructor
  intro P x
  cases x with
  | here => rfl
  | there x =>
      cases x with
      | here => rfl
      | there x => nomatch x

def alignedExtension : alignedBatch.Extension emptyTrace where
  next := alignedBatch.toExactTrace.asAt
  steps_eq := rfl
  alignment := alignedBatch_alignment

theorem two_entry_body_results_in_order :
    let D := (BoundOrigins.empty idR).pushPending
      ((occurrenceSupply idR).results batchAB).resolved
    D.ref (PendingVar.eraseAux (Ctx.empty : Ctx TwoGenSig)
        (.here : PendingVar TwoSelected P)) = ResolvedRef.of idR obsA ∧
      D.ref (PendingVar.eraseAux (Ctx.empty : Ctx TwoGenSig)
        (.there .here : PendingVar TwoSelected P)) = ResolvedRef.of idR obsB := by
  dsimp only
  constructor
  · rw [BoundOrigins.pushPending_entry,
      BatchResultAssignment.resolved_ref]
    rfl
  · rw [BoundOrigins.pushPending_entry,
      BatchResultAssignment.resolved_ref]
    rfl

def aliasOccurrenceSupply (R : AliasResolver TwoGenSig) : BatchResultSupply R where
  results := fun {_ _} _ =>
    { origin := fun {Q} x => observationOrigin TwoGenSig Q.erase
        (3 + x.index) 0 (20 + x.index) (2 + x.index) }

theorem aliasAligned_keyAt_eq :
    aliasBatch.exactKeyAt (aliasOccurrenceSupply traceResolver)
        traceAliasAssignment (.here : PendingVar TwoSelected P) =
      aliasBatch.exactKeyAt (aliasOccurrenceSupply traceResolver)
        traceAliasAssignment (.there .here : PendingVar TwoSelected P) := by
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
  apply ExactObsKey.ext
  · have hcode :
        aliasNewest.toStructuralCode (aliasOccurrenceSupply traceResolver)
            (CodeOriginAssignment.ofOrigin traceAliasAssignment) =
          aliasOlder.toStructuralCode (aliasOccurrenceSupply traceResolver)
            (CodeOriginAssignment.ofOrigin traceAliasAssignment) := by
        change SNegCode.var (CanonRef.free (traceAliasAssignment.ref .here)) =
          SNegCode.var (CanonRef.free
            (traceAliasAssignment.ref (.there .here)))
        rw [href]
    exact congrArg SNegCode.toStructuralNatTree hcode
  · have hcode :
        aliasNewest.toStructuralCode (aliasOccurrenceSupply traceResolver)
            (CodeOriginAssignment.ofOrigin traceAliasAssignment) =
          aliasOlder.toStructuralCode (aliasOccurrenceSupply traceResolver)
            (CodeOriginAssignment.ofOrigin traceAliasAssignment) := by
        change SNegCode.var (CanonRef.free (traceAliasAssignment.ref .here)) =
          SNegCode.var (CanonRef.free
            (traceAliasAssignment.ref (.there .here)))
        rw [href]
    exact congrArg SNegCode.freeDeps hcode

theorem aliasAligned_keySig_eq
    {Q T : Pos TwoGenSig.nBases} (x : PendingVar TwoSelected Q)
    (y : PendingVar TwoSelected T) :
    (Q.erase, ExactObsKey.code
        (aliasBatch.exactKeyAt (aliasOccurrenceSupply traceResolver)
          traceAliasAssignment x)) =
      (T.erase, ExactObsKey.code
        (aliasBatch.exactKeyAt (aliasOccurrenceSupply traceResolver)
          traceAliasAssignment y)) := by
  cases x with
  | here =>
      cases y with
      | here => rfl
      | there y =>
          cases y with
          | here =>
              exact congrArg
                (fun k : ExactObsKey traceResolver P.erase =>
                  (P.erase, ExactObsKey.code k)) aliasAligned_keyAt_eq
          | there y => nomatch y
  | there x =>
      cases x with
      | here =>
          cases y with
          | here =>
              exact (congrArg
                (fun k : ExactObsKey traceResolver P.erase =>
                  (P.erase, ExactObsKey.code k)) aliasAligned_keyAt_eq).symm
          | there y =>
              cases y with
              | here => rfl
              | there y => nomatch y
      | there x => nomatch x

def aliasAlignedBatch : ExactBatch traceResolver
    (aliasOccurrenceSupply traceResolver) traceAliasAssignment aliasBatch where
  pre := tracePre
  plan := aliasPlan
  assignmentScoped := traceAliasAssignment_scoped
  resultsQuotiented := fun x y =>
    ⟨fun _ => alias_results_equivalent x y,
      fun _ => aliasAligned_keySig_eq x y⟩

theorem aliasAlignedBatch_alignment : aliasAlignedBatch.Alignment := by
  constructor
  intro P x
  cases x with
  | here => rfl
  | there x =>
      cases x with
      | here => rfl
      | there x => nomatch x

theorem alias_duplicate_occurrences_not_deduped :
    aliasBatch.exactKeyAt (aliasOccurrenceSupply traceResolver)
        traceAliasAssignment (.here : PendingVar TwoSelected P) =
      aliasBatch.exactKeyAt (aliasOccurrenceSupply traceResolver)
        traceAliasAssignment (.there .here : PendingVar TwoSelected P) ∧
      aliasAlignedBatch.steps.length = 2 ∧
      traceResolver.Equivalent
        (aliasAlignedBatch.plan.result
          (.here : PendingVar TwoSelected P)).raw
        (aliasAlignedBatch.plan.result
          (.there .here : PendingVar TwoSelected P)).raw := by
  constructor
  · exact aliasAligned_keyAt_eq
  · constructor
    · rfl
    · exact alias_results_equivalent _ _

/-- The old unrelated structural supply cannot certify the trace allocation. -/
theorem distinctBatch_supply_misaligned : ¬ distinctBatch.Alignment := by
  intro h
  have heq := h.results_eq (.here : PendingVar TwoSelected P)
  have hraw := congrArg TypedOrigin.raw heq
  change (rootOrigin TwoGenSig P.erase 900 0).raw = obsA.raw at hraw
  exact (by decide :
    (rootOrigin TwoGenSig P.erase 900 0).raw ≠ obsA.raw) hraw

end PairTraceExtensionFixtures

end Gimbal.Equality.Scherer
