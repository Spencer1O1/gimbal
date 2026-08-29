/-
  Proof-relevant structural evaluation with occurrence-local exact sources.

  This is a certified partial lift of `LocalSaturatedEval`: a sourced control
  supplies exact data only for traces admitted by its path predicate.  The raw
  evaluator and its finite pending flow remain unchanged.
-/

import Gimbal.Equality.Scherer.LocalSaturatedEval
import Gimbal.Equality.Scherer.LocalSourceTree

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

universe u v

structure SourcedResult (α : Type u) (Cert : α → Type v) where
  value : α
  certificate : Cert value

abbrev SourcedResults (α : Type u) (Cert : α → Type v) :=
  List (SourcedResult α Cert)

/-! ### Literal list occurrences -/

namespace List

structure Occurrence {α : Type u} (xs : List α) where
  index : Fin xs.length

def Occurrence.value {α : Type u} {xs : List α}
    (o : Occurrence xs) : α :=
  xs.get o.index

def occurrences {α : Type u} : (xs : List α) → List (Occurrence xs)
  | [] => []
  | _ :: xs =>
      ⟨0, by simp⟩ :: (occurrences xs).map fun o =>
        ⟨o.index.succ, by simpa using o.index.isLt⟩

@[simp] theorem occurrences_nil {α : Type u} :
    occurrences ([] : List α) = [] := rfl

@[simp] theorem occurrences_cons {α : Type u} (x : α) (xs : List α) :
    occurrences (x :: xs) =
      ⟨0, by simp⟩ :: (occurrences xs).map fun o =>
        ⟨o.index.succ, by simpa using o.index.isLt⟩ := rfl

@[simp] theorem Occurrence.value_head {α : Type u} (x : α) (xs : List α) :
    (⟨0, by simp⟩ : Occurrence (x :: xs)).value = x := rfl

@[simp] theorem Occurrence.value_succ {α : Type u} (x : α)
    (xs : List α) (o : Occurrence xs) :
    (⟨o.index.succ, by simpa using o.index.isLt⟩ :
      Occurrence (x :: xs)).value = o.value := by
  simp [Occurrence.value]

theorem occurrence_values {α : Type u} (xs : List α) :
    (occurrences xs).map (·.value) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [occurrences, List.map_cons]
      congr 1
      rw [List.map_map]
      calc
        List.map
            ((fun y => y.value) ∘ fun o : Occurrence xs =>
              (⟨o.index.succ, by simpa using o.index.isLt⟩ :
                Occurrence (x :: xs)))
            (occurrences xs) =
            List.map (fun o : Occurrence xs => o.value) (occurrences xs) := by
              apply List.map_congr_left
              intro o _
              exact Occurrence.value_succ x xs o
        _ = xs := ih

end List

/-! ### A trace-local certified control -/

structure AlignedSplitFork {R : AliasResolver sig}
    (TraceOK : ExactTraceAt R → Prop) (base : ExactTraceAt R)
    {A B : Pos sig.nBases} (parent : ResolvedRef R (Pos.sum A B).erase)
    (choice : SplitChoice R parent) where
  fork : SplitFork base parent
  left_eq : choice.leftOrigin = fork.leftPayload
  right_eq : choice.rightOrigin = fork.rightPayload
  leftOK : TraceOK fork.leftTrace
  rightOK : TraceOK fork.rightTrace

structure SourcedSatCallback (U : SearchUniverse sig)
    (R : AliasResolver sig) (O : Type)
    (Base : Ctx2 U.toTypeUniverse) (raw : SatCallback U R O Base)
    (TraceOK : ExactTraceAt R → Prop) where
  sourceAt :
    ∀ {Δ : Ctx sig} {T : ExactTraceAt R}, TraceOK T →
      (D : BoundOrigins R Δ) →
      {Old New : StableCtx sig} →
      (evalAddr : EvalAddr) → (localAddr : LocalAddr) →
      (seg : Segment U.toTypeUniverse R O Base Old New) →
      (E : CodeOriginAssignment R Δ (Old.append New)) →
      E.realize D = seg.frame.origins →
      (P : UPos U) →
      (i : Fin (raw evalAddr seg P).length) →
      SourcedFreshSat R T D E ((raw evalAddr seg P).get i)

structure SourcedControl (U : SearchUniverse sig)
    (R : AliasResolver sig) (O : Type)
    (Base : Ctx2 U.toTypeUniverse) where
  raw : Control U R O Base
  TraceOK : ExactTraceAt R → Prop
  splitForkAt :
    ∀ {T : ExactTraceAt R}, TraceOK T →
      (evalAddr : EvalAddr) → (localAddr : LocalAddr) →
      (A B : UPos U) →
      (parent : ResolvedRef R (Pos.sum A.1 B.1).erase) →
      (i : Fin (raw.flow.splitChoices evalAddr A B parent).length) →
      AlignedSplitFork TraceOK T parent
        ((raw.flow.splitChoices evalAddr A B parent).get i)
  saturate : SourcedSatCallback U R O Base raw.saturate TraceOK

def SourcedControl.forget (ctl : SourcedControl U R O Base) :
    Control U R O Base :=
  ctl.raw

/-! ### Realization transport used by the structural recursion -/

private theorem OriginAssignment.ext'
    {R : AliasResolver sig} {Γ : StableCtx sig}
    (left right : OriginAssignment R Γ)
    (h : ∀ {S} (x : StableVar Γ S), left.ref x = right.ref x) :
    left = right := by
  cases left with
  | mk left =>
      cases right with
      | mk right =>
          congr
          funext S x
          exact h x

private theorem CodeOriginAssignment.realize_rename_weaken_eq
    {R : AliasResolver sig} {Δ : Ctx sig} {Γ : StableCtx sig}
    (D : BoundOrigins R Δ) (source : ResolvedRef R A)
    (E : CodeOriginAssignment R Δ Γ) :
    (E.rename (Rename.weaken : Rename sig Δ (Δ.snoc A))).realize
        (D.snoc source) = E.realize D := by
  cases hleft : (E.rename (Rename.weaken : Rename sig Δ (Δ.snoc A))).realize
      (D.snoc source) with
  | mk left =>
      cases hright : E.realize D with
      | mk right =>
          congr
          funext S x
          simpa [hleft, hright] using
            CodeOriginAssignment.realize_rename_weaken_ref D source E x

private theorem CodeOriginAssignment.realize_snoc_eq
    {R : AliasResolver sig} {Δ : Ctx sig} {Γ : StableCtx sig}
    (D : BoundOrigins R Δ) (E : CodeOriginAssignment R Δ Γ)
    {S : StableTy sig.nBases} (source : CanonRef R Δ S.erase) :
    (E.snoc source).realize D =
      (E.realize D).snoc (source.realize D) := by
  apply OriginAssignment.ext'
  intro T x
  cases x <;> rfl

/-! ### Source-producing structural evaluation -/

def runSourcedSInv {U : SearchUniverse sig} {R : AliasResolver sig}
    {O : Type} {Base : Ctx2 U.toTypeUniverse}
    (closed : U.StructurallyClosed) (ctl : SourcedControl U R O Base)
    (evalAddr : EvalAddr) (localAddr : LocalAddr) :
    ∀ {Δ : Ctx sig} {T : ExactTraceAt R}, ctl.TraceOK T →
      (D : BoundOrigins R Δ) →
      {Old New : StableCtx sig} →
      (seg : Segment U.toTypeUniverse R O Base Old New) →
      (E : CodeOriginAssignment R Δ (Old.append New)) →
      E.realize D = seg.frame.origins →
      (resolved : ResolvedPending U O) →
      (pending : CodePendingAssignment R Δ resolved.erase) →
      (G : Goal sig.nBases) → G.InUniverse U →
      SourcedResults (FreshSInv Old New resolved.erase G)
        (SourcedFreshSInv R T D E pending)
  | Δ, T, hT, D, Old, New, seg, E, hE,
      ⟨⟨.sum A B, hSum⟩, K⟩ :: rest, pending, G, hG =>
      let hA := closed.sum_left hSum
      let hB := closed.sum_right hSum
      let choices := ctl.raw.flow.splitChoices evalAddr ⟨A, hA⟩ ⟨B, hB⟩
        ((pending.ref .here).realize D)
      (List.occurrences choices).flatMap fun occurrence =>
        let choice := occurrence.value
        let sourcedFork := ctl.splitForkAt hT evalAddr
          (.splitChoice occurrence.index.val :: localAddr) ⟨A, hA⟩ ⟨B, hB⟩
          ((pending.ref .here).realize D) occurrence.index
        let leftE := E.rename (Rename.weaken (A := A.erase))
        let leftPending := CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := A.erase)))
        let leftD := D.snoc choice.leftRef
        let leftHE : leftE.realize leftD = seg.frame.origins := by
          rw [CodeOriginAssignment.realize_rename_weaken_eq, hE]
        (runSourcedSInv closed ctl (.caseLeft :: evalAddr)
          (.eval .caseLeft :: .splitChoice occurrence.index.val :: localAddr)
          sourcedFork.leftOK leftD seg leftE leftHE
          (⟨⟨A, hA⟩, K⟩ :: rest) leftPending G hG).flatMap fun left =>
            let rightE := E.rename (Rename.weaken (A := B.erase))
            let rightPending := CodePendingAssignment.cons (.bound .here)
              (pending.tail.rename (Rename.weaken (A := B.erase)))
            let rightD := D.snoc choice.rightRef
            let rightHE : rightE.realize rightD = seg.frame.origins := by
              rw [CodeOriginAssignment.realize_rename_weaken_eq, hE]
            (runSourcedSInv closed ctl (.caseRight :: evalAddr)
              (.eval .caseRight :: .splitChoice occurrence.index.val :: localAddr)
              sourcedFork.rightOK rightD seg rightE rightHE
              (⟨⟨B, hB⟩, K⟩ :: rest) rightPending G hG).map fun right =>
                { value := FreshSInv.caseSum left.value right.value
                  certificate :=
                    { source := .caseSum choice sourcedFork.fork
                        sourcedFork.left_eq sourcedFork.right_eq
                        left.certificate.source right.certificate.source
                      exact := by
                        change left.certificate.source.Exact ∧
                          right.certificate.source.Exact
                        exact ⟨left.certificate.exact,
                          right.certificate.exact⟩ } }
  | _, _, _, _, _, _, _, _, _, ⟨⟨.zero, _⟩, _⟩ :: _, _, _, _ =>
      [{ value := FreshSInv.abort
         certificate := ⟨.abort, trivial⟩ }]
  | Δ, T, hT, D, Old, New, seg, E, hE,
      ⟨⟨.atom q, hq⟩, K⟩ :: rest, pending, G, hG =>
      let childSeg := seg.storeAtom (closed.stable_atom hq) K (pending.realize D)
      let childE := E.snoc (S := .atom q) (pending.ref .here)
      let childHE : childE.realize D = childSeg.frame.origins := by
        rw [CodeOriginAssignment.realize_snoc_eq, hE]
        rfl
      (runSourcedSInv closed ctl (.storeTail :: evalAddr)
        (.eval .storeTail :: localAddr) hT D childSeg childE childHE
        rest pending.tail G hG).map fun child =>
          { value := FreshSInv.storeAtom child.value
            certificate :=
              { source := .storeAtom child.certificate.source
                exact := child.certificate.exact } }
  | Δ, T, hT, D, Old, New, seg, E, hE,
      ⟨⟨.shift N, hN⟩, K⟩ :: rest, pending, G, hG =>
      let childSeg := seg.storeShift
        (closed.stable_neg (closed.pos_shift hN)) K (pending.realize D)
      let childE := E.snoc (S := .neg N) (pending.ref .here)
      let childHE : childE.realize D = childSeg.frame.origins := by
        rw [CodeOriginAssignment.realize_snoc_eq, hE]
        rfl
      (runSourcedSInv closed ctl (.storeTail :: evalAddr)
        (.eval .storeTail :: localAddr) hT D childSeg childE childHE
        rest pending.tail G hG).map fun child =>
          { value := FreshSInv.storeShift child.value
            certificate :=
              { source := .storeShift child.certificate.source
                exact := child.certificate.exact } }
  | _, _, _, _, _, _, _, _, _, [], _, .neg .one, _ =>
      [{ value := FreshSInv.unit
         certificate := ⟨.unit, trivial⟩ }]
  | Δ, T, hT, D, Old, New, seg, E, hE, [], pending,
      .neg (.prod A B), hProd =>
      (runSourcedSInv closed ctl (.pairLeft :: evalAddr)
        (.eval .pairLeft :: localAddr) hT D seg E hE [] pending
        (.neg A) (closed.prod_left hProd)).flatMap fun left =>
          (runSourcedSInv closed ctl (.pairRight :: evalAddr)
            (.eval .pairRight :: localAddr) hT D seg E hE [] pending
            (.neg B) (closed.prod_right hProd)).map fun right =>
              { value := FreshSInv.pair left.value right.value
                certificate :=
                  { source := .pair left.certificate.source
                      right.certificate.source
                    exact := by
                      change left.certificate.source.Exact ∧
                        right.certificate.source.Exact
                      exact ⟨left.certificate.exact,
                        right.certificate.exact⟩ } }
  | Δ, T, hT, D, Old, New, seg, E, hE, [], pending,
      .neg (.arr A B), hArr =>
      let hA := closed.arr_dom hArr
      let sources := ctl.raw.flow.lambdaSources (.lamBody :: evalAddr) ⟨A, hA⟩
      (List.occurrences sources).flatMap fun occurrence =>
        let source := occurrence.value
        let bodyHE :
            (E.rename (Rename.weaken (A := A.erase))).realize
              (D.snoc source) = seg.frame.origins := by
          rw [CodeOriginAssignment.realize_rename_weaken_eq, hE]
        (runSourcedSInv closed ctl (.lamBody :: evalAddr)
          (.eval .lamBody :: .lambdaChoice occurrence.index.val :: localAddr)
          hT (D.snoc source) seg (E.rename (Rename.weaken (A := A.erase))) bodyHE
          (ResolvedPending.lambdaPending ⟨A, hA⟩)
          (CodePendingAssignment.cons (.bound .here)
            (CodePendingAssignment.rename (Rename.weaken (A := A.erase))
              pending))
          (.neg B) (closed.arr_cod hArr)).map fun body =>
            { value := FreshSInv.lam body.value
              certificate :=
                { source := .lam source body.certificate.source
                  exact := by
                    change body.certificate.source.Exact
                    exact body.certificate.exact } }
  | Δ, T, hT, D, Old, New, seg, E, hE, [], _,
      .neg (.shift P), hShift =>
      let rawAddr := .satShift :: evalAddr
      let raw := ctl.raw.saturate rawAddr seg ⟨P, closed.neg_shift hShift⟩
      (List.occurrences raw).map fun occurrence =>
        let sat := ctl.saturate.sourceAt hT D rawAddr
          (.saturationChoice occurrence.index.val :: .eval .satShift :: localAddr)
          seg E hE ⟨P, closed.neg_shift hShift⟩ occurrence.index
        { value := FreshSInv.satShift occurrence.value
          certificate :=
            { source := .satShift sat.source
              exact := by
                change sat.source.Exact
                exact sat.exact } }
  | Δ, T, hT, D, Old, New, seg, E, hE, [], _, .pos P, hP =>
      let rawAddr := .satPos :: evalAddr
      let raw := ctl.raw.saturate rawAddr seg ⟨P, hP⟩
      (List.occurrences raw).map fun occurrence =>
        let sat := ctl.saturate.sourceAt hT D rawAddr
          (.saturationChoice occurrence.index.val :: .eval .satPos :: localAddr)
          seg E hE ⟨P, hP⟩ occurrence.index
        { value := FreshSInv.satPos occurrence.value
          certificate :=
            { source := .satPos sat.source
              exact := by
                change sat.source.Exact
                exact sat.exact } }
termination_by Δ T hT D Old New seg E hE resolved pending G hG =>
  invWeight resolved G
decreasing_by
  all_goals simp [invWeight, pendingLocalWeight, goalLocalWeight,
    posLocalWeight, negLocalWeight, ResolvedPending.lambdaPending] <;> omega

def runSourcedSPos {U : SearchUniverse sig} {R : AliasResolver sig}
    {O : Type} {Base : Ctx2 U.toTypeUniverse}
    (closed : U.StructurallyClosed) (ctl : SourcedControl U R O Base)
    (evalAddr : EvalAddr) (localAddr : LocalAddr)
    {Δ : Ctx sig} {T : ExactTraceAt R} (hT : ctl.TraceOK T)
    (D : BoundOrigins R Δ) {Γ : StableCtx sig}
    (seg : Segment U.toTypeUniverse R O Base Γ .empty)
    (E : CodeOriginAssignment R Δ Γ)
    (hE : E.realize D = seg.frame.origins) :
    ∀ (P : Pos sig.nBases), P ∈ U.pos →
      SourcedResults (FreshSPos Γ P) (SourcedFreshSPos R T D E)
  | .atom q, hq =>
      (seg.frame.reps ⟨.atom q, closed.stable_atom hq⟩).map fun rep =>
        { value := rep.toFreshSAtom
          certificate :=
            { source := LocalPosSource.atom (T := T) (D := D) (E := E) rep.1
              exact := by trivial } }
  | .zero, _ => []
  | .sum A B, hSum =>
      ((runSourcedSPos closed ctl (.posInl :: evalAddr)
        (.positiveChoice 0 :: .eval .posInl :: localAddr) hT D seg E hE A
        (closed.sum_left hSum)).map fun left =>
          { value := FreshSPos.inl left.value
            certificate :=
              { source := .inl left.certificate.source
                exact := left.certificate.exact } }) ++
      ((runSourcedSPos closed ctl (.posInr :: evalAddr)
        (.positiveChoice 1 :: .eval .posInr :: localAddr) hT D seg E hE B
        (closed.sum_right hSum)).map fun right =>
          { value := FreshSPos.inr right.value
            certificate :=
              { source := .inr right.certificate.source
                exact := right.certificate.exact } })
  | .shift N, hShift =>
      (runSourcedSInv closed ctl (.posShift :: evalAddr)
        (.eval .posShift :: localAddr) hT D seg E hE []
        (CodePendingAssignment.empty R Δ) (.neg N)
        (closed.pos_shift hShift)).map fun child =>
          { value := FreshSPos.shift child.value
            certificate :=
              { source := .shift child.certificate.source
                exact := child.certificate.exact } }
termination_by P hP => posLocalWeight P
decreasing_by
  all_goals simp [posLocalWeight] <;> omega

/-! ### Small definitional gates -/

@[simp] theorem SourcedControl.forget_raw
    (ctl : SourcedControl U R O Base) : ctl.forget = ctl.raw := rfl

theorem AlignedSplitFork.left_trace_ok
    (fork : AlignedSplitFork TraceOK T parent choice) :
    TraceOK fork.fork.leftTrace := fork.leftOK

theorem AlignedSplitFork.right_trace_ok
    (fork : AlignedSplitFork TraceOK T parent choice) :
    TraceOK fork.fork.rightTrace := fork.rightOK

end Gimbal.Equality.Scherer
