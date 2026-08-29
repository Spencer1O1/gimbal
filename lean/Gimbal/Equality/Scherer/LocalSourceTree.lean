/-
  Unary occurrence-local source trees for saturated Scherer syntax.

  Every trace extension and locally generated origin is carried only at the
  literal syntax occurrence which uses it.  Exact-key agreement is a later
  layer; this file deliberately records the raw occurrence data first.
-/

import Gimbal.Equality.Scherer.OccurrenceExact

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

mutual

inductive LocalNegSource (R : AliasResolver sig) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Γ : StableCtx sig} → (E : CodeOriginAssignment R Δ Γ) →
    {N : Neg sig.nBases} → SNegNeu Γ N → Type where
  | var {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {N : Neg sig.nBases} (x : StableVar Γ (.neg N)) :
      LocalNegSource R T D E (.var x)
  | fst {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Neg sig.nBases} {n : SNegNeu Γ (.prod A B)} :
      LocalNegSource R T D E n → LocalNegSource R T D E (.fst n)
  | snd {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Neg sig.nBases} {n : SNegNeu Γ (.prod A B)} :
      LocalNegSource R T D E n → LocalNegSource R T D E (.snd n)
  | app {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A : Pos sig.nBases} {N : Neg sig.nBases}
      {n : SNegNeu Γ (.arr A N)} {p : SPosNeu Γ A} :
      LocalNegSource R T D E n → LocalPosSource R T D E p →
      LocalNegSource R T D E (.app n p)

inductive LocalPosSource (R : AliasResolver sig) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Γ : StableCtx sig} → (E : CodeOriginAssignment R Δ Γ) →
    {P : Pos sig.nBases} → SPosNeu Γ P → Type where
  | atom {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {q : Fin sig.nBases} (x : StableVar Γ (.atom q)) :
      LocalPosSource R T D E (.atom x)
  | inl {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases} {p : SPosNeu Γ A} :
      LocalPosSource R T D E p → LocalPosSource R T D E (.inl (B := B) p)
  | inr {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases} {p : SPosNeu Γ B} :
      LocalPosSource R T D E p → LocalPosSource R T D E (.inr (A := A) p)
  | shift {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {N : Neg sig.nBases} {t : SInv Γ .empty .empty (.neg N)} :
      LocalInvSource R (Old := Γ) (New := .empty) T D E
        (CodePendingAssignment.empty R Δ) t →
      LocalPosSource R T D E (.shift t)

inductive LocalInvSource (R : AliasResolver sig) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Old New : StableCtx sig} → {ps : Pending sig} → {G : Goal sig.nBases} →
    (E : CodeOriginAssignment R Δ (Old.append New)) →
    (pending : CodePendingAssignment R Δ ps) → SInv Old New ps G → Type where
  | caseSum {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {A B : Pos sig.nBases} {ps : Pending sig}
      {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons (.sum A B) ps)}
      {left : SInv Old New (.cons A ps) G}
      {right : SInv Old New (.cons B ps) G}
      (choice : SplitChoice R ((pending.ref .here).realize D))
      (fork : SplitFork T ((pending.ref .here).realize D))
      (left_eq : choice.leftOrigin = fork.leftPayload)
      (right_eq : choice.rightOrigin = fork.rightPayload)
      (leftSource : LocalInvSource R fork.leftTrace (D.snoc choice.leftRef)
        (E.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := A.erase)))) left)
      (rightSource : LocalInvSource R fork.rightTrace (D.snoc choice.rightRef)
        (E.rename (Rename.weaken (A := B.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := B.erase)))) right) :
      LocalInvSource R T D E pending (.caseSum left right)
  | abort {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons .zero ps)} :
      LocalInvSource R T D E pending
        (.abort (Old := Old) (New := New) (ps := ps) (G := G))
  | storeAtom {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {q : Fin sig.nBases} {ps : Pending sig}
      {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons (.atom q) ps)}
      {t : SInv Old (New.snoc (.atom q)) ps G} :
      LocalInvSource R (Old := Old) (New := New.snoc (.atom q)) T D
        (E.snoc (S := .atom q) (pending.ref .here))
        pending.tail t → LocalInvSource R T D E pending (.storeAtom t)
  | storeShift {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {N : Neg sig.nBases} {ps : Pending sig}
      {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons (.shift N) ps)}
      {t : SInv Old (New.snoc (.neg N)) ps G} :
      LocalInvSource R (Old := Old) (New := New.snoc (.neg N)) T D
        (E.snoc (S := .neg N) (pending.ref .here))
        pending.tail t → LocalInvSource R T D E pending (.storeShift t)
  | unit {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty} :
      LocalInvSource R T D E pending (.unit (Old := Old) (New := New))
  | pair {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {A B : Neg sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {left : SInv Old New .empty (.neg A)}
      {right : SInv Old New .empty (.neg B)} :
      LocalInvSource R T D E pending left →
      LocalInvSource R T D E pending right →
      LocalInvSource R T D E pending (.pair left right)
  | lam {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {A : Pos sig.nBases} {B : Neg sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {body : SInv Old New (.cons A .empty) (.neg B)}
      (source : ResolvedRef R A.erase)
      (bodySource : LocalInvSource R T (D.snoc source)
        (E.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.rename (Rename.weaken (A := A.erase)))) body) :
      LocalInvSource R T D E pending (.lam body)
  | satShift {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {P : Pos sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty} {s : Sat Old New P} :
      LocalSatSource R T D E s → LocalInvSource R T D E pending (.satShift s)
  | satPos {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {P : Pos sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty} {s : Sat Old New P} :
      LocalSatSource R T D E s → LocalInvSource R T D E pending (.satPos s)

inductive LocalSatSource (R : AliasResolver sig) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Old New : StableCtx sig} →
    (E : CodeOriginAssignment R Δ (Old.append New)) →
    {P : Pos sig.nBases} → Sat Old New P → Type where
  | inconsistent {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {P : Pos sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {z : SNegNeu (Old.append New) (.shift .zero)} :
      LocalNegSource R T D E z →
      LocalSatSource R T D E (.inconsistent (P := P) z)
  | done {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {P : Pos sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {p : SPosNeu (Old.append New) P} :
      LocalPosSource R T D E p → LocalSatSource R T D E (.done p)
  | batch {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {selected : Pending sig}
      {P : Pos sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {obs : NonemptyBatchObs (Old.append New) selected}
      {body : SInv (Old.append New) .empty selected (.pos P)}
      (obsSource : LocalBatchSource R T D E obs)
      (keys : BatchExactKeys R selected)
      (B : LocalExactBatch R obs keys) (addr : LocalAddr)
      (addressed : B.Addressed addr) (X : B.Extension T)
      (bodySource : LocalInvSource R (Old := Old.append New) (New := .empty) X.next
        (D.pushPending X.results.resolved)
        (E.rename (Pending.weakenCodeBase selected Δ))
        (CodePendingAssignment.boundBatch X.results Δ) body) :
      LocalSatSource R T D E (.batch obs body)

inductive LocalBatchSource (R : AliasResolver sig) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Γ : StableCtx sig} → (E : CodeOriginAssignment R Δ Γ) →
    {selected : Pending sig} → NonemptyBatchObs Γ selected → Type where
  | one {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {Q : Pos sig.nBases} {n : SNegNeu Γ (.shift Q)} :
      LocalNegSource R T D E n → LocalBatchSource R T D E (.one n)
  | cons {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {Q : Pos sig.nBases} {ps : Pending sig} {n : SNegNeu Γ (.shift Q)}
      {rest : NonemptyBatchObs Γ ps} :
      LocalNegSource R T D E n → LocalBatchSource R T D E rest →
      LocalBatchSource R T D E (.cons n rest)

end

/-! ### Source-directed locally nameless structural codes -/

mutual

def localNegToStructuralCode
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {N : Neg sig.nBases}
    {n : SNegNeu Γ N} {Ξ : Ctx sig} (s : LocalNegSource R T D E n)
    (C : CodeOriginAssignment R Ξ Γ) : SNegCode R Ξ N :=
  match s with
  | .var x => .var (C.ref x)
  | .fst n => .fst (localNegToStructuralCode n C)
  | .snd n => .snd (localNegToStructuralCode n C)
  | .app n p => .app (localNegToStructuralCode n C) (localPosToStructuralCode p C)
termination_by structural s

def localPosToStructuralCode
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {P : Pos sig.nBases}
    {p : SPosNeu Γ P} {Ξ : Ctx sig} (s : LocalPosSource R T D E p)
    (C : CodeOriginAssignment R Ξ Γ) : SPosCode R Ξ P :=
  match s with
  | .atom x => .atom (C.ref x)
  | .inl p => .inl (localPosToStructuralCode p C)
  | .inr p => .inr (localPosToStructuralCode p C)
  | .shift t => .shift (localInvToStructuralCode t C (CodePendingAssignment.empty R Ξ))
termination_by structural s

def localInvToStructuralCode
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Old New : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} {E : CodeOriginAssignment R Δ (Old.append New)}
    {pending : CodePendingAssignment R Δ ps} {t : SInv Old New ps G}
    {Ξ : Ctx sig} (s : LocalInvSource R T D E pending t)
    (C : CodeOriginAssignment R Ξ (Old.append New))
    (cp : CodePendingAssignment R Ξ ps) : BranchCode R Ξ ps G :=
  match s with
  | .caseSum _ _ _ _ left right =>
      .caseSum
        (localInvToStructuralCode left (C.rename (Rename.weaken (A := _)))
          (CodePendingAssignment.cons (.bound .here)
            (cp.tail.rename (Rename.weaken (A := _)))))
        (localInvToStructuralCode right (C.rename (Rename.weaken (A := _)))
          (CodePendingAssignment.cons (.bound .here)
            (cp.tail.rename (Rename.weaken (A := _)))))
  | .abort (ps := ps) => .abort (ps := ps)
  | .storeAtom child =>
      .storeAtom (localInvToStructuralCode child (C.snoc (cp.ref .here)) cp.tail)
  | .storeShift child =>
      .storeShift (localInvToStructuralCode child (C.snoc (cp.ref .here)) cp.tail)
  | .unit => .unit
  | .pair left right =>
      .pair (localInvToStructuralCode left C cp) (localInvToStructuralCode right C cp)
  | .lam _ body =>
      .lam (localInvToStructuralCode body (C.rename (Rename.weaken (A := _)))
        (CodePendingAssignment.cons (.bound .here)
          (cp.rename (Rename.weaken (A := _)))))
  | .satShift s => .satShift (localSatToStructuralCode s C)
  | .satPos s => .satPos (localSatToStructuralCode s C)
termination_by structural s

def localSatToStructuralCode
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Old New : StableCtx sig}
    {E : CodeOriginAssignment R Δ (Old.append New)} {P : Pos sig.nBases}
    {sat : Sat Old New P} {Ξ : Ctx sig} (s : LocalSatSource R T D E sat)
    (C : CodeOriginAssignment R Ξ (Old.append New)) : SatCode R Ξ P :=
  match s with
  | .inconsistent _ => .inconsistent
  | .done p => .done (localPosToStructuralCode p C)
  | .batch obs _ _ _ _ X body =>
      .batch (localBatchToStructuralCode obs C)
        (localInvToStructuralCode body
          (C.rename (Pending.weakenCodeBase _ Ξ))
          (CodePendingAssignment.boundBatch X.results Ξ))
termination_by structural s

def localBatchToStructuralCode
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {selected : Pending sig}
    {obs : NonemptyBatchObs Γ selected} {Ξ : Ctx sig}
    (s : LocalBatchSource R T D E obs)
    (C : CodeOriginAssignment R Ξ Γ) : BatchCode R Ξ selected :=
  match s with
  | .one n => .one (localNegToStructuralCode n C)
  | .cons n rest => .cons (localNegToStructuralCode n C)
      (localBatchToStructuralCode rest C)
termination_by structural s

end

abbrev LocalNegSource.toStructuralCode := @localNegToStructuralCode
abbrev LocalPosSource.toStructuralCode := @localPosToStructuralCode
abbrev LocalInvSource.toStructuralCode := @localInvToStructuralCode
abbrev LocalSatSource.toStructuralCode := @localSatToStructuralCode
abbrev LocalBatchSource.toStructuralCode := @localBatchToStructuralCode

def LocalNegSource.exactKey
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {Q : Pos sig.nBases}
    {n : SNegNeu Γ (.shift Q)} (s : LocalNegSource R T D E n) :
    ExactObsKey R Q.erase :=
  ExactObsKey.ofStructural
    (s.toStructuralCode (CodeOriginAssignment.ofOrigin (E.realize D)))

def LocalBatchSource.exactKeys
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {selected : Pending sig}
    {obs : NonemptyBatchObs Γ selected} :
    (s : LocalBatchSource R T D E obs) → BatchExactKeys R selected
  | .one n => ⟨fun x => match x with
      | .here => n.exactKey
      | .there x => nomatch x⟩
  | .cons n rest => ⟨fun x => match x with
      | .here => n.exactKey
      | .there x => rest.exactKeys.keyAt x⟩

/-! ### Recursive occurrence exactness -/

mutual

def LocalNegSource.Exact
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {N : Neg sig.nBases}
    {n : SNegNeu Γ N} : LocalNegSource R T D E n → Prop
  | .var _ => True
  | .fst n | .snd n => n.Exact
  | .app n p => n.Exact ∧ p.Exact
termination_by structural s => s

def LocalPosSource.Exact
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {P : Pos sig.nBases}
    {p : SPosNeu Γ P} : LocalPosSource R T D E p → Prop
  | .atom _ => True
  | .inl p | .inr p => p.Exact
  | .shift t => t.Exact
termination_by structural s => s

def LocalInvSource.Exact
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Old New : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} {E : CodeOriginAssignment R Δ (Old.append New)}
    {pending : CodePendingAssignment R Δ ps} {t : SInv Old New ps G} :
    LocalInvSource R T D E pending t → Prop
  | .caseSum _ _ _ _ left right => left.Exact ∧ right.Exact
  | .abort => True
  | .storeAtom child | .storeShift child => child.Exact
  | .unit => True
  | .pair left right => left.Exact ∧ right.Exact
  | .lam _ body => body.Exact
  | .satShift s | .satPos s => s.Exact
termination_by structural s => s

def LocalSatSource.Exact
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Old New : StableCtx sig}
    {E : CodeOriginAssignment R Δ (Old.append New)} {P : Pos sig.nBases}
    {sat : Sat Old New P} : LocalSatSource R T D E sat → Prop
  | .inconsistent z => z.Exact
  | .done p => p.Exact
  | .batch obsSource keys _ _ _ _ bodySource =>
      obsSource.Exact ∧ bodySource.Exact ∧
        ∀ {Q} (x : PendingVar _ Q),
          keys.keyAt x = obsSource.exactKeys.keyAt x
termination_by structural s => s

def LocalBatchSource.Exact
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {selected : Pending sig}
    {obs : NonemptyBatchObs Γ selected} : LocalBatchSource R T D E obs → Prop
  | .one n => n.Exact
  | .cons n rest => n.Exact ∧ rest.Exact
termination_by structural s => s

end

/-- The occurrence-local data retained when an exact saturated source is a
literal batch.  This dependent record is the later layer's existential view;
it preserves the exact batch, its address proof, and its owned extension. -/
structure LocalExactBatchView (R : AliasResolver sig)
    {Δ : Ctx sig} (T : ExactTraceAt R) (D : BoundOrigins R Δ)
    {Γ : StableCtx sig} (E : CodeOriginAssignment R Δ Γ)
    {selected : Pending sig} {P : Pos sig.nBases}
    (obs : NonemptyBatchObs Γ selected)
    (body : SInv Γ .empty selected (.pos P)) where
  obsSource : LocalBatchSource R T D E obs
  obsExact : obsSource.Exact
  keys : BatchExactKeys R selected
  batch : LocalExactBatch R obs keys
  addr : LocalAddr
  addressed : batch.Addressed addr
  extension : batch.Extension T
  bodySource : LocalInvSource R (Old := Γ) (New := .empty) extension.next
    (D.pushPending extension.results.resolved)
    (E.rename (Pending.weakenCodeBase selected Δ))
    (CodePendingAssignment.boundBatch extension.results Δ) body
  bodyExact : bodySource.Exact
  keys_eq : ∀ {Q} (x : PendingVar selected Q),
    keys.keyAt x = obsSource.exactKeys.keyAt x

def LocalSatSource.Exact.toBatchView
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Old New : StableCtx sig}
    {E : CodeOriginAssignment R Δ (Old.append New)}
    {selected : Pending sig} {P : Pos sig.nBases}
    {obs : NonemptyBatchObs (Old.append New) selected}
    {body : SInv (Old.append New) .empty selected (.pos P)}
    {source : LocalSatSource R T D E (.batch obs body)}
    (h : source.Exact) : LocalExactBatchView R T D E obs body :=
  match source with
  | .batch obsSource keys B addr addressed X bodySource =>
      ⟨obsSource, h.1, keys, B, addr, addressed, X, bodySource, h.2.1, h.2.2⟩

/-! ### Fresh values with exact occurrence sources -/

structure SourcedFreshSNeg (R : AliasResolver sig)
    {Δ : Ctx sig} (T : ExactTraceAt R) (D : BoundOrigins R Δ)
    {Γ : StableCtx sig} (E : CodeOriginAssignment R Δ Γ)
    {N : Neg sig.nBases} (fresh : FreshSNeg Γ N) where
  source : LocalNegSource R T D E fresh.neutral
  exact : source.Exact

structure SourcedFreshSPos (R : AliasResolver sig)
    {Δ : Ctx sig} (T : ExactTraceAt R) (D : BoundOrigins R Δ)
    {Γ : StableCtx sig} (E : CodeOriginAssignment R Δ Γ)
    {P : Pos sig.nBases} (fresh : FreshSPos Γ P) where
  source : LocalPosSource R T D E fresh.neutral
  exact : source.Exact

structure SourcedFreshSInv (R : AliasResolver sig)
    {Δ : Ctx sig} (T : ExactTraceAt R) (D : BoundOrigins R Δ)
    {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
    (E : CodeOriginAssignment R Δ (Old.append New))
    (pending : CodePendingAssignment R Δ ps)
    (fresh : FreshSInv Old New ps G) where
  source : LocalInvSource R T D E pending fresh.proof
  exact : source.Exact

structure SourcedFreshSat (R : AliasResolver sig)
    {Δ : Ctx sig} (T : ExactTraceAt R) (D : BoundOrigins R Δ)
    {Old New : StableCtx sig} (E : CodeOriginAssignment R Δ (Old.append New))
    {P : Pos sig.nBases} (fresh : FreshSat Old New P) where
  source : LocalSatSource R T D E fresh.proof
  exact : source.Exact

def SourcedFreshSNeg.forget
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {N : Neg sig.nBases}
    {fresh : FreshSNeg Γ N} (_ : SourcedFreshSNeg R T D E fresh) : FreshSNeg Γ N :=
  fresh

def SourcedFreshSPos.forget
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {P : Pos sig.nBases}
    {fresh : FreshSPos Γ P} (_ : SourcedFreshSPos R T D E fresh) : FreshSPos Γ P :=
  fresh

def SourcedFreshSInv.forget
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Old New : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} {E : CodeOriginAssignment R Δ (Old.append New)}
    {pending : CodePendingAssignment R Δ ps} {fresh : FreshSInv Old New ps G}
    (_ : SourcedFreshSInv R T D E pending fresh) : FreshSInv Old New ps G := fresh

def SourcedFreshSat.forget
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Old New : StableCtx sig}
    {E : CodeOriginAssignment R Δ (Old.append New)} {P : Pos sig.nBases}
    {fresh : FreshSat Old New P} (_ : SourcedFreshSat R T D E fresh) :
    FreshSat Old New P := fresh

@[simp] theorem SourcedFreshSNeg.forget_eq (s : SourcedFreshSNeg R T D E fresh) :
    s.forget = fresh := rfl

@[simp] theorem SourcedFreshSPos.forget_eq (s : SourcedFreshSPos R T D E fresh) :
    s.forget = fresh := rfl

@[simp] theorem SourcedFreshSInv.forget_eq
    (s : SourcedFreshSInv R T D E pending fresh) : s.forget = fresh := rfl

@[simp] theorem SourcedFreshSat.forget_eq (s : SourcedFreshSat R T D E fresh) :
    s.forget = fresh := rfl

/-! ### Boundary fixtures -/

namespace LocalSourceTreeFixtures

theorem exact_free_negative
    {R : AliasResolver sig} (T : ExactTraceAt R)
    (E : OriginAssignment R Γ) {N : Neg sig.nBases}
    (x : StableVar Γ (.neg N)) :
    (LocalNegSource.var (T := T) (D := BoundOrigins.empty R)
      (E := CodeOriginAssignment.ofOrigin E) x).Exact := trivial

theorem exact_free_atom
    {R : AliasResolver sig} (T : ExactTraceAt R)
    (E : OriginAssignment R Γ) {q : Fin sig.nBases}
    (x : StableVar Γ (.atom q)) :
    (LocalPosSource.atom (T := T) (D := BoundOrigins.empty R)
      (E := CodeOriginAssignment.ofOrigin E) x).Exact := trivial

theorem free_atom_terminal_coding
    {R : AliasResolver sig} {Δ Ξ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {q : Fin sig.nBases}
    (C : CodeOriginAssignment R Ξ Γ) (x : StableVar Γ (.atom q)) :
    (LocalPosSource.atom (R := R) (T := T) (D := D) (E := E) x).toStructuralCode C =
      .atom (C.ref x) := rfl

theorem app_argument_order
    {R : AliasResolver sig} {Δ Ξ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {A : Pos sig.nBases}
    {N : Neg sig.nBases} {n : SNegNeu Γ (.arr A N)} {p : SPosNeu Γ A}
    (C : CodeOriginAssignment R Ξ Γ)
    (fn : LocalNegSource R T D E n) (arg : LocalPosSource R T D E p) :
    (LocalNegSource.app fn arg).toStructuralCode C =
      .app (fn.toStructuralCode C) (arg.toStructuralCode C) := rfl

theorem store_atom_reuses_pending_source
    {R : AliasResolver sig} {Δ Ξ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Old New : StableCtx sig} {q : Fin sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    {E : CodeOriginAssignment R Δ (Old.append New)}
    {pending : CodePendingAssignment R Δ (.cons (.atom q) ps)}
    {t : SInv Old (New.snoc (.atom q)) ps G}
    (child : LocalInvSource R (Old := Old) (New := New.snoc (.atom q)) T D
      (E.snoc (S := .atom q) (pending.ref .here)) pending.tail t)
    (C : CodeOriginAssignment R Ξ (Old.append New))
    (cp : CodePendingAssignment R Ξ (.cons (.atom q) ps)) :
    (LocalInvSource.storeAtom child).toStructuralCode C cp =
      .storeAtom (child.toStructuralCode (C.snoc (cp.ref .here)) cp.tail) := rfl

theorem store_shift_reuses_pending_source
    {R : AliasResolver sig} {Δ Ξ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Old New : StableCtx sig} {N : Neg sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    {E : CodeOriginAssignment R Δ (Old.append New)}
    {pending : CodePendingAssignment R Δ (.cons (.shift N) ps)}
    {t : SInv Old (New.snoc (.neg N)) ps G}
    (child : LocalInvSource R (Old := Old) (New := New.snoc (.neg N)) T D
      (E.snoc (S := .neg N) (pending.ref .here)) pending.tail t)
    (C : CodeOriginAssignment R Ξ (Old.append New))
    (cp : CodePendingAssignment R Ξ (.cons (.shift N) ps)) :
    (LocalInvSource.storeShift child).toStructuralCode C cp =
      .storeShift (child.toStructuralCode (C.snoc (cp.ref .here)) cp.tail) := rfl

theorem lambda_uses_bound_local_code
    {R : AliasResolver sig} {Δ Ξ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Old New : StableCtx sig} {A : Pos sig.nBases}
    {B : Neg sig.nBases} {E : CodeOriginAssignment R Δ (Old.append New)}
    {pending : CodePendingAssignment R Δ .empty}
    {body : SInv Old New (.cons A .empty) (.neg B)}
    (source : ResolvedRef R A.erase)
    (bodySource : LocalInvSource R T (D.snoc source)
      (E.rename (Rename.weaken (A := A.erase)))
      (CodePendingAssignment.cons (.bound .here)
        (pending.rename (Rename.weaken (A := A.erase)))) body)
    (C : CodeOriginAssignment R Ξ (Old.append New))
    (cp : CodePendingAssignment R Ξ .empty) :
    (LocalInvSource.lam source bodySource).toStructuralCode C cp =
      .lam (bodySource.toStructuralCode (C.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (cp.rename (Rename.weaken (A := A.erase))))) := rfl

theorem exact_store_atom
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Old New : StableCtx sig} {q : Fin sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    {E : CodeOriginAssignment R Δ (Old.append New)}
    {pending : CodePendingAssignment R Δ (.cons (.atom q) ps)}
    {t : SInv Old (New.snoc (.atom q)) ps G}
    (child : LocalInvSource R (Old := Old) (New := New.snoc (.atom q)) T D
      (E.snoc (S := .atom q) (pending.ref .here)) pending.tail t)
    (h : child.Exact) : (LocalInvSource.storeAtom child).Exact := h

theorem exact_lambda
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Old New : StableCtx sig} {A : Pos sig.nBases}
    {B : Neg sig.nBases} {E : CodeOriginAssignment R Δ (Old.append New)}
    {pending : CodePendingAssignment R Δ .empty}
    {body : SInv Old New (.cons A .empty) (.neg B)}
    (source : ResolvedRef R A.erase)
    (bodySource : LocalInvSource R T (D.snoc source)
      (E.rename (Rename.weaken (A := A.erase)))
      (CodePendingAssignment.cons (.bound .here)
        (pending.rename (Rename.weaken (A := A.erase)))) body)
    (h : bodySource.Exact) : (LocalInvSource.lam source bodySource).Exact := h

theorem case_children_keep_separate_fork_traces
    {R : AliasResolver sig} {T : ExactTraceAt R} {A B : Object sig.nBases}
    {parent : ResolvedRef R (.coprod A B)} (fork : SplitFork T parent) :
    fork.leftTrace.steps = .splitL parent.origin fork.leftPayload :: T.steps ∧
      fork.rightTrace.steps = .splitR parent.origin fork.rightPayload :: T.steps :=
  ⟨fork.left_steps, fork.right_steps⟩

theorem one_batch_code_preserves_entry
    {R : AliasResolver sig} {Δ Ξ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {Q : Pos sig.nBases}
    {n : SNegNeu Γ (.shift Q)} (source : LocalNegSource R T D E n)
    (C : CodeOriginAssignment R Ξ Γ) :
    (LocalBatchSource.one source).toStructuralCode C =
      .one (source.toStructuralCode C) := rfl

theorem two_batch_code_preserves_order_and_duplicates
    {R : AliasResolver sig} {Δ Ξ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {Q : Pos sig.nBases}
    {n : SNegNeu Γ (.shift Q)} (source : LocalNegSource R T D E n)
    (C : CodeOriginAssignment R Ξ Γ) :
    (LocalBatchSource.cons source (LocalBatchSource.one source)).toStructuralCode C =
      .cons (source.toStructuralCode C) (.one (source.toStructuralCode C)) := rfl

theorem exact_one_literal_batch
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {Q : Pos sig.nBases}
    {n : SNegNeu Γ (.shift Q)} (source : LocalNegSource R T D E n)
    (h : source.Exact) : (LocalBatchSource.one source).Exact := h

theorem exact_two_literal_batch
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {Q : Pos sig.nBases}
    {n : SNegNeu Γ (.shift Q)} (source : LocalNegSource R T D E n)
    (h : source.Exact) :
    (LocalBatchSource.cons source (LocalBatchSource.one source)).Exact := ⟨h, h⟩

theorem exact_one_two_literal_key_equality
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {Q : Pos sig.nBases}
    {n : SNegNeu Γ (.shift Q)} (source : LocalNegSource R T D E n) :
    (LocalBatchSource.one source).exactKeys.keyAt .here = source.exactKey ∧
      (LocalBatchSource.cons source (LocalBatchSource.one source)).exactKeys.keyAt .here =
        source.exactKey ∧
      (LocalBatchSource.cons source (LocalBatchSource.one source)).exactKeys.keyAt
          (.there .here) = source.exactKey :=
  ⟨rfl, rfl, rfl⟩

def nested_batch_exact_view
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {selected : Pending sig}
    {P : Pos sig.nBases} {obs : NonemptyBatchObs Γ selected}
    {body : SInv Γ .empty selected (.pos P)}
    (obsSource : LocalBatchSource R T D E obs) (hobs : obsSource.Exact)
    (keys : BatchExactKeys R selected) (B : LocalExactBatch R obs keys)
    (addr : LocalAddr) (addressed : B.Addressed addr) (X : B.Extension T)
    (bodySource : LocalInvSource R (Old := Γ) (New := .empty) X.next
      (D.pushPending X.results.resolved)
      (E.rename (Pending.weakenCodeBase selected Δ))
      (CodePendingAssignment.boundBatch X.results Δ) body)
    (hbody : bodySource.Exact)
    (hkeys : ∀ {Q} (x : PendingVar selected Q),
      keys.keyAt x = obsSource.exactKeys.keyAt x) :
    LocalExactBatchView R T D E obs body := by
  let source : LocalSatSource R (Old := Γ) (New := .empty) T D E
      (.batch obs body) :=
    .batch obsSource keys B addr addressed X bodySource
  have hexact : source.Exact := by
    change obsSource.Exact ∧ bodySource.Exact ∧ _
    exact ⟨hobs, hbody, hkeys⟩
  exact hexact.toBatchView

theorem sourced_fresh_forget_is_original
    (s : SourcedFreshSat R T D E fresh) : s.forget = fresh := rfl

theorem no_sourcedFreshSat_of_invalid
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Old New : StableCtx sig}
    {E : CodeOriginAssignment R Δ (Old.append New)} {P : Pos sig.nBases}
    {sat : Sat Old New P} (hbad : sat.freshValid = false) :
    ¬ ∃ (fresh : FreshSat Old New P), fresh.proof = sat ∧
      Nonempty (SourcedFreshSat R T D E fresh) := by
  rintro ⟨fresh, hproof, _⟩
  have hvalid := fresh.valid
  rw [hproof, hbad] at hvalid
  exact Bool.noConfusion hvalid

abbrev InvalidOld : StableCtx Fixtures.sig0 :=
  StableCtx.snoc .empty (.neg (.shift .zero))

abbrev InvalidNew : StableCtx Fixtures.sig0 :=
  StableCtx.snoc .empty
    (.neg (.arr (.shift (.shift (.shift .one))) (.shift .zero)))

/-- The regression uses only equality of the underlying fresh proof, not
proof irrelevance for either freshness or exactness certificates. -/
theorem recursively_invalid_nested_freshness_cannot_be_packaged
    {R : AliasResolver Fixtures.sig0} {Δ : Ctx Fixtures.sig0}
    {T : ExactTraceAt R} {D : BoundOrigins R Δ}
    {E : CodeOriginAssignment R Δ (InvalidOld.append InvalidNew)} :
    ¬ ∃ (fresh : FreshSat InvalidOld InvalidNew (.shift .one)),
      fresh.proof = FreshnessFixtures.usesNew_but_nested_oldOnly_invalid ∧
        Nonempty (SourcedFreshSat R T D E fresh) :=
  no_sourcedFreshSat_of_invalid
    FreshnessFixtures.usesNew_but_nested_oldOnly_invalid_freshValid_false

/-- Even when an application argument contains a literal nested batch, its
exact key is built from that occurrence's extension and never from a global
`BatchResultSupply`. -/
def nestedBatchExactKey
    {R : AliasResolver sig} {Δ : Ctx sig} {T : ExactTraceAt R}
    {D : BoundOrigins R Δ} {Γ : StableCtx sig}
    {E : CodeOriginAssignment R Δ Γ} {selected : Pending sig}
    {P Q : Pos sig.nBases} {obs : NonemptyBatchObs Γ selected}
    {body : SInv Γ .empty selected (.pos P)}
    {fn : SNegNeu Γ (.arr (.shift (.shift P)) (.shift Q))}
    (fnSource : LocalNegSource R T D E fn)
    (obsSource : LocalBatchSource R T D E obs)
    (keys : BatchExactKeys R selected) (B : LocalExactBatch R obs keys)
    (addr : LocalAddr) (addressed : B.Addressed addr) (X : B.Extension T)
    (bodySource : LocalInvSource R (Old := Γ) (New := .empty) X.next
      (D.pushPending X.results.resolved)
      (E.rename (Pending.weakenCodeBase selected Δ))
      (CodePendingAssignment.boundBatch X.results Δ) body) : ExactObsKey R Q.erase :=
  let batchSource : LocalSatSource R (Old := Γ) (New := .empty) T D E
      (.batch obs body) :=
    .batch (Old := Γ) (New := .empty) obsSource keys B addr addressed X bodySource
  let argSource : LocalPosSource R T D E (.shift (.satShift (.batch obs body))) :=
    .shift (.satShift batchSource)
  (LocalNegSource.app fnSource argSource).exactKey

end LocalSourceTreeFixtures

end Gimbal.Equality.Scherer
