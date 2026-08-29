/-
  Proof-relevant pair codes for already aligned saturated Scherer forms.
  All nondeterministic choices are supplied by `PairPlan`; construction does
  not select observations, allocate origins, or compare unresolved binders.
-/

import Gimbal.Equality.Scherer.PairTraceExtension

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Closing structural assignments -/

namespace CodeOriginAssignment

/-- Replace every externally assigned canonical reference by its terminal ref. -/
def resolved (D : BoundOrigins R Δ) (E : CodeOriginAssignment R Δ Γ) :
    CodeOriginAssignment R Δ Γ where
  ref x := .free ((E.ref x).realize D)

@[simp] theorem resolved_ref (D : BoundOrigins R Δ)
    (E : CodeOriginAssignment R Δ Γ) (x : StableVar Γ S) :
    (E.resolved D).ref x = .free ((E.ref x).realize D) := rfl

end CodeOriginAssignment

/-! ### Caller-supplied construction plans -/

mutual

inductive PairPosPlan (R : AliasResolver sig) (supply : BatchResultSupply R) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Γ : StableCtx sig} → (E : CodeOriginAssignment R Δ Γ) →
    {P : Pos sig.nBases} → {left right : SPosNeu Γ P} →
    PairedSPosNeu left right → Type where
  | atom {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {q : Fin sig.nBases} (x y : StableVar Γ (.atom q)) :
      PairPosPlan R supply T D E (.atom x y)
  | inl {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases} {left right : SPosNeu Γ A}
      {h : PairedSPosNeu left right} :
      PairPosPlan R supply T D E h →
      PairPosPlan R supply T D E (PairedSPosNeu.inl (B := B) h)
  | inr {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases} {left right : SPosNeu Γ B}
      {h : PairedSPosNeu left right} :
      PairPosPlan R supply T D E h →
      PairPosPlan R supply T D E (PairedSPosNeu.inr (A := A) h)
  | inl_inr {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases}
      (left : SPosNeu Γ A) (right : SPosNeu Γ B) :
      PairPosPlan R supply T D E (PairedSPosNeu.inl_inr left right)
  | inr_inl {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases}
      (left : SPosNeu Γ B) (right : SPosNeu Γ A) :
      PairPosPlan R supply T D E (PairedSPosNeu.inr_inl left right)
  | shift {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {N : Neg sig.nBases}
      {left right : SInv Γ .empty .empty (.neg N)}
      {h : PairedNormal left right} :
      PairPlan R supply (Old := Γ) (New := .empty) T D E
        (CodePendingAssignment.empty R Δ) h →
      PairPosPlan R supply T D E (PairedSPosNeu.shift (Γ := Γ) h)

inductive PairSatPlan (R : AliasResolver sig) (supply : BatchResultSupply R) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Old New : StableCtx sig} →
    (E : CodeOriginAssignment R Δ (Old.append New)) →
    {P : Pos sig.nBases} → {left right : Sat Old New P} →
    PairedSelected left right → Type where
  | inconsistent {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig}
      {E : CodeOriginAssignment R Δ (Old.append New)} {P : Pos sig.nBases}
      (left right : SNegNeu (Old.append New) (.shift .zero)) :
      PairSatPlan R supply T D E
        (PairedSelected.inconsistent (P := P) left right)
  | done {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig}
      {E : CodeOriginAssignment R Δ (Old.append New)} {P : Pos sig.nBases}
      {left right : SPosNeu (Old.append New) P}
      {h : PairedSPosNeu left right} :
      PairPosPlan R supply T D E h →
      PairSatPlan R supply T D E (PairedSelected.done h)
  | batch {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {selected : Pending sig} {P : Pos sig.nBases}
      {obs : NonemptyBatchObs (Old.append New) selected}
      {left right : SInv (Old.append New) .empty selected (.pos P)}
      {h : PairedNormal left right}
      (B : ExactBatch R supply (E.realize D) obs)
      (X : B.Extension T)
      (body : PairPlan R supply (Old := Old.append New) (New := .empty) X.next
        (D.pushPending (supply.results obs).resolved)
        (E.rename (Pending.weakenCodeBase selected Δ))
        (CodePendingAssignment.boundBatch (supply.results obs) Δ) h) :
      PairSatPlan R supply T D E (PairedSelected.batch obs h)

inductive PairPlan (R : AliasResolver sig) (supply : BatchResultSupply R) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Old New : StableCtx sig} → {ps : Pending sig} →
    {G : Goal sig.nBases} →
    (E : CodeOriginAssignment R Δ (Old.append New)) →
    (pending : CodePendingAssignment R Δ ps) →
    {left right : SInv Old New ps G} → PairedNormal left right → Type where
  | dead {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ ps}
      {left right : SInv Old New ps G}
      {h : PairedNormal left right}
      (hdead : T.toTypedTrace.IsDead) :
      PairPlan R supply T D E pending h
  | caseSum {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {A B : Pos sig.nBases}
      {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons (.sum A B) ps)}
      {leftA rightA : SInv Old New (.cons A ps) G}
      {leftB rightB : SInv Old New (.cons B ps) G}
      {hA : PairedNormal leftA rightA} {hB : PairedNormal leftB rightB}
      (fork : SplitFork T ((pending.ref .here).realize D))
      (leftSource : ResolvedRef R A.erase)
      (rightSource : ResolvedRef R B.erase)
      (leftSource_eq : leftSource = ResolvedRef.of R fork.leftPayload)
      (rightSource_eq : rightSource = ResolvedRef.of R fork.rightPayload)
      (leftPlan : PairPlan R supply fork.leftTrace (D.snoc leftSource)
        (E.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := A.erase)))) hA)
      (rightPlan : PairPlan R supply fork.rightTrace (D.snoc rightSource)
        (E.rename (Rename.weaken (A := B.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := B.erase)))) hB) :
      PairPlan R supply T D E pending (PairedNormal.caseSum hA hB)
  | abort {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons .zero ps)} :
      PairPlan R supply T D E pending
        (PairedNormal.abort (Old := Old) (New := New) (ps := ps) (G := G))
  | storeAtom {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {q : Fin sig.nBases}
      {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons (.atom q) ps)}
      {left right : SInv Old (New.snoc (.atom q)) ps G}
      {h : PairedNormal left right} :
      PairPlan R supply (Old := Old) (New := New.snoc (.atom q)) T D
        (E.snoc (S := .atom q) (pending.ref .here)) pending.tail h →
      PairPlan R supply T D E pending (PairedNormal.storeAtom h)
  | storeShift {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {N : Neg sig.nBases}
      {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons (.shift N) ps)}
      {left right : SInv Old (New.snoc (.neg N)) ps G}
      {h : PairedNormal left right} :
      PairPlan R supply (Old := Old) (New := New.snoc (.neg N)) T D
        (E.snoc (S := .neg N) (pending.ref .here)) pending.tail h →
      PairPlan R supply T D E pending (PairedNormal.storeShift h)
  | unit {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty} :
      PairPlan R supply T D E pending
        (PairedNormal.unit (Old := Old) (New := New))
  | pair {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {A B : Neg sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {leftA rightA : SInv Old New .empty (.neg A)}
      {leftB rightB : SInv Old New .empty (.neg B)}
      {hA : PairedNormal leftA rightA} {hB : PairedNormal leftB rightB} :
      PairPlan R supply T D E pending hA →
      PairPlan R supply T D E pending hB →
      PairPlan R supply T D E pending
        (PairedNormal.pair hA hB)
  | lam {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {A : Pos sig.nBases} {B : Neg sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {left right : SInv Old New (.cons A .empty) (.neg B)}
      {h : PairedNormal left right}
      (source : ResolvedRef R A.erase)
      (body : PairPlan R supply T (D.snoc source)
        (E.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.rename (Rename.weaken (A := A.erase)))) h) :
      PairPlan R supply T D E pending
        (PairedNormal.lam h)
  | satShift {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {P : Pos sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {left right : Sat Old New P}
      {h : PairedSelected left right} :
      PairSatPlan R supply T D E h →
      PairPlan R supply T D E pending
        (PairedNormal.satShift h)
  | satPos {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {P : Pos sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {left right : Sat Old New P}
      {h : PairedSelected left right} :
      PairSatPlan R supply T D E h →
      PairPlan R supply T D E pending
        (PairedNormal.satPos h)

end

/-! ### Pair-code data -/

mutual

inductive PairPosCode (R : AliasResolver sig) (supply : BatchResultSupply R) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Γ : StableCtx sig} → (E : CodeOriginAssignment R Δ Γ) →
    {P : Pos sig.nBases} → {left right : SPosNeu Γ P} →
    PairedSPosNeu left right → Type where
  | atom {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {q : Fin sig.nBases} (x y : StableVar Γ (.atom q)) :
      PairPosCode R supply T D E (.atom x y)
  | inl {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases} {left right : SPosNeu Γ A}
      {h : PairedSPosNeu left right} :
      PairPosCode R supply T D E h →
      PairPosCode R supply T D E (PairedSPosNeu.inl (B := B) h)
  | inr {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases} {left right : SPosNeu Γ B}
      {h : PairedSPosNeu left right} :
      PairPosCode R supply T D E h →
      PairPosCode R supply T D E (PairedSPosNeu.inr (A := A) h)
  | inl_inr {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases}
      (left : SPosNeu Γ A) (right : SPosNeu Γ B) :
      PairPosCode R supply T D E (PairedSPosNeu.inl_inr left right)
  | inr_inl {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases}
      (left : SPosNeu Γ B) (right : SPosNeu Γ A) :
      PairPosCode R supply T D E (PairedSPosNeu.inr_inl left right)
  | shift {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {N : Neg sig.nBases}
      {left right : SInv Γ .empty .empty (.neg N)}
      {h : PairedNormal left right} :
      PairCode R supply (Old := Γ) (New := .empty) T D E
        (CodePendingAssignment.empty R Δ) h →
      PairPosCode R supply T D E (PairedSPosNeu.shift (Γ := Γ) h)

inductive PairSatCode (R : AliasResolver sig) (supply : BatchResultSupply R) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Old New : StableCtx sig} →
    (E : CodeOriginAssignment R Δ (Old.append New)) →
    {P : Pos sig.nBases} → {left right : Sat Old New P} →
    PairedSelected left right → Type where
  | inconsistent {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig}
      {E : CodeOriginAssignment R Δ (Old.append New)} {P : Pos sig.nBases}
      (left right : SNegNeu (Old.append New) (.shift .zero)) :
      PairSatCode R supply T D E
        (PairedSelected.inconsistent (P := P) left right)
  | done {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig}
      {E : CodeOriginAssignment R Δ (Old.append New)} {P : Pos sig.nBases}
      {left right : SPosNeu (Old.append New) P}
      {h : PairedSPosNeu left right} :
      PairPosCode R supply T D E h →
      PairSatCode R supply T D E (PairedSelected.done h)
  | batch {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {selected : Pending sig} {P : Pos sig.nBases}
      {obs : NonemptyBatchObs (Old.append New) selected}
      {left right : SInv (Old.append New) .empty selected (.pos P)}
      {h : PairedNormal left right}
      (B : ExactBatch R supply (E.realize D) obs)
      (X : B.Extension T)
      (body : PairCode R supply (Old := Old.append New) (New := .empty) X.next
        (D.pushPending (supply.results obs).resolved)
        (E.rename (Pending.weakenCodeBase selected Δ))
        (CodePendingAssignment.boundBatch (supply.results obs) Δ) h) :
      PairSatCode R supply T D E (PairedSelected.batch obs h)

inductive PairCode (R : AliasResolver sig) (supply : BatchResultSupply R) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Old New : StableCtx sig} → {ps : Pending sig} →
    {G : Goal sig.nBases} →
    (E : CodeOriginAssignment R Δ (Old.append New)) →
    (pending : CodePendingAssignment R Δ ps) →
    {left right : SInv Old New ps G} → PairedNormal left right → Type where
  | dead {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ ps}
      {left right : SInv Old New ps G}
      {h : PairedNormal left right} (hdead : T.toTypedTrace.IsDead) :
      PairCode R supply T D E pending h
  | caseSum {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {A B : Pos sig.nBases}
      {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons (.sum A B) ps)}
      {leftA rightA : SInv Old New (.cons A ps) G}
      {leftB rightB : SInv Old New (.cons B ps) G}
      {hA : PairedNormal leftA rightA} {hB : PairedNormal leftB rightB}
      (fork : SplitFork T ((pending.ref .here).realize D))
      (leftSource : ResolvedRef R A.erase)
      (rightSource : ResolvedRef R B.erase)
      (leftSource_eq : leftSource = ResolvedRef.of R fork.leftPayload)
      (rightSource_eq : rightSource = ResolvedRef.of R fork.rightPayload)
      (left : PairCode R supply fork.leftTrace (D.snoc leftSource)
        (E.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := A.erase)))) hA)
      (right : PairCode R supply fork.rightTrace (D.snoc rightSource)
        (E.rename (Rename.weaken (A := B.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := B.erase)))) hB) :
      PairCode R supply T D E pending (PairedNormal.caseSum hA hB)
  | abort {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons .zero ps)} :
      PairCode R supply T D E pending
        (PairedNormal.abort (Old := Old) (New := New) (ps := ps) (G := G))
  | storeAtom {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {q : Fin sig.nBases}
      {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons (.atom q) ps)}
      {left right : SInv Old (New.snoc (.atom q)) ps G}
      {h : PairedNormal left right} :
      PairCode R supply (Old := Old) (New := New.snoc (.atom q)) T D
        (E.snoc (S := .atom q) (pending.ref .here)) pending.tail h →
      PairCode R supply T D E pending (PairedNormal.storeAtom h)
  | storeShift {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {N : Neg sig.nBases}
      {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons (.shift N) ps)}
      {left right : SInv Old (New.snoc (.neg N)) ps G}
      {h : PairedNormal left right} :
      PairCode R supply (Old := Old) (New := New.snoc (.neg N)) T D
        (E.snoc (S := .neg N) (pending.ref .here)) pending.tail h →
      PairCode R supply T D E pending (PairedNormal.storeShift h)
  | unit {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty} :
      PairCode R supply T D E pending
        (PairedNormal.unit (Old := Old) (New := New))
  | pair {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {A B : Neg sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {leftA rightA : SInv Old New .empty (.neg A)}
      {leftB rightB : SInv Old New .empty (.neg B)}
      {hA : PairedNormal leftA rightA} {hB : PairedNormal leftB rightB} :
      PairCode R supply T D E pending hA →
      PairCode R supply T D E pending hB →
      PairCode R supply T D E pending
        (PairedNormal.pair hA hB)
  | lam {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {A : Pos sig.nBases} {B : Neg sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {left right : SInv Old New (.cons A .empty) (.neg B)}
      {h : PairedNormal left right}
      (source : ResolvedRef R A.erase)
      (body : PairCode R supply T (D.snoc source)
        (E.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.rename (Rename.weaken (A := A.erase)))) h) :
      PairCode R supply T D E pending
        (PairedNormal.lam h)
  | satShift {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {P : Pos sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {left right : Sat Old New P}
      {h : PairedSelected left right} :
      PairSatCode R supply T D E h →
      PairCode R supply T D E pending
        (PairedNormal.satShift h)
  | satPos {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {P : Pos sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {left right : Sat Old New P}
      {h : PairedSelected left right} :
      PairSatCode R supply T D E h →
      PairCode R supply T D E pending
        (PairedNormal.satPos h)

end

/-! ### Total plan realization -/

mutual

def PairPosPlan.build :
    (p : PairPosPlan R supply T D E h) → PairPosCode R supply T D E h
  | .atom x y => .atom x y
  | .inl p => .inl p.build
  | .inr p => .inr p.build
  | .inl_inr left right => .inl_inr left right
  | .inr_inl left right => .inr_inl left right
  | .shift p => .shift p.build

def PairSatPlan.build :
    (p : PairSatPlan R supply T D E h) → PairSatCode R supply T D E h
  | .inconsistent left right => .inconsistent left right
  | .done p => .done p.build
  | .batch B X body => .batch B X body.build

def PairPlan.build :
    (p : PairPlan R supply T D E pending h) →
      PairCode R supply T D E pending h
  | .dead hdead => .dead hdead
  | .caseSum fork leftSource rightSource hleft hright left right =>
      .caseSum fork leftSource rightSource hleft hright left.build right.build
  | .abort => .abort
  | .storeAtom p => .storeAtom p.build
  | .storeShift p => .storeShift p.build
  | .unit => .unit
  | .pair left right => .pair left.build right.build
  | .lam source body => .lam source body.build
  | .satShift p => .satShift p.build
  | .satPos p => .satPos p.build

end

/-! ### Resolved structural projections -/

mutual

def PairPosCode.leftProjection
    {Δ : Ctx sig} {T : ExactTraceAt R} (D : BoundOrigins R Δ)
    {Γ : StableCtx sig} (E : CodeOriginAssignment R Δ Γ)
    {P : Pos sig.nBases} {left right : SPosNeu Γ P}
    {h : PairedSPosNeu left right} :
    PairPosCode R supply T D E h → SPosCode R Δ P
  | .atom x _ => .atom (.free ((E.ref x).realize D))
  | .inl p => .inl p.leftProjection
  | .inr p => .inr p.leftProjection
  | .inl_inr left _ =>
      .inl (left.toStructuralCode supply (E.resolved D))
  | .inr_inl left _ =>
      .inr (left.toStructuralCode supply (E.resolved D))
  | .shift p => .shift p.leftProjection

def PairPosCode.rightProjection
    {Δ : Ctx sig} {T : ExactTraceAt R} (D : BoundOrigins R Δ)
    {Γ : StableCtx sig} (E : CodeOriginAssignment R Δ Γ)
    {P : Pos sig.nBases} {left right : SPosNeu Γ P}
    {h : PairedSPosNeu left right} :
    PairPosCode R supply T D E h → SPosCode R Δ P
  | .atom _ y => .atom (.free ((E.ref y).realize D))
  | .inl p => .inl p.rightProjection
  | .inr p => .inr p.rightProjection
  | .inl_inr _ right =>
      .inr (right.toStructuralCode supply (E.resolved D))
  | .inr_inl _ right =>
      .inl (right.toStructuralCode supply (E.resolved D))
  | .shift p => .shift p.rightProjection

def PairSatCode.leftProjection
    {Δ : Ctx sig} {T : ExactTraceAt R} (D : BoundOrigins R Δ)
    {Old New : StableCtx sig}
    (E : CodeOriginAssignment R Δ (Old.append New))
    {P : Pos sig.nBases} {left right : Sat Old New P}
    {h : PairedSelected left right} :
    PairSatCode R supply T D E h → SatCode R Δ P
  | .inconsistent _ _ => .inconsistent
  | .done p => .done p.leftProjection
  | .batch (obs := obs) _ _ body =>
      .batch (obs.toStructuralCode supply (E.resolved D)) body.leftProjection

def PairSatCode.rightProjection
    {Δ : Ctx sig} {T : ExactTraceAt R} (D : BoundOrigins R Δ)
    {Old New : StableCtx sig}
    (E : CodeOriginAssignment R Δ (Old.append New))
    {P : Pos sig.nBases} {left right : Sat Old New P}
    {h : PairedSelected left right} :
    PairSatCode R supply T D E h → SatCode R Δ P
  | .inconsistent _ _ => .inconsistent
  | .done p => .done p.rightProjection
  | .batch (obs := obs) _ _ body =>
      .batch (obs.toStructuralCode supply (E.resolved D)) body.rightProjection

def PairCode.leftProjection
    {Δ : Ctx sig} {T : ExactTraceAt R} (D : BoundOrigins R Δ)
    {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
    (E : CodeOriginAssignment R Δ (Old.append New))
    (pending : CodePendingAssignment R Δ ps)
    {left right : SInv Old New ps G} {h : PairedNormal left right} :
    PairCode R supply T D E pending h → BranchCode R Δ ps G
  | .dead _ => .dead
  | .caseSum _ _ _ _ _ left right =>
      .caseSum left.leftProjection right.leftProjection
  | .abort => .abort
  | .storeAtom p => .storeAtom p.leftProjection
  | .storeShift p => .storeShift p.leftProjection
  | .unit => .unit
  | .pair left right => .pair left.leftProjection right.leftProjection
  | .lam _ body => .lam body.leftProjection
  | .satShift p => .satShift p.leftProjection
  | .satPos p => .satPos p.leftProjection

def PairCode.rightProjection
    {Δ : Ctx sig} {T : ExactTraceAt R} (D : BoundOrigins R Δ)
    {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
    (E : CodeOriginAssignment R Δ (Old.append New))
    (pending : CodePendingAssignment R Δ ps)
    {left right : SInv Old New ps G} {h : PairedNormal left right} :
    PairCode R supply T D E pending h → BranchCode R Δ ps G
  | .dead _ => .dead
  | .caseSum _ _ _ _ _ left right =>
      .caseSum left.rightProjection right.rightProjection
  | .abort => .abort
  | .storeAtom p => .storeAtom p.rightProjection
  | .storeShift p => .storeShift p.rightProjection
  | .unit => .unit
  | .pair left right => .pair left.rightProjection right.rightProjection
  | .lam _ body => .lam body.rightProjection
  | .satShift p => .satShift p.rightProjection
  | .satPos p => .satPos p.rightProjection

end

/-! Projection dependencies are intrinsically typed and resolver-terminal. -/

theorem PairPosCode.leftProjection_terminal
    (c : PairPosCode R supply T D E h) (o : Origin sig)
    (ho : o ∈ c.leftProjection.freeDeps) : R.target o = none :=
  c.leftProjection.freeDeps_terminal o ho

theorem PairPosCode.rightProjection_terminal
    (c : PairPosCode R supply T D E h) (o : Origin sig)
    (ho : o ∈ c.rightProjection.freeDeps) : R.target o = none :=
  c.rightProjection.freeDeps_terminal o ho

theorem PairSatCode.leftProjection_terminal
    (c : PairSatCode R supply T D E h) (o : Origin sig)
    (ho : o ∈ c.leftProjection.freeDeps) : R.target o = none :=
  c.leftProjection.freeDeps_terminal o ho

theorem PairSatCode.rightProjection_terminal
    (c : PairSatCode R supply T D E h) (o : Origin sig)
    (ho : o ∈ c.rightProjection.freeDeps) : R.target o = none :=
  c.rightProjection.freeDeps_terminal o ho

theorem PairCode.leftProjection_terminal
    (c : PairCode R supply T D E pending h) (o : Origin sig)
    (ho : o ∈ c.leftProjection.freeDeps) : R.target o = none :=
  c.leftProjection.freeDeps_terminal o ho

theorem PairCode.rightProjection_terminal
    (c : PairCode R supply T D E pending h) (o : Origin sig)
    (ho : o ∈ c.rightProjection.freeDeps) : R.target o = none :=
  c.rightProjection.freeDeps_terminal o ho

/-- Both batch projections contain the one literal ordered observation code. -/
theorem PairSatCode.batch_literal_reused
    {Δ : Ctx sig} {T : ExactTraceAt R} (D : BoundOrigins R Δ)
    {Old New : StableCtx sig}
    (E : CodeOriginAssignment R Δ (Old.append New))
    {selected : Pending sig} {P : Pos sig.nBases}
    {obs : NonemptyBatchObs (Old.append New) selected}
    {left right : SInv (Old.append New) .empty selected (.pos P)}
    {h : PairedNormal left right}
    (B : ExactBatch R supply (E.realize D) obs) (X : B.Extension T)
    (body : PairCode R supply (Old := Old.append New) (New := .empty) X.next
      (D.pushPending (supply.results obs).resolved)
      (E.rename (Pending.weakenCodeBase selected Δ))
      (CodePendingAssignment.boundBatch (supply.results obs) Δ) h) :
    let c : PairSatCode R supply T D E (PairedSelected.batch obs h) :=
      .batch B X body
    c.leftProjection =
        .batch (obs.toStructuralCode supply (E.resolved D)) body.leftProjection ∧
      c.rightProjection =
        .batch (obs.toStructuralCode supply (E.resolved D)) body.rightProjection := by
  exact ⟨rfl, rfl⟩

/-! ### Boundary fixtures -/

namespace PairCodeFixtures

open PairTraceFixtures PairStructuralCodeFixtures ExactTraceFixtures
  PairTraceExtensionFixtures

abbrev AliasAtomCtx : StableCtx TwoGenSig :=
  ((StableCtx.empty : StableCtx TwoGenSig).snoc (.atom q0)).snoc (.atom q0)

def aliasAtomAssignment : OriginAssignment traceResolver AliasAtomCtx :=
  ((OriginAssignment.empty traceResolver).snoc (S := .atom q0)
    (ResolvedRef.of traceResolver store2)).snoc (S := .atom q0)
      (ResolvedRef.of traceResolver atom0)

theorem aliasAtomPair : PairedSPosNeu
    (SPosNeu.atom (.there .here : StableVar AliasAtomCtx (.atom q0)))
    (SPosNeu.atom (.here : StableVar AliasAtomCtx (.atom q0))) :=
  .atom _ _

def aliasAtomCode : PairPosCode traceResolver (supply traceResolver)
    (ExactTraceAt.empty traceResolver) (BoundOrigins.empty traceResolver)
    (CodeOriginAssignment.ofOrigin aliasAtomAssignment) aliasAtomPair :=
  (PairPosPlan.atom _ _).build

/-- Alias chains disappear before the two structural projections are exposed. -/
theorem aliased_atoms_resolve_equal :
    aliasAtomCode.leftProjection = aliasAtomCode.rightProjection := by
  have href : ResolvedRef.of traceResolver store2 =
      ResolvedRef.of traceResolver atom0 := by
    rw [ResolvedRef.of_eq_iff]
    unfold AliasResolver.Equivalent
    rw [traceResolver_store2, traceResolver_atom0]
  exact congrArg (fun r : ResolvedRef traceResolver Q =>
    SPosCode.atom (.free r)) href

abbrev DistinctAtomCtx : StableCtx TwoGenSig := AliasAtomCtx

def distinctAtomAssignment : OriginAssignment idR DistinctAtomCtx :=
  ((OriginAssignment.empty idR).snoc (S := .atom q0) refA).snoc
    (S := .atom q0) refB

theorem distinctAtomPair : PairedSPosNeu
    (SPosNeu.atom (.there .here : StableVar DistinctAtomCtx (.atom q0)))
    (SPosNeu.atom (.here : StableVar DistinctAtomCtx (.atom q0))) :=
  .atom _ _

def distinctAtomCode : PairPosCode idR (supply idR) emptyTrace
    (BoundOrigins.empty idR)
    (CodeOriginAssignment.ofOrigin distinctAtomAssignment) distinctAtomPair :=
  (PairPosPlan.atom _ _).build

/-- A common result type does not collapse distinct terminal sources. -/
theorem distinct_terminal_atoms_stay_distinct :
    distinctAtomCode.leftProjection ≠ distinctAtomCode.rightProjection := by
  intro h
  change SPosCode.atom (.free refA) = SPosCode.atom (.free refB) at h
  exact refA_ne_refB (CanonRef.free.inj (SPosCode.atom.inj h))

theorem oppositeTagPair : PairedSPosNeu sumLeft sumRight :=
  .inl_inr shiftedUnit shiftedUnit

def oppositeTagCode : PairPosCode idR (supply idR) emptyTrace
    (BoundOrigins.empty idR)
    (CodeOriginAssignment.ofOrigin (OriginAssignment.empty idR)) oppositeTagPair :=
  (PairPosPlan.inl_inr shiftedUnit shiftedUnit).build

theorem opposite_tags_are_live_code :
    oppositeTagCode.leftProjection ≠ oppositeTagCode.rightProjection := by
  intro h
  cases h

theorem zeroPair : PairedSelected inconsistentOlder inconsistentNewest :=
  PairedSelected.inconsistent (Old := ZeroCtx) (New := .empty)
    zeroOlder zeroNewest

def zeroCode : PairSatCode idR (supply idR) (Old := ZeroCtx) (New := .empty)
    emptyTrace
    (BoundOrigins.empty idR)
    (CodeOriginAssignment.ofOrigin zeroAssignment) zeroPair :=
  (PairSatPlan.inconsistent (Old := ZeroCtx) (New := .empty)
    zeroOlder zeroNewest).build

/-- The canonical inconsistent code is independent of the chosen zero neutral. -/
theorem inconsistent_witnesses_same_pair_code :
    zeroCode.leftProjection = .inconsistent ∧
      zeroCode.rightProjection = .inconsistent := by
  exact ⟨rfl, rfl⟩

def twoStoreBody (Γ : StableCtx TwoGenSig) :
    SInv Γ .empty TwoSelected (.pos P) :=
  .storeAtom (.storeAtom (.satPos (.done (.atom .here))))

theorem twoStorePaired (Γ : StableCtx TwoGenSig) :
    PairedNormal (twoStoreBody Γ) (twoStoreBody Γ) :=
  .storeAtom (.storeAtom (.satPos (.done (.atom .here .here))))

abbrev TwoAtomNew : StableCtx TwoGenSig :=
  ((StableCtx.empty : StableCtx TwoGenSig).snoc (.atom q0)).snoc (.atom q0)

def aliasAlignedExtension : aliasAlignedBatch.Extension
    (ExactTraceAt.empty traceResolver) where
  next := aliasAlignedBatch.toExactTrace.asAt
  steps_eq := rfl
  alignment := aliasAlignedBatch_alignment

def aliasBodyPlan : PairPlan traceResolver (aliasOccurrenceSupply traceResolver)
    (Old := AliasPairCtx) (New := .empty)
    aliasAlignedExtension.next
    ((BoundOrigins.empty traceResolver).pushPending
      ((aliasOccurrenceSupply traceResolver).results aliasBatch).resolved)
    ((CodeOriginAssignment.ofOrigin traceAliasAssignment).rename
      (TwoSelected.weakenCodeBase (.empty : Ctx TwoGenSig)))
    (CodePendingAssignment.boundBatch
      ((aliasOccurrenceSupply traceResolver).results aliasBatch)
      (.empty : Ctx TwoGenSig))
    (twoStorePaired AliasPairCtx) :=
  .storeAtom (.storeAtom
    (PairPlan.satPos (Old := AliasPairCtx) (New := TwoAtomNew)
      (PairSatPlan.done (Old := AliasPairCtx) (New := TwoAtomNew)
        (PairPosPlan.atom .here .here))))

def duplicateBatchCode : PairSatCode traceResolver
    (aliasOccurrenceSupply traceResolver) (Old := AliasPairCtx) (New := .empty)
    (ExactTraceAt.empty traceResolver)
    (BoundOrigins.empty traceResolver)
    (CodeOriginAssignment.ofOrigin traceAliasAssignment)
    (PairedSelected.batch (Old := AliasPairCtx) (New := .empty)
      aliasBatch (twoStorePaired AliasPairCtx)) :=
  (PairSatPlan.batch aliasAlignedBatch aliasAlignedExtension aliasBodyPlan).build

def outerBatchLength : SatCode R Δ P → Option Nat
  | .batch obs _ => some obs.length
  | _ => none

/-- Equal aliased keys retain two literal observation occurrences. -/
theorem duplicate_AA_pair_retains_two :
    outerBatchLength duplicateBatchCode.leftProjection = some 2 ∧
      aliasAlignedBatch.steps.length = 2 := by
  exact ⟨rfl, rfl⟩

/-- Different literal order cannot cross the paired-batch boundary. -/
theorem AB_BA_not_paired :
    ¬ PairedSelected
      (Sat.batch (Old := ObsCtx) (New := .empty) batchAB (twoStoreBody ObsCtx))
      (Sat.batch (Old := ObsCtx) (New := .empty) batchBA (twoStoreBody ObsCtx)) := by
  intro h
  have hobs : batchAB = batchBA := eq_of_heq h.batch_observations_heq
  apply batch_order_distinct
  exact congrArg (fun obs => obs.toStructuralCode (supply idR)
    (CodeOriginAssignment.ofOrigin obsAssignment)) hobs

abbrev OneSelected : Pending TwoGenSig := .cons P .empty

def fstBatch : NonemptyBatchObs ProdCtx OneSelected := .one (.fst prodNeu)
def sndBatch : NonemptyBatchObs ProdCtx OneSelected := .one (.snd prodNeu)

def oneStoreBody (Γ : StableCtx TwoGenSig) :
    SInv Γ .empty OneSelected (.pos P) :=
  .storeAtom (.satPos (.done (.atom .here)))

/-- Equal-result projections with different neutral structure are not aligned. -/
theorem fst_snd_not_paired :
    ¬ PairedSelected
      (Sat.batch (Old := ProdCtx) (New := .empty) fstBatch (oneStoreBody ProdCtx))
      (Sat.batch (Old := ProdCtx) (New := .empty) sndBatch (oneStoreBody ProdCtx)) := by
  intro h
  have hobs : fstBatch = sndBatch := eq_of_heq h.batch_observations_heq
  have hcode := congrArg (fun obs => obs.toStructuralCode (supply idR)
    (CodeOriginAssignment.ofOrigin prodAssignment)) hobs
  cases hcode

abbrev SumPending : Pending TwoGenSig := .cons (.sum P P) .empty

def sumPendingAssignment : CodePendingAssignment idR .empty SumPending :=
  .cons (.free sumRef) (CodePendingAssignment.empty idR .empty)

def emptyStableAssignment (R : AliasResolver TwoGenSig) (Δ : Ctx TwoGenSig) :
    CodeOriginAssignment R Δ (.empty : StableCtx TwoGenSig) where
  ref x := nomatch x

def splitChild : SInv (sig := TwoGenSig) .empty .empty (.cons P .empty) (.neg .one) :=
  .storeAtom .unit

theorem splitPair : PairedNormal (SInv.caseSum splitChild splitChild)
    (SInv.caseSum splitChild splitChild) :=
  .caseSum (.storeAtom .unit) (.storeAtom .unit)

def leftSplitPlan : PairPlan idR (supply idR) (Old := .empty) (New := .empty)
    siblingFork.leftTrace
    ((BoundOrigins.empty idR).snoc (ResolvedRef.of idR siblingFork.leftPayload))
    ((emptyStableAssignment idR .empty).rename (Rename.weaken (A := Q)))
    (.cons (.bound .here)
      (sumPendingAssignment.tail.rename (Rename.weaken (A := Q))))
    (PairedNormal.storeAtom PairedNormal.unit) :=
  .storeAtom .unit

def rightSplitPlan : PairPlan idR (supply idR) (Old := .empty) (New := .empty)
    siblingFork.rightTrace
    ((BoundOrigins.empty idR).snoc (ResolvedRef.of idR siblingFork.rightPayload))
    ((emptyStableAssignment idR .empty).rename (Rename.weaken (A := Q)))
    (.cons (.bound .here)
      (sumPendingAssignment.tail.rename (Rename.weaken (A := Q))))
    (PairedNormal.storeAtom PairedNormal.unit) :=
  .storeAtom .unit

def siblingPlan : PairPlan idR (supply idR) (Old := .empty) (New := .empty)
    emptyTrace (BoundOrigins.empty idR) (emptyStableAssignment idR .empty)
    sumPendingAssignment splitPair :=
  .caseSum siblingFork (ResolvedRef.of idR siblingFork.leftPayload)
    (ResolvedRef.of idR siblingFork.rightPayload) rfl rfl
    leftSplitPlan rightSplitPlan

def siblingCode := siblingPlan.build

/-- Siblings are certified under distinct path-local split traces. -/
theorem sibling_traces_are_separate :
    siblingFork.leftTrace.steps ≠ siblingFork.rightTrace.steps := by
  intro h
  have htag := congrArg (fun steps => steps.head?.bind TraceStep.splitTag?) h
  simp [siblingFork, ExactTraceAt.singleSplitL, ExactTraceAt.singleSplitR,
    TraceStep.splitTag?] at htag

end PairCodeFixtures

end Gimbal.Equality.Scherer
