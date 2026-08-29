/-
  Agreement or an aligned, path-local terminal mismatch for proof-relevant
  paired saturated codes.  Selection and model construction live above this
  layer.
-/

import Gimbal.Equality.Scherer.PairCode

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Structural agreement -/

mutual

inductive PosAgreement (R : AliasResolver sig) (supply : BatchResultSupply R) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Γ : StableCtx sig} → (E : CodeOriginAssignment R Δ Γ) →
    {P : Pos sig.nBases} → {left right : SPosNeu Γ P} →
    (h : PairedSPosNeu left right) →
    PairPosCode R supply T D E h → Type where
  | traceDead (hd : T.toTypedTrace.IsDead) : PosAgreement R supply T D E h c
  | atom (x y : StableVar Γ (.atom q))
      (heq : (E.ref x).realize D = (E.ref y).realize D) :
      PosAgreement R supply T D E (.atom x y) (.atom x y)
  | inl (a : PosAgreement R supply T D E h c) :
      PosAgreement R supply T D E (PairedSPosNeu.inl (B := B) h) (.inl c)
  | inr (a : PosAgreement R supply T D E h c) :
      PosAgreement R supply T D E (PairedSPosNeu.inr (A := A) h) (.inr c)
  | shift {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {N : Neg sig.nBases}
      {left right : SInv Γ .empty .empty (.neg N)}
      {h : PairedNormal left right}
      {c : PairCode R supply (Old := Γ) (New := .empty) T D E
        (CodePendingAssignment.empty R Δ) h}
      (a : PairAgreement R supply (Old := Γ) (New := .empty) T D E
        (CodePendingAssignment.empty R Δ) h c) :
      PosAgreement R supply T D E (PairedSPosNeu.shift (Γ := Γ) h)
        (PairPosCode.shift (R := R) (supply := supply) (T := T) (D := D)
          (E := E) (Γ := Γ) (N := N) c)

inductive SatAgreement (R : AliasResolver sig) (supply : BatchResultSupply R) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Old New : StableCtx sig} →
    (E : CodeOriginAssignment R Δ (Old.append New)) →
    {P : Pos sig.nBases} → {left right : Sat Old New P} →
    (h : PairedSelected left right) →
    PairSatCode R supply T D E h → Type where
  | traceDead (hd : T.toTypedTrace.IsDead) : SatAgreement R supply T D E h c
  | inconsistent {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig}
      {E : CodeOriginAssignment R Δ (Old.append New)} {P : Pos sig.nBases}
      (left right : SNegNeu (Old.append New) (.shift .zero)) :
      SatAgreement R supply T D E
        (PairedSelected.inconsistent (P := P) left right)
        (.inconsistent left right)
  | done (a : PosAgreement R supply T D E h c) :
      SatAgreement R supply T D E (PairedSelected.done h) (.done c)
  | batch {Old New : StableCtx sig} {selected : Pending sig}
      {P : Pos sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {obs : NonemptyBatchObs (Old.append New) selected}
      {left right : SInv (Old.append New) .empty selected (.pos P)}
      {h : PairedNormal left right}
      (B : ExactBatch R supply (E.realize D) obs) (X : B.Extension T)
      {c : PairCode R supply (Old := Old.append New) (New := .empty) X.next
        (D.pushPending (supply.results obs).resolved)
        (E.rename (Pending.weakenCodeBase selected Δ))
        (CodePendingAssignment.boundBatch (supply.results obs) Δ) h}
      (a : PairAgreement R supply (Old := Old.append New) (New := .empty)
        (left := left) (right := right) X.next
        (D.pushPending (supply.results obs).resolved)
        (E.rename (Pending.weakenCodeBase selected Δ))
        (CodePendingAssignment.boundBatch (supply.results obs) Δ) h c) :
      SatAgreement R supply T D E (PairedSelected.batch obs h) (.batch B X c)

inductive PairAgreement (R : AliasResolver sig) (supply : BatchResultSupply R) :
    {Δ : Ctx sig} → (T : ExactTraceAt R) → (D : BoundOrigins R Δ) →
    {Old New : StableCtx sig} → {ps : Pending sig} → {G : Goal sig.nBases} →
    (E : CodeOriginAssignment R Δ (Old.append New)) →
    (pending : CodePendingAssignment R Δ ps) →
    {left right : SInv Old New ps G} → (h : PairedNormal left right) →
    PairCode R supply T D E pending h → Type where
  | traceDead (hd : T.toTypedTrace.IsDead) : PairAgreement R supply T D E pending h c
  | dead (hd : T.toTypedTrace.IsDead) : PairAgreement R supply T D E pending h (.dead hd)
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
      (hl : leftSource = ResolvedRef.of R fork.leftPayload)
      (hr : rightSource = ResolvedRef.of R fork.rightPayload)
      {cA : PairCode R supply fork.leftTrace (D.snoc leftSource)
        (E.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := A.erase)))) hA}
      {cB : PairCode R supply fork.rightTrace (D.snoc rightSource)
        (E.rename (Rename.weaken (A := B.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := B.erase)))) hB}
      (left : PairAgreement R supply fork.leftTrace (D.snoc leftSource)
        (E.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := A.erase)))) hA cA)
      (right : PairAgreement R supply fork.rightTrace (D.snoc rightSource)
        (E.rename (Rename.weaken (A := B.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := B.erase)))) hB cB) :
      PairAgreement R supply T D E pending (PairedNormal.caseSum hA hB)
        (.caseSum fork leftSource rightSource hl hr cA cB)
  | abort {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons .zero ps)} :
      PairAgreement R supply T D E pending
      (PairedNormal.abort (Old := Old) (New := New) (ps := ps) (G := G)) .abort
  | storeAtom {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {q : Fin sig.nBases}
      {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons (.atom q) ps)}
      {left right : SInv Old (New.snoc (.atom q)) ps G}
      {h : PairedNormal left right}
      {c : PairCode R supply (Old := Old) (New := New.snoc (.atom q)) T D
        (E.snoc (S := .atom q) (pending.ref .here)) pending.tail h}
      (a : PairAgreement R supply (Old := Old) (New := New.snoc (.atom q)) T D
      (E.snoc (S := .atom q) (pending.ref .here)) pending.tail h c) :
      PairAgreement R supply T D E pending (PairedNormal.storeAtom h) (.storeAtom c)
  | storeShift {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {N : Neg sig.nBases}
      {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons (.shift N) ps)}
      {left right : SInv Old (New.snoc (.neg N)) ps G}
      {h : PairedNormal left right}
      {c : PairCode R supply (Old := Old) (New := New.snoc (.neg N)) T D
        (E.snoc (S := .neg N) (pending.ref .here)) pending.tail h}
      (a : PairAgreement R supply (Old := Old) (New := New.snoc (.neg N)) T D
      (E.snoc (S := .neg N) (pending.ref .here)) pending.tail h c) :
      PairAgreement R supply T D E pending (PairedNormal.storeShift h) (.storeShift c)
  | unit {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty} :
      PairAgreement R supply T D E pending
      (PairedNormal.unit (Old := Old) (New := New)) .unit
  | pair (a : PairAgreement R supply T D E pending hA cA)
      (b : PairAgreement R supply T D E pending hB cB) :
      PairAgreement R supply T D E pending (PairedNormal.pair hA hB) (.pair cA cB)
  | lam {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {A : Pos sig.nBases} {B : Neg sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {left right : SInv Old New (.cons A .empty) (.neg B)}
      {h : PairedNormal left right}
      (source : ResolvedRef R A.erase)
      {c : PairCode R supply T (D.snoc source)
        (E.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.rename (Rename.weaken (A := A.erase)))) h}
      (a : PairAgreement R supply T (D.snoc source)
        (E.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.rename (Rename.weaken (A := A.erase)))) h c) :
      PairAgreement R supply T D E pending (PairedNormal.lam h) (.lam source c)
  | satShift (a : SatAgreement R supply T D E h c) :
      PairAgreement R supply T D E pending (PairedNormal.satShift h) (.satShift c)
  | satPos (a : SatAgreement R supply T D E h c) :
      PairAgreement R supply T D E pending (PairedNormal.satPos h) (.satPos c)

end

/-! ### Separate aligned paths -/

inductive PairSide | left | right

mutual

inductive PosSidePath (R : AliasResolver sig) (supply : BatchResultSupply R) :
    (side : PairSide) →
    {Δ : Ctx sig} → {T : ExactTraceAt R} → {D : BoundOrigins R Δ} →
    {Γ : StableCtx sig} → {E : CodeOriginAssignment R Δ Γ} →
    {P : Pos sig.nBases} → {left right : SPosNeu Γ P} →
    {h : PairedSPosNeu left right} → PairPosCode R supply T D E h →
    (U : ExactTraceAt R) → TypedTrace.ResolvedSource sig → Type where
  | atomLeft {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {q : Fin sig.nBases} (x y : StableVar Γ (.atom q)) :
      PosSidePath R supply .left
        (PairPosCode.atom (R := R) (supply := supply) (T := T) (D := D)
          (E := E) x y) T
        (.atom q ((E.ref x).realize D).origin)
  | atomRight {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {q : Fin sig.nBases} (x y : StableVar Γ (.atom q)) :
      PosSidePath R supply .right
        (PairPosCode.atom (R := R) (supply := supply) (T := T) (D := D)
          (E := E) x y) T
        (.atom q ((E.ref y).realize D).origin)
  | inl (p : PosSidePath R supply side c U s) :
      PosSidePath R supply side (.inl c) U s
  | inr (p : PosSidePath R supply side c U s) :
      PosSidePath R supply side (.inr c) U s
  | inl_inr_left {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases} (x : SPosNeu Γ A) (y : SPosNeu Γ B) :
      PosSidePath R supply .left
        (PairPosCode.inl_inr (R := R) (supply := supply) (T := T) (D := D)
          (E := E) x y) T
        (.tag (.coprod A.erase B.erase) false)
  | inl_inr_right {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases} (x : SPosNeu Γ A) (y : SPosNeu Γ B) :
      PosSidePath R supply .right
        (PairPosCode.inl_inr (R := R) (supply := supply) (T := T) (D := D)
          (E := E) x y) T
        (.tag (.coprod A.erase B.erase) true)
  | inr_inl_left {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases} (x : SPosNeu Γ B) (y : SPosNeu Γ A) :
      PosSidePath R supply .left
        (PairPosCode.inr_inl (R := R) (supply := supply) (T := T) (D := D)
          (E := E) x y) T
        (.tag (.coprod A.erase B.erase) true)
  | inr_inl_right {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
      {A B : Pos sig.nBases} (x : SPosNeu Γ B) (y : SPosNeu Γ A) :
      PosSidePath R supply .right
        (PairPosCode.inr_inl (R := R) (supply := supply) (T := T) (D := D)
          (E := E) x y) T
        (.tag (.coprod A.erase B.erase) false)
  | shift (p : SidePath R supply side c U s) :
      PosSidePath R supply side (.shift c) U s

inductive SatSidePath (R : AliasResolver sig) (supply : BatchResultSupply R) :
    (side : PairSide) →
    {Δ : Ctx sig} → {T : ExactTraceAt R} → {D : BoundOrigins R Δ} →
    {Old New : StableCtx sig} →
    {E : CodeOriginAssignment R Δ (Old.append New)} →
    {P : Pos sig.nBases} → {left right : Sat Old New P} →
    {h : PairedSelected left right} → PairSatCode R supply T D E h →
    (U : ExactTraceAt R) → TypedTrace.ResolvedSource sig → Type where
  | done (p : PosSidePath R supply side c U s) :
      SatSidePath R supply side (.done c) U s
  | batch {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {selected : Pending sig}
      {P : Pos sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {obs : NonemptyBatchObs (Old.append New) selected}
      {left right : SInv (Old.append New) .empty selected (.pos P)}
      {h : PairedNormal left right}
      (B : ExactBatch R supply (E.realize D) obs) (X : B.Extension T)
      {c : PairCode R supply (Old := Old.append New) (New := .empty) X.next
        (D.pushPending (supply.results obs).resolved)
        (E.rename (Pending.weakenCodeBase selected Δ))
        (CodePendingAssignment.boundBatch (supply.results obs) Δ) h}
      {U : ExactTraceAt R} {s : TypedTrace.ResolvedSource sig}
      (p : SidePath R supply side c U s) :
      SatSidePath R supply side (.batch B X c) U s

inductive SidePath (R : AliasResolver sig) (supply : BatchResultSupply R) :
    (side : PairSide) →
    {Δ : Ctx sig} → {T : ExactTraceAt R} → {D : BoundOrigins R Δ} →
    {Old New : StableCtx sig} → {ps : Pending sig} → {G : Goal sig.nBases} →
    {E : CodeOriginAssignment R Δ (Old.append New)} →
    {pending : CodePendingAssignment R Δ ps} →
    {left right : SInv Old New ps G} → {h : PairedNormal left right} →
    PairCode R supply T D E pending h →
    (U : ExactTraceAt R) → TypedTrace.ResolvedSource sig → Type where
  | caseLeft {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {A B : Pos sig.nBases}
      {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons (.sum A B) ps)}
      {leftA rightA : SInv Old New (.cons A ps) G}
      {leftB rightB : SInv Old New (.cons B ps) G}
      {hA : PairedNormal leftA rightA} {hB : PairedNormal leftB rightB}
      (fork : SplitFork T ((pending.ref .here).realize D))
      (leftSource : ResolvedRef R A.erase) (rightSource : ResolvedRef R B.erase)
      (hl : leftSource = ResolvedRef.of R fork.leftPayload)
      (hr : rightSource = ResolvedRef.of R fork.rightPayload)
      {c : PairCode R supply fork.leftTrace (D.snoc leftSource)
        (E.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := A.erase)))) hA}
      (cR : PairCode R supply fork.rightTrace (D.snoc rightSource)
        (E.rename (Rename.weaken (A := B.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := B.erase)))) hB)
      {U : ExactTraceAt R} {s : TypedTrace.ResolvedSource sig}
      (p : SidePath R supply side c U s) :
      SidePath R supply side (.caseSum fork leftSource rightSource hl hr c cR) U s
  | caseRight {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {A B : Pos sig.nBases}
      {ps : Pending sig} {G : Goal sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ (.cons (.sum A B) ps)}
      {leftA rightA : SInv Old New (.cons A ps) G}
      {leftB rightB : SInv Old New (.cons B ps) G}
      {hA : PairedNormal leftA rightA} {hB : PairedNormal leftB rightB}
      (fork : SplitFork T ((pending.ref .here).realize D))
      (leftSource : ResolvedRef R A.erase) (rightSource : ResolvedRef R B.erase)
      (hl : leftSource = ResolvedRef.of R fork.leftPayload)
      (hr : rightSource = ResolvedRef.of R fork.rightPayload)
      (cL : PairCode R supply fork.leftTrace (D.snoc leftSource)
        (E.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := A.erase)))) hA)
      {c : PairCode R supply fork.rightTrace (D.snoc rightSource)
        (E.rename (Rename.weaken (A := B.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.tail.rename (Rename.weaken (A := B.erase)))) hB}
      {U : ExactTraceAt R} {s : TypedTrace.ResolvedSource sig}
      (p : SidePath R supply side c U s) :
      SidePath R supply side (.caseSum fork leftSource rightSource hl hr cL c) U s
  | storeAtom (p : SidePath R supply side c U s) :
      SidePath R supply side (.storeAtom c) U s
  | storeShift (p : SidePath R supply side c U s) :
      SidePath R supply side (.storeShift c) U s
  | pairLeft (p : SidePath R supply side c U s) :
      SidePath R supply side (.pair c cR) U s
  | pairRight (p : SidePath R supply side c U s) :
      SidePath R supply side (.pair cL c) U s
  | lam {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {A : Pos sig.nBases} {B : Neg sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {left right : SInv Old New (.cons A .empty) (.neg B)}
      {h : PairedNormal left right} (source : ResolvedRef R A.erase)
      {c : PairCode R supply T (D.snoc source)
        (E.rename (Rename.weaken (A := A.erase)))
        (CodePendingAssignment.cons (.bound .here)
          (pending.rename (Rename.weaken (A := A.erase)))) h}
      {U : ExactTraceAt R} {s : TypedTrace.ResolvedSource sig}
      (p : SidePath R supply side c U s) :
      SidePath R supply side (.lam source c) U s
  | satShift {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {P : Pos sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {left right : Sat Old New P} {h : PairedSelected left right}
      {c : PairSatCode R supply T D E h}
      {U : ExactTraceAt R} {s : TypedTrace.ResolvedSource sig}
      (p : SatSidePath R supply side c U s) :
      SidePath R supply side
        (PairCode.satShift (pending := pending) c) U s
  | satPos {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
      {Old New : StableCtx sig} {P : Pos sig.nBases}
      {E : CodeOriginAssignment R Δ (Old.append New)}
      {pending : CodePendingAssignment R Δ .empty}
      {left right : Sat Old New P} {h : PairedSelected left right}
      {c : PairSatCode R supply T D E h}
      {U : ExactTraceAt R} {s : TypedTrace.ResolvedSource sig}
      (p : SatSidePath R supply side c U s) :
      SidePath R supply side
        (PairCode.satPos (pending := pending) c) U s

end

structure PosBiPath {sig : Signature} {R : AliasResolver sig}
    {supply : BatchResultSupply R}
    {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
    {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
    {P : Pos sig.nBases} {leftTerm rightTerm : SPosNeu Γ P}
    {h : PairedSPosNeu leftTerm rightTerm}
    (c : PairPosCode R supply T D E h)
    (U : ExactTraceAt R) (left right : TypedTrace.ResolvedSource sig) where
  leftPath : PosSidePath R supply .left c U left
  rightPath : PosSidePath R supply .right c U right

structure SatBiPath {sig : Signature} {R : AliasResolver sig}
    {supply : BatchResultSupply R}
    {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
    {Old New : StableCtx sig}
    {E : CodeOriginAssignment R Δ (Old.append New)}
    {P : Pos sig.nBases} {leftTerm rightTerm : Sat Old New P}
    {h : PairedSelected leftTerm rightTerm}
    (c : PairSatCode R supply T D E h)
    (U : ExactTraceAt R) (left right : TypedTrace.ResolvedSource sig) where
  leftPath : SatSidePath R supply .left c U left
  rightPath : SatSidePath R supply .right c U right

structure BiPath {sig : Signature} {R : AliasResolver sig}
    {supply : BatchResultSupply R}
    {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
    {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
    {E : CodeOriginAssignment R Δ (Old.append New)}
    {pending : CodePendingAssignment R Δ ps}
    {leftTerm rightTerm : SInv Old New ps G}
    {h : PairedNormal leftTerm rightTerm}
    (c : PairCode R supply T D E pending h)
    (U : ExactTraceAt R) (left right : TypedTrace.ResolvedSource sig) where
  leftPath : SidePath R supply .left c U left
  rightPath : SidePath R supply .right c U right

structure PosAlignedMismatch {sig : Signature} {R : AliasResolver sig}
    {supply : BatchResultSupply R}
    {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
    {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
    {P : Pos sig.nBases} {leftTerm rightTerm : SPosNeu Γ P}
    {h : PairedSPosNeu leftTerm rightTerm}
    (c : PairPosCode R supply T D E h) where
  trace : ExactTraceAt R
  leftSource : TypedTrace.ResolvedSource sig
  rightSource : TypedTrace.ResolvedSource sig
  path : PosBiPath c trace leftSource rightSource
  live : trace.toTypedTrace.IsLive
  apart : TypedTrace.ResolvedSourceApart trace.toTypedTrace leftSource rightSource

structure SatAlignedMismatch {sig : Signature} {R : AliasResolver sig}
    {supply : BatchResultSupply R}
    {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
    {Old New : StableCtx sig}
    {E : CodeOriginAssignment R Δ (Old.append New)}
    {P : Pos sig.nBases} {leftTerm rightTerm : Sat Old New P}
    {h : PairedSelected leftTerm rightTerm}
    (c : PairSatCode R supply T D E h) where
  trace : ExactTraceAt R
  leftSource : TypedTrace.ResolvedSource sig
  rightSource : TypedTrace.ResolvedSource sig
  path : SatBiPath c trace leftSource rightSource
  live : trace.toTypedTrace.IsLive
  apart : TypedTrace.ResolvedSourceApart trace.toTypedTrace leftSource rightSource

structure AlignedMismatch {sig : Signature} {R : AliasResolver sig}
    {supply : BatchResultSupply R}
    {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
    {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
    {E : CodeOriginAssignment R Δ (Old.append New)}
    {pending : CodePendingAssignment R Δ ps}
    {leftTerm rightTerm : SInv Old New ps G}
    {h : PairedNormal leftTerm rightTerm}
    (c : PairCode R supply T D E pending h) where
  trace : ExactTraceAt R
  leftSource : TypedTrace.ResolvedSource sig
  rightSource : TypedTrace.ResolvedSource sig
  path : BiPath c trace leftSource rightSource
  live : trace.toTypedTrace.IsLive
  apart : TypedTrace.ResolvedSourceApart trace.toTypedTrace leftSource rightSource

/-! ### Total structural comparison -/

theorem ResolvedRef.resolve_ne_of_ne {R : AliasResolver sig}
    {A : Object sig.nBases} {x y : ResolvedRef R A} (h : x ≠ y) :
    R.resolve x.origin.raw ≠ R.resolve y.origin.raw := by
  rw [R.resolve_eq_self_of_target_eq_none x.terminal,
    R.resolve_eq_self_of_target_eq_none y.terminal]
  intro hraw
  apply h
  apply ResolvedRef.ext
  apply TypedOrigin.ext
  exact hraw

noncomputable def compare
    {R : AliasResolver sig} {supply : BatchResultSupply R}
    {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
    {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
    {E : CodeOriginAssignment R Δ (Old.append New)}
    {pending : CodePendingAssignment R Δ ps}
    {left right : SInv Old New ps G} {h : PairedNormal left right}
    (c : PairCode R supply T D E pending h) :
    PairAgreement R supply T D E pending h c ⊕ AlignedMismatch c := by
  classical
  exact PairCode.rec (R := R) (supply := supply)
    (motive_1 := fun {Δ} T D {Γ} E {P left right} h c =>
      PosAgreement R supply T D E h c ⊕ PosAlignedMismatch c)
    (motive_2 := fun {Δ} T D {Old New} E {P left right} h c =>
      SatAgreement R supply T D E h c ⊕ SatAlignedMismatch c)
    (motive_3 := fun {Δ} T D {Old New ps G} E pending
        {left right} h c =>
      PairAgreement R supply T D E pending h c ⊕ AlignedMismatch c)
    (fun {Δ T D Γ E q} x y => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      ·
        by_cases heq : (E.ref x).realize D = (E.ref y).realize D
        · exact .inl (.atom x y heq)
        · exact .inr {
            trace := T
            leftSource := .atom _ ((E.ref x).realize D).origin
            rightSource := .atom _ ((E.ref y).realize D).origin
            path := ⟨.atomLeft x y, .atomRight x y⟩
            live := hd
            apart := .atom (ResolvedRef.resolve_ne_of_ne heq) })
    (fun {Δ T D Γ E A B left right h} c ih => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact match ih with
        | .inl a => .inl (.inl a)
        | .inr m => .inr {
            trace := m.trace
            leftSource := m.leftSource
            rightSource := m.rightSource
            path := ⟨.inl m.path.leftPath, .inl m.path.rightPath⟩
            live := m.live
            apart := m.apart })
    (fun {Δ T D Γ E A B left right h} c ih => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact match ih with
        | .inl a => .inl (.inr a)
        | .inr m => .inr {
            trace := m.trace
            leftSource := m.leftSource
            rightSource := m.rightSource
            path := ⟨.inr m.path.leftPath, .inr m.path.rightPath⟩
            live := m.live
            apart := m.apart })
    (fun {Δ T D Γ E A B} x y => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact .inr {
          trace := T
          leftSource := .tag _ false
          rightSource := .tag _ true
          path := ⟨.inl_inr_left x y, .inl_inr_right x y⟩
          live := hd
          apart := .tag (by decide) })
    (fun {Δ T D Γ E A B} x y => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact .inr {
          trace := T
          leftSource := .tag _ true
          rightSource := .tag _ false
          path := ⟨.inr_inl_left x y, .inr_inl_right x y⟩
          live := hd
          apart := .tag (by decide) })
    (fun {Δ T D Γ E N left right h} c ih => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact match ih with
        | .inl a => .inl (.shift a)
        | .inr m => .inr {
            trace := m.trace
            leftSource := m.leftSource
            rightSource := m.rightSource
            path := ⟨.shift m.path.leftPath, .shift m.path.rightPath⟩
            live := m.live
            apart := m.apart })
    (fun {Δ T D Old New E P} left right => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact .inl (.inconsistent left right))
    (fun {Δ T D Old New E P left right h} c ih => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact match ih with
        | .inl a => .inl (.done a)
        | .inr m => .inr {
            trace := m.trace
            leftSource := m.leftSource
            rightSource := m.rightSource
            path := ⟨.done m.path.leftPath, .done m.path.rightPath⟩
            live := m.live
            apart := m.apart })
    (fun {Δ T D Old New E selected P obs left right h} B X c ih => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact match ih with
        | .inl a => .inl (.batch B X a)
        | .inr m => .inr {
            trace := m.trace
            leftSource := m.leftSource
            rightSource := m.rightSource
            path := ⟨.batch B X m.path.leftPath, .batch B X m.path.rightPath⟩
            live := m.live
            apart := m.apart })
    (fun hdead => .inl (.dead hdead))
    (fun {Δ T D Old New A B ps G E pending leftA rightA leftB rightB hA hB}
        fork leftSource rightSource hl hr cL cR ihL ihR => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact match ihL with
        | .inr m => .inr {
            trace := m.trace
            leftSource := m.leftSource
            rightSource := m.rightSource
            path := ⟨.caseLeft fork leftSource rightSource hl hr cR m.path.leftPath,
              .caseLeft fork leftSource rightSource hl hr cR m.path.rightPath⟩
            live := m.live
            apart := m.apart }
        | .inl aL => match ihR with
          | .inl aR => .inl (.caseSum fork leftSource rightSource hl hr aL aR)
          | .inr m => .inr {
              trace := m.trace
              leftSource := m.leftSource
              rightSource := m.rightSource
              path := ⟨.caseRight fork leftSource rightSource hl hr cL m.path.leftPath,
                .caseRight fork leftSource rightSource hl hr cL m.path.rightPath⟩
              live := m.live
              apart := m.apart })
    (fun {Δ T D Old New ps G E pending} => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact .inl .abort)
    (fun {Δ T D Old New q ps G E pending left right h} c ih => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact match ih with
        | .inl a => .inl (.storeAtom a)
        | .inr m => .inr {
            trace := m.trace
            leftSource := m.leftSource
            rightSource := m.rightSource
            path := ⟨.storeAtom m.path.leftPath, .storeAtom m.path.rightPath⟩
            live := m.live
            apart := m.apart })
    (fun {Δ T D Old New N ps G E pending left right h} c ih => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact match ih with
        | .inl a => .inl (.storeShift a)
        | .inr m => .inr {
            trace := m.trace
            leftSource := m.leftSource
            rightSource := m.rightSource
            path := ⟨.storeShift m.path.leftPath, .storeShift m.path.rightPath⟩
            live := m.live
            apart := m.apart })
    (fun {Δ T D Old New E pending} => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact .inl .unit)
    (fun {Δ T D Old New A B E pending leftA rightA leftB rightB hA hB}
        cL cR ihL ihR => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact match ihL with
        | .inr m => .inr {
            trace := m.trace
            leftSource := m.leftSource
            rightSource := m.rightSource
            path := ⟨.pairLeft (cR := cR) m.path.leftPath,
              .pairLeft (cR := cR) m.path.rightPath⟩
            live := m.live
            apart := m.apart }
        | .inl aL => match ihR with
          | .inl aR => .inl (.pair aL aR)
          | .inr m => .inr {
              trace := m.trace
              leftSource := m.leftSource
              rightSource := m.rightSource
              path := ⟨.pairRight (cL := cL) m.path.leftPath,
                .pairRight (cL := cL) m.path.rightPath⟩
              live := m.live
              apart := m.apart })
    (fun {Δ T D Old New A B E pending left right h} source c ih => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact match ih with
        | .inl a => .inl (.lam source a)
        | .inr m => .inr {
            trace := m.trace
            leftSource := m.leftSource
            rightSource := m.rightSource
            path := ⟨.lam source m.path.leftPath, .lam source m.path.rightPath⟩
            live := m.live
            apart := m.apart })
    (fun {Δ T D Old New P E pending left right h} c ih => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact match ih with
        | .inl a => .inl (.satShift a)
        | .inr m => .inr {
            trace := m.trace
            leftSource := m.leftSource
            rightSource := m.rightSource
            path := ⟨.satShift m.path.leftPath, .satShift m.path.rightPath⟩
            live := m.live
            apart := m.apart })
    (fun {Δ T D Old New P E pending left right h} c ih => by
      by_cases hd : T.toTypedTrace.IsDead
      · exact .inl (.traceDead hd)
      · exact match ih with
        | .inl a => .inl (.satPos a)
        | .inr m => .inr {
            trace := m.trace
            leftSource := m.leftSource
            rightSource := m.rightSource
            path := ⟨.satPos m.path.leftPath, .satPos m.path.rightPath⟩
            live := m.live
            apart := m.apart })
    c

/-- Positive comparison is the same mutual fold viewed through `satPos/done`. -/
noncomputable def comparePos
    {R : AliasResolver sig} {supply : BatchResultSupply R}
    {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
    {Γ : StableCtx sig} {E : CodeOriginAssignment R Δ Γ}
    {P : Pos sig.nBases} {left right : SPosNeu Γ P}
    {h : PairedSPosNeu left right}
    (c : PairPosCode R supply T D E h) :
    PosAgreement R supply T D E h c ⊕ PosAlignedMismatch c := by
  cases hout : compare
      (PairCode.satPos (R := R) (supply := supply)
        (pending := CodePendingAssignment.empty R Δ)
        (PairSatCode.done (R := R) (supply := supply) (T := T)
          (D := D) (Old := Γ) (New := .empty) (E := E) c)) with
  | inl a =>
      cases a with
      | traceDead hd => exact .inl (.traceDead hd)
      | satPos a =>
          cases a with
          | traceDead hd => exact .inl (.traceDead hd)
          | done a => exact .inl a
  | inr m =>
      cases hl : m.path.leftPath with
      | satPos lp =>
          cases hl' : lp with
          | done lp' =>
          cases hr : m.path.rightPath with
          | satPos rp =>
            cases hr' : rp with
            | done rp' =>
              exact .inr {
                trace := m.trace
                leftSource := m.leftSource
                rightSource := m.rightSource
                path := ⟨lp', rp'⟩
                live := m.live
                apart := m.apart }

/-- Saturated comparison is the same mutual fold viewed through `satPos`. -/
noncomputable def compareSat
    {R : AliasResolver sig} {supply : BatchResultSupply R}
    {Δ : Ctx sig} {T : ExactTraceAt R} {D : BoundOrigins R Δ}
    {Old New : StableCtx sig}
    {E : CodeOriginAssignment R Δ (Old.append New)}
    {P : Pos sig.nBases} {left right : Sat Old New P}
    {h : PairedSelected left right}
    (c : PairSatCode R supply T D E h) :
    SatAgreement R supply T D E h c ⊕ SatAlignedMismatch c := by
  cases hout : compare
      (PairCode.satPos (R := R) (supply := supply)
        (pending := CodePendingAssignment.empty R Δ) c) with
  | inl a =>
      cases a with
      | traceDead hd => exact .inl (.traceDead hd)
      | satPos a => exact .inl a
  | inr m =>
      cases hl : m.path.leftPath with
      | satPos lp =>
          cases hr : m.path.rightPath with
          | satPos rp =>
              exact .inr {
                trace := m.trace
                leftSource := m.leftSource
                rightSource := m.rightSource
                path := ⟨lp, rp⟩
                live := m.live
                apart := m.apart }

/-! ### Adversarial boundary fixtures -/

namespace PairMismatchFixtures

open PairTraceFixtures PairStructuralCodeFixtures ExactTraceFixtures
  PairTraceExtensionFixtures PairCodeFixtures

theorem empty_live (R : AliasResolver sig) :
    (ExactTraceAt.empty R).toTypedTrace.IsLive := by
  rintro ⟨s, hs, t, ht, rest⟩
  simp [ExactTraceAt.empty] at hs

def aliasAtomsAgreement :
    PosAgreement traceResolver (supply traceResolver)
      (ExactTraceAt.empty traceResolver) (BoundOrigins.empty traceResolver)
      (CodeOriginAssignment.ofOrigin aliasAtomAssignment)
      aliasAtomPair aliasAtomCode := by
  apply PosAgreement.atom
  change ResolvedRef.of traceResolver store2 =
    ResolvedRef.of traceResolver atom0
  rw [ResolvedRef.of_eq_iff]
  unfold AliasResolver.Equivalent
  rw [traceResolver_store2, traceResolver_atom0]

def distinctAtomsMismatch : PosAlignedMismatch distinctAtomCode where
  trace := emptyTrace
  leftSource := .atom q0 refA.origin
  rightSource := .atom q0 refB.origin
  path := ⟨.atomLeft _ _, .atomRight _ _⟩
  live := empty_live idR
  apart := .atom (ResolvedRef.resolve_ne_of_ne refA_ne_refB)

def oppositeTagsMismatch : PosAlignedMismatch oppositeTagCode where
  trace := emptyTrace
  leftSource := .tag (.coprod
    ((.shift .one : Pos TwoGenSig.nBases).erase)
    ((.shift .one : Pos TwoGenSig.nBases).erase)) false
  rightSource := .tag (.coprod
    ((.shift .one : Pos TwoGenSig.nBases).erase)
    ((.shift .one : Pos TwoGenSig.nBases).erase)) true
  path := ⟨.inl_inr_left shiftedUnit shiftedUnit,
    .inl_inr_right shiftedUnit shiftedUnit⟩
  live := empty_live idR
  apart := .tag (by decide)

def inconsistentWitnessesAgreement :
    SatAgreement (Old := ZeroCtx) (New := .empty)
      idR (supply idR) emptyTrace (BoundOrigins.empty idR)
      (CodeOriginAssignment.ofOrigin zeroAssignment) zeroPair zeroCode :=
  SatAgreement.inconsistent (R := idR) (supply := supply idR)
    (T := emptyTrace) (D := BoundOrigins.empty idR)
    (Old := ZeroCtx) (New := .empty)
    (E := CodeOriginAssignment.ofOrigin zeroAssignment) zeroOlder zeroNewest

noncomputable def duplicateBatchOutcome := compareSat duplicateBatchCode

theorem duplicate_batch_is_compared_without_collapse :
    outerBatchLength duplicateBatchCode.leftProjection = some 2 ∧
      aliasAlignedBatch.steps.length = 2 :=
  duplicate_AA_pair_retains_two

noncomputable def siblingOutcome := compare siblingCode

theorem sibling_paths_remain_separate :
    siblingFork.leftTrace.steps ≠ siblingFork.rightTrace.steps :=
  sibling_traces_are_separate

/-- These witnesses are structural.  `AlignedMismatch` does not yet contain
the recursive `ArgumentsApart`/atom-capacity invariant needed for higher-order
finite separation.  Nor does arbitrary `PairCode` certify strict inconsistency
priority or context reachability; that semantic boundary belongs to the later
selector certificate. -/
theorem structural_only_boundary :
    Nonempty (PosAlignedMismatch distinctAtomCode) ∧
      Nonempty (PosAlignedMismatch oppositeTagCode) :=
  ⟨⟨distinctAtomsMismatch⟩, ⟨oppositeTagsMismatch⟩⟩

theorem unaligned_batches_rejected :
    (¬ PairedSelected
      (Sat.batch (Old := ObsCtx) (New := .empty) batchAB (twoStoreBody ObsCtx))
      (Sat.batch (Old := ObsCtx) (New := .empty) batchBA (twoStoreBody ObsCtx))) ∧
    (¬ PairedSelected
      (Sat.batch (Old := ProdCtx) (New := .empty) fstBatch (oneStoreBody ProdCtx))
      (Sat.batch (Old := ProdCtx) (New := .empty) sndBatch (oneStoreBody ProdCtx))) :=
  ⟨AB_BA_not_paired, fst_snd_not_paired⟩

end PairMismatchFixtures

end Gimbal.Equality.Scherer
