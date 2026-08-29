/-
  Proof-relevant structural pairing for saturated Scherer normal forms.

  This layer deliberately records no search trace and computes no equality
  code.  Its batch constructor is the synchronization boundary: both sides
  must literally use the same ordered observation batch.  Inconsistent
  leaves instead ignore the particular zero neutral, because a common local
  contradiction is the highest-priority saturated outcome.
-/

import Gimbal.Equality.Scherer.Focused

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Paired saturated normal forms -/

mutual

/--
Two saturated positive neutrals at the same type.  Atomic sources may differ;
at sums, a differing injection tag is a terminal structural mismatch.  Shift
payloads recurse back into paired saturated normal forms.
-/
inductive PairedSPosNeu :
    {Γ : StableCtx sig} → {P : Pos sig.nBases} →
    SPosNeu Γ P → SPosNeu Γ P → Prop where
  | atom {Γ q} (x y : StableVar Γ (.atom q)) :
      PairedSPosNeu (.atom x) (.atom y)
  | inl {Γ A B} {x y : SPosNeu Γ A} :
      PairedSPosNeu x y →
      PairedSPosNeu (SPosNeu.inl (B := B) x) (SPosNeu.inl (B := B) y)
  | inr {Γ A B} {x y : SPosNeu Γ B} :
      PairedSPosNeu x y →
      PairedSPosNeu (SPosNeu.inr (A := A) x) (SPosNeu.inr (A := A) y)
  | inl_inr {Γ A B} (x : SPosNeu Γ A) (y : SPosNeu Γ B) :
      PairedSPosNeu (SPosNeu.inl (B := B) x) (SPosNeu.inr (A := A) y)
  | inr_inl {Γ A B} (x : SPosNeu Γ B) (y : SPosNeu Γ A) :
      PairedSPosNeu (SPosNeu.inr (A := A) x) (SPosNeu.inl (B := B) y)
  | shift {Γ N} {d e : SInv Γ .empty .empty (.neg N)} :
      PairedNormal d e →
      PairedSPosNeu (.shift d) (.shift e)

/--
Two selected saturated outcomes.  A batch is pairable only when both `Sat`
terms contain one and the same `NonemptyBatchObs` value, in the same order.
Inconsistent leaves retain the actual witnesses as indices but do not compare
their proof syntax.
-/
inductive PairedSelected :
    {Old New : StableCtx sig} → {P : Pos sig.nBases} →
    Sat Old New P → Sat Old New P → Prop where
  | inconsistent {Old New : StableCtx sig} {P : Pos sig.nBases}
      (left right : SNegNeu (Old.append New) (.shift .zero)) :
      PairedSelected (.inconsistent (P := P) left) (.inconsistent right)
  | done {Old New : StableCtx sig} {P : Pos sig.nBases}
      {left right : SPosNeu (Old.append New) P} :
      PairedSPosNeu left right →
      PairedSelected (.done left) (.done right)
  | batch {Old New : StableCtx sig} {selected : Pending sig}
      {P : Pos sig.nBases}
      (obs : NonemptyBatchObs (Old.append New) selected)
      {left right : SInv (Old.append New) .empty selected (.pos P)} :
      PairedNormal left right →
      PairedSelected (.batch obs left) (.batch obs right)

/--
Two saturated invertible derivations with identical judgment indices.  Every
constructor is forced and mirrored; products deliberately retain both child
occurrences even when they are definitionally identical.
-/
inductive PairedNormal :
    {Old New : StableCtx sig} → {ps : Pending sig} → {G : Goal sig.nBases} →
    SInv Old New ps G → SInv Old New ps G → Prop where
  | caseSum {Old New : StableCtx sig} {A B : Pos sig.nBases}
      {ps : Pending sig} {G : Goal sig.nBases}
      {leftA rightA : SInv Old New (.cons A ps) G}
      {leftB rightB : SInv Old New (.cons B ps) G} :
      PairedNormal leftA rightA →
      PairedNormal leftB rightB →
      PairedNormal (.caseSum leftA leftB) (.caseSum rightA rightB)
  | abort {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases} :
      PairedNormal
        (SInv.abort (Old := Old) (New := New) (ps := ps) (G := G))
        (SInv.abort (Old := Old) (New := New) (ps := ps) (G := G))
  | storeAtom {Old New : StableCtx sig} {q : Fin sig.nBases}
      {ps : Pending sig} {G : Goal sig.nBases}
      {left right : SInv Old (New.snoc (.atom q)) ps G} :
      PairedNormal left right →
      PairedNormal (.storeAtom left) (.storeAtom right)
  | storeShift {Old New : StableCtx sig} {N : Neg sig.nBases}
      {ps : Pending sig} {G : Goal sig.nBases}
      {left right : SInv Old (New.snoc (.neg N)) ps G} :
      PairedNormal left right →
      PairedNormal (.storeShift left) (.storeShift right)
  | unit {Old New : StableCtx sig} :
      PairedNormal
        (SInv.unit (Old := Old) (New := New))
        (SInv.unit (Old := Old) (New := New))
  | pair {Old New : StableCtx sig} {A B : Neg sig.nBases}
      {leftA rightA : SInv Old New .empty (.neg A)}
      {leftB rightB : SInv Old New .empty (.neg B)} :
      PairedNormal leftA rightA →
      PairedNormal leftB rightB →
      PairedNormal (.pair leftA leftB) (.pair rightA rightB)
  | lam {Old New : StableCtx sig} {A : Pos sig.nBases} {B : Neg sig.nBases}
      {left right : SInv Old New (.cons A .empty) (.neg B)} :
      PairedNormal left right →
      PairedNormal (.lam left) (.lam right)
  | satShift {Old New : StableCtx sig} {P : Pos sig.nBases}
      {left right : Sat Old New P} :
      PairedSelected left right →
      PairedNormal (.satShift left) (.satShift right)
  | satPos {Old New : StableCtx sig} {P : Pos sig.nBases}
      {left right : Sat Old New P} :
      PairedSelected left right →
      PairedNormal (.satPos left) (.satPos right)

end

/-! ### Constructor inversion -/

namespace PairedSPosNeu

theorem asInl {Γ : StableCtx sig} {A B : Pos sig.nBases}
    {left right : SPosNeu Γ A} :
    PairedSPosNeu (SPosNeu.inl (B := B) left) (SPosNeu.inl (B := B) right) →
      PairedSPosNeu left right
  | .inl h => h

theorem asInr {Γ : StableCtx sig} {A B : Pos sig.nBases}
    {left right : SPosNeu Γ B} :
    PairedSPosNeu (SPosNeu.inr (A := A) left) (SPosNeu.inr (A := A) right) →
      PairedSPosNeu left right
  | .inr h => h

theorem asShift {Γ : StableCtx sig} {N : Neg sig.nBases}
    {left right : SInv Γ .empty .empty (.neg N)} :
    PairedSPosNeu (.shift left) (.shift right) → PairedNormal left right
  | .shift h => h

end PairedSPosNeu

namespace PairedSelected

theorem asInconsistent {Old New : StableCtx sig} {P : Pos sig.nBases}
    {left right : SNegNeu (Old.append New) (.shift .zero)} :
    PairedSelected (.inconsistent (P := P) left) (.inconsistent right) → True := by
  intro _
  trivial

theorem asDone {Old New : StableCtx sig} {P : Pos sig.nBases}
    {left right : SPosNeu (Old.append New) P} :
    PairedSelected (.done left) (.done right) → PairedSPosNeu left right
  | .done h => h

theorem asBatch {Old New : StableCtx sig} {selected : Pending sig}
    {P : Pos sig.nBases}
    (obs : NonemptyBatchObs (Old.append New) selected)
    {left right : SInv (Old.append New) .empty selected (.pos P)} :
    PairedSelected (.batch obs left) (.batch obs right) →
      PairedNormal left right
  | .batch _ h => h

/-- Any paired batch terms contain propositionally identical observation data. -/
theorem batch_observations_heq {Old New : StableCtx sig} {P : Pos sig.nBases}
    {selectedLeft selectedRight : Pending sig}
    {obsLeft : NonemptyBatchObs (Old.append New) selectedLeft}
    {obsRight : NonemptyBatchObs (Old.append New) selectedRight}
    {left : SInv (Old.append New) .empty selectedLeft (.pos P)}
    {right : SInv (Old.append New) .empty selectedRight (.pos P)}
    (h : PairedSelected (.batch obsLeft left) (.batch obsRight right)) :
    HEq obsLeft obsRight := by
  cases h
  rfl

end PairedSelected

namespace PairedNormal

theorem asCaseSum {Old New : StableCtx sig} {A B : Pos sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    {leftA rightA : SInv Old New (.cons A ps) G}
    {leftB rightB : SInv Old New (.cons B ps) G} :
    PairedNormal (.caseSum leftA leftB) (.caseSum rightA rightB) →
      PairedNormal leftA rightA ∧ PairedNormal leftB rightB
  | .caseSum ha hb => ⟨ha, hb⟩

theorem asStoreAtom {Old New : StableCtx sig} {q : Fin sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    {left right : SInv Old (New.snoc (.atom q)) ps G} :
    PairedNormal (.storeAtom left) (.storeAtom right) → PairedNormal left right
  | .storeAtom h => h

theorem asStoreShift {Old New : StableCtx sig} {N : Neg sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    {left right : SInv Old (New.snoc (.neg N)) ps G} :
    PairedNormal (.storeShift left) (.storeShift right) → PairedNormal left right
  | .storeShift h => h

theorem asPair {Old New : StableCtx sig} {A B : Neg sig.nBases}
    {leftA rightA : SInv Old New .empty (.neg A)}
    {leftB rightB : SInv Old New .empty (.neg B)} :
    PairedNormal (.pair leftA leftB) (.pair rightA rightB) →
      PairedNormal leftA rightA ∧ PairedNormal leftB rightB
  | .pair ha hb => ⟨ha, hb⟩

theorem asLam {Old New : StableCtx sig} {A : Pos sig.nBases}
    {B : Neg sig.nBases}
    {left right : SInv Old New (.cons A .empty) (.neg B)} :
    PairedNormal (.lam left) (.lam right) → PairedNormal left right
  | .lam h => h

theorem asSatShift {Old New : StableCtx sig} {P : Pos sig.nBases}
    {left right : Sat Old New P} :
    PairedNormal (.satShift left) (.satShift right) → PairedSelected left right
  | .satShift h => h

theorem asSatPos {Old New : StableCtx sig} {P : Pos sig.nBases}
    {left right : Sat Old New P} :
    PairedNormal (.satPos left) (.satPos right) → PairedSelected left right
  | .satPos h => h

end PairedNormal

/-! ### Contract fixtures -/

namespace PairedSelectedFixtures

def sig0 : Signature := ⟨0, #[]⟩
def sig1 : Signature := ⟨1, #[]⟩

def q : Fin sig1.nBases := ⟨0, Nat.zero_lt_one⟩
def P : Pos sig1.nBases := .atom q

/-- Two observation sources of the same type in one pre-batch context. -/
def ObsCtx : StableCtx sig1 :=
  (StableCtx.empty.snoc (.neg (.shift P))).snoc (.neg (.shift P))

def newestObs : SNegNeu ObsCtx (.shift P) :=
  .var .here

def olderObs : SNegNeu ObsCtx (.shift P) :=
  .var (.there .here)

def newestBatch : NonemptyBatchObs ObsCtx (.cons P .empty) :=
  .one newestObs

def olderBatch : NonemptyBatchObs ObsCtx (.cons P .empty) :=
  .one olderObs

/-- A shared body which stores the selected atom and immediately retrieves it. -/
def batchBody : SInv ObsCtx .empty (.cons P .empty) (.pos P) :=
  .storeAtom (.satPos (.done (.atom .here)))

theorem pairedBatchBody : PairedNormal batchBody batchBody :=
  .storeAtom (.satPos (.done (.atom .here .here)))

/-- One literal ordered batch is accepted on both sides. -/
theorem commonBatchPaired :
    PairedSelected
      (Sat.batch (Old := ObsCtx) (New := .empty) newestBatch batchBody)
      (Sat.batch (Old := ObsCtx) (New := .empty) newestBatch batchBody) :=
  .batch (Old := ObsCtx) (New := .empty) newestBatch pairedBatchBody

/-- The two batches have the same selected-result telescope. -/
theorem distinctObs_same_results :
    (.cons P .empty : Pending sig1) = .cons P .empty := rfl

/-- They may also have identical future support summaries. -/
theorem distinctObs_same_support_summary :
    ([(P, 7)] : List (Pos sig1.nBases × Nat)) = [(P, 7)] := rfl

/--
Equal result and support summaries do not suffice: the literal observation
terms differ, so the paired-batch constructor is unavailable.
-/
theorem distinctObs_not_paired :
    ¬ PairedSelected
      (Sat.batch (Old := ObsCtx) (New := .empty) newestBatch batchBody)
      (Sat.batch (Old := ObsCtx) (New := .empty) olderBatch batchBody) := by
  intro h
  have hobs := PairedSelected.batch_observations_heq h
  cases hobs

/-- Duplicate product children are occurrence-sensitive and both remain legal. -/
def pairUnitUnit :
    SInv (sig := sig0) .empty .empty .empty (.neg (.prod .one .one)) :=
  .pair .unit .unit

theorem productDuplicateSiblingsPaired : PairedNormal pairUnitUnit pairUnitUnit :=
  .pair .unit .unit

/-- Two different zero witnesses in the same locally inconsistent context. -/
def ZeroCtx : StableCtx sig0 :=
  (StableCtx.empty.snoc (.neg (.shift .zero))).snoc (.neg (.shift .zero))

def olderZero : SNegNeu ZeroCtx (.shift .zero) :=
  .var (.there .here)

def newestZero : SNegNeu ZeroCtx (.shift .zero) :=
  .var .here

def inconsistentLeft : Sat ZeroCtx .empty (.shift .one) :=
  .inconsistent olderZero

def inconsistentRight : Sat ZeroCtx .empty (.shift .one) :=
  .inconsistent newestZero

/-- Inconsistent leaves pair without comparing the chosen zero-neutral syntax. -/
theorem commonInconsistentPaired :
    PairedSelected inconsistentLeft inconsistentRight :=
  .inconsistent (Old := ZeroCtx) (New := .empty) olderZero newestZero

/-- Opposite sum tags form a paired terminal structural mismatch. -/
def shiftedUnit : SPosNeu (sig := sig0) .empty (.shift .one) :=
  .shift .unit

def sumLeft :
    SPosNeu (sig := sig0) .empty (.sum (.shift .one) (.shift .one)) :=
  .inl shiftedUnit

def sumRight :
    SPosNeu (sig := sig0) .empty (.sum (.shift .one) (.shift .one)) :=
  .inr shiftedUnit

theorem sumTagMismatchPaired : PairedSPosNeu sumLeft sumRight :=
  .inl_inr shiftedUnit shiftedUnit

end PairedSelectedFixtures

end Gimbal.Equality.Scherer
