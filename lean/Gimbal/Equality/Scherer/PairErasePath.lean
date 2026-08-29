/-
  Typed one-hole paths for contextual erasure equality.

  These paths contain only focused syntax.  In particular, they do not give
  traces, origins, or dead branches any semantic meaning.  A later selector
  certificate may use them to state that an unreachable hole is irrelevant.
-/

import Gimbal.Equality.Scherer.Erase
import Gimbal.Equality.TmEq

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Equality under fixed renaming and substitution -/

theorem TmEq.renameSame {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) {t u : Tm Γ A} (h : TmEq t u) :
    TmEq (rename ρ t) (rename ρ u) := by
  refine ⟨?_⟩
  intro X env
  rw [interpret_rename, interpret_rename]
  exact h.qm_eq (Env.rename env ρ)

/-- Applying one fixed substitution preserves `TmEq`. -/
theorem TmEq.subst_same {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (σ : Subst sig Γ Δ) {t u : Tm Γ A} (h : TmEq t u) :
    TmEq (subst σ t) (subst σ u) := by
  refine ⟨?_⟩
  intro X env
  rw [interpret_qm_subst, interpret_qm_subst]
  exact h.qm_eq (Env.ofSubst env σ)

/-! ### Typed saturated erasure paths -/

/-
A one-hole path from an `SInv` judgment to one fixed root `SInv` judgment.
Case and pair frames freeze one common sibling, so replacing children can be
done one at a time and composed by transitivity.
-/
mutual
  inductive InvPath (ROld RNew : StableCtx sig) (Rps : Pending sig)
      (RG : Goal sig.nBases) :
      {Old New : StableCtx sig} → {ps : Pending sig} →
      {G : Goal sig.nBases} → Type where
    | root : InvPath ROld RNew Rps RG
        (Old := ROld) (New := RNew) (ps := Rps) (G := RG)
    | caseLeft
        (K : InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .cons (.sum A B) rest) (G := G))
        (fixed : SInv Old New (.cons B rest) G) :
        InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .cons A rest) (G := G)
    | caseRight
        (K : InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .cons (.sum A B) rest) (G := G))
        (fixed : SInv Old New (.cons A rest) G) :
        InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .cons B rest) (G := G)
    | storeAtom
        (K : InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .cons (.atom q) rest) (G := G)) :
        InvPath ROld RNew Rps RG
          (Old := Old) (New := New.snoc (.atom q)) (ps := rest) (G := G)
    | storeShift
        (K : InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .cons (.shift N) rest) (G := G)) :
        InvPath ROld RNew Rps RG
          (Old := Old) (New := New.snoc (.neg N)) (ps := rest) (G := G)
    | pairLeft
        (K : InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .empty)
          (G := .neg (.prod A B)))
        (fixed : SInv Old New .empty (.neg B)) :
        InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .empty) (G := .neg A)
    | pairRight
        (K : InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .empty)
          (G := .neg (.prod A B)))
        (fixed : SInv Old New .empty (.neg A)) :
        InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .empty) (G := .neg B)
    | lam
        (K : InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .empty)
          (G := .neg (.arr A B))) :
        InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .cons A .empty) (G := .neg B)
    | fromShift
        (K : PosPath ROld RNew Rps RG
          (Γ := Γ) (P := .shift N)) :
        InvPath ROld RNew Rps RG
          (Old := Γ) (New := .empty) (ps := .empty) (G := .neg N)
    | fromBatch
        (K : SatPath ROld RNew Rps RG
          (Old := Old) (New := New) (P := P))
        (obs : NonemptyBatchObs (Old.append New) selected) :
        InvPath ROld RNew Rps RG
          (Old := Old.append New) (New := .empty)
          (ps := selected) (G := .pos P)

  /-- A one-hole path from a saturated selection to a fixed root `SInv`. -/
  inductive SatPath (ROld RNew : StableCtx sig) (Rps : Pending sig)
      (RG : Goal sig.nBases) :
      {Old New : StableCtx sig} → {P : Pos sig.nBases} → Type where
    | fromSatPos
        (K : InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .empty) (G := .pos P)) :
        SatPath ROld RNew Rps RG (Old := Old) (New := New) (P := P)
    | fromSatShift
        (K : InvPath ROld RNew Rps RG
          (Old := Old) (New := New) (ps := .empty)
          (G := .neg (.shift P))) :
        SatPath ROld RNew Rps RG (Old := Old) (New := New) (P := P)

  /-- A one-hole path from a saturated positive neutral to a root `SInv`. -/
  inductive PosPath (ROld RNew : StableCtx sig) (Rps : Pending sig)
      (RG : Goal sig.nBases) :
      {Γ : StableCtx sig} → {P : Pos sig.nBases} → Type where
    | fromDone
        (K : SatPath ROld RNew Rps RG
          (Old := Old) (New := New) (P := P)) :
        PosPath ROld RNew Rps RG (Γ := Old.append New) (P := P)
    | inl
        (K : PosPath ROld RNew Rps RG (Γ := Γ) (P := .sum A B)) :
        PosPath ROld RNew Rps RG (Γ := Γ) (P := A)
    | inr
        (K : PosPath ROld RNew Rps RG (Γ := Γ) (P := .sum A B)) :
        PosPath ROld RNew Rps RG (Γ := Γ) (P := B)
end

/-! ### Filling paths -/

mutual
  @[simp] def InvPath.fill
      (K : InvPath ROld RNew Rps RG (Old := Old) (New := New)
        (ps := ps) (G := G)) :
      SInv Old New ps G → SInv ROld RNew Rps RG :=
    match K with
    | .root => fun t => t
    | .caseLeft K fixed => fun t => K.fill (.caseSum t fixed)
    | .caseRight K fixed => fun t => K.fill (.caseSum fixed t)
    | .storeAtom K => fun t => K.fill (.storeAtom t)
    | .storeShift K => fun t => K.fill (.storeShift t)
    | .pairLeft K fixed => fun t => K.fill (.pair t fixed)
    | .pairRight K fixed => fun t => K.fill (.pair fixed t)
    | .lam K => fun t => K.fill (.lam t)
    | .fromShift K => fun t => K.fill (.shift t)
    | .fromBatch K obs => fun t => K.fill (.batch obs t)

  @[simp] def SatPath.fill
      (K : SatPath ROld RNew Rps RG (Old := Old) (New := New) (P := P)) :
      Sat Old New P → SInv ROld RNew Rps RG :=
    match K with
    | .fromSatPos K => fun s => K.fill (.satPos s)
    | .fromSatShift K => fun s => K.fill (.satShift s)

  @[simp] def PosPath.fill
      (K : PosPath ROld RNew Rps RG (Γ := Γ) (P := P)) :
      SPosNeu Γ P → SInv ROld RNew Rps RG :=
    match K with
    | .fromDone K => fun p => K.fill (.done p)
    | .inl K => fun p => K.fill (.inl p)
    | .inr K => fun p => K.fill (.inr p)
end

/-! ### Contextual equality and irrelevance -/

def InvPath.ContextualTmEq
    (K : InvPath ROld RNew Rps RG (Old := Old) (New := New)
      (ps := ps) (G := G)) (t u : SInv Old New ps G) : Prop :=
  TmEq (K.fill t).erase (K.fill u).erase

def SatPath.ContextualTmEq
    (K : SatPath ROld RNew Rps RG (Old := Old) (New := New) (P := P))
    (s t : Sat Old New P) : Prop :=
  TmEq (K.fill s).erase (K.fill t).erase

def PosPath.ContextualTmEq
    (K : PosPath ROld RNew Rps RG (Γ := Γ) (P := P))
    (p q : SPosNeu Γ P) : Prop :=
  TmEq (K.fill p).erase (K.fill q).erase

def InvPath.Irrelevant
    (K : InvPath ROld RNew Rps RG (Old := Old) (New := New)
      (ps := ps) (G := G)) : Prop :=
  ∀ t u, K.ContextualTmEq t u

def SatPath.Irrelevant
    (K : SatPath ROld RNew Rps RG (Old := Old) (New := New) (P := P)) : Prop :=
  ∀ s t, K.ContextualTmEq s t

def PosPath.Irrelevant
    (K : PosPath ROld RNew Rps RG (Γ := Γ) (P := P)) : Prop :=
  ∀ p q, K.ContextualTmEq p q

private def InvPath.Lifts
    (K : InvPath ROld RNew Rps RG (Old := Old) (New := New)
      (ps := ps) (G := G)) : Prop :=
  ∀ {t u : SInv Old New ps G}, TmEq t.erase u.erase → K.ContextualTmEq t u

private def SatPath.Lifts
    (K : SatPath ROld RNew Rps RG (Old := Old) (New := New) (P := P)) : Prop :=
  ∀ {s t : Sat Old New P}, TmEq s.erase t.erase → K.ContextualTmEq s t

private def PosPath.Lifts
    (K : PosPath ROld RNew Rps RG (Γ := Γ) (P := P)) : Prop :=
  ∀ {p q : SPosNeu Γ P}, TmEq p.erase q.erase → K.ContextualTmEq p q

@[simp] theorem InvPath.root_contextualTmEq
    (t u : SInv Old New ps G) :
    (InvPath.root (ROld := Old) (RNew := New) (Rps := ps) (RG := G)).ContextualTmEq
      t u ↔ TmEq t.erase u.erase := Iff.rfl

/-! ### Erasure congruence for one focused frame -/

private theorem tmEq_caseLeft {Old New : StableCtx sig}
    {A B : Pos sig.nBases} {rest : Pending sig} {G : Goal sig.nBases}
    {l l' : SInv Old New (.cons A rest) G}
    (r : SInv Old New (.cons B rest) G) (h : TmEq l.erase l'.erase) :
    TmEq (SInv.erase (.caseSum l r)) (SInv.erase (.caseSum l' r)) := by
  simp only [SInv.erase]
  apply TmEq.renameSame
  apply TmEq.«case» (.refl _)
  · exact TmEq.renameSame _ (TmEq.renameSame _ h)
  · exact .refl _

private theorem tmEq_caseRight {Old New : StableCtx sig}
    {A B : Pos sig.nBases} {rest : Pending sig} {G : Goal sig.nBases}
    (l : SInv Old New (.cons A rest) G)
    {r r' : SInv Old New (.cons B rest) G} (h : TmEq r.erase r'.erase) :
    TmEq (SInv.erase (.caseSum l r)) (SInv.erase (.caseSum l r')) := by
  simp only [SInv.erase]
  apply TmEq.renameSame
  apply TmEq.«case» (.refl _)
  · exact .refl _
  · exact TmEq.renameSame _ (TmEq.renameSame _ h)

private theorem InvPath.lifts
    (K : InvPath ROld RNew Rps RG (Old := Old) (New := New)
      (ps := ps) (G := G)) : K.Lifts := by
  exact InvPath.rec
      (motive_1 := fun K => K.Lifts)
      (motive_2 := fun K => K.Lifts)
      (motive_3 := fun K => K.Lifts)
      (by
        intro t u h
        simpa [InvPath.Lifts, InvPath.ContextualTmEq, InvPath.fill] using h)
      (by
        intro Old New A B rest G K fixed ih t u h
        apply ih
        exact tmEq_caseLeft fixed h)
      (by
        intro Old New A B rest G K fixed ih t u h
        apply ih
        exact tmEq_caseRight fixed h)
      (by
        intro Old New q rest G K ih t u h
        apply ih
        simpa [SInv.erase, eraseSInvCtx, Pending.eraseAux, StableCtx.append,
          StableCtx.erase, StableTy.erase, Pos.erase] using h)
      (by
        intro Old New N rest G K ih t u h
        apply ih
        simpa [SInv.erase, eraseSInvCtx, Pending.eraseAux, StableCtx.append,
          StableCtx.erase, StableTy.erase, Pos.erase, Neg.erase] using h)
      (by
        intro Old New A B K fixed ih t u h
        apply ih
        simpa [SInv.erase, Goal.erase, Neg.erase] using TmEq.pair h (.refl fixed.erase))
      (by
        intro Old New A B K fixed ih t u h
        apply ih
        simpa [SInv.erase, Goal.erase, Neg.erase] using TmEq.pair (.refl fixed.erase) h)
      (by
        intro Old New A B K ih t u h
        apply ih
        simpa [SInv.erase, eraseSInvCtx, Pending.eraseAux, Goal.erase, Neg.erase] using
          TmEq.lam h)
      (by
        intro Γ N K ih t u h
        apply ih (p := .shift t) (q := .shift u)
        simpa [SPosNeu.erase, eraseSInvCtx, eraseInvCtx, Pending.eraseAux,
          StableCtx.append, StableCtx.erase, Goal.erase, Pos.erase] using h)
      (by
        intro Old New P selected K obs ih t u h
        apply ih (s := .batch obs t) (t := .batch obs u)
        simpa [Sat.erase] using
          TmEq.subst_same (fun {_} x => batchSubstLookup obs x) h)
      (by
        intro Old New P K ih s t h
        apply ih (t := .satPos s) (u := .satPos t)
        simpa [SInv.erase, eraseSInvCtx, Pending.eraseAux, Goal.erase] using h)
      (by
        intro Old New P K ih s t h
        apply ih (t := .satShift s) (u := .satShift t)
        simpa [SInv.erase, eraseSInvCtx, Pending.eraseAux, Goal.erase, Neg.erase] using h)
      (by
        intro Old New P K ih p q h
        apply ih (s := .done p) (t := .done q)
        simpa [Sat.erase] using h)
      (by
        intro Γ A B K ih p q h
        apply ih (p := .inl p) (q := .inl q)
        simpa [SPosNeu.erase, Pos.erase] using TmEq.inl h)
      (by
        intro Γ A B K ih p q h
        apply ih (p := .inr p) (q := .inr q)
        simpa [SPosNeu.erase, Pos.erase] using TmEq.inr h)
      K

theorem InvPath.contextual_of_tmEq
    (K : InvPath ROld RNew Rps RG (Old := Old) (New := New)
      (ps := ps) (G := G)) {t u : SInv Old New ps G}
    (h : TmEq t.erase u.erase) : K.ContextualTmEq t u :=
  K.lifts h

theorem SatPath.contextual_of_tmEq
    (K : SatPath ROld RNew Rps RG (Old := Old) (New := New) (P := P))
    {s t : Sat Old New P} (h : TmEq s.erase t.erase) :
    K.ContextualTmEq s t := by
  cases K with
  | fromSatPos K => exact K.lifts h
  | fromSatShift K => exact K.lifts h

theorem PosPath.contextual_of_tmEq
    (K : PosPath ROld RNew Rps RG (Γ := Γ) (P := P))
    {p q : SPosNeu Γ P} (h : TmEq p.erase q.erase) :
    K.ContextualTmEq p q := by
  cases K with
  | fromDone K => exact SatPath.contextual_of_tmEq K h
  | inl K => exact PosPath.contextual_of_tmEq K (.inl h)
  | inr K => exact PosPath.contextual_of_tmEq K (.inr h)

/-! ### Sequential replacement of paired children -/

theorem InvPath.pair_sequential
    (K : InvPath ROld RNew Rps RG (Old := Old) (New := New)
      (ps := .empty) (G := .neg (.prod A B)))
    {l l' : SInv Old New .empty (.neg A)}
    {r r' : SInv Old New .empty (.neg B)}
    (hl : (K.pairLeft r).ContextualTmEq l l')
    (hr : (K.pairRight l').ContextualTmEq r r') :
    K.ContextualTmEq (.pair l r) (.pair l' r') := by
  unfold InvPath.ContextualTmEq at hl hr ⊢
  exact hl.trans hr

theorem InvPath.case_sequential
    (K : InvPath ROld RNew Rps RG (Old := Old) (New := New)
      (ps := .cons (.sum A B) rest) (G := G))
    {l l' : SInv Old New (.cons A rest) G}
    {r r' : SInv Old New (.cons B rest) G}
    (hl : (K.caseLeft r).ContextualTmEq l l')
    (hr : (K.caseRight l').ContextualTmEq r r') :
    K.ContextualTmEq (.caseSum l r) (.caseSum l' r') := by
  unfold InvPath.ContextualTmEq at hl hr ⊢
  exact hl.trans hr

/-! ### Boundary fixtures -/

namespace PairErasePathFixtures

open Fixtures

def pairRoot : SInv (sig := sig0) .empty .empty .empty
    (.neg (.prod .one .one)) := .pair .unit .unit

theorem root_is_ordinary_tmEq :
    (InvPath.root (ROld := (.empty : StableCtx sig0)) (RNew := .empty)
      (Rps := .empty) (RG := .neg (.prod .one .one))).ContextualTmEq
      pairRoot pairRoot ↔ TmEq pairRoot.erase pairRoot.erase := Iff.rfl

theorem pair_components_compose_sequentially :
    (InvPath.root (ROld := (.empty : StableCtx sig0)) (RNew := .empty)
      (Rps := .empty) (RG := .neg (.prod .one .one))).ContextualTmEq
      (.pair .unit .unit) (.pair .unit .unit) := by
  apply InvPath.pair_sequential
  · exact InvPath.contextual_of_tmEq _ (.refl _)
  · exact InvPath.contextual_of_tmEq _ (.refl _)

def caseRoot : SInv (sig := sig0) .empty .empty
    (.cons (.sum .zero .zero) .empty) (.neg .one) :=
  .caseSum .abort .abort

theorem case_siblings_compose_sequentially :
    (InvPath.root (ROld := (.empty : StableCtx sig0)) (RNew := .empty)
      (Rps := .cons (.sum .zero .zero) .empty) (RG := .neg .one)).ContextualTmEq
      caseRoot caseRoot := by
  apply InvPath.case_sequential
  · exact InvPath.contextual_of_tmEq _ (.refl _)
  · exact InvPath.contextual_of_tmEq _ (.refl _)

abbrev ZeroCtx : StableCtx sig0 :=
  (StableCtx.empty : StableCtx sig0).snoc (.neg (.shift .zero))

def literalObs : NonemptyBatchObs ZeroCtx (.cons .zero .empty) :=
  .one (.var .here)

def batchBody : SInv (sig := sig0) ZeroCtx .empty
    (.cons .zero .empty) (.pos (.shift .one)) := .abort

def batchRoot : SInv (sig := sig0) ZeroCtx .empty .empty
    (.pos (.shift .one)) := .satPos (.batch literalObs batchBody)

def batchBodyPath : InvPath ZeroCtx .empty .empty (.pos (.shift .one))
    (Old := ZeroCtx) (New := .empty)
    (ps := .cons .zero .empty) (G := .pos (.shift .one)) :=
  .fromBatch (.fromSatPos .root) literalObs

theorem batch_fill_uses_literal_observation :
    batchBodyPath.fill batchBody = batchRoot := rfl

theorem batch_fill_erases_by_same_substitution :
    (batchBodyPath.fill batchBody).erase =
      subst (batchSubst literalObs) batchBody.erase := rfl

end PairErasePathFixtures

end Gimbal.Equality.Scherer
