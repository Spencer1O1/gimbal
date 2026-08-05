/-
  Scherer-core typed erasure (S2).

  Maps intrinsic focused/saturated judgments to `Equality.Tm` under exact
  erasure contexts `eraseInvCtx` / `eraseSInvCtx`. Pending-head coproduct and
  zero use finite binder rotation. `Foc.letShift` uses `subst0`. Saturation
  batches use one parallel substitution of all pre-batch observations.
-/

import Gimbal.Equality.Scherer.Focused

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-- Local composition (avoid importing `Algebra` → old `Focused`). -/
def renameComp {Γ Δ Ε : Ctx sig}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) : Rename sig Γ Ε :=
  fun {A} (x : Var Γ A) => ρ (τ x)

/-! ### Pending-head rotation -/

/-- Lift a renaming through pending erasure. -/
def renameEraseAux {Γ Δ : Ctx sig} (ρ : Rename sig Γ Δ) :
    (ps : Pending sig) →
      Rename sig (Pending.eraseAux ps Γ) (Pending.eraseAux ps Δ)
  | .empty => ρ
  | .cons _ qs => renameEraseAux (Rename.ext ρ) qs

/--
Rotate pending-head binder `H` to newest:
`eraseAux ps (Δ ▻ H) → eraseAux ps Δ ▻ H`.
-/
def rotateHeadToNewest {Δ : Ctx sig} {H : Object sig.nBases} :
    (ps : Pending sig) →
      Rename sig (Pending.eraseAux ps (Δ.snoc H))
        ((Pending.eraseAux ps Δ).snoc H)
  | .empty => Rename.id
  | .cons Q qs =>
      renameComp
        (rotateHeadToNewest (Δ := Δ.snoc Q.erase) (H := H) qs)
        (renameEraseAux
          (Rename.exchange (Γ := Δ) (A := H) (B := Q.erase)) qs)

/-- Inverse: `eraseAux ps Δ ▻ A → eraseAux ps (Δ ▻ A)`. -/
def rotateNewestToHead {Δ : Ctx sig} {A : Object sig.nBases} :
    (ps : Pending sig) →
      Rename sig ((Pending.eraseAux ps Δ).snoc A)
        (Pending.eraseAux ps (Δ.snoc A))
  | .empty => Rename.id
  | .cons Q qs =>
      renameComp
        (renameEraseAux
          (Rename.exchange (Γ := Δ) (A := Q.erase) (B := A)) qs)
        (rotateNewestToHead (Δ := Δ.snoc Q.erase) (A := A) qs)

/-- Variable for pending-head formula under `eraseAux ps (Δ ▻ H)`. -/
def pendingHeadVar {Δ : Ctx sig} {H : Object sig.nBases} :
    (ps : Pending sig) → Var (Pending.eraseAux ps (Δ.snoc H)) H
  | .empty => .here
  | .cons Q qs =>
      renameEraseAux
          (Rename.exchange (Γ := Δ) (A := Q.erase) (B := H)) qs
          (pendingHeadVar (Δ := Δ.snoc Q.erase) (H := H) qs)

/-- Split a newest-binder variable into `here` vs `there`. -/
def splitNewest {Γ : Ctx sig} {H A : Object sig.nBases} :
    Var (Γ.snoc H) A → (A = H) ⊕' Var Γ A
  | .here => .inl rfl
  | .there z => .inr z

/-! ### Ordinary erasure -/

mutual
def NegNeu.erase {Γ : StableCtx sig} {N : Neg sig.nBases} :
    NegNeu Γ N → Tm Γ.erase N.erase
  | .var x => .var x.erase
  | .fst n => .fst (NegNeu.erase n)
  | .snd n => .snd (NegNeu.erase n)
  | .app n p => .app (NegNeu.erase n) (PosNeu.erase p)

def PosNeu.erase {Γ : StableCtx sig} {P : Pos sig.nBases} :
    PosNeu Γ P → Tm Γ.erase P.erase
  | .atom x => .var x.erase
  | .inl p => .inl (PosNeu.erase p)
  | .inr p => .inr (PosNeu.erase p)
  | .shift t => Inv.erase t

def Foc.erase {Γ : StableCtx sig} {Q : Pos sig.nBases} :
    Foc Γ Q → Tm Γ.erase Q.erase
  | .up p => PosNeu.erase p
  | .letShift n t => subst0 (Inv.erase t) (NegNeu.erase n)

def Inv.erase {Γ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases} :
    Inv Γ ps G → Tm (eraseInvCtx Γ ps) G.erase
  | .unit => .unit
  | .pair t u => .pair (Inv.erase t) (Inv.erase u)
  | .lam t => .lam (Inv.erase t)
  | .focusPos f => Foc.erase f
  | .focusShift f => Foc.erase f
  | .storeAtom (q := q) t =>
      Inv.erase (Γ := StableCtx.snoc Γ (.atom q)) t
  | .storeShift (N := N) t =>
      Inv.erase (Γ := StableCtx.snoc Γ (.neg N)) t
  | .abort (ps := rest) =>
      let Δ := Γ.erase
      let H : Object sig.nBases := .never
      let Γmid := Pending.eraseAux rest Δ
      let n : Tm (Γmid.snoc H) H := .var .here
      rename (rotateNewestToHead (Δ := Δ) (A := H) rest) (.abort n)
  | .caseSum (A := A) (B := B) (ps := rest) l r =>
      let Δ := Γ.erase
      let H : Object sig.nBases := .coprod A.erase B.erase
      let Γmid := Pending.eraseAux rest Δ
      let t :=
        rename (Rename.skip1 (Γ := Γmid) (A := A.erase) (B := H))
          (rename (rotateHeadToNewest (Δ := Δ) (H := A.erase) rest) (Inv.erase l))
      let u :=
        rename (Rename.skip1 (Γ := Γmid) (A := B.erase) (B := H))
          (rename (rotateHeadToNewest (Δ := Δ) (H := B.erase) rest) (Inv.erase r))
      let s : Tm (Γmid.snoc H) H := .var .here
      rename (rotateNewestToHead (Δ := Δ) (A := H) rest) (.case s t u)
end

/-! ### Saturated erasure -/

mutual
def SNegNeu.erase {Γ : StableCtx sig} {N : Neg sig.nBases} :
    SNegNeu Γ N → Tm Γ.erase N.erase
  | .var x => .var x.erase
  | .fst n => .fst (SNegNeu.erase n)
  | .snd n => .snd (SNegNeu.erase n)
  | .app n p => .app (SNegNeu.erase n) (SPosNeu.erase p)

def SPosNeu.erase {Γ : StableCtx sig} {P : Pos sig.nBases} :
    SPosNeu Γ P → Tm Γ.erase P.erase
  | .atom x => .var x.erase
  | .inl p => .inl (SPosNeu.erase p)
  | .inr p => .inr (SPosNeu.erase p)
  | .shift t => SInv.erase t

/-- Lookup under a parallel batch substitution. -/
def batchSubstLookup {Γ : StableCtx sig} {selected : Pending sig}
    (obs : NonemptyBatchObs Γ selected) {A : Object sig.nBases}
    (x : Var (Pending.eraseAux selected Γ.erase) A) : Tm Γ.erase A :=
  match obs with
  | .one n => Subst.single (SNegNeu.erase n) x
  | .cons (Q := Q) (ps := rest) n σrest =>
      match splitNewest
          (rotateHeadToNewest (Δ := Γ.erase) (H := Q.erase) rest x) with
      | .inl h =>
          (h ▸ (SNegNeu.erase n : Tm Γ.erase Q.erase) : Tm Γ.erase A)
      | .inr z => batchSubstLookup σrest z

def Sat.erase {Old New : StableCtx sig} {P : Pos sig.nBases} :
    Sat Old New P → Tm (Old.append New).erase P.erase
  | .up v => SPosNeu.erase v
  | .batch obs body =>
      subst (fun {_} x => batchSubstLookup obs x) (SInv.erase body)

def SInv.erase {Old New : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} :
    SInv Old New ps G → Tm (eraseSInvCtx Old New ps) G.erase
  | .unit => .unit
  | .pair t u => .pair (SInv.erase t) (SInv.erase u)
  | .lam t => .lam (SInv.erase t)
  | .storeAtom (q := q) t =>
      SInv.erase (New := New.snoc (.atom q)) t
  | .storeShift (N := N) t =>
      SInv.erase (New := New.snoc (.neg N)) t
  | .satPos s => Sat.erase s
  | .satShift s => Sat.erase s
  | .abort (ps := rest) =>
      let Δ := (Old.append New).erase
      let H : Object sig.nBases := .never
      let Γmid := Pending.eraseAux rest Δ
      let n : Tm (Γmid.snoc H) H := .var .here
      rename (rotateNewestToHead (Δ := Δ) (A := H) rest) (.abort n)
  | .caseSum (A := A) (B := B) (ps := rest) l r =>
      let Δ := (Old.append New).erase
      let H : Object sig.nBases := .coprod A.erase B.erase
      let Γmid := Pending.eraseAux rest Δ
      let t :=
        rename (Rename.skip1 (Γ := Γmid) (A := A.erase) (B := H))
          (rename (rotateHeadToNewest (Δ := Δ) (H := A.erase) rest) (SInv.erase l))
      let u :=
        rename (Rename.skip1 (Γ := Γmid) (A := B.erase) (B := H))
          (rename (rotateHeadToNewest (Δ := Δ) (H := B.erase) rest) (SInv.erase r))
      let s : Tm (Γmid.snoc H) H := .var .here
      rename (rotateNewestToHead (Δ := Δ) (A := H) rest) (.case s t u)
end

/-- Parallel substitution for a nonempty batch (one `Subst`, not a subst0 chain). -/
def batchSubst {Γ : StableCtx sig} {selected : Pending sig}
    (obs : NonemptyBatchObs Γ selected) :
    Subst sig (Pending.eraseAux selected Γ.erase) Γ.erase :=
  fun {_} x => batchSubstLookup obs x

/-- Alias matching the public erasure surface for batches. -/
abbrev NonemptyBatchObs.toSubst {Γ : StableCtx sig} {selected : Pending sig} :
    NonemptyBatchObs Γ selected →
      Subst sig (Pending.eraseAux selected Γ.erase) Γ.erase :=
  batchSubst

/-! ### Erasure fixtures -/

namespace EraseFixtures

open Fixtures

def erase_letShift :
    Tm (sig := sig0)
      (StableCtx.snoc (.empty : StableCtx sig0) (.neg (.shift .zero))).erase
      (Pos.shift (.one : Neg sig0.nBases)).erase :=
  Foc.erase foc_letShift

def erase_case_zero_sum :
    Tm (sig := sig0)
      (eraseInvCtx (.empty : StableCtx sig0) (.cons (.sum .zero .zero) .empty))
      (Goal.neg (.one : Neg sig0.nBases)).erase :=
  Inv.erase inv_case_zero_sum

def erase_sat_up :
    Tm (sig := sig0)
      (StableCtx.append (.empty : StableCtx sig0) .empty).erase
      (Pos.shift (.one : Neg sig0.nBases)).erase :=
  Sat.erase sat_up

def erase_batch_one :
    Tm (sig := sig0)
      (StableCtx.snoc (.empty : StableCtx sig0) (.neg (.shift .zero))).erase
      (Pos.shift (.one : Neg sig0.nBases)).erase :=
  SInv.erase sinv_batch_one

def sinv_batch_two :
    SInv (sig := sig0)
      (StableCtx.snoc .empty (.neg (.shift .zero))) .empty .empty
      (.pos (.shift .one)) :=
  .satPos <|
    .batch
      (.cons (.var .here) (.one (.var .here)))
      .abort

def erase_batch_two :
    Tm (sig := sig0)
      (StableCtx.snoc (.empty : StableCtx sig0) (.neg (.shift .zero))).erase
      (Pos.shift (.one : Neg sig0.nBases)).erase :=
  SInv.erase sinv_batch_two

theorem erase_unit_eq :
    Inv.erase (inv_unit : Inv (sig := sig0) .empty .empty (.neg .one)) =
      (Tm.unit : Tm (sig := sig0) .empty .unit) := rfl

theorem erase_sat_up_eq :
    Sat.erase (sat_up : Sat (sig := sig0) .empty .empty (.shift .one)) =
      (Tm.unit : Tm (sig := sig0) .empty .unit) := rfl

end EraseFixtures

end Gimbal.Equality.Scherer
