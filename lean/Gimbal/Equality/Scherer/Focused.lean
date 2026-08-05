/-
  Scherer-core intrinsic focused judgments (S2 focus/saturation revise).

  Constructor surface matches `Milestone 8 Scherer Core Proof Ledger.md`:
  * `Foc` is only `up` and real `letShift`
  * `Inv.focusShift` / `Inv.focusPos`
  * no `SFoc`, direct saturated focus, or generic `enterSat`
  * `SInv.satShift` / `SInv.satPos`
  * `Sat.done` (empty selection; payload in `old ++ new`) and nonempty `Sat.batch`
    of `SNegNeu (old++new) (.shift Q)`
  * batch body: `SInv (old++new) .empty selected (.pos P)`
  * `SPosNeu.shift` from `SInv Γ .empty .empty (.neg N)` only

  Erasure/renaming and selection validity remain out of scope.
-/

import Gimbal.Equality.Scherer.Syntax

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Ordinary neutrals and focus -/

mutual
/-- Ordinary negative neutrals. Application takes a positive neutral. -/
inductive NegNeu : StableCtx sig → Neg sig.nBases → Type where
  | var {Γ N} : StableVar Γ (.neg N) → NegNeu Γ N
  | fst {Γ A B} : NegNeu Γ (.prod A B) → NegNeu Γ A
  | snd {Γ A B} : NegNeu Γ (.prod A B) → NegNeu Γ B
  | app {Γ A N} : NegNeu Γ (.arr A N) → PosNeu Γ A → NegNeu Γ N

/--
Ordinary positive neutrals. `shift` is only from an invertible negative
derivation with empty pending.
-/
inductive PosNeu : StableCtx sig → Pos sig.nBases → Type where
  | atom {Γ q} : StableVar Γ (.atom q) → PosNeu Γ (.atom q)
  | inl {Γ A B} : PosNeu Γ A → PosNeu Γ (.sum A B)
  | inr {Γ A B} : PosNeu Γ B → PosNeu Γ (.sum A B)
  | shift {Γ N} : Inv Γ .empty (.neg N) → PosNeu Γ (.shift N)

/--
Ordinary positive focus. Only `up` and the real `letShift`
(`NegNeu` of `↓P` plus invertible body under pending `[P]`).
-/
inductive Foc : StableCtx sig → Pos sig.nBases → Type where
  | up {Γ Q} : PosNeu Γ Q → Foc Γ Q
  | letShift {Γ P Q} :
      NegNeu Γ (.shift P) →
      Inv Γ (.cons P .empty) (.pos Q) →
      Foc Γ Q

/-- Ordinary invertible judgment `Γ ; pending ⊢inv Goal`. -/
inductive Inv : StableCtx sig → Pending sig → Goal sig.nBases → Type where
  | caseSum {Γ A B ps G} :
      Inv Γ (.cons A ps) G →
      Inv Γ (.cons B ps) G →
      Inv Γ (.cons (.sum A B) ps) G
  | abort {Γ ps G} :
      Inv Γ (.cons .zero ps) G
  | storeAtom {Γ q ps G} :
      Inv (Γ.snoc (.atom q)) ps G →
      Inv Γ (.cons (.atom q) ps) G
  | storeShift {Γ N ps G} :
      Inv (Γ.snoc (.neg N)) ps G →
      Inv Γ (.cons (.shift N) ps) G
  | unit {Γ} :
      Inv Γ .empty (.neg .one)
  | pair {Γ A B} :
      Inv Γ .empty (.neg A) →
      Inv Γ .empty (.neg B) →
      Inv Γ .empty (.neg (.prod A B))
  | lam {Γ A B} :
      Inv Γ (.cons A .empty) (.neg B) →
      Inv Γ .empty (.neg (.arr A B))
  | focusShift {Γ P} :
      Foc Γ P →
      Inv Γ .empty (.neg (.shift P))
  | focusPos {Γ P} :
      Foc Γ P →
      Inv Γ .empty (.pos P)
end

/-! ### Saturated neutrals, nonempty batches, saturated judgments -/

mutual
/-- Saturated negative neutrals. -/
inductive SNegNeu : StableCtx sig → Neg sig.nBases → Type where
  | var {Γ N} : StableVar Γ (.neg N) → SNegNeu Γ N
  | fst {Γ A B} : SNegNeu Γ (.prod A B) → SNegNeu Γ A
  | snd {Γ A B} : SNegNeu Γ (.prod A B) → SNegNeu Γ B
  | app {Γ A N} : SNegNeu Γ (.arr A N) → SPosNeu Γ A → SNegNeu Γ N

/--
Saturated positive neutrals. `shift` requires `SInv Γ [] [] (neg N)`
(empty new context).
-/
inductive SPosNeu : StableCtx sig → Pos sig.nBases → Type where
  | atom {Γ q} : StableVar Γ (.atom q) → SPosNeu Γ (.atom q)
  | inl {Γ A B} : SPosNeu Γ A → SPosNeu Γ (.sum A B)
  | inr {Γ A B} : SPosNeu Γ B → SPosNeu Γ (.sum A B)
  | shift {Γ N} :
      SInv Γ .empty .empty (.neg N) →
      SPosNeu Γ (.shift N)

/--
Nonempty atomic batch of observations. Each entry for result `Q` is
`SNegNeu Γ (.shift Q)` in the shared pre-batch context `Γ`.
Empty batches are unrepresentable.
-/
inductive NonemptyBatchObs : StableCtx sig → Pending sig → Type where
  | one {Γ Q} :
      SNegNeu Γ (.shift Q) →
      NonemptyBatchObs Γ (.cons Q .empty)
  | cons {Γ Q ps} :
      SNegNeu Γ (.shift Q) →
      NonemptyBatchObs Γ ps →
      NonemptyBatchObs Γ (.cons Q ps)

/--
Saturation at positive boundary `P`.
`done` covers the empty-selection case: a saturated positive neutral already
typed in `old ++ new` (New may be nonempty when the result is strongly
retrievable without observations).
`batch` requires a nonempty observation list typed in `old ++ new`, with body
under promoted old context, empty new, and all selected results as pending.
-/
inductive Sat : StableCtx sig → StableCtx sig → Pos sig.nBases → Type where
  | done {Old New P} :
      SPosNeu (Old.append New) P →
      Sat Old New P
  | batch {Old New selected P} :
      NonemptyBatchObs (Old.append New) selected →
      SInv (Old.append New) .empty selected (.pos P) →
      Sat Old New P

/--
Saturated invertible judgment. Saturation entry is only `satShift` / `satPos`
(no direct saturated focus, no generic `enterSat`).
-/
inductive SInv : StableCtx sig → StableCtx sig → Pending sig → Goal sig.nBases → Type where
  | caseSum {Old New A B ps G} :
      SInv Old New (.cons A ps) G →
      SInv Old New (.cons B ps) G →
      SInv Old New (.cons (.sum A B) ps) G
  | abort {Old New ps G} :
      SInv Old New (.cons .zero ps) G
  | storeAtom {Old New q ps G} :
      SInv Old (New.snoc (.atom q)) ps G →
      SInv Old New (.cons (.atom q) ps) G
  | storeShift {Old New N ps G} :
      SInv Old (New.snoc (.neg N)) ps G →
      SInv Old New (.cons (.shift N) ps) G
  | unit {Old New} :
      SInv Old New .empty (.neg .one)
  | pair {Old New A B} :
      SInv Old New .empty (.neg A) →
      SInv Old New .empty (.neg B) →
      SInv Old New .empty (.neg (.prod A B))
  | lam {Old New A B} :
      SInv Old New (.cons A .empty) (.neg B) →
      SInv Old New .empty (.neg (.arr A B))
  | satShift {Old New P} :
      Sat Old New P →
      SInv Old New .empty (.neg (.shift P))
  | satPos {Old New P} :
      Sat Old New P →
      SInv Old New .empty (.pos P)
end

/-! ### Constructor inversion -/

namespace Inv

def asCaseSum {Γ : StableCtx sig} {A B : Pos sig.nBases} {ps : Pending sig}
    {G : Goal sig.nBases} :
    Inv Γ (.cons (.sum A B) ps) G →
      Inv Γ (.cons A ps) G × Inv Γ (.cons B ps) G
  | .caseSum l r => (l, r)

def asAbort {Γ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases} :
    Inv Γ (.cons .zero ps) G → PUnit
  | .abort => ⟨⟩

def asStoreAtom {Γ : StableCtx sig} {q : Fin sig.nBases} {ps : Pending sig}
    {G : Goal sig.nBases} :
    Inv Γ (.cons (.atom q) ps) G → Inv (Γ.snoc (.atom q)) ps G
  | .storeAtom t => t

def asStoreShift {Γ : StableCtx sig} {N : Neg sig.nBases} {ps : Pending sig}
    {G : Goal sig.nBases} :
    Inv Γ (.cons (.shift N) ps) G → Inv (Γ.snoc (.neg N)) ps G
  | .storeShift t => t

def asUnit {Γ : StableCtx sig} :
    Inv Γ .empty (.neg .one) → PUnit
  | .unit => ⟨⟩

def asPair {Γ : StableCtx sig} {A B : Neg sig.nBases} :
    Inv Γ .empty (.neg (.prod A B)) →
      Inv Γ .empty (.neg A) × Inv Γ .empty (.neg B)
  | .pair t u => (t, u)

def asLam {Γ : StableCtx sig} {A : Pos sig.nBases} {B : Neg sig.nBases} :
    Inv Γ .empty (.neg (.arr A B)) → Inv Γ (.cons A .empty) (.neg B)
  | .lam t => t

def asFocusShift {Γ : StableCtx sig} {P : Pos sig.nBases} :
    Inv Γ .empty (.neg (.shift P)) → Foc Γ P
  | .focusShift f => f

def asFocusPos {Γ : StableCtx sig} {P : Pos sig.nBases} :
    Inv Γ .empty (.pos P) → Foc Γ P
  | .focusPos f => f

end Inv

namespace SInv

def asCaseSum {Old New : StableCtx sig} {A B : Pos sig.nBases} {ps : Pending sig}
    {G : Goal sig.nBases} :
    SInv Old New (.cons (.sum A B) ps) G →
      SInv Old New (.cons A ps) G × SInv Old New (.cons B ps) G
  | .caseSum l r => (l, r)

def asAbort {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases} :
    SInv Old New (.cons .zero ps) G → PUnit
  | .abort => ⟨⟩

def asStoreAtom {Old New : StableCtx sig} {q : Fin sig.nBases} {ps : Pending sig}
    {G : Goal sig.nBases} :
    SInv Old New (.cons (.atom q) ps) G →
      SInv Old (New.snoc (.atom q)) ps G
  | .storeAtom t => t

def asStoreShift {Old New : StableCtx sig} {N : Neg sig.nBases} {ps : Pending sig}
    {G : Goal sig.nBases} :
    SInv Old New (.cons (.shift N) ps) G →
      SInv Old (New.snoc (.neg N)) ps G
  | .storeShift t => t

def asUnit {Old New : StableCtx sig} :
    SInv Old New .empty (.neg .one) → PUnit
  | .unit => ⟨⟩

def asPair {Old New : StableCtx sig} {A B : Neg sig.nBases} :
    SInv Old New .empty (.neg (.prod A B)) →
      SInv Old New .empty (.neg A) × SInv Old New .empty (.neg B)
  | .pair t u => (t, u)

def asLam {Old New : StableCtx sig} {A : Pos sig.nBases} {B : Neg sig.nBases} :
    SInv Old New .empty (.neg (.arr A B)) →
      SInv Old New (.cons A .empty) (.neg B)
  | .lam t => t

def asSatShift {Old New : StableCtx sig} {P : Pos sig.nBases} :
    SInv Old New .empty (.neg (.shift P)) → Sat Old New P
  | .satShift s => s

def asSatPos {Old New : StableCtx sig} {P : Pos sig.nBases} :
    SInv Old New .empty (.pos P) → Sat Old New P
  | .satPos s => s

end SInv

namespace Sat

def asDone {Old New : StableCtx sig} {P : Pos sig.nBases} :
    Sat Old New P → Option (SPosNeu (Old.append New) P)
  | .done v => some v
  | .batch _ _ => none

def asBatch {Old New : StableCtx sig} {P : Pos sig.nBases} :
    Sat Old New P →
      Option ((selected : Pending sig) ×
        NonemptyBatchObs (Old.append New) selected ×
        SInv (Old.append New) .empty selected (.pos P))
  | .batch obs body => some ⟨_, obs, body⟩
  | .done _ => none

end Sat

namespace Foc

def asUp {Γ : StableCtx sig} {Q : Pos sig.nBases} :
    Foc Γ Q → Option (PosNeu Γ Q)
  | .up v => some v
  | .letShift _ _ => none

def asLetShift {Γ : StableCtx sig} {Q : Pos sig.nBases} :
    Foc Γ Q →
      Option ((P : Pos sig.nBases) ×
        NegNeu Γ (.shift P) × Inv Γ (.cons P .empty) (.pos Q))
  | .letShift (P := P) n t => some ⟨P, n, t⟩
  | .up _ => none

end Foc

/-! ### Fixtures -/

namespace Fixtures

def sig0 : Signature := ⟨0, #[]⟩
def sig1 : Signature := ⟨1, #[]⟩

def inv_unit : Inv (sig := sig0) .empty .empty (.neg .one) :=
  .unit

def inv_pair_unit : Inv (sig := sig0) .empty .empty (.neg (.prod .one .one)) :=
  .pair .unit .unit

def inv_lam_unit :
    Inv (sig := sig0) .empty .empty (.neg (.arr (.shift .one) .one)) :=
  .lam (.storeShift .unit)

def inv_abort_zero : Inv (sig := sig0) .empty (.cons .zero .empty) (.neg .one) :=
  .abort

def inv_case_zero_sum :
    Inv (sig := sig0) .empty (.cons (.sum .zero .zero) .empty) (.neg .one) :=
  .caseSum .abort .abort

/-- Ordinary `Foc.letShift`: blur `↓0` and abort under pending `[0]`. -/
def foc_letShift :
    Foc (sig := sig0)
      (StableCtx.snoc .empty (.neg (.shift .zero))) (.shift .one) :=
  .letShift (.var .here) .abort

/-- Ordinary positive focus via `Foc.up (PosNeu.shift ...)`. -/
def foc_up_shift : Foc (sig := sig0) .empty (.shift .one) :=
  .up (.shift .unit)

/-- `Inv.focusPos` after ordinary `letShift`. -/
def inv_focusPos_letShift :
    Inv (sig := sig0)
      (StableCtx.snoc .empty (.neg (.shift .zero))) .empty
      (.pos (.shift .one)) :=
  .focusPos foc_letShift

/-- `Inv.focusShift`: negative-shift goal from ordinary focus. -/
def inv_focusShift :
    Inv (sig := sig0) .empty .empty (.neg (.shift (.shift .one))) :=
  .focusShift foc_up_shift

/-- Atom focus via `focusPos`. -/
def inv_focusPos_atom :
    Inv (sig := sig1)
      (StableCtx.snoc .empty (.atom ⟨0, Nat.zero_lt_one⟩)) .empty
      (.pos (.atom ⟨0, Nat.zero_lt_one⟩)) :=
  .focusPos (.up (.atom .here))

/-- `Sat.done` from `SPosNeu.shift` of saturated unit (empty/empty). -/
def sat_done :
    Sat (sig := sig0) .empty .empty (.shift .one) :=
  .done (.shift (SInv.unit (Old := .empty) (New := .empty)))

/--
Empty-selection saturation with nonempty `New`: atom `q` is strongly
retrievable from `New` alone (`SPosNeu.atom .here`). The old empty-selection
constructor forced `New = []`, so this state was previously unrepresentable.
-/
def sat_done_atom_new :
    Sat (sig := sig1) .empty
      (StableCtx.snoc .empty (.atom ⟨0, Nat.zero_lt_one⟩))
      (.atom ⟨0, Nat.zero_lt_one⟩) :=
  .done (.atom .here)

/-- No-observation saturation entered as a positive goal. -/
def sinv_satPos_done :
    SInv (sig := sig0) .empty .empty .empty (.pos (.shift .one)) :=
  .satPos sat_done

/-- No-observation saturation entered as a negative-shift goal. -/
def sinv_satShift_done :
    SInv (sig := sig0) .empty .empty .empty (.neg (.shift (.shift .one))) :=
  .satShift sat_done

/--
Nonempty atomic batch: one observation `↓0` in `old ++ new`, body aborts under
pending `[0]` toward a positive goal, then `satPos`.
-/
def sinv_batch_one :
    SInv (sig := sig0)
      (StableCtx.snoc .empty (.neg (.shift .zero))) .empty .empty
      (.pos (.shift .one)) :=
  .satPos <|
    .batch
      (.one (.var .here))
      .abort

theorem foc_letShift_invert :
    (Foc.asLetShift foc_letShift).isSome = true := rfl

theorem sat_done_invert :
    (Sat.asDone sat_done).isSome = true := rfl

theorem sat_done_atom_new_invert :
    (Sat.asDone sat_done_atom_new).isSome = true := rfl

theorem inv_focusShift_invert :
    Inv.asFocusShift inv_focusShift = foc_up_shift := rfl

theorem sat_batch_isSome :
    (Sat.asBatch
        (match sinv_batch_one with
          | .satPos s => s)).isSome =
      true := rfl

end Fixtures

end Gimbal.Equality.Scherer
