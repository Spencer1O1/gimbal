/-
  Scherer-core freshness / provenance foundation.

  Variable masks identify caller-`New` binders inside `Old.append New`. Extending
  a mask under `storeAtom` / `storeShift` maps the locally introduced variable to
  `false`, so binder indices alone never count as outer-new.

  `FreshObs` / `SelectedBatch` are the proof-carrying selected API: every nested
  `Sat.batch` observation is checked against that batch's current `New`. Raw
  `Sat` / `NonemptyBatchObs` stay unchanged; search/S4 must return these packages
  rather than unvalidated batches.
-/

import Gimbal.Equality.Scherer.Focused

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Variable masks -/

/-- Boolean mask over stable variables of a context. -/
def VarMask (Γ : StableCtx sig) : Type :=
  ∀ (S : StableTy sig.nBases), StableVar Γ S → Bool

namespace VarMask

/-- Extend under a newest binder; the local variable is never outer-new. -/
def extend {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (m : VarMask Γ) : VarMask (Γ.snoc S)
  | _, .here => false
  | _, .there x => m _ x

/-- The constantly-false mask. -/
def falseMask (Γ : StableCtx sig) : VarMask Γ :=
  fun _ _ => false

theorem extend_falseMask {Γ : StableCtx sig} (S : StableTy sig.nBases) :
    extend (falseMask Γ) (S := S) = falseMask (Γ.snoc S) := by
  funext T x
  cases x <;> rfl

end VarMask

/--
Whether a variable of `Old.append New` arises from the `New` factor.

Defined by recursion on `New` (not by numeric origin indices), so it stays
aligned with `StableCtx.append` / `store*` snoc order.
-/
def isFromNew (Old : StableCtx sig) :
    (New : StableCtx sig) → {S : StableTy sig.nBases} →
      StableVar (Old.append New) S → Bool
  | .empty, _, _ => false
  | .snoc _ _, _, .here => true
  | .snoc Δ _, _, .there x => isFromNew Old Δ x

/-- Mask marking exactly the variables contributed by `New`. -/
def newMask (Old New : StableCtx sig) : VarMask (Old.append New) :=
  fun _ x => isFromNew Old New x

/-- Inject a `New`-side variable into `Old.append New`. -/
def StableVar.fromNew {Old : StableCtx sig} :
    {New : StableCtx sig} → {S : StableTy sig.nBases} →
      StableVar New S → StableVar (Old.append New) S
  | .snoc _ _, _, .here => .here
  | .snoc Δ _, _, .there x => .there (StableVar.fromNew (New := Δ) x)

theorem isFromNew_fromNew {Old : StableCtx sig} :
    ∀ {New : StableCtx sig} {S : StableTy sig.nBases}
      (x : StableVar New S),
      isFromNew Old New (StableVar.fromNew (Old := Old) x) = true
  | .snoc _ _, _, .here => rfl
  | .snoc Δ _, _, .there x => by
      simp only [StableVar.fromNew, isFromNew]
      exact isFromNew_fromNew (Old := Old) (New := Δ) x

theorem isFromNew_weakenAppend {Old : StableCtx sig} {S : StableTy sig.nBases}
    (x : StableVar Old S) :
    ∀ (New : StableCtx sig),
      isFromNew Old New (StableVar.weakenAppend New x) = false
  | .empty => rfl
  | .snoc Δ _ => by
      simp only [StableVar.weakenAppend, isFromNew]
      exact isFromNew_weakenAppend x Δ

theorem newMask_eq_falseMask_of_empty (Old : StableCtx sig) :
    newMask Old .empty = (VarMask.falseMask Old : VarMask (Old.append .empty)) := by
  funext S x
  rfl

/-! ### Saturated `uses` (Boolean OR over masked variables) -/

mutual
def SNegNeu.uses {Γ : StableCtx sig} {N : Neg sig.nBases}
    (m : VarMask Γ) : SNegNeu Γ N → Bool
  | .var x => m _ x
  | .fst n => SNegNeu.uses m n
  | .snd n => SNegNeu.uses m n
  | .app n p => SNegNeu.uses m n || SPosNeu.uses m p

def SPosNeu.uses {Γ : StableCtx sig} {P : Pos sig.nBases}
    (m : VarMask Γ) : SPosNeu Γ P → Bool
  | .atom x => m _ x
  | .inl p => SPosNeu.uses m p
  | .inr p => SPosNeu.uses m p
  | .shift t => SInv.uses (Old := Γ) (New := .empty) m t

def NonemptyBatchObs.anyUses {Γ : StableCtx sig} {ps : Pending sig}
    (m : VarMask Γ) : NonemptyBatchObs Γ ps → Bool
  | .one n => SNegNeu.uses m n
  | .cons n rest => SNegNeu.uses m n || NonemptyBatchObs.anyUses m rest

def NonemptyBatchObs.allUses {Γ : StableCtx sig} {ps : Pending sig}
    (m : VarMask Γ) : NonemptyBatchObs Γ ps → Bool
  | .one n => SNegNeu.uses m n
  | .cons n rest => SNegNeu.uses m n && NonemptyBatchObs.allUses m rest

def Sat.uses {Old New : StableCtx sig} {P : Pos sig.nBases}
    (m : VarMask (Old.append New)) : Sat Old New P → Bool
  | .inconsistent z => SNegNeu.uses m z
  | .done v => SPosNeu.uses m v
  | .batch obs body =>
      NonemptyBatchObs.anyUses m obs ||
        SInv.uses (Old := Old.append New) (New := .empty) m body

def SInv.uses {Old New : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
    (m : VarMask (Old.append New)) : SInv Old New ps G → Bool
  | .unit => false
  | .abort => false
  | .pair t u => SInv.uses m t || SInv.uses m u
  | .lam t => SInv.uses m t
  | .caseSum l r => SInv.uses m l || SInv.uses m r
  | .storeAtom (q := q) t =>
      SInv.uses (Old := Old) (New := New.snoc (.atom q))
        (VarMask.extend (S := .atom q) m) t
  | .storeShift (N := N) t =>
      SInv.uses (Old := Old) (New := New.snoc (.neg N))
        (VarMask.extend (S := .neg N) m) t
  | .satShift s => Sat.uses m s
  | .satPos s => Sat.uses m s
end

/-! ### Nested batch validity (`freshValid`) -/

mutual
/--
Structural validity: every nested `Sat.batch` observation uses that batch's
current `New` (via `newMask`), and every observation itself is recursively
fresh-valid. Does not assume root `New = []` implies batch-free.
-/
def SNegNeu.freshValid {Γ : StableCtx sig} {N : Neg sig.nBases} :
    SNegNeu Γ N → Bool
  | .var _ => true
  | .fst n => SNegNeu.freshValid n
  | .snd n => SNegNeu.freshValid n
  | .app n p => SNegNeu.freshValid n && SPosNeu.freshValid p

def SPosNeu.freshValid {Γ : StableCtx sig} {P : Pos sig.nBases} :
    SPosNeu Γ P → Bool
  | .atom _ => true
  | .inl p => SPosNeu.freshValid p
  | .inr p => SPosNeu.freshValid p
  | .shift t => SInv.freshValid t

/-- Recursively check `SNegNeu.freshValid` on every batch observation. -/
def NonemptyBatchObs.allFreshValid {Γ : StableCtx sig} {ps : Pending sig} :
    NonemptyBatchObs Γ ps → Bool
  | .one n => SNegNeu.freshValid n
  | .cons n rest => SNegNeu.freshValid n && NonemptyBatchObs.allFreshValid rest

def Sat.freshValid {Old New : StableCtx sig} {P : Pos sig.nBases} :
    Sat Old New P → Bool
  | .inconsistent z => SNegNeu.freshValid z
  | .done v => SPosNeu.freshValid v
  | .batch obs body =>
      NonemptyBatchObs.allUses (newMask Old New) obs &&
        NonemptyBatchObs.allFreshValid obs &&
        SInv.freshValid body

def SInv.freshValid {Old New : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} : SInv Old New ps G → Bool
  | .unit => true
  | .abort => true
  | .pair t u => SInv.freshValid t && SInv.freshValid u
  | .lam t => SInv.freshValid t
  | .caseSum l r => SInv.freshValid l && SInv.freshValid r
  | .storeAtom t => SInv.freshValid t
  | .storeShift t => SInv.freshValid t
  | .satShift s => Sat.freshValid s
  | .satPos s => Sat.freshValid s
end

/-! ### False-mask lemmas -/

mutual
theorem SNegNeu.uses_falseMask {Γ : StableCtx sig} {N : Neg sig.nBases} :
    ∀ (n : SNegNeu Γ N), SNegNeu.uses (VarMask.falseMask Γ) n = false
  | .var _ => rfl
  | .fst n => SNegNeu.uses_falseMask n
  | .snd n => SNegNeu.uses_falseMask n
  | .app n p => by
      simp only [SNegNeu.uses, SNegNeu.uses_falseMask n, SPosNeu.uses_falseMask p,
        Bool.or_self]

theorem SPosNeu.uses_falseMask {Γ : StableCtx sig} {P : Pos sig.nBases} :
    ∀ (p : SPosNeu Γ P), SPosNeu.uses (VarMask.falseMask Γ) p = false
  | .atom _ => rfl
  | .inl p => SPosNeu.uses_falseMask p
  | .inr p => SPosNeu.uses_falseMask p
  | .shift t => by
      simpa [SPosNeu.uses] using
        SInv.uses_falseMask (Old := Γ) (New := .empty) t

theorem NonemptyBatchObs.anyUses_falseMask {Γ : StableCtx sig} {ps : Pending sig} :
    ∀ (obs : NonemptyBatchObs Γ ps),
      NonemptyBatchObs.anyUses (VarMask.falseMask Γ) obs = false
  | .one n => SNegNeu.uses_falseMask n
  | .cons n rest => by
      simp only [NonemptyBatchObs.anyUses, SNegNeu.uses_falseMask n,
        NonemptyBatchObs.anyUses_falseMask rest, Bool.or_self]

theorem NonemptyBatchObs.allUses_falseMask {Γ : StableCtx sig} {ps : Pending sig} :
    ∀ (obs : NonemptyBatchObs Γ ps),
      NonemptyBatchObs.allUses (VarMask.falseMask Γ) obs = false
  | .one n => SNegNeu.uses_falseMask n
  | .cons n rest => by
      simp only [NonemptyBatchObs.allUses, SNegNeu.uses_falseMask n,
        Bool.false_and]

theorem Sat.uses_falseMask {Old New : StableCtx sig} {P : Pos sig.nBases} :
    ∀ (s : Sat Old New P),
      Sat.uses (VarMask.falseMask (Old.append New)) s = false
  | .inconsistent z => SNegNeu.uses_falseMask z
  | .done v => SPosNeu.uses_falseMask v
  | .batch obs body => by
      simp only [Sat.uses, NonemptyBatchObs.anyUses_falseMask obs, Bool.false_or]
      exact SInv.uses_falseMask (Old := Old.append New) (New := .empty) body

theorem SInv.uses_falseMask {Old New : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} :
    ∀ (t : SInv Old New ps G),
      SInv.uses (VarMask.falseMask (Old.append New)) t = false
  | .unit => rfl
  | .abort => rfl
  | .pair t u => by
      simp only [SInv.uses, SInv.uses_falseMask t, SInv.uses_falseMask u,
        Bool.or_self]
  | .lam t => SInv.uses_falseMask t
  | .caseSum l r => by
      simp only [SInv.uses, SInv.uses_falseMask l, SInv.uses_falseMask r,
        Bool.or_self]
  | .storeAtom (q := q) t => by
      simp only [SInv.uses]
      rw [show VarMask.extend (S := .atom q) (VarMask.falseMask (Old.append New)) =
            VarMask.falseMask (Old.append (New.snoc (.atom q))) from
          VarMask.extend_falseMask (S := .atom q)]
      exact SInv.uses_falseMask (Old := Old) (New := New.snoc (.atom q)) t
  | .storeShift (N := N) t => by
      simp only [SInv.uses]
      rw [show VarMask.extend (S := .neg N) (VarMask.falseMask (Old.append New)) =
            VarMask.falseMask (Old.append (New.snoc (.neg N))) from
          VarMask.extend_falseMask (S := .neg N)]
      exact SInv.uses_falseMask (Old := Old) (New := New.snoc (.neg N)) t
  | .satShift s => Sat.uses_falseMask s
  | .satPos s => Sat.uses_falseMask s
end

/-! ### Proof-carrying selected observations -/

structure FreshObs (Old New : StableCtx sig) (P : Pos sig.nBases) where
  neu : SNegNeu (Old.append New) (.shift P)
  usesNew : neu.uses (newMask Old New) = true
  valid : neu.freshValid = true

inductive SelectedBatch (Old New : StableCtx sig) : Pending sig → Type where
  | one {P : Pos sig.nBases} :
      FreshObs Old New P →
      SelectedBatch Old New (.cons P .empty)
  | cons {P : Pos sig.nBases} {ps : Pending sig} :
      FreshObs Old New P →
      SelectedBatch Old New ps →
      SelectedBatch Old New (.cons P ps)

namespace SelectedBatch

def toNonemptyBatchObs {Old New : StableCtx sig} {ps : Pending sig} :
    SelectedBatch Old New ps → NonemptyBatchObs (Old.append New) ps
  | .one o => .one o.neu
  | .cons o rest => .cons o.neu (toNonemptyBatchObs rest)

/-- Pending results carried by a selected batch (always nonempty). -/
def results {Old New : StableCtx sig} {ps : Pending sig} :
    SelectedBatch Old New ps → List (Pos sig.nBases)
  | .one (P := P) _ => [P]
  | .cons (P := P) _ rest => P :: results rest

def pendingResults : Pending sig → List (Pos sig.nBases)
  | .empty => []
  | .cons P ps => P :: pendingResults ps

theorem results_eq_pending {Old New : StableCtx sig} :
    ∀ {ps : Pending sig} (b : SelectedBatch Old New ps),
      results b = pendingResults ps
  | _, .one _ => rfl
  | _, .cons _ rest => by
      simp only [results, pendingResults, results_eq_pending rest]

theorem nonempty_results {Old New : StableCtx sig} :
    ∀ {ps : Pending sig} (b : SelectedBatch Old New ps),
      results b ≠ []
  | _, .one _ => by simp [results]
  | _, .cons _ _ => by simp [results]

/-- Every packed observation uses the shared pre-batch `New` mask. -/
theorem all_entries_use_newMask {Old New : StableCtx sig} :
    ∀ {ps : Pending sig} (b : SelectedBatch Old New ps),
      NonemptyBatchObs.allUses (newMask Old New) (toNonemptyBatchObs b) = true
  | _, .one o => o.usesNew
  | _, .cons o rest => by
      simp only [toNonemptyBatchObs, NonemptyBatchObs.allUses, o.usesNew,
        all_entries_use_newMask rest, Bool.true_and]

/-- Every packed observation carries nested-batch validity. -/
theorem all_entries_freshValid {Old New : StableCtx sig} :
    ∀ {ps : Pending sig} (b : SelectedBatch Old New ps),
      NonemptyBatchObs.allFreshValid (toNonemptyBatchObs b) = true
  | _, .one o => o.valid
  | _, .cons o rest => by
      simp only [toNonemptyBatchObs, NonemptyBatchObs.allFreshValid, o.valid,
        all_entries_freshValid rest, Bool.true_and]

end SelectedBatch

/-- An outer-empty `New` cannot inhabit `FreshObs`. -/
theorem FreshObs.false_of_new_empty {Old : StableCtx sig} {P : Pos sig.nBases}
    (o : FreshObs Old .empty P) : False := by
  have hfalse : o.neu.uses (newMask Old .empty) = false := by
    rw [newMask_eq_falseMask_of_empty]
    exact SNegNeu.uses_falseMask o.neu
  exact Bool.noConfusion (o.usesNew.symm.trans hfalse)

/-! ### Fixtures -/

namespace FreshnessFixtures

open Fixtures

/-- Old-only atom under empty `New`: uses is false. -/
def oldOnly_atom :
    SPosNeu (sig := sig1)
      (StableCtx.snoc .empty (.atom ⟨0, Nat.zero_lt_one⟩))
      (.atom ⟨0, Nat.zero_lt_one⟩) :=
  .atom .here

theorem oldOnly_atom_uses_false :
    oldOnly_atom.uses (newMask
      (StableCtx.snoc (.empty : StableCtx sig1) (.atom ⟨0, Nat.zero_lt_one⟩))
      .empty) = false := by
  native_decide

/-- Same atom drawn from nonempty `New`: uses is true. -/
def newSide_atom :
    SPosNeu (sig := sig1)
      (StableCtx.append .empty
        (StableCtx.snoc .empty (.atom ⟨0, Nat.zero_lt_one⟩)))
      (.atom ⟨0, Nat.zero_lt_one⟩) :=
  .atom .here

theorem newSide_atom_uses_true :
    newSide_atom.uses (newMask (.empty : StableCtx sig1)
      (StableCtx.snoc .empty (.atom ⟨0, Nat.zero_lt_one⟩))) = true := by
  native_decide

/--
Store-local variable under an outer mask that marks a different `New`.
The locally introduced binder is mapped to `false` by `VarMask.extend`.
-/
theorem store_local_not_outer_new :
    let Old : StableCtx sig1 := .empty
    let New : StableCtx sig1 :=
      StableCtx.snoc .empty (.atom ⟨0, Nat.zero_lt_one⟩)
    let m := newMask Old New
    let m' := VarMask.extend (S := .neg (.shift (.zero : Pos 1))) m
    m' _ (StableVar.here
      (Γ := Old.append New)
      (S := .neg (.shift (.zero : Pos 1)))) = false := by
  native_decide

/--
Lambda/store-local: after extending an outer caller-`New` mask, the newest
local binder is `false` (does not satisfy the outer freshness mask).
-/
theorem lam_store_local_not_outer_new :
    let Old : StableCtx sig0 := .empty
    let outerNew : StableCtx sig0 :=
      StableCtx.snoc .empty (.neg (.shift (.zero : Pos 0)))
    let m := newMask Old outerNew
    let m' := VarMask.extend (S := .neg (.shift (.zero : Pos 0))) m
    m' _ (StableVar.here
      (Γ := Old.append outerNew)
      (S := .neg (.shift (.zero : Pos 0)))) = false := by
  native_decide

/--
Nested batch after `storeShift`: pending `↓↓0` stores binder `¬↓0`, which
becomes that batch's current `New`. Observation `.var .here` uses New and
`freshValid` holds — even though the outer `New` was empty.
-/
def nested_batch_after_store :
    SInv (sig := sig0) .empty .empty
      (.cons (.shift (.shift .zero)) .empty) (.pos (.shift .one)) :=
  .storeShift <|
    .satPos <|
      .batch (.one (.var .here)) .abort

theorem nested_batch_after_store_freshValid :
    nested_batch_after_store.freshValid = true := by
  native_decide

/--
Root `New = []` does not mean batch-free: the nested batch above is validated
against its own (nonempty) New after the store.
-/
theorem freshValid_checks_nested_not_root_empty :
    nested_batch_after_store.freshValid = true ∧
      (∃ (s : Sat (sig := sig0) .empty
            (StableCtx.snoc .empty (.neg (.shift .zero)))
            (.shift .one)),
        Sat.freshValid s = true) := by
  refine ⟨nested_batch_after_store_freshValid, ?_⟩
  refine ⟨.batch (.one (.var .here)) .abort, ?_⟩
  native_decide

/--
Raw old-only batch at empty `New`: observations cannot use New, so
`Sat.freshValid` rejects it.
-/
def raw_oldOnly_batch :
    Sat (sig := sig0)
      (StableCtx.snoc .empty (.neg (.shift .zero)))
      .empty
      (.shift .one) :=
  .batch (.one (.var .here)) .abort

theorem raw_oldOnly_batch_freshValid_false :
    raw_oldOnly_batch.freshValid = false := by
  native_decide

theorem sat_inconsistent_old_freshValid {P : Pos 0} :
    (sat_inconsistent_old (P := P)).freshValid = true :=
  rfl

theorem sat_inconsistent_new_freshValid {P : Pos 0} :
    (sat_inconsistent_new (P := P)).freshValid = true :=
  rfl

/--
Outer observation uses a New function head, so `allUses` holds, but a shifted
application argument embeds an old-only nested batch. That nested batch fails
`freshValid`, so `allFreshValid` and the outer `Sat.freshValid` are false.
-/
def usesNew_but_nested_oldOnly_invalid_obs :
    NonemptyBatchObs (sig := sig0)
      (StableCtx.append
        (StableCtx.snoc .empty (.neg (.shift .zero)))
        (StableCtx.snoc .empty
          (.neg (.arr (.shift (.shift (.shift .one))) (.shift .zero)))))
      (.cons (.zero : Pos 0) .empty) :=
  .one
    (.app (.var .here)
      (.shift
        (.satShift
          (.batch (.one (.var (.there .here))) .abort))))

def usesNew_but_nested_oldOnly_invalid :
    Sat (sig := sig0)
      (StableCtx.snoc .empty (.neg (.shift .zero)))
      (StableCtx.snoc .empty
        (.neg (.arr (.shift (.shift (.shift .one))) (.shift .zero))))
      (.shift .one) :=
  .batch usesNew_but_nested_oldOnly_invalid_obs .abort

theorem usesNew_but_nested_oldOnly_invalid_allUses :
    NonemptyBatchObs.allUses
      (newMask
        (StableCtx.snoc (.empty : StableCtx sig0) (.neg (.shift .zero)))
        (StableCtx.snoc .empty
          (.neg (.arr (.shift (.shift (.shift .one))) (.shift .zero)))))
      usesNew_but_nested_oldOnly_invalid_obs = true := by
  native_decide

theorem usesNew_but_nested_oldOnly_invalid_allFreshValid_false :
    NonemptyBatchObs.allFreshValid usesNew_but_nested_oldOnly_invalid_obs =
      false := by
  native_decide

theorem usesNew_but_nested_oldOnly_invalid_freshValid_false :
    usesNew_but_nested_oldOnly_invalid.freshValid = false := by
  native_decide

/-- Inconsistency inherits recursive validity; it cannot hide a bad nested batch. -/
def inconsistent_nested_invalid :
    Sat (sig := sig0)
      (StableCtx.snoc .empty (.neg (.shift .zero)))
      (StableCtx.snoc .empty
        (.neg (.arr (.shift (.shift (.shift .one))) (.shift .zero))))
      (.shift .one) :=
  match usesNew_but_nested_oldOnly_invalid_obs with
  | .one z => .inconsistent z

theorem inconsistent_nested_invalid_freshValid_false :
    inconsistent_nested_invalid.freshValid = false := by
  native_decide

/-- Selected packing of a New-side observation. -/
def selected_one_new :
    SelectedBatch (sig := sig0) .empty
      (StableCtx.snoc .empty (.neg (.shift .zero)))
      (.cons (.zero : Pos 0) .empty) :=
  .one ⟨
    .var .here,
    by native_decide,
    by native_decide
  ⟩

theorem selected_one_new_results :
    SelectedBatch.results selected_one_new = [.zero] := rfl

theorem selected_one_new_toBatch_allUses :
    NonemptyBatchObs.allUses
      (newMask (.empty : StableCtx sig0)
        (StableCtx.snoc .empty (.neg (.shift .zero))))
      (SelectedBatch.toNonemptyBatchObs selected_one_new) = true := by
  native_decide

end FreshnessFixtures

end Gimbal.Equality.Scherer
