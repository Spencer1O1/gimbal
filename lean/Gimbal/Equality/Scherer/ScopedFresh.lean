/-
  Scherer-core scoped freshness equivalence.

  `ScopedFresh*` is the exact raw-support reading of nested batch validity:
  every batch entry must hit that batch's `newLevels`, and recursive structure
  matches `freshValid`. Equivalence theorems close the bridge to `FreshObs`.
-/

import Gimbal.Equality.Scherer.RawSupport

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Scoped freshness (raw-support formulation) -/

mutual
/-- Structural scoped freshness of a saturated negative neutral. -/
def ScopedFreshNeg {Γ : StableCtx sig} {N : Neg sig.nBases} : SNegNeu Γ N → Bool
  | .var _ => true
  | .fst n => ScopedFreshNeg n
  | .snd n => ScopedFreshNeg n
  | .app n p => ScopedFreshNeg n && ScopedFreshPos p

/-- Structural scoped freshness of a saturated positive neutral. -/
def ScopedFreshPos {Γ : StableCtx sig} {P : Pos sig.nBases} : SPosNeu Γ P → Bool
  | .atom _ => true
  | .inl p => ScopedFreshPos p
  | .inr p => ScopedFreshPos p
  | .shift t => ScopedFreshInv (Old := Γ) (New := .empty) t

/-- Every batch observation is recursively scoped-fresh. -/
def ScopedFreshBatch {Γ : StableCtx sig} {ps : Pending sig} :
    NonemptyBatchObs Γ ps → Bool
  | .one n => ScopedFreshNeg n
  | .cons n rest => ScopedFreshNeg n && ScopedFreshBatch rest

/--
Scoped freshness of a saturation judgment.
`batch` requires: every observation hits `newLevels Old New`, every observation
is recursively scoped-fresh, and the body is scoped-fresh at
`(Old.append New, empty)`.
-/
def ScopedFreshSat {Old New : StableCtx sig} {P : Pos sig.nBases} :
    Sat Old New P → Bool
  | .inconsistent z => ScopedFreshNeg z
  | .done v => ScopedFreshPos v
  | .batch obs body =>
      NonemptyBatchObs.allHits (newLevels Old New) obs &&
        ScopedFreshBatch obs &&
        ScopedFreshInv (Old := Old.append New) (New := .empty) body

/-- Scoped freshness of saturated inversion. -/
def ScopedFreshInv {Old New : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} : SInv Old New ps G → Bool
  | .unit => true
  | .abort => true
  | .pair t u => ScopedFreshInv t && ScopedFreshInv u
  | .lam t => ScopedFreshInv t
  | .caseSum l r => ScopedFreshInv l && ScopedFreshInv r
  | .storeAtom t => ScopedFreshInv t
  | .storeShift t => ScopedFreshInv t
  | .satShift s => ScopedFreshSat s
  | .satPos s => ScopedFreshSat s
end

/-! ### Equivalence with `freshValid` -/

private theorem allUses_newMask_eq_allHits_newLevels
    {Old New : StableCtx sig} {ps : Pending sig}
    (obs : NonemptyBatchObs (Old.append New) ps) :
    NonemptyBatchObs.allUses (newMask Old New) obs =
      NonemptyBatchObs.allHits (newLevels Old New) obs := by
  have hmask := maskOf_newLevels Old New
  calc
    NonemptyBatchObs.allUses (newMask Old New) obs
        = NonemptyBatchObs.allUses (RawSupport.maskOf (newLevels Old New)) obs := by
          rw [← hmask]
    _ = NonemptyBatchObs.allHits (newLevels Old New) obs :=
      NonemptyBatchObs.allUses_rawSupport_iff (newLevels Old New) obs

mutual
theorem SNegNeu.freshValid_iff_scopedFresh {Γ : StableCtx sig} {N : Neg sig.nBases} :
    ∀ (n : SNegNeu Γ N), SNegNeu.freshValid n = ScopedFreshNeg n
  | .var _ => rfl
  | .fst n => SNegNeu.freshValid_iff_scopedFresh n
  | .snd n => SNegNeu.freshValid_iff_scopedFresh n
  | .app n p => by
      simp only [SNegNeu.freshValid, ScopedFreshNeg,
        SNegNeu.freshValid_iff_scopedFresh n,
        SPosNeu.freshValid_iff_scopedFresh p]

theorem SPosNeu.freshValid_iff_scopedFresh {Γ : StableCtx sig} {P : Pos sig.nBases} :
    ∀ (p : SPosNeu Γ P), SPosNeu.freshValid p = ScopedFreshPos p
  | .atom _ => rfl
  | .inl p => SPosNeu.freshValid_iff_scopedFresh p
  | .inr p => SPosNeu.freshValid_iff_scopedFresh p
  | .shift t => by
      simpa [SPosNeu.freshValid, ScopedFreshPos] using
        SInv.freshValid_iff_scopedFresh (Old := Γ) (New := .empty) t

theorem NonemptyBatchObs.allFreshValid_iff_scopedFresh {Γ : StableCtx sig}
    {ps : Pending sig} :
    ∀ (obs : NonemptyBatchObs Γ ps),
      NonemptyBatchObs.allFreshValid obs = ScopedFreshBatch obs
  | .one n => SNegNeu.freshValid_iff_scopedFresh n
  | .cons n rest => by
      simp only [NonemptyBatchObs.allFreshValid, ScopedFreshBatch,
        SNegNeu.freshValid_iff_scopedFresh n,
        NonemptyBatchObs.allFreshValid_iff_scopedFresh rest]

theorem Sat.freshValid_iff_scopedFresh {Old New : StableCtx sig}
    {P : Pos sig.nBases} :
    ∀ (s : Sat Old New P), Sat.freshValid s = ScopedFreshSat s
  | .inconsistent z => by
      simpa [Sat.freshValid, ScopedFreshSat] using
        SNegNeu.freshValid_iff_scopedFresh z
  | .done v => by
      simpa [Sat.freshValid, ScopedFreshSat] using
        SPosNeu.freshValid_iff_scopedFresh v
  | .batch obs body => by
      simp only [Sat.freshValid, ScopedFreshSat,
        allUses_newMask_eq_allHits_newLevels obs,
        NonemptyBatchObs.allFreshValid_iff_scopedFresh obs]
      exact congrArg _ (SInv.freshValid_iff_scopedFresh
        (Old := Old.append New) (New := .empty) body)

theorem SInv.freshValid_iff_scopedFresh {Old New : StableCtx sig}
    {ps : Pending sig} {G : Goal sig.nBases} :
    ∀ (t : SInv Old New ps G), SInv.freshValid t = ScopedFreshInv t
  | .unit => rfl
  | .abort => rfl
  | .pair t u => by
      simp only [SInv.freshValid, ScopedFreshInv,
        SInv.freshValid_iff_scopedFresh t, SInv.freshValid_iff_scopedFresh u]
  | .lam t => SInv.freshValid_iff_scopedFresh t
  | .caseSum l r => by
      simp only [SInv.freshValid, ScopedFreshInv,
        SInv.freshValid_iff_scopedFresh l, SInv.freshValid_iff_scopedFresh r]
  | .storeAtom t => SInv.freshValid_iff_scopedFresh t
  | .storeShift t => SInv.freshValid_iff_scopedFresh t
  | .satShift s => by
      simpa [SInv.freshValid, ScopedFreshInv] using Sat.freshValid_iff_scopedFresh s
  | .satPos s => by
      simpa [SInv.freshValid, ScopedFreshInv] using Sat.freshValid_iff_scopedFresh s
end

/-! ### `FreshObs` boundary -/

private theorem uses_newMask_iff_hits_newLevels {Old New : StableCtx sig}
    {N : Neg sig.nBases} (n : SNegNeu (Old.append New) N) :
    n.uses (newMask Old New) = true ↔
      RawSupport.hits n.rawSupport (newLevels Old New) = true := by
  have h := SNegNeu.uses_rawSupport (newLevels Old New) n
  rw [maskOf_newLevels] at h
  constructor
  · intro huses
    rw [← h, huses]
  · intro hhits
    rw [h, hhits]

theorem freshObs_nonempty_iff {Old New : StableCtx sig} {P : Pos sig.nBases} :
    Nonempty (FreshObs Old New P) ↔
      ∃ n : SNegNeu (Old.append New) (.shift P),
        RawSupport.hits n.rawSupport (newLevels Old New) = true ∧
          ScopedFreshNeg n = true := by
  constructor
  · rintro ⟨⟨n, huses, hvalid⟩⟩
    refine ⟨n, (uses_newMask_iff_hits_newLevels n).mp huses, ?_⟩
    rw [← SNegNeu.freshValid_iff_scopedFresh]
    exact hvalid
  · rintro ⟨n, hhits, hsf⟩
    refine ⟨⟨n, (uses_newMask_iff_hits_newLevels n).mpr hhits, ?_⟩⟩
    rw [SNegNeu.freshValid_iff_scopedFresh]
    exact hsf

/-! ### Adversarial regressions -/

namespace ScopedFreshFixtures

open Fixtures FreshnessFixtures

/--
Existing outer-uses-New / nested-old-only fixture: hits the outer New mask, but
is not `ScopedFresh` (nested batch fails recursive freshness).
-/
theorem outer_hits_but_not_scopedFresh :
    let Old : StableCtx sig0 :=
      StableCtx.snoc .empty (.neg (.shift .zero))
    let New : StableCtx sig0 :=
      StableCtx.snoc .empty
        (.neg (.arr (.shift (.shift (.shift .one))) (.shift .zero)))
    let K := newLevels Old New
    RawSupport.hits usesNew_but_nested_oldOnly_invalid_obs.rawSupport K = true ∧
      ScopedFreshBatch usesNew_but_nested_oldOnly_invalid_obs = false ∧
      ScopedFreshSat usesNew_but_nested_oldOnly_invalid = false := by
  refine ⟨?hits, ?batch, ?sat⟩
  · native_decide
  · rw [← NonemptyBatchObs.allFreshValid_iff_scopedFresh]
    exact usesNew_but_nested_oldOnly_invalid_allFreshValid_false
  · rw [← Sat.freshValid_iff_scopedFresh]
    exact usesNew_but_nested_oldOnly_invalid_freshValid_false

/--
Store-local variable may validate its nested current batch, but after pop it
cannot satisfy an enclosing caller-`New` requirement (local level is gone).
-/
theorem store_local_cannot_satisfy_enclosing_new :
    let Old : StableCtx sig0 := .empty
    let New : StableCtx sig0 :=
      StableCtx.snoc .empty (.neg (.shift .zero))
    let localS : StableTy 0 := .neg (.shift .zero)
    let nestedNew := New.snoc localS
    let nestedK := newLevels Old nestedNew
    let localLevel : StableLevel (Old.append nestedNew) := Fin.last _
    RawSupport.hits ({localLevel} : RawSupport _) nestedK = true ∧
      RawSupport.hits (popSupport (S := localS) {localLevel})
        (newLevels Old New) = false := by
  native_decide

/--
`Sat.done` may be scoped-fresh while mentioning only Old binders: scoped
freshness is not equivalent to one global support ∩ New check.
-/
theorem sat_done_scopedFresh_oldOnly :
    let Old : StableCtx sig0 :=
      StableCtx.snoc .empty (.neg (.shift .zero))
    let New : StableCtx sig0 := .empty
    let s : Sat (sig := sig0) Old New (.shift .one) :=
      .done (.shift .unit)
    ScopedFreshSat s = true ∧
      RawSupport.hits s.rawSupport (newLevels Old New) = false := by
  native_decide

/--
In a multi-entry batch, every entry — not merely their union — must hit
current New.
-/
theorem multi_entry_every_obs_must_hit_new :
    let Old : StableCtx sig0 :=
      StableCtx.snoc .empty (.neg (.shift (.zero : Pos 0)))
    let New : StableCtx sig0 :=
      StableCtx.snoc .empty (.neg (.shift (.zero : Pos 0)))
    let K := newLevels Old New
    RawSupport.hits (NonemptyBatchObs.rawSupport RawSupportFixtures.two_obs) K =
        true ∧
      NonemptyBatchObs.allHits K RawSupportFixtures.two_obs = false := by
  native_decide

end ScopedFreshFixtures

end Gimbal.Equality.Scherer
