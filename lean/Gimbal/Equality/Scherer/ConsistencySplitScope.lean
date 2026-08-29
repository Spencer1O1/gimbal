/-
  Syntax-split realization for generative consistency batches.

  A flat `ConsistencyScope` remembers the realized current-round mask but not
  which suffix of its intrinsic context is the focused syntax's `New`.
  `SplitConsistencyScope` supplies exactly that missing link.  It changes
  neither focused syntax nor normalized query keys.
-/

import Gimbal.Equality.Scherer.ConsistencyScope

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-- The realized current-round mask is exactly the variables contributed by
the syntax-level `New` suffix.  The ambient context equality is intrinsic in
the type of `s`. -/
structure SplitConsistencyScope {U : SearchUniverse sig} {O : Type}
    {B : Nat} (Old New : StableCtx sig)
    (s : ConsistencyScope U O B (Old.append New)) : Prop where
  current_eq : ∀ {S : StableTy sig.nBases}
    (x : StableVar (Old.append New) S),
    s.current S x = newMask Old New S x

namespace SplitConsistencyScope

variable {U : SearchUniverse sig} {O : Type} {B : Nat}
  {Old New : StableCtx sig}
  {s : ConsistencyScope U O B (Old.append New)}

/-- Function equality form of the pointwise split contract. -/
theorem current_mask_eq (split : SplitConsistencyScope Old New s) :
    s.current = newMask Old New := by
  funext S x
  exact split.current_eq x

/-- A round reset has empty syntax `New` and an everywhere-false current mask. -/
theorem resetRound (s : ConsistencyScope U O B Old) :
    SplitConsistencyScope Old .empty s.resetRound where
  current_eq := by
    intro S x
    rw [s.resetRound_current_false x]
    rfl

/-- Changing coverage does not change split realization. -/
theorem withCoverage (split : SplitConsistencyScope Old New s)
    (coverage : Finset (Obligation U O)) :
    SplitConsistencyScope Old New (s.withCoverage coverage) where
  current_eq := split.current_eq

/-- A resolved store extends both the realized current mask and syntax `New`
by the same newest variable. -/
theorem pushResolved (split : SplitConsistencyScope Old New s)
    (hd : s.state.depth < B) (S : UStable U) (K : DepSupport O) :
    SplitConsistencyScope Old (New.snoc S.val) (s.pushResolved hd S K) where
  current_eq := by
    intro T x
    cases x with
    | here =>
        rw [s.pushResolved_current_here hd S K]
        rfl
    | there x =>
        rw [s.pushResolved_current_there hd S K x]
        exact split.current_eq x

end SplitConsistencyScope

end Gimbal.Equality.Scherer
