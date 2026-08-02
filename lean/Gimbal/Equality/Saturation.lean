/-
  Pair-directed saturation scaffolding for Milestone 7.

  Builds one shared schedule from reachability (consistency witnesses that use
  `Γnew`), then wraps an invertible continuation as a saturation-phase term.
  Full recursive application through invertible branches and ICC canonicalization
  come next; this module locks the schedule API.
-/

import Gimbal.Equality.Focus
import Gimbal.Equality.Reachability

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- Convert a snoc context into a reachability context (all hypotheses "new"). -/
def Ctx.toReachCtx : Ctx sig → ReachCtx sig.nBases
  | .empty => ⟨#[], 0⟩
  | .snoc Γ A =>
    let r := Γ.toReachCtx
    ⟨r.hyps.push A, r.newFrom⟩

/-- Reachability context with an explicit old/new split. -/
def Ctx.toReachCtxSplit (Γold Γnew : Ctx sig) : ReachCtx sig.nBases :=
  let old := Γold.toReachCtx
  let neu := Γnew.toReachCtx
  ⟨old.hyps ++ neu.hyps, old.hyps.size⟩

/--
Build the shared saturation schedule for a context/goal from the finite
reachability closure.
-/
def scheduleFor (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases) :
    Schedule sig.nBases :=
  buildSchedule (runReachability Γ goal)

/--
Enter the saturation phase: attach the reachability schedule to an invertible
continuation. Pair-directed comparison will compute one schedule from the
shared context and apply it to both terms via this constructor.
-/
def saturate (Γ : ReachCtx sig.nBases) {Δ : Ctx sig} {A : Object sig.nBases}
    (goal : Object sig.nBases) (cont : InvTm Δ A) : SatTm Δ A :=
  .mk (scheduleFor Γ goal) cont

/-- Saturate under a focused context treated entirely as `Γnew`. -/
def saturateCtx {Γ : Ctx sig} {A : Object sig.nBases}
    (goal : Object sig.nBases) (cont : InvTm Γ A) : SatTm Γ A :=
  saturate Γ.toReachCtx goal cont

/-- Schedule size helper for fixtures. -/
def scheduleSize (s : Schedule sig.nBases) : Nat :=
  s.size

end Equality
end Gimbal
