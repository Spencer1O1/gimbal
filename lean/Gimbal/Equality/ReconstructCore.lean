/-
  Shared reconstruction command/value vocabulary and hypothesis lookup.

  Used by both the well-founded worker (`ReconstructWF`) and saturation's
  schedule application. Kept free of fueled/WF algorithms so either side can
  own the recursive implementation without an import cycle.
-/

import Gimbal.Equality.Focus
import Gimbal.Equality.Reachability

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- Find a hypothesis with exact type `A` (oldest wins). -/
def findHypVar (hyps : Array (Object sig.nBases)) (A : Object sig.nBases) :
    Option (Var (Ctx.ofHyps hyps) A) :=
  Id.run do
    for i in [:hyps.size] do
      match Ctx.varOldest hyps i with
      | some ⟨B, x⟩ =>
        if h : B = A then
          return some (h ▸ x)
        else
          pure ()
      | none => pure ()
    return none

inductive ReconstructCmd (sig : Signature) where
  | neuOf (hyps : Array (Object sig.nBases)) (A : Object sig.nBases)
  | witness (hyps : Array (Object sig.nBases)) (w : Witness)
  | invOf (hyps : Array (Object sig.nBases)) (A : Object sig.nBases)

inductive ReconstructVal (sig : Signature) where
  | neu (hyps : Array (Object sig.nBases)) (A : Object sig.nBases)
      (n : NegNeu (Ctx.ofHyps hyps) A) : ReconstructVal sig
  | wit (hyps : Array (Object sig.nBases))
      (p : (A : Object sig.nBases) × NegNeu (Ctx.ofHyps hyps) A) : ReconstructVal sig
  | inv (hyps : Array (Object sig.nBases)) (A : Object sig.nBases)
      (t : InvTm (Ctx.ofHyps hyps) A) : ReconstructVal sig

end Equality
end Gimbal
