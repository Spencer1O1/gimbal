/-
  The reference pipeline never leaves the focused fragment.

  Focusing produces a well-focused term, saturation under an admissible
  schedule keeps it well focused, and ICC canonicalization keeps it well
  focused. So every intermediate the reference comparator compares is a legal
  focused term, which is what the structural comparison is entitled to assume.
-/

import Gimbal.Equality.ICCWell
import Gimbal.Equality.SatWell
import Gimbal.Equality.Focus

namespace Gimbal
namespace Equality

variable {sig : Signature}

/--
One reference phase: build the shared schedule for two well-focused terms,
saturate under it, canonicalize. The result is still well focused.
-/
theorem wellInv_referencePhase (fuel : Nat) {Γ : ReachCtx sig.nBases}
    {goal A : Object sig.nBases} {t u : InvTm (Ctx.ofHyps Γ.hyps) A}
    {entries : Array (PairEntry sig Γ.hyps)} {c : CertifiedReachResult sig.nBases}
    {t' : InvTm (Ctx.ofHyps Γ.hyps) A}
    (ht : WellInv t) (hu : WellInv u) (hobs : pairObs Γ goal t u = .ok entries c)
    (h : applyPairObs fuel c.state Γ.hyps entries t = .ok t') :
    WellInv (canonicalize t') :=
  wellInv_canonicalize (wellInv_saturate_pairObs fuel ht hu hobs ht h)

/-- Focusing feeds the pipeline a legal focused term to begin with. -/
theorem wellInv_focus {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) :
    WellInv (focus t) :=
  wellInv_focusTm t

end Equality
end Gimbal
