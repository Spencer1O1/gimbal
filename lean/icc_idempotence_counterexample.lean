/-
  Regression: `canonicalize` is idempotent on the former counterexample.

  Previously `canonicalize (canonicalize tm) ≠ canonicalize tm` because
  `caseCommute` past a pair left a coprod η-redex in a component. Fixed by
  routing every emitted `case` through `mkCase`.
-/

import Gimbal

namespace Gimbal
namespace Equality

abbrev TSig : Signature := ⟨2, #[]⟩

def tHyps : Array (Object 2) := #[.coprod (.base 0) (.base 1)]
abbrev TCtx : Ctx TSig := Ctx.ofHyps tHyps

def tN : NegNeu TCtx (.coprod (.base 0) (.base 1)) := .var .here

def tC : Object 2 := .prod (.coprod (.base 0) (.base 1)) .unit

def tTm : InvTm TCtx tC :=
  .case tN
    (.pair (InvTm.etaInl (.base 0) (.base 1)) .unit)
    (.pair (InvTm.etaInr (.base 0) (.base 1)) .unit)

example : InvTm.beq (canonicalize (canonicalize tTm)) (canonicalize tTm) = true := by
  native_decide

end Equality
end Gimbal
