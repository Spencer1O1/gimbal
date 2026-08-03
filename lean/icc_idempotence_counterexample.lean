/-
  Reproducer: `canonicalize` is not idempotent.

  Not part of the library (nothing imports it); run with
  `lake env lean icc_idempotence_counterexample.lean`. It prints `false` today.

  `canonicalize tm` commutes the `case` past the pair, which manufactures a
  fresh `case` node in the first component. That node is a coproduct
  η-expansion, but `tryCoprodEta` is only ever attempted at the node
  `canonicalizeInv` started from, so it survives the first pass and is
  contracted by the second.

  See "8F open" in the Milestone 8 handoff for the fix (route every `case`
  emitted by `caseCommute` through a `mkCase` smart constructor).
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

/-- Should be `true`; currently `false`. -/
def canonicalizeIsIdempotentHere : Bool :=
  InvTm.beq (canonicalize (canonicalize tTm)) (canonicalize tTm)

#eval canonicalizeIsIdempotentHere

end Equality
end Gimbal
