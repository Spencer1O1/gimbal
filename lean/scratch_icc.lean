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

def idemOk : Bool :=
  InvTm.beq (canonicalize (canonicalize tTm)) (canonicalize tTm)

#eval idemOk

end Equality
end Gimbal
