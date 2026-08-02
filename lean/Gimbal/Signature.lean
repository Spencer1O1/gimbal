/-
  Phase 0 signatures: base count plus generating morphisms with declared
  source and target objects.
-/

import Gimbal.Object

namespace Gimbal

/-- One generating morphism declaration over `n` bases. -/
structure Generator (n : Nat) where
  source : Object n
  target : Object n
  deriving DecidableEq, Repr

/-- A finite Phase 0 signature. -/
structure Signature where
  /-- Number of opaque base objects. -/
  nBases : Nat
  /-- Generating morphisms, in declaration order (dense `Fin` ids). -/
  generators : Array (Generator nBases)
  deriving Repr

/-- Number of generating morphisms. -/
abbrev Signature.nGens (sig : Signature) : Nat :=
  sig.generators.size

/-- Look up a generator by dense id. -/
def Signature.gen (sig : Signature) (q : Fin sig.nGens) : Generator sig.nBases :=
  sig.generators[q]

end Gimbal
