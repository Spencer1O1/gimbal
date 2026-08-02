/-
  Explicit Phase 0 terms. Structurally valid under a signature, possibly ill-typed.
  Corresponds to Rust `Term`.
-/

import Gimbal.Signature

namespace Gimbal

/-- Explicit core term over signature `sig`. -/
inductive Term (sig : Signature) where
  | generator : Fin sig.nGens → Term sig
  | id : Object sig.nBases → Term sig
  | compose : Term sig → Term sig → Term sig
  | discard : Object sig.nBases → Term sig
  | absurd : Object sig.nBases → Term sig
  | first : Object sig.nBases → Object sig.nBases → Term sig
  | second : Object sig.nBases → Object sig.nBases → Term sig
  | pair : Term sig → Term sig → Term sig
  | left : Object sig.nBases → Object sig.nBases → Term sig
  | right : Object sig.nBases → Object sig.nBases → Term sig
  | case : Term sig → Term sig → Term sig
  | curry : Term sig → Term sig
  | eval : Object sig.nBases → Object sig.nBases → Term sig
  deriving Repr

end Gimbal
