/-
  Phase 0 core objects, indexed by the number of base generators in a signature.
-/

namespace Gimbal

/-- Core objects over `n` opaque base identities. -/
inductive Object (n : Nat) where
  | base : Fin n → Object n
  | unit : Object n
  | never : Object n
  | prod : Object n → Object n → Object n
  | coprod : Object n → Object n → Object n
  | exp : Object n → Object n → Object n
  deriving DecidableEq, Repr

end Gimbal
