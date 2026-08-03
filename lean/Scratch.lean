import Gimbal.Equality.Abstract

namespace Gimbal
namespace Equality

variable {sig : Signature}

example {Γ : Ctx sig} {A B : Object sig.nBases} (x : Var Γ A) (n : NegNeu Γ B)
    (h : NegNeu.beq (.var x) n = true) : True := by
  cases n with
  | var y => trivial
  | app f a => simp [NegNeu.beq] at h
  | fst f => simp [NegNeu.beq] at h
  | snd f => simp [NegNeu.beq] at h

example {Γ : Ctx sig} {A B : Object sig.nBases} (x : Var Γ A) (n : NegNeu Γ B)
    (h : NegNeu.beq (.var x) n = true) : True := by
  cases n <;> first | trivial | simp [NegNeu.beq] at h

end Equality
end Gimbal
