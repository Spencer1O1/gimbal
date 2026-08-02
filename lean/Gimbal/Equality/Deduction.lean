/-
  Declarative simple-deduction / strong-positive / uses-new relations
  (Milestone 8 handoff §5–6). Independent of the executable reachability
  worklist; soundness/completeness against `runReachability` are proved later.
-/

import Gimbal.Equality.LambdaSyntax
import Gimbal.Equality.Polarized
import Gimbal.Equality.Reachability

namespace Gimbal
namespace Equality

variable {n : Nat}

/-! ### Declarative judgment forms -/

/--
Simple deduction of an object from a reachability context (old ∪ new).
Covers variables, unit, products, both coproduct injections, function
application, and the polarization shifts used by the executable closure.
-/
inductive SimpleDeduction (Γ : ReachCtx n) : Object n → Prop where
  | hyp {A} (i : Nat) :
      Γ.hyps[i]? = some A →
      objectPolarity A = .pos →
      SimpleDeduction Γ A
  | unit : SimpleDeduction Γ (.unit : Object n)
  | fst {L R} :
      SimpleDeduction Γ (.prod L R) →
      SimpleDeduction Γ L
  | snd {L R} :
      SimpleDeduction Γ (.prod L R) →
      SimpleDeduction Γ R
  | pair {L R} :
      SimpleDeduction Γ L →
      SimpleDeduction Γ R →
      SimpleDeduction Γ (.prod L R)
  | inl {L R} :
      SimpleDeduction Γ L →
      SimpleDeduction Γ (.coprod L R)
  | inr {L R} :
      SimpleDeduction Γ R →
      SimpleDeduction Γ (.coprod L R)
  | appHyp {Arg Ret} (i : Nat) :
      Γ.hyps[i]? = some (.exp Arg Ret) →
      SimpleDeduction Γ Arg →
      SimpleDeduction Γ Ret
  | appTy {Arg Ret} :
      SimpleDeduction Γ (.exp Arg Ret) →
      SimpleDeduction Γ Arg →
      SimpleDeduction Γ Ret
  /-- Function η / identity expansion: a return type yields `Arg → Ret`. -/
  | expEta {Arg Ret} :
      SimpleDeduction Γ Ret →
      SimpleDeduction Γ (.exp Arg Ret)
  | never {A} :
      SimpleDeduction Γ (.never : Object n) →
      SimpleDeduction Γ A

/--
Strong-positive availability: a positive type with a constructible or
observed witness suitable for cut / retrieval (refined in later proofs).
-/
inductive StrongPositive (Γ : ReachCtx n) : Object n → Prop where
  | ofDeduction {P} :
      objectPolarity P = .pos →
      SimpleDeduction Γ P →
      StrongPositive Γ P

/--
A derivation depends on at least one hypothesis from `Γnew`
(`hypIdx ≥ Γ.newFrom`).
-/
inductive UsesNew (Γ : ReachCtx n) : Object n → Prop where
  | hyp {A} (i : Nat) :
      Γ.hyps[i]? = some A →
      Γ.isNew i = true →
      UsesNew Γ A
  | fst {L R} :
      UsesNew Γ (.prod L R) →
      UsesNew Γ L
  | snd {L R} :
      UsesNew Γ (.prod L R) →
      UsesNew Γ R
  | pairL {L R} :
      UsesNew Γ L →
      SimpleDeduction Γ R →
      UsesNew Γ (.prod L R)
  | pairR {L R} :
      SimpleDeduction Γ L →
      UsesNew Γ R →
      UsesNew Γ (.prod L R)
  | inl {L R} :
      UsesNew Γ L →
      UsesNew Γ (.coprod L R)
  | inr {L R} :
      UsesNew Γ R →
      UsesNew Γ (.coprod L R)
  | appHypArg {Arg Ret} (i : Nat) :
      Γ.hyps[i]? = some (.exp Arg Ret) →
      UsesNew Γ Arg →
      UsesNew Γ Ret
  | appHypFn {Arg Ret} (i : Nat) :
      Γ.hyps[i]? = some (.exp Arg Ret) →
      Γ.isNew i = true →
      SimpleDeduction Γ Arg →
      UsesNew Γ Ret
  | appTyFn {Arg Ret} :
      UsesNew Γ (.exp Arg Ret) →
      SimpleDeduction Γ Arg →
      UsesNew Γ Ret
  | appTyArg {Arg Ret} :
      SimpleDeduction Γ (.exp Arg Ret) →
      UsesNew Γ Arg →
      UsesNew Γ Ret
  | expEta {Arg Ret} :
      UsesNew Γ Ret →
      UsesNew Γ (.exp Arg Ret)

end Equality
end Gimbal
