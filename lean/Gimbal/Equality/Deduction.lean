/-
  Declarative simple-deduction / strong-positive / uses-new relations
  (Milestone 8 handoff §5–6). Independent of the executable reachability
  worklist; soundness and completeness against `runReachability` are proved in
  `Gimbal.Equality.ReachSound`.

  One generic judgment `Deduce Γ ok U A` carries two side conditions:

  * `ok i` restricts which hypotheses a derivation may use — instantiating it
    with "not in `Γnew`" gives the old-only fragment of the provenance lattice;
  * `U A` restricts which formulas may occur — instantiating it with membership
    in the subformula table gives exactly the fragment the finite closure can
    represent.

  Both are `True` for the unrestricted relation `SimpleDeduction`.
-/

import Gimbal.Equality.LambdaSyntax
import Gimbal.Equality.Polarized
import Gimbal.Equality.Reachability

namespace Gimbal
namespace Equality

variable {n : Nat}

/-! ### The generic deduction judgment -/

/--
Simple deduction of an object from a reachability context (old ∪ new).
Covers variables, unit, products, both coproduct injections, function
application and identity expansion, the negative-hypothesis eliminations, and
ex falso.
-/
inductive Deduce (Γ : ReachCtx n) (ok : Nat → Prop) (U : Object n → Prop) :
    Object n → Prop where
  | hyp {A} (i : Nat) :
      Γ.hyps[i]? = some A → objectPolarity A = .pos → ok i → U A →
      Deduce Γ ok U A
  | unit :
      U (.unit : Object n) → Deduce Γ ok U (.unit : Object n)
  /-- A product hypothesis is negative: the binding itself justifies projection. -/
  | fstHyp {L R} (i : Nat) :
      Γ.hyps[i]? = some (.prod L R) → ok i → U L → Deduce Γ ok U L
  | sndHyp {L R} (i : Nat) :
      Γ.hyps[i]? = some (.prod L R) → ok i → U R → Deduce Γ ok U R
  | fst {L R} :
      Deduce Γ ok U (.prod L R) → U L → Deduce Γ ok U L
  | snd {L R} :
      Deduce Γ ok U (.prod L R) → U R → Deduce Γ ok U R
  | pair {L R} :
      Deduce Γ ok U L → Deduce Γ ok U R → U (.prod L R) →
      Deduce Γ ok U (.prod L R)
  | inl {L R} :
      Deduce Γ ok U L → U (.coprod L R) → Deduce Γ ok U (.coprod L R)
  | inr {L R} :
      Deduce Γ ok U R → U (.coprod L R) → Deduce Γ ok U (.coprod L R)
  | appHyp {Arg Ret} (i : Nat) :
      Γ.hyps[i]? = some (.exp Arg Ret) → ok i →
      Deduce Γ ok U Arg → U Ret → Deduce Γ ok U Ret
  | appTy {Arg Ret} :
      Deduce Γ ok U (.exp Arg Ret) → Deduce Γ ok U Arg → U Ret →
      Deduce Γ ok U Ret
  /-- Function η / identity expansion: a return type yields `Arg → Ret`. -/
  | expEta {Arg Ret} :
      Deduce Γ ok U Ret → U (.exp Arg Ret) → Deduce Γ ok U (.exp Arg Ret)
  | exFalso {A} :
      Deduce Γ ok U (.never : Object n) → U A → Deduce Γ ok U A

/-- Both side conditions may be relaxed. -/
theorem Deduce.mono {Γ : ReachCtx n} {ok ok' : Nat → Prop} {U U' : Object n → Prop}
    (hok : ∀ i, ok i → ok' i) (hU : ∀ A, U A → U' A) :
    ∀ {A}, Deduce Γ ok U A → Deduce Γ ok' U' A := by
  intro A d
  induction d with
  | hyp i hi hp ho hu => exact .hyp i hi hp (hok _ ho) (hU _ hu)
  | unit hu => exact .unit (hU _ hu)
  | fstHyp i hi ho hu => exact .fstHyp i hi (hok _ ho) (hU _ hu)
  | sndHyp i hi ho hu => exact .sndHyp i hi (hok _ ho) (hU _ hu)
  | fst _ hu ih => exact .fst ih (hU _ hu)
  | snd _ hu ih => exact .snd ih (hU _ hu)
  | pair _ _ hu ihl ihr => exact .pair ihl ihr (hU _ hu)
  | inl _ hu ih => exact .inl ih (hU _ hu)
  | inr _ hu ih => exact .inr ih (hU _ hu)
  | appHyp i hi ho _ hu ih => exact .appHyp i hi (hok _ ho) ih (hU _ hu)
  | appTy _ _ hu ihf iha => exact .appTy ihf iha (hU _ hu)
  | expEta _ hu ih => exact .expEta ih (hU _ hu)
  | exFalso _ hu ih => exact .exFalso ih (hU _ hu)

/-- Unrestricted simple deduction. -/
abbrev SimpleDeduction (Γ : ReachCtx n) (A : Object n) : Prop :=
  Deduce Γ (fun _ => True) (fun _ => True) A

/-- Deduction that never touches the new fragment (`Γold ⊢ A`). -/
abbrev OldDeduction (Γ : ReachCtx n) (A : Object n) : Prop :=
  Deduce Γ (fun i => Γ.isNew i = false) (fun _ => True) A

/-- Deduction confined to a finite formula universe (the subformula table). -/
abbrev SubDeduction (U : Object n → Prop) (Γ : ReachCtx n) (A : Object n) : Prop :=
  Deduce Γ (fun _ => True) U A

theorem OldDeduction.toSimple {Γ : ReachCtx n} {A : Object n}
    (d : OldDeduction Γ A) : SimpleDeduction Γ A :=
  Deduce.mono (fun _ _ => trivial) (fun _ _ => trivial) d

theorem SubDeduction.toSimple {U : Object n → Prop} {Γ : ReachCtx n} {A : Object n}
    (d : SubDeduction U Γ A) : SimpleDeduction Γ A :=
  Deduce.mono (fun _ h => h) (fun _ _ => trivial) d

/-! ### Strong-positive retrievability -/

/--
Strong-positive availability: a positive type with a constructible or
observed witness suitable for cut / retrieval.
-/
inductive StrongPositive (Γ : ReachCtx n) : Object n → Prop where
  | ofDeduction {P} :
      objectPolarity P = .pos →
      SimpleDeduction Γ P →
      StrongPositive Γ P

theorem StrongPositive.toSimple {Γ : ReachCtx n} {P : Object n}
    (h : StrongPositive Γ P) : SimpleDeduction Γ P := by
  cases h with
  | ofDeduction _ d => exact d

/-! ### Uses-new provenance -/

/--
A derivation that depends on at least one hypothesis from `Γnew`
(`Γ.isNew i = true`).
-/
inductive UsesNew (Γ : ReachCtx n) : Object n → Prop where
  | hyp {A} (i : Nat) :
      Γ.hyps[i]? = some A →
      objectPolarity A = .pos →
      Γ.isNew i = true →
      UsesNew Γ A
  | fstHyp {L R} (i : Nat) :
      Γ.hyps[i]? = some (.prod L R) → Γ.isNew i = true → UsesNew Γ L
  | sndHyp {L R} (i : Nat) :
      Γ.hyps[i]? = some (.prod L R) → Γ.isNew i = true → UsesNew Γ R
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

/-- A uses-new derivation is in particular a derivation. -/
theorem UsesNew.toSimple {Γ : ReachCtx n} {A : Object n} (h : UsesNew Γ A) :
    SimpleDeduction Γ A := by
  induction h with
  | hyp i hi hp _ => exact .hyp i hi hp trivial trivial
  | fstHyp i hi _ => exact .fstHyp i hi trivial trivial
  | sndHyp i hi _ => exact .sndHyp i hi trivial trivial
  | fst _ ih => exact .fst ih trivial
  | snd _ ih => exact .snd ih trivial
  | pairL _ hr ih => exact .pair ih hr trivial
  | pairR hl _ ih => exact .pair hl ih trivial
  | inl _ ih => exact .inl ih trivial
  | inr _ ih => exact .inr ih trivial
  | appHypArg i hi _ ih => exact .appHyp i hi trivial ih trivial
  | appHypFn i hi _ ha => exact .appHyp i hi trivial ha trivial
  | appTyFn _ ha ih => exact .appTy ih ha trivial
  | appTyArg hf _ ih => exact .appTy hf ih trivial
  | expEta _ ih => exact .expEta ih trivial

end Equality
end Gimbal
