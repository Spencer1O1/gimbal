/-
  Private intrinsically typed mirror of Phase 0 morphisms.
  Typing lives in the indices; used by the Milestone 7 equality calculus.
-/

import Gimbal.Morphism

namespace Gimbal
namespace Equality

/--
Intrinsically typed checked morphism from `A` to `B`.

This is a computational mirror of `Morphism`: constructors carry source/target in
their types, so equality-calculus code can recurse on syntax without eliminating
the multi-constructor `Prop` `HasType`.
-/
inductive IntrinsicMorphism (sig : Signature) :
    Object sig.nBases → Object sig.nBases → Type where
  | generator (q : Fin sig.nGens) :
      IntrinsicMorphism sig (sig.gen q).source (sig.gen q).target
  | id (A : Object sig.nBases) :
      IntrinsicMorphism sig A A
  | compose {A B C : Object sig.nBases} :
      IntrinsicMorphism sig A B →
      IntrinsicMorphism sig B C →
      IntrinsicMorphism sig A C
  | discard (A : Object sig.nBases) :
      IntrinsicMorphism sig A .unit
  | absurd (A : Object sig.nBases) :
      IntrinsicMorphism sig .never A
  | first (A B : Object sig.nBases) :
      IntrinsicMorphism sig (.prod A B) A
  | second (A B : Object sig.nBases) :
      IntrinsicMorphism sig (.prod A B) B
  | pair {X A B : Object sig.nBases} :
      IntrinsicMorphism sig X A →
      IntrinsicMorphism sig X B →
      IntrinsicMorphism sig X (.prod A B)
  | left (A B : Object sig.nBases) :
      IntrinsicMorphism sig A (.coprod A B)
  | right (A B : Object sig.nBases) :
      IntrinsicMorphism sig B (.coprod A B)
  | case {A B X : Object sig.nBases} :
      IntrinsicMorphism sig A X →
      IntrinsicMorphism sig B X →
      IntrinsicMorphism sig (.coprod A B) X
  | curry {X A B : Object sig.nBases} :
      IntrinsicMorphism sig (.prod X A) B →
      IntrinsicMorphism sig X (.exp A B)
  | eval (A B : Object sig.nBases) :
      IntrinsicMorphism sig (.prod (.exp A B) A) B

/-- Forget intrinsic typing back to the public extrinsic term. -/
def IntrinsicMorphism.erase {sig : Signature} {A B : Object sig.nBases} :
    IntrinsicMorphism sig A B → Term sig
  | .generator q => .generator q
  | .id A => .id A
  | .compose f g => .compose f.erase g.erase
  | .discard A => .discard A
  | .absurd A => .absurd A
  | .first A B => .first A B
  | .second A B => .second A B
  | .pair f g => .pair f.erase g.erase
  | .left A B => .left A B
  | .right A B => .right A B
  | .case f g => .case f.erase g.erase
  | .curry f => .curry f.erase
  | .eval A B => .eval A B

/-- Intrinsic morphisms are well-typed as public morphisms. -/
theorem IntrinsicMorphism.hasType {sig : Signature} {A B : Object sig.nBases}
    (f : IntrinsicMorphism sig A B) : HasType sig f.erase A B := by
  induction f with
  | generator q => exact .generator q
  | id A => exact .id A
  | compose _ _ ihf ihg => exact .compose ihf ihg
  | discard A => exact .discard A
  | absurd A => exact .absurd A
  | first A B => exact .first A B
  | second A B => exact .second A B
  | pair _ _ ihf ihg => exact .pair ihf ihg
  | left A B => exact .left A B
  | right A B => exact .right A B
  | case _ _ ihf ihg => exact .case ihf ihg
  | curry _ ih => exact .curry ih
  | eval A B => exact .eval A B

/-- Reconstitute a public checked morphism from an intrinsic one. -/
def IntrinsicMorphism.toMorphism {sig : Signature} {A B : Object sig.nBases}
    (f : IntrinsicMorphism sig A B) : Morphism sig A B :=
  ⟨f.erase, f.hasType⟩

end Equality
end Gimbal
