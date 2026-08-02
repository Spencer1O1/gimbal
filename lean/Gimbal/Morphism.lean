/-
  Checked Phase 0 morphisms: a term plus a typing derivation.
  Corresponds to Rust `Morphism` after successful `check`.
-/

import Gimbal.Typing

namespace Gimbal

/-- Trusted typed morphism from `A` to `B` in `sig`. -/
structure Morphism (sig : Signature) (A B : Object sig.nBases) where
  term : Term sig
  typed : HasType sig term A B

namespace Morphism

variable {sig : Signature}

def generator (q : Fin sig.nGens) : Morphism sig (sig.gen q).source (sig.gen q).target :=
  ⟨.generator q, .generator q⟩

def id (A : Object sig.nBases) : Morphism sig A A :=
  ⟨.id A, .id A⟩

def compose {A B C : Object sig.nBases}
    (f : Morphism sig A B) (g : Morphism sig B C) : Morphism sig A C :=
  ⟨.compose f.term g.term, .compose f.typed g.typed⟩

def discard (A : Object sig.nBases) : Morphism sig A .unit :=
  ⟨.discard A, .discard A⟩

def absurd (A : Object sig.nBases) : Morphism sig .never A :=
  ⟨.absurd A, .absurd A⟩

def first (A B : Object sig.nBases) : Morphism sig (.prod A B) A :=
  ⟨.first A B, .first A B⟩

def second (A B : Object sig.nBases) : Morphism sig (.prod A B) B :=
  ⟨.second A B, .second A B⟩

def pair {X A B : Object sig.nBases}
    (f : Morphism sig X A) (g : Morphism sig X B) : Morphism sig X (.prod A B) :=
  ⟨.pair f.term g.term, .pair f.typed g.typed⟩

def left (A B : Object sig.nBases) : Morphism sig A (.coprod A B) :=
  ⟨.left A B, .left A B⟩

def right (A B : Object sig.nBases) : Morphism sig B (.coprod A B) :=
  ⟨.right A B, .right A B⟩

def case {A B X : Object sig.nBases}
    (f : Morphism sig A X) (g : Morphism sig B X) : Morphism sig (.coprod A B) X :=
  ⟨.case f.term g.term, .case f.typed g.typed⟩

def curry {X A B : Object sig.nBases}
    (f : Morphism sig (.prod X A) B) : Morphism sig X (.exp A B) :=
  ⟨.curry f.term, .curry f.typed⟩

def eval (A B : Object sig.nBases) : Morphism sig (.prod (.exp A B) A) B :=
  ⟨.eval A B, .eval A B⟩

end Morphism

end Gimbal
