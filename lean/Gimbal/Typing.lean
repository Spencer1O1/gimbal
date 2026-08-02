/-
  Typing judgment for Phase 0 terms. Corresponds to Rust `check`.
-/

import Gimbal.Term

namespace Gimbal

/-- Typing judgment: term has morphism type `A` to `B`. -/
inductive HasType (sig : Signature) : Term sig → Object sig.nBases → Object sig.nBases → Prop where
  | generator (q : Fin sig.nGens) :
      HasType sig (.generator q) (sig.gen q).source (sig.gen q).target
  | id (A : Object sig.nBases) :
      HasType sig (.id A) A A
  | compose {t u : Term sig} {A B C : Object sig.nBases} :
      HasType sig t A B →
      HasType sig u B C →
      HasType sig (.compose t u) A C
  | discard (A : Object sig.nBases) :
      HasType sig (.discard A) A .unit
  | absurd (A : Object sig.nBases) :
      HasType sig (.absurd A) .never A
  | first (A B : Object sig.nBases) :
      HasType sig (.first A B) (.prod A B) A
  | second (A B : Object sig.nBases) :
      HasType sig (.second A B) (.prod A B) B
  | pair {t u : Term sig} {X A B : Object sig.nBases} :
      HasType sig t X A →
      HasType sig u X B →
      HasType sig (.pair t u) X (.prod A B)
  | left (A B : Object sig.nBases) :
      HasType sig (.left A B) A (.coprod A B)
  | right (A B : Object sig.nBases) :
      HasType sig (.right A B) B (.coprod A B)
  | case {t u : Term sig} {A B X : Object sig.nBases} :
      HasType sig t A X →
      HasType sig u B X →
      HasType sig (.case t u) (.coprod A B) X
  | curry {t : Term sig} {X A B : Object sig.nBases} :
      HasType sig t (.prod X A) B →
      HasType sig (.curry t) X (.exp A B)
  | eval (A B : Object sig.nBases) :
      HasType sig (.eval A B) (.prod (.exp A B) A) B

end Gimbal
