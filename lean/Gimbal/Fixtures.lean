/-
  Lean fixtures corresponding to the Rust `Number` signature examples.
-/

import Gimbal.SyntacticCategory

namespace Gimbal.Fixtures

open Gimbal
open CategoryTheory

/-- `Number` as the unique base. -/
def Number : Object 1 := .base 0

/-- Signature with `two`, `three : Unit → Number` and `add : Number × Number → Number`. -/
def numberSignature : Signature where
  nBases := 1
  generators := #[
    ⟨.unit, Number⟩,
    ⟨.unit, Number⟩,
    ⟨.prod Number Number, Number⟩
  ]

abbrev NumSig := numberSignature

def two : Morphism NumSig .unit Number :=
  Morphism.generator (sig := NumSig) ⟨0, by decide⟩

def three : Morphism NumSig .unit Number :=
  Morphism.generator (sig := NumSig) ⟨1, by decide⟩

def add : Morphism NumSig (.prod Number Number) Number :=
  Morphism.generator (sig := NumSig) ⟨2, by decide⟩

/-- `pair(two, three) >>> add : Unit → Number`. -/
def pairThenAdd : Morphism NumSig .unit Number :=
  (two.pair three).compose add

/-- Ill-typed composition as a raw term (mirrors Rust constructible-but-unchecked terms). -/
def illTypedComposeTerm : Term NumSig :=
  .compose (.generator ⟨0, by decide⟩) (.generator ⟨2, by decide⟩)

/-- `curry(add) : Number → Number ⇒ Number`. -/
def curryAdd : Morphism NumSig Number (.exp Number Number) :=
  add.curry

theorem two_id_left : DefEq ((Morphism.id .unit).compose two) two :=
  .id_left two

theorem pairThenAdd_prod_beta_first :
    DefEq
      ((two.pair three).compose (Morphism.first (sig := NumSig) Number Number))
      two :=
  .prod_beta_first two three

def NumberObject : «CΣ» NumSig := ⟨Number⟩
def UnitObject : «CΣ» NumSig := ⟨.unit⟩

def quotedTwo : UnitObject ⟶ NumberObject :=
  «CΣ».Hom.mk two

example : 𝟙 UnitObject ≫ quotedTwo = quotedTwo :=
  «CΣ».Hom.id_comp quotedTwo

end Gimbal.Fixtures
