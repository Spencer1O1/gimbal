/-
  Lean fixtures corresponding to the Rust `Number` signature examples.
-/

import Gimbal.SyntacticCategory.BicartesianClosed

namespace Gimbal.Fixtures

open Gimbal
open CategoryTheory CategoryTheory.Limits MonoidalCategory

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
def NeverObject : «CΣ» NumSig := «CΣ».neverObj
def NumberProd : «CΣ» NumSig := «CΣ».prodObj NumberObject NumberObject
def NumberCoprod : «CΣ» NumSig := «CΣ».coprodObj NumberObject NumberObject
def NumberExp : «CΣ» NumSig := «CΣ».expObj NumberObject NumberObject

def quotedTwo : UnitObject ⟶ NumberObject :=
  «CΣ».Hom.mk two

def quotedThree : UnitObject ⟶ NumberObject :=
  «CΣ».Hom.mk three

def quotedAdd : NumberProd ⟶ NumberObject :=
  «CΣ».Hom.mk add

def discardNumber : NumberObject ⟶ «CΣ».unitObj :=
  «CΣ».Hom.discard NumberObject

example : 𝟙 UnitObject ≫ quotedTwo = quotedTwo :=
  «CΣ».Hom.id_comp quotedTwo

/-- Terminal uniqueness at the quotient level. -/
example (f : NumberObject ⟶ «CΣ».unitObj) :
    f = «CΣ».Hom.discard NumberObject :=
  «CΣ».Hom.terminal_uniq f

/-- Initial uniqueness at the quotient level. -/
example (f : NeverObject ⟶ NumberObject) :
    f = «CΣ».Hom.absurd NumberObject :=
  «CΣ».Hom.initial_uniq f

/-- Product beta. -/
example :
    «CΣ».Hom.pair quotedTwo quotedThree ≫ «CΣ».Hom.first NumberObject NumberObject =
      quotedTwo :=
  «CΣ».Hom.pair_first quotedTwo quotedThree

example :
    «CΣ».Hom.pair quotedTwo quotedThree ≫ «CΣ».Hom.second NumberObject NumberObject =
      quotedThree :=
  «CΣ».Hom.pair_second quotedTwo quotedThree

/-- Product eta. -/
example (h : UnitObject ⟶ NumberProd) :
    «CΣ».Hom.pair
      (h ≫ «CΣ».Hom.first NumberObject NumberObject)
      (h ≫ «CΣ».Hom.second NumberObject NumberObject) = h :=
  «CΣ».Hom.prod_eta h

/-- Product universal-property equivalence. -/
example :
    («CΣ».productLiftEquiv UnitObject NumberObject NumberObject
      (quotedTwo, quotedThree)) =
      «CΣ».Hom.pair quotedTwo quotedThree :=
  rfl

/-- Coproduct beta. -/
example :
    «CΣ».Hom.left NumberObject NumberObject ≫
        «CΣ».Hom.case discardNumber discardNumber =
      discardNumber :=
  «CΣ».Hom.left_case discardNumber discardNumber

example :
    «CΣ».Hom.right NumberObject NumberObject ≫
        «CΣ».Hom.case discardNumber discardNumber =
      discardNumber :=
  «CΣ».Hom.right_case discardNumber discardNumber

/-- Coproduct eta. -/
example (h : NumberCoprod ⟶ «CΣ».unitObj) :
    «CΣ».Hom.case
      («CΣ».Hom.left NumberObject NumberObject ≫ h)
      («CΣ».Hom.right NumberObject NumberObject ≫ h) = h :=
  «CΣ».Hom.coprod_eta h

/-- Coproduct universal-property equivalence. -/
example :
    («CΣ».coproductDescEquiv NumberObject NumberObject «CΣ».unitObj
      (discardNumber, discardNumber)) =
      «CΣ».Hom.case discardNumber discardNumber :=
  rfl

/-- Exponential beta / eta on quoted `add`. -/
def quotedCurryAdd : NumberObject ⟶ NumberExp :=
  «CΣ».Hom.curry quotedAdd

example : «CΣ».Hom.uncurry quotedCurryAdd = quotedAdd :=
  «CΣ».Hom.uncurry_curry quotedAdd

example : «CΣ».Hom.curry («CΣ».Hom.uncurry quotedCurryAdd) = quotedCurryAdd :=
  «CΣ».Hom.curry_uncurry quotedCurryAdd

/-- Curry naturality in the domain. -/
example (h : UnitObject ⟶ NumberObject) (f : NumberProd ⟶ NumberObject) :
    «CΣ».Hom.curry («CΣ».Hom.comp («CΣ».Hom.prodMap h («CΣ».Hom.id NumberObject)) f) =
      «CΣ».Hom.comp h («CΣ».Hom.curry f) :=
  «CΣ».Hom.curry_natural_left h f

/-- Mathlib tensor selects Gimbal's chosen product. -/
example : (NumberObject ⊗ NumberObject) = NumberProd :=
  «CΣ».tensorObj_eq_prodObj NumberObject NumberObject

/-- Mathlib tensor unit selects Gimbal's chosen terminal. -/
example : (𝟙_ («CΣ» NumSig)) = «CΣ».unitObj :=
  «CΣ».tensorUnit_eq_unitObj

/-- Mathlib internal hom object is the chosen exponential. -/
example : («CΣ».expFunctor NumberObject).obj NumberObject = NumberExp :=
  «CΣ».expFunctor_obj NumberObject NumberObject

example : (NumberObject ⟶[«CΣ» NumSig] NumberObject) = NumberExp :=
  «CΣ».ihom_obj_eq_expObj NumberObject NumberObject

-- Bridge examples need the named cartesian braiding instance in scope for `β_`.
section BridgeExamples
attribute [local instance] «CΣ».cartesianBraided

/-- Mathlib curry = Gimbal curry after braiding `Y ⊗ A ⟶ A ⊗ Y`. -/
noncomputable example (f : NumberObject ⊗ UnitObject ⟶ NumberObject) :
    MonoidalClosed.curry f =
      «CΣ».Hom.curry ((β_ NumberObject UnitObject).inv ≫ f) :=
  «CΣ».monoidalClosed_curry_eq_hom_curry f

/-- Gimbal eval = Mathlib ev after braiding `(A ⇒ B) ⊗ A ⟶ A ⊗ (A ⇒ B)`. -/
noncomputable example :
    «CΣ».Hom.eval NumberObject NumberObject =
      (β_ NumberObject NumberExp).inv ≫ (ihom.ev NumberObject).app NumberObject :=
  «CΣ».hom_eval_eq_ihom_ev

end BridgeExamples

end Gimbal.Fixtures
