/-
  Definitional equality on checked morphisms.

  Congruence closure of the bicartesian-closed laws. Opaque generators have no
  extra equations. Milestone 5 packages morphisms modulo this relation into `CΣ`.
-/

import Gimbal.Morphism

namespace Gimbal

/-- Definitional equality of checked morphisms at a fixed arrow type. -/
inductive DefEq {sig : Signature} :
    {A B : Object sig.nBases} → Morphism sig A B → Morphism sig A B → Prop where
  | refl {A B : Object sig.nBases} (f : Morphism sig A B) :
      DefEq f f
  | symm {A B : Object sig.nBases} {f g : Morphism sig A B} :
      DefEq f g → DefEq g f
  | trans {A B : Object sig.nBases} {f g h : Morphism sig A B} :
      DefEq f g → DefEq g h → DefEq f h
  | cong_compose {A B C : Object sig.nBases}
      {f₁ f₂ : Morphism sig A B} {g₁ g₂ : Morphism sig B C} :
      DefEq f₁ f₂ → DefEq g₁ g₂ →
      DefEq (f₁.compose g₁) (f₂.compose g₂)
  | cong_pair {X A B : Object sig.nBases}
      {f₁ f₂ : Morphism sig X A} {g₁ g₂ : Morphism sig X B} :
      DefEq f₁ f₂ → DefEq g₁ g₂ →
      DefEq (f₁.pair g₁) (f₂.pair g₂)
  | cong_case {A B X : Object sig.nBases}
      {f₁ f₂ : Morphism sig A X} {g₁ g₂ : Morphism sig B X} :
      DefEq f₁ f₂ → DefEq g₁ g₂ →
      DefEq (f₁.case g₁) (f₂.case g₂)
  | cong_curry {X A B : Object sig.nBases}
      {f g : Morphism sig (.prod X A) B} :
      DefEq f g → DefEq f.curry g.curry
  | id_left {A B : Object sig.nBases} (f : Morphism sig A B) :
      DefEq ((Morphism.id A).compose f) f
  | id_right {A B : Object sig.nBases} (f : Morphism sig A B) :
      DefEq (f.compose (Morphism.id B)) f
  | assoc {A B C D : Object sig.nBases}
      (f : Morphism sig A B) (g : Morphism sig B C) (h : Morphism sig C D) :
      DefEq ((f.compose g).compose h) (f.compose (g.compose h))
  | terminal_uniq {A : Object sig.nBases} (f : Morphism sig A .unit) :
      DefEq f (Morphism.discard A)
  | initial_uniq {A : Object sig.nBases} (f : Morphism sig .never A) :
      DefEq f (Morphism.absurd A)
  | prod_beta_first {X A B : Object sig.nBases}
      (f : Morphism sig X A) (g : Morphism sig X B) :
      DefEq ((f.pair g).compose (Morphism.first A B)) f
  | prod_beta_second {X A B : Object sig.nBases}
      (f : Morphism sig X A) (g : Morphism sig X B) :
      DefEq ((f.pair g).compose (Morphism.second A B)) g
  | prod_eta {X A B : Object sig.nBases} (h : Morphism sig X (.prod A B)) :
      DefEq
        (((h.compose (Morphism.first A B)).pair (h.compose (Morphism.second A B))))
        h
  | coprod_beta_left {A B X : Object sig.nBases}
      (f : Morphism sig A X) (g : Morphism sig B X) :
      DefEq ((Morphism.left A B).compose (f.case g)) f
  | coprod_beta_right {A B X : Object sig.nBases}
      (f : Morphism sig A X) (g : Morphism sig B X) :
      DefEq ((Morphism.right A B).compose (f.case g)) g
  | coprod_eta {A B X : Object sig.nBases} (h : Morphism sig (.coprod A B) X) :
      DefEq
        ((((Morphism.left A B).compose h).case ((Morphism.right A B).compose h)))
        h
  /-- `uncurry(curry(f)) = f` with `uncurry(k) = pair(first >>> k, second) >>> eval`. -/
  | exp_beta {X A B : Object sig.nBases} (f : Morphism sig (.prod X A) B) :
      DefEq
        (((((Morphism.first X A).compose f.curry).pair (Morphism.second X A)).compose
            (Morphism.eval A B)))
        f
  /-- `curry(uncurry(h)) = h`. -/
  | exp_eta {X A B : Object sig.nBases} (h : Morphism sig X (.exp A B)) :
      DefEq
        (((((Morphism.first X A).compose h).pair (Morphism.second X A)).compose
              (Morphism.eval A B))).curry
        h

end Gimbal
