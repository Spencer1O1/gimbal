/-
  Chosen exponentials of `«CΣ»` (syntax-facing curry/uncurry).
-/

import Gimbal.SyntacticCategory.Product

namespace Gimbal
namespace «CΣ»

open CategoryTheory

variable {sig : Signature}

/-- Chosen exponential object `A ⇒ B`. -/
def expObj (A B : «CΣ» sig) : «CΣ» sig :=
  ⟨.exp A.asObject B.asObject⟩

def Hom.eval (A B : «CΣ» sig) : Hom (prodObj (expObj A B) A) B :=
  Hom.mk (Morphism.eval A.asObject B.asObject)

def Hom.curry {X A B : «CΣ» sig} (f : Hom (prodObj X A) B) : Hom X (expObj A B) :=
  Quotient.liftOn f (fun f => Hom.mk f.curry)
    (by
      intro f g h
      exact Quotient.sound (DefEq.cong_curry h))

@[simp]
theorem Hom.curry_mk {X A B : «CΣ» sig}
    (f : Morphism sig (.prod X.asObject A.asObject) B.asObject) :
    Hom.curry (Hom.mk f) = Hom.mk f.curry :=
  rfl

/-- `uncurry(h) = pair(first >>> h, second) >>> eval`. -/
def Hom.uncurry {X A B : «CΣ» sig} (h : Hom X (expObj A B)) : Hom (prodObj X A) B :=
  Hom.comp (Hom.pair (Hom.comp (Hom.first X A) h) (Hom.second X A)) (Hom.eval A B)

@[simp]
theorem Hom.uncurry_curry {X A B : «CΣ» sig} (f : Hom (prodObj X A) B) :
    Hom.uncurry (Hom.curry f) = f := by
  refine Quotient.inductionOn f ?_
  intro f
  exact Quotient.sound (DefEq.exp_beta f)

@[simp]
theorem Hom.curry_uncurry {X A B : «CΣ» sig} (h : Hom X (expObj A B)) :
    Hom.curry (Hom.uncurry h) = h := by
  refine Quotient.inductionOn h ?_
  intro h
  exact Quotient.sound (DefEq.exp_eta h)

/-- Native Gimbal exponential adjunction equivalence (`X × A` on the left). -/
def Hom.curryEquiv (X A B : «CΣ» sig) :
    Hom (prodObj X A) B ≃ Hom X (expObj A B) where
  toFun := Hom.curry
  invFun := Hom.uncurry
  left_inv := Hom.uncurry_curry
  right_inv := Hom.curry_uncurry

/-- Product of morphisms via pairing. -/
def Hom.prodMap {A A' B B' : «CΣ» sig} (f : Hom A A') (g : Hom B B') :
    Hom (prodObj A B) (prodObj A' B') :=
  Hom.pair (Hom.comp (Hom.first A B) f) (Hom.comp (Hom.second A B) g)

/-- `m >>> pair(f', g') ≡ pair(m >>> f', m >>> g')`. -/
private theorem defEq_comp_pair {X A B C D : Object sig.nBases}
    (m : Morphism sig X (.prod A B))
    (f' : Morphism sig (.prod A B) C)
    (g' : Morphism sig (.prod A B) D) :
    DefEq (m.compose (f'.pair g')) ((m.compose f').pair (m.compose g')) := by
  refine DefEq.trans (DefEq.symm (DefEq.prod_eta _)) ?_
  refine DefEq.cong_pair ?_ ?_
  · refine DefEq.trans (DefEq.assoc m (f'.pair g') (Morphism.first C D)) ?_
    exact DefEq.cong_compose (DefEq.refl m) (DefEq.prod_beta_first f' g')
  · refine DefEq.trans (DefEq.assoc m (f'.pair g') (Morphism.second C D)) ?_
    exact DefEq.cong_compose (DefEq.refl m) (DefEq.prod_beta_second f' g')

private theorem defEq_pair_comp_first {X A B C : Object sig.nBases}
    (f : Morphism sig X A) (g : Morphism sig X B) (k : Morphism sig A C) :
    DefEq (((f.pair g).compose ((Morphism.first A B).compose k))) (f.compose k) := by
  refine DefEq.trans
    (DefEq.symm (DefEq.assoc (f.pair g) (Morphism.first A B) k)) ?_
  exact DefEq.cong_compose (DefEq.prod_beta_first f g) (DefEq.refl k)

private theorem defEq_pair_comp_second {X A B : Object sig.nBases}
    (f : Morphism sig X A) (g : Morphism sig X B) :
    DefEq ((f.pair g).compose (Morphism.second A B)) g :=
  DefEq.prod_beta_second f g

/-- Uncurry of `h >>> curry f` equals `prodMap h id >>> f`. -/
private theorem Hom.uncurry_comp_curry {X X' A B : «CΣ» sig}
    (h : Morphism sig X.asObject X'.asObject)
    (f : Morphism sig (.prod X'.asObject A.asObject) B.asObject) :
    Hom.uncurry (Hom.comp (Hom.mk h) (Hom.curry (Hom.mk f))) =
      Hom.comp (Hom.prodMap (Hom.mk h) (Hom.id A)) (Hom.mk f) := by
  apply Quotient.sound
  -- Prove RHS ≡ LHS as DefEq (then sound gives equality; we use symm at end)
  let fstXA := Morphism.first X.asObject A.asObject
  let sndXA := Morphism.second X.asObject A.asObject
  let fstX'A := Morphism.first X'.asObject A.asObject
  let sndX'A := Morphism.second X'.asObject A.asObject
  let ev := Morphism.eval A.asObject B.asObject
  let m := (fstXA.compose h).pair sndXA
  let q := (fstX'A.compose f.curry).pair sndX'A
  -- RHS after dropping id: m >>> f
  -- Replace f by q >>> ev: m >>> (q >>> ev)
  -- Reassoc: (m >>> q) >>> ev
  -- Reduce m >>> q to pair((fst>>>h)>>>curry f, snd)
  -- Reassoc first component to fst >>> (h >>> curry f)
  refine DefEq.symm ?_
  refine DefEq.trans
    (DefEq.cong_compose (DefEq.cong_pair (DefEq.refl _) (DefEq.id_right _)) (DefEq.refl f)) ?_
  refine DefEq.trans
    (DefEq.cong_compose (DefEq.refl m) (DefEq.symm (DefEq.exp_beta f))) ?_
  refine DefEq.trans (DefEq.symm (DefEq.assoc m q ev)) ?_
  refine DefEq.trans
    (DefEq.cong_compose (defEq_comp_pair m (fstX'A.compose f.curry) sndX'A) (DefEq.refl ev)) ?_
  refine DefEq.trans
    (DefEq.cong_compose
      (DefEq.cong_pair (defEq_pair_comp_first (fstXA.compose h) sndXA f.curry)
        (defEq_pair_comp_second (fstXA.compose h) sndXA))
      (DefEq.refl ev)) ?_
  exact DefEq.cong_compose
    (DefEq.cong_pair (DefEq.assoc fstXA h f.curry) (DefEq.refl sndXA))
    (DefEq.refl ev)

/-- Curry is natural in the domain `X`. -/
theorem Hom.curry_natural_left {X X' A B : «CΣ» sig}
    (h : Hom X X') (f : Hom (prodObj X' A) B) :
    Hom.curry (Hom.comp (Hom.prodMap h (Hom.id A)) f) = Hom.comp h (Hom.curry f) := by
  refine Quotient.inductionOn₂ h f ?_
  intro h f
  have key := Hom.uncurry_comp_curry h f
  have := congrArg Hom.curry key
  rw [Hom.curry_uncurry] at this
  exact this.symm

end «CΣ»
end Gimbal
