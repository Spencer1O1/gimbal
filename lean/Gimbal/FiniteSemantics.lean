/-
  Finite-set semantics for the public Gimbal language.

  This module is deliberately independent of the private equality engines.
  It interprets a public `HasType` derivation directly and proves that every
  constructor of public `DefEq` is sound in every finite model of the opaque
  signature.
-/

import Gimbal.DefinitionalEquality
import Gimbal.Equality.Elaborate
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

namespace Gimbal

/-- Interpretation of an object when base `q` has `card q` elements. -/
@[reducible] def SemObj {n : Nat} (card : Fin n → Nat) : Object n → Type
  | .base q => Fin (card q)
  | .unit => PUnit
  | .never => Empty
  | .prod A B => SemObj card A × SemObj card B
  | .coprod A B => Sum (SemObj card A) (SemObj card B)
  | .exp A B => SemObj card A → SemObj card B

mutual
  /-- Every object denotes a finite type. -/
  @[reducible] def SemObj.fintype {n : Nat} (card : Fin n → Nat) :
      (A : Object n) → Fintype (SemObj card A)
    | .base _ => inferInstance
    | .unit => inferInstance
    | .never => inferInstance
    | .prod A B => by
        letI : Fintype (SemObj card A) := SemObj.fintype card A
        letI : Fintype (SemObj card B) := SemObj.fintype card B
        change Fintype (SemObj card A × SemObj card B)
        exact inferInstance
    | .coprod A B => by
        letI : Fintype (SemObj card A) := SemObj.fintype card A
        letI : Fintype (SemObj card B) := SemObj.fintype card B
        change Fintype (Sum (SemObj card A) (SemObj card B))
        exact inferInstance
    | .exp A B => by
        letI : Fintype (SemObj card A) := SemObj.fintype card A
        letI : Fintype (SemObj card B) := SemObj.fintype card B
        letI : DecidableEq (SemObj card A) := SemObj.decidableEq card A
        change Fintype (SemObj card A → SemObj card B)
        exact inferInstance

  /-- Equality in every semantic object is decidable. -/
  @[reducible] def SemObj.decidableEq {n : Nat} (card : Fin n → Nat) :
      (A : Object n) → DecidableEq (SemObj card A)
    | .base _ => inferInstance
    | .unit => inferInstance
    | .never => inferInstance
    | .prod A B => by
        letI : DecidableEq (SemObj card A) := SemObj.decidableEq card A
        letI : DecidableEq (SemObj card B) := SemObj.decidableEq card B
        change DecidableEq (SemObj card A × SemObj card B)
        exact inferInstance
    | .coprod A B => by
        letI : DecidableEq (SemObj card A) := SemObj.decidableEq card A
        letI : DecidableEq (SemObj card B) := SemObj.decidableEq card B
        change DecidableEq (Sum (SemObj card A) (SemObj card B))
        exact inferInstance
    | .exp A B => by
        letI : Fintype (SemObj card A) := SemObj.fintype card A
        letI : DecidableEq (SemObj card A) := SemObj.decidableEq card A
        letI : DecidableEq (SemObj card B) := SemObj.decidableEq card B
        change DecidableEq (SemObj card A → SemObj card B)
        exact inferInstance
end

/-- A finite-set interpretation of all base objects and opaque generators. -/
structure FinModel (sig : Signature) where
  /-- Cardinality assigned to each opaque base object. Zero is allowed. -/
  baseCard : Fin sig.nBases → Nat
  /-- Arbitrary total function assigned to each opaque generator. -/
  generator : (q : Fin sig.nGens) →
    SemObj baseCard (sig.gen q).source → SemObj baseCard (sig.gen q).target

namespace FinModel

variable {sig : Signature}

/-- Interpret an intrinsically typed public term. -/
def denoteIntrinsic (M : FinModel sig) :
    {A B : Object sig.nBases} → Equality.IntrinsicMorphism sig A B →
      SemObj M.baseCard A → SemObj M.baseCard B
  | _, _, .generator q => M.generator q
  | _, _, .id _ => id
  | _, _, .compose f g => fun x => M.denoteIntrinsic g (M.denoteIntrinsic f x)
  | _, _, .discard _ => fun _ => PUnit.unit
  | _, _, .absurd _ => fun x => nomatch x
  | _, _, .first _ _ => Prod.fst
  | _, _, .second _ _ => Prod.snd
  | _, _, .pair f g => fun x => (M.denoteIntrinsic f x, M.denoteIntrinsic g x)
  | _, _, .left _ _ => Sum.inl
  | _, _, .right _ _ => Sum.inr
  | _, _, .case f g => fun x =>
      match x with
      | .inl a => M.denoteIntrinsic f a
      | .inr b => M.denoteIntrinsic g b
  | _, _, .curry f => fun x a => M.denoteIntrinsic f (x, a)
  | _, _, .eval _ _ => fun f => f.1 f.2

/-- Interpret a checked public morphism. -/
def denote (M : FinModel sig) {A B : Object sig.nBases} (f : Morphism sig A B) :
    SemObj M.baseCard A → SemObj M.baseCard B :=
  M.denoteIntrinsic (Equality.ofMorphism f)

private theorem elaborate_erase {A B : Object sig.nBases}
    (f : Equality.IntrinsicMorphism sig A B) :
    Equality.elaborate f.erase = some ⟨A, B, f⟩ := by
  induction f with
  | generator q => rfl
  | id A => rfl
  | compose f g ihf ihg =>
      simp only [Equality.IntrinsicMorphism.erase, Equality.elaborate, ihf, ihg]
      simp
  | discard A => rfl
  | absurd A => rfl
  | first A B => rfl
  | second A B => rfl
  | pair f g ihf ihg =>
      simp only [Equality.IntrinsicMorphism.erase, Equality.elaborate, ihf, ihg]
      simp
  | left A B => rfl
  | right A B => rfl
  | case f g ihf ihg =>
      simp only [Equality.IntrinsicMorphism.erase, Equality.elaborate, ihf, ihg]
      simp
  | curry f ih =>
      simp only [Equality.IntrinsicMorphism.erase, Equality.elaborate, ih]
  | eval A B => rfl

private theorem intrinsic_eq_of_erase_eq {A B : Object sig.nBases}
    {f g : Equality.IntrinsicMorphism sig A B} (h : f.erase = g.erase) : f = g := by
  have hf := elaborate_erase f
  rw [h, elaborate_erase g] at hf
  have hs : (⟨A, B, g⟩ : Σ A, Σ B, Equality.IntrinsicMorphism sig A B) =
      ⟨A, B, f⟩ := Option.some.inj hf
  cases hs
  rfl

private theorem ofMorphism_eq {A B : Object sig.nBases} (f : Morphism sig A B)
    (g : Equality.IntrinsicMorphism sig A B) (h : g.erase = f.term) :
    Equality.ofMorphism f = g :=
  intrinsic_eq_of_erase_eq (Equality.ofMorphism_erase f |>.trans h.symm)

@[simp] theorem ofMorphism_generator (q : Fin sig.nGens) :
    Equality.ofMorphism (Morphism.generator q) = .generator q :=
  ofMorphism_eq _ _ rfl

@[simp] theorem ofMorphism_id (A : Object sig.nBases) :
    Equality.ofMorphism (Morphism.id A) = .id A :=
  ofMorphism_eq _ _ rfl

@[simp] theorem ofMorphism_compose {A B C : Object sig.nBases}
    (f : Morphism sig A B) (g : Morphism sig B C) :
    Equality.ofMorphism (f.compose g) =
      .compose (Equality.ofMorphism f) (Equality.ofMorphism g) := by
  apply ofMorphism_eq
  change Term.compose (Equality.ofMorphism f).erase (Equality.ofMorphism g).erase =
    Term.compose f.term g.term
  rw [Equality.ofMorphism_erase, Equality.ofMorphism_erase]

@[simp] theorem ofMorphism_pair {X A B : Object sig.nBases}
    (f : Morphism sig X A) (g : Morphism sig X B) :
    Equality.ofMorphism (f.pair g) = .pair (Equality.ofMorphism f) (Equality.ofMorphism g) := by
  apply ofMorphism_eq
  change Term.pair (Equality.ofMorphism f).erase (Equality.ofMorphism g).erase =
    Term.pair f.term g.term
  rw [Equality.ofMorphism_erase, Equality.ofMorphism_erase]

@[simp] theorem ofMorphism_case {A B X : Object sig.nBases}
    (f : Morphism sig A X) (g : Morphism sig B X) :
    Equality.ofMorphism (f.case g) = .case (Equality.ofMorphism f) (Equality.ofMorphism g) := by
  apply ofMorphism_eq
  change Term.case (Equality.ofMorphism f).erase (Equality.ofMorphism g).erase =
    Term.case f.term g.term
  rw [Equality.ofMorphism_erase, Equality.ofMorphism_erase]

@[simp] theorem ofMorphism_curry {X A B : Object sig.nBases}
    (f : Morphism sig (.prod X A) B) :
    Equality.ofMorphism f.curry = .curry (Equality.ofMorphism f) := by
  apply ofMorphism_eq
  change Term.curry (Equality.ofMorphism f).erase = Term.curry f.term
  rw [Equality.ofMorphism_erase]

@[simp] theorem ofMorphism_discard (A : Object sig.nBases) :
    Equality.ofMorphism (Morphism.discard A) = .discard A := ofMorphism_eq _ _ rfl

@[simp] theorem ofMorphism_absurd (A : Object sig.nBases) :
    Equality.ofMorphism (Morphism.absurd A) = .absurd A := ofMorphism_eq _ _ rfl

@[simp] theorem ofMorphism_first (A B : Object sig.nBases) :
    Equality.ofMorphism (Morphism.first A B) = .first A B := ofMorphism_eq _ _ rfl

@[simp] theorem ofMorphism_second (A B : Object sig.nBases) :
    Equality.ofMorphism (Morphism.second A B) = .second A B := ofMorphism_eq _ _ rfl

@[simp] theorem ofMorphism_left (A B : Object sig.nBases) :
    Equality.ofMorphism (Morphism.left A B) = .left A B := ofMorphism_eq _ _ rfl

@[simp] theorem ofMorphism_right (A B : Object sig.nBases) :
    Equality.ofMorphism (Morphism.right A B) = .right A B := ofMorphism_eq _ _ rfl

@[simp] theorem ofMorphism_eval (A B : Object sig.nBases) :
    Equality.ofMorphism (Morphism.eval A B) = .eval A B := ofMorphism_eq _ _ rfl

@[simp] theorem denote_generator (M : FinModel sig) (q : Fin sig.nGens) :
    M.denote (Morphism.generator q) = M.generator q := by
  simp [denote, denoteIntrinsic]

@[simp] theorem denote_id (M : FinModel sig) (A : Object sig.nBases) :
    M.denote (Morphism.id A) = id := by simp [denote, denoteIntrinsic]

@[simp] theorem denote_compose (M : FinModel sig) {A B C : Object sig.nBases}
    (f : Morphism sig A B) (g : Morphism sig B C) :
    M.denote (f.compose g) = fun x => M.denote g (M.denote f x) := by
  simp [denote, denoteIntrinsic]

@[simp] theorem denote_discard (M : FinModel sig) (A : Object sig.nBases) :
    M.denote (Morphism.discard A) = fun _ => PUnit.unit := by simp [denote, denoteIntrinsic]

@[simp] theorem denote_absurd (M : FinModel sig) (A : Object sig.nBases) :
    M.denote (Morphism.absurd A) = fun x => nomatch x := by simp [denote, denoteIntrinsic]

@[simp] theorem denote_first (M : FinModel sig) (A B : Object sig.nBases) :
    M.denote (Morphism.first A B) = Prod.fst := by simp [denote, denoteIntrinsic]

@[simp] theorem denote_second (M : FinModel sig) (A B : Object sig.nBases) :
    M.denote (Morphism.second A B) = Prod.snd := by simp [denote, denoteIntrinsic]

@[simp] theorem denote_pair (M : FinModel sig) {X A B : Object sig.nBases}
    (f : Morphism sig X A) (g : Morphism sig X B) :
    M.denote (f.pair g) = fun x => (M.denote f x, M.denote g x) := by
  simp [denote, denoteIntrinsic]

@[simp] theorem denote_left (M : FinModel sig) (A B : Object sig.nBases) :
    M.denote (Morphism.left A B) = Sum.inl := by simp [denote, denoteIntrinsic]

@[simp] theorem denote_right (M : FinModel sig) (A B : Object sig.nBases) :
    M.denote (Morphism.right A B) = Sum.inr := by simp [denote, denoteIntrinsic]

@[simp] theorem denote_case (M : FinModel sig) {A B X : Object sig.nBases}
    (f : Morphism sig A X) (g : Morphism sig B X) :
    M.denote (f.case g) = fun x =>
      match x with
      | .inl a => M.denote f a
      | .inr b => M.denote g b := by simp [denote, denoteIntrinsic]

@[simp] theorem denote_curry (M : FinModel sig) {X A B : Object sig.nBases}
    (f : Morphism sig (.prod X A) B) :
    M.denote f.curry = fun x a => M.denote f (x, a) := by simp [denote, denoteIntrinsic]

@[simp] theorem denote_eval (M : FinModel sig) (A B : Object sig.nBases) :
    M.denote (Morphism.eval A B) = fun f => f.1 f.2 := by simp [denote, denoteIntrinsic]

/-- Every public definitional equality is valid in every finite-set model. -/
theorem sound_defEq (M : FinModel sig) {A B : Object sig.nBases}
    {f g : Morphism sig A B} (h : DefEq f g) :
    M.denote f = M.denote g := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | cong_compose _ _ ih₁ ih₂ =>
      funext x
      simp only [denote_compose, ih₁, ih₂]
  | cong_pair _ _ ih₁ ih₂ =>
      funext x
      simp only [denote_pair, ih₁, ih₂]
  | cong_case _ _ ih₁ ih₂ =>
      funext x
      cases x <;> simp only [denote_case, ih₁, ih₂]
  | cong_curry _ ih =>
      funext x a
      simp only [denote_curry, ih]
  | id_left =>
      funext x
      simp only [denote_compose, denote_id]
      rfl
  | id_right =>
      funext x
      simp only [denote_compose, denote_id]
      rfl
  | assoc =>
      funext x
      simp only [denote_compose]
  | terminal_uniq =>
      funext x
      rfl
  | initial_uniq =>
      funext x
      exact nomatch x
  | prod_beta_first =>
      funext x
      simp only [denote_compose, denote_pair, denote_first]
  | prod_beta_second =>
      funext x
      simp only [denote_compose, denote_pair, denote_second]
  | prod_eta =>
      funext x
      simp only [denote_pair, denote_compose, denote_first, denote_second]
  | coprod_beta_left =>
      funext x
      simp only [denote_compose, denote_left, denote_case]
  | coprod_beta_right =>
      funext x
      simp only [denote_compose, denote_right, denote_case]
  | coprod_eta =>
      funext x
      cases x <;> simp only [denote_case, denote_compose, denote_left, denote_right]
  | exp_beta =>
      funext x
      simp only [denote_compose, denote_pair, denote_first, denote_second,
        denote_curry, denote_eval]
  | exp_eta =>
      funext x a
      simp only [denote_curry, denote_compose, denote_pair, denote_first,
        denote_second, denote_eval]

end FinModel

/-! ### Small semantic fixtures -/

namespace FiniteSemanticsFixtures

/-- Package an arbitrary interpretation of every opaque generator. -/
def arbitraryModel (sig : Signature) (card : Fin sig.nBases → Nat)
    (gens : (q : Fin sig.nGens) →
      SemObj card (sig.gen q).source → SemObj card (sig.gen q).target) :
    FinModel sig := ⟨card, gens⟩

/-- Two models may assign unrelated functions to the same opaque generator. -/
theorem two_arbitrary_opaque_interpretations (sig : Signature)
    (card : Fin sig.nBases → Nat)
    (gens₁ gens₂ : (q : Fin sig.nGens) →
      SemObj card (sig.gen q).source → SemObj card (sig.gen q).target)
    (q : Fin sig.nGens) :
    (arbitraryModel sig card gens₁).denote (Morphism.generator q) = gens₁ q ∧
    (arbitraryModel sig card gens₂).denote (Morphism.generator q) = gens₂ q := by
  simp [arbitraryModel]

variable {sig : Signature} (M : FinModel sig)

theorem product_beta_eta {X A B : Object sig.nBases}
    (f : Morphism sig X A) (g : Morphism sig X B)
    (h : Morphism sig X (.prod A B)) :
    M.denote ((f.pair g).compose (Morphism.first A B)) = M.denote f ∧
    M.denote
      ((h.compose (Morphism.first A B)).pair (h.compose (Morphism.second A B))) =
      M.denote h :=
  ⟨M.sound_defEq (.prod_beta_first f g), M.sound_defEq (.prod_eta h)⟩

theorem coproduct_beta_eta {A B X : Object sig.nBases}
    (f : Morphism sig A X) (g : Morphism sig B X)
    (h : Morphism sig (.coprod A B) X) :
    M.denote ((Morphism.left A B).compose (f.case g)) = M.denote f ∧
    M.denote
      (((Morphism.left A B).compose h).case ((Morphism.right A B).compose h)) =
      M.denote h :=
  ⟨M.sound_defEq (.coprod_beta_left f g), M.sound_defEq (.coprod_eta h)⟩

theorem exponential_beta_eta {X A B : Object sig.nBases}
    (f : Morphism sig (.prod X A) B) (h : Morphism sig X (.exp A B)) :
    M.denote
      ((((Morphism.first X A).compose f.curry).pair (Morphism.second X A)).compose
        (Morphism.eval A B)) = M.denote f ∧
    M.denote
      (((((Morphism.first X A).compose h).pair (Morphism.second X A)).compose
        (Morphism.eval A B)).curry) = M.denote h :=
  ⟨M.sound_defEq (.exp_beta f), M.sound_defEq (.exp_eta h)⟩

theorem zero_elimination (A : Object sig.nBases) :
    M.denote (Morphism.absurd A) = fun x => nomatch x := by
  simp only [FinModel.denote_absurd]

end FiniteSemanticsFixtures

end Gimbal
