/-
  Categorical interpretation of equality-calculus terms (Milestone 8B).
-/

import Gimbal.Equality.Algebra
import Gimbal.Equality.Translate
import Gimbal.DefinitionalEquality
import Gimbal.SyntacticCategory.BicartesianClosed

namespace Gimbal
namespace Equality

variable {sig : Signature}

open CategoryTheory

/-- Typed environment: each variable of `Γ` is a morphism from domain `X`. -/
def Env (X : Object sig.nBases) (Γ : Ctx sig) : Type :=
  ∀ {A : Object sig.nBases}, Var Γ A → IntrinsicMorphism sig X A

/-- Extend an environment under a binder: domain becomes `X × A`. -/
def Env.extend {X : Object sig.nBases} {Γ : Ctx sig} {A : Object sig.nBases}
    (ρ : Env X Γ) : Env (.prod X A) (Γ ▻ A)
  | _, .here => .second X A
  | _, .there x => .compose (.first X A) (ρ x)

/-- Precompose an environment along a renaming. -/
def Env.rename {X : Object sig.nBases} {Γ Δ : Ctx sig}
    (ρ : Env X Δ) (r : Rename sig Γ Δ) : Env X Γ :=
  fun {A} (x : Var Γ A) => ρ (r x)

/-- Add a constant binding (domain unchanged). -/
def Env.snocConst {X : Object sig.nBases} {Γ : Ctx sig} {A : Object sig.nBases}
    (ρ : Env X Γ) (c : IntrinsicMorphism sig X A) : Env X (Γ ▻ A)
  | _, .here => c
  | _, .there y => ρ y

/-- Intrinsic morphisms are definitionally equal when their public forms are. -/
def IntrinsicDefEq {A B : Object sig.nBases}
    (f g : IntrinsicMorphism sig A B) : Prop :=
  DefEq f.toMorphism g.toMorphism

/--
Distributivity `X × (A + B) → (X × A) + (X × B)`.

Implements `(x, s) ↦ case s of inl a => inl (x,a) | inr b => inr (x,b)`.
-/
def IntrinsicMorphism.distrib (X A B : Object sig.nBases) :
    IntrinsicMorphism sig
      (.prod X (.coprod A B))
      (.coprod (.prod X A) (.prod X B)) :=
  let C : Object sig.nBases := .coprod (.prod X A) (.prod X B)
  let leftBranch : IntrinsicMorphism sig A (.exp X C) :=
    .curry <|
      .compose
        (.pair (.second A X) (.first A X))
        (.left (.prod X A) (.prod X B))
  let rightBranch : IntrinsicMorphism sig B (.exp X C) :=
    .curry <|
      .compose
        (.pair (.second B X) (.first B X))
        (.right (.prod X A) (.prod X B))
  .compose
    (.pair
      (.compose
        (.second X (.coprod A B))
        (.case leftBranch rightBranch))
      (.first X (.coprod A B)))
    (.eval X C)

/-- Interpret an intrinsic term in a typed environment. -/
def interpret {X : Object sig.nBases} {Γ : Ctx sig} {A : Object sig.nBases}
    (ρ : Env X Γ) : Tm Γ A → IntrinsicMorphism sig X A
  | .var x => ρ x
  | .unit => .discard X
  | .abort t => .compose (interpret ρ t) (.absurd A)
  | .pair t u => .pair (interpret ρ t) (interpret ρ u)
  | .fst (A := A₀) (B := B₀) t =>
      .compose (interpret ρ t) (.first A₀ B₀)
  | .snd (A := A₀) (B := B₀) t =>
      .compose (interpret ρ t) (.second A₀ B₀)
  | .inl (A := A₀) (B := B₀) t =>
      .compose (interpret ρ t) (.left A₀ B₀)
  | .inr (A := A₀) (B := B₀) t =>
      .compose (interpret ρ t) (.right A₀ B₀)
  | .case (A := A₀) (B := B₀) s t u =>
      .compose
        (.pair (.id X) (interpret ρ s))
        (.compose
          (IntrinsicMorphism.distrib X A₀ B₀)
          (.case (interpret (Env.extend (A := A₀) ρ) t)
            (interpret (Env.extend (A := B₀) ρ) u)))
  | .lam (A := A₀) t =>
      .curry (interpret (Env.extend (A := A₀) ρ) t)
  | .app (A := A₀) (B := B₀) t u =>
      .compose (.pair (interpret ρ t) (interpret ρ u)) (.eval A₀ B₀)

/-- Environment of a substitution under `ρ`. -/
def Env.ofSubst {X : Object sig.nBases} {Γ Δ : Ctx sig}
    (ρ : Env X Δ) (σ : Subst sig Γ Δ) : Env X Γ :=
  fun {A} (x : Var Γ A) => interpret ρ (σ x)

/-- Constant element of `S ⇒ T` at domain `X`, from generator `q`. -/
def generatorValue (X : Object sig.nBases) (q : Fin sig.nGens) :
    IntrinsicMorphism sig X (genType sig q) :=
  let S := (sig.gen q).source
  .compose (.discard X)
    (.curry (.compose (.second .unit S) (.generator q)))

/-- Empty environment (no variables). -/
def Env.empty (X : Object sig.nBases) : Env X Ctx.empty :=
  fun {A} (x : Var Ctx.empty A) => nomatch x

/-- Environment on a generator-context prefix. -/
def genEnvPrefix (X : Object sig.nBases)
    (i : Nat) (hi : i ≤ sig.nGens) : Env X (genCtxPrefix sig i hi) :=
  match i with
  | 0 => (by rfl : genCtxPrefix sig 0 hi = Ctx.empty) ▸ Env.empty X
  | i + 1 =>
      have hi' : i ≤ sig.nGens := Nat.le_of_succ_le hi
      have i_lt : i < sig.nGens := Nat.lt_of_succ_le hi
      Env.snocConst (genEnvPrefix X i hi') (generatorValue X ⟨i, i_lt⟩)

/-- Environment interpreting every generator variable as a constant. -/
def genEnv (X : Object sig.nBases) : Env X (genCtx sig) :=
  genEnvPrefix X sig.nGens (Nat.le_refl _)

/-- Root environment for translation: generators constant, source variable = id. -/
def rootEnv (A : Object sig.nBases) : Env A (translateCtx A)
  | _, .here => .id A
  | _, .there x => genEnv A x

/-- `genEnv` at `genVar q` is the constant generator value. -/
theorem genEnv_genVar (X : Object sig.nBases) (q : Fin sig.nGens) :
    genEnv X (genVar sig q) = generatorValue X q := by
  have go (i : Nat) (hi : i ≤ sig.nGens) (q : Fin i) :
      genEnvPrefix X i hi (genVarPrefix sig i hi q) =
        generatorValue X ⟨q.val, Nat.lt_of_lt_of_le q.isLt hi⟩ := by
    induction i with
    | zero => exact nomatch q
    | succ i ih =>
        have hi' : i ≤ sig.nGens := Nat.le_of_succ_le hi
        have i_lt : i < sig.nGens := Nat.lt_of_succ_le hi
        unfold genEnvPrefix genVarPrefix
        by_cases h : q.val = i
        · -- Lookup is the newest binder.
          have hq : q = ⟨i, by omega⟩ := Fin.eq_of_val_eq h
          rw [hq]
          -- After rewrite, the `if` in `genVarPrefix` takes the `here` branch.
          simp only [Env.snocConst]
          rfl
        · simp only [h, Env.snocConst]
          exact ih hi' ⟨q.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ q.isLt) h⟩
  simpa [genEnv, genVar, genCtx] using go sig.nGens (Nat.le_refl _) ⟨q.val, q.isLt⟩

private theorem Env.extend_pointwise {X : Object sig.nBases} {Γ : Ctx sig}
    {A : Object sig.nBases} {ρ τ : Env X Γ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B), ρ x = τ x)
    {B : Object sig.nBases} (x : Var (Γ ▻ A) B) :
    Env.extend ρ x = Env.extend τ x := by
  cases x with
  | here => rfl
  | there y =>
      change IntrinsicMorphism.compose
        (IntrinsicMorphism.first X A) (ρ y) =
        IntrinsicMorphism.compose
          (IntrinsicMorphism.first X A) (τ y)
      rw [h y]

/-- Pointwise-equal environments give identical interpretations. -/
theorem interpret_eq_of_pointwise {X : Object sig.nBases} {Γ : Ctx sig}
    {A : Object sig.nBases} {ρ τ : Env X Γ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B), ρ x = τ x)
    (t : Tm Γ A) : interpret ρ t = interpret τ t := by
  revert X ρ τ h
  induction t with
  | var x =>
      intro X ρ τ h
      exact h x
  | unit =>
      intro X ρ τ h
      rfl
  | abort t ih =>
      intro X ρ τ h
      change IntrinsicMorphism.compose (interpret ρ t) _ =
        IntrinsicMorphism.compose (interpret τ t) _
      rw [ih h]
  | pair t u iht ihu =>
      intro X ρ τ h
      change IntrinsicMorphism.pair (interpret ρ t) (interpret ρ u) =
        IntrinsicMorphism.pair (interpret τ t) (interpret τ u)
      rw [iht h, ihu h]
  | fst t ih =>
      intro X ρ τ h
      change IntrinsicMorphism.compose (interpret ρ t) _ =
        IntrinsicMorphism.compose (interpret τ t) _
      rw [ih h]
  | snd t ih =>
      intro X ρ τ h
      change IntrinsicMorphism.compose (interpret ρ t) _ =
        IntrinsicMorphism.compose (interpret τ t) _
      rw [ih h]
  | inl t ih =>
      intro X ρ τ h
      change IntrinsicMorphism.compose (interpret ρ t) _ =
        IntrinsicMorphism.compose (interpret τ t) _
      rw [ih h]
  | inr t ih =>
      intro X ρ τ h
      change IntrinsicMorphism.compose (interpret ρ t) _ =
        IntrinsicMorphism.compose (interpret τ t) _
      rw [ih h]
  | case s t u ihs iht ihu =>
      intro X ρ τ h
      change IntrinsicMorphism.compose
          (IntrinsicMorphism.pair (IntrinsicMorphism.id X) (interpret ρ s))
          (IntrinsicMorphism.compose _ (IntrinsicMorphism.case
            (interpret (Env.extend ρ) t) (interpret (Env.extend ρ) u))) =
        IntrinsicMorphism.compose
          (IntrinsicMorphism.pair (IntrinsicMorphism.id X) (interpret τ s))
          (IntrinsicMorphism.compose _ (IntrinsicMorphism.case
            (interpret (Env.extend τ) t) (interpret (Env.extend τ) u)))
      rw [ihs h, iht (Env.extend_pointwise h), ihu (Env.extend_pointwise h)]
  | lam t ih =>
      intro X ρ τ h
      change IntrinsicMorphism.curry (interpret (Env.extend ρ) t) =
        IntrinsicMorphism.curry (interpret (Env.extend τ) t)
      rw [ih (Env.extend_pointwise h)]
  | app t u iht ihu =>
      intro X ρ τ h
      change IntrinsicMorphism.compose
          (IntrinsicMorphism.pair (interpret ρ t) (interpret ρ u)) _ =
        IntrinsicMorphism.compose
          (IntrinsicMorphism.pair (interpret τ t) (interpret τ u)) _
      rw [iht h, ihu h]

private theorem Env.rename_extend_pointwise {X : Object sig.nBases}
    {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Env X Δ) (r : Rename sig Γ Δ)
    {B : Object sig.nBases} (x : Var (Γ ▻ A) B) :
    Env.rename (Env.extend ρ) (Rename.ext r) x =
      Env.extend (Env.rename ρ r) x := by
  cases x <;> rfl

/-- Interpretation commutes with renaming. -/
theorem interpret_rename {X : Object sig.nBases} {Γ Δ : Ctx sig}
    {A : Object sig.nBases} (ρ : Env X Δ) (r : Rename sig Γ Δ)
    (t : Tm Γ A) :
    interpret ρ (rename r t) = interpret (Env.rename ρ r) t := by
  induction t generalizing Δ X with
  | var | unit => rfl
  | abort t ih => simp [rename, interpret, ih]
  | pair t u iht ihu => simp [rename, interpret, iht, ihu]
  | fst t ih | snd t ih | inl t ih | inr t ih =>
      simp [rename, interpret, ih]
  | case s t u ihs iht ihu =>
      change IntrinsicMorphism.compose
          (IntrinsicMorphism.pair (IntrinsicMorphism.id X)
            (interpret ρ (rename r s)))
          (IntrinsicMorphism.compose _ (IntrinsicMorphism.case
            (interpret (Env.extend ρ) (rename (Rename.ext r) t))
            (interpret (Env.extend ρ) (rename (Rename.ext r) u)))) =
        IntrinsicMorphism.compose
          (IntrinsicMorphism.pair (IntrinsicMorphism.id X)
            (interpret (Env.rename ρ r) s))
          (IntrinsicMorphism.compose _ (IntrinsicMorphism.case
            (interpret (Env.extend (Env.rename ρ r)) t)
            (interpret (Env.extend (Env.rename ρ r)) u)))
      rw [ihs ρ r, iht (Env.extend ρ) (Rename.ext r),
        ihu (Env.extend ρ) (Rename.ext r)]
      rw [interpret_eq_of_pointwise (Env.rename_extend_pointwise ρ r) t,
        interpret_eq_of_pointwise (Env.rename_extend_pointwise ρ r) u]
  | lam t ih =>
      change IntrinsicMorphism.curry
          (interpret (Env.extend ρ) (rename (Rename.ext r) t)) =
        IntrinsicMorphism.curry
          (interpret (Env.extend (Env.rename ρ r)) t)
      rw [ih (Env.extend ρ) (Rename.ext r)]
      rw [interpret_eq_of_pointwise (Env.rename_extend_pointwise ρ r) t]
  | app t u iht ihu => simp [rename, interpret, iht, ihu]

private abbrev quotientObject (A : Object sig.nBases) : «CΣ» sig :=
  ⟨A⟩

private def quotientMorphism {A B : Object sig.nBases}
    (f : IntrinsicMorphism sig A B) :
    «CΣ».Hom (quotientObject A) (quotientObject B) :=
  «CΣ».Hom.mk f.toMorphism

private theorem intrinsicDefEq_of_quotient_eq
    {A B : Object sig.nBases} {f g : IntrinsicMorphism sig A B}
    (h : quotientMorphism f = quotientMorphism g) :
    IntrinsicDefEq f g :=
  («CΣ».Hom.mk_eq_mk_iff f.toMorphism g.toMorphism).mp h

private theorem quotient_eq_of_intrinsicDefEq
    {A B : Object sig.nBases} {f g : IntrinsicMorphism sig A B}
    (h : IntrinsicDefEq f g) :
    quotientMorphism f = quotientMorphism g :=
  («CΣ».Hom.mk_eq_mk_iff f.toMorphism g.toMorphism).mpr h

private theorem quotientMorphism_compose
    {A B C : Object sig.nBases}
    (f : IntrinsicMorphism sig A B) (g : IntrinsicMorphism sig B C) :
    quotientMorphism (.compose f g) =
      «CΣ».Hom.comp (quotientMorphism f) (quotientMorphism g) :=
  rfl

private theorem quotientMorphism_pair
    {X A B : Object sig.nBases}
    (f : IntrinsicMorphism sig X A) (g : IntrinsicMorphism sig X B) :
    quotientMorphism (.pair f g) =
      «CΣ».Hom.pair (quotientMorphism f) (quotientMorphism g) :=
  rfl

private theorem quotientMorphism_curry
    {X A B : Object sig.nBases}
    (f : IntrinsicMorphism sig (.prod X A) B) :
    quotientMorphism (.curry f) =
      «CΣ».Hom.curry (quotientMorphism f) :=
  rfl

private theorem quotientMorphism_case
    {A B X : Object sig.nBases}
    (f : IntrinsicMorphism sig A X) (g : IntrinsicMorphism sig B X) :
    quotientMorphism (.case f g) =
      «CΣ».Hom.case (quotientMorphism f) (quotientMorphism g) :=
  rfl

private theorem interpret_quotient_eq_of_pointwise
    {X : Object sig.nBases} {Γ : Ctx sig} {A : Object sig.nBases}
    {ρ τ : Env X Γ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B),
      quotientMorphism (ρ x) = quotientMorphism (τ x))
    (t : Tm Γ A) :
    quotientMorphism (interpret ρ t) = quotientMorphism (interpret τ t) := by
  revert X ρ τ h
  induction t with
  | var x =>
      intro X ρ τ h
      exact h x
  | unit =>
      intro X ρ τ h
      rfl
  | abort t ih =>
      intro X ρ τ h
      change quotientMorphism (.compose (interpret ρ t) _) =
        quotientMorphism (.compose (interpret τ t) _)
      rw [quotientMorphism_compose, quotientMorphism_compose, ih h]
  | pair t u iht ihu =>
      intro X ρ τ h
      change «CΣ».Hom.pair
          (quotientMorphism (interpret ρ t)) (quotientMorphism (interpret ρ u)) =
        «CΣ».Hom.pair
          (quotientMorphism (interpret τ t)) (quotientMorphism (interpret τ u))
      rw [iht h, ihu h]
  | fst t ih =>
      intro X ρ τ h
      change quotientMorphism (.compose (interpret ρ t) (.first _ _)) =
        quotientMorphism (.compose (interpret τ t) (.first _ _))
      rw [quotientMorphism_compose, quotientMorphism_compose, ih h]
  | snd t ih =>
      intro X ρ τ h
      change quotientMorphism (.compose (interpret ρ t) (.second _ _)) =
        quotientMorphism (.compose (interpret τ t) (.second _ _))
      rw [quotientMorphism_compose, quotientMorphism_compose, ih h]
  | inl t ih =>
      intro X ρ τ h
      change quotientMorphism (.compose (interpret ρ t) (.left _ _)) =
        quotientMorphism (.compose (interpret τ t) (.left _ _))
      rw [quotientMorphism_compose, quotientMorphism_compose, ih h]
  | inr t ih =>
      intro X ρ τ h
      change quotientMorphism (.compose (interpret ρ t) (.right _ _)) =
        quotientMorphism (.compose (interpret τ t) (.right _ _))
      rw [quotientMorphism_compose, quotientMorphism_compose, ih h]
  | case s t u ihs iht ihu =>
      intro X ρ τ h
      change quotientMorphism
          (.compose (.pair (.id X) (interpret ρ s))
            (.compose _ (.case
              (interpret (Env.extend ρ) t) (interpret (Env.extend ρ) u)))) =
        quotientMorphism
          (.compose (.pair (.id X) (interpret τ s))
            (.compose _ (.case
              (interpret (Env.extend τ) t) (interpret (Env.extend τ) u))))
      simp only [quotientMorphism_compose, quotientMorphism_pair,
        quotientMorphism_case]
      rw [ihs h]
      rw [iht (ρ := Env.extend ρ) (τ := Env.extend τ) (fun x => by
        cases x with
        | here => rfl
        | there y =>
            change quotientMorphism (.compose _ (ρ y)) =
              quotientMorphism (.compose _ (τ y))
            rw [quotientMorphism_compose, quotientMorphism_compose, h y])]
      rw [ihu (ρ := Env.extend ρ) (τ := Env.extend τ) (fun x => by
        cases x with
        | here => rfl
        | there y =>
            change quotientMorphism (.compose _ (ρ y)) =
              quotientMorphism (.compose _ (τ y))
            rw [quotientMorphism_compose, quotientMorphism_compose, h y])]
  | lam t ih =>
      intro X ρ τ h
      change quotientMorphism (.curry (interpret (Env.extend ρ) t)) =
        quotientMorphism (.curry (interpret (Env.extend τ) t))
      rw [quotientMorphism_curry, quotientMorphism_curry]
      rw [ih (ρ := Env.extend ρ) (τ := Env.extend τ) (fun x => by
        cases x with
        | here => rfl
        | there y =>
            change quotientMorphism (.compose _ (ρ y)) =
              quotientMorphism (.compose _ (τ y))
            rw [quotientMorphism_compose, quotientMorphism_compose, h y])]
  | app t u iht ihu =>
      intro X ρ τ h
      change quotientMorphism
          (.compose (.pair (interpret ρ t) (interpret ρ u)) _) =
        quotientMorphism
          (.compose (.pair (interpret τ t) (interpret τ u)) _)
      rw [quotientMorphism_compose, quotientMorphism_compose,
        quotientMorphism_pair, quotientMorphism_pair, iht h, ihu h]

/-- Pointwise definitionally equal environments give definitionally equal interpretations. -/
theorem interpret_defeq_of_pointwise
    {X : Object sig.nBases} {Γ : Ctx sig} {A : Object sig.nBases}
    {ρ τ : Env X Γ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B),
      IntrinsicDefEq (ρ x) (τ x))
    (t : Tm Γ A) :
    IntrinsicDefEq (interpret ρ t) (interpret τ t) := by
  apply intrinsicDefEq_of_quotient_eq
  apply interpret_quotient_eq_of_pointwise
  intro B x
  exact quotient_eq_of_intrinsicDefEq (h x)

private theorem quotient_comp_pair
    {X Y A B : Object sig.nBases}
    (f : «CΣ».Hom (quotientObject X) (quotientObject Y))
    (g : «CΣ».Hom (quotientObject Y) (quotientObject A))
    (h : «CΣ».Hom (quotientObject Y) (quotientObject B)) :
    «CΣ».Hom.comp f («CΣ».Hom.pair g h) =
      «CΣ».Hom.pair («CΣ».Hom.comp f g) («CΣ».Hom.comp f h) := by
  apply «CΣ».Hom.pair_unique
  · change «CΣ».Hom.comp
      («CΣ».Hom.comp f («CΣ».Hom.pair g h)) («CΣ».Hom.first _ _) =
        «CΣ».Hom.comp f g
    rw [«CΣ».Hom.assoc]
    exact congrArg («CΣ».Hom.comp f) («CΣ».Hom.pair_first g h)
  · change «CΣ».Hom.comp
      («CΣ».Hom.comp f («CΣ».Hom.pair g h)) («CΣ».Hom.second _ _) =
        «CΣ».Hom.comp f h
    rw [«CΣ».Hom.assoc]
    exact congrArg («CΣ».Hom.comp f) («CΣ».Hom.pair_second g h)

/-- Generator constants are natural in their domain. -/
theorem genEnv_genVar_natural
    {X Y : Object sig.nBases} (f : IntrinsicMorphism sig X Y)
    (q : Fin sig.nGens) :
    IntrinsicDefEq
      (.compose f (genEnv Y (genVar sig q)))
      (genEnv X (genVar sig q)) := by
  rw [genEnv_genVar, genEnv_genVar]
  apply intrinsicDefEq_of_quotient_eq
  simp only [generatorValue, quotientMorphism_compose]
  rw [← «CΣ».Hom.assoc]
  exact congrArg
    (fun z => «CΣ».Hom.comp z
      (quotientMorphism
        (.curry (.compose (.second .unit (sig.gen q).source) (.generator q)))))
    («CΣ».Hom.terminal_uniq
      («CΣ».Hom.comp (quotientMorphism f)
        (quotientMorphism (IntrinsicMorphism.discard Y))))

/-- Translation retraction for opaque generators. -/
theorem interpret_translate_generator (q : Fin sig.nGens) :
    IntrinsicDefEq
      (interpret (rootEnv (sig.gen q).source)
        (translate (IntrinsicMorphism.generator q)))
      (.generator q) := by
  apply intrinsicDefEq_of_quotient_eq
  let S := (sig.gen q).source
  let T := (sig.gen q).target
  change quotientMorphism
      (IntrinsicMorphism.compose
        (IntrinsicMorphism.pair
          (rootEnv S (.there (genVar sig q)))
          (rootEnv S .here))
        (IntrinsicMorphism.eval S T)) =
    quotientMorphism (IntrinsicMorphism.generator q)
  rw [show rootEnv S (.there (genVar sig q)) = generatorValue S q by
      exact genEnv_genVar S q]
  change quotientMorphism
      (IntrinsicMorphism.compose
        (IntrinsicMorphism.pair (generatorValue S q) (IntrinsicMorphism.id S))
        (IntrinsicMorphism.eval S T)) =
    quotientMorphism (IntrinsicMorphism.generator q)
  let drop : «CΣ».Hom (quotientObject S) (quotientObject .unit) :=
    quotientMorphism (IntrinsicMorphism.discard S)
  let fstUS : «CΣ».Hom
      («CΣ».prodObj (quotientObject .unit) (quotientObject S))
      (quotientObject .unit) :=
    quotientMorphism (IntrinsicMorphism.first .unit S)
  let sndUS : «CΣ».Hom
      («CΣ».prodObj (quotientObject .unit) (quotientObject S))
      (quotientObject S) :=
    quotientMorphism (IntrinsicMorphism.second .unit S)
  let gen : «CΣ».Hom (quotientObject S) (quotientObject T) :=
    quotientMorphism (IntrinsicMorphism.generator q)
  let k : «CΣ».Hom
      («CΣ».prodObj (quotientObject .unit) (quotientObject S))
      (quotientObject T) :=
    «CΣ».Hom.comp sndUS gen
  let ev : «CΣ».Hom
      (quotientObject (.prod (.exp S T) S)) (quotientObject T) :=
    quotientMorphism (IntrinsicMorphism.eval S T)
  let into : «CΣ».Hom (quotientObject S)
      («CΣ».prodObj (quotientObject .unit) (quotientObject S)) :=
    «CΣ».Hom.pair drop («CΣ».Hom.id (quotientObject S))
  change
    «CΣ».Hom.comp
      («CΣ».Hom.pair
        («CΣ».Hom.comp drop («CΣ».Hom.curry k))
        («CΣ».Hom.id (quotientObject S)))
      ev = gen
  have hpair :
      «CΣ».Hom.comp into
          («CΣ».Hom.pair
            («CΣ».Hom.comp fstUS («CΣ».Hom.curry k)) sndUS) =
        «CΣ».Hom.pair
          («CΣ».Hom.comp drop («CΣ».Hom.curry k))
          («CΣ».Hom.id (quotientObject S)) := by
    refine (quotient_comp_pair into
      («CΣ».Hom.comp fstUS («CΣ».Hom.curry k)) sndUS).trans ?_
    apply congrArg₂ «CΣ».Hom.pair
    · rw [← «CΣ».Hom.assoc]
      exact congrArg
        (fun z => «CΣ».Hom.comp z («CΣ».Hom.curry k))
        («CΣ».Hom.pair_first drop («CΣ».Hom.id (quotientObject S)))
    · exact «CΣ».Hom.pair_second drop («CΣ».Hom.id (quotientObject S))
  rw [← hpair, «CΣ».Hom.assoc]
  change «CΣ».Hom.comp into («CΣ».Hom.uncurry («CΣ».Hom.curry k)) = gen
  rw [«CΣ».Hom.uncurry_curry]
  change «CΣ».Hom.comp into («CΣ».Hom.comp sndUS gen) = gen
  rw [← «CΣ».Hom.assoc]
  have hsnd : «CΣ».Hom.comp into sndUS =
      «CΣ».Hom.id (quotientObject S) :=
    «CΣ».Hom.pair_second drop («CΣ».Hom.id (quotientObject S))
  rw [hsnd, «CΣ».Hom.id_comp]

/-- Translation retraction for identities. -/
theorem interpret_translate_id (A : Object sig.nBases) :
    IntrinsicDefEq
      (interpret (rootEnv A) (translate (IntrinsicMorphism.id A)))
      (.id A) := by
  exact DefEq.refl _

/-- Translation retraction for terminal maps. -/
theorem interpret_translate_discard (A : Object sig.nBases) :
    IntrinsicDefEq
      (interpret (rootEnv A) (translate (IntrinsicMorphism.discard A)))
      (.discard A) := by
  exact DefEq.refl _

/-- Translation retraction for initial maps. -/
theorem interpret_translate_absurd (A : Object sig.nBases) :
    IntrinsicDefEq
      (interpret (rootEnv (.never : Object sig.nBases))
        (translate (IntrinsicMorphism.absurd A)))
      (.absurd A) := by
  change DefEq
    ((Morphism.id (.never : Object sig.nBases)).compose (Morphism.absurd A))
    (Morphism.absurd A)
  exact DefEq.id_left _

/-- Translation retraction for the first product projection. -/
theorem interpret_translate_first (A B : Object sig.nBases) :
    IntrinsicDefEq
      (interpret (rootEnv (.prod A B))
        (translate (IntrinsicMorphism.first A B)))
      (.first A B) := by
  change DefEq
    ((Morphism.id (.prod A B)).compose (Morphism.first A B))
    (Morphism.first A B)
  exact DefEq.id_left _

/-- Translation retraction for the second product projection. -/
theorem interpret_translate_second (A B : Object sig.nBases) :
    IntrinsicDefEq
      (interpret (rootEnv (.prod A B))
        (translate (IntrinsicMorphism.second A B)))
      (.second A B) := by
  change DefEq
    ((Morphism.id (.prod A B)).compose (Morphism.second A B))
    (Morphism.second A B)
  exact DefEq.id_left _

/-- Translation retraction for the left coproduct injection. -/
theorem interpret_translate_left (A B : Object sig.nBases) :
    IntrinsicDefEq
      (interpret (rootEnv A) (translate (IntrinsicMorphism.left A B)))
      (.left A B) := by
  change DefEq
    ((Morphism.id A).compose (Morphism.left A B))
    (Morphism.left A B)
  exact DefEq.id_left _

/-- Translation retraction for the right coproduct injection. -/
theorem interpret_translate_right (A B : Object sig.nBases) :
    IntrinsicDefEq
      (interpret (rootEnv B) (translate (IntrinsicMorphism.right A B)))
      (.right A B) := by
  change DefEq
    ((Morphism.id B).compose (Morphism.right A B))
    (Morphism.right A B)
  exact DefEq.id_left _

/-- The translation retraction is closed under pairing. -/
theorem interpret_translate_pair {X A B : Object sig.nBases}
    (f : IntrinsicMorphism sig X A) (g : IntrinsicMorphism sig X B)
    (hf : IntrinsicDefEq (interpret (rootEnv X) (translate f)) f)
    (hg : IntrinsicDefEq (interpret (rootEnv X) (translate g)) g) :
    IntrinsicDefEq
      (interpret (rootEnv X) (translate (IntrinsicMorphism.pair f g)))
      (.pair f g) := by
  exact DefEq.cong_pair hf hg

/-- Translation retraction for evaluation. -/
theorem interpret_translate_eval (A B : Object sig.nBases) :
    IntrinsicDefEq
      (interpret (rootEnv (.prod (.exp A B) A))
        (translate (IntrinsicMorphism.eval A B)))
      (.eval A B) := by
  let X : Object sig.nBases := .prod (.exp A B) A
  let ev : Morphism sig (.prod (.exp A B) A) B :=
    Morphism.eval A B
  change DefEq
    ((((Morphism.id X).compose (Morphism.first (.exp A B) A)).pair
      ((Morphism.id X).compose (Morphism.second (.exp A B) A))).compose ev)
    ev
  refine DefEq.trans
    (DefEq.cong_compose
      (DefEq.cong_pair
        (DefEq.id_left (Morphism.first (.exp A B) A))
        (DefEq.id_left (Morphism.second (.exp A B) A)))
      (DefEq.refl ev)) ?_
  refine DefEq.trans
    (DefEq.cong_compose
      (DefEq.symm (DefEq.cong_pair
        (DefEq.id_left (Morphism.first (.exp A B) A))
        (DefEq.id_left (Morphism.second (.exp A B) A))))
      (DefEq.refl ev)) ?_
  refine DefEq.trans
    (DefEq.cong_compose (DefEq.prod_eta (Morphism.id X)) (DefEq.refl ev)) ?_
  exact DefEq.id_left ev

/-! ### Arrow-typed aliases for the `«CΣ»` combinators

The `«CΣ».Hom.*` combinators are typed in the unbundled `«CΣ».Hom` family. That
family does not unify with `⟶` while the endpoints are still metavariables, so
`≫` cannot be elaborated in their argument positions. These aliases restate the
same maps with `⟶` results, and the lemmas below restate the universal
properties over them.
-/

private abbrev cfst (A B : «CΣ» sig) : «CΣ».prodObj A B ⟶ A :=
  «CΣ».Hom.first A B

private abbrev csnd (A B : «CΣ» sig) : «CΣ».prodObj A B ⟶ B :=
  «CΣ».Hom.second A B

private abbrev cpair {X A B : «CΣ» sig} (f : X ⟶ A) (g : X ⟶ B) :
    X ⟶ «CΣ».prodObj A B :=
  «CΣ».Hom.pair f g

private abbrev cinl (A B : «CΣ» sig) : A ⟶ «CΣ».coprodObj A B :=
  «CΣ».Hom.left A B

private abbrev cinr (A B : «CΣ» sig) : B ⟶ «CΣ».coprodObj A B :=
  «CΣ».Hom.right A B

private abbrev ccase {A B X : «CΣ» sig} (f : A ⟶ X) (g : B ⟶ X) :
    «CΣ».coprodObj A B ⟶ X :=
  «CΣ».Hom.case f g

private abbrev ccurry {X A B : «CΣ» sig} (f : «CΣ».prodObj X A ⟶ B) :
    X ⟶ «CΣ».expObj A B :=
  «CΣ».Hom.curry f

private abbrev cuncurry {X A B : «CΣ» sig} (h : X ⟶ «CΣ».expObj A B) :
    «CΣ».prodObj X A ⟶ B :=
  «CΣ».Hom.uncurry h

private abbrev cev (A B : «CΣ» sig) :
    «CΣ».prodObj («CΣ».expObj A B) A ⟶ B :=
  «CΣ».Hom.eval A B

private abbrev cdrop (A : «CΣ» sig) : A ⟶ «CΣ».unitObj :=
  «CΣ».Hom.discard A

@[simp] private theorem cpair_cfst {X A B : «CΣ» sig} (f : X ⟶ A) (g : X ⟶ B) :
    cpair f g ≫ cfst A B = f :=
  «CΣ».Hom.pair_first f g

@[simp] private theorem cpair_csnd {X A B : «CΣ» sig} (f : X ⟶ A) (g : X ⟶ B) :
    cpair f g ≫ csnd A B = g :=
  «CΣ».Hom.pair_second f g

@[simp] private theorem cpair_cfst_assoc {X A B Z : «CΣ» sig}
    (f : X ⟶ A) (g : X ⟶ B) (k : A ⟶ Z) :
    cpair f g ≫ cfst A B ≫ k = f ≫ k := by
  rw [← Category.assoc, cpair_cfst]

@[simp] private theorem cpair_csnd_assoc {X A B Z : «CΣ» sig}
    (f : X ⟶ A) (g : X ⟶ B) (k : B ⟶ Z) :
    cpair f g ≫ csnd A B ≫ k = g ≫ k := by
  rw [← Category.assoc, cpair_csnd]

private theorem cpair_unique {X A B : «CΣ» sig} {f : X ⟶ A} {g : X ⟶ B}
    (h : X ⟶ «CΣ».prodObj A B) (hf : h ≫ cfst A B = f) (hg : h ≫ csnd A B = g) :
    h = cpair f g :=
  «CΣ».Hom.pair_unique h hf hg

private theorem cpair_eta {X A B : «CΣ» sig} (h : X ⟶ «CΣ».prodObj A B) :
    cpair (h ≫ cfst A B) (h ≫ csnd A B) = h :=
  «CΣ».Hom.prod_eta h

@[simp] private theorem cinl_ccase {A B X : «CΣ» sig} (f : A ⟶ X) (g : B ⟶ X) :
    cinl A B ≫ ccase f g = f :=
  «CΣ».Hom.left_case f g

@[simp] private theorem cinr_ccase {A B X : «CΣ» sig} (f : A ⟶ X) (g : B ⟶ X) :
    cinr A B ≫ ccase f g = g :=
  «CΣ».Hom.right_case f g

@[simp] private theorem cinl_ccase_assoc {A B X Z : «CΣ» sig}
    (f : A ⟶ X) (g : B ⟶ X) (k : X ⟶ Z) :
    cinl A B ≫ ccase f g ≫ k = f ≫ k := by
  rw [← Category.assoc, cinl_ccase]

@[simp] private theorem cinr_ccase_assoc {A B X Z : «CΣ» sig}
    (f : A ⟶ X) (g : B ⟶ X) (k : X ⟶ Z) :
    cinr A B ≫ ccase f g ≫ k = g ≫ k := by
  rw [← Category.assoc, cinr_ccase]

private theorem ccase_unique {A B X : «CΣ» sig} {f : A ⟶ X} {g : B ⟶ X}
    (h : «CΣ».coprodObj A B ⟶ X) (hf : cinl A B ≫ h = f) (hg : cinr A B ≫ h = g) :
    h = ccase f g :=
  «CΣ».Hom.case_unique h hf hg

private theorem ccase_eta {A B X : «CΣ» sig} (h : «CΣ».coprodObj A B ⟶ X) :
    ccase (cinl A B ≫ h) (cinr A B ≫ h) = h :=
  «CΣ».Hom.coprod_eta h

@[simp] private theorem cuncurry_ccurry {X A B : «CΣ» sig}
    (f : «CΣ».prodObj X A ⟶ B) :
    cuncurry (ccurry f) = f :=
  «CΣ».Hom.uncurry_curry f

@[simp] private theorem ccurry_cuncurry {X A B : «CΣ» sig}
    (h : X ⟶ «CΣ».expObj A B) :
    ccurry (cuncurry h) = h :=
  «CΣ».Hom.curry_uncurry h

private theorem cuncurry_def {X A B : «CΣ» sig} (h : X ⟶ «CΣ».expObj A B) :
    cuncurry h = cpair (cfst X A ≫ h) (csnd X A) ≫ cev A B :=
  rfl

private theorem cterminal_uniq {A : «CΣ» sig} (f : A ⟶ «CΣ».unitObj) :
    f = cdrop A :=
  «CΣ».Hom.terminal_uniq f

/-! ### Quotient bridge stated with categorical notation -/

private def qm {A B : Object sig.nBases} (f : IntrinsicMorphism sig A B) :
    quotientObject A ⟶ quotientObject B :=
  quotientMorphism f

private theorem intrinsicDefEq_of_qm_eq {A B : Object sig.nBases}
    {f g : IntrinsicMorphism sig A B} (h : qm f = qm g) : IntrinsicDefEq f g :=
  intrinsicDefEq_of_quotient_eq h

private theorem qm_eq_of_intrinsicDefEq {A B : Object sig.nBases}
    {f g : IntrinsicMorphism sig A B} (h : IntrinsicDefEq f g) : qm f = qm g :=
  quotient_eq_of_intrinsicDefEq h

@[simp] private theorem qm_compose {A B C : Object sig.nBases}
    (f : IntrinsicMorphism sig A B) (g : IntrinsicMorphism sig B C) :
    qm (.compose f g) = qm f ≫ qm g :=
  rfl

@[simp] private theorem qm_pair {X A B : Object sig.nBases}
    (f : IntrinsicMorphism sig X A) (g : IntrinsicMorphism sig X B) :
    qm (.pair f g) = cpair (qm f) (qm g) :=
  rfl

@[simp] private theorem qm_case {A B X : Object sig.nBases}
    (f : IntrinsicMorphism sig A X) (g : IntrinsicMorphism sig B X) :
    qm (.case f g) = ccase (qm f) (qm g) :=
  rfl

@[simp] private theorem qm_curry {X A B : Object sig.nBases}
    (f : IntrinsicMorphism sig (.prod X A) B) :
    qm (.curry f) = ccurry (qm f) :=
  rfl

@[simp] private theorem qm_id (A : Object sig.nBases) :
    qm (IntrinsicMorphism.id A) = 𝟙 (quotientObject A) :=
  rfl

@[simp] private theorem qm_discard (A : Object sig.nBases) :
    qm (IntrinsicMorphism.discard A) = cdrop (quotientObject A) :=
  rfl

@[simp] private theorem qm_first (A B : Object sig.nBases) :
    qm (IntrinsicMorphism.first A B) = cfst (quotientObject A) (quotientObject B) :=
  rfl

@[simp] private theorem qm_second (A B : Object sig.nBases) :
    qm (IntrinsicMorphism.second A B) = csnd (quotientObject A) (quotientObject B) :=
  rfl

@[simp] private theorem qm_left (A B : Object sig.nBases) :
    qm (IntrinsicMorphism.left A B) = cinl (quotientObject A) (quotientObject B) :=
  rfl

@[simp] private theorem qm_right (A B : Object sig.nBases) :
    qm (IntrinsicMorphism.right A B) = cinr (quotientObject A) (quotientObject B) :=
  rfl

@[simp] private theorem qm_eval (A B : Object sig.nBases) :
    qm (IntrinsicMorphism.eval A B) = cev (quotientObject A) (quotientObject B) :=
  rfl

/-! ### Product plumbing in `«CΣ»` -/

/-- Exchange the two factors of a chosen product. -/
private def csSwap (A B : «CΣ» sig) : «CΣ».prodObj A B ⟶ «CΣ».prodObj B A :=
  cpair (csnd A B) (cfst A B)

/-- Act on the left factor of a chosen product. -/
private def csProdFst {X Y : «CΣ» sig} (f : X ⟶ Y) (A : «CΣ» sig) :
    «CΣ».prodObj X A ⟶ «CΣ».prodObj Y A :=
  cpair (cfst X A ≫ f) (csnd X A)

/-- Act on the right factor of a chosen product. -/
private def csProdSnd (X : «CΣ» sig) {A B : «CΣ» sig} (g : A ⟶ B) :
    «CΣ».prodObj X A ⟶ «CΣ».prodObj X B :=
  cpair (cfst X A) (csnd X A ≫ g)

private theorem cs_comp_pair {W X A B : «CΣ» sig}
    (f : W ⟶ X) (g : X ⟶ A) (h : X ⟶ B) :
    f ≫ cpair g h = cpair (f ≫ g) (f ≫ h) := by
  refine cpair_unique _ ?_ ?_ <;> simp

private theorem cs_case_comp {A B X Y : «CΣ» sig}
    (f : A ⟶ X) (g : B ⟶ X) (k : X ⟶ Y) :
    ccase f g ≫ k = ccase (f ≫ k) (g ≫ k) := by
  refine ccase_unique _ ?_ ?_ <;> simp

private theorem cs_pair_fst_snd (A B : «CΣ» sig) :
    cpair (cfst A B) (csnd A B) = 𝟙 («CΣ».prodObj A B) := by
  simpa using cpair_eta (𝟙 («CΣ».prodObj A B))

@[simp] private theorem csSwap_cfst (A B : «CΣ» sig) :
    csSwap A B ≫ cfst B A = csnd A B := by
  simp [csSwap]

@[simp] private theorem csSwap_csnd (A B : «CΣ» sig) :
    csSwap A B ≫ csnd B A = cfst A B := by
  simp [csSwap]

@[simp] private theorem csSwap_cfst_assoc {A B Z : «CΣ» sig} (k : B ⟶ Z) :
    csSwap A B ≫ cfst B A ≫ k = csnd A B ≫ k := by
  rw [← Category.assoc, csSwap_cfst]

@[simp] private theorem csSwap_csnd_assoc {A B Z : «CΣ» sig} (k : A ⟶ Z) :
    csSwap A B ≫ csnd B A ≫ k = cfst A B ≫ k := by
  rw [← Category.assoc, csSwap_csnd]

private theorem csSwap_csSwap (A B : «CΣ» sig) :
    csSwap A B ≫ csSwap B A = 𝟙 («CΣ».prodObj A B) := by
  rw [← cs_pair_fst_snd A B]
  refine cpair_unique _ ?_ ?_ <;> simp

private theorem csProdSnd_csSwap (X : «CΣ» sig) {A B : «CΣ» sig} (g : A ⟶ B) :
    csProdSnd X g ≫ csSwap X B = csSwap X A ≫ csProdFst g X := by
  have h1 : csProdSnd X g ≫ csSwap X B = cpair (csnd X A ≫ g) (cfst X A) := by
    refine cpair_unique _ ?_ ?_ <;> simp [csProdSnd]
  have h2 : csSwap X A ≫ csProdFst g X = cpair (csnd X A ≫ g) (cfst X A) := by
    refine cpair_unique _ ?_ ?_ <;> simp [csProdFst]
  rw [h1, h2]

private theorem csProdFst_csSwap {A B : «CΣ» sig} (u : A ⟶ B) (X : «CΣ» sig) :
    csProdFst u X ≫ csSwap B X = csSwap A X ≫ csProdSnd X u := by
  have h1 : csProdFst u X ≫ csSwap B X = cpair (csnd A X) (cfst A X ≫ u) := by
    refine cpair_unique _ ?_ ?_ <;> simp [csProdFst]
  have h2 : csSwap A X ≫ csProdSnd X u = cpair (csnd A X) (cfst A X ≫ u) := by
    refine cpair_unique _ ?_ ?_ <;> simp [csProdSnd]
  rw [h1, h2]

private theorem csProdSnd_csProdFst {X Y A B : «CΣ» sig} (f : X ⟶ Y) (u : A ⟶ B) :
    csProdSnd X u ≫ csProdFst f B = csProdFst f A ≫ csProdSnd Y u := by
  have h1 : csProdSnd X u ≫ csProdFst f B =
      cpair (cfst X A ≫ f) (csnd X A ≫ u) := by
    refine cpair_unique _ ?_ ?_ <;> simp [csProdSnd, csProdFst]
  have h2 : csProdFst f A ≫ csProdSnd Y u =
      cpair (cfst X A ≫ f) (csnd X A ≫ u) := by
    refine cpair_unique _ ?_ ?_ <;> simp [csProdSnd, csProdFst]
  rw [h1, h2]

private theorem csProdFst_eq_prodMap {X Y : «CΣ» sig} (f : X ⟶ Y) (A : «CΣ» sig) :
    csProdFst f A = «CΣ».Hom.prodMap f («CΣ».Hom.id A) := by
  show cpair (cfst X A ≫ f) (csnd X A) = cpair (cfst X A ≫ f) (csnd X A ≫ 𝟙 A)
  rw [Category.comp_id]

/-- Currying is natural in the domain, stated with `≫` and `csProdFst`. -/
private theorem cs_curry_natural {X X' A B : «CΣ» sig}
    (h : X ⟶ X') (f : «CΣ».prodObj X' A ⟶ B) :
    ccurry (csProdFst h A ≫ f) = h ≫ ccurry f := by
  rw [csProdFst_eq_prodMap]
  exact «CΣ».Hom.curry_natural_left h f

private theorem csProdFst_cuncurry {A A' X C : «CΣ» sig}
    (h : A ⟶ A') (K : A' ⟶ «CΣ».expObj X C) :
    csProdFst h X ≫ cuncurry K = cuncurry (h ≫ K) := by
  have hn := cs_curry_natural (A := X) h (cuncurry K)
  rw [ccurry_cuncurry] at hn
  have hu := congrArg cuncurry hn
  rwa [cuncurry_ccurry] at hu

private theorem cs_swap_cuncurry {X S C : «CΣ» sig} (K : S ⟶ «CΣ».expObj X C) :
    csSwap X S ≫ cuncurry K =
      cpair (csnd X S ≫ K) (cfst X S) ≫ cev X C := by
  have h1 : csSwap X S ≫ (cfst S X ≫ K) = csnd X S ≫ K := by simp
  have h2 : csSwap X S ≫ csnd S X = cfst X S := by simp
  rw [cuncurry_def, ← Category.assoc, cs_comp_pair, h1, h2]

/-! ### Distributivity: `X × (A + B) ⟶ (X × A) + (X × B)` -/

private def csDistribLeft (X A B : «CΣ» sig) :
    A ⟶ «CΣ».expObj X («CΣ».coprodObj («CΣ».prodObj X A) («CΣ».prodObj X B)) :=
  ccurry (csSwap A X ≫ cinl («CΣ».prodObj X A) («CΣ».prodObj X B))

private def csDistribRight (X A B : «CΣ» sig) :
    B ⟶ «CΣ».expObj X («CΣ».coprodObj («CΣ».prodObj X A) («CΣ».prodObj X B)) :=
  ccurry (csSwap B X ≫ cinr («CΣ».prodObj X A) («CΣ».prodObj X B))

private def csDistrib (X A B : «CΣ» sig) :
    «CΣ».prodObj X («CΣ».coprodObj A B) ⟶
      «CΣ».coprodObj («CΣ».prodObj X A) («CΣ».prodObj X B) :=
  cpair
      (csnd X («CΣ».coprodObj A B) ≫
        ccase (csDistribLeft X A B) (csDistribRight X A B))
      (cfst X («CΣ».coprodObj A B)) ≫
    cev X («CΣ».coprodObj («CΣ».prodObj X A) («CΣ».prodObj X B))

@[simp] private theorem qm_distrib (X A B : Object sig.nBases) :
    qm (IntrinsicMorphism.distrib X A B) =
      csDistrib (quotientObject X) (quotientObject A) (quotientObject B) :=
  rfl

private theorem csDistrib_eq_swap_cuncurry (X A B : «CΣ» sig) :
    csDistrib X A B =
      csSwap X («CΣ».coprodObj A B) ≫
        cuncurry (ccase (csDistribLeft X A B) (csDistribRight X A B)) :=
  (cs_swap_cuncurry _).symm

/-- Step A: `(x, inl a) ↦ inl (x, a)`. -/
private theorem csProdSnd_left_csDistrib (X A B : «CΣ» sig) :
    csProdSnd X (cinl A B) ≫ csDistrib X A B =
      cinl («CΣ».prodObj X A) («CΣ».prodObj X B) := by
  rw [csDistrib_eq_swap_cuncurry, ← Category.assoc, csProdSnd_csSwap,
    Category.assoc, csProdFst_cuncurry, cinl_ccase]
  unfold csDistribLeft
  rw [cuncurry_ccurry, ← Category.assoc, csSwap_csSwap, Category.id_comp]

/-- Step B: `(x, inr b) ↦ inr (x, b)`. -/
private theorem csProdSnd_right_csDistrib (X A B : «CΣ» sig) :
    csProdSnd X (cinr A B) ≫ csDistrib X A B =
      cinr («CΣ».prodObj X A) («CΣ».prodObj X B) := by
  rw [csDistrib_eq_swap_cuncurry, ← Category.assoc, csProdSnd_csSwap,
    Category.assoc, csProdFst_cuncurry, cinr_ccase]
  unfold csDistribRight
  rw [cuncurry_ccurry, ← Category.assoc, csSwap_csSwap, Category.id_comp]

/--
Maps out of `X × (A + B)` are determined by their restrictions along the two
injections: transpose to `(A + B) ⟶ (X ⇒ Z)` and use the coproduct universal
property there.
-/
private theorem cs_hom_ext_prod_coprod {X A B Z : «CΣ» sig}
    {g h : «CΣ».prodObj X («CΣ».coprodObj A B) ⟶ Z}
    (hl : csProdSnd X (cinl A B) ≫ g = csProdSnd X (cinl A B) ≫ h)
    (hr : csProdSnd X (cinr A B) ≫ g = csProdSnd X (cinr A B) ≫ h) :
    g = h := by
  have hL : ∀ k : «CΣ».prodObj X («CΣ».coprodObj A B) ⟶ Z,
      cinl A B ≫ ccurry (csSwap («CΣ».coprodObj A B) X ≫ k) =
        ccurry (csSwap A X ≫ csProdSnd X (cinl A B) ≫ k) := by
    intro k
    rw [← cs_curry_natural, ← Category.assoc, csProdFst_csSwap, Category.assoc]
  have hR : ∀ k : «CΣ».prodObj X («CΣ».coprodObj A B) ⟶ Z,
      cinr A B ≫ ccurry (csSwap («CΣ».coprodObj A B) X ≫ k) =
        ccurry (csSwap B X ≫ csProdSnd X (cinr A B) ≫ k) := by
    intro k
    rw [← cs_curry_natural, ← Category.assoc, csProdFst_csSwap, Category.assoc]
  have hcurry :
      ccurry (csSwap («CΣ».coprodObj A B) X ≫ g) =
        ccurry (csSwap («CΣ».coprodObj A B) X ≫ h) := by
    refine ((ccase_eta (ccurry (csSwap («CΣ».coprodObj A B) X ≫ g))).symm.trans
      ?_).trans (ccase_eta (ccurry (csSwap («CΣ».coprodObj A B) X ≫ h)))
    rw [hL g, hL h, hR g, hR h, hl, hr]
  have hswap := congrArg cuncurry hcurry
  rw [cuncurry_ccurry, cuncurry_ccurry] at hswap
  calc g = 𝟙 («CΣ».prodObj X («CΣ».coprodObj A B)) ≫ g := (Category.id_comp g).symm
    _ = (csSwap X («CΣ».coprodObj A B) ≫ csSwap («CΣ».coprodObj A B) X) ≫ g := by
        rw [csSwap_csSwap]
    _ = csSwap X («CΣ».coprodObj A B) ≫ csSwap («CΣ».coprodObj A B) X ≫ g :=
        Category.assoc _ _ _
    _ = csSwap X («CΣ».coprodObj A B) ≫ csSwap («CΣ».coprodObj A B) X ≫ h := by
        rw [hswap]
    _ = (csSwap X («CΣ».coprodObj A B) ≫ csSwap («CΣ».coprodObj A B) X) ≫ h :=
        (Category.assoc _ _ _).symm
    _ = 𝟙 («CΣ».prodObj X («CΣ».coprodObj A B)) ≫ h := by rw [csSwap_csSwap]
    _ = h := Category.id_comp h

/-- Step C: distributivity is natural in the product factor. -/
private theorem csDistrib_natural {X Y A B : «CΣ» sig} (f : X ⟶ Y) :
    csProdFst f («CΣ».coprodObj A B) ≫ csDistrib Y A B =
      csDistrib X A B ≫
        ccase
          (csProdFst f A ≫ cinl («CΣ».prodObj Y A) («CΣ».prodObj Y B))
          (csProdFst f B ≫ cinr («CΣ».prodObj Y A) («CΣ».prodObj Y B)) := by
  refine cs_hom_ext_prod_coprod ?_ ?_
  · rw [← Category.assoc, csProdSnd_csProdFst, Category.assoc,
      csProdSnd_left_csDistrib, ← Category.assoc, csProdSnd_left_csDistrib,
      cinl_ccase]
  · rw [← Category.assoc, csProdSnd_csProdFst, Category.assoc,
      csProdSnd_right_csDistrib, ← Category.assoc, csProdSnd_right_csDistrib,
      cinr_ccase]

/-! ### Naturality of interpretation -/

/-- Precompose every entry of an environment with `f : X ⟶ Y`. -/
def Env.precomp {X Y : Object sig.nBases} {Γ : Ctx sig}
    (f : IntrinsicMorphism sig X Y) (ρ : Env Y Γ) : Env X Γ :=
  fun {_} x => .compose f (ρ x)

/-- `f × id_A : X × A ⟶ Y × A`. -/
def IntrinsicMorphism.prodFirst {X Y : Object sig.nBases}
    (f : IntrinsicMorphism sig X Y) (A : Object sig.nBases) :
    IntrinsicMorphism sig (.prod X A) (.prod Y A) :=
  .pair (.compose (.first X A) f) (.second X A)

@[simp] private theorem qm_prodFirst {X Y : Object sig.nBases}
    (f : IntrinsicMorphism sig X Y) (A : Object sig.nBases) :
    qm (f.prodFirst A) = csProdFst (qm f) (quotientObject A) :=
  rfl

private theorem interpret_qm_eq_of_pointwise
    {X : Object sig.nBases} {Γ : Ctx sig} {A : Object sig.nBases} {ρ τ : Env X Γ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B), qm (ρ x) = qm (τ x))
    (t : Tm Γ A) :
    qm (interpret ρ t) = qm (interpret τ t) :=
  interpret_quotient_eq_of_pointwise (fun x => h x) t

private theorem qm_extend_precomp {X Y : Object sig.nBases} {Γ : Ctx sig}
    {A₀ : Object sig.nBases} (f : IntrinsicMorphism sig X Y) (ρ : Env Y Γ)
    {B : Object sig.nBases} (x : Var (Γ ▻ A₀) B) :
    qm (Env.precomp (f.prodFirst A₀) (Env.extend ρ) x) =
      qm (Env.extend (Env.precomp f ρ) x) := by
  cases x <;>
    simp [Env.precomp, Env.extend, IntrinsicMorphism.prodFirst]

/-- Rewriting a `case` interpretation along naturality of distributivity. -/
private theorem cs_case_natural {X Y A B Z : «CΣ» sig}
    (F : X ⟶ Y) (s : X ⟶ «CΣ».coprodObj A B)
    (a : «CΣ».prodObj Y A ⟶ Z) (b : «CΣ».prodObj Y B ⟶ Z) :
    cpair F s ≫ csDistrib Y A B ≫ ccase a b =
      cpair (𝟙 X) s ≫ csDistrib X A B ≫
        ccase (csProdFst F A ≫ a) (csProdFst F B ≫ b) := by
  have hp : cpair (𝟙 X) s ≫ csProdFst F («CΣ».coprodObj A B) = cpair F s := by
    simp [csProdFst, cs_comp_pair]
  calc cpair F s ≫ csDistrib Y A B ≫ ccase a b
      = (cpair (𝟙 X) s ≫ csProdFst F («CΣ».coprodObj A B)) ≫
          csDistrib Y A B ≫ ccase a b := by rw [hp]
    _ = cpair (𝟙 X) s ≫
          (csProdFst F («CΣ».coprodObj A B) ≫ csDistrib Y A B) ≫ ccase a b := by
        simp only [Category.assoc]
    _ = cpair (𝟙 X) s ≫
          (csDistrib X A B ≫
            ccase (csProdFst F A ≫ cinl («CΣ».prodObj Y A) («CΣ».prodObj Y B))
              (csProdFst F B ≫ cinr («CΣ».prodObj Y A) («CΣ».prodObj Y B))) ≫
          ccase a b := by rw [csDistrib_natural]
    _ = cpair (𝟙 X) s ≫ csDistrib X A B ≫
          ccase (csProdFst F A ≫ a) (csProdFst F B ≫ b) := by
        rw [Category.assoc, cs_case_comp]
        simp only [Category.assoc, cinl_ccase, cinr_ccase]

private theorem interpret_qm_natural {X Y : Object sig.nBases} {Γ : Ctx sig}
    {A : Object sig.nBases} (f : IntrinsicMorphism sig X Y) (ρ : Env Y Γ)
    (t : Tm Γ A) :
    qm f ≫ qm (interpret ρ t) = qm (interpret (Env.precomp f ρ) t) := by
  revert X Y f ρ
  induction t with
  | var x => intro X Y f ρ; rfl
  | unit =>
      intro X Y f ρ
      simp only [interpret, qm_discard]
      exact cterminal_uniq _
  | abort t ih =>
      intro X Y f ρ
      simp only [interpret, qm_compose, ← Category.assoc, ih f ρ]
  | pair t u iht ihu =>
      intro X Y f ρ
      simp only [interpret, qm_pair, cs_comp_pair, iht f ρ, ihu f ρ]
  | fst t ih =>
      intro X Y f ρ
      simp only [interpret, qm_compose, ← Category.assoc, ih f ρ]
  | snd t ih =>
      intro X Y f ρ
      simp only [interpret, qm_compose, ← Category.assoc, ih f ρ]
  | inl t ih =>
      intro X Y f ρ
      simp only [interpret, qm_compose, ← Category.assoc, ih f ρ]
  | inr t ih =>
      intro X Y f ρ
      simp only [interpret, qm_compose, ← Category.assoc, ih f ρ]
  | case s t u ihs iht ihu =>
      intro X Y f ρ
      have ha : csProdFst (qm f) (quotientObject _) ≫
          qm (interpret (Env.extend ρ) t) =
            qm (interpret (Env.extend (Env.precomp f ρ)) t) := by
        rw [← qm_prodFirst, iht (f.prodFirst _) (Env.extend ρ)]
        exact interpret_qm_eq_of_pointwise (qm_extend_precomp f ρ) t
      have hb : csProdFst (qm f) (quotientObject _) ≫
          qm (interpret (Env.extend ρ) u) =
            qm (interpret (Env.extend (Env.precomp f ρ)) u) := by
        rw [← qm_prodFirst, ihu (f.prodFirst _) (Env.extend ρ)]
        exact interpret_qm_eq_of_pointwise (qm_extend_precomp f ρ) u
      simp only [interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib]
      rw [← ha, ← hb, ← ihs f ρ, ← Category.assoc, cs_comp_pair, Category.comp_id]
      exact cs_case_natural _ _ _ _
  | lam t ih =>
      intro X Y f ρ
      simp only [interpret, qm_curry]
      rw [← cs_curry_natural]
      congr 1
      rw [← qm_prodFirst, ih (f.prodFirst _) (Env.extend ρ)]
      exact interpret_qm_eq_of_pointwise (qm_extend_precomp f ρ) t
  | app t u iht ihu =>
      intro X Y f ρ
      simp only [interpret, qm_compose, qm_pair, qm_eval, ← Category.assoc,
        cs_comp_pair, iht f ρ, ihu f ρ]

/-- Interpretation is natural in the domain of the environment. -/
theorem interpret_natural {X Y : Object sig.nBases} {Γ : Ctx sig}
    {A : Object sig.nBases} (f : IntrinsicMorphism sig X Y) (ρ : Env Y Γ)
    (t : Tm Γ A) :
    IntrinsicDefEq (.compose f (interpret ρ t)) (interpret (Env.precomp f ρ) t) :=
  intrinsicDefEq_of_qm_eq (interpret_qm_natural f ρ t)

/-! ### Naturality of the generator environment -/

/-- Every generator constant is natural in the domain. -/
theorem genEnv_natural {X Y : Object sig.nBases} (f : IntrinsicMorphism sig X Y)
    {C : Object sig.nBases} (x : Var (genCtx sig) C) :
    IntrinsicDefEq (.compose f (genEnv Y x)) (genEnv X x) := by
  apply intrinsicDefEq_of_qm_eq
  have go : ∀ (i : Nat) (hi : i ≤ sig.nGens) {D : Object sig.nBases}
      (y : Var (genCtxPrefix sig i hi) D),
      qm (.compose f (genEnvPrefix Y i hi y)) = qm (genEnvPrefix X i hi y) := by
    intro i
    induction i with
    | zero => intro hi D y; exact nomatch y
    | succ i ih =>
        intro hi D y
        cases y with
        | here =>
            simp only [genEnvPrefix, Env.snocConst, generatorValue, qm_compose,
              qm_discard]
            rw [← Category.assoc,
              cterminal_uniq (qm f ≫ cdrop (quotientObject Y))]
        | there z => exact ih (Nat.le_of_succ_le hi) z
  exact go sig.nGens (Nat.le_refl _) x

/-! ### Interpretation under substitution -/

private theorem qm_exts_ofSubst {X : Object sig.nBases} {Γ Δ : Ctx sig}
    {A₀ : Object sig.nBases} (ρ : Env X Δ) (σ : Subst sig Γ Δ)
    {B : Object sig.nBases} (x : Var (Γ ▻ A₀) B) :
    qm (Env.ofSubst (Env.extend ρ) (Subst.exts σ) x) =
      qm (Env.extend (Env.ofSubst ρ σ) x) := by
  cases x with
  | here => rfl
  | there y =>
      have henv :
          interpret (Env.rename (Env.extend (A := A₀) ρ) Rename.weaken) (σ y) =
            interpret (Env.precomp (IntrinsicMorphism.first X A₀) ρ) (σ y) :=
        interpret_eq_of_pointwise (fun _ => rfl) (σ y)
      show qm (interpret (Env.extend ρ) (weakenTerm (σ y))) =
        qm (.compose (IntrinsicMorphism.first X A₀) (interpret ρ (σ y)))
      rw [weakenTerm_eq_rename, interpret_rename, henv, qm_compose]
      exact (interpret_qm_natural (IntrinsicMorphism.first X A₀) ρ (σ y)).symm

private theorem interpret_qm_subst {X : Object sig.nBases} {Γ Δ : Ctx sig}
    {A : Object sig.nBases} (ρ : Env X Δ) (σ : Subst sig Γ Δ) (t : Tm Γ A) :
    qm (interpret ρ (subst σ t)) = qm (interpret (Env.ofSubst ρ σ) t) := by
  revert X Δ ρ σ
  induction t with
  | var x => intro X Δ ρ σ; rfl
  | unit => intro X Δ ρ σ; rfl
  | abort t ih =>
      intro X Δ ρ σ
      simp only [subst, interpret, qm_compose, ih ρ σ]
  | pair t u iht ihu =>
      intro X Δ ρ σ
      simp only [subst, interpret, qm_pair, iht ρ σ, ihu ρ σ]
  | fst t ih =>
      intro X Δ ρ σ
      simp only [subst, interpret, qm_compose, ih ρ σ]
  | snd t ih =>
      intro X Δ ρ σ
      simp only [subst, interpret, qm_compose, ih ρ σ]
  | inl t ih =>
      intro X Δ ρ σ
      simp only [subst, interpret, qm_compose, ih ρ σ]
  | inr t ih =>
      intro X Δ ρ σ
      simp only [subst, interpret, qm_compose, ih ρ σ]
  | case s t u ihs iht ihu =>
      intro X Δ ρ σ
      simp only [subst, interpret, qm_compose, qm_pair, qm_case, qm_id, qm_distrib,
        ihs ρ σ, iht (Env.extend ρ) (Subst.exts σ), ihu (Env.extend ρ) (Subst.exts σ),
        interpret_qm_eq_of_pointwise (qm_exts_ofSubst ρ σ) t,
        interpret_qm_eq_of_pointwise (qm_exts_ofSubst ρ σ) u]
  | lam t ih =>
      intro X Δ ρ σ
      simp only [subst, interpret, qm_curry, ih (Env.extend ρ) (Subst.exts σ),
        interpret_qm_eq_of_pointwise (qm_exts_ofSubst ρ σ) t]
  | app t u iht ihu =>
      intro X Δ ρ σ
      simp only [subst, interpret, qm_compose, qm_pair, iht ρ σ, ihu ρ σ]

/-- Interpretation commutes with substitution, up to definitional equality. -/
theorem interpret_subst {X : Object sig.nBases} {Γ Δ : Ctx sig}
    {A : Object sig.nBases} (ρ : Env X Δ) (σ : Subst sig Γ Δ) (t : Tm Γ A) :
    IntrinsicDefEq (interpret ρ (subst σ t)) (interpret (Env.ofSubst ρ σ) t) :=
  intrinsicDefEq_of_qm_eq (interpret_qm_subst ρ σ t)

/-- Weakening a term is precomposition with the first projection. -/
theorem interpret_weakenTerm {X A₀ : Object sig.nBases} {Γ : Ctx sig}
    {B : Object sig.nBases} (ρ : Env X Γ) (t : Tm Γ B) :
    IntrinsicDefEq
      (interpret (Env.extend (A := A₀) ρ) (weakenTerm t))
      (.compose (IntrinsicMorphism.first X A₀) (interpret ρ t)) := by
  apply intrinsicDefEq_of_qm_eq
  have henv :
      interpret (Env.rename (Env.extend (A := A₀) ρ) Rename.weaken) t =
        interpret (Env.precomp (IntrinsicMorphism.first X A₀) ρ) t :=
    interpret_eq_of_pointwise (fun _ => rfl) t
  rw [weakenTerm_eq_rename, interpret_rename, henv, qm_compose]
  exact (interpret_qm_natural (IntrinsicMorphism.first X A₀) ρ t).symm

/-- Substituting for the newest binder is pairing with the substituted element. -/
theorem interpret_subst0 {X A₀ : Object sig.nBases} {Γ : Ctx sig}
    {B : Object sig.nBases} (ρ : Env X Γ) (t : Tm (Γ ▻ A₀) B) (n : Tm Γ A₀) :
    IntrinsicDefEq (interpret ρ (subst0 t n))
      (interpret (Env.snocConst ρ (interpret ρ n)) t) := by
  apply intrinsicDefEq_of_qm_eq
  refine (interpret_qm_subst ρ (Subst.single n) t).trans ?_
  refine interpret_qm_eq_of_pointwise ?_ t
  intro C x
  cases x <;> rfl

@[simp] private theorem csProdSnd_left_csDistrib_assoc {X A B Z : «CΣ» sig}
    (k : «CΣ».coprodObj («CΣ».prodObj X A) («CΣ».prodObj X B) ⟶ Z) :
    csProdSnd X (cinl A B) ≫ csDistrib X A B ≫ k =
      cinl («CΣ».prodObj X A) («CΣ».prodObj X B) ≫ k := by
  rw [← Category.assoc, csProdSnd_left_csDistrib]

@[simp] private theorem csProdSnd_right_csDistrib_assoc {X A B Z : «CΣ» sig}
    (k : «CΣ».coprodObj («CΣ».prodObj X A) («CΣ».prodObj X B) ⟶ Z) :
    csProdSnd X (cinr A B) ≫ csDistrib X A B ≫ k =
      cinr («CΣ».prodObj X A) («CΣ».prodObj X B) ≫ k := by
  rw [← Category.assoc, csProdSnd_right_csDistrib]

/--
Distributing the diagonal on a coproduct and casing on the two second
projections recovers the original case split.
-/
private theorem cs_case_diag {A B Z : «CΣ» sig} (a : A ⟶ Z) (b : B ⟶ Z) :
    cpair (𝟙 («CΣ».coprodObj A B)) (𝟙 («CΣ».coprodObj A B)) ≫
        csDistrib («CΣ».coprodObj A B) A B ≫
        ccase (csnd («CΣ».coprodObj A B) A ≫ a)
          (csnd («CΣ».coprodObj A B) B ≫ b) =
      ccase a b := by
  have hl : cinl A B ≫ cpair (𝟙 («CΣ».coprodObj A B)) (𝟙 («CΣ».coprodObj A B)) =
      cpair (cinl A B) (𝟙 A) ≫ csProdSnd («CΣ».coprodObj A B) (cinl A B) := by
    simp [csProdSnd, cs_comp_pair]
  have hr : cinr A B ≫ cpair (𝟙 («CΣ».coprodObj A B)) (𝟙 («CΣ».coprodObj A B)) =
      cpair (cinr A B) (𝟙 B) ≫ csProdSnd («CΣ».coprodObj A B) (cinr A B) := by
    simp [csProdSnd, cs_comp_pair]
  refine ccase_unique _ ?_ ?_
  · rw [← Category.assoc, hl, Category.assoc]
    simp
  · rw [← Category.assoc, hr, Category.assoc]
    simp

/-! ### Translation retraction -/

/-- The substitution `translate` uses for composition. -/
private def composeSubst {A B₀ : Object sig.nBases} (f : IntrinsicMorphism sig A B₀) :
    Subst sig (translateCtx B₀) (translateCtx A)
  | _, .here => translate f
  | _, .there x => .var (.there x)

private theorem translate_compose_eq {A B₀ C : Object sig.nBases}
    (f : IntrinsicMorphism sig A B₀) (g : IntrinsicMorphism sig B₀ C) :
    translate (.compose f g) = subst (composeSubst f) (translate g) :=
  rfl

/-- The substitution `translate` uses under a `curry` binder. -/
private def currySubst (X A₀ : Object sig.nBases) :
    Subst sig (translateCtx (.prod X A₀)) (translateCtx X ▻ A₀)
  | _, .here => .pair (.var (.there .here)) (.var .here)
  | _, .there v => .var (.there (.there v))

private theorem translate_curry_eq {X A₀ B₀ : Object sig.nBases}
    (f : IntrinsicMorphism sig (.prod X A₀) B₀) :
    translate (.curry f) = .lam (subst (currySubst X A₀) (translate f)) :=
  rfl

/-- The translation retraction is closed under composition. -/
theorem interpret_translate_compose {A B₀ C : Object sig.nBases}
    (f : IntrinsicMorphism sig A B₀) (g : IntrinsicMorphism sig B₀ C)
    (hf : IntrinsicDefEq (interpret (rootEnv A) (translate f)) f)
    (hg : IntrinsicDefEq (interpret (rootEnv B₀) (translate g)) g) :
    IntrinsicDefEq
      (interpret (rootEnv A) (translate (IntrinsicMorphism.compose f g)))
      (.compose f g) := by
  apply intrinsicDefEq_of_qm_eq
  have hpw : ∀ {D : Object sig.nBases} (x : Var (translateCtx B₀) D),
      qm (Env.ofSubst (rootEnv A) (composeSubst f) x) =
        qm (Env.precomp f (rootEnv B₀) x) := by
    intro D x
    cases x with
    | here =>
        show qm (interpret (rootEnv A) (translate f)) =
          qm (IntrinsicMorphism.compose f (IntrinsicMorphism.id B₀))
        rw [qm_compose, qm_id, Category.comp_id]
        exact qm_eq_of_intrinsicDefEq hf
    | there y =>
        show qm (genEnv A y) = qm (IntrinsicMorphism.compose f (genEnv B₀ y))
        exact (qm_eq_of_intrinsicDefEq (genEnv_natural f y)).symm
  rw [translate_compose_eq, interpret_qm_subst,
    interpret_qm_eq_of_pointwise hpw (translate g),
    ← interpret_qm_natural f (rootEnv B₀) (translate g),
    qm_eq_of_intrinsicDefEq hg, qm_compose]

/-- Interpretation of a translated `case` branch, under the shifted environment. -/
private theorem interpret_qm_translate_branch {S C₀ Z : Object sig.nBases}
    (h : IntrinsicMorphism sig C₀ Z)
    (ih : IntrinsicDefEq (interpret (rootEnv C₀) (translate h)) h) :
    qm (interpret (Env.extend (A := C₀) (rootEnv S))
        (rename (renameSkipMiddle (Γ := genCtx sig) (A := C₀) (B := S))
          (translate h))) =
      csnd (quotientObject S) (quotientObject C₀) ≫ qm h := by
  have hpw : ∀ {D : Object sig.nBases} (x : Var (translateCtx C₀) D),
      qm (Env.rename (Env.extend (A := C₀) (rootEnv S))
          (renameSkipMiddle (Γ := genCtx sig) (A := C₀) (B := S)) x) =
        qm (Env.precomp (IntrinsicMorphism.second S C₀) (rootEnv C₀) x) := by
    intro D x
    cases x with
    | here =>
        show qm (IntrinsicMorphism.second S C₀) =
          qm (IntrinsicMorphism.compose (IntrinsicMorphism.second S C₀)
            (IntrinsicMorphism.id C₀))
        simp
    | there y =>
        show qm (IntrinsicMorphism.compose (IntrinsicMorphism.first S C₀)
            (genEnv S y)) =
          qm (IntrinsicMorphism.compose (IntrinsicMorphism.second S C₀)
            (genEnv C₀ y))
        rw [qm_eq_of_intrinsicDefEq (genEnv_natural (IntrinsicMorphism.first S C₀) y),
          qm_eq_of_intrinsicDefEq (genEnv_natural (IntrinsicMorphism.second S C₀) y)]
  rw [interpret_rename]
  refine (interpret_qm_eq_of_pointwise hpw (translate h)).trans ?_
  refine (interpret_qm_natural (IntrinsicMorphism.second S C₀) (rootEnv C₀)
    (translate h)).symm.trans ?_
  rw [qm_eq_of_intrinsicDefEq ih, qm_second]

/-- The translation retraction is closed under case analysis. -/
theorem interpret_translate_case {A₀ B₀ Z : Object sig.nBases}
    (f : IntrinsicMorphism sig A₀ Z) (g : IntrinsicMorphism sig B₀ Z)
    (hf : IntrinsicDefEq (interpret (rootEnv A₀) (translate f)) f)
    (hg : IntrinsicDefEq (interpret (rootEnv B₀) (translate g)) g) :
    IntrinsicDefEq
      (interpret (rootEnv (Object.coprod A₀ B₀))
        (translate (IntrinsicMorphism.case f g)))
      (.case f g) := by
  apply intrinsicDefEq_of_qm_eq
  simp only [translate, interpret, rootEnv, qm_compose, qm_pair, qm_case, qm_id,
    qm_distrib, interpret_qm_translate_branch f hf,
    interpret_qm_translate_branch g hg]
  exact cs_case_diag (qm f) (qm g)

/-- The translation retraction is closed under currying. -/
theorem interpret_translate_curry {X A₀ B₀ : Object sig.nBases}
    (f : IntrinsicMorphism sig (.prod X A₀) B₀)
    (hf : IntrinsicDefEq (interpret (rootEnv (Object.prod X A₀)) (translate f)) f) :
    IntrinsicDefEq
      (interpret (rootEnv X) (translate (IntrinsicMorphism.curry f)))
      (.curry f) := by
  apply intrinsicDefEq_of_qm_eq
  have hpw : ∀ {D : Object sig.nBases} (x : Var (translateCtx (Object.prod X A₀)) D),
      qm (Env.ofSubst (Env.extend (A := A₀) (rootEnv X)) (currySubst X A₀) x) =
        qm (rootEnv (Object.prod X A₀) x) := by
    intro D x
    cases x with
    | here =>
        show qm (IntrinsicMorphism.pair
            (IntrinsicMorphism.compose (IntrinsicMorphism.first X A₀)
              (IntrinsicMorphism.id X))
            (IntrinsicMorphism.second X A₀)) =
          qm (IntrinsicMorphism.id (Object.prod X A₀))
        simp [cs_pair_fst_snd]
    | there v =>
        show qm (IntrinsicMorphism.compose (IntrinsicMorphism.first X A₀)
            (genEnv X v)) = qm (genEnv (Object.prod X A₀) v)
        exact qm_eq_of_intrinsicDefEq
          (genEnv_natural (IntrinsicMorphism.first X A₀) v)
  rw [translate_curry_eq]
  simp only [interpret, qm_curry]
  congr 1
  rw [interpret_qm_subst, interpret_qm_eq_of_pointwise hpw (translate f)]
  exact qm_eq_of_intrinsicDefEq hf

/-- Interpreting a translated morphism in the root environment recovers it. -/
theorem interpret_translate {A B : Object sig.nBases}
    (f : IntrinsicMorphism sig A B) :
    IntrinsicDefEq (interpret (rootEnv A) (translate f)) f := by
  induction f with
  | generator q => exact interpret_translate_generator q
  | id A => exact interpret_translate_id A
  | compose f g ihf ihg => exact interpret_translate_compose f g ihf ihg
  | discard A => exact interpret_translate_discard A
  | absurd A => exact interpret_translate_absurd A
  | first A B => exact interpret_translate_first A B
  | second A B => exact interpret_translate_second A B
  | pair f g ihf ihg => exact interpret_translate_pair f g ihf ihg
  | left A B => exact interpret_translate_left A B
  | right A B => exact interpret_translate_right A B
  | case f g ihf ihg => exact interpret_translate_case f g ihf ihg
  | curry f ih => exact interpret_translate_curry f ih
  | eval A B => exact interpret_translate_eval A B

/-- Interpreting the translation of a public checked morphism recovers it. -/
theorem interpret_translateMorphism {A B : Object sig.nBases}
    (f : Morphism sig A B) :
    DefEq (interpret (rootEnv A) (translateMorphism f)).toMorphism f := by
  have h : DefEq (interpret (rootEnv A) (translate (ofMorphism f))).toMorphism
      (ofMorphism f).toMorphism := interpret_translate (ofMorphism f)
  rwa [ofMorphism_toMorphism] at h

end Equality
end Gimbal
