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

end Equality
end Gimbal
