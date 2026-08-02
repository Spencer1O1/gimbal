/-
  Categorical interpretation of equality-calculus terms (Milestone 8B).
-/

import Gimbal.Equality.Algebra
import Gimbal.Equality.Translate
import Gimbal.DefinitionalEquality

namespace Gimbal
namespace Equality

variable {sig : Signature}

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

end Equality
end Gimbal
