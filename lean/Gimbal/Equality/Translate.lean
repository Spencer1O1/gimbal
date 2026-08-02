/-
  Structural translation from intrinsic morphisms into equality-calculus terms
  under the rigid generator context `Γgen`.
-/

import Gimbal.Equality.Elaborate
import Gimbal.Equality.LambdaSyntax

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- Context `Γgen , x : A`. -/
def translateCtx (A : Object sig.nBases) : Ctx sig :=
  genCtx sig ▻ A

/--
Rename that skips one middle binder: `(Γ ▻ A) → (Γ ▻ B ▻ A)`.
Used for case branches.
-/
def renameSkipMiddle {Γ : Ctx sig} {A B : Object sig.nBases} :
    Rename sig (Γ ▻ A) (Γ ▻ B ▻ A)
  | _, .here => .here
  | _, .there y => .there (.there y)

/--
Translate an intrinsic morphism `f : A ⟶ B` to a term

```text
Γgen , x : A ⊢ translate(f, x) : B
```
-/
def translate {A B : Object sig.nBases}
    (f : IntrinsicMorphism sig A B) : Tm (translateCtx A) B :=
  match f with
  | .generator q =>
      .app (.var (.there (genVar sig q))) (.var .here)
  | .id _ =>
      .var .here
  | .compose (B := B₀) f g =>
      -- `Γgen , x : A ⊢ translate f : B₀` and `Γgen , y : B₀ ⊢ translate g : C`.
      -- Substitute `y ↦ translate f`, keeping the shared `Γgen` prefix.
      let σ : Subst sig (translateCtx B₀) (translateCtx A)
        | _, .here => translate f
        | _, .there x => .var (.there x)
      subst σ (translate g)
  | .discard _ =>
      .unit
  | .absurd _ =>
      .abort (.var .here)
  | .first _ _ =>
      .fst (.var .here)
  | .second _ _ =>
      .snd (.var .here)
  | .pair f g =>
      .pair (translate f) (translate g)
  | .left _ _ =>
      .inl (.var .here)
  | .right _ _ =>
      .inr (.var .here)
  | .case (A := A₀) (B := B₀) (X := C) f g =>
      let leftBranch : Tm (translateCtx (.coprod A₀ B₀) ▻ A₀) C :=
        rename renameSkipMiddle (translate f)
      let rightBranch : Tm (translateCtx (.coprod A₀ B₀) ▻ B₀) C :=
        rename renameSkipMiddle (translate g)
      .case (.var .here) leftBranch rightBranch
  | .curry (X := X) (A := A₀) (B := B₀) f =>
      -- `λ a. translate f[(x,a)/p]` under `Γgen , x : X , a : A₀`.
      let σ : Subst sig (translateCtx (.prod X A₀)) (translateCtx X ▻ A₀)
        | _, .here => .pair (.var (.there .here)) (.var .here)
        | _, .there v => .var (.there (.there v))
      .lam (subst σ (translate f))
  | .eval _ _ =>
      .app (.fst (.var .here)) (.snd (.var .here))

/-- Translate a public checked morphism via the intrinsic mirror. -/
def translateMorphism {A B : Object sig.nBases}
    (f : Morphism sig A B) : Tm (translateCtx A) B :=
  translate (ofMorphism f)

end Equality
end Gimbal
