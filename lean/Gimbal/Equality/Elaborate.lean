/-
  Executable elaboration from extrinsic `Term` into intrinsic morphisms.
  Conversion from public `Morphism` uses elaboration on the term plus uniqueness;
  it does not eliminate `HasType` into `Type`.
-/

import Gimbal.Equality.IntrinsicMorphism

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- Typing derivations determine unique source and target. -/
theorem hasType_unique {t : Term sig} {A B A' B' : Object sig.nBases}
    (h : HasType sig t A B) (h' : HasType sig t A' B') : A = A' ∧ B = B' := by
  induction t generalizing A B A' B' with
  | generator q =>
    cases h; cases h'; exact ⟨rfl, rfl⟩
  | id A₀ =>
    cases h; cases h'; exact ⟨rfl, rfl⟩
  | compose t u ih_t ih_u =>
    match h, h' with
    | .compose ht hu, .compose ht' hu' =>
      obtain ⟨rfl, hB⟩ := ih_t ht ht'
      obtain ⟨_, hC⟩ := ih_u hu hu'
      cases hB; cases hC
      exact ⟨rfl, rfl⟩
  | discard A₀ =>
    cases h; cases h'; exact ⟨rfl, rfl⟩
  | absurd A₀ =>
    cases h; cases h'; exact ⟨rfl, rfl⟩
  | first A₀ B₀ =>
    cases h; cases h'; exact ⟨rfl, rfl⟩
  | second A₀ B₀ =>
    cases h; cases h'; exact ⟨rfl, rfl⟩
  | pair t u ih_t ih_u =>
    match h, h' with
    | .pair ht hu, .pair ht' hu' =>
      obtain ⟨rfl, hA⟩ := ih_t ht ht'
      obtain ⟨_, hB⟩ := ih_u hu hu'
      cases hA; cases hB
      exact ⟨rfl, rfl⟩
  | left A₀ B₀ =>
    cases h; cases h'; exact ⟨rfl, rfl⟩
  | right A₀ B₀ =>
    cases h; cases h'; exact ⟨rfl, rfl⟩
  | case t u ih_t ih_u =>
    match h, h' with
    | .case ht hu, .case ht' hu' =>
      obtain ⟨hA, rfl⟩ := ih_t ht ht'
      obtain ⟨hB, _⟩ := ih_u hu hu'
      cases hA; cases hB
      exact ⟨rfl, rfl⟩
  | curry t ih =>
    match h, h' with
    | .curry ht, .curry ht' =>
      obtain ⟨hprod, rfl⟩ := ih ht ht'
      cases hprod
      exact ⟨rfl, rfl⟩
  | eval A₀ B₀ =>
    cases h; cases h'; exact ⟨rfl, rfl⟩

/--
Elaborate an extrinsic term into an intrinsically typed morphism, synthesizing
source and target. Returns `none` when the term is ill-typed.
-/
def elaborate : Term sig → Option (Σ A : Object sig.nBases,
    Σ B : Object sig.nBases, IntrinsicMorphism sig A B)
  | .generator q =>
    some ⟨(sig.gen q).source, (sig.gen q).target, .generator q⟩
  | .id A =>
    some ⟨A, A, .id A⟩
  | .compose t u =>
    match elaborate t, elaborate u with
    | some ⟨A, B, f⟩, some ⟨B', C, g⟩ =>
      if h : B = B' then
        some ⟨A, C, .compose f (h ▸ g)⟩
      else
        none
    | _, _ => none
  | .discard A =>
    some ⟨A, .unit, .discard A⟩
  | .absurd A =>
    some ⟨.never, A, .absurd A⟩
  | .first A B =>
    some ⟨.prod A B, A, .first A B⟩
  | .second A B =>
    some ⟨.prod A B, B, .second A B⟩
  | .pair t u =>
    match elaborate t, elaborate u with
    | some ⟨X, A, f⟩, some ⟨X', B, g⟩ =>
      if h : X = X' then
        some ⟨X, .prod A B, .pair f (h ▸ g)⟩
      else
        none
    | _, _ => none
  | .left A B =>
    some ⟨A, .coprod A B, .left A B⟩
  | .right A B =>
    some ⟨B, .coprod A B, .right A B⟩
  | .case t u =>
    match elaborate t, elaborate u with
    | some ⟨A, X, f⟩, some ⟨B, X', g⟩ =>
      if h : X = X' then
        some ⟨.coprod A B, X, .case f (h ▸ g)⟩
      else
        none
    | _, _ => none
  | .curry t =>
    match elaborate t with
    | some ⟨.prod X A, B, f⟩ =>
      some ⟨X, .exp A B, .curry f⟩
    | _ => none
  | .eval A B =>
    some ⟨.prod (.exp A B) A, B, .eval A B⟩

private theorem erase_cast_source {A A' B : Object sig.nBases}
    (h : A = A') (f : IntrinsicMorphism sig A' B) :
    (h ▸ f).erase = f.erase := by
  cases h
  rfl

private theorem erase_cast_target {A B B' : Object sig.nBases}
    (h : B = B') (f : IntrinsicMorphism sig A B') :
    (h ▸ f).erase = f.erase := by
  cases h
  rfl

private theorem elaborate_sound_erase {t : Term sig} {A B : Object sig.nBases}
    {f : IntrinsicMorphism sig A B}
    (h : elaborate t = some ⟨A, B, f⟩) : f.erase = t := by
  induction t generalizing A B f with
  | generator q =>
    injection h with h; cases h; rfl
  | id A' =>
    injection h with h; cases h; rfl
  | compose t u ih_t ih_u =>
    simp only [elaborate] at h
    cases ht : elaborate t with
    | none => simp [ht] at h
    | some wt =>
      cases hu : elaborate u with
      | none => simp [ht, hu] at h
      | some wu =>
        simp only [ht, hu] at h
        rcases wt with ⟨A₀, B₀, f₀⟩
        rcases wu with ⟨B₁, C₀, g₀⟩
        dsimp only at h
        split at h
        · next hEq =>
          injection h with h; cases h
          simp [IntrinsicMorphism.erase, ih_t ht, erase_cast_source hEq g₀, ih_u hu]
        · cases h
  | discard A' =>
    injection h with h; cases h; rfl
  | absurd A' =>
    injection h with h; cases h; rfl
  | first A' B' =>
    injection h with h; cases h; rfl
  | second A' B' =>
    injection h with h; cases h; rfl
  | pair t u ih_t ih_u =>
    simp only [elaborate] at h
    cases ht : elaborate t with
    | none => simp [ht] at h
    | some wt =>
      cases hu : elaborate u with
      | none => simp [ht, hu] at h
      | some wu =>
        simp only [ht, hu] at h
        rcases wt with ⟨X₀, A₀, f₀⟩
        rcases wu with ⟨X₁, B₀, g₀⟩
        dsimp only at h
        split at h
        · next hEq =>
          injection h with h; cases h
          simp [IntrinsicMorphism.erase, ih_t ht, erase_cast_source hEq g₀, ih_u hu]
        · cases h
  | left A' B' =>
    injection h with h; cases h; rfl
  | right A' B' =>
    injection h with h; cases h; rfl
  | case t u ih_t ih_u =>
    simp only [elaborate] at h
    cases ht : elaborate t with
    | none => simp [ht] at h
    | some wt =>
      cases hu : elaborate u with
      | none => simp [ht, hu] at h
      | some wu =>
        simp only [ht, hu] at h
        rcases wt with ⟨A₀, X₀, f₀⟩
        rcases wu with ⟨B₀, X₁, g₀⟩
        dsimp only at h
        split at h
        · next hEq =>
          injection h with h; cases h
          simp [IntrinsicMorphism.erase, ih_t ht, erase_cast_target hEq g₀, ih_u hu]
        · cases h
  | curry t ih =>
    simp only [elaborate] at h
    cases ht : elaborate t with
    | none => simp [ht] at h
    | some wt =>
      simp only [ht] at h
      rcases wt with ⟨P, B₀, f₀⟩
      cases P with
      | prod X A₀ =>
        dsimp only at h
        injection h with h; cases h
        simp [IntrinsicMorphism.erase, ih ht]
      | _ =>
        simp at h
  | eval A' B' =>
    injection h with h; cases h; rfl

theorem elaborate_sound {t : Term sig} {A B : Object sig.nBases}
    {f : IntrinsicMorphism sig A B}
    (h : elaborate t = some ⟨A, B, f⟩) :
    f.erase = t ∧ HasType sig t A B := by
  refine ⟨elaborate_sound_erase h, ?_⟩
  exact (elaborate_sound_erase h) ▸ f.hasType

/-- Every well-typed term elaborates to an intrinsic morphism at those endpoints. -/
theorem elaborate_of_hasType {t : Term sig} {A B : Object sig.nBases}
    (ht : HasType sig t A B) :
    ∃ f : IntrinsicMorphism sig A B, elaborate t = some ⟨A, B, f⟩ := by
  induction ht with
  | generator q =>
    exact ⟨.generator q, rfl⟩
  | id A =>
    exact ⟨.id A, rfl⟩
  | compose ht hu ih_t ih_u =>
    obtain ⟨f, hf⟩ := ih_t
    obtain ⟨g, hg⟩ := ih_u
    refine ⟨.compose f g, ?_⟩
    simp [elaborate, hf, hg]
  | discard A =>
    exact ⟨.discard A, rfl⟩
  | absurd A =>
    exact ⟨.absurd A, rfl⟩
  | first A B =>
    exact ⟨.first A B, rfl⟩
  | second A B =>
    exact ⟨.second A B, rfl⟩
  | pair ht hu ih_t ih_u =>
    obtain ⟨f, hf⟩ := ih_t
    obtain ⟨g, hg⟩ := ih_u
    refine ⟨.pair f g, ?_⟩
    simp [elaborate, hf, hg]
  | left A B =>
    exact ⟨.left A B, rfl⟩
  | right A B =>
    exact ⟨.right A B, rfl⟩
  | case ht hu ih_t ih_u =>
    obtain ⟨f, hf⟩ := ih_t
    obtain ⟨g, hg⟩ := ih_u
    refine ⟨.case f g, ?_⟩
    simp [elaborate, hf, hg]
  | curry ht ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨.curry f, ?_⟩
    simp [elaborate, hf]
  | eval A B =>
    exact ⟨.eval A B, rfl⟩

/--
Convert a public checked morphism into the private intrinsic mirror.

Computes by elaborating the underlying term (allowed recursion on `Term`), then
casts using typing uniqueness. Does not eliminate `HasType` into `Type`.
-/
def ofMorphism {A B : Object sig.nBases} (f : Morphism sig A B) :
    IntrinsicMorphism sig A B :=
  match h : elaborate f.term with
  | some ⟨A', B', g⟩ =>
    have sound := elaborate_sound h
    have uniq := hasType_unique sound.2 f.typed
    uniq.1 ▸ uniq.2 ▸ g
  | none =>
    False.elim <| by
      obtain ⟨g, hg⟩ := elaborate_of_hasType f.typed
      simp [h] at hg

theorem ofMorphism_erase {A B : Object sig.nBases} (f : Morphism sig A B) :
    (ofMorphism f).erase = f.term := by
  dsimp [ofMorphism]
  split
  · next A' B' g h =>
    have sound := elaborate_sound h
    have uniq := hasType_unique sound.2 f.typed
    cases uniq.1
    cases uniq.2
    exact sound.1
  · next h =>
    obtain ⟨g, hg⟩ := elaborate_of_hasType f.typed
    simp [h] at hg

private theorem morphism_eq_of_term_eq {A B : Object sig.nBases}
    {f g : Morphism sig A B} (h : f.term = g.term) : f = g := by
  cases f; cases g; cases h; rfl

theorem ofMorphism_toMorphism {A B : Object sig.nBases} (f : Morphism sig A B) :
    (ofMorphism f).toMorphism = f :=
  morphism_eq_of_term_eq (ofMorphism_erase f)

end Equality
end Gimbal
