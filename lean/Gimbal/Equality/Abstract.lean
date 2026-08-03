/-
  Typed neutral abstraction — the computational content of strong positive cut
  (Milestone 8E).

  When saturation observes a neutral `n : NegNeu Γ P` it binds `n` to a fresh
  variable. For that to preserve meaning, every *occurrence* of `n` has to be
  replaced by the new variable, not merely weakened past it. Occurrences are
  recognised by typed structural equality (`NegNeu.beq`); its soundness lemma
  hands back both the type equality and the term equality, so a replacement site
  is by construction a site where the original subterm *is* the observation.

  The correctness statement is stated against an arbitrary substitution that
  already identifies the abstraction variable with the observation
  (`abstractAtom_subst`); the `letPos` cut is the instance where that
  substitution is `subst0 · n.erase`.
-/

import Gimbal.Equality.Hereditary

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Variables are determined by their de Bruijn index -/

theorem Var.eq_of_toRawIdx {Γ : Ctx sig} :
    ∀ {A B : Object sig.nBases} (x : Var Γ A) (y : Var Γ B),
      x.toRawIdx = y.toRawIdx → A = B ∧ HEq x y
  | _, _, .here, .here, _ => ⟨rfl, HEq.refl _⟩
  | _, _, .here, .there _, h => by simp [Var.toRawIdx] at h
  | _, _, .there _, .here, h => by simp [Var.toRawIdx] at h
  | _, _, .there x, .there y, h => by
      obtain ⟨rfl, hxy⟩ := Var.eq_of_toRawIdx x y (by simpa [Var.toRawIdx] using h)
      cases eq_of_heq hxy
      exact ⟨rfl, HEq.refl _⟩

/-! ### Typed structural equality

Heterogeneous in both the context and the type, so that binders can be entered
without transporting either side. Soundness for neutrals returns the type
equality as well; that is what makes replacement well-typed.

`sat` nodes are operational metadata rather than focused syntax, so two
saturation phases are never identified here.
-/

mutual
def NegNeu.beq : {Γ Δ : Ctx sig} → {A B : Object sig.nBases} →
    NegNeu Γ A → NegNeu Δ B → Bool
  | _, _, _, _, .var x, .var y => x.toRawIdx == y.toRawIdx
  | _, _, _, _, .app f a, .app g b => NegNeu.beq f g && InvTm.beq a b
  | _, _, _, _, .fst f, .fst g => NegNeu.beq f g
  | _, _, _, _, .snd f, .snd g => NegNeu.beq f g
  | _, _, _, _, _, _ => false

def PosNeu.beq : {Γ Δ : Ctx sig} → {A B : Object sig.nBases} →
    PosNeu Γ A → PosNeu Δ B → Bool
  | _, _, _, _, .neu n, .neu m => NegNeu.beq n m
  | _, _, _, _, .inl p, .inl q => PosNeu.beq p q
  | _, _, _, _, .inr p, .inr q => PosNeu.beq p q
  | _, _, _, _, .val t, .val u => InvTm.beq t u
  | _, _, _, _, _, _ => false

def InvTm.beq : {Γ Δ : Ctx sig} → {A B : Object sig.nBases} →
    InvTm Γ A → InvTm Δ B → Bool
  | _, _, _, _, .unit, .unit => true
  | _, _, _, _, .pair t₁ t₂, .pair u₁ u₂ => InvTm.beq t₁ u₁ && InvTm.beq t₂ u₂
  | _, _, _, _, .lam t, .lam u => InvTm.beq t u
  | _, _, _, _, .case n t u, .case m v w =>
      NegNeu.beq n m && InvTm.beq t v && InvTm.beq u w
  | _, _, _, _, .abort n, .abort m => NegNeu.beq n m
  | _, _, _, _, .foc f, .foc g => FocTm.beq f g
  | _, _, _, _, _, _ => false

def FocTm.beq : {Γ Δ : Ctx sig} → {A B : Object sig.nBases} →
    FocTm Γ A → FocTm Δ B → Bool
  | _, _, _, _, .pos (.done p), .pos (.done q) => PosNeu.beq p q
  | _, _, _, _, .neg (.done n), .neg (.done m) => NegNeu.beq n m
  | _, _, _, _, .letPos n t, .letPos m u => NegNeu.beq n m && InvTm.beq t u
  | _, _, _, _, _, _ => false
end

/-!
Soundness of the typed comparison. For neutrals it also returns the type
equality: that is what makes replacing an occurrence by the abstraction
variable well-typed.
-/

mutual
theorem NegNeu.eq_of_beq {Γ : Ctx sig} :
    ∀ {A B : Object sig.nBases} (m : NegNeu Γ A) (n : NegNeu Γ B),
      NegNeu.beq m n = true → A = B ∧ HEq m n
  | _, _, .var x, n, h => by
      cases n with
      | var y =>
          obtain ⟨rfl, hxy⟩ :=
            Var.eq_of_toRawIdx x y (by simpa [NegNeu.beq] using h)
          cases eq_of_heq hxy
          exact ⟨rfl, HEq.refl _⟩
      | app g b => simp [NegNeu.beq] at h
      | fst g => simp [NegNeu.beq] at h
      | snd g => simp [NegNeu.beq] at h
  | _, _, .app f a, n, h => by
      cases n with
      | app g b =>
          simp only [NegNeu.beq, Bool.and_eq_true] at h
          obtain ⟨hty, hfg⟩ := NegNeu.eq_of_beq f g h.1
          injection hty with hA hB
          subst hA; subst hB
          cases eq_of_heq hfg
          cases InvTm.eq_of_beq a b h.2
          exact ⟨rfl, HEq.refl _⟩
      | var y => simp [NegNeu.beq] at h
      | fst g => simp [NegNeu.beq] at h
      | snd g => simp [NegNeu.beq] at h
  | _, _, .fst f, n, h => by
      cases n with
      | fst g =>
          obtain ⟨hty, hfg⟩ := NegNeu.eq_of_beq f g (by simpa [NegNeu.beq] using h)
          injection hty with hA hB
          subst hA; subst hB
          cases eq_of_heq hfg
          exact ⟨rfl, HEq.refl _⟩
      | var y => simp [NegNeu.beq] at h
      | app g b => simp [NegNeu.beq] at h
      | snd g => simp [NegNeu.beq] at h
  | _, _, .snd f, n, h => by
      cases n with
      | snd g =>
          obtain ⟨hty, hfg⟩ := NegNeu.eq_of_beq f g (by simpa [NegNeu.beq] using h)
          injection hty with hA hB
          subst hA; subst hB
          cases eq_of_heq hfg
          exact ⟨rfl, HEq.refl _⟩
      | var y => simp [NegNeu.beq] at h
      | app g b => simp [NegNeu.beq] at h
      | fst g => simp [NegNeu.beq] at h
termination_by _A _B m _n _h => NegNeu.size m

theorem PosNeu.eq_of_beq {Γ : Ctx sig} :
    ∀ {A : Object sig.nBases} (p q : PosNeu Γ A), PosNeu.beq p q = true → p = q
  | _, .neu n, q, h => by
      cases q with
      | neu m =>
          obtain ⟨_, hnm⟩ := NegNeu.eq_of_beq n m (by simpa [PosNeu.beq] using h)
          rw [eq_of_heq hnm]
      | inl q' => simp [PosNeu.beq] at h
      | inr q' => simp [PosNeu.beq] at h
      | val u => simp [PosNeu.beq] at h
  | _, .inl p, q, h => by
      cases q with
      | inl q' => rw [PosNeu.eq_of_beq p q' (by simpa [PosNeu.beq] using h)]
      | neu m => simp [PosNeu.beq] at h
      | inr q' => simp [PosNeu.beq] at h
      | val u => simp [PosNeu.beq] at h
  | _, .inr p, q, h => by
      cases q with
      | inr q' => rw [PosNeu.eq_of_beq p q' (by simpa [PosNeu.beq] using h)]
      | neu m => simp [PosNeu.beq] at h
      | inl q' => simp [PosNeu.beq] at h
      | val u => simp [PosNeu.beq] at h
  | _, .val t, q, h => by
      cases q with
      | val u => rw [InvTm.eq_of_beq t u (by simpa [PosNeu.beq] using h)]
      | neu m => simp [PosNeu.beq] at h
      | inl q' => simp [PosNeu.beq] at h
      | inr q' => simp [PosNeu.beq] at h
termination_by _A p _q _h => PosNeu.size p

theorem InvTm.eq_of_beq {Γ : Ctx sig} :
    ∀ {A : Object sig.nBases} (t u : InvTm Γ A), InvTm.beq t u = true → t = u
  | _, .unit, u, h => by
      cases u with
      | unit => rfl
      | case n v w => simp [InvTm.beq] at h
      | abort n => simp [InvTm.beq] at h
      | foc g => simp [InvTm.beq] at h
  | _, .pair t₁ t₂, u, h => by
      cases u with
      | pair u₁ u₂ =>
          simp only [InvTm.beq, Bool.and_eq_true] at h
          rw [InvTm.eq_of_beq t₁ u₁ h.1, InvTm.eq_of_beq t₂ u₂ h.2]
      | case n v w => simp [InvTm.beq] at h
      | abort n => simp [InvTm.beq] at h
      | foc g => simp [InvTm.beq] at h
  | _, .lam t, u, h => by
      cases u with
      | lam v => rw [InvTm.eq_of_beq t v (by simpa [InvTm.beq] using h)]
      | case n v w => simp [InvTm.beq] at h
      | abort n => simp [InvTm.beq] at h
      | foc g => simp [InvTm.beq] at h
  | _, .case n t u, s, h => by
      cases s with
      | case m v w =>
          simp only [InvTm.beq, Bool.and_eq_true] at h
          obtain ⟨hty, hnm⟩ := NegNeu.eq_of_beq n m h.1.1
          injection hty with hA hB
          subst hA; subst hB
          cases eq_of_heq hnm
          rw [InvTm.eq_of_beq t v h.1.2, InvTm.eq_of_beq u w h.2]
      | unit => simp [InvTm.beq] at h
      | pair v w => simp [InvTm.beq] at h
      | lam v => simp [InvTm.beq] at h
      | abort m => simp [InvTm.beq] at h
      | foc g => simp [InvTm.beq] at h
  | _, .abort n, u, h => by
      cases u with
      | abort m =>
          obtain ⟨_, hnm⟩ := NegNeu.eq_of_beq n m (by simpa [InvTm.beq] using h)
          rw [eq_of_heq hnm]
      | unit => simp [InvTm.beq] at h
      | pair v w => simp [InvTm.beq] at h
      | lam v => simp [InvTm.beq] at h
      | case m v w => simp [InvTm.beq] at h
      | foc g => simp [InvTm.beq] at h
  | _, .foc f, u, h => by
      cases u with
      | foc g => rw [FocTm.eq_of_beq f g (by simpa [InvTm.beq] using h)]
      | unit => simp [InvTm.beq] at h
      | pair v w => simp [InvTm.beq] at h
      | lam v => simp [InvTm.beq] at h
      | case m v w => simp [InvTm.beq] at h
      | abort m => simp [InvTm.beq] at h
termination_by _A t _u _h => InvTm.size t

theorem FocTm.eq_of_beq {Γ : Ctx sig} :
    ∀ {A : Object sig.nBases} (f g : FocTm Γ A), FocTm.beq f g = true → f = g
  | _, .pos (.done p), g, h => by
      cases g with
      | pos q =>
          cases q with
          | done q' => rw [PosNeu.eq_of_beq p q' (by simpa [FocTm.beq] using h)]
      | neg m => simp [FocTm.beq] at h
      | letPos m u => simp [FocTm.beq] at h
      | sat s => simp [FocTm.beq] at h
  | _, .neg (.done n), g, h => by
      cases g with
      | neg q =>
          cases q with
          | done m =>
              obtain ⟨_, hnm⟩ := NegNeu.eq_of_beq n m (by simpa [FocTm.beq] using h)
              rw [eq_of_heq hnm]
      | pos q => simp [FocTm.beq] at h
      | letPos m u => simp [FocTm.beq] at h
      | sat s => simp [FocTm.beq] at h
  | _, .letPos n t, g, h => by
      cases g with
      | letPos m u =>
          simp only [FocTm.beq, Bool.and_eq_true] at h
          obtain ⟨rfl, hnm⟩ := NegNeu.eq_of_beq n m h.1
          cases eq_of_heq hnm
          rw [InvTm.eq_of_beq t u h.2]
      | pos q => simp [FocTm.beq] at h
      | neg q => simp [FocTm.beq] at h
      | sat s => simp [FocTm.beq] at h
  | _, .sat s, g, h => by simp [FocTm.beq] at h
termination_by _A f _g _h => FocTm.size f
end

end Equality
end Gimbal
