/-
  Typed structural equality for focused syntax.

  Comparison is heterogeneous in both the context and the type, so that binders
  can be entered without transporting either side. Soundness for neutrals
  returns the type equality as well; that is what makes a replacement at an
  occurrence site well-typed, and what lets the ICC canonicalizer identify the
  two scrutinees of a nested `case`.

  **Schedule metadata (intentional split):**

  * `FocTm.beq` compares `sat` **schedules** (`decide (s = s')`) as well as
    bodies. It is strict structural equality of focused terms, including
    operational saturation annotations.
  * `ICCCode` / `FocCode.beq` **erase** schedules: encode maps `.sat (.mk _ t)`
    to `.foc (.body c)`. Code equality is the semantic ICC comparison surface
    for design E; it must not require schedule identity.
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

`FocTm.beq` on `.sat` is schedule-strict (see module docstring). Ordered-phase
codes erase schedules; do not conflate the two equality surfaces.
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
  | _, _, _, _, .sat (.mk s t), .sat (.mk s' u) =>
      decide (s = s') && InvTm.beq t u
  | _, _, _, _, _, _ => false
end

/-! ### A total structural order on raw focused syntax

The nested `case`/`case` commuting conversion is symmetric: it can move either
scrutinee outward. Orienting it needs a total order on scrutinees, and the order
has to be stable under weakening, since the conversion re-weakens the scrutinee
it pushes inward. Comparing raw syntax lexicographically, with de Bruijn indices
compared numerically, is such an order: weakening shifts free indices by a
strictly monotone map and leaves the tree shape alone.
-/

mutual
def RawNeu.cmp : RawNeu → RawNeu → Ordering
  | .var i, .var j => compare i j
  | .var _, _ => .lt
  | _, .var _ => .gt
  | .app n a, .app m b => (RawNeu.cmp n m).then (RawFocused.cmp a b)
  | .app .., _ => .lt
  | _, .app .. => .gt
  | .fst n, .fst m => RawNeu.cmp n m
  | .fst _, _ => .lt
  | _, .fst _ => .gt
  | .snd n, .snd m => RawNeu.cmp n m

def RawPos.cmp : RawPos → RawPos → Ordering
  | .neu n, .neu m => RawNeu.cmp n m
  | .neu _, _ => .lt
  | _, .neu _ => .gt
  | .inl p, .inl q => RawPos.cmp p q
  | .inl _, _ => .lt
  | _, .inl _ => .gt
  | .inr p, .inr q => RawPos.cmp p q
  | .inr _, _ => .lt
  | _, .inr _ => .gt
  | .val t, .val u => RawFocused.cmp t u

def RawFocused.cmp : RawFocused → RawFocused → Ordering
  | .unit, .unit => .eq
  | .unit, _ => .lt
  | _, .unit => .gt
  | .pair t₁ t₂, .pair u₁ u₂ => (RawFocused.cmp t₁ u₁).then (RawFocused.cmp t₂ u₂)
  | .pair .., _ => .lt
  | _, .pair .. => .gt
  | .lam t, .lam u => RawFocused.cmp t u
  | .lam _, _ => .lt
  | _, .lam _ => .gt
  | .case n t₁ t₂, .case m u₁ u₂ =>
      ((RawNeu.cmp n m).then (RawFocused.cmp t₁ u₁)).then (RawFocused.cmp t₂ u₂)
  | .case .., _ => .lt
  | _, .case .. => .gt
  | .abort n, .abort m => RawNeu.cmp n m
  | .abort _, _ => .lt
  | _, .abort _ => .gt
  | .pos p, .pos q => RawPos.cmp p q
  | .pos _, _ => .lt
  | _, .pos _ => .gt
  | .neg n, .neg m => RawNeu.cmp n m
  | .neg _, _ => .lt
  | _, .neg _ => .gt
  | .letPos n t, .letPos m u => (RawNeu.cmp n m).then (RawFocused.cmp t u)
  | .letPos .., _ => .lt
  | _, .letPos .. => .gt
  | .sat k t, .sat l u => (compare k l).then (RawFocused.cmp t u)
end

/-- Strict order on typed neutrals, via their raw form. -/
def NegNeu.blt {Γ Δ : Ctx sig} {A B : Object sig.nBases}
    (n : NegNeu Γ A) (m : NegNeu Δ B) : Bool :=
  RawNeu.cmp (NegNeu.toRaw n) (NegNeu.toRaw m) == .lt

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
  | _, .sat (.mk s t), g, h => by
      cases g with
      | sat s' =>
          cases s' with
          | mk s' u =>
              simp only [FocTm.beq, Bool.and_eq_true, decide_eq_true_eq] at h
              cases h.1
              rw [InvTm.eq_of_beq t u h.2]
      | pos q => simp [FocTm.beq] at h
      | neg q => simp [FocTm.beq] at h
      | letPos m u => simp [FocTm.beq] at h
termination_by _A f _g _h => FocTm.size f
end

/-! ### Reflexivity of typed `beq` -/

mutual
theorem NegNeu.beq_rfl {Γ : Ctx sig} :
    ∀ {A : Object sig.nBases} (n : NegNeu Γ A), NegNeu.beq n n = true
  | _, .var x => by simp [NegNeu.beq]
  | _, .app f a => by
      simp only [NegNeu.beq, Bool.and_eq_true]
      exact ⟨NegNeu.beq_rfl f, InvTm.beq_rfl a⟩
  | _, .fst f => by
      simp only [NegNeu.beq]
      exact NegNeu.beq_rfl f
  | _, .snd f => by
      simp only [NegNeu.beq]
      exact NegNeu.beq_rfl f
termination_by _A n => NegNeu.size n

theorem PosNeu.beq_rfl {Γ : Ctx sig} :
    ∀ {A : Object sig.nBases} (p : PosNeu Γ A), PosNeu.beq p p = true
  | _, .neu n => by
      simp only [PosNeu.beq]
      exact NegNeu.beq_rfl n
  | _, .inl p => by
      simp only [PosNeu.beq]
      exact PosNeu.beq_rfl p
  | _, .inr p => by
      simp only [PosNeu.beq]
      exact PosNeu.beq_rfl p
  | _, .val t => by
      simp only [PosNeu.beq]
      exact InvTm.beq_rfl t
termination_by _A p => PosNeu.size p

theorem InvTm.beq_rfl {Γ : Ctx sig} :
    ∀ {A : Object sig.nBases} (t : InvTm Γ A), InvTm.beq t t = true
  | _, .unit => by simp [InvTm.beq]
  | _, .pair t₁ t₂ => by
      simp only [InvTm.beq, Bool.and_eq_true]
      exact ⟨InvTm.beq_rfl t₁, InvTm.beq_rfl t₂⟩
  | _, .lam t => by
      simp only [InvTm.beq]
      exact InvTm.beq_rfl t
  | _, .case n t u => by
      simp only [InvTm.beq, Bool.and_eq_true]
      exact ⟨⟨NegNeu.beq_rfl n, InvTm.beq_rfl t⟩, InvTm.beq_rfl u⟩
  | _, .abort n => by
      simp only [InvTm.beq]
      exact NegNeu.beq_rfl n
  | _, .foc f => by
      simp only [InvTm.beq]
      exact FocTm.beq_rfl f
termination_by _A t => InvTm.size t

theorem FocTm.beq_rfl {Γ : Ctx sig} :
    ∀ {A : Object sig.nBases} (f : FocTm Γ A), FocTm.beq f f = true
  | _, .pos (.done p) => by
      simp only [FocTm.beq]
      exact PosNeu.beq_rfl p
  | _, .neg (.done n) => by
      simp only [FocTm.beq]
      exact NegNeu.beq_rfl n
  | _, .letPos n t => by
      simp only [FocTm.beq, Bool.and_eq_true]
      exact ⟨NegNeu.beq_rfl n, InvTm.beq_rfl t⟩
  | _, .sat (.mk s t) => by
      simp only [FocTm.beq, decide_eq_true_eq, Bool.true_and]
      exact InvTm.beq_rfl t
termination_by _A f => FocTm.size f
end

end Equality
end Gimbal
