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

import Gimbal.Equality.Preserve

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

/-! ### Occurrence sites

A site is recognised by `NegNeu.beq`, whose soundness lemma supplies the type
equality; that is what makes the replacement `x : Var Γ P` typecheck at the
site's own type.
-/

@[simp] theorem NegNeu.cast_self {Γ : Ctx sig} {A : Object sig.nBases}
    (h : A = A) (n : NegNeu Γ A) : NegNeu.cast h n = n := rfl

/-- The abstraction variable, transported to the type of a matching site. -/
def NegNeu.atSite {Γ : Ctx sig} {P A : Object sig.nBases} (x : Var Γ P)
    {m : NegNeu Γ P} {n : NegNeu Γ A} (h : NegNeu.beq n m = true) : NegNeu Γ A :=
  NegNeu.cast (NegNeu.eq_of_beq n m h).1.symm (.var x)

/-! ### Typed neutral abstraction

`abstr x m t` replaces every occurrence of the observed neutral `m` by the
abstraction variable `x`. Descending under a binder shifts both together, so
the pair `(x, m)` stays well-typed without any raw de Bruijn arithmetic.
-/

mutual
/-- Replace occurrences of `m` inside a neutral spine. -/
def NegNeu.abstr {Γ : Ctx sig} {P A : Object sig.nBases}
    (x : Var Γ P) (m : NegNeu Γ P) : NegNeu Γ A → NegNeu Γ A
  | .var y =>
      if h : NegNeu.beq (NegNeu.var y) m = true then NegNeu.atSite x h
      else .var y
  | .app f a =>
      if h : NegNeu.beq (NegNeu.app f a) m = true then NegNeu.atSite x h
      else .app (NegNeu.abstr x m f) (InvTm.abstr x m a)
  | .fst f =>
      if h : NegNeu.beq (NegNeu.fst f) m = true then NegNeu.atSite x h
      else .fst (NegNeu.abstr x m f)
  | .snd f =>
      if h : NegNeu.beq (NegNeu.snd f) m = true then NegNeu.atSite x h
      else .snd (NegNeu.abstr x m f)

/-- Replace occurrences of `m` inside a positive value. -/
def PosNeu.abstr {Γ : Ctx sig} {P A : Object sig.nBases}
    (x : Var Γ P) (m : NegNeu Γ P) : PosNeu Γ A → PosNeu Γ A
  | .neu n => .neu (NegNeu.abstr x m n)
  | .inl p => .inl (PosNeu.abstr x m p)
  | .inr p => .inr (PosNeu.abstr x m p)
  | .val t => .val (InvTm.abstr x m t)

/-- Replace occurrences of `m` inside an invertible term. -/
def InvTm.abstr {Γ : Ctx sig} {P A : Object sig.nBases}
    (x : Var Γ P) (m : NegNeu Γ P) : InvTm Γ A → InvTm Γ A
  | .unit => .unit
  | .pair t u => .pair (InvTm.abstr x m t) (InvTm.abstr x m u)
  | .lam t => .lam (InvTm.abstr (.there x) (NegNeu.weaken m) t)
  | .case n t u =>
      .case (NegNeu.abstr x m n)
        (InvTm.abstr (.there x) (NegNeu.weaken m) t)
        (InvTm.abstr (.there x) (NegNeu.weaken m) u)
  | .abort n => .abort (NegNeu.abstr x m n)
  | .foc f => .foc (FocTm.abstr x m f)

/-- Replace occurrences of `m` inside a focused term. -/
def FocTm.abstr {Γ : Ctx sig} {P A : Object sig.nBases}
    (x : Var Γ P) (m : NegNeu Γ P) : FocTm Γ A → FocTm Γ A
  | .pos (.done p) => .pos (.done (PosNeu.abstr x m p))
  | .neg (.done n) => .neg (.done (NegNeu.abstr x m n))
  | .letPos n t =>
      .letPos (NegNeu.abstr x m n)
        (InvTm.abstr (.there x) (NegNeu.weaken m) t)
  | .sat (.mk s t) => .sat (.mk s (InvTm.abstr x m t))
end

/-! ### Abstraction is invisible to any substitution that undoes it

The single hypothesis is that the substitution sends the abstraction variable
back to (the substituted) observation. Every replacement site is a site where
the subterm *is* the observation, so the two sides substitute to the same term.
-/

/-- Pushing a substitution past a weakening. -/
theorem subst_exts_weakenTerm {Γ Δ : Ctx sig} {A B : Object sig.nBases}
    (σ : Subst sig Γ Δ) (t : Tm Γ B) :
    subst (Subst.exts (A := A) σ) (weakenTerm t) = weakenTerm (subst σ t) := by
  rw [weakenTerm_eq_rename, subst_rename, weakenTerm_eq_rename, rename_subst]
  refine subst_eq_of_pointwise ?_ t
  intro C x
  rfl

/-- A replacement site is a site where the subterm *is* the observation. -/
theorem subst_erase_atSite {Γ Δ : Ctx sig} {P A : Object sig.nBases}
    (σ : Subst sig Γ Δ) (x : Var Γ P) {m : NegNeu Γ P} {n : NegNeu Γ A}
    (h : NegNeu.beq n m = true) (hx : σ x = subst σ m.erase) :
    subst σ (NegNeu.atSite x h).erase = subst σ n.erase := by
  obtain ⟨hty, hnm⟩ := NegNeu.eq_of_beq n m h
  cases hty
  cases eq_of_heq hnm
  simp only [NegNeu.atSite, NegNeu.cast_self, NegNeu.erase]
  exact hx

/-- The abstraction invariant survives going under a binder. -/
theorem abstr_hyp_exts {Γ Δ : Ctx sig} {P B : Object sig.nBases}
    {σ : Subst sig Γ Δ} {x : Var Γ P} {m : NegNeu Γ P}
    (hx : σ x = subst σ m.erase) :
    Subst.exts (A := B) σ (Var.there x) =
      subst (Subst.exts (A := B) σ) (NegNeu.weaken (B := B) m).erase := by
  show weakenTerm (σ x) = _
  rw [NegNeu.erase_weaken, subst_exts_weakenTerm, hx]

mutual
theorem NegNeu.subst_erase_abstr {Γ Δ : Ctx sig} {P A : Object sig.nBases}
    (σ : Subst sig Γ Δ) (x : Var Γ P) (m : NegNeu Γ P)
    (hx : σ x = subst σ m.erase) :
    ∀ n : NegNeu Γ A, subst σ (NegNeu.abstr x m n).erase = subst σ n.erase
  | .var y => by
      rw [NegNeu.abstr]
      split
      · exact subst_erase_atSite σ x ‹_› hx
      · rfl
  | .app f a => by
      rw [NegNeu.abstr]
      split
      · exact subst_erase_atSite σ x ‹_› hx
      · simp only [NegNeu.erase, subst]
        rw [NegNeu.subst_erase_abstr σ x m hx f,
          InvTm.subst_erase_abstr σ x m hx a]
  | .fst f => by
      rw [NegNeu.abstr]
      split
      · exact subst_erase_atSite σ x ‹_› hx
      · simp only [NegNeu.erase, subst]
        rw [NegNeu.subst_erase_abstr σ x m hx f]
  | .snd f => by
      rw [NegNeu.abstr]
      split
      · exact subst_erase_atSite σ x ‹_› hx
      · simp only [NegNeu.erase, subst]
        rw [NegNeu.subst_erase_abstr σ x m hx f]

theorem PosNeu.subst_erase_abstr {Γ Δ : Ctx sig} {P A : Object sig.nBases}
    (σ : Subst sig Γ Δ) (x : Var Γ P) (m : NegNeu Γ P)
    (hx : σ x = subst σ m.erase) :
    ∀ p : PosNeu Γ A, subst σ (PosNeu.abstr x m p).erase = subst σ p.erase
  | .neu n => by
      simp only [PosNeu.abstr, PosNeu.erase]
      exact NegNeu.subst_erase_abstr σ x m hx n
  | .inl p => by
      simp only [PosNeu.abstr, PosNeu.erase, subst]
      rw [PosNeu.subst_erase_abstr σ x m hx p]
  | .inr p => by
      simp only [PosNeu.abstr, PosNeu.erase, subst]
      rw [PosNeu.subst_erase_abstr σ x m hx p]
  | .val t => by
      simp only [PosNeu.abstr, PosNeu.erase]
      exact InvTm.subst_erase_abstr σ x m hx t

theorem InvTm.subst_erase_abstr {Γ Δ : Ctx sig} {P A : Object sig.nBases}
    (σ : Subst sig Γ Δ) (x : Var Γ P) (m : NegNeu Γ P)
    (hx : σ x = subst σ m.erase) :
    ∀ t : InvTm Γ A, subst σ (InvTm.abstr x m t).erase = subst σ t.erase
  | .unit => by simp only [InvTm.abstr]
  | .pair t u => by
      simp only [InvTm.abstr, InvTm.erase, subst]
      rw [InvTm.subst_erase_abstr σ x m hx t, InvTm.subst_erase_abstr σ x m hx u]
  | .lam t => by
      simp only [InvTm.abstr, InvTm.erase, subst]
      rw [InvTm.subst_erase_abstr (Subst.exts σ) (.there x) (NegNeu.weaken m)
        (abstr_hyp_exts hx) t]
  | .case n t u => by
      simp only [InvTm.abstr, InvTm.erase, subst]
      rw [NegNeu.subst_erase_abstr σ x m hx n,
        InvTm.subst_erase_abstr (Subst.exts σ) (.there x) (NegNeu.weaken m)
          (abstr_hyp_exts hx) t,
        InvTm.subst_erase_abstr (Subst.exts σ) (.there x) (NegNeu.weaken m)
          (abstr_hyp_exts hx) u]
  | .abort n => by
      simp only [InvTm.abstr, InvTm.erase, subst]
      rw [NegNeu.subst_erase_abstr σ x m hx n]
  | .foc f => by
      simp only [InvTm.abstr, InvTm.erase]
      exact FocTm.subst_erase_abstr σ x m hx f

theorem FocTm.subst_erase_abstr {Γ Δ : Ctx sig} {P A : Object sig.nBases}
    (σ : Subst sig Γ Δ) (x : Var Γ P) (m : NegNeu Γ P)
    (hx : σ x = subst σ m.erase) :
    ∀ f : FocTm Γ A, subst σ (FocTm.abstr x m f).erase = subst σ f.erase
  | .pos (.done p) => by
      simp only [FocTm.abstr, FocTm.erase, PosIntro.erase]
      exact PosNeu.subst_erase_abstr σ x m hx p
  | .neg (.done n) => by
      simp only [FocTm.abstr, FocTm.erase, NegElim.erase]
      exact NegNeu.subst_erase_abstr σ x m hx n
  | .letPos n t => by
      simp only [FocTm.abstr, FocTm.erase]
      show subst σ (subst0 _ _) = subst σ (subst0 _ _)
      rw [subst0, subst0, subst_comp, subst_comp]
      have hn := NegNeu.subst_erase_abstr σ x m hx n
      have ht := InvTm.subst_erase_abstr (Subst.exts σ) (.there x)
        (NegNeu.weaken m) (abstr_hyp_exts hx) t
      calc subst (substComp σ (Subst.single (NegNeu.abstr x m n).erase))
              (InvTm.abstr (.there x) (NegNeu.weaken m) t).erase
          = subst (substComp (Subst.single (subst σ n.erase)) (Subst.exts σ))
              (InvTm.abstr (.there x) (NegNeu.weaken m) t).erase := by
            refine subst_eq_of_pointwise ?_ _
            intro C y
            cases y with
            | here => exact hn
            | there z => exact (subst0_weakenTerm (σ z) (subst σ n.erase)).symm
        _ = subst (Subst.single (subst σ n.erase)) (subst (Subst.exts σ)
              (InvTm.abstr (.there x) (NegNeu.weaken m) t).erase) := by
            rw [subst_comp]
        _ = subst (Subst.single (subst σ n.erase)) (subst (Subst.exts σ) t.erase) := by
            rw [ht]
        _ = subst (substComp σ (Subst.single n.erase)) t.erase := by
            rw [subst_comp]
            refine subst_eq_of_pointwise ?_ _
            intro C y
            cases y with
            | here => rfl
            | there z => exact subst0_weakenTerm (σ z) (subst σ n.erase)
  | .sat (.mk s t) => by
      simp only [FocTm.abstr, FocTm.erase, SatTm.erase]
      exact InvTm.subst_erase_abstr σ x m hx t
end

/-! ### Strong positive cut

Binding the observation with `letPos` and abstracting its occurrences leaves
the erasure *unchanged* — not merely equal up to the theory.
-/

/-- The `letPos` cut of an abstracted continuation erases to the continuation. -/
theorem erase_letPos_abstr {Γ : Ctx sig} {P A : Object sig.nBases}
    (m : NegNeu Γ P) (t : InvTm Γ A) :
    (FocTm.letPos m
        (InvTm.abstr (P := P) .here (NegNeu.weaken m) (InvTm.weaken t))).erase =
      t.erase := by
  have hx : (Subst.single m.erase) (Var.here (A := P)) =
      subst (Subst.single m.erase) (NegNeu.weaken (B := P) m).erase := by
    rw [NegNeu.erase_weaken]
    exact (subst0_weakenTerm m.erase m.erase).symm
  show subst0 (InvTm.abstr .here (NegNeu.weaken m) (InvTm.weaken t)).erase
      m.erase = t.erase
  rw [subst0, InvTm.subst_erase_abstr (Subst.single m.erase) .here
    (NegNeu.weaken m) hx (InvTm.weaken t), InvTm.erase_weaken]
  exact subst0_weakenTerm t.erase m.erase

/-! ### Abstraction preserves phase legality -/

theorem wellNeg_atSite {Γ : Ctx sig} {P A : Object sig.nBases} (x : Var Γ P)
    {m : NegNeu Γ P} {n : NegNeu Γ A} (h : NegNeu.beq n m = true) :
    WellNeg (NegNeu.atSite x h) := by
  obtain ⟨hty, _⟩ := NegNeu.eq_of_beq n m h
  cases hty
  simp only [NegNeu.atSite, NegNeu.cast_self]
  exact .var

mutual
theorem wellNeg_abstr {Γ : Ctx sig} {P A : Object sig.nBases} (x : Var Γ P)
    (m : NegNeu Γ P) :
    ∀ {n : NegNeu Γ A}, WellNeg n → WellNeg (NegNeu.abstr x m n)
  | .var _, _ => by
      rw [NegNeu.abstr]; split
      · exact wellNeg_atSite x ‹_›
      · exact .var
  | .app _ _, .app hf ha => by
      rw [NegNeu.abstr]; split
      · exact wellNeg_atSite x ‹_›
      · exact .app (wellNeg_abstr x m hf) (wellInv_abstr x m ha)
  | .fst _, .fst hf => by
      rw [NegNeu.abstr]; split
      · exact wellNeg_atSite x ‹_›
      · exact .fst (wellNeg_abstr x m hf)
  | .snd _, .snd hf => by
      rw [NegNeu.abstr]; split
      · exact wellNeg_atSite x ‹_›
      · exact .snd (wellNeg_abstr x m hf)

theorem wellPos_abstr {Γ : Ctx sig} {P A : Object sig.nBases} (x : Var Γ P)
    (m : NegNeu Γ P) :
    ∀ {p : PosNeu Γ A}, WellPos p → WellPos (PosNeu.abstr x m p)
  | .neu _, .neu hpol hn => by
      rw [PosNeu.abstr]; exact .neu hpol (wellNeg_abstr x m hn)
  | .inl _, .inl hp => by rw [PosNeu.abstr]; exact .inl (wellPos_abstr x m hp)
  | .inr _, .inr hp => by rw [PosNeu.abstr]; exact .inr (wellPos_abstr x m hp)
  | .val _, .val hpol ht => by
      rw [PosNeu.abstr]; exact .val hpol (wellInv_abstr x m ht)

theorem wellInv_abstr {Γ : Ctx sig} {P A : Object sig.nBases} (x : Var Γ P)
    (m : NegNeu Γ P) :
    ∀ {t : InvTm Γ A}, WellInv t → WellInv (InvTm.abstr x m t)
  | .unit, _ => by rw [InvTm.abstr]; exact .unit
  | .pair _ _, .pair ht hu => by
      rw [InvTm.abstr]; exact .pair (wellInv_abstr x m ht) (wellInv_abstr x m hu)
  | .lam _, .lam ht => by rw [InvTm.abstr]; exact .lam (wellInv_abstr _ _ ht)
  | .case _ _ _, .case hn ht hu => by
      rw [InvTm.abstr]
      exact .case (wellNeg_abstr x m hn) (wellInv_abstr _ _ ht)
        (wellInv_abstr _ _ hu)
  | .abort _, .abort hn => by rw [InvTm.abstr]; exact .abort (wellNeg_abstr x m hn)
  | .foc _, .foc hf => by rw [InvTm.abstr]; exact .foc (wellFoc_abstr x m hf)

theorem wellFoc_abstr {Γ : Ctx sig} {P A : Object sig.nBases} (x : Var Γ P)
    (m : NegNeu Γ P) :
    ∀ {f : FocTm Γ A}, WellFoc f → WellFoc (FocTm.abstr x m f)
  | .pos (.done _), .pos hpol hp => by
      rw [FocTm.abstr]; exact .pos hpol (wellPos_abstr x m hp)
  | .neg (.done _), .neg hpol hn => by
      rw [FocTm.abstr]; exact .neg hpol (wellNeg_abstr x m hn)
  | .letPos _ _, .letPos hpol hn ht => by
      rw [FocTm.abstr]
      exact .letPos hpol (wellNeg_abstr x m hn) (wellInv_abstr _ _ ht)
  | .sat (.mk _ _), .sat ht => by rw [FocTm.abstr]; exact .sat (wellInv_abstr x m ht)
end

/-- Strong positive cut preserves meaning. -/
theorem tmEq_letPos_abstr {Γ : Ctx sig} {P A : Object sig.nBases}
    (m : NegNeu Γ P) (t : InvTm Γ A) :
    TmEq
      (InvTm.foc (FocTm.letPos m
        (InvTm.abstr (P := P) .here (NegNeu.weaken m) (InvTm.weaken t)))).erase
      t.erase :=
  TmEq.of_eq (erase_letPos_abstr m t)

end Equality
end Gimbal
