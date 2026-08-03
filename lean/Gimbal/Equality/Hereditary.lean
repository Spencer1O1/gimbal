/-
  Hereditary substitution for the focused equality calculus.

  Focusing is a total function on intrinsic terms: rather than substituting and
  then re-normalizing under a fuel budget, a substitution contracts every redex
  it exposes as it goes (computational cut admissibility).

  Termination is by the explicit lexicographic measure

      (objectSize (cut type), phase rank, structural size)

  with phase rank `0` for the hereditary eliminators and `1` for the
  substitution functions. A substitution only enters an eliminator at the type
  of the value it just produced, which is always a subformula of the cut type,
  so the first component never grows; when it stays equal the rank strictly
  drops, and each eliminator recurses on a strictly smaller term.
-/

import Gimbal.Equality.Focused

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Measures -/

/-- Structural size of a type: the dominant component of the measure. -/
def objectSize {n : Nat} : Object n → Nat
  | .base _ => 1
  | .unit => 1
  | .never => 1
  | .prod A B => objectSize A + objectSize B + 1
  | .coprod A B => objectSize A + objectSize B + 1
  | .exp A B => objectSize A + objectSize B + 1

@[simp] theorem objectSize_prod {n : Nat} (A B : Object n) :
    objectSize (.prod A B) = objectSize A + objectSize B + 1 := rfl

@[simp] theorem objectSize_coprod {n : Nat} (A B : Object n) :
    objectSize (.coprod A B) = objectSize A + objectSize B + 1 := rfl

@[simp] theorem objectSize_exp {n : Nat} (A B : Object n) :
    objectSize (.exp A B) = objectSize A + objectSize B + 1 := rfl

theorem objectSize_pos {n : Nat} (A : Object n) : 0 < objectSize A := by
  cases A <;> simp [objectSize]

mutual
/-- Structural size of a negative neutral. -/
def NegNeu.size {Γ : Ctx sig} {A : Object sig.nBases} : NegNeu Γ A → Nat
  | .var _ => 1
  | .app n t => NegNeu.size n + InvTm.size t + 1
  | .fst n => NegNeu.size n + 1
  | .snd n => NegNeu.size n + 1

/-- Structural size of a positive value. -/
def PosNeu.size {Γ : Ctx sig} {A : Object sig.nBases} : PosNeu Γ A → Nat
  | .neu n => NegNeu.size n + 1
  | .inl p => PosNeu.size p + 1
  | .inr p => PosNeu.size p + 1
  | .val t => InvTm.size t + 1

/-- Structural size of an invertible term. -/
def InvTm.size {Γ : Ctx sig} {A : Object sig.nBases} : InvTm Γ A → Nat
  | .unit => 1
  | .pair t u => InvTm.size t + InvTm.size u + 1
  | .lam t => InvTm.size t + 1
  | .case n t u => NegNeu.size n + InvTm.size t + InvTm.size u + 1
  | .abort n => NegNeu.size n + 1
  | .foc f => FocTm.size f + 1

/-- Structural size of a focused term. -/
def FocTm.size {Γ : Ctx sig} {A : Object sig.nBases} : FocTm Γ A → Nat
  | .pos (.done p) => PosNeu.size p + 1
  | .neg (.done n) => NegNeu.size n + 1
  | .letPos n t => NegNeu.size n + InvTm.size t + 1
  | .sat (.mk _ t) => InvTm.size t + 1
end

/-- Let the termination checker see through the structural size functions. -/
macro_rules
  | `(tactic| decreasing_trivial) =>
    `(tactic| simp only [NegNeu.size, PosNeu.size, InvTm.size, FocTm.size]; omega)

/-! ### Renaming preserves size

The measure is taken on terms that focusing sometimes has to re-index (to
exchange or contract binders), so size must not see renamings.
-/

mutual
theorem NegNeu.size_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (n : NegNeu Γ A) :
    (NegNeu.rename ρ n).size = n.size :=
  match n with
  | .var _ => rfl
  | .app m t => by
      simp [NegNeu.rename, NegNeu.size, NegNeu.size_rename ρ m,
        InvTm.size_rename ρ t]
  | .fst m => by simp [NegNeu.rename, NegNeu.size, NegNeu.size_rename ρ m]
  | .snd m => by simp [NegNeu.rename, NegNeu.size, NegNeu.size_rename ρ m]
termination_by n.size
decreasing_by all_goals decreasing_trivial

theorem PosNeu.size_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (p : PosNeu Γ A) :
    (PosNeu.rename ρ p).size = p.size :=
  match p with
  | .neu n => by simp [PosNeu.rename, PosNeu.size, NegNeu.size_rename ρ n]
  | .inl q => by simp [PosNeu.rename, PosNeu.size, PosNeu.size_rename ρ q]
  | .inr q => by simp [PosNeu.rename, PosNeu.size, PosNeu.size_rename ρ q]
  | .val t => by simp [PosNeu.rename, PosNeu.size, InvTm.size_rename ρ t]
termination_by p.size
decreasing_by all_goals decreasing_trivial

theorem InvTm.size_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (t : InvTm Γ A) :
    (InvTm.rename ρ t).size = t.size :=
  match t with
  | .unit => rfl
  | .pair t u => by
      simp [InvTm.rename, InvTm.size, InvTm.size_rename ρ t,
        InvTm.size_rename ρ u]
  | .lam t => by
      simp [InvTm.rename, InvTm.size, InvTm.size_rename (Rename.ext ρ) t]
  | .case n t u => by
      simp [InvTm.rename, InvTm.size, NegNeu.size_rename ρ n,
        InvTm.size_rename (Rename.ext ρ) t, InvTm.size_rename (Rename.ext ρ) u]
  | .abort n => by simp [InvTm.rename, InvTm.size, NegNeu.size_rename ρ n]
  | .foc f => by simp [InvTm.rename, InvTm.size, FocTm.size_rename ρ f]
termination_by t.size
decreasing_by all_goals decreasing_trivial

theorem FocTm.size_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (f : FocTm Γ A) :
    (FocTm.rename ρ f).size = f.size :=
  match f with
  | .pos (.done p) => by
      simp [FocTm.rename, PosIntro.rename, FocTm.size, PosNeu.size_rename ρ p]
  | .neg (.done n) => by
      simp [FocTm.rename, NegElim.rename, FocTm.size, NegNeu.size_rename ρ n]
  | .letPos n t => by
      simp [FocTm.rename, FocTm.size, NegNeu.size_rename ρ n,
        InvTm.size_rename (Rename.ext ρ) t]
  | .sat (.mk _ t) => by
      simp [FocTm.rename, SatTm.rename, FocTm.size, InvTm.size_rename ρ t]
termination_by f.size
decreasing_by all_goals decreasing_trivial
end

/-- Let the termination checker see through the structural size functions. -/
macro_rules
  | `(tactic| decreasing_trivial) =>
    `(tactic| simp only [NegNeu.size, PosNeu.size, InvTm.size, FocTm.size,
        NegNeu.size_rename, PosNeu.size_rename, InvTm.size_rename,
        FocTm.size_rename]; omega)

@[simp] theorem InvTm.size_weaken {Γ : Ctx sig} {A B : Object sig.nBases}
    (t : InvTm Γ A) : (InvTm.weaken (B := B) t).size = t.size :=
  InvTm.size_rename _ t

/-! ### Identity expansion

Neutrals are expanded to eta-long invertible terms, so a neutral only ever
survives at a positive type (or as the scrutinee of `case`/`abort`).
-/

/-- Identity expansion of a neutral at type `A`. -/
def NegNeu.eta : (A : Object sig.nBases) → {Γ : Ctx sig} → NegNeu Γ A → InvTm Γ A
  | .unit, _, _ => .unit
  | .prod A B, _, n => .pair (NegNeu.eta A (.fst n)) (NegNeu.eta B (.snd n))
  | .exp A B, _, n =>
      .lam (NegNeu.eta B (.app (NegNeu.weaken n) (NegNeu.eta A (.var .here))))
  | .base _, _, n => .foc (.pos (.done (.neu n)))
  | .never, _, n => .abort n
  | .coprod _ _, _, n => .foc (.pos (.done (.neu n)))

/-- A positive value read back as an invertible term. -/
def PosNeu.toInv {Γ : Ctx sig} {A : Object sig.nBases} : PosNeu Γ A → InvTm Γ A
  | .neu n => NegNeu.eta _ n
  | .inl p => .foc (.pos (.done (.inl p)))
  | .inr p => .foc (.pos (.done (.inr p)))
  | .val t => t

/-! ### Coproduct injections

`inl`/`inr` build a positive value, so an injection has to be pushed past the
invertible eliminations of its argument (a case tree of values, not a value).
-/

/-- Inject into the left summand, commuting past invertible eliminations. -/
def InvTm.hinl {Γ : Ctx sig} {A : Object sig.nBases} (B : Object sig.nBases) :
    InvTm Γ A → InvTm Γ (.coprod A B)
  | .case n t u => .case n (InvTm.hinl B t) (InvTm.hinl B u)
  | .abort n => .abort n
  | .foc (.letPos n t) => .foc (.letPos n (InvTm.hinl B t))
  | .foc (.sat (.mk s t)) => .foc (.sat (.mk s (InvTm.hinl B t)))
  | .foc (.pos (.done p)) => .foc (.pos (.done (.inl p)))
  | .foc (.neg (.done n)) => .foc (.pos (.done (.inl (.val (NegNeu.eta _ n)))))
  | .unit => .foc (.pos (.done (.inl (.val .unit))))
  | .pair t u => .foc (.pos (.done (.inl (.val (.pair t u)))))
  | .lam t => .foc (.pos (.done (.inl (.val (.lam t)))))

/-- Inject into the right summand, commuting past invertible eliminations. -/
def InvTm.hinr {Γ : Ctx sig} {B : Object sig.nBases} (A : Object sig.nBases) :
    InvTm Γ B → InvTm Γ (.coprod A B)
  | .case n t u => .case n (InvTm.hinr A t) (InvTm.hinr A u)
  | .abort n => .abort n
  | .foc (.letPos n t) => .foc (.letPos n (InvTm.hinr A t))
  | .foc (.sat (.mk s t)) => .foc (.sat (.mk s (InvTm.hinr A t)))
  | .foc (.pos (.done p)) => .foc (.pos (.done (.inr p)))
  | .foc (.neg (.done n)) => .foc (.pos (.done (.inr (.val (NegNeu.eta _ n)))))
  | .unit => .foc (.pos (.done (.inr (.val .unit))))
  | .pair t u => .foc (.pos (.done (.inr (.val (.pair t u)))))
  | .lam t => .foc (.pos (.done (.inr (.val (.lam t)))))

/-! ### Coproduct η patterns

The two branches of a coproduct η-expansion: the newest variable, identity
expanded and injected on the corresponding side. Saturation commits a
coproduct observation to these, and the ICC canonicalizer contracts them
again. The expansion is what keeps the branch legal when the summand is
negative: `inl ⟨⟩` has to be written `inl (↓⟨⟩)`.
-/

/-- `x. inl x`, the left branch of a coproduct η-expansion. -/
def InvTm.etaInl {Γ : Ctx sig} (A B : Object sig.nBases) :
    InvTm (Γ ▻ A) (.coprod A B) :=
  InvTm.hinl B (NegNeu.eta A (.var .here))

/-- `y. inr y`, the right branch of a coproduct η-expansion. -/
def InvTm.etaInr {Γ : Ctx sig} (A B : Object sig.nBases) :
    InvTm (Γ ▻ B) (.coprod A B) :=
  InvTm.hinr A (NegNeu.eta B (.var .here))

/-! ### Hereditary substitution -/

/--
Result of substituting into a neutral spine.

Either the head was some other variable and the spine is still neutral, or the
spine was exactly the substituted variable, or the head was reduced — in which
case the value's type is a *proper* subformula of the cut type, which is what
makes the eliminators below terminate.
-/
inductive HSubst {sig : Signature} (Γ : Ctx sig) (A C : Object sig.nBases) where
  | neu : NegNeu Γ C → HSubst Γ A C
  | here : InvTm Γ C → A = C → HSubst Γ A C
  | val : InvTm Γ C → objectSize C < objectSize A → HSubst Γ A C

/-- Contract two copies of the newest binder when their types agree. -/
def Rename.diagEq {Γ : Ctx sig} {A P : Object sig.nBases} (h : A = P) :
    Rename sig (Γ ▻ A ▻ P) (Γ ▻ A) := by
  subst h; exact Rename.diag

mutual

/-- Hereditary application. -/
def happ {Γ : Ctx sig} {A B : Object sig.nBases}
    (f : InvTm Γ (.exp A B)) (u : InvTm Γ A) : InvTm Γ B :=
  match f with
  | .lam body => hsubstInv body u
  | .case n t₁ t₂ =>
      .case n (happ t₁ (InvTm.weaken u)) (happ t₂ (InvTm.weaken u))
  | .abort n => .abort n
  | .foc (.pos (.done (.neu n))) => NegNeu.eta B (.app n u)
  | .foc (.pos (.done (.val w))) => happ w u
  | .foc (.neg (.done n)) => NegNeu.eta B (.app n u)
  | .foc (.letPos n w) => .foc (.letPos n (happ w (InvTm.weaken u)))
  | .foc (.sat (.mk s w)) => .foc (.sat (.mk s (happ w u)))
termination_by (objectSize (Object.exp A B), 0, f.size)

/-- Hereditary first projection. -/
def hfst {Γ : Ctx sig} {A B : Object sig.nBases}
    (t : InvTm Γ (.prod A B)) : InvTm Γ A :=
  match t with
  | .pair t₁ _ => t₁
  | .case n t₁ t₂ => .case n (hfst t₁) (hfst t₂)
  | .abort n => .abort n
  | .foc (.pos (.done (.neu n))) => NegNeu.eta A (.fst n)
  | .foc (.pos (.done (.val w))) => hfst w
  | .foc (.neg (.done n)) => NegNeu.eta A (.fst n)
  | .foc (.letPos n w) => .foc (.letPos n (hfst w))
  | .foc (.sat (.mk s w)) => .foc (.sat (.mk s (hfst w)))
termination_by (objectSize (Object.prod A B), 0, t.size)

/-- Hereditary second projection. -/
def hsnd {Γ : Ctx sig} {A B : Object sig.nBases}
    (t : InvTm Γ (.prod A B)) : InvTm Γ B :=
  match t with
  | .pair _ t₂ => t₂
  | .case n t₁ t₂ => .case n (hsnd t₁) (hsnd t₂)
  | .abort n => .abort n
  | .foc (.pos (.done (.neu n))) => NegNeu.eta B (.snd n)
  | .foc (.pos (.done (.val w))) => hsnd w
  | .foc (.neg (.done n)) => NegNeu.eta B (.snd n)
  | .foc (.letPos n w) => .foc (.letPos n (hsnd w))
  | .foc (.sat (.mk s w)) => .foc (.sat (.mk s (hsnd w)))
termination_by (objectSize (Object.prod A B), 0, t.size)

/-- Hereditary elimination of the empty type. -/
def habort {Γ : Ctx sig} (C : Object sig.nBases)
    (w : InvTm Γ .never) : InvTm Γ C :=
  match w with
  | .case n t₁ t₂ => .case n (habort C t₁) (habort C t₂)
  | .abort n => .abort n
  | .foc (.pos (.done (.neu n))) => .abort n
  | .foc (.pos (.done (.val w'))) => habort C w'
  | .foc (.neg (.done n)) => .abort n
  | .foc (.letPos n w') => .foc (.letPos n (habort C w'))
  | .foc (.sat (.mk s w')) => .foc (.sat (.mk s (habort C w')))
termination_by (objectSize (Object.never (n := sig.nBases)), 0, w.size)

/-- Hereditary case analysis. -/
def hcase {Γ : Ctx sig} {A B C : Object sig.nBases}
    (s : InvTm Γ (.coprod A B)) (l : InvTm (Γ ▻ A) C) (r : InvTm (Γ ▻ B) C) :
    InvTm Γ C :=
  match s with
  | .case n s₁ s₂ =>
      .case n
        (hcase s₁ (InvTm.rename Rename.skip1 l) (InvTm.rename Rename.skip1 r))
        (hcase s₂ (InvTm.rename Rename.skip1 l) (InvTm.rename Rename.skip1 r))
  | .abort n => .abort n
  | .foc (.pos (.done (.neu n))) => .case n l r
  | .foc (.pos (.done (.inl p))) => hsubstInv l (PosNeu.toInv p)
  | .foc (.pos (.done (.inr p))) => hsubstInv r (PosNeu.toInv p)
  | .foc (.pos (.done (.val w))) => hcase w l r
  | .foc (.neg (.done n)) => .case n l r
  | .foc (.letPos n w) =>
      .foc (.letPos n
        (hcase w (InvTm.rename Rename.skip1 l) (InvTm.rename Rename.skip1 r)))
  | .foc (.sat (.mk sc w)) => .foc (.sat (.mk sc (hcase w l r)))
termination_by (objectSize (Object.coprod A B), 0, s.size)

/-- Hereditary substitution into an invertible term. -/
def hsubstInv {Γ : Ctx sig} {A C : Object sig.nBases}
    (t : InvTm (Γ ▻ A) C) (v : InvTm Γ A) : InvTm Γ C :=
  match t with
  | .unit => .unit
  | .pair t₁ t₂ => .pair (hsubstInv t₁ v) (hsubstInv t₂ v)
  | .lam t₁ =>
      .lam (hsubstInv (InvTm.rename Rename.exchange t₁) (InvTm.weaken v))
  | .case n t₁ t₂ =>
      match hsubstNeu n v with
      | .neu n' =>
          .case n'
            (hsubstInv (InvTm.rename Rename.exchange t₁) (InvTm.weaken v))
            (hsubstInv (InvTm.rename Rename.exchange t₂) (InvTm.weaken v))
      | .here w _ =>
          hcase w
            (hsubstInv (InvTm.rename Rename.exchange t₁) (InvTm.weaken v))
            (hsubstInv (InvTm.rename Rename.exchange t₂) (InvTm.weaken v))
      | .val w _ =>
          hcase w
            (hsubstInv (InvTm.rename Rename.exchange t₁) (InvTm.weaken v))
            (hsubstInv (InvTm.rename Rename.exchange t₂) (InvTm.weaken v))
  | .abort n =>
      match hsubstNeu n v with
      | .neu n' => .abort n'
      | .here w _ => habort C w
      | .val w _ => habort C w
  | .foc (.pos (.done p)) => hsubstPos p v
  | .foc (.neg (.done n)) =>
      match hsubstNeu n v with
      | .neu n' => NegNeu.eta C n'
      | .here w _ => w
      | .val w _ => w
  | .foc (.letPos (P := P) n t₁) =>
      match hsubstNeu n v with
      | .neu n' =>
          .foc (.letPos n'
            (hsubstInv (InvTm.rename Rename.exchange t₁) (InvTm.weaken v)))
      | .here _ h =>
          -- The let binds the cut variable itself: contract the two copies.
          hsubstInv (InvTm.rename (Rename.diagEq h) t₁) v
      | .val w _ =>
          hsubstInv
            (hsubstInv (InvTm.rename Rename.exchange t₁) (InvTm.weaken v)) w
  | .foc (.sat (.mk s t₁)) => .foc (.sat (.mk s (hsubstInv t₁ v)))
termination_by (objectSize A, 1, t.size)
decreasing_by
  all_goals
    first
    | decreasing_tactic
    | (subst_vars; decreasing_tactic)

/-- Hereditary substitution into a positive value. -/
def hsubstPos {Γ : Ctx sig} {A C : Object sig.nBases}
    (p : PosNeu (Γ ▻ A) C) (v : InvTm Γ A) : InvTm Γ C :=
  match p with
  | .neu n =>
      match hsubstNeu n v with
      | .neu n' => NegNeu.eta C n'
      | .here w _ => w
      | .val w _ => w
  | .inl (B := B₁) q => InvTm.hinl B₁ (hsubstPos q v)
  | .inr (A := A₁) q => InvTm.hinr A₁ (hsubstPos q v)
  | .val t => hsubstInv t v
termination_by (objectSize A, 1, p.size)

/-- Hereditary substitution into a neutral spine. -/
def hsubstNeu {Γ : Ctx sig} {A C : Object sig.nBases}
    (n : NegNeu (Γ ▻ A) C) (v : InvTm Γ A) : HSubst Γ A C :=
  match n with
  | .var .here => .here v rfl
  | .var (.there x) => .neu (.var x)
  | .app (A := A₁) (B := B₁) m u =>
      match hsubstNeu m v with
      | .neu m' => .neu (.app m' (hsubstInv u v))
      | .here w h =>
          .val (happ w (hsubstInv u v)) (by subst h; simp; omega)
      | .val w hlt =>
          .val (happ w (hsubstInv u v)) (by simp at hlt; omega)
  | .fst (A := A₁) (B := B₁) m =>
      match hsubstNeu m v with
      | .neu m' => .neu (.fst m')
      | .here w h => .val (hfst w) (by subst h; simp; omega)
      | .val w hlt => .val (hfst w) (by simp at hlt; omega)
  | .snd (A := A₁) (B := B₁) m =>
      match hsubstNeu m v with
      | .neu m' => .neu (.snd m')
      | .here w h => .val (hsnd w) (by subst h; simp; omega)
      | .val w hlt => .val (hsnd w) (by simp at hlt; omega)
termination_by (objectSize A, 1, n.size)
decreasing_by
  all_goals
    first
    | decreasing_tactic
    | (subst_vars; decreasing_tactic)

end

/-! ### Phase legality of the output

Every hereditary operation maps well-focused inputs to well-focused outputs,
so focusing lands in the legal fragment (`WellInv`) by construction.
-/

/-! #### Renaming preserves legality -/

mutual
theorem wellInv_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) {t : InvTm Γ A} (h : WellInv t) :
    WellInv (InvTm.rename ρ t) :=
  match t, h with
  | .unit, _ => .unit
  | .pair _ _, .pair ht hu => .pair (wellInv_rename ρ ht) (wellInv_rename ρ hu)
  | .lam _, .lam ht => .lam (wellInv_rename (Rename.ext ρ) ht)
  | .case _ _ _, .case hn ht hu =>
      .case (wellNeg_rename ρ hn) (wellInv_rename (Rename.ext ρ) ht)
        (wellInv_rename (Rename.ext ρ) hu)
  | .abort _, .abort hn => .abort (wellNeg_rename ρ hn)
  | .foc _, .foc hf => .foc (wellFoc_rename ρ hf)
termination_by t.size

theorem wellFoc_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) {f : FocTm Γ A} (h : WellFoc f) :
    WellFoc (FocTm.rename ρ f) :=
  match f, h with
  | .pos (.done _), .pos hpol hp => .pos hpol (wellPos_rename ρ hp)
  | .neg (.done _), .neg hpol hn => .neg hpol (wellNeg_rename ρ hn)
  | .letPos _ _, .letPos hpol hn ht =>
      .letPos hpol (wellNeg_rename ρ hn) (wellInv_rename (Rename.ext ρ) ht)
  | .sat (.mk _ _), .sat ht => .sat (wellInv_rename ρ ht)
termination_by f.size

theorem wellPos_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) {p : PosNeu Γ A} (h : WellPos p) :
    WellPos (PosNeu.rename ρ p) :=
  match p, h with
  | .neu _, .neu hpol hn => .neu hpol (wellNeg_rename ρ hn)
  | .inl _, .inl hp => .inl (wellPos_rename ρ hp)
  | .inr _, .inr hp => .inr (wellPos_rename ρ hp)
  | .val _, .val hpol ht => .val hpol (wellInv_rename ρ ht)
termination_by p.size

theorem wellNeg_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) {n : NegNeu Γ A} (h : WellNeg n) :
    WellNeg (NegNeu.rename ρ n) :=
  match n, h with
  | .var _, _ => .var
  | .app _ _, .app hn ht => .app (wellNeg_rename ρ hn) (wellInv_rename ρ ht)
  | .fst _, .fst hn => .fst (wellNeg_rename ρ hn)
  | .snd _, .snd hn => .snd (wellNeg_rename ρ hn)
termination_by n.size
end

theorem wellInv_weaken {Γ : Ctx sig} {A B : Object sig.nBases} {t : InvTm Γ A}
    (h : WellInv t) : WellInv (InvTm.weaken (B := B) t) :=
  wellInv_rename _ h

/-! #### Identity expansion and injections -/

theorem wellInv_eta :
    ∀ (A : Object sig.nBases) {Γ : Ctx sig} {n : NegNeu Γ A}, WellNeg n →
      WellInv (NegNeu.eta A n) := by
  intro A
  induction A with
  | base q => intro Γ n hn; exact .foc (.pos rfl (.neu rfl hn))
  | unit => intro Γ n _; exact .unit
  | never => intro Γ n hn; exact .abort hn
  | prod A B ihA ihB => intro Γ n hn; exact .pair (ihA (.fst hn)) (ihB (.snd hn))
  | coprod A B _ _ => intro Γ n hn; exact .foc (.pos rfl (.neu rfl hn))
  | exp A B ihA ihB =>
      intro Γ n hn
      exact .lam (ihB (.app (wellNeg_rename _ hn) (ihA .var)))

theorem wellInv_toInv {Γ : Ctx sig} {A : Object sig.nBases} {p : PosNeu Γ A}
    (h : WellPos p) : WellInv p.toInv := by
  cases h with
  | neu _ hn => exact wellInv_eta _ hn
  | inl hp => exact .foc (.pos rfl (.inl hp))
  | inr hp => exact .foc (.pos rfl (.inr hp))
  | val _ ht => exact ht

theorem wellInv_hinl {Γ : Ctx sig} {A : Object sig.nBases}
    (B : Object sig.nBases) {t : InvTm Γ A} (h : WellInv t) :
    WellInv (InvTm.hinl B t) := by
  induction t using InvTm.hinl.induct generalizing B with
  | case1 _ _ _ _ n t u iht ihu =>
      cases h with
      | case hn ht hu => exact .case hn (iht B ht) (ihu B hu)
  | case2 => cases h with | abort hn => exact .abort hn
  | case3 _ _ _ n t iht =>
      cases h with
      | foc hf =>
          cases hf with
          | letPos hpol hn ht => exact .foc (.letPos hpol hn (iht B ht))
  | case4 _ _ s t iht =>
      cases h with
      | foc hf => cases hf with | sat ht => exact .foc (.sat (iht B ht))
  | case5 _ _ p =>
      cases h with
      | foc hf => cases hf with | pos _ hp => exact .foc (.pos rfl (.inl hp))
  | case6 _ _ n =>
      cases h with
      | foc hf =>
          cases hf with
          | neg hpol hn =>
              exact .foc (.pos rfl (.inl (.val hpol (wellInv_eta _ hn))))
  | case7 => exact .foc (.pos rfl (.inl (.val rfl .unit)))
  | case8 _ _ _ t u =>
      cases h with
      | pair ht hu => exact .foc (.pos rfl (.inl (.val rfl (.pair ht hu))))
  | case9 _ _ _ t =>
      cases h with
      | lam ht => exact .foc (.pos rfl (.inl (.val rfl (.lam ht))))

theorem wellInv_hinr {Γ : Ctx sig} {B : Object sig.nBases}
    (A : Object sig.nBases) {t : InvTm Γ B} (h : WellInv t) :
    WellInv (InvTm.hinr A t) := by
  induction t using InvTm.hinr.induct generalizing A with
  | case1 _ _ _ _ n t u iht ihu =>
      cases h with
      | case hn ht hu => exact .case hn (iht A ht) (ihu A hu)
  | case2 => cases h with | abort hn => exact .abort hn
  | case3 _ _ _ n t iht =>
      cases h with
      | foc hf =>
          cases hf with
          | letPos hpol hn ht => exact .foc (.letPos hpol hn (iht A ht))
  | case4 _ _ s t iht =>
      cases h with
      | foc hf => cases hf with | sat ht => exact .foc (.sat (iht A ht))
  | case5 _ _ p =>
      cases h with
      | foc hf => cases hf with | pos _ hp => exact .foc (.pos rfl (.inr hp))
  | case6 _ _ n =>
      cases h with
      | foc hf =>
          cases hf with
          | neg hpol hn =>
              exact .foc (.pos rfl (.inr (.val hpol (wellInv_eta _ hn))))
  | case7 => exact .foc (.pos rfl (.inr (.val rfl .unit)))
  | case8 _ _ _ t u =>
      cases h with
      | pair ht hu => exact .foc (.pos rfl (.inr (.val rfl (.pair ht hu))))
  | case9 _ _ _ t =>
      cases h with
      | lam ht => exact .foc (.pos rfl (.inr (.val rfl (.lam ht))))

/-- The η-expanded injections are legal branches at any summand polarity. -/
theorem wellInv_etaInl {Γ : Ctx sig} (A B : Object sig.nBases) :
    WellInv (InvTm.etaInl (Γ := Γ) A B) :=
  wellInv_hinl B (wellInv_eta A .var)

theorem wellInv_etaInr {Γ : Ctx sig} (A B : Object sig.nBases) :
    WellInv (InvTm.etaInr (Γ := Γ) A B) :=
  wellInv_hinr A (wellInv_eta B .var)

/-! #### The hereditary operations -/

/-- Legality of a spine-substitution result, by case. -/
def WellHSubst {Γ : Ctx sig} {A C : Object sig.nBases} : HSubst Γ A C → Prop
  | .neu n => WellNeg n
  | .here w _ => WellInv w
  | .val w _ => WellInv w

mutual

theorem wellInv_happ {Γ : Ctx sig} {A B : Object sig.nBases}
    {f : InvTm Γ (.exp A B)} {u : InvTm Γ A}
    (hf : WellInv f) (hu : WellInv u) : WellInv (happ f u) := by
  match f, hf with
  | .lam _, .lam hb => simpa [happ] using wellInv_hsubstInv hb hu
  | .case _ _ _, .case hn h₁ h₂ =>
      simp only [happ]
      exact .case hn (wellInv_happ h₁ (wellInv_weaken hu))
        (wellInv_happ h₂ (wellInv_weaken hu))
  | .abort _, .abort hn => simpa [happ] using WellInv.abort hn
  | .foc (.pos (.done (.neu _))), .foc (.pos hpol _) => simp at hpol
  | .foc (.pos (.done (.val _))), .foc (.pos hpol _) => simp at hpol
  | .foc (.neg (.done _)), .foc (.neg _ hn) =>
      simp only [happ]; exact wellInv_eta _ (.app hn hu)
  | .foc (.letPos _ _), .foc (.letPos hpol hn hw) =>
      simp only [happ]
      exact .foc (.letPos hpol hn (wellInv_happ hw (wellInv_weaken hu)))
  | .foc (.sat (.mk _ _)), .foc (.sat hw) =>
      simp only [happ]; exact .foc (.sat (wellInv_happ hw hu))
termination_by (objectSize (Object.exp A B), 0, f.size)

theorem wellInv_hfst {Γ : Ctx sig} {A B : Object sig.nBases}
    {t : InvTm Γ (.prod A B)} (h : WellInv t) : WellInv (hfst t) := by
  match t, h with
  | .pair _ _, .pair h₁ _ => simpa [hfst] using h₁
  | .case _ _ _, .case hn h₁ h₂ =>
      simp only [hfst]; exact .case hn (wellInv_hfst h₁) (wellInv_hfst h₂)
  | .abort _, .abort hn => simpa [hfst] using WellInv.abort hn
  | .foc (.pos (.done (.neu _))), .foc (.pos hpol _) => simp at hpol
  | .foc (.pos (.done (.val _))), .foc (.pos hpol _) => simp at hpol
  | .foc (.neg (.done _)), .foc (.neg _ hn) =>
      simp only [hfst]; exact wellInv_eta _ (.fst hn)
  | .foc (.letPos _ _), .foc (.letPos hpol hn hw) =>
      simp only [hfst]; exact .foc (.letPos hpol hn (wellInv_hfst hw))
  | .foc (.sat (.mk _ _)), .foc (.sat hw) =>
      simp only [hfst]; exact .foc (.sat (wellInv_hfst hw))
termination_by (objectSize (Object.prod A B), 0, t.size)

theorem wellInv_hsnd {Γ : Ctx sig} {A B : Object sig.nBases}
    {t : InvTm Γ (.prod A B)} (h : WellInv t) : WellInv (hsnd t) := by
  match t, h with
  | .pair _ _, .pair _ h₂ => simpa [hsnd] using h₂
  | .case _ _ _, .case hn h₁ h₂ =>
      simp only [hsnd]; exact .case hn (wellInv_hsnd h₁) (wellInv_hsnd h₂)
  | .abort _, .abort hn => simpa [hsnd] using WellInv.abort hn
  | .foc (.pos (.done (.neu _))), .foc (.pos hpol _) => simp at hpol
  | .foc (.pos (.done (.val _))), .foc (.pos hpol _) => simp at hpol
  | .foc (.neg (.done _)), .foc (.neg _ hn) =>
      simp only [hsnd]; exact wellInv_eta _ (.snd hn)
  | .foc (.letPos _ _), .foc (.letPos hpol hn hw) =>
      simp only [hsnd]; exact .foc (.letPos hpol hn (wellInv_hsnd hw))
  | .foc (.sat (.mk _ _)), .foc (.sat hw) =>
      simp only [hsnd]; exact .foc (.sat (wellInv_hsnd hw))
termination_by (objectSize (Object.prod A B), 0, t.size)

theorem wellInv_habort {Γ : Ctx sig} (C : Object sig.nBases)
    {w : InvTm Γ .never} (h : WellInv w) : WellInv (habort C w) := by
  match w, h with
  | .case _ _ _, .case hn h₁ h₂ =>
      simp only [habort]
      exact .case hn (wellInv_habort C h₁) (wellInv_habort C h₂)
  | .abort _, .abort hn => simpa [habort] using WellInv.abort hn
  | .foc (.pos (.done (.neu _))), .foc (.pos _ (.neu _ hn)) =>
      simp only [habort]; exact .abort hn
  | .foc (.pos (.done (.val _))), .foc (.pos _ (.val hpol _)) => simp at hpol
  | .foc (.neg (.done _)), .foc (.neg hpol _) => simp at hpol
  | .foc (.letPos _ _), .foc (.letPos hpol hn hw) =>
      simp only [habort]; exact .foc (.letPos hpol hn (wellInv_habort C hw))
  | .foc (.sat (.mk _ _)), .foc (.sat hw) =>
      simp only [habort]; exact .foc (.sat (wellInv_habort C hw))
termination_by (objectSize (Object.never (n := sig.nBases)), 0, w.size)

theorem wellInv_hcase {Γ : Ctx sig} {A B C : Object sig.nBases}
    {s : InvTm Γ (.coprod A B)} {l : InvTm (Γ ▻ A) C} {r : InvTm (Γ ▻ B) C}
    (hs : WellInv s) (hl : WellInv l) (hr : WellInv r) :
    WellInv (hcase s l r) := by
  match s, hs with
  | .case _ _ _, .case hn h₁ h₂ =>
      simp only [hcase]
      exact .case hn
        (wellInv_hcase h₁ (wellInv_rename _ hl) (wellInv_rename _ hr))
        (wellInv_hcase h₂ (wellInv_rename _ hl) (wellInv_rename _ hr))
  | .abort _, .abort hn => simpa [hcase] using WellInv.abort hn
  | .foc (.pos (.done (.neu _))), .foc (.pos _ (.neu _ hn)) =>
      simp only [hcase]; exact .case hn hl hr
  | .foc (.pos (.done (.inl _))), .foc (.pos _ (.inl hp)) =>
      simp only [hcase]; exact wellInv_hsubstInv hl (wellInv_toInv hp)
  | .foc (.pos (.done (.inr _))), .foc (.pos _ (.inr hp)) =>
      simp only [hcase]; exact wellInv_hsubstInv hr (wellInv_toInv hp)
  | .foc (.pos (.done (.val _))), .foc (.pos _ (.val hpol _)) => simp at hpol
  | .foc (.neg (.done _)), .foc (.neg hpol _) => simp at hpol
  | .foc (.letPos _ _), .foc (.letPos hpol hn hw) =>
      simp only [hcase]
      exact .foc (.letPos hpol hn
        (wellInv_hcase hw (wellInv_rename _ hl) (wellInv_rename _ hr)))
  | .foc (.sat (.mk _ _)), .foc (.sat hw) =>
      simp only [hcase]; exact .foc (.sat (wellInv_hcase hw hl hr))
termination_by (objectSize (Object.coprod A B), 0, s.size)

theorem wellInv_hsubstInv {Γ : Ctx sig} {A C : Object sig.nBases}
    {t : InvTm (Γ ▻ A) C} {v : InvTm Γ A} (ht : WellInv t) (hv : WellInv v) :
    WellInv (hsubstInv t v) := by
  match t, ht with
  | .unit, _ => simpa [hsubstInv] using WellInv.unit
  | .pair _ _, .pair h₁ h₂ =>
      simp only [hsubstInv]
      exact .pair (wellInv_hsubstInv h₁ hv) (wellInv_hsubstInv h₂ hv)
  | .lam _, .lam hb =>
      simp only [hsubstInv]
      exact .lam (wellInv_hsubstInv (wellInv_rename _ hb) (wellInv_weaken hv))
  | .case n _ _, .case hn h₁ h₂ =>
      simp only [hsubstInv]
      have hres := wellHSubst_hsubstNeu hn hv
      match hsubstNeu n v, hres with
      | .neu _, hn' =>
          exact .case hn'
            (wellInv_hsubstInv (wellInv_rename _ h₁) (wellInv_weaken hv))
            (wellInv_hsubstInv (wellInv_rename _ h₂) (wellInv_weaken hv))
      | .here _ _, hw =>
          exact wellInv_hcase hw
            (wellInv_hsubstInv (wellInv_rename _ h₁) (wellInv_weaken hv))
            (wellInv_hsubstInv (wellInv_rename _ h₂) (wellInv_weaken hv))
      | .val _ _, hw =>
          exact wellInv_hcase hw
            (wellInv_hsubstInv (wellInv_rename _ h₁) (wellInv_weaken hv))
            (wellInv_hsubstInv (wellInv_rename _ h₂) (wellInv_weaken hv))
  | .abort n, .abort hn =>
      simp only [hsubstInv]
      have hres := wellHSubst_hsubstNeu hn hv
      match hsubstNeu n v, hres with
      | .neu _, hn' => exact .abort hn'
      | .here _ _, hw => exact wellInv_habort C hw
      | .val _ _, hw => exact wellInv_habort C hw
  | .foc (.pos (.done _)), .foc (.pos _ hp) =>
      simp only [hsubstInv]; exact wellInv_hsubstPos hp hv
  | .foc (.neg (.done n)), .foc (.neg _ hn) =>
      simp only [hsubstInv]
      have hres := wellHSubst_hsubstNeu hn hv
      match hsubstNeu n v, hres with
      | .neu _, hn' => exact wellInv_eta _ hn'
      | .here _ _, hw => exact hw
      | .val _ _, hw => exact hw
  | .foc (.letPos n _), .foc (.letPos hpol hn hb) =>
      simp only [hsubstInv]
      have hres := wellHSubst_hsubstNeu hn hv
      match hsubstNeu n v, hres with
      | .neu _, hn' =>
          exact .foc (.letPos hpol hn'
            (wellInv_hsubstInv (wellInv_rename _ hb) (wellInv_weaken hv)))
      | .here _ _, _ => exact wellInv_hsubstInv (wellInv_rename _ hb) hv
      | .val _ _, hw =>
          exact wellInv_hsubstInv
            (wellInv_hsubstInv (wellInv_rename _ hb) (wellInv_weaken hv)) hw
  | .foc (.sat (.mk _ _)), .foc (.sat hb) =>
      simp only [hsubstInv]; exact .foc (.sat (wellInv_hsubstInv hb hv))
termination_by (objectSize A, 1, t.size)
decreasing_by
  all_goals
    first
    | decreasing_tactic
    | (subst_vars; decreasing_tactic)

theorem wellInv_hsubstPos {Γ : Ctx sig} {A C : Object sig.nBases}
    {p : PosNeu (Γ ▻ A) C} {v : InvTm Γ A} (hp : WellPos p) (hv : WellInv v) :
    WellInv (hsubstPos p v) := by
  match p, hp with
  | .neu n, .neu _ hn =>
      simp only [hsubstPos]
      have hres := wellHSubst_hsubstNeu hn hv
      match hsubstNeu n v, hres with
      | .neu _, hn' => exact wellInv_eta _ hn'
      | .here _ _, hw => exact hw
      | .val _ _, hw => exact hw
  | .inl _, .inl hq =>
      simp only [hsubstPos]; exact wellInv_hinl _ (wellInv_hsubstPos hq hv)
  | .inr _, .inr hq =>
      simp only [hsubstPos]; exact wellInv_hinr _ (wellInv_hsubstPos hq hv)
  | .val _, .val _ hb =>
      simp only [hsubstPos]; exact wellInv_hsubstInv hb hv
termination_by (objectSize A, 1, p.size)

theorem wellHSubst_hsubstNeu {Γ : Ctx sig} {A C : Object sig.nBases}
    {n : NegNeu (Γ ▻ A) C} {v : InvTm Γ A} (hn : WellNeg n) (hv : WellInv v) :
    WellHSubst (hsubstNeu n v) := by
  match n, hn with
  | .var .here, _ => simpa [hsubstNeu, WellHSubst] using hv
  | .var (.there _), _ => simpa [hsubstNeu, WellHSubst] using WellNeg.var
  | .app m _, .app hm hu =>
      simp only [hsubstNeu]
      have hres := wellHSubst_hsubstNeu hm hv
      match hsubstNeu m v, hres with
      | .neu _, hm' =>
          exact WellNeg.app hm' (wellInv_hsubstInv hu hv)
      | .here _ _, hw => exact wellInv_happ hw (wellInv_hsubstInv hu hv)
      | .val _ _, hw => exact wellInv_happ hw (wellInv_hsubstInv hu hv)
  | .fst m, .fst hm =>
      simp only [hsubstNeu]
      have hres := wellHSubst_hsubstNeu hm hv
      match hsubstNeu m v, hres with
      | .neu _, hm' => exact WellNeg.fst hm'
      | .here _ _, hw => exact wellInv_hfst hw
      | .val _ _, hw => exact wellInv_hfst hw
  | .snd m, .snd hm =>
      simp only [hsubstNeu]
      have hres := wellHSubst_hsubstNeu hm hv
      match hsubstNeu m v, hres with
      | .neu _, hm' => exact WellNeg.snd hm'
      | .here _ _, hw => exact wellInv_hsnd hw
      | .val _ _, hw => exact wellInv_hsnd hw
termination_by (objectSize A, 1, n.size)
decreasing_by
  all_goals
    first
    | decreasing_tactic
    | (subst_vars; decreasing_tactic)

end

/-! ### Total focusing -/

/--
Focus an intrinsic term: a total, structurally recursive translation whose
eliminators are the hereditary operations above.
-/
def focusTm {Γ : Ctx sig} {A : Object sig.nBases} : Tm Γ A → InvTm Γ A
  | .var x => NegNeu.eta A (.var x)
  | .unit => .unit
  | .abort t => habort A (focusTm t)
  | .pair t u => .pair (focusTm t) (focusTm u)
  | .fst t => hfst (focusTm t)
  | .snd t => hsnd (focusTm t)
  | .inl (B := B₁) t => InvTm.hinl B₁ (focusTm t)
  | .inr (A := A₁) t => InvTm.hinr A₁ (focusTm t)
  | .case s t u => hcase (focusTm s) (focusTm t) (focusTm u)
  | .lam t => .lam (focusTm t)
  | .app t u => happ (focusTm t) (focusTm u)

/-! ### Focusing lands in the legal fragment -/

/--
Completeness of focusing: every intrinsic term has a focused representative,
and that representative is phase-legal.
-/
theorem wellInv_focusTm {Γ : Ctx sig} {A : Object sig.nBases} (t : Tm Γ A) :
    WellInv (focusTm t) := by
  induction t with
  | var x => exact wellInv_eta _ .var
  | unit => exact .unit
  | abort _ ih => exact wellInv_habort _ ih
  | pair _ _ iht ihu => exact .pair iht ihu
  | fst _ ih => exact wellInv_hfst ih
  | snd _ ih => exact wellInv_hsnd ih
  | inl _ ih => exact wellInv_hinl _ ih
  | inr _ ih => exact wellInv_hinr _ ih
  | «case» _ _ _ ihs iht ihu => exact wellInv_hcase ihs iht ihu
  | lam _ ih => exact .lam ih
  | app _ _ iht ihu => exact wellInv_happ iht ihu

end Equality
end Gimbal
