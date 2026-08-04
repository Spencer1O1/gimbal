/-
  Intrinsically typed nameless STLC for the equality calculus.
  Snoc contexts, typed de Bruijn variables, renaming, and substitution.
  Types are Phase 0 `Object`s (unpolarized).
-/

import Gimbal.Object
import Gimbal.Signature

namespace Gimbal
namespace Equality

/-- Snoc typing context over signature `sig`. -/
inductive Ctx (sig : Signature) : Type where
  | empty : Ctx sig
  | snoc : Ctx sig → Object sig.nBases → Ctx sig

/-- Notation for `Ctx.snoc`. -/
infixl:67 " ▻ " => Ctx.snoc

namespace Ctx

variable {sig : Signature}

def length : Ctx sig → Nat
  | .empty => 0
  | .snoc Γ _ => Γ.length + 1

/-- Build a context by snoc'ing hypotheses oldest-first. -/
def ofList (xs : List (Object sig.nBases)) : Ctx sig :=
  xs.foldl Ctx.snoc .empty

/-- Array variant of `ofList`. -/
def ofHyps (hyps : Array (Object sig.nBases)) : Ctx sig :=
  ofList hyps.toList

theorem ofList_concat_singleton (xs : List (Object sig.nBases))
    (A : Object sig.nBases) :
    ofList (xs ++ [A]) = ofList xs ▻ A := by
  simp [ofList, List.foldl_append, List.foldl]

theorem ofHyps_push (hyps : Array (Object sig.nBases))
    (A : Object sig.nBases) :
    ofHyps (hyps.push A) = ofHyps hyps ▻ A := by
  simp [ofHyps, Array.toList_push, ofList_concat_singleton]

end Ctx

/-- Typed de Bruijn variable: membership of `A` in `Γ`. -/
inductive Var {sig : Signature} : Ctx sig → Object sig.nBases → Type where
  | here {Γ : Ctx sig} {A : Object sig.nBases} : Var (Γ ▻ A) A
  | there {Γ : Ctx sig} {A B : Object sig.nBases} : Var Γ A → Var (Γ ▻ B) A

namespace Ctx

variable {sig : Signature}

/-- Variable counted from the newest binder (`0` = `here`). -/
def varFromEnd : (Γ : Ctx sig) → Nat → Option ((A : Object sig.nBases) × Var Γ A)
  | .empty, _ => none
  | .snoc _ A, 0 => some ⟨A, .here⟩
  | .snoc Γ _, n + 1 =>
      match varFromEnd Γ n with
      | some ⟨B, x⟩ => some ⟨B, .there x⟩
      | none => none

/--
Variable for hypothesis index `i` (0 = oldest) in `ofHyps hyps`.
-/
def varOldest (hyps : Array (Object sig.nBases)) (i : Nat) :
    Option ((A : Object sig.nBases) × Var (ofHyps hyps) A) :=
  if i < hyps.size then
    varFromEnd (ofHyps hyps) (hyps.size - 1 - i)
  else
    none

private theorem varFromEnd_ofList_getLast {sig : Signature}
    (ys : List (Object sig.nBases)) (B : Object sig.nBases) :
    ∃ x, varFromEnd (sig := sig) (ofList (ys ++ [B])) 0 = some ⟨B, x⟩ := by
  rw [ofList_concat_singleton]
  simp [varFromEnd]

private theorem varFromEnd_ofList_succ {sig : Signature}
    (ys : List (Object sig.nBases)) (B : Object sig.nBases) (k : Nat)
    {A : Object sig.nBases} {x : Var (ofList ys) A}
    (h : varFromEnd (sig := sig) (ofList ys) k = some ⟨A, x⟩) :
    ∃ y, varFromEnd (sig := sig) (ofList (ys ++ [B])) (k + 1) = some ⟨A, y⟩ := by
  rw [ofList_concat_singleton]
  simp [varFromEnd, h]

private theorem varFromEnd_ofList_reverse {sig : Signature} :
    ∀ (xs : List (Object sig.nBases)) (k : Nat) {A : Object sig.nBases},
      xs.reverse[k]? = some A →
        ∃ x, varFromEnd (sig := sig) (ofList xs) k = some ⟨A, x⟩
  | [], k, A, h => by simp at h
  | xs, k, A, h => by
      have hne : xs ≠ [] := fun he => by subst he; simp at h
      obtain ⟨ys, B, rfl⟩ : ∃ ys B, xs = ys ++ [B] := by
        obtain ⟨ys, B, hconcat⟩ := (List.eq_nil_or_concat xs).resolve_left hne
        exact ⟨ys, B, by simpa [List.concat_eq_append] using hconcat⟩
      cases k with
      | zero =>
          have hB : A = B := by
            simp [List.reverse_append, List.getElem?_cons_zero] at h
            exact h.symm
          subst hB
          exact varFromEnd_ofList_getLast ys A
      | succ k =>
          simp [List.reverse_append, List.getElem?_cons_succ] at h
          obtain ⟨x, hx⟩ := varFromEnd_ofList_reverse ys k h
          exact varFromEnd_ofList_succ ys B k hx

/-- If `hyps[i]? = some A`, then `varOldest` returns a variable of that type. -/
theorem varOldest_eq_of_getElem? (hyps : Array (Object sig.nBases)) (i : Nat)
    {A : Object sig.nBases} (h : hyps[i]? = some A) :
    ∃ x, varOldest (sig := sig) hyps i = some ⟨A, x⟩ := by
  have hi : i < hyps.size := (Array.getElem?_eq_some_iff.mp h).1
  simp only [varOldest, hi, ↓reduceIte, ofHyps]
  have hlen : hyps.toList.length = hyps.size := Array.length_toList
  have hrev : hyps.toList.reverse[hyps.size - 1 - i]? = some A := by
    have hidx : hyps.size - 1 - i < hyps.toList.length := by
      simp [hlen]; omega
    rw [List.getElem?_reverse hidx]
    have : hyps.toList.length - 1 - (hyps.size - 1 - i) = i := by omega
    rw [this]
    simpa [Array.getElem?_toList] using h
  simpa using varFromEnd_ofList_reverse hyps.toList (hyps.size - 1 - i) hrev

/-- Weaken a variable across one newest binder. -/
def weakenVar {Γ : Ctx sig} {A B : Object sig.nBases}
    (x : Var Γ A) : Var (Γ ▻ B) A :=
  .there x

end Ctx

/-- Intrinsically typed term: `Γ ⊢ A`. -/
inductive Tm {sig : Signature} : Ctx sig → Object sig.nBases → Type where
  | var {Γ A} : Var Γ A → Tm Γ A
  | unit {Γ} : Tm Γ .unit
  | abort {Γ A} : Tm Γ .never → Tm Γ A
  | pair {Γ A B} : Tm Γ A → Tm Γ B → Tm Γ (.prod A B)
  | fst {Γ A B} : Tm Γ (.prod A B) → Tm Γ A
  | snd {Γ A B} : Tm Γ (.prod A B) → Tm Γ B
  | inl {Γ A B} : Tm Γ A → Tm Γ (.coprod A B)
  | inr {Γ A B} : Tm Γ B → Tm Γ (.coprod A B)
  | case {Γ A B C} :
      Tm Γ (.coprod A B) →
      Tm (Γ ▻ A) C →
      Tm (Γ ▻ B) C →
      Tm Γ C
  | lam {Γ A B} : Tm (Γ ▻ A) B → Tm Γ (.exp A B)
  | app {Γ A B} : Tm Γ (.exp A B) → Tm Γ A → Tm Γ B

/-! ### Renaming -/

/-- A renaming maps variables in `Γ` to variables in `Δ`. -/
def Rename (sig : Signature) (Γ Δ : Ctx sig) : Type :=
  ∀ {A : Object sig.nBases}, Var Γ A → Var Δ A

namespace Rename

variable {sig : Signature}

def id {Γ : Ctx sig} : Rename sig Γ Γ :=
  fun x => x

/-- Extend a renaming under one binder. -/
def ext {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) : Rename sig (Γ ▻ A) (Δ ▻ A)
  | _, .here => .here
  | _, .there x => .there (ρ x)

/-- Weaken into an extended context. -/
def weaken {Γ : Ctx sig} {A : Object sig.nBases} : Rename sig Γ (Γ ▻ A) :=
  fun x => .there x

/-- Exchange the two newest binders: `(Γ ▻ A ▻ B) → (Γ ▻ B ▻ A)`. -/
def exchange {Γ : Ctx sig} {A B : Object sig.nBases} :
    Rename sig (Γ ▻ A ▻ B) (Γ ▻ B ▻ A)
  | _, .here => .there .here
  | _, .there .here => .here
  | _, .there (.there x) => .there (.there x)

/-- Contract two copies of the same newest binder: `(Γ ▻ A ▻ A) → (Γ ▻ A)`. -/
def diag {Γ : Ctx sig} {A : Object sig.nBases} :
    Rename sig (Γ ▻ A ▻ A) (Γ ▻ A)
  | _, .here => .here
  | _, .there .here => .here
  | _, .there (.there x) => .there x

/-- Insert one binder underneath the newest one: `(Γ ▻ A) → (Γ ▻ B ▻ A)`. -/
def skip1 {Γ : Ctx sig} {A B : Object sig.nBases} :
    Rename sig (Γ ▻ A) (Γ ▻ B ▻ A)
  | _, .here => .here
  | _, .there x => .there (.there x)

end Rename

/-- Apply a renaming to a term. -/
def rename {sig : Signature} {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) : Tm Γ A → Tm Δ A
  | .var x => .var (ρ x)
  | .unit => .unit
  | .abort t => .abort (rename ρ t)
  | .pair t u => .pair (rename ρ t) (rename ρ u)
  | .fst t => .fst (rename ρ t)
  | .snd t => .snd (rename ρ t)
  | .inl t => .inl (rename ρ t)
  | .inr t => .inr (rename ρ t)
  | .case s t u =>
      .case (rename ρ s) (rename (Rename.ext ρ) t) (rename (Rename.ext ρ) u)
  | .lam t => .lam (rename (Rename.ext ρ) t)
  | .app t u => .app (rename ρ t) (rename ρ u)

/-- Weaken a term by one binder. -/
def weakenTerm {sig : Signature} {Γ : Ctx sig} {A B : Object sig.nBases}
    (t : Tm Γ B) : Tm (Γ ▻ A) B :=
  rename Rename.weaken t

/-! ### Substitution -/

/-- A substitution maps variables in `Γ` to terms in `Δ`. -/
def Subst (sig : Signature) (Γ Δ : Ctx sig) : Type :=
  ∀ {A : Object sig.nBases}, Var Γ A → Tm Δ A

namespace Subst

variable {sig : Signature}

def ids {Γ : Ctx sig} : Subst sig Γ Γ :=
  fun x => .var x

/-- Extend a substitution under one binder. -/
def exts {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (σ : Subst sig Γ Δ) : Subst sig (Γ ▻ A) (Δ ▻ A)
  | _, .here => .var .here
  | _, .there x => weakenTerm (σ x)

/-- Substitution that replaces only the most recently bound variable. -/
def single {Γ : Ctx sig} {A : Object sig.nBases}
    (n : Tm Γ A) : Subst sig (Γ ▻ A) Γ
  | _, .here => n
  | _, .there x => .var x

end Subst

/-- Apply a parallel substitution to a term. -/
def subst {sig : Signature} {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (σ : Subst sig Γ Δ) : Tm Γ A → Tm Δ A
  | .var x => σ x
  | .unit => .unit
  | .abort t => .abort (subst σ t)
  | .pair t u => .pair (subst σ t) (subst σ u)
  | .fst t => .fst (subst σ t)
  | .snd t => .snd (subst σ t)
  | .inl t => .inl (subst σ t)
  | .inr t => .inr (subst σ t)
  | .case s t u =>
      .case (subst σ s) (subst (Subst.exts σ) t) (subst (Subst.exts σ) u)
  | .lam t => .lam (subst (Subst.exts σ) t)
  | .app t u => .app (subst σ t) (subst σ u)

/-- Substitute `n` for the most recently bound variable in `t`. -/
def subst0 {sig : Signature} {Γ : Ctx sig} {A B : Object sig.nBases}
    (t : Tm (Γ ▻ A) B) (n : Tm Γ A) : Tm Γ B :=
  subst (Subst.single n) t

/-! ### Generator context prefix -/

/-- Arrow type of a signature generator. -/
def genType (sig : Signature) (q : Fin sig.nGens) : Object sig.nBases :=
  .exp (sig.gen q).source (sig.gen q).target

/--
Prefix of the generator telescope after snoc'ing generators `0 .. i-1`
(`0` outermost / largest de Bruijn index).
-/
def genCtxPrefix (sig : Signature) : (i : Nat) → i ≤ sig.nGens → Ctx sig
  | 0, _ => .empty
  | i + 1, hi =>
      have hi' : i ≤ sig.nGens := Nat.le_of_succ_le hi
      have i_lt : i < sig.nGens := Nat.lt_of_succ_le hi
      genCtxPrefix sig i hi' ▻ genType sig ⟨i, i_lt⟩

/-- Variable for generator `q` in `genCtxPrefix i`. -/
def genVarPrefix (sig : Signature) :
    (i : Nat) → (hi : i ≤ sig.nGens) →
    (q : Fin i) → Var (genCtxPrefix sig i hi)
      (genType sig ⟨q.val, Nat.lt_of_lt_of_le q.isLt hi⟩)
  | 0, _, q => nomatch q
  | i + 1, hi, q =>
      have hi' : i ≤ sig.nGens := Nat.le_of_succ_le hi
      have i_lt : i < sig.nGens := Nat.lt_of_succ_le hi
      if h : q.val = i then
        have hty : genType sig ⟨q.val, Nat.lt_of_lt_of_le q.isLt hi⟩ =
            genType sig ⟨i, i_lt⟩ := by simp [h]
        hty ▸ Var.here
      else
        have q_lt_i : q.val < i :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ q.isLt) h
        .there (genVarPrefix sig i hi' ⟨q.val, q_lt_i⟩)

/--
Telescope of rigid generator variables, snoc'd in ID order
(`0` outermost / largest de Bruijn index).
-/
structure GenTelescope (sig : Signature) where
  ctx : Ctx sig
  var : (q : Fin sig.nGens) → Var ctx (genType sig q)

/-- Build the generator telescope by snoc'ing generators `0 .. nGens-1`. -/
def genTelescope (sig : Signature) : GenTelescope sig :=
  ⟨genCtxPrefix sig sig.nGens (Nat.le_refl _),
   fun q => genVarPrefix sig sig.nGens (Nat.le_refl _) ⟨q.val, q.isLt⟩⟩

/-- Fixed rigid generator context `Γgen`. -/
def genCtx (sig : Signature) : Ctx sig :=
  genCtxPrefix sig sig.nGens (Nat.le_refl _)

/-- Variable for generator `q` in `Γgen`. -/
def genVar (sig : Signature) (q : Fin sig.nGens) :
    Var (genCtx sig) (genType sig q) :=
  genVarPrefix sig sig.nGens (Nat.le_refl _) ⟨q.val, q.isLt⟩

end Equality
end Gimbal
