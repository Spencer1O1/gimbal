/-
  Opacity of neutral heads under hereditary substitution.

  A neutral spine is headed by a variable. Focusing never reduces or inspects
  that head: it only ever extends the spine, or — when the head is exactly the
  variable being substituted — replaces the whole spine by the substituted
  value. Generator variables are free variables of the translation context, so
  they are never the cut binder, and the results below say their spines survive
  substitution untouched.
-/

import Gimbal.Equality.Hereditary

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- `HeadVar x n` says the neutral spine `n` is headed by the variable `x`. -/
inductive NegNeu.HeadVar {Γ : Ctx sig} {B : Object sig.nBases} (x : Var Γ B) :
    {A : Object sig.nBases} → NegNeu Γ A → Prop where
  | var : NegNeu.HeadVar x (.var x)
  | app {A C : Object sig.nBases} {n : NegNeu Γ (.exp A C)} {t : InvTm Γ A} :
      NegNeu.HeadVar x n → NegNeu.HeadVar x (.app n t)
  | fst {A C : Object sig.nBases} {n : NegNeu Γ (.prod A C)} :
      NegNeu.HeadVar x n → NegNeu.HeadVar x (.fst n)
  | snd {A C : Object sig.nBases} {n : NegNeu Γ (.prod A C)} :
      NegNeu.HeadVar x n → NegNeu.HeadVar x (.snd n)

/-- Every neutral spine has a head variable. -/
theorem NegNeu.headVar_exists {Γ : Ctx sig} {A : Object sig.nBases} :
    (n : NegNeu Γ A) → ∃ (B : Object sig.nBases) (x : Var Γ B), n.HeadVar x
  | .var x => ⟨_, x, .var⟩
  | .app m _ => by
      obtain ⟨B, x, h⟩ := NegNeu.headVar_exists m; exact ⟨B, x, .app h⟩
  | .fst m => by
      obtain ⟨B, x, h⟩ := NegNeu.headVar_exists m; exact ⟨B, x, .fst h⟩
  | .snd m => by
      obtain ⟨B, x, h⟩ := NegNeu.headVar_exists m; exact ⟨B, x, .snd h⟩
termination_by n => n.size
decreasing_by all_goals decreasing_trivial

/-!
### The head is never reduced

Substituting for the newest binder in a spine headed by an *older* variable
never consults the substituted value at the head: the result is still a
neutral, headed by the same variable.
-/

theorem hsubstNeu_opaque {Γ : Ctx sig} {A C B : Object sig.nBases}
    {x : Var Γ B} {n : NegNeu (Γ ▻ A) C} (h : n.HeadVar (.there x))
    (v : InvTm Γ A) :
    ∃ n' : NegNeu Γ C, hsubstNeu n v = .neu n' ∧ n'.HeadVar x := by
  induction h with
  | var => exact ⟨.var x, by rw [hsubstNeu], .var⟩
  | @app A₁ C₁ m t hm ih =>
      obtain ⟨m', hm', hhead⟩ := ih
      refine ⟨.app m' (hsubstInv t v), ?_, .app hhead⟩
      rw [hsubstNeu, hm']
  | @fst A₁ C₁ m hm ih =>
      obtain ⟨m', hm', hhead⟩ := ih
      refine ⟨.fst m', ?_, .fst hhead⟩
      rw [hsubstNeu, hm']
  | @snd A₁ C₁ m hm ih =>
      obtain ⟨m', hm', hhead⟩ := ih
      refine ⟨.snd m', ?_, .snd hhead⟩
      rw [hsubstNeu, hm']

/-- Generator variables are free, so their spines are opaque to substitution. -/
theorem hsubstNeu_opaque_genVar {Γ : Ctx sig} {A C : Object sig.nBases}
    {ρ : Rename sig (genCtx sig) Γ} {q : Fin sig.nGens}
    {n : NegNeu (Γ ▻ A) C} (h : n.HeadVar (.there (ρ (genVar sig q))))
    (v : InvTm Γ A) :
    ∃ n' : NegNeu Γ C,
      hsubstNeu n v = .neu n' ∧ n'.HeadVar (ρ (genVar sig q)) :=
  hsubstNeu_opaque h v

/-!
### The head is never inspected

When an eliminator meets a neutral it re-embeds that neutral verbatim, one
spine entry longer. No case of `happ`/`hfst`/`hsnd`/`hcase`/`habort` looks at
the head variable, so a generator head can only ever grow a spine.
-/

@[simp] theorem happ_neu {Γ : Ctx sig} {A B : Object sig.nBases}
    (n : NegNeu Γ (.exp A B)) (u : InvTm Γ A) :
    happ (.foc (.pos (.done (.neu n)))) u = NegNeu.eta B (.app n u) := by
  rw [happ]

@[simp] theorem happ_negNeu {Γ : Ctx sig} {A B : Object sig.nBases}
    (n : NegNeu Γ (.exp A B)) (u : InvTm Γ A) :
    happ (.foc (.neg (.done n))) u = NegNeu.eta B (.app n u) := by
  rw [happ]

@[simp] theorem hfst_neu {Γ : Ctx sig} {A B : Object sig.nBases}
    (n : NegNeu Γ (.prod A B)) :
    hfst (.foc (.pos (.done (.neu n)))) = NegNeu.eta A (.fst n) := by
  rw [hfst]

@[simp] theorem hfst_negNeu {Γ : Ctx sig} {A B : Object sig.nBases}
    (n : NegNeu Γ (.prod A B)) :
    hfst (.foc (.neg (.done n))) = NegNeu.eta A (.fst n) := by
  rw [hfst]

@[simp] theorem hsnd_neu {Γ : Ctx sig} {A B : Object sig.nBases}
    (n : NegNeu Γ (.prod A B)) :
    hsnd (.foc (.pos (.done (.neu n)))) = NegNeu.eta B (.snd n) := by
  rw [hsnd]

@[simp] theorem hsnd_negNeu {Γ : Ctx sig} {A B : Object sig.nBases}
    (n : NegNeu Γ (.prod A B)) :
    hsnd (.foc (.neg (.done n))) = NegNeu.eta B (.snd n) := by
  rw [hsnd]

@[simp] theorem habort_neu {Γ : Ctx sig} (C : Object sig.nBases)
    (n : NegNeu Γ .never) :
    habort C (.foc (.pos (.done (.neu n)))) = .abort n := by
  rw [habort]

@[simp] theorem hcase_neu {Γ : Ctx sig} {A B C : Object sig.nBases}
    (n : NegNeu Γ (.coprod A B)) (l : InvTm (Γ ▻ A) C) (r : InvTm (Γ ▻ B) C) :
    hcase (.foc (.pos (.done (.neu n)))) l r = .case n l r := by
  rw [hcase]

/-- A variable focuses to its own identity expansion: no head is contracted. -/
@[simp] theorem focusTm_var {Γ : Ctx sig} {A : Object sig.nBases} (x : Var Γ A) :
    focusTm (.var x) = NegNeu.eta A (.var x) := rfl

end Equality
end Gimbal
