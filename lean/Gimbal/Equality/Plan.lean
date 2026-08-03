/-
  Saturation plans — the proof-facing saturation calculus (Milestone 8E).

  A `SatPlan` is an intrinsically typed, dependency-ordered tree of
  observations. Because each node's continuation is indexed by the context the
  node itself extends, "every scheduled observation is well-typed and in scope"
  is discharged by construction rather than by an executable invariant check.

  Applying a plan is total: structural recursion on the plan, no fuel, no
  failure branch. Each node is justified by one equational law of the theory:

  * `atom` is strong positive cut — `letPos` plus typed neutral abstraction,
    whose erasure is *unchanged* (`erase_letPos_abstr`);
  * `sum` is a case split whose branches do not yet use the observation, and is
    justified by sum η (`TmEq.case_weaken_self`);
  * `absurd` is the canonical collapse in an inconsistent context, justified by
    strictness of the initial object (`TmEq.of_never`).
-/

import Gimbal.Equality.Abstract

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Plans -/

/--
An ordered saturation plan. Every constructor extends the context it schedules
into, so a plan cannot mention a neutral that is out of scope at the point the
observation is applied.
-/
inductive SatPlan : Ctx sig → Type where
  /-- No further observations in this branch. -/
  | done {Γ} : SatPlan Γ
  /-- The context is inconsistent; collapse through the discovered `0` proof. -/
  | absurd {Γ} (n : NegNeu Γ .never) : SatPlan Γ
  /-- Strong positive cut on a non-sum positive observation. -/
  | atom {Γ P} (n : NegNeu Γ P) (rest : SatPlan (Γ ▻ P)) : SatPlan Γ
  /-- Case split on a coproduct observation. -/
  | sum {Γ L R} (n : NegNeu Γ (.coprod L R))
      (l : SatPlan (Γ ▻ L)) (r : SatPlan (Γ ▻ R)) : SatPlan Γ

/-- Number of observations in a plan (both branches of a split are counted). -/
def SatPlan.size {Γ : Ctx sig} : SatPlan Γ → Nat
  | .done => 0
  | .absurd _ => 1
  | .atom _ rest => rest.size + 1
  | .sum _ l r => l.size + r.size + 1

/-- Apply a plan to a continuation. Total: no fuel, no failure. -/
def SatPlan.apply {Γ : Ctx sig} {A : Object sig.nBases} :
    SatPlan Γ → InvTm Γ A → InvTm Γ A
  | .done, t => t
  | .absurd n, _ => .abort n
  | .atom n rest, t =>
      .foc (.letPos n
        (rest.apply (InvTm.abstr .here (NegNeu.weaken n) (InvTm.weaken t))))
  | .sum n l r, t =>
      .case n (l.apply (InvTm.weaken t)) (r.apply (InvTm.weaken t))

/-! ### Admissibility

A plan is admissible when every scheduled neutral is a legal focused spine and
every atom observation really is at a positive type. Scope is not part of the
predicate: it is already forced by the indexing.
-/

inductive WellPlan : {Γ : Ctx sig} → SatPlan Γ → Prop where
  | done {Γ} : WellPlan (.done (Γ := Γ))
  | absurd {Γ} {n : NegNeu Γ .never} : WellNeg n → WellPlan (.absurd n)
  | atom {Γ P} {n : NegNeu Γ P} {rest : SatPlan (Γ ▻ P)} :
      objectPolarity P = .pos → WellNeg n → WellPlan rest →
      WellPlan (.atom n rest)
  | sum {Γ L R} {n : NegNeu Γ (.coprod L R)}
      {l : SatPlan (Γ ▻ L)} {r : SatPlan (Γ ▻ R)} :
      WellNeg n → WellPlan l → WellPlan r → WellPlan (.sum n l r)

/-! ### Applying an admissible plan returns well-focused output -/

theorem SatPlan.wellInv_apply {Γ : Ctx sig} :
    ∀ {pl : SatPlan Γ}, WellPlan pl →
      ∀ {A : Object sig.nBases} {t : InvTm Γ A}, WellInv t →
        WellInv (pl.apply t)
  | .done, _, _, _, ht => ht
  | .absurd _, .absurd hn, _, _, _ => .abort hn
  | .atom _ rest, .atom hpol hn hrest, _, _, ht =>
      .foc (.letPos hpol hn
        (SatPlan.wellInv_apply (pl := rest) hrest
          (wellInv_abstr _ _ (wellInv_rename Rename.weaken ht))))
  | .sum _ l r, .sum hn hl hr, _, _, ht =>
      .case hn
        (SatPlan.wellInv_apply (pl := l) hl (wellInv_rename Rename.weaken ht))
        (SatPlan.wellInv_apply (pl := r) hr (wellInv_rename Rename.weaken ht))

/-! ### Applying a plan preserves meaning -/

theorem SatPlan.tmEq_apply {Γ : Ctx sig} :
    ∀ (pl : SatPlan Γ) {A : Object sig.nBases} (t : InvTm Γ A),
      TmEq (pl.apply t).erase t.erase
  | .done, _, t => .refl t.erase
  | .absurd n, _, t => TmEq.of_never n.erase _ _
  | .atom n rest, _, t => by
      have ih := SatPlan.tmEq_apply rest
        (InvTm.abstr (P := _) .here (NegNeu.weaken n) (InvTm.weaken t))
      show TmEq (subst0 _ n.erase) t.erase
      refine .trans (TmEq.subst0_congr ih (.refl n.erase)) ?_
      exact .of_eq (erase_letPos_abstr n t)
  | .sum n l r, _, t => by
      have ihl := SatPlan.tmEq_apply l (InvTm.weaken (B := _) t)
      have ihr := SatPlan.tmEq_apply r (InvTm.weaken (B := _) t)
      rw [InvTm.erase_weaken] at ihl ihr
      refine .trans (TmEq.case (.refl n.erase) ihl ihr) ?_
      exact TmEq.case_weaken_self n.erase t.erase

/-- Interpretation form of the preservation theorem. -/
theorem SatPlan.interpret_apply {Γ : Ctx sig} {A : Object sig.nBases}
    (pl : SatPlan Γ) (t : InvTm Γ A) {X : Object sig.nBases} (ρ : Env X Γ) :
    IntrinsicDefEq (interpret ρ (pl.apply t).erase) (interpret ρ t.erase) :=
  (pl.tmEq_apply t).intrinsicDefEq ρ

/-! ### Renaming plans -/

def SatPlan.rename {Γ Δ : Ctx sig} (ρ : Rename sig Γ Δ) : SatPlan Γ → SatPlan Δ
  | .done => .done
  | .absurd n => .absurd (NegNeu.rename ρ n)
  | .atom n rest => .atom (NegNeu.rename ρ n) (rest.rename (Rename.ext ρ))
  | .sum n l r =>
      .sum (NegNeu.rename ρ n) (l.rename (Rename.ext ρ)) (r.rename (Rename.ext ρ))

theorem SatPlan.wellPlan_rename {Γ Δ : Ctx sig} (ρ : Rename sig Γ Δ) :
    ∀ {pl : SatPlan Γ}, WellPlan pl → WellPlan (pl.rename ρ)
  | .done, _ => .done
  | .absurd _, .absurd hn => .absurd (wellNeg_rename ρ hn)
  | .atom _ rest, .atom hpol hn hrest =>
      .atom hpol (wellNeg_rename ρ hn)
        (SatPlan.wellPlan_rename (pl := rest) (Rename.ext ρ) hrest)
  | .sum _ l r, .sum hn hl hr =>
      .sum (wellNeg_rename ρ hn)
        (SatPlan.wellPlan_rename (pl := l) (Rename.ext ρ) hl)
        (SatPlan.wellPlan_rename (pl := r) (Rename.ext ρ) hr)

/-! ### Extending a plan

`p.append q` schedules everything in `p`, then everything in `q` at every leaf
of `p`. This is the "extend a valid schedule" operation: admissibility is
preserved, and so is meaning (the latter for free, since *every* plan preserves
meaning).
-/

def SatPlan.append {Γ : Ctx sig} : SatPlan Γ → SatPlan Γ → SatPlan Γ
  | .done, q => q
  | .absurd n, _ => .absurd n
  | .atom n rest, q => .atom n (rest.append (q.rename Rename.weaken))
  | .sum n l r, q =>
      .sum n (l.append (q.rename Rename.weaken)) (r.append (q.rename Rename.weaken))

/-- Extending an admissible plan by an admissible plan stays admissible. -/
theorem SatPlan.wellPlan_append {Γ : Ctx sig} :
    ∀ {p : SatPlan Γ}, WellPlan p → ∀ {q : SatPlan Γ}, WellPlan q →
      WellPlan (p.append q)
  | .done, _, _, hq => hq
  | .absurd _, .absurd hn, _, _ => .absurd hn
  | .atom _ rest, .atom hpol hn hrest, _, hq =>
      .atom hpol hn
        (SatPlan.wellPlan_append (p := rest) hrest
          (SatPlan.wellPlan_rename Rename.weaken hq))
  | .sum _ l r, .sum hn hl hr, _, hq =>
      .sum hn
        (SatPlan.wellPlan_append (p := l) hl
          (SatPlan.wellPlan_rename Rename.weaken hq))
        (SatPlan.wellPlan_append (p := r) hr
          (SatPlan.wellPlan_rename Rename.weaken hq))

/-- Extension never changes the meaning of the saturated form. -/
theorem SatPlan.tmEq_append {Γ : Ctx sig} {A : Object sig.nBases}
    (p q : SatPlan Γ) (t : InvTm Γ A) :
    TmEq ((p.append q).apply t).erase (p.apply t).erase :=
  .trans ((p.append q).tmEq_apply t) (p.tmEq_apply t).symm

/-! ### Inconsistent contexts collapse

An inconsistent context is exactly one that supplies a neutral proof of `0`.
Saturation there reaches the canonical absurd branch, and *any* two
continuations become equal — which is what the comparison downstream needs.
-/

/-- The canonical plan for an inconsistent context. -/
def SatPlan.ofAbsurd {Γ : Ctx sig} (n : NegNeu Γ .never) : SatPlan Γ :=
  .absurd n

@[simp] theorem SatPlan.apply_ofAbsurd {Γ : Ctx sig} {A : Object sig.nBases}
    (n : NegNeu Γ .never) (t : InvTm Γ A) :
    (SatPlan.ofAbsurd n).apply t = .abort n := rfl

/-- In an inconsistent context both inputs saturate to the same syntax. -/
theorem SatPlan.absurd_apply_eq {Γ : Ctx sig} {A : Object sig.nBases}
    (n : NegNeu Γ .never) (t u : InvTm Γ A) :
    (SatPlan.ofAbsurd n).apply t = (SatPlan.ofAbsurd n).apply u := rfl

/-- …and the collapse is sound: the two inputs really were equal. -/
theorem SatPlan.tmEq_of_absurd {Γ : Ctx sig} {A : Object sig.nBases}
    (n : NegNeu Γ .never) (t u : InvTm Γ A) : TmEq t.erase u.erase :=
  TmEq.of_never n.erase _ _

end Equality
end Gimbal
