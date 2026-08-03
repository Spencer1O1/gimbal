/-
  Invertible commuting conversions (`≈icc`) for Milestone 7.

  Provides an inductive relation for the Milestone 8 proof bridge and a
  deterministic fueled canonicalizer used by executable comparison.
  Full completeness of the canonicalizer is deferred to Milestone 8.
-/

import Gimbal.Equality.Beq

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### ICC relation -/

mutual
/--
Invertible commuting conversions: congruence plus the commuting rules that
move `case` past invertible introductions.
-/
inductive ICCEq : {Γ : Ctx sig} → {A : Object sig.nBases} →
    InvTm Γ A → InvTm Γ A → Prop where
  | refl {Γ A} (t : InvTm Γ A) : ICCEq t t
  | symm {Γ A} {t u : InvTm Γ A} : ICCEq t u → ICCEq u t
  | trans {Γ A} {t u v : InvTm Γ A} : ICCEq t u → ICCEq u v → ICCEq t v
  | pair_cong {Γ A B} {t₁ t₂ : InvTm Γ A} {u₁ u₂ : InvTm Γ B} :
      ICCEq t₁ t₂ → ICCEq u₁ u₂ → ICCEq (.pair t₁ u₁) (.pair t₂ u₂)
  | lam_cong {Γ A B} {t u : InvTm (Γ ▻ A) B} :
      ICCEq t u → ICCEq (.lam t) (.lam u)
  | case_cong {Γ A B C} {n : NegNeu Γ (.coprod A B)}
      {t₁ t₂ : InvTm (Γ ▻ A) C} {u₁ u₂ : InvTm (Γ ▻ B) C} :
      ICCEq t₁ t₂ → ICCEq u₁ u₂ → ICCEq (.case n t₁ u₁) (.case n t₂ u₂)
  | foc_cong {Γ A} {f g : FocTm Γ A} :
      ICCFocEq f g → ICCEq (.foc f) (.foc g)
  | case_unit {Γ A B} (n : NegNeu Γ (.coprod A B)) :
      ICCEq (.case n .unit .unit) (.unit (Γ := Γ))
  | case_pair {Γ A B C D}
      (n : NegNeu Γ (.coprod A B))
      (t₁ : InvTm (Γ ▻ A) C) (t₂ : InvTm (Γ ▻ B) C)
      (u₁ : InvTm (Γ ▻ A) D) (u₂ : InvTm (Γ ▻ B) D) :
      ICCEq
        (.case n (.pair t₁ u₁) (.pair t₂ u₂))
        (.pair (.case n t₁ t₂) (.case n u₁ u₂))
  | case_lam {Γ A B C D}
      (n : NegNeu Γ (.coprod A B))
      (t : InvTm (Γ ▻ A ▻ C) D) (u : InvTm (Γ ▻ B ▻ C) D) :
      ICCEq
        (.case n (.lam t) (.lam u))
        (.lam (.case (NegNeu.weaken n)
          (InvTm.rename Rename.exchange t)
          (InvTm.rename Rename.exchange u)))
  | case_case {Γ A B C D E}
      (n : NegNeu Γ (.coprod A B))
      (m : NegNeu Γ (.coprod C D))
      (t₁ : InvTm (Γ ▻ A ▻ C) E) (t₂ : InvTm (Γ ▻ A ▻ D) E)
      (u₁ : InvTm (Γ ▻ B ▻ C) E) (u₂ : InvTm (Γ ▻ B ▻ D) E) :
      ICCEq
        (.case n
          (.case (NegNeu.weaken m) t₁ t₂)
          (.case (NegNeu.weaken m) u₁ u₂))
        (.case m
          (.case (NegNeu.weaken n)
            (InvTm.rename Rename.exchange t₁)
            (InvTm.rename Rename.exchange u₁))
          (.case (NegNeu.weaken n)
            (InvTm.rename Rename.exchange t₂)
            (InvTm.rename Rename.exchange u₂)))
  | abort_eq {Γ A} (n m : NegNeu Γ .never) :
      ICCEq (.abort (A := A) n) (.abort m)
  /-- Coproduct η: a `case` returning the two injections of its own binder. -/
  | coprod_eta {Γ A B} (n : NegNeu Γ (.coprod A B)) :
      ICCEq (.case n (InvTm.etaInl A B) (InvTm.etaInr A B))
        (.foc (.pos (.done (.neu n))))

inductive ICCFocEq : {Γ : Ctx sig} → {A : Object sig.nBases} →
    FocTm Γ A → FocTm Γ A → Prop where
  | refl {Γ A} (f : FocTm Γ A) : ICCFocEq f f
  | symm {Γ A} {f g : FocTm Γ A} : ICCFocEq f g → ICCFocEq g f
  | trans {Γ A} {f g h : FocTm Γ A} : ICCFocEq f g → ICCFocEq g h → ICCFocEq f h
  | letPos_cong {Γ P A} {n : NegNeu Γ P}
      {t u : InvTm (Γ ▻ P) A} :
      ICCEq t u → ICCFocEq (.letPos n t) (.letPos n u)
  | pos_cong {Γ A} {p q : PosIntro Γ A} :
      p = q → ICCFocEq (.pos p) (.pos q)
  | neg_cong {Γ A} {p q : NegElim Γ A} :
      p = q → ICCFocEq (.neg p) (.neg q)
  /-- Schedules are operational metadata: they do not affect the class. -/
  | sat_cong {Γ A} {s₁ s₂ : Schedule sig.nBases} {t u : InvTm Γ A} :
      ICCEq t u → ICCFocEq (.sat (.mk s₁ t)) (.sat (.mk s₂ u))
  /-- A saturation phase whose body is already focused is that focus. -/
  | sat_foc {Γ A} (s : Schedule sig.nBases) (f : FocTm Γ A) :
      ICCFocEq (.sat (.mk s (.foc f))) f
end

/-! ### Deterministic canonicalizer

Fuel-free: `caseCommute` recurses on the size of its left branch (renaming
preserves size), and the mutual canonicalizer is structural.
-/

/-- Commute a fully-normalized `case` past invertible introductions. -/
def caseCommute {Γ : Ctx sig} {A B C : Object sig.nBases}
    (n : NegNeu Γ (.coprod A B))
    (t : InvTm (Γ ▻ A) C) (u : InvTm (Γ ▻ B) C) : InvTm Γ C :=
  match t with
  | .unit =>
      match u with
      | .unit => .unit
      | u => .case n .unit u
  | .pair t₁ u₁ =>
      match u with
      | .pair t₂ u₂ =>
          .pair (caseCommute n t₁ t₂) (caseCommute n u₁ u₂)
      | u => .case n (.pair t₁ u₁) u
  | .lam t₁ =>
      match u with
      | .lam u₁ =>
          .lam (caseCommute (NegNeu.weaken n)
            (InvTm.rename Rename.exchange t₁)
            (InvTm.rename Rename.exchange u₁))
      | u => .case n (.lam t₁) u
  | .case (A := L) (B := R) n₁ t₁ u₁ =>
      match u with
      | .case (A := L') (B := R') n₂ t₂ u₂ =>
          if hL : L = L' then
            if hR : R = R' then
              match NegNeu.unweaken? n₁, NegNeu.unweaken? n₂ with
              | some m₁, some m₂ =>
                -- The conversion is symmetric, so it is only applied in the
                -- direction that puts the smaller scrutinee outermost;
                -- otherwise canonicalization would oscillate between the two
                -- nestings instead of being idempotent.
                if NegNeu.beq m₁ m₂ && NegNeu.blt m₁ n then
                  let t₂' : InvTm (Γ ▻ B ▻ L) _ := hL.symm ▸ t₂
                  let u₂' : InvTm (Γ ▻ B ▻ R) _ := hR.symm ▸ u₂
                  .case m₁
                    (caseCommute (NegNeu.weaken (B := L) n)
                      (InvTm.rename Rename.exchange t₁)
                      (InvTm.rename Rename.exchange t₂'))
                    (caseCommute (NegNeu.weaken (B := R) n)
                      (InvTm.rename Rename.exchange u₁)
                      (InvTm.rename Rename.exchange u₂'))
                else
                  .case n (.case n₁ t₁ u₁) u
              | _, _ => .case n (.case n₁ t₁ u₁) u
            else .case n (.case n₁ t₁ u₁) u
          else .case n (.case n₁ t₁ u₁) u
      | u => .case n (.case n₁ t₁ u₁) u
  | t => .case n t u
termination_by InvTm.size t
decreasing_by
  all_goals simp only [InvTm.size, InvTm.size_rename]
  all_goals omega

/--
Coproduct η: `case n (x. inl x) (y. inr y) = n` when the result type is the sum.

The branches are recognised by typed structural equality, which is
heterogeneous, so the result type is checked once and the comparison needs no
transport.
-/
def tryCoprodEta {Γ : Ctx sig} {A B C : Object sig.nBases}
    (n : NegNeu Γ (.coprod A B))
    (t : InvTm (Γ ▻ A) C) (u : InvTm (Γ ▻ B) C) : Option (InvTm Γ C) :=
  if h : C = (.coprod A B : Object sig.nBases) then
    if InvTm.beq t (InvTm.etaInl (Γ := Γ) A B) &&
        InvTm.beq u (InvTm.etaInr (Γ := Γ) A B) then
      some (h ▸ .foc (.pos (.done (.neu n))))
    else none
  else none

mutual
/-- Push `case` outward past invertible introductions. -/
def canonicalizeInv {Γ : Ctx sig} {A : Object sig.nBases} :
    InvTm Γ A → InvTm Γ A
  | .unit => .unit
  | .pair t u => .pair (canonicalizeInv t) (canonicalizeInv u)
  | .lam t => .lam (canonicalizeInv t)
  | .abort n => .abort n
  | .case n t u =>
      let t' := canonicalizeInv t
      let u' := canonicalizeInv u
      match tryCoprodEta n t' u' with
      | some r => r
      | none => caseCommute n t' u'
  | .foc f => .foc (canonicalizeFoc f)

def canonicalizeFoc {Γ : Ctx sig} {A : Object sig.nBases} :
    FocTm Γ A → FocTm Γ A
  | .pos p => .pos p
  | .neg n => .neg n
  | .letPos n t => .letPos n (canonicalizeInv t)
  | .sat (.mk _s t) =>
      -- Drop schedule metadata; keep only the saturated body.
      match canonicalizeInv t with
      | .foc f => f
      | t' => .sat (.mk ⟨#[]⟩ t')
end

/-- ICC canonicalizer (total, structural). -/
def canonicalize {Γ : Ctx sig} {A : Object sig.nBases}
    (t : InvTm Γ A) : InvTm Γ A :=
  canonicalizeInv t

end Equality
end Gimbal
