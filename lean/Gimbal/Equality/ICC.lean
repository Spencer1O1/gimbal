/-
  Invertible commuting conversions (`≈icc`) for Milestone 7.

  Provides an inductive relation for the Milestone 8 proof bridge and a
  deterministic fueled canonicalizer used by executable comparison.
  Full completeness of the canonicalizer is deferred to Milestone 8.
-/

import Gimbal.Equality.Focused

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

inductive ICCFocEq : {Γ : Ctx sig} → {A : Object sig.nBases} →
    FocTm Γ A → FocTm Γ A → Prop where
  | refl {Γ A} (f : FocTm Γ A) : ICCFocEq f f
  | letPos_cong {Γ P A} {n : NegNeu Γ P}
      {t u : InvTm (Γ ▻ P) A} :
      ICCEq t u → ICCFocEq (.letPos n t) (.letPos n u)
  | pos_cong {Γ A} {p q : PosIntro Γ A} :
      p = q → ICCFocEq (.pos p) (.pos q)
  | neg_cong {Γ A} {p q : NegElim Γ A} :
      p = q → ICCFocEq (.neg p) (.neg q)
  | sat_cong {Γ A} {s₁ s₂ : Schedule sig.nBases} {t u : InvTm Γ A} :
      s₁ = s₂ → ICCEq t u → ICCFocEq (.sat (.mk s₁ t)) (.sat (.mk s₂ u))
end

/-! ### Deterministic canonicalizer -/

/-- Commute a fully-normalized `case` past invertible introductions. -/
def caseCommute {Γ : Ctx sig} {A B C : Object sig.nBases}
    (fuel : Nat)
    (n : NegNeu Γ (.coprod A B))
    (t : InvTm (Γ ▻ A) C) (u : InvTm (Γ ▻ B) C) : InvTm Γ C :=
  match fuel with
  | 0 => .case n t u
  | fuel + 1 =>
    match t with
    | .unit =>
        match u with
        | .unit => .unit
        | u => .case n .unit u
    | .pair t₁ u₁ =>
        match u with
        | .pair t₂ u₂ =>
            .pair (caseCommute fuel n t₁ t₂) (caseCommute fuel n u₁ u₂)
        | u => .case n (.pair t₁ u₁) u
    | .lam t₁ =>
        match u with
        | .lam u₁ =>
            .lam (caseCommute fuel (NegNeu.weaken n)
              (InvTm.rename Rename.exchange t₁)
              (InvTm.rename Rename.exchange u₁))
        | u => .case n (.lam t₁) u
    | .case (A := C) (B := D) n₁ t₁ u₁ =>
        match u with
        | .case (A := C') (B := D') n₂ t₂ u₂ =>
            if hC : C = C' then
              if hD : D = D' then
                match NegNeu.unweaken? n₁, NegNeu.unweaken? n₂ with
                | some m₁, some m₂ =>
                  if NegNeu.toRaw m₁ == NegNeu.toRaw m₂ then
                    let t₂' : InvTm (Γ ▻ B ▻ C) _ := hC.symm ▸ t₂
                    let u₂' : InvTm (Γ ▻ B ▻ D) _ := hD.symm ▸ u₂
                    .case m₁
                      (caseCommute fuel (NegNeu.weaken (B := C) n)
                        (InvTm.rename Rename.exchange t₁)
                        (InvTm.rename Rename.exchange t₂'))
                      (caseCommute fuel (NegNeu.weaken (B := D) n)
                        (InvTm.rename Rename.exchange u₁)
                        (InvTm.rename Rename.exchange u₂'))
                  else
                    .case n (.case n₁ t₁ u₁) u
                | _, _ => .case n (.case n₁ t₁ u₁) u
              else .case n (.case n₁ t₁ u₁) u
            else .case n (.case n₁ t₁ u₁) u
        | u => .case n (.case n₁ t₁ u₁) u
    | t => .case n t u

/--
Coproduct η: `case n (x. inl x) (y. inr y) = n` when the result type is the sum.
Checked via raw spines so the mutual canonicalizer stays structurally recursive.
-/
def tryCoprodEta {Γ : Ctx sig} {A B C : Object sig.nBases}
    (n : NegNeu Γ (.coprod A B))
    (t : InvTm (Γ ▻ A) C) (u : InvTm (Γ ▻ B) C) : Option (InvTm Γ C) :=
  if h : C = (.coprod A B : Object sig.nBases) then
    match InvTm.toRaw t, InvTm.toRaw u with
    | .pos (.inl (.neu (.var 0))), .pos (.inr (.neu (.var 0))) =>
        some (h ▸ .foc (.pos (.done (.neu n))))
    | _, _ => none
  else
    none

mutual
/-- Push `case` outward past invertible introductions (fueled). -/
def canonicalizeInv (fuel : Nat) {Γ : Ctx sig} {A : Object sig.nBases} :
    InvTm Γ A → InvTm Γ A
  | t =>
    match fuel with
    | 0 => t
    | fuel + 1 =>
      match t with
      | .unit => .unit
      | .pair t u =>
          .pair (canonicalizeInv fuel t) (canonicalizeInv fuel u)
      | .lam t =>
          .lam (canonicalizeInv fuel t)
      | .abort n =>
          .abort n
      | .case n t u =>
          let t' := canonicalizeInv fuel t
          let u' := canonicalizeInv fuel u
          match tryCoprodEta n t' u' with
          | some r => r
          | none => caseCommute fuel n t' u'
      | .foc f =>
          .foc (canonicalizeFoc fuel f)

def canonicalizeFoc (fuel : Nat) {Γ : Ctx sig} {A : Object sig.nBases} :
    FocTm Γ A → FocTm Γ A
  | .pos p => .pos p
  | .neg n => .neg n
  | .letPos n t => .letPos n (canonicalizeInv fuel t)
  | .sat (.mk _s t) =>
      -- Drop schedule metadata; keep only the saturated body.
      match canonicalizeInv fuel t with
      | .foc f => f
      | t' => .sat (.mk ⟨#[]⟩ t')
end

/-- Default-fuel ICC canonicalizer. -/
def canonicalize {Γ : Ctx sig} {A : Object sig.nBases}
    (t : InvTm Γ A) (fuel : Nat := 2048) : InvTm Γ A :=
  canonicalizeInv fuel t

end Equality
end Gimbal
