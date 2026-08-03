/-
  Unique-order invertible-phase codes (Milestone 8F design E).

  `ICCCode` is the ordered representation of an invertible phase: left-positive
  worklist order is forced by `Origin`, not by raw scrutinee syntax. The public
  characterization target is

      ICCEq t u ↔ encodeICC ε t = encodeICC ε u

  Reification to `InvTm` is optional and deferred; the reference comparator may
  compare codes directly.

  Encoding is driven by `forcedRule` on the origin worklist. Recursion is
  currently bounded by candidate `encodeMeasure` (pending formula weight).
  Adequacy of that bound — every successful peel returns before fuel runs out —
  is an active obligation (`EncodeTotal` in `Completeness.lean`); the fuel
  parameter must not remain on the proof-critical path. Prefer well-founded
  recursion on worklist/goal weight once adequacy is proved.
-/

import Gimbal.Equality.Beq
import Gimbal.Equality.ICC
import Gimbal.Equality.ICCOrigin
import Init.Data.List.Sort.Lemmas

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Ordered codes -/

mutual
/--
Invertible-phase code in Scherer's unique-order subsystem.
Case/abort nodes are keyed by `Origin`, so binder exchange cannot flip their
relative order.
-/
inductive ICCCode : Ctx sig → Object sig.nBases → Type where
  | unit {Γ} : ICCCode Γ .unit
  | pair {Γ A B} : ICCCode Γ A → ICCCode Γ B → ICCCode Γ (.prod A B)
  | lam {Γ A B} : ICCCode (Γ ▻ A) B → ICCCode Γ (.exp A B)
  | case {Γ A B C} (o : Origin sig) :
      ICCCode (Γ ▻ A) C → ICCCode (Γ ▻ B) C → ICCCode Γ C
  | abort {Γ A} (o : Origin sig) : ICCCode Γ A
  | foc {Γ A} : FocCode Γ A → ICCCode Γ A

/-- Focused residue: observation binders keep origins; neutrals stay structural. -/
inductive FocCode : Ctx sig → Object sig.nBases → Type where
  | pos {Γ A} : PosNeu Γ A → FocCode Γ A
  | neg {Γ A} : NegNeu Γ A → FocCode Γ A
  | letPos {Γ P A} (o : Origin sig) :
      NegNeu Γ P → ICCCode (Γ ▻ P) A → FocCode Γ A
  /-- Saturation metadata is erased; only the body is coded. -/
  | body {Γ A} : ICCCode Γ A → FocCode Γ A
end

/-! ### Structural equality of codes -/

mutual
def ICCCode.beq : {Γ Δ : Ctx sig} → {A B : Object sig.nBases} →
    ICCCode Γ A → ICCCode Δ B → Bool
  | _, _, _, _, .unit, .unit => true
  | _, _, _, _, .pair t₁ t₂, .pair u₁ u₂ =>
      ICCCode.beq t₁ u₁ && ICCCode.beq t₂ u₂
  | _, _, _, _, .lam t, .lam u => ICCCode.beq t u
  | _, _, _, _, .case (A := L₁) (B := R₁) o₁ t u,
      .case (A := L₂) (B := R₂) o₂ v w =>
      decide (L₁ = L₂) && decide (R₁ = R₂) &&
        o₁ == o₂ && ICCCode.beq t v && ICCCode.beq u w
  | _, _, _, _, .abort o₁, .abort o₂ => o₁ == o₂
  | _, _, _, _, .foc f, .foc g => FocCode.beq f g
  | _, _, _, _, _, _ => false

def FocCode.beq : {Γ Δ : Ctx sig} → {A B : Object sig.nBases} →
    FocCode Γ A → FocCode Δ B → Bool
  | _, _, _, _, .pos p, .pos q => PosNeu.beq p q
  | _, _, _, _, .neg n, .neg m => NegNeu.beq n m
  | _, _, _, _, .letPos o₁ n t, .letPos o₂ m u =>
      o₁ == o₂ && NegNeu.beq n m && ICCCode.beq t u
  | _, _, _, _, .body t, .body u => ICCCode.beq t u
  | _, _, _, _, _, _ => false
end

/-! ### Structural Boolean equality on codes -/

mutual
theorem ICCCode.beq_rfl : {Γ : Ctx sig} → {A : Object sig.nBases} →
    (c : ICCCode Γ A) → ICCCode.beq c c = true
  | _, _, .unit => rfl
  | _, _, .pair c₁ c₂ => by
      simp only [ICCCode.beq, Bool.and_eq_true]
      exact ⟨ICCCode.beq_rfl c₁, ICCCode.beq_rfl c₂⟩
  | _, _, .lam c => ICCCode.beq_rfl c
  | _, _, .case o c₁ c₂ => by
      simp only [ICCCode.beq, decide_eq_true_eq, beq_self_eq_true, Bool.and_eq_true,
        true_and]
      exact ⟨ICCCode.beq_rfl c₁, ICCCode.beq_rfl c₂⟩
  | _, _, .abort o => by simp [ICCCode.beq]
  | _, _, .foc f => FocCode.beq_rfl f

theorem FocCode.beq_rfl : {Γ : Ctx sig} → {A : Object sig.nBases} →
    (f : FocCode Γ A) → FocCode.beq f f = true
  | _, _, .pos p => by
      simp only [FocCode.beq]
      exact PosNeu.beq_rfl p
  | _, _, .neg n => by
      simp only [FocCode.beq]
      exact NegNeu.beq_rfl n
  | _, _, .letPos o n c => by
      simp only [FocCode.beq, beq_self_eq_true, Bool.and_eq_true, true_and]
      exact ⟨NegNeu.beq_rfl n, ICCCode.beq_rfl c⟩
  | _, _, .body c => ICCCode.beq_rfl c
end

mutual
theorem ICCCode.eq_of_beq {Γ : Ctx sig} :
    ∀ {A : Object sig.nBases} (c d : ICCCode Γ A),
      ICCCode.beq c d = true → c = d
  | _, .unit, d, h => by
      cases d with
      | unit => rfl
      | case _ _ _ => simp [ICCCode.beq] at h
      | abort _ => simp [ICCCode.beq] at h
      | foc _ => simp [ICCCode.beq] at h
  | _, .pair c₁ c₂, d, h => by
      cases d with
      | pair d₁ d₂ =>
          simp only [ICCCode.beq, Bool.and_eq_true] at h
          rw [ICCCode.eq_of_beq c₁ d₁ h.1, ICCCode.eq_of_beq c₂ d₂ h.2]
      | case _ _ _ => simp [ICCCode.beq] at h
      | abort _ => simp [ICCCode.beq] at h
      | foc _ => simp [ICCCode.beq] at h
  | _, .lam c, d, h => by
      cases d with
      | lam e => rw [ICCCode.eq_of_beq c e (by simpa [ICCCode.beq] using h)]
      | case _ _ _ => simp [ICCCode.beq] at h
      | abort _ => simp [ICCCode.beq] at h
      | foc _ => simp [ICCCode.beq] at h
  | _, .case o c₁ c₂, d, h => by
      cases d with
      | case o' d₁ d₂ =>
          simp only [ICCCode.beq, Bool.and_eq_true, decide_eq_true_eq] at h
          rcases h with ⟨⟨⟨⟨rfl, rfl⟩, ho⟩, hc₁⟩, hc₂⟩
          cases LawfulBEq.eq_of_beq ho
          rw [ICCCode.eq_of_beq c₁ d₁ hc₁, ICCCode.eq_of_beq c₂ d₂ hc₂]
      | unit => simp [ICCCode.beq] at h
      | pair _ _ => simp [ICCCode.beq] at h
      | lam _ => simp [ICCCode.beq] at h
      | abort _ => simp [ICCCode.beq] at h
      | foc _ => simp [ICCCode.beq] at h
  | _, .abort o, d, h => by
      cases d with
      | abort o' =>
          simp only [ICCCode.beq] at h
          cases LawfulBEq.eq_of_beq h
          rfl
      | unit => simp [ICCCode.beq] at h
      | pair _ _ => simp [ICCCode.beq] at h
      | lam _ => simp [ICCCode.beq] at h
      | case _ _ _ => simp [ICCCode.beq] at h
      | foc _ => simp [ICCCode.beq] at h
  | _, .foc f, d, h => by
      cases d with
      | foc g => rw [FocCode.eq_of_beq f g (by simpa [ICCCode.beq] using h)]
      | unit => simp [ICCCode.beq] at h
      | pair _ _ => simp [ICCCode.beq] at h
      | lam _ => simp [ICCCode.beq] at h
      | case _ _ _ => simp [ICCCode.beq] at h
      | abort _ => simp [ICCCode.beq] at h

theorem FocCode.eq_of_beq {Γ : Ctx sig} :
    ∀ {A : Object sig.nBases} (f g : FocCode Γ A),
      FocCode.beq f g = true → f = g
  | _, .pos p, g, h => by
      cases g with
      | pos q => rw [PosNeu.eq_of_beq p q (by simpa [FocCode.beq] using h)]
      | neg _ => simp [FocCode.beq] at h
      | letPos _ _ _ => simp [FocCode.beq] at h
      | body _ => simp [FocCode.beq] at h
  | _, .neg n, g, h => by
      cases g with
      | neg m =>
          obtain ⟨_, hnm⟩ := NegNeu.eq_of_beq n m (by simpa [FocCode.beq] using h)
          cases eq_of_heq hnm
          rfl
      | pos _ => simp [FocCode.beq] at h
      | letPos _ _ _ => simp [FocCode.beq] at h
      | body _ => simp [FocCode.beq] at h
  | _, .letPos o n c, g, h => by
      cases g with
      | letPos o' m d =>
          simp only [FocCode.beq, Bool.and_eq_true] at h
          cases LawfulBEq.eq_of_beq h.1.1
          obtain ⟨rfl, hnm⟩ := NegNeu.eq_of_beq n m h.1.2
          cases eq_of_heq hnm
          rw [ICCCode.eq_of_beq c d h.2]
      | pos _ => simp [FocCode.beq] at h
      | neg _ => simp [FocCode.beq] at h
      | body _ => simp [FocCode.beq] at h
  | _, .body c, g, h => by
      cases g with
      | body d => rw [ICCCode.eq_of_beq c d (by simpa [FocCode.beq] using h)]
      | pos _ => simp [FocCode.beq] at h
      | neg _ => simp [FocCode.beq] at h
      | letPos _ _ _ => simp [FocCode.beq] at h
end

theorem ICCCode.beq_iff_eq {Γ : Ctx sig} {A : Object sig.nBases}
    (c d : ICCCode Γ A) : ICCCode.beq c d = true ↔ c = d :=
  ⟨ICCCode.eq_of_beq c d, fun h => h ▸ ICCCode.beq_rfl c⟩

theorem FocCode.beq_iff_eq {Γ : Ctx sig} {A : Object sig.nBases}
    (f g : FocCode Γ A) : FocCode.beq f g = true ↔ f = g :=
  ⟨FocCode.eq_of_beq f g, fun h => h ▸ FocCode.beq_rfl f⟩

/-! ### Worklist measure (candidate) -/

/-- Constructor weight of a formula — decreases when an invertible connective is peeled. -/
def objectWeight {n : Nat} : Object n → Nat
  | .base _ | .never | .unit => 1
  | .prod A B | .coprod A B | .exp A B => objectWeight A + objectWeight B + 1

def worklistWeight (ws : List (PosEntry sig)) : Nat :=
  ws.foldl (fun acc e => acc + objectWeight e.ty) 0

def encodeMeasure (ws : List (PosEntry sig)) (goal : Object sig.nBases) : Nat :=
  worklistWeight ws + objectWeight goal

theorem objectWeight_pos {n : Nat} (A : Object n) : 0 < objectWeight A := by
  cases A <;> simp [objectWeight] <;> omega

private theorem List.foldl_add_nat {α : Type _} (ws : List α) (f : α → Nat) (a : Nat) :
    ws.foldl (fun acc x => acc + f x) a =
      a + ws.foldl (fun acc x => acc + f x) 0 := by
  induction ws generalizing a with
  | nil => rfl
  | cons x xs ih =>
      have hx :
          (x :: xs).foldl (fun acc y => acc + f y) 0 =
            f x + xs.foldl (fun acc y => acc + f y) 0 := by
        simpa [List.foldl, Nat.zero_add] using ih (f x)
      change xs.foldl (fun acc y => acc + f y) (a + f x) =
        a + (x :: xs).foldl (fun acc y => acc + f y) 0
      rw [ih (a + f x), hx]
      omega

theorem worklistWeight_cons (e : PosEntry sig) (ws : List (PosEntry sig)) :
    worklistWeight (e :: ws) = objectWeight e.ty + worklistWeight ws := by
  simp only [worklistWeight, List.foldl]
  have h := List.foldl_add_nat ws (fun e => objectWeight e.ty) (objectWeight e.ty)
  simpa [Nat.zero_add] using h

theorem encodeMeasure_cons_pos (e : PosEntry sig) (ws : List (PosEntry sig))
    (goal : Object sig.nBases) :
    0 < encodeMeasure (e :: ws) goal := by
  have he : 0 < objectWeight e.ty := objectWeight_pos _
  have hg : 0 < objectWeight goal := objectWeight_pos _
  rw [encodeMeasure, worklistWeight_cons]
  omega

/-- Dropping a worklist head strictly decreases the encode measure. -/
theorem encodeMeasure_tail_lt (e : PosEntry sig) (ws : List (PosEntry sig))
    (goal : Object sig.nBases) :
    encodeMeasure ws goal < encodeMeasure (e :: ws) goal := by
  have he : 0 < objectWeight e.ty := objectWeight_pos _
  simp only [encodeMeasure, worklistWeight_cons]
  omega

/-- Right-product recursion uses a strictly smaller goal weight. -/
theorem encodeMeasure_prod_fst_lt (ws : List (PosEntry sig))
    (L R : Object sig.nBases) :
    encodeMeasure ws L < encodeMeasure ws (.prod L R) := by
  simp only [encodeMeasure, objectWeight]
  omega

theorem encodeMeasure_prod_snd_lt (ws : List (PosEntry sig))
    (L R : Object sig.nBases) :
    encodeMeasure ws R < encodeMeasure ws (.prod L R) := by
  simp only [encodeMeasure, objectWeight]
  omega

theorem encodeMeasure_exp_ret_lt (ws : List (PosEntry sig))
    (Arg Ret : Object sig.nBases) :
    encodeMeasure ws Ret < encodeMeasure ws (.exp Arg Ret) := by
  simp only [encodeMeasure, objectWeight]
  omega

/-! ### Worklist permutation (for `pushPos` / `mergeSort`) -/

private theorem foldl_objectWeight_perm {ws ws' : List (PosEntry sig)}
    (h : ws.Perm ws') (a : Nat) :
    ws.foldl (fun acc e => acc + objectWeight e.ty) a =
      ws'.foldl (fun acc e => acc + objectWeight e.ty) a := by
  induction h generalizing a with
  | nil => rfl
  | cons _ h ih =>
      simpa [List.foldl] using ih _
  | swap x y l =>
      simp only [List.foldl]
      have hx :=
        List.foldl_add_nat l (fun e => objectWeight e.ty)
          (a + objectWeight x.ty + objectWeight y.ty)
      have hy :=
        List.foldl_add_nat l (fun e => objectWeight e.ty)
          (a + objectWeight y.ty + objectWeight x.ty)
      rw [hx, hy]
      omega
  | trans _ _ ih₁ ih₂ =>
      exact (ih₁ a).trans (ih₂ a)

theorem worklistWeight_of_perm {ws ws' : List (PosEntry sig)}
    (h : ws.Perm ws') :
    worklistWeight ws = worklistWeight ws' :=
  foldl_objectWeight_perm h 0

theorem worklistWeight_mergeSort (ws : List (PosEntry sig))
    (le : PosEntry sig → PosEntry sig → Bool) :
    worklistWeight (ws.mergeSort le) = worklistWeight ws :=
  worklistWeight_of_perm (List.mergeSort_perm ws le)

/-! ### Adequate encode fuel (input-dependent; no fixed public bound)

`encodeMeasure` alone is **not** adequate: a positive `letPos` strictly
increases worklist weight (`encodeMeasure_lt_pushPos_of_pos`). The term-derived
`posPushBudget` pre-pays every `objectWeight P` that encode may insert via
observation binders. Together with structural size (for `sat` unwrap and
ordinary peeling), this yields a single derived fuel for every recursive path.
-/

mutual
/-- Extra formula weight encode may push via positive `letPos` binders. -/
def InvTm.posPushBudget {Γ : Ctx sig} {A : Object sig.nBases} : InvTm Γ A → Nat
  | .unit => 0
  | .pair t u => InvTm.posPushBudget t + InvTm.posPushBudget u
  | .lam t => InvTm.posPushBudget t
  | .case _ t u => InvTm.posPushBudget t + InvTm.posPushBudget u
  | .abort _ => 0
  | .foc f => FocTm.posPushBudget f

def FocTm.posPushBudget {Γ : Ctx sig} {A : Object sig.nBases} : FocTm Γ A → Nat
  | .pos _ => 0
  | .neg _ => 0
  | .letPos (P := P) _ t => objectWeight P + InvTm.posPushBudget t
  | .sat (.mk _ t) => InvTm.posPushBudget t
end

mutual
theorem InvTm.posPushBudget_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (t : InvTm Γ A) :
    (InvTm.rename ρ t).posPushBudget = t.posPushBudget :=
  match t with
  | .unit => rfl
  | .pair t u => by
      simp [InvTm.rename, InvTm.posPushBudget, InvTm.posPushBudget_rename ρ t,
        InvTm.posPushBudget_rename ρ u]
  | .lam t => by
      simp [InvTm.rename, InvTm.posPushBudget,
        InvTm.posPushBudget_rename (Rename.ext ρ) t]
  | .case n t u => by
      simp [InvTm.rename, InvTm.posPushBudget,
        InvTm.posPushBudget_rename (Rename.ext ρ) t,
        InvTm.posPushBudget_rename (Rename.ext ρ) u]
  | .abort _ => rfl
  | .foc f => by
      simp [InvTm.rename, InvTm.posPushBudget, FocTm.posPushBudget_rename ρ f]
termination_by t.size
decreasing_by all_goals decreasing_trivial

theorem FocTm.posPushBudget_rename {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (f : FocTm Γ A) :
    (FocTm.rename ρ f).posPushBudget = f.posPushBudget :=
  match f with
  | .pos _ | .neg _ => rfl
  | .letPos n t => by
      simp [FocTm.rename, FocTm.posPushBudget,
        InvTm.posPushBudget_rename (Rename.ext ρ) t]
  | .sat (.mk s t) => by
      simp [FocTm.rename, SatTm.rename, FocTm.posPushBudget,
        InvTm.posPushBudget_rename ρ t]
termination_by f.size
decreasing_by all_goals decreasing_trivial
end

/--
Derived adequate fuel (design target for `encodeICC`).

`encodeMeasure` alone fails on positive `letPos`. This bound adds:
* `posPushBudget` — pre-pays every positive observation push;
* `2 * InvTm.size` — pays `sat`/focus unwrap and ensures strict decrease on
  term-shaped recursion.

Commute pairs may have unequal sizes (so unequal fuels); lifting Go-level
agreement to `encodeICC` equality needs fuel monotonicity. Until that lands,
`encodeICC` still runs on `encodeFuel` and commute proofs use shared-fuel
lemmas where budgets match and size is replaced by a common max, or Go-level
packaging.

No fixed public constant (e.g. 2048).
-/
def encodeFuel {Γ : Ctx sig} {A : Object sig.nBases}
    (ws : List (PosEntry sig)) (t : InvTm Γ A) : Nat :=
  encodeMeasure ws A + InvTm.posPushBudget t + 2 * InvTm.size t

/-- Focused counterpart. -/
def encodeFuelFoc {Γ : Ctx sig} {A : Object sig.nBases}
    (ws : List (PosEntry sig)) (f : FocTm Γ A) : Nat :=
  encodeMeasure ws A + FocTm.posPushBudget f + 2 * FocTm.size f

theorem encodeFuel_foc {Γ : Ctx sig} {A : Object sig.nBases}
    (ws : List (PosEntry sig)) (f : FocTm Γ A) :
    encodeFuel ws (.foc f) = encodeFuelFoc ws f + 2 := by
  simp only [encodeFuel, encodeFuelFoc, InvTm.size, InvTm.posPushBudget]
  omega

theorem encodeFuel_pos {Γ : Ctx sig} {A : Object sig.nBases}
    (ws : List (PosEntry sig)) (t : InvTm Γ A) :
    0 < encodeFuel ws t := by
  have hs : 0 < InvTm.size t := by
    cases t <;> simp [InvTm.size, FocTm.size] <;> try omega
  simp only [encodeFuel]
  omega

/-! ### Forced next rule -/

/-- Which unique-order rule is forced by the current worklist and goal. -/
inductive ForcedRule (sig : Signature) : Type where
  | leftCoprod (e : PosEntry sig) (L R : Object sig.nBases)
  | leftNever (e : PosEntry sig)
  /-- Head positive is stable (atomic): move it off the worklist without focusing. -/
  | moveStable (e : PosEntry sig)
  | rightUnit
  | rightProd (L R : Object sig.nBases)
  | rightExp (Arg Ret : Object sig.nBases)
  | focus
  deriving Repr

def forcedRule (ws : List (PosEntry sig)) (goal : Object sig.nBases) :
    ForcedRule sig :=
  match ws with
  | e :: _ =>
      match e.ty with
      | .coprod L R => .leftCoprod e L R
      | .never => .leftNever e
      | .base _ => .moveStable e
      | _ => .moveStable e
  | [] =>
      match goal with
      | .unit => .rightUnit
      | .prod L R => .rightProd L R
      | .exp Arg Ret => .rightExp Arg Ret
      | _ => .focus

/-! ### Peeling -/

/-- Origin of a variable scrutinee, if any. -/
def originOfVar {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) : NegNeu Γ A → Option (Origin sig)
  | .var x => some (ε x)
  | _ => none

/--
Push a `case` past matching invertible introductions (ICC `case_pair` /
`case_lam` / `case_unit` in the outward direction). Used only to expose a
forced origin; never orients by `NegNeu.blt`.
-/
def distCaseOut {Γ : Ctx sig} {A B C : Object sig.nBases}
    (n : NegNeu Γ (.coprod A B))
    (t : InvTm (Γ ▻ A) C) (u : InvTm (Γ ▻ B) C) : Option (InvTm Γ C) :=
  match t, u with
  | .pair t₁ u₁, .pair t₂ u₂ =>
      some (.pair (.case n t₁ t₂) (.case n u₁ u₂))
  | .lam t₁, .lam u₁ =>
      some (.lam (.case (NegNeu.weaken n)
        (InvTm.rename Rename.exchange t₁)
        (InvTm.rename Rename.exchange u₁)))
  | .unit, .unit => some .unit
  | _, _ => none

/--
Expose a `case` whose scrutinee variable has origin `o`, reconstructing via
distribution and origin-directed `case`/`case` exchange. Fuel decreases with
`InvTm.size` on every recursive call.
-/
def peelCaseOuterGo {Γ : Ctx sig} {C : Object sig.nBases}
    (fuel : Nat) (ε : OriginEnv Γ) (o : Origin sig) (t : InvTm Γ C) :
    Option ((A B : Object sig.nBases) × NegNeu Γ (.coprod A B) ×
      InvTm (Γ ▻ A) C × InvTm (Γ ▻ B) C) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match t with
    | .case (A := A) (B := B) (.var x) tL tR =>
        if ε x == o then
          some ⟨A, B, .var x, tL, tR⟩
        else
          let εL : OriginEnv (Γ ▻ A) :=
            OriginEnv.weaken (A := A) ε (.split (ε x) false)
          let εR : OriginEnv (Γ ▻ B) :=
            OriginEnv.weaken (A := B) ε (.split (ε x) true)
          match peelCaseOuterGo fuel εL o tL, peelCaseOuterGo fuel εR o tR with
          | some ⟨C₁, D₁, n₁, a₁, b₁⟩, some ⟨C₂, D₂, n₂, a₂, b₂⟩ =>
              if hC : C₁ = C₂ then
                if hD : D₁ = D₂ then
                  let n₂' : NegNeu (Γ ▻ B) (.coprod C₁ D₁) :=
                    hD ▸ hC ▸ n₂
                  let a₂' : InvTm (Γ ▻ B ▻ C₁) C := hC ▸ a₂
                  let b₂' : InvTm (Γ ▻ B ▻ D₁) C := hD ▸ b₂
                  if NegNeu.beq n₁ n₂' then
                    match NegNeu.unweaken? n₁ with
                    | some m =>
                        match originOfVar ε m with
                        | some om =>
                            if om == o then
                              some ⟨C₁, D₁, m,
                                .case (NegNeu.weaken (B := C₁) (.var x))
                                  (InvTm.rename Rename.exchange a₁)
                                  (InvTm.rename Rename.exchange a₂'),
                                .case (NegNeu.weaken (B := D₁) (.var x))
                                  (InvTm.rename Rename.exchange b₁)
                                  (InvTm.rename Rename.exchange b₂')⟩
                            else none
                        | none => none
                    | none => none
                  else none
                else none
              else none
          | _, _ =>
              match distCaseOut (.var x) tL tR with
              | some t' => peelCaseOuterGo fuel ε o t'
              | none => none
    | .pair t₁ t₂ =>
        match peelCaseOuterGo fuel ε o t₁, peelCaseOuterGo fuel ε o t₂ with
        | some ⟨A, B, n, l₁, r₁⟩, some ⟨A', B', n', l₂, r₂⟩ =>
            if hA : A = A' then
              if hB : B = B' then
                let n' : NegNeu Γ (.coprod A B) := hB ▸ hA ▸ n'
                let l₂' : InvTm (Γ ▻ A) _ := hA ▸ l₂
                let r₂' : InvTm (Γ ▻ B) _ := hB ▸ r₂
                if NegNeu.beq n n' then
                  some ⟨A, B, n, .pair l₁ l₂', .pair r₁ r₂'⟩
                else none
              else none
            else none
        | _, _ => none
    | .lam (A := Arg) body =>
        -- Peel only needs a non-colliding binder tag; encode assigns real `dom`
        -- nesting. Forced origins are hyp/obs/split, never `dom`.
        let ε' : OriginEnv (Γ ▻ Arg) :=
          OriginEnv.weaken (A := Arg) ε (.dom 0)
        match peelCaseOuterGo fuel ε' o body with
        | some ⟨A, B, n, tL, tR⟩ =>
            match NegNeu.unweaken? n with
            | some n0 =>
                some ⟨A, B, n0,
                  .lam (InvTm.rename Rename.exchange tL),
                  .lam (InvTm.rename Rename.exchange tR)⟩
            | none => none
        | none => none
    | .unit => none
    | .abort _ => none
    | .foc f =>
        -- Dig under observation structure so a forced hyp left-coprod can be
        -- exposed despite `Origin.cmp` ordering hyp < obs while `applyPairObs`
        -- nests atom observations as outer `letPos`.
        match f with
        | .sat (.mk _ body) =>
            peelCaseOuterGo fuel ε o body
        | .letPos (P := P) n body =>
            -- Peel only needs a non-colliding binder tag; encode assigns real
            -- `obsSlot` later. Use `.dom 0` (same as λ dig): forced origins are
            -- hyp/obs/split, never `dom`, and `rekeyHypToObs` fixes `.dom`, so
            -- dig under letPos commutes with newest-hyp→obs rekey (unlike a
            -- temporary `.obs 0`, which collides after `hyp ↦ obs 0`).
            let ε' : OriginEnv (Γ ▻ P) :=
              OriginEnv.weaken (A := P) ε (.dom 0)
            match peelCaseOuterGo fuel ε' o body with
            | some ⟨A, B, m, tL, tR⟩ =>
                match NegNeu.unweaken? m with
                | some m0 =>
                    some ⟨A, B, m0,
                      .foc (.letPos (NegNeu.weaken (B := A) n)
                        (InvTm.rename Rename.exchange tL)),
                      .foc (.letPos (NegNeu.weaken (B := B) n)
                        (InvTm.rename Rename.exchange tR))⟩
                | none => none
            | none => none
        | .pos _ | .neg _ => none
    | .case _ _ _ => none

def peelCaseOuter {Γ : Ctx sig} {C : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) (t : InvTm Γ C) :
    Option ((A B : Object sig.nBases) × NegNeu Γ (.coprod A B) ×
      InvTm (Γ ▻ A) C × InvTm (Γ ▻ B) C) :=
  peelCaseOuterGo (InvTm.size t) ε o t

def peelPair {Γ : Ctx sig} {L R : Object sig.nBases} :
    InvTm Γ (.prod L R) → Option (InvTm Γ L × InvTm Γ R)
  | .pair t u => some (t, u)
  | _ => none

def peelLam {Γ : Ctx sig} {Arg Ret : Object sig.nBases} :
    InvTm Γ (.exp Arg Ret) → Option (InvTm (Γ ▻ Arg) Ret)
  | .lam t => some t
  | _ => none

def peelUnit {Γ : Ctx sig} : InvTm Γ .unit → Bool
  | .unit => true
  | _ => false

def pushPos (ws : List (PosEntry sig)) (o : Origin sig) (ty : Object sig.nBases) :
    List (PosEntry sig) :=
  if objectPolarity ty == .pos then
    ({ origin := o, ty := ty } :: ws).mergeSort fun a b =>
      Origin.ble a.origin b.origin
  else ws

/--
`pushPos` either leaves the worklist alone (negative type) or inserts one
entry and reorders; weight gains exactly `objectWeight ty` when polarity is
positive.
-/
theorem worklistWeight_pushPos (ws : List (PosEntry sig)) (o : Origin sig)
    (ty : Object sig.nBases) :
    worklistWeight (pushPos ws o ty) =
      if objectPolarity ty == .pos then
        objectWeight ty + worklistWeight ws
      else
        worklistWeight ws := by
  dsimp only [pushPos]
  cases hpol : objectPolarity ty == Polarity.pos
  · change worklistWeight ws = worklistWeight ws
    rfl
  · change
      worklistWeight
          (({ origin := o, ty := ty } :: ws).mergeSort
            fun a b => Origin.ble a.origin b.origin) =
        objectWeight ty + worklistWeight ws
    rw [worklistWeight_mergeSort, worklistWeight_cons]

/-- Pushing a formula adds at most that formula's weight. -/
theorem worklistWeight_pushPos_le (ws : List (PosEntry sig)) (o : Origin sig)
    (ty : Object sig.nBases) :
    worklistWeight (pushPos ws o ty) ≤ objectWeight ty + worklistWeight ws := by
  rw [worklistWeight_pushPos]
  split <;> omega

/-- At a positive type, `pushPos` adds exactly one copy of its weight. -/
theorem encodeMeasure_pushPos_of_pos (ws : List (PosEntry sig)) (o : Origin sig)
    (ty goal : Object sig.nBases) (hpos : objectPolarity ty = .pos) :
    encodeMeasure (pushPos ws o ty) goal =
      objectWeight ty + encodeMeasure ws goal := by
  have hbeq : (objectPolarity ty == Polarity.pos) = true := by simp [hpos]
  simp only [encodeMeasure]
  rw [worklistWeight_pushPos, hbeq]
  change
    objectWeight ty + worklistWeight ws + objectWeight goal =
      objectWeight ty + (worklistWeight ws + objectWeight goal)
  omega

/--
A positive insertion strictly increases the measure. In particular, a
positive `letPos` observation cannot be justified by `encodeMeasure` alone
— use `encodeFuel` (measure + size + posPushBudget).
-/
theorem encodeMeasure_pushPos_pos_lt (ws : List (PosEntry sig)) (o : Origin sig)
    (ty goal : Object sig.nBases) (hpos : objectPolarity ty = .pos) :
    encodeMeasure ws goal < encodeMeasure (pushPos ws o ty) goal := by
  have hw := objectWeight_pos ty
  have hbeq : (objectPolarity ty == Polarity.pos) = true := by
    simp [hpos]
  simp only [encodeMeasure]
  rw [worklistWeight_pushPos, hbeq]
  change
    worklistWeight ws + objectWeight goal <
      objectWeight ty + worklistWeight ws + objectWeight goal
  omega

theorem encodeMeasure_lt_pushPos_of_pos (ws : List (PosEntry sig)) (o : Origin sig)
    (ty goal : Object sig.nBases) (hpos : objectPolarity ty = .pos) :
    encodeMeasure ws goal < encodeMeasure (pushPos ws o ty) goal :=
  encodeMeasure_pushPos_pos_lt ws o ty goal hpos

/--
Left-coprod recursion: after consuming a `.coprod L R` head, each branch
worklist (tail + optional push of the binder) has strictly smaller measure
than the parent. Here `ws` is already the tail of the forced worklist.
-/
theorem encodeMeasure_leftCoprod_lt (e : PosEntry sig) (ws : List (PosEntry sig))
    {L R : Object sig.nBases} (hty : e.ty = .coprod L R)
    (goal : Object sig.nBases) (side : Bool) :
    encodeMeasure (pushPos ws (.split e.origin side) (if side then R else L)) goal <
      encodeMeasure (e :: ws) goal := by
  have he : objectWeight e.ty = objectWeight L + objectWeight R + 1 := by
    simp [hty, objectWeight]
  have hL := objectWeight_pos L
  have hR := objectWeight_pos R
  cases side with
  | false =>
      change encodeMeasure (pushPos ws (.split e.origin false) L) goal <
        encodeMeasure (e :: ws) goal
      simp only [encodeMeasure, worklistWeight_cons, he]
      rw [worklistWeight_pushPos]
      cases hpol : objectPolarity L == Polarity.pos
      · change
          worklistWeight ws + objectWeight goal <
            objectWeight L + objectWeight R + 1 + worklistWeight ws + objectWeight goal
        omega
      · change
          objectWeight L + worklistWeight ws + objectWeight goal <
            objectWeight L + objectWeight R + 1 + worklistWeight ws + objectWeight goal
        omega
  | true =>
      change encodeMeasure (pushPos ws (.split e.origin true) R) goal <
        encodeMeasure (e :: ws) goal
      simp only [encodeMeasure, worklistWeight_cons, he]
      rw [worklistWeight_pushPos]
      cases hpol : objectPolarity R == Polarity.pos
      · change
          worklistWeight ws + objectWeight goal <
            objectWeight L + objectWeight R + 1 + worklistWeight ws + objectWeight goal
        omega
      · change
          objectWeight R + worklistWeight ws + objectWeight goal <
            objectWeight L + objectWeight R + 1 + worklistWeight ws + objectWeight goal
        omega

/--
Right-λ recursion: encode the body at `Ret` under `pushPos` of the domain.
Always strictly smaller than encoding at `.exp Arg Ret` on the same spine.
-/
theorem encodeMeasure_exp_push_lt (ws : List (PosEntry sig)) (o : Origin sig)
    (Arg Ret : Object sig.nBases) :
    encodeMeasure (pushPos ws o Arg) Ret <
      encodeMeasure ws (.exp Arg Ret) := by
  have hArg := objectWeight_pos Arg
  have hRet := objectWeight_pos Ret
  simp only [encodeMeasure, objectWeight]
  rw [worklistWeight_pushPos]
  cases hpol : objectPolarity Arg == Polarity.pos
  · change
      worklistWeight ws + objectWeight Ret <
        worklistWeight ws + (objectWeight Arg + objectWeight Ret + 1)
    omega
  · change
      objectWeight Arg + worklistWeight ws + objectWeight Ret <
        worklistWeight ws + (objectWeight Arg + objectWeight Ret + 1)
    omega

/-! ### `encodeFuel` decreases on recursive encode paths -/

/-- `moveStable`: same term, lighter worklist. -/
theorem encodeFuel_moveStable_lt {Γ : Ctx sig} {A : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (t : InvTm Γ A) :
    encodeFuel ws t < encodeFuel (e :: ws) t := by
  have he := objectWeight_pos e.ty
  simp only [encodeFuel, encodeMeasure, worklistWeight_cons]
  omega

/-- Right-product: each component has strictly smaller fuel than the pair. -/
theorem encodeFuel_pair_fst_lt {Γ : Ctx sig} {L R : Object sig.nBases}
    (ws : List (PosEntry sig)) (t : InvTm Γ L) (u : InvTm Γ R) :
    encodeFuel ws t < encodeFuel ws (.pair t u) := by
  have hR := objectWeight_pos R
  simp only [encodeFuel, encodeMeasure, objectWeight, InvTm.size, InvTm.posPushBudget]
  omega

theorem encodeFuel_pair_snd_lt {Γ : Ctx sig} {L R : Object sig.nBases}
    (ws : List (PosEntry sig)) (t : InvTm Γ L) (u : InvTm Γ R) :
    encodeFuel ws u < encodeFuel ws (.pair t u) := by
  have hL := objectWeight_pos L
  simp only [encodeFuel, encodeMeasure, objectWeight, InvTm.size, InvTm.posPushBudget]
  omega

/-- Right-λ: body under `pushPos` of the domain has smaller fuel than the λ. -/
theorem encodeFuel_lam_lt {Γ : Ctx sig} {Arg Ret : Object sig.nBases}
    (ws : List (PosEntry sig)) (o : Origin sig) (body : InvTm (Γ ▻ Arg) Ret) :
    encodeFuel (pushPos ws o Arg) body < encodeFuel ws (.lam body) := by
  have hmeas := encodeMeasure_exp_push_lt ws o Arg Ret
  simp only [encodeFuel, InvTm.size, InvTm.posPushBudget] at *
  omega

/--
Positive `letPos`: after two outer steps, the child under `pushPos` fits.
Budget pre-pays `objectWeight P`; size pays the dual unwrap.
-/
theorem encodeFuel_letPos_le {Γ : Ctx sig} {P A : Object sig.nBases}
    (ws : List (PosEntry sig)) (o : Origin sig)
    (_n : NegNeu Γ P) (t : InvTm (Γ ▻ P) A) :
    encodeFuel (pushPos ws o P) t + 2 ≤ encodeFuel ws (.foc (.letPos _n t)) := by
  have hmeas : encodeMeasure (pushPos ws o P) A ≤
      objectWeight P + encodeMeasure ws A := by
    simp only [encodeMeasure]
    have := worklistWeight_pushPos_le ws o P
    omega
  simp only [encodeFuel, InvTm.size, InvTm.posPushBudget, FocTm.size,
    FocTm.posPushBudget]
  omega

/-- `sat` unwrap: two outer steps; size of the `foc`/`sat` shell pays. -/
theorem encodeFuel_sat_le {Γ : Ctx sig} {A : Object sig.nBases}
    (ws : List (PosEntry sig)) (_s : Schedule sig.nBases) (t : InvTm Γ A) :
    encodeFuel ws t + 2 ≤ encodeFuel ws (.foc (.sat (.mk _s t))) := by
  simp only [encodeFuel, InvTm.size, InvTm.posPushBudget, FocTm.size,
    FocTm.posPushBudget]
  omega

/-- Focus fuel vs `.foc` fuel. -/
theorem encodeFuel_focus_eq {Γ : Ctx sig} {A : Object sig.nBases}
    (ws : List (PosEntry sig)) (f : FocTm Γ A) :
    encodeFuel ws (.foc f) = encodeFuelFoc ws f + 2 :=
  encodeFuel_foc ws f

/-- Adequate bound for a left-coprod continuation (max of the two branches). -/
def encodeFuelBranches {Γ : Ctx sig} {L R A : Object sig.nBases}
    (ws : List (PosEntry sig)) (e : PosEntry sig)
    (tL : InvTm (Γ ▻ L) A) (tR : InvTm (Γ ▻ R) A) : Nat :=
  let ws' := ws.tail
  max (encodeFuel (pushPos ws' (.split e.origin false) L) tL)
      (encodeFuel (pushPos ws' (.split e.origin true) R) tR)

/--
Left-coprod branch: after consuming `.coprod L R`, each peeled branch under
`pushPos` has strictly smaller fuel than the parent case.
-/
theorem encodeFuel_leftCoprod_lt {Γ : Ctx sig} {A B C : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (o : Origin sig)
    (hty : e.ty = .coprod A B)
    (n : NegNeu Γ (.coprod A B))
    (tL : InvTm (Γ ▻ A) C) (tR : InvTm (Γ ▻ B) C) :
    encodeFuel (pushPos ws o A) tL <
      encodeFuel (e :: ws) (.case n tL tR) := by
  have hpush := worklistWeight_pushPos_le ws o A
  have hB := objectWeight_pos B
  have hn : 0 < NegNeu.size n := by
    cases n <;> simp [NegNeu.size] <;> omega
  simp only [encodeFuel, encodeMeasure, worklistWeight_cons, hty, objectWeight,
    InvTm.size, InvTm.posPushBudget]
  omega

theorem encodeFuel_leftCoprod_right_lt {Γ : Ctx sig} {A B C : Object sig.nBases}
    (e : PosEntry sig) (ws : List (PosEntry sig)) (o : Origin sig)
    (hty : e.ty = .coprod A B)
    (n : NegNeu Γ (.coprod A B))
    (tL : InvTm (Γ ▻ A) C) (tR : InvTm (Γ ▻ B) C) :
    encodeFuel (pushPos ws o B) tR <
      encodeFuel (e :: ws) (.case n tL tR) := by
  have hpush := worklistWeight_pushPos_le ws o B
  have hA := objectWeight_pos A
  have hn : 0 < NegNeu.size n := by
    cases n <;> simp [NegNeu.size] <;> omega
  simp only [encodeFuel, encodeMeasure, worklistWeight_cons, hty, objectWeight,
    InvTm.size, InvTm.posPushBudget]
  omega

/-! ### Encoding -/

mutual
/--
Shared continuation for a forced left-coprod: encode the two branches under
split origins and assemble `.case e.origin _ _`. Used by both successful peel
and left-η for `.unit`, so `case_unit` is an `Option` identity.
-/
def encodeLeftCoprodBranches (fuel : Nat) {Γ : Ctx sig}
    (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (e : PosEntry sig)
    {L R A : Object sig.nBases}
    (tL : InvTm (Γ ▻ L) A) (tR : InvTm (Γ ▻ R) A) :
    Option (ICCCode Γ A) :=
  let ws' := ws.tail
  let εL : OriginEnv (Γ ▻ L) :=
    OriginEnv.weaken (A := L) ε (.split e.origin false)
  let εR : OriginEnv (Γ ▻ R) :=
    OriginEnv.weaken (A := R) ε (.split e.origin true)
  let wsL := pushPos ws' (.split e.origin false) L
  let wsR := pushPos ws' (.split e.origin true) R
  match encodeICCGo fuel wsL εL domNest obsSlot tL,
        encodeICCGo fuel wsR εR domNest obsSlot tR with
  | some cL, some cR => some (.case e.origin cL cR)
  | _, _ => none

/--
Worklist-driven encode, bounded by `encodeMeasure`.

* `domNest` — next λ-domain origin index (`Origin.dom`)
* `obsSlot` — next observation origin index (`Origin.obs`)
-/
def encodeICCGo (fuel : Nat) {Γ : Ctx sig} (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat) {A : Object sig.nBases} :
    InvTm Γ A → Option (ICCCode Γ A)
  | t =>
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match forcedRule ws A with
      | .moveStable _ =>
          encodeICCGo fuel ws.tail ε domNest obsSlot t
      | .rightUnit =>
          if h : A = (.unit : Object sig.nBases) then
            if peelUnit (h ▸ t) then some (h ▸ .unit) else none
          else none
      | .rightProd L R =>
          if h : A = (.prod L R : Object sig.nBases) then
            match peelPair (h ▸ t) with
            | some (t₁, t₂) =>
                match encodeICCGo fuel ws ε domNest obsSlot t₁,
                      encodeICCGo fuel ws ε domNest obsSlot t₂ with
                | some c₁, some c₂ => some (h ▸ .pair c₁ c₂)
                | _, _ => none
            | none =>
                match h ▸ t with
                | .foc f =>
                    match encodeFocGo fuel ws ε domNest obsSlot f with
                    | some c => some (h ▸ c)
                    | none => none
                | _ => none
          else none
      | .rightExp Arg Ret =>
          if h : A = (.exp Arg Ret : Object sig.nBases) then
            match peelLam (h ▸ t) with
            | some body =>
                let o := Origin.dom (sig := sig) domNest
                let ε' : OriginEnv (Γ ▻ Arg) :=
                  OriginEnv.weaken (A := Arg) ε o
                let ws' := pushPos ws o Arg
                match encodeICCGo fuel ws' ε' (domNest + 1) obsSlot body with
                | some c => some (h ▸ .lam c)
                | none => none
            | none =>
                match h ▸ t with
                | .foc f =>
                    match encodeFocGo fuel ws ε domNest obsSlot f with
                    | some c => some (h ▸ c)
                    | none => none
                | _ => none
          else none
      | .leftCoprod e L R =>
          match peelCaseOuter ε e.origin t with
          | some ⟨L', R', _n, tL, tR⟩ =>
              if hL : L' = L then
                if hR : R' = R then
                  let tL' : InvTm (Γ ▻ L) A := hL ▸ tL
                  let tR' : InvTm (Γ ▻ R) A := hR ▸ tR
                  encodeLeftCoprodBranches fuel ws ε domNest obsSlot e tL' tR'
                else none
              else none
          | none =>
              -- Left-η for `.unit`: same branch continuation as a successful peel.
              match t with
              | .unit =>
                  match OriginEnv.find? ε e.origin with
                  | some ⟨ty, x⟩ =>
                      if hty : ty = (.coprod L R : Object sig.nBases) then
                        if ε x == e.origin then
                          encodeLeftCoprodBranches fuel ws ε domNest obsSlot e
                            (.unit : InvTm (Γ ▻ L) .unit)
                            (.unit : InvTm (Γ ▻ R) .unit)
                        else none
                      else none
                  | none => none
              | _ => none
      | .leftNever e =>
          -- Code keyed by forced origin (`abort_eq`); scrutinee spine erased.
          match t with
          | .abort _ => some (.abort e.origin)
          | _ => none
      | .focus =>
          match t with
          | .foc f => encodeFocGo fuel ws ε domNest obsSlot f
          | _ => none

def encodeFocGo (fuel : Nat) {Γ : Ctx sig} (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat) {A : Object sig.nBases} :
    FocTm Γ A → Option (ICCCode Γ A)
  | .pos (.done p) => some (.foc (.pos p))
  | .neg (.done n) => some (.foc (.neg n))
  | .letPos (P := P) n t =>
      match fuel with
      | 0 => none
      | fuel + 1 =>
          let o := Origin.obs (sig := sig) obsSlot
          let ε' : OriginEnv (Γ ▻ P) := OriginEnv.weaken (A := P) ε o
          let ws' := pushPos ws o P
          match encodeICCGo fuel ws' ε' domNest (obsSlot + 1) t with
          | some c => some (.foc (.letPos o n c))
          | none => none
  | .sat (.mk _ t) =>
      match fuel with
      | 0 => none
      | fuel + 1 =>
          match encodeICCGo fuel ws ε domNest obsSlot t with
          | some c => some (.foc (.body c))
          | none => none
end

/-- Encode under a phase-entry origin environment.

Fueled by the derived adequate bound `encodeFuel` (measure + letPos budget +
`2 * size`). Commute pairs may have unequal fuels; lift Go-level agreement to
`encodeICC` via `max` and successful-result monotonicity. Positive `letPos` is
why measure alone is not enough (`encodeMeasure_lt_pushPos_of_pos`).

No fixed public constant (e.g. 2048).
-/
def encodeICC {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (t : InvTm Γ A) : Option (ICCCode Γ A) :=
  let ws := OriginEnv.posWorklist ε
  encodeICCGo (encodeFuel ws t) ws ε 0 0 t

/-- Encode with default oldest-first hyp origins for an `ofHyps` context. -/
def encodeICCHyps {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A) : Option (ICCCode (Ctx.ofHyps hyps) A) :=
  encodeICC (OriginEnv.ofHyps hyps) t

/-- Compare two invertible terms by ordered-phase codes when both encode. -/
def encodeICCEq {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (t u : InvTm Γ A) : Bool :=
  match encodeICC ε t, encodeICC ε u with
  | some c, some d => ICCCode.beq c d
  | _, _ => false

/-! ### Theorem interfaces -/

/-- Membership in the encoder domain (explicit; not a silent `isSome` guard). -/
def EncodableICC {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (t : InvTm Γ A) : Prop :=
  (encodeICC ε t).isSome

theorem EncodableICC.iff_isSome {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (t : InvTm Γ A) :
    EncodableICC ε t ↔ (encodeICC ε t).isSome := Iff.rfl

/-- Prefer this form in proofs: a concrete code witness, not bare `isSome`. -/
theorem EncodableICC.exists {Γ : Ctx sig} {A : Object sig.nBases}
    {ε : OriginEnv Γ} {t : InvTm Γ A} (h : EncodableICC ε t) :
    ∃ c, encodeICC ε t = some c :=
  Option.isSome_iff_exists.mp h

theorem EncodableICC.of_eq_some {Γ : Ctx sig} {A : Object sig.nBases}
    {ε : OriginEnv Γ} {t : InvTm Γ A} {c : ICCCode Γ A}
    (h : encodeICC ε t = some c) : EncodableICC ε t := by
  simp only [EncodableICC, h, Option.isSome_some]

/-- Extract the unique code when encodable. -/
def EncodableICC.get {Γ : Ctx sig} {A : Object sig.nBases}
    {ε : OriginEnv Γ} {t : InvTm Γ A} (h : EncodableICC ε t) : ICCCode Γ A :=
  (encodeICC ε t).get (by simpa [EncodableICC] using h)

theorem EncodableICC.get_eq {Γ : Ctx sig} {A : Object sig.nBases}
    {ε : OriginEnv Γ} {t : InvTm Γ A} (h : EncodableICC ε t) :
    encodeICC ε t = some h.get := by
  simp only [EncodableICC.get]
  exact Option.eq_some_of_isSome _

/--
Strong ICC step on codes: encodability is preserved both ways, and codes agree
whenever either side is encodable.

`encodeICC ε t = encodeICC ε u` (as `Option`) implies this. The published
characterization must never treat `none = none` as ICC equality.
-/
def EncodeIccStep {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (t u : InvTm Γ A) : Prop :=
  (EncodableICC ε t ↔ EncodableICC ε u) ∧
    (EncodableICC ε t → encodeICC ε t = encodeICC ε u)

theorem EncodeIccStep.of_option_eq {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) {t u : InvTm Γ A}
    (h : encodeICC ε t = encodeICC ε u) : EncodeIccStep ε t u := by
  refine ⟨?_, fun _ => h⟩
  simp only [EncodableICC, h]

theorem EncodeIccStep.symm {Γ : Ctx sig} {A : Object sig.nBases}
    {ε : OriginEnv Γ} {t u : InvTm Γ A}
    (h : EncodeIccStep ε t u) : EncodeIccStep ε u t :=
  ⟨h.1.symm, fun hu => by
    have ht := h.1.mpr hu
    exact (h.2 ht).symm⟩

theorem EncodeIccStep.either {Γ : Ctx sig} {A : Object sig.nBases}
    {ε : OriginEnv Γ} {t u : InvTm Γ A}
    (h : EncodeIccStep ε t u)
    (hex : EncodableICC ε t ∨ EncodableICC ε u) :
    EncodableICC ε t ∧ EncodableICC ε u ∧ encodeICC ε t = encodeICC ε u := by
  cases hex with
  | inl ht => exact ⟨ht, h.1.mp ht, h.2 ht⟩
  | inr hu =>
      have ht := h.1.mpr hu
      exact ⟨ht, hu, h.2 ht⟩

/--
Transitivity: domain preservation of the first step supplies the intermediate
encodability needed to chain code equalities. No external `EncodableICC u`
hypothesis.
-/
theorem EncodeIccStep.trans {Γ : Ctx sig} {A : Object sig.nBases}
    {ε : OriginEnv Γ} {t u v : InvTm Γ A}
    (htu : EncodeIccStep ε t u) (huv : EncodeIccStep ε u v) :
    EncodeIccStep ε t v := by
  refine ⟨htu.1.trans huv.1, fun ht => ?_⟩
  have hu : EncodableICC ε u := htu.1.mp ht
  exact (htu.2 ht).trans (huv.2 hu)

theorem EncodeIccStep.refl {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (t : InvTm Γ A) : EncodeIccStep ε t t :=
  EncodeIccStep.of_option_eq ε rfl

/--
Primary characterization on the encoder domain — both directions.

* **Invariance** (`EncodeIccInvariantGoal`): `ICCEq t u → EncodeIccStep ε t u`
  (hence codes agree when either encodes).
* **Reflection / common-code soundness** (`EncodeIccReflectGoal`): same
  successful code implies `ICCEq`. This is the content of “rigidity” for
  design E — not merely that encode is a function.

Both sides must be encodable for the published iff — `none = none` is never
ICC equality. `EncodeTotal` discharges encodability on the valid fragment.
-/
def IccEqIffEncodeEqGoal : Prop :=
  ∀ {Γ : Ctx sig} {A : Object sig.nBases} (ε : OriginEnv Γ) (t u : InvTm Γ A),
    EncodableICC ε t → EncodableICC ε u →
      (ICCEq t u ↔ encodeICC ε t = encodeICC ε u)

/--
Reflection: a shared successful code implies ICC equality.

Peel soundness (`peelCaseOuter_icc`) supports the inductive argument that each
encodable term is ICC-equivalent to the ordered phase its code denotes; two
terms with the same code are then ICC-equivalent to each other.
-/
def EncodeIccReflectGoal : Prop :=
  ∀ {Γ : Ctx sig} {A : Object sig.nBases} (ε : OriginEnv Γ)
    {t u : InvTm Γ A} {c : ICCCode Γ A},
    encodeICC ε t = some c → encodeICC ε u = some c → ICCEq t u

/--
Rigidity for design E = reflection/common-code soundness (`EncodeIccReflectGoal`).
Determinism of `encodeICC` alone is not rigidity.
-/
abbrev EncodeIccRigidityGoal : Prop := EncodeIccReflectGoal (sig := sig)


/-! ### EncodeReady: syntactic totality precondition

`WellInv` alone is not enough: unique-order encode can return structural `none`
when the term is not aligned with `forcedRule`. `EncodeReady` is the stronger
alignment predicate used by `ValidEncodeFragment` / `EncodeTotal`.
-/

mutual
/-- Term is ready for unique-order encode under worklist `ws`. -/
inductive EncodeReady : ∀ {Γ : Ctx sig} (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat) {A : Object sig.nBases},
    InvTm Γ A → Prop where
  | moveStable {Γ A} {e : PosEntry sig} {ws : List (PosEntry sig)}
      {ε : OriginEnv Γ} {domNest obsSlot : Nat} {t : InvTm Γ A}
      (hfr : forcedRule (e :: ws) A = .moveStable e)
      (h : EncodeReady ws ε domNest obsSlot t) :
      EncodeReady (e :: ws) ε domNest obsSlot t
  | leftNever {Γ A} {e : PosEntry sig} {_ws : List (PosEntry sig)}
      {_ε : OriginEnv Γ} {_domNest _obsSlot : Nat} {n : NegNeu Γ .never}
      (hty : e.ty = .never) :
      EncodeReady (e :: _ws) _ε _domNest _obsSlot (.abort (A := A) n)
  | rightUnit {Γ} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat}
      (hfr : forcedRule ws (.unit : Object sig.nBases) = .rightUnit) :
      EncodeReady ws ε domNest obsSlot (.unit (Γ := Γ))
  | rightProd_pair {Γ L R} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {t : InvTm Γ L} {u : InvTm Γ R}
      (hfr : forcedRule ws (.prod L R) = .rightProd L R)
      (ht : EncodeReady ws ε domNest obsSlot t)
      (hu : EncodeReady ws ε domNest obsSlot u) :
      EncodeReady ws ε domNest obsSlot (.pair t u)
  | rightProd_foc {Γ L R} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {f : FocTm Γ (.prod L R)}
      (hfr : forcedRule ws (.prod L R) = .rightProd L R)
      (hf : EncodeReadyFoc ws ε domNest obsSlot f) :
      EncodeReady ws ε domNest obsSlot (.foc f)
  | rightExp_lam {Γ Arg Ret} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {body : InvTm (Γ ▻ Arg) Ret}
      (hfr : forcedRule ws (.exp Arg Ret) = .rightExp Arg Ret)
      (hb : EncodeReady
        (pushPos ws (.dom (sig := sig) domNest) Arg)
        (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) domNest))
        (domNest + 1) obsSlot body) :
      EncodeReady ws ε domNest obsSlot (.lam body)
  | rightExp_foc {Γ Arg Ret} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {f : FocTm Γ (.exp Arg Ret)}
      (hfr : forcedRule ws (.exp Arg Ret) = .rightExp Arg Ret)
      (hf : EncodeReadyFoc ws ε domNest obsSlot f) :
      EncodeReady ws ε domNest obsSlot (.foc f)
  | leftCoprod_peel {Γ A L R} {e : PosEntry sig} {ws : List (PosEntry sig)}
      {ε : OriginEnv Γ} {domNest obsSlot : Nat}
      {n : NegNeu Γ (.coprod L R)}
      {tL : InvTm (Γ ▻ L) A} {tR : InvTm (Γ ▻ R) A} {t : InvTm Γ A}
      (hfr : forcedRule (e :: ws) A = .leftCoprod e L R)
      (hpeel : peelCaseOuter ε e.origin t = some ⟨L, R, n, tL, tR⟩)
      (hL : EncodeReady
        (pushPos ws (.split e.origin false) L)
        (OriginEnv.weaken (A := L) ε (.split e.origin false))
        domNest obsSlot tL)
      (hR : EncodeReady
        (pushPos ws (.split e.origin true) R)
        (OriginEnv.weaken (A := R) ε (.split e.origin true))
        domNest obsSlot tR) :
      EncodeReady (e :: ws) ε domNest obsSlot t
  | leftCoprod_unitEta {Γ L R} {e : PosEntry sig} {ws : List (PosEntry sig)}
      {ε : OriginEnv Γ} {domNest obsSlot : Nat}
      {x : Var Γ (.coprod L R)}
      (hfr : forcedRule (e :: ws) (.unit : Object sig.nBases) = .leftCoprod e L R)
      (hfind : OriginEnv.find? ε e.origin = some ⟨.coprod L R, x⟩)
      (hit : (ε x == e.origin) = true)
      (hL : EncodeReady
        (pushPos ws (.split e.origin false) L)
        (OriginEnv.weaken (A := L) ε (.split e.origin false))
        domNest obsSlot (.unit : InvTm (Γ ▻ L) .unit))
      (hR : EncodeReady
        (pushPos ws (.split e.origin true) R)
        (OriginEnv.weaken (A := R) ε (.split e.origin true))
        domNest obsSlot (.unit : InvTm (Γ ▻ R) .unit)) :
      EncodeReady (e :: ws) ε domNest obsSlot (.unit (Γ := Γ))
  | focus {Γ A} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {f : FocTm Γ A}
      (hfr : forcedRule ws A = .focus)
      (hf : EncodeReadyFoc ws ε domNest obsSlot f) :
      EncodeReady ws ε domNest obsSlot (.foc f)

/-- Focused counterpart of `EncodeReady`. -/
inductive EncodeReadyFoc : ∀ {Γ : Ctx sig} (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat) {A : Object sig.nBases},
    FocTm Γ A → Prop where
  | pos {Γ A} {_ws : List (PosEntry sig)} {_ε : OriginEnv Γ}
      {_domNest _obsSlot : Nat} {p : PosNeu Γ A} :
      EncodeReadyFoc _ws _ε _domNest _obsSlot (.pos (.done p))
  | neg {Γ A} {_ws : List (PosEntry sig)} {_ε : OriginEnv Γ}
      {_domNest _obsSlot : Nat} {n : NegNeu Γ A} :
      EncodeReadyFoc _ws _ε _domNest _obsSlot (.neg (.done n))
  | letPos {Γ P A} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {n : NegNeu Γ P} {t : InvTm (Γ ▻ P) A}
      (ht : EncodeReady
        (pushPos ws (.obs (sig := sig) obsSlot) P)
        (OriginEnv.weaken (A := P) ε (.obs (sig := sig) obsSlot))
        domNest (obsSlot + 1) t) :
      EncodeReadyFoc ws ε domNest obsSlot (.letPos n t)
  | sat {Γ A} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {s : Schedule sig.nBases} {t : InvTm Γ A}
      (ht : EncodeReady ws ε domNest obsSlot t) :
      EncodeReadyFoc ws ε domNest obsSlot (.sat (.mk s t))
end

/-! ### Peel-free fragment of `EncodeReady`

Omits `leftCoprod_peel` / `leftCoprod_unitEta`. Enough to rekey newest-hyp → obs
and wrap atom `letPos` when the phase worklist is base-only (`moveStable`).
-/

mutual
/-- `EncodeReady` without left-coprod peel / unit-η. -/
inductive EncodeReadyNoPeel : ∀ {Γ : Ctx sig} (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat) {A : Object sig.nBases},
    InvTm Γ A → Prop where
  | moveStable {Γ A} {e : PosEntry sig} {ws : List (PosEntry sig)}
      {ε : OriginEnv Γ} {domNest obsSlot : Nat} {t : InvTm Γ A}
      (hfr : forcedRule (e :: ws) A = .moveStable e)
      (h : EncodeReadyNoPeel ws ε domNest obsSlot t) :
      EncodeReadyNoPeel (e :: ws) ε domNest obsSlot t
  | leftNever {Γ A} {e : PosEntry sig} {_ws : List (PosEntry sig)}
      {_ε : OriginEnv Γ} {_domNest _obsSlot : Nat} {n : NegNeu Γ .never}
      (hty : e.ty = .never) :
      EncodeReadyNoPeel (e :: _ws) _ε _domNest _obsSlot (.abort (A := A) n)
  | rightUnit {Γ} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat}
      (hfr : forcedRule ws (.unit : Object sig.nBases) = .rightUnit) :
      EncodeReadyNoPeel ws ε domNest obsSlot (.unit (Γ := Γ))
  | rightProd_pair {Γ L R} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {t : InvTm Γ L} {u : InvTm Γ R}
      (hfr : forcedRule ws (.prod L R) = .rightProd L R)
      (ht : EncodeReadyNoPeel ws ε domNest obsSlot t)
      (hu : EncodeReadyNoPeel ws ε domNest obsSlot u) :
      EncodeReadyNoPeel ws ε domNest obsSlot (.pair t u)
  | rightProd_foc {Γ L R} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {f : FocTm Γ (.prod L R)}
      (hfr : forcedRule ws (.prod L R) = .rightProd L R)
      (hf : EncodeReadyFocNoPeel ws ε domNest obsSlot f) :
      EncodeReadyNoPeel ws ε domNest obsSlot (.foc f)
  | rightExp_lam {Γ Arg Ret} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {body : InvTm (Γ ▻ Arg) Ret}
      (hfr : forcedRule ws (.exp Arg Ret) = .rightExp Arg Ret)
      (hb : EncodeReadyNoPeel
        (pushPos ws (.dom (sig := sig) domNest) Arg)
        (OriginEnv.weaken (A := Arg) ε (.dom (sig := sig) domNest))
        (domNest + 1) obsSlot body) :
      EncodeReadyNoPeel ws ε domNest obsSlot (.lam body)
  | rightExp_foc {Γ Arg Ret} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {f : FocTm Γ (.exp Arg Ret)}
      (hfr : forcedRule ws (.exp Arg Ret) = .rightExp Arg Ret)
      (hf : EncodeReadyFocNoPeel ws ε domNest obsSlot f) :
      EncodeReadyNoPeel ws ε domNest obsSlot (.foc f)
  | focus {Γ A} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {f : FocTm Γ A}
      (hfr : forcedRule ws A = .focus)
      (hf : EncodeReadyFocNoPeel ws ε domNest obsSlot f) :
      EncodeReadyNoPeel ws ε domNest obsSlot (.foc f)

/-- Focused counterpart of `EncodeReadyNoPeel`. -/
inductive EncodeReadyFocNoPeel : ∀ {Γ : Ctx sig} (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) (domNest obsSlot : Nat) {A : Object sig.nBases},
    FocTm Γ A → Prop where
  | pos {Γ A} {_ws : List (PosEntry sig)} {_ε : OriginEnv Γ}
      {_domNest _obsSlot : Nat} {p : PosNeu Γ A} :
      EncodeReadyFocNoPeel _ws _ε _domNest _obsSlot (.pos (.done p))
  | neg {Γ A} {_ws : List (PosEntry sig)} {_ε : OriginEnv Γ}
      {_domNest _obsSlot : Nat} {n : NegNeu Γ A} :
      EncodeReadyFocNoPeel _ws _ε _domNest _obsSlot (.neg (.done n))
  | letPos {Γ P A} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {n : NegNeu Γ P} {t : InvTm (Γ ▻ P) A}
      (ht : EncodeReadyNoPeel
        (pushPos ws (.obs (sig := sig) obsSlot) P)
        (OriginEnv.weaken (A := P) ε (.obs (sig := sig) obsSlot))
        domNest (obsSlot + 1) t) :
      EncodeReadyFocNoPeel ws ε domNest obsSlot (.letPos n t)
  | sat {Γ A} {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
      {domNest obsSlot : Nat} {s : Schedule sig.nBases} {t : InvTm Γ A}
      (ht : EncodeReadyNoPeel ws ε domNest obsSlot t) :
      EncodeReadyFocNoPeel ws ε domNest obsSlot (.sat (.mk s t))
end

theorem encodeReady_of_noPeel {Γ : Ctx sig} {A : Object sig.nBases}
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {domNest obsSlot : Nat} {t : InvTm Γ A}
    (h : EncodeReadyNoPeel ws ε domNest obsSlot t) :
    EncodeReady ws ε domNest obsSlot t := by
  revert A ws ε domNest obsSlot t
  refine EncodeReadyNoPeel.rec
    (motive_1 := fun {Γ} ws ε d o {A} t _ => EncodeReady ws ε d o t)
    (motive_2 := fun {Γ} ws ε d o {A} f _ => EncodeReadyFoc ws ε d o f)
    ?ms ?ln ?ru ?rp ?rpf ?re ?ref ?fo ?pos ?neg ?lp ?sat
  case ms => intros; exact .moveStable ‹_› ‹_›
  case ln => intros; exact .leftNever ‹_›
  case ru => intros; exact .rightUnit ‹_›
  case rp => intros; exact .rightProd_pair ‹_› ‹_› ‹_›
  case rpf => intros; exact .rightProd_foc ‹_› ‹_›
  case re => intros; exact .rightExp_lam ‹_› ‹_›
  case ref => intros; exact .rightExp_foc ‹_› ‹_›
  case fo => intros; exact .focus ‹_› ‹_›
  case pos => intros; exact .pos
  case neg => intros; exact .neg
  case lp => intros; exact .letPos ‹_›
  case sat => intros; exact .sat ‹_›

theorem encodeReadyFoc_of_noPeel {Γ : Ctx sig} {A : Object sig.nBases}
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ}
    {domNest obsSlot : Nat} {f : FocTm Γ A}
    (h : EncodeReadyFocNoPeel ws ε domNest obsSlot f) :
    EncodeReadyFoc ws ε domNest obsSlot f := by
  revert A ws ε domNest obsSlot f
  refine EncodeReadyFocNoPeel.rec
    (motive_1 := fun {Γ} ws ε d o {A} t _ => EncodeReady ws ε d o t)
    (motive_2 := fun {Γ} ws ε d o {A} f _ => EncodeReadyFoc ws ε d o f)
    ?ms ?ln ?ru ?rp ?rpf ?re ?ref ?fo ?pos ?neg ?lp ?sat
  case ms => intros; exact .moveStable ‹_› ‹_›
  case ln => intros; exact .leftNever ‹_›
  case ru => intros; exact .rightUnit ‹_›
  case rp => intros; exact .rightProd_pair ‹_› ‹_› ‹_›
  case rpf => intros; exact .rightProd_foc ‹_› ‹_›
  case re => intros; exact .rightExp_lam ‹_› ‹_›
  case ref => intros; exact .rightExp_foc ‹_› ‹_›
  case fo => intros; exact .focus ‹_› ‹_›
  case pos => intros; exact .pos
  case neg => intros; exact .neg
  case lp => intros; exact .letPos ‹_›
  case sat => intros; exact .sat ‹_›

end Equality
end Gimbal
