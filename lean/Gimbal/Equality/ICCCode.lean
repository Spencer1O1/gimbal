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
    | .foc _ => none
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

/-- Encode under a phase-entry origin environment. -/
def encodeICC {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (t : InvTm Γ A) : Option (ICCCode Γ A) :=
  let ws := OriginEnv.posWorklist ε
  encodeICCGo (encodeMeasure ws A) ws ε 0 0 t

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
Primary characterization on the encoder domain.

Both sides must be encodable — `none = none` is never read as ICC equality.
On the valid fragment, `EncodeTotal` discharges the encodability hypotheses.
-/
def IccEqIffEncodeEqGoal : Prop :=
  ∀ {Γ : Ctx sig} {A : Object sig.nBases} (ε : OriginEnv Γ) (t u : InvTm Γ A),
    EncodableICC ε t → EncodableICC ε u →
      (ICCEq t u ↔ encodeICC ε t = encodeICC ε u)

end Equality
end Gimbal
