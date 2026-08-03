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
  | _, _, _, _, .case o₁ t u, .case o₂ v w =>
      o₁ == o₂ && ICCCode.beq t v && ICCCode.beq u w
  | _, _, _, _, .abort o₁, .abort o₂ => o₁ == o₂
  | _, _, _, _, .foc f, .foc g => FocCode.beq f g
  | _, _, _, _, _, _ => false

def FocCode.beq : {Γ Δ : Ctx sig} → {A B : Object sig.nBases} →
    FocCode Γ A → FocCode Δ B → Bool
  | _, _, _, _, .pos p, .pos q => PosNeu.beq p q
  | _, _, _, _, .neg n, .neg m => NegNeu.beq n m
  | _, _, _, _, .letPos o₁ _n t, .letPos o₂ _m u =>
      o₁ == o₂ && ICCCode.beq t u
  | _, _, _, _, .body t, .body u => ICCCode.beq t u
  | _, _, _, _, _, _ => false
end

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
        -- WIP (`OriginCollisionFree`): same λ-binder placeholder as encode.
        let ε' : OriginEnv (Γ ▻ Arg) :=
          OriginEnv.weaken (A := Arg) ε (.split (.hyp 0) false)
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
/-- Worklist-driven encode, bounded by `encodeMeasure`. -/
def encodeICCGo (fuel : Nat) {Γ : Ctx sig} (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) {A : Object sig.nBases} :
    InvTm Γ A → Option (ICCCode Γ A)
  | t =>
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match forcedRule ws A with
      | .moveStable _ =>
          encodeICCGo fuel ws.tail ε t
      | .rightUnit =>
          if h : A = (.unit : Object sig.nBases) then
            if peelUnit (h ▸ t) then some (h ▸ .unit) else none
          else none
      | .rightProd L R =>
          if h : A = (.prod L R : Object sig.nBases) then
            match peelPair (h ▸ t) with
            | some (t₁, t₂) =>
                match encodeICCGo fuel ws ε t₁, encodeICCGo fuel ws ε t₂ with
                | some c₁, some c₂ => some (h ▸ .pair c₁ c₂)
                | _, _ => none
            | none =>
                match h ▸ t with
                | .foc f =>
                    match encodeFocGo fuel ws ε f with
                    | some c => some (h ▸ c)
                    | none => none
                | _ => none
          else none
      | .rightExp Arg Ret =>
          if h : A = (.exp Arg Ret : Object sig.nBases) then
            match peelLam (h ▸ t) with
            | some body =>
                -- WIP (`OriginCollisionFree`): λ-domain binders need a dedicated
                -- origin; `.split (.hyp 0) false` collides with a real hyp-0 split.
                let ε' : OriginEnv (Γ ▻ Arg) :=
                  OriginEnv.weaken (A := Arg) ε (.split (.hyp 0) false)
                match encodeICCGo fuel ws ε' body with
                | some c => some (h ▸ .lam c)
                | none => none
            | none =>
                match h ▸ t with
                | .foc f =>
                    match encodeFocGo fuel ws ε f with
                    | some c => some (h ▸ c)
                    | none => none
                | _ => none
          else none
      | .leftCoprod e L R =>
          match peelCaseOuter ε e.origin t with
          | some ⟨L', R', _n, tL, tR⟩ =>
              if hL : L' = L then
                if hR : R' = R then
                  let ws' := ws.tail
                  let tL' : InvTm (Γ ▻ L) A := hL ▸ tL
                  let tR' : InvTm (Γ ▻ R) A := hR ▸ tR
                  let εL : OriginEnv (Γ ▻ L) :=
                    OriginEnv.weaken (A := L) ε (.split e.origin false)
                  let εR : OriginEnv (Γ ▻ R) :=
                    OriginEnv.weaken (A := R) ε (.split e.origin true)
                  let wsL := pushPos ws' (.split e.origin false) L
                  let wsR := pushPos ws' (.split e.origin true) R
                  match encodeICCGo fuel wsL εL tL',
                        encodeICCGo fuel wsR εR tR' with
                  | some cL, some cR => some (.case e.origin cL cR)
                  | _, _ => none
                else none
              else none
          | none => none
      | .leftNever e =>
          match t with
          | .abort (.var x) =>
              if ε x == e.origin then some (.abort e.origin) else none
          | .abort _ => some (.abort e.origin)
          | _ => none
      | .focus =>
          match t with
          | .foc f => encodeFocGo fuel ws ε f
          | _ => none

def encodeFocGo (fuel : Nat) {Γ : Ctx sig} (ws : List (PosEntry sig))
    (ε : OriginEnv Γ) {A : Object sig.nBases} :
    FocTm Γ A → Option (ICCCode Γ A)
  | .pos (.done p) => some (.foc (.pos p))
  | .neg (.done n) => some (.foc (.neg n))
  | .letPos (P := P) n t =>
      match fuel with
      | 0 => none
      | fuel + 1 =>
          -- WIP (`OriginCollisionFree`): every observation needs its canonical
          -- schedule slot. `Origin.obs 0` collapses all `letPos` binders and
          -- must be replaced before encode invariance / reference totality.
          let o := Origin.obs 0
          let ε' : OriginEnv (Γ ▻ P) := OriginEnv.weaken (A := P) ε o
          match encodeICCGo fuel ws ε' t with
          | some c => some (.foc (.letPos o n c))
          | none => none
  | .sat (.mk _ t) =>
      match fuel with
      | 0 => none
      | fuel + 1 =>
          match encodeICCGo fuel ws ε t with
          | some c => some (.foc (.body c))
          | none => none
end

/-- Encode under a phase-entry origin environment. -/
def encodeICC {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (t : InvTm Γ A) : Option (ICCCode Γ A) :=
  let ws := OriginEnv.posWorklist ε
  encodeICCGo (encodeMeasure ws A) ws ε t

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

/-- Primary M8F target once encode is total on well-focused saturated terms. -/
def IccEqIffEncodeEqGoal : Prop :=
  ∀ {Γ : Ctx sig} {A : Object sig.nBases} (ε : OriginEnv Γ) (t u : InvTm Γ A),
    (encodeICC ε t).isSome ∧ (encodeICC ε u).isSome →
      (ICCEq t u ↔ encodeICC ε t = encodeICC ε u)

/-- Every ICC generator preserves codes. -/
def EncodeIccInvariantGoal : Prop :=
  ∀ {Γ : Ctx sig} {A : Object sig.nBases} (ε : OriginEnv Γ)
    {t u : InvTm Γ A}, ICCEq t u → encodeICC ε t = encodeICC ε u

end Equality
end Gimbal
