/-
  Stable origins for invertible-phase reification (Milestone 8F design E).

  An origin names a processable positive assumption independently of the raw
  de Bruijn index it currently occupies. Phase-entry hypotheses use their
  oldest-first slot; case splits record parent origin plus branch; saturation
  observations use the canonical schedule slot assigned at phase entry —
  never a constant such as `obs 0` for every `letPos` (see
  `OriginCollisionFree` in `Completeness.lean`).

  Origins are the orientation key for the unique-order subsystem: the worklist
  is sorted by `Origin.cmp`, never by `NegNeu.blt` / raw spines.
-/

import Gimbal.Equality.Algebra
import Gimbal.Equality.Focused
import Gimbal.Equality.Polarized

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Origins -/

/--
Stable identity of a binder introduced during an invertible phase.

* `hyp i` — phase-entry hypothesis at oldest-first index `i`
* `obs i` — saturation observation at canonical schedule slot `i`
* `dom i` — λ-domain binder at nesting depth `i` from phase entry
* `split o side` — payload binder from casing on `o`
  (`false` = left/`inl`, `true` = right/`inr`)
-/
inductive Origin (sig : Signature) : Type where
  | hyp (idx : Nat)
  | obs (slot : Nat)
  | dom (nesting : Nat)
  | split (parent : Origin sig) (side : Bool)
  deriving DecidableEq, Repr

/-- Total order used to force left-to-right processing of the worklist. -/
def Origin.cmp : Origin sig → Origin sig → Ordering
  | .hyp i, .hyp j => compare i j
  | .hyp _, _ => .lt
  | .obs _, .hyp _ => .gt
  | .obs i, .obs j => compare i j
  | .obs _, .dom _ => .lt
  | .obs _, .split .. => .lt
  | .dom _, .hyp _ => .gt
  | .dom _, .obs _ => .gt
  | .dom i, .dom j => compare i j
  | .dom _, .split .. => .lt
  | .split .., .hyp _ => .gt
  | .split .., .obs _ => .gt
  | .split .., .dom _ => .gt
  | .split p false, .split q false => Origin.cmp p q
  | .split p true, .split q true => Origin.cmp p q
  | .split p false, .split q true =>
      match Origin.cmp p q with
      | .eq => .lt
      | o => o
  | .split p true, .split q false =>
      match Origin.cmp p q with
      | .eq => .gt
      | o => o

def Origin.blt (o₁ o₂ : Origin sig) : Bool :=
  Origin.cmp o₁ o₂ == .lt

def Origin.ble (o₁ o₂ : Origin sig) : Bool :=
  let c := Origin.cmp o₁ o₂
  c == .lt || c == .eq

@[simp] theorem Origin.cmp_hyp_hyp (i j : Nat) :
    Origin.cmp (.hyp (sig := sig) i) (.hyp j) = compare i j := rfl

/-- `cmp` agrees with equality on the nose for identical constructors. -/
theorem Origin.cmp_self (o : Origin sig) : Origin.cmp o o = .eq := by
  induction o with
  | hyp i =>
      simp only [Origin.cmp]
      change compareOfLessAndEq i i = .eq
      simp [compareOfLessAndEq]
  | obs i =>
      simp only [Origin.cmp]
      change compareOfLessAndEq i i = .eq
      simp [compareOfLessAndEq]
  | dom i =>
      simp only [Origin.cmp]
      change compareOfLessAndEq i i = .eq
      simp [compareOfLessAndEq]
  | split p s ih => cases s <;> simp [Origin.cmp, ih]

/-! ### Origin environments -/

/--
Assignment of a stable origin to every variable in `Γ`.
`here` is the newest binder; phase-entry `hyp` indices remain oldest-first.
-/
def OriginEnv (Γ : Ctx sig) : Type :=
  ∀ {A : Object sig.nBases}, Var Γ A → Origin sig

namespace OriginEnv

def empty : OriginEnv (sig := sig) .empty :=
  fun x => nomatch x

/-- Extend under a new newest binder. -/
def snoc {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) : OriginEnv (Γ ▻ A)
  | _, .here => o
  | _, .there x => ε x

/--
Phase-entry environment: hypothesis `i` (oldest-first) gets `Origin.hyp i`.
Uses `Var.toRawIdx` (0 = newest) so `hypIdx = size - 1 - rawIdx`.
-/
def ofHyps (hyps : Array (Object sig.nBases)) : OriginEnv (Ctx.ofHyps hyps) :=
  fun {A} x => .hyp (hyps.size - 1 - Var.toRawIdx x)

/-- Transport origins along a renaming: look up after mapping the variable. -/
def rename {Γ Δ : Ctx sig} (ρ : Rename sig Γ Δ) (ε : OriginEnv Δ) :
    OriginEnv Γ
  | _, x => ε (ρ x)

/-- Origins after weakening: old bindings unchanged; new binder gets `o`. -/
def weaken {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) : OriginEnv (Γ ▻ A) :=
  OriginEnv.snoc ε o

/--
Exchange the two newest variables while each binding keeps its origin.
`Rename.exchange` is applied in the inverse direction (it is an involution).
-/
def exchange {Γ : Ctx sig} {A B : Object sig.nBases}
    (ε : OriginEnv (Γ ▻ A ▻ B)) : OriginEnv (Γ ▻ B ▻ A)
  | _, x => ε (Rename.exchange (A := B) (B := A) x)

@[simp] theorem snoc_here {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) :
    OriginEnv.snoc (A := A) ε o .here = o := rfl

@[simp] theorem snoc_there {Γ : Ctx sig} {A B : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) (x : Var Γ B) :
    OriginEnv.snoc (A := A) ε o (.there x) = ε x := rfl

theorem rename_id_apply {Γ : Ctx sig} (ε : OriginEnv Γ)
    {A : Object sig.nBases} (x : Var Γ A) :
    OriginEnv.rename (Rename.id (Γ := Γ)) ε x = ε x := rfl

theorem rename_comp_apply {Γ Δ Ε : Ctx sig}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) (ε : OriginEnv Ε)
    {A : Object sig.nBases} (x : Var Γ A) :
    OriginEnv.rename (Rename.comp ρ τ) ε x =
      OriginEnv.rename τ (OriginEnv.rename ρ ε) x := rfl

/-- Exchange is involutive on variables. -/
theorem exchange_exchange_var {Γ : Ctx sig} {A B C : Object sig.nBases}
    (x : Var (Γ ▻ A ▻ B) C) :
    Rename.exchange (A := B) (B := A)
        (Rename.exchange (A := A) (B := B) x) = x := by
  cases x with
  | here => rfl
  | there x =>
      cases x with
      | here => rfl
      | there _ => rfl

theorem exchange_involutive_apply {Γ : Ctx sig} {A B C : Object sig.nBases}
    (ε : OriginEnv (Γ ▻ A ▻ B)) (x : Var (Γ ▻ A ▻ B) C) :
    OriginEnv.exchange (A := B) (B := A)
        (OriginEnv.exchange (A := A) (B := B) ε) x = ε x := by
  simp only [OriginEnv.exchange]
  exact congrArg ε (exchange_exchange_var x)

/-- Weakening does not change origins of older variables. -/
theorem weaken_there {Γ : Ctx sig} {A B : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) (x : Var Γ B) :
    OriginEnv.weaken (A := A) ε o (.there x) = ε x :=
  rfl

/--
Exchanging the two newest binders never changes the origin of a variable
from the parent context.
-/
theorem exchange_preserves_older {Γ : Ctx sig} {A B C : Object sig.nBases}
    (ε : OriginEnv (Γ ▻ A ▻ B)) (x : Var Γ C) :
    OriginEnv.exchange (A := A) (B := B) ε (.there (.there x)) =
      ε (.there (.there x)) := by
  simp only [OriginEnv.exchange, Rename.exchange]

/-! ### Well-formed / collision-free origin environments -/

/--
Origins of live variables are pairwise distinct.
This is the formal `OriginCollisionFree` obligation from Milestone 8F:
distinct binders carry distinct origins under weaken / push.
-/
structure WellFormed {Γ : Ctx sig} (ε : OriginEnv Γ) : Prop where
  injective : ∀ {A B : Object sig.nBases} (x : Var Γ A) (y : Var Γ B),
    ε x = ε y → ∃ h : A = B, HEq x y

/-- Origin `o` is not carried by any live variable in `ε`. -/
def Fresh {Γ : Ctx sig} (ε : OriginEnv Γ) (o : Origin sig) : Prop :=
  ∀ {A : Object sig.nBases} (x : Var Γ A), ε x ≠ o

theorem WellFormed.empty :
    WellFormed (OriginEnv.empty : OriginEnv (Ctx.empty : Ctx sig)) where
  injective := fun x => nomatch x

theorem Fresh.empty (o : Origin sig) :
    Fresh (OriginEnv.empty : OriginEnv (Ctx.empty : Ctx sig)) o :=
  fun x => nomatch x

/-- Pushing a fresh origin preserves injectivity. -/
theorem WellFormed.weaken {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig)
    (hwf : WellFormed ε) (hfresh : Fresh ε o) :
    WellFormed (OriginEnv.weaken (A := A) ε o) where
  injective := by
    intro B C x y hxy
    cases x with
    | here =>
        cases y with
        | here => exact ⟨rfl, by trivial⟩
        | there y =>
            simp [OriginEnv.weaken, OriginEnv.snoc] at hxy
            exact False.elim (hfresh y hxy.symm)
    | there x =>
        cases y with
        | here =>
            simp [OriginEnv.weaken, OriginEnv.snoc] at hxy
            exact False.elim (hfresh x hxy)
        | there y =>
            simp [OriginEnv.weaken, OriginEnv.snoc] at hxy
            obtain ⟨hBC, hEq⟩ := hwf.injective x y hxy
            cases hBC
            cases hEq
            exact ⟨rfl, by trivial⟩

/-- A fresh origin remains fresh after pushing a different origin. -/
theorem Fresh.weaken {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (o o' : Origin sig)
    (hfresh : Fresh ε o') (hne : o ≠ o') :
    Fresh (OriginEnv.weaken (A := A) ε o) o' := by
  intro B x
  cases x with
  | here =>
      simp [OriginEnv.weaken, OriginEnv.snoc]
      exact hne
  | there y =>
      simpa [OriginEnv.weaken, OriginEnv.snoc] using hfresh y

/-- Restrict well-formedness to the parent context (drop newest binder). -/
theorem WellFormed.there {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv (Γ ▻ A)) (hwf : WellFormed ε) :
    WellFormed (fun {_B} x => ε (.there x)) where
  injective := fun {_ _} u v huv => by
    obtain ⟨hBC, hEq⟩ := hwf.injective (.there u) (.there v) huv
    cases hBC
    cases hEq
    exact ⟨rfl, by trivial⟩

end OriginEnv

/-! ### Positive worklist entries -/

/-- A processable positive assumption: its origin and formula. -/
structure PosEntry (sig : Signature) where
  origin : Origin sig
  ty : Object sig.nBases
  deriving DecidableEq, Repr

/-- Positive entries collected newest-first (before `Origin.ble` sort). -/
def OriginEnv.posCollect {Γ : Ctx sig} (ε : OriginEnv Γ) : List (PosEntry sig) :=
  let rec collect : (Δ : Ctx sig) → OriginEnv Δ → List (PosEntry sig)
    | .empty, _ => []
    | .snoc Δ A, ε' =>
        let rest := collect Δ (fun {A} x => ε' (Var.there x))
        if objectPolarity A == .pos then
          { origin := ε' .here, ty := A } :: rest
        else
          rest
  collect Γ ε

/-- Collect positively polarized variables as a worklist ordered by `Origin.cmp`. -/
def OriginEnv.posWorklist {Γ : Ctx sig} (ε : OriginEnv Γ) : List (PosEntry sig) :=
  (OriginEnv.posCollect ε).mergeSort fun e₁ e₂ => Origin.ble e₁.origin e₂.origin

theorem OriginEnv.posWorklist_eq_mergeSort {Γ : Ctx sig} (ε : OriginEnv Γ) :
    OriginEnv.posWorklist ε =
      (OriginEnv.posCollect ε).mergeSort fun e₁ e₂ =>
        Origin.ble e₁.origin e₂.origin :=
  rfl

/-- Hyp origins compare by oldest-first index. -/
theorem Origin.ble_hyp_hyp (i j : Nat) :
    Origin.ble (.hyp (sig := sig) i) (.hyp j) = true ↔ i ≤ j := by
  simp only [Origin.ble, Origin.cmp_hyp_hyp, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro h
    cases h with
    | inl hlt =>
        exact Nat.le_of_lt (Nat.compare_eq_lt.mp hlt)
    | inr heq =>
        exact Nat.le_of_eq (Nat.compare_eq_eq.mp heq)
  · intro hle
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl (Nat.compare_eq_lt.mpr hlt)
    · exact Or.inr (Nat.compare_eq_eq.mpr heq)

/-- Resolve an origin to the unique variable currently carrying it, if any. -/
def OriginEnv.find? {Γ : Ctx sig} (ε : OriginEnv Γ) (o : Origin sig) :
    Option ((A : Object sig.nBases) × Var Γ A) :=
  let rec go : (Δ : Ctx sig) → OriginEnv Δ → Option ((A : Object sig.nBases) × Var Δ A)
    | .empty, _ => none
    | .snoc Δ A, ε' =>
        if ε' (.here : Var (Δ ▻ A) A) == o then
          some ⟨A, .here⟩
        else
          (go Δ (fun {B} x => ε' (Var.there x))).map fun ⟨B, x⟩ =>
            ⟨B, .there x⟩
  go Γ ε

/-! ### `ofHyps` under `push` -/

theorem Var.toRawIdx_cast {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (h : Γ = Δ) (x : Var Γ A) :
    Var.toRawIdx (h ▸ x) = Var.toRawIdx x := by
  induction h
  rfl

theorem Var.toRawIdx_here {Γ : Ctx sig} {A : Object sig.nBases} :
    Var.toRawIdx (.here : Var (Γ ▻ A) A) = 0 := rfl

theorem Var.toRawIdx_there {Γ : Ctx sig} {A B : Object sig.nBases}
    (x : Var Γ A) :
    Var.toRawIdx (.there (B := B) x) = Var.toRawIdx x + 1 := rfl

/-- Variables are determined by de Bruijn index (local copy for origin WF). -/
theorem Var.eq_of_toRawIdx' {Γ : Ctx sig} :
    ∀ {A B : Object sig.nBases} (x : Var Γ A) (y : Var Γ B),
      x.toRawIdx = y.toRawIdx → A = B ∧ HEq x y
  | _, _, .here, .here, _ => ⟨rfl, HEq.refl _⟩
  | _, _, .here, .there _, h => by simp [Var.toRawIdx] at h
  | _, _, .there _, .here, h => by simp [Var.toRawIdx] at h
  | _, _, .there x, .there y, h => by
      obtain ⟨rfl, hxy⟩ := Var.eq_of_toRawIdx' x y (by simpa [Var.toRawIdx] using h)
      cases eq_of_heq hxy
      exact ⟨rfl, HEq.refl _⟩

/-- The newest variable of `ofHyps (hyps.push P)`. -/
def OriginEnv.herePush (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases) : Var (Ctx.ofHyps (hyps.push P)) P :=
  (Ctx.ofHyps_push hyps P).symm ▸ .here

/-- Newest binder under `ofHyps (hyps.push P)` carries `hyp hyps.size`. -/
theorem OriginEnv.ofHyps_here_push (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases) :
    OriginEnv.ofHyps (hyps.push P) (OriginEnv.herePush hyps P) =
      Origin.hyp (sig := sig) hyps.size := by
  unfold OriginEnv.herePush OriginEnv.ofHyps
  apply congrArg Origin.hyp
  have hraw :=
    Var.toRawIdx_cast (Ctx.ofHyps_push hyps P).symm
      (.here : Var (Ctx.ofHyps hyps ▻ P) P)
  rw [hraw, Var.toRawIdx_here, Array.size_push]
  exact Nat.sub_zero _

/--
`ofHyps (hyps.push P)` agrees with `weaken (ofHyps hyps) (.hyp hyps.size)`
on the pushed context (via `Ctx.ofHyps_push`).
-/
theorem OriginEnv.ofHyps_push_eq_weaken_hyp (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases) {A : Object sig.nBases}
    (x : Var (Ctx.ofHyps hyps ▻ P) A) :
    OriginEnv.ofHyps (hyps.push P)
        ((Ctx.ofHyps_push hyps P).symm ▸ x) =
      OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.hyp (sig := sig) hyps.size) x := by
  cases x with
  | here =>
      simpa [OriginEnv.weaken, OriginEnv.herePush] using
        OriginEnv.ofHyps_here_push hyps P
  | there y =>
      unfold OriginEnv.ofHyps OriginEnv.weaken OriginEnv.snoc
      apply congrArg Origin.hyp
      have hraw :=
        Var.toRawIdx_cast (Ctx.ofHyps_push hyps P).symm
          (.there y : Var (Ctx.ofHyps hyps ▻ P) A)
      rw [hraw, Var.toRawIdx_there, Array.size_push]
      omega

theorem Var.cast_cast {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (h : Γ = Δ) (x : Var Γ A) :
    (h.symm ▸ (h ▸ x) : Var Γ A) = x := by
  subst h
  rfl

/-- Forward cast form of `ofHyps_push_eq_weaken_hyp`. -/
theorem OriginEnv.ofHyps_eq_weaken_hyp_cast (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases) {A : Object sig.nBases}
    (y : Var (Ctx.ofHyps (hyps.push P)) A) :
    OriginEnv.ofHyps (hyps.push P) y =
      OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.hyp (sig := sig) hyps.size)
        ((Ctx.ofHyps_push hyps P) ▸ y) := by
  have hΓ := Ctx.ofHyps_push hyps P
  refine Eq.trans
    (congrArg (OriginEnv.ofHyps (hyps.push P)) (Var.cast_cast hΓ y).symm) ?_
  exact OriginEnv.ofHyps_push_eq_weaken_hyp hyps P (hΓ ▸ y)

/-! ### Origin order facts for hyp↔obs rename -/

@[simp] theorem Origin.cmp_hyp_obs (i k : Nat) :
    Origin.cmp (.hyp (sig := sig) i) (.obs k) = .lt := rfl

@[simp] theorem Origin.cmp_obs_hyp (k i : Nat) :
    Origin.cmp (.obs (sig := sig) k) (.hyp i) = .gt := rfl

theorem Origin.ble_hyp_obs (i k : Nat) :
    Origin.ble (.hyp (sig := sig) i) (.obs k) = true := by
  simp [Origin.ble, Origin.cmp_hyp_obs]

theorem Origin.ble_obs_hyp (k i : Nat) :
    Origin.ble (.obs (sig := sig) k) (.hyp i) = false := by
  simp [Origin.ble, Origin.cmp_obs_hyp]

/--
Rename newest-hyp tag `hyp hypIdx` to `obs k`, and shift existing obs indices
`≥ k` up by one so the new observation sorts after all hyps and before later obs.
-/
def Origin.rekeyHypToObs (hypIdx k : Nat) : Origin sig → Origin sig
  | .hyp i => if i == hypIdx then .obs k else .hyp i
  | .obs j => .obs (if j < k then j else j + 1)
  | .dom n => .dom n
  | .split p s => .split (Origin.rekeyHypToObs hypIdx k p) s

def PosEntry.rekeyHypToObs (hypIdx k : Nat) (e : PosEntry sig) : PosEntry sig :=
  { origin := Origin.rekeyHypToObs hypIdx k e.origin, ty := e.ty }

@[simp] theorem Origin.rekeyHypToObs_hyp_exact (hypIdx k : Nat) :
    Origin.rekeyHypToObs (sig := sig) hypIdx k (.hyp hypIdx) = .obs k := by
  simp [Origin.rekeyHypToObs]

@[simp] theorem Origin.rekeyHypToObs_hyp_ne (hypIdx k i : Nat) (hne : i ≠ hypIdx) :
    Origin.rekeyHypToObs (sig := sig) hypIdx k (.hyp i) = .hyp i := by
  simp [Origin.rekeyHypToObs, hne]

theorem Var.toRawIdx_lt_length {Γ : Ctx sig} {A : Object sig.nBases}
    (x : Var Γ A) : Var.toRawIdx x < Γ.length := by
  induction x with
  | here => simp [Var.toRawIdx, Ctx.length]
  | there _ ih =>
      simp only [Var.toRawIdx, Ctx.length]
      omega

theorem Ctx.length_foldl_snoc (xs : List (Object sig.nBases)) (Γ : Ctx sig) :
    (xs.foldl Ctx.snoc Γ).length = Γ.length + xs.length := by
  induction xs generalizing Γ with
  | nil => simp [List.foldl]
  | cons a as ih =>
      simp only [List.foldl, List.length_cons, Ctx.length, ih]
      omega

theorem Ctx.length_ofHyps (hyps : Array (Object sig.nBases)) :
    (Ctx.ofHyps hyps).length = hyps.size := by
  simp only [Ctx.ofHyps, Ctx.ofList, Ctx.length_foldl_snoc, Ctx.length,
    Array.length_toList]
  omega

/-- `ofHyps` never mentions `hyp hyps.size` (that index appears only after push). -/
theorem OriginEnv.ofHyps_ne_size (hyps : Array (Object sig.nBases))
    {A : Object sig.nBases} (x : Var (Ctx.ofHyps hyps) A) :
    OriginEnv.ofHyps hyps x ≠ Origin.hyp (sig := sig) hyps.size := by
  intro heq
  have hidx : hyps.size - 1 - Var.toRawIdx x = hyps.size := by
    simp only [OriginEnv.ofHyps] at heq
    injection heq
  have hlt : Var.toRawIdx x < hyps.size := by
    have := Var.toRawIdx_lt_length x
    simpa [Ctx.length_ofHyps] using this
  omega

/-- Phase-entry `ofHyps` assigns distinct `hyp` indices — collision-free. -/
theorem OriginEnv.ofHyps_wellFormed (hyps : Array (Object sig.nBases)) :
    OriginEnv.WellFormed (OriginEnv.ofHyps (sig := sig) hyps) where
  injective := by
    intro A B x y heq
    have hidx : hyps.size - 1 - Var.toRawIdx x = hyps.size - 1 - Var.toRawIdx y := by
      simpa [OriginEnv.ofHyps] using Origin.hyp.inj heq
    have hx : Var.toRawIdx x < hyps.size := by
      have := Var.toRawIdx_lt_length x
      simpa [Ctx.length_ofHyps] using this
    have hy : Var.toRawIdx y < hyps.size := by
      have := Var.toRawIdx_lt_length y
      simpa [Ctx.length_ofHyps] using this
    have hraw : Var.toRawIdx x = Var.toRawIdx y := by omega
    obtain ⟨hAB, hEq⟩ := Var.eq_of_toRawIdx' x y hraw
    exact ⟨hAB, hEq⟩

/-- `hyp hyps.size` is fresh for `ofHyps hyps`. -/
theorem OriginEnv.ofHyps_fresh_size (hyps : Array (Object sig.nBases)) :
    OriginEnv.Fresh (OriginEnv.ofHyps (sig := sig) hyps)
      (.hyp (sig := sig) hyps.size) :=
  fun x => OriginEnv.ofHyps_ne_size hyps x

/-- Rekey is identity on `ofHyps` (no `hyp hyps.size`, no obs). -/
theorem OriginEnv.ofHyps_rekey_id (hyps : Array (Object sig.nBases)) (k : Nat)
    {A : Object sig.nBases} (x : Var (Ctx.ofHyps hyps) A) :
    Origin.rekeyHypToObs hyps.size k (OriginEnv.ofHyps hyps x) =
      OriginEnv.ofHyps hyps x := by
  have hne : OriginEnv.ofHyps hyps x ≠ .hyp (sig := sig) hyps.size :=
    OriginEnv.ofHyps_ne_size hyps x
  dsimp only [OriginEnv.ofHyps] at hne ⊢
  -- Goal: rekey (hyp (size-1-raw)) = hyp (size-1-raw)
  have hne' : hyps.size - 1 - Var.toRawIdx x ≠ hyps.size := by
    intro hi; exact hne (by rw [hi])
  simp [Origin.rekeyHypToObs, hne']

/-- Rekey turns `weaken (ofHyps) (.hyp size)` into `weaken (ofHyps) (.obs k)`. -/
theorem OriginEnv.rekey_ofHyps_weaken_to_obs (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases) (k : Nat) {A : Object sig.nBases}
    (x : Var (Ctx.ofHyps hyps ▻ P) A) :
    Origin.rekeyHypToObs hyps.size k
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size) x) =
      OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.obs (sig := sig) k) x := by
  cases x with
  | here => simp [OriginEnv.weaken, Origin.rekeyHypToObs]
  | there y =>
      simp only [OriginEnv.weaken, OriginEnv.snoc]
      exact OriginEnv.ofHyps_rekey_id hyps k y

private theorem Origin.rekey_obs_idx_inj (k i j : Nat)
    (h : (if i < k then i else i + 1) = (if j < k then j else j + 1)) : i = j := by
  split at h <;> split at h <;> omega

/-- `rekeyHypToObs` is injective (needed so miss-tests `ε x == o` survive rekey). -/
theorem Origin.rekeyHypToObs_inj {hypIdx k : Nat} {o₁ o₂ : Origin sig}
    (h : Origin.rekeyHypToObs hypIdx k o₁ = Origin.rekeyHypToObs hypIdx k o₂) :
    o₁ = o₂ := by
  induction o₁ generalizing o₂ with
  | hyp i =>
      cases o₂ with
      | hyp j =>
          simp only [Origin.rekeyHypToObs] at h
          by_cases hi : i = hypIdx <;> by_cases hj : j = hypIdx
          · subst hi; subst hj; rfl
          · simp [hi, hj] at h
          · simp [hi, hj] at h
          · simp [hi, hj] at h; exact congrArg _ h
      | obs j =>
          simp only [Origin.rekeyHypToObs] at h
          by_cases hi : i = hypIdx
          · subst hi
            simp only [beq_self_eq_true, ↓reduceIte] at h
            have hk : k = (if j < k then j else j + 1) := by
              injection h
            split at hk <;> omega
          · simp [hi] at h
      | dom _ =>
          simp only [Origin.rekeyHypToObs] at h
          by_cases hi : i = hypIdx <;> simp [hi] at h
      | split _ _ =>
          simp only [Origin.rekeyHypToObs] at h
          by_cases hi : i = hypIdx <;> simp [hi] at h
  | obs i =>
      cases o₂ with
      | hyp j =>
          simp only [Origin.rekeyHypToObs] at h
          by_cases hj : j = hypIdx
          · subst hj
            simp only [beq_self_eq_true, ↓reduceIte] at h
            have hk : (if i < k then i else i + 1) = k := by
              injection h
            split at hk <;> omega
          · simp [hj] at h
      | obs j =>
          simp only [Origin.rekeyHypToObs] at h
          exact congrArg _ (Origin.rekey_obs_idx_inj k i j (by injection h))
      | dom _ =>
          simp only [Origin.rekeyHypToObs] at h
          split at h <;> cases h
      | split _ _ =>
          simp only [Origin.rekeyHypToObs] at h
          split at h <;> cases h
  | dom n =>
      cases o₂ with
      | hyp j =>
          simp only [Origin.rekeyHypToObs] at h
          by_cases hj : j = hypIdx <;> simp [hj] at h
      | obs _ =>
          simp only [Origin.rekeyHypToObs] at h
          split at h <;> cases h
      | dom m =>
          simp only [Origin.rekeyHypToObs] at h
          injection h with hn
          subst hn
          rfl
      | split _ _ =>
          simp only [Origin.rekeyHypToObs] at h
          cases h
  | split p side ih =>
      cases o₂ with
      | hyp j =>
          simp only [Origin.rekeyHypToObs] at h
          by_cases hj : j = hypIdx <;> simp [hj] at h
      | obs _ =>
          simp only [Origin.rekeyHypToObs] at h
          split at h <;> cases h
      | dom _ =>
          simp only [Origin.rekeyHypToObs] at h
          cases h
      | split q side' =>
          simp only [Origin.rekeyHypToObs] at h
          injection h with hp hs
          have := ih hp
          subst this
          subst hs
          rfl

theorem Origin.beq_rekeyHypToObs (hypIdx k : Nat) (o₁ o₂ : Origin sig) :
    (Origin.rekeyHypToObs hypIdx k o₁ == Origin.rekeyHypToObs hypIdx k o₂) =
      (o₁ == o₂) := by
  by_cases heq : o₁ = o₂
  · subst heq; simp
  · have hne : Origin.rekeyHypToObs hypIdx k o₁ ≠
        Origin.rekeyHypToObs hypIdx k o₂ := fun hr =>
      heq (Origin.rekeyHypToObs_inj hr)
    rw [beq_eq_false_iff_ne.mpr heq, beq_eq_false_iff_ne.mpr hne]

@[simp] theorem OriginEnv.find?_empty (ε : OriginEnv (Ctx.empty : Ctx sig))
    (o : Origin sig) :
    OriginEnv.find? ε o = none :=
  rfl

theorem OriginEnv.find?_snoc {Δ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv (Δ ▻ A)) (o : Origin sig) :
    OriginEnv.find? ε o =
      (if ε (.here : Var (Δ ▻ A) A) == o then
        some ⟨A, .here⟩
      else
        (OriginEnv.find? (fun {_B} x => ε (.there x)) o).map
          fun p => ⟨p.1, .there p.2⟩) :=
  rfl

/-- `find? = some` implies the recovered variable carries that origin. -/
theorem OriginEnv.find?_eq_some_eq {Γ : Ctx sig} (ε : OriginEnv Γ)
    (o : Origin sig) {A : Object sig.nBases} (x : Var Γ A)
    (h : OriginEnv.find? ε o = some ⟨A, x⟩) : ε x = o := by
  induction Γ generalizing A with
  | empty =>
      simp only [OriginEnv.find?] at h
      nomatch h
  | snoc Δ B ih =>
      rw [OriginEnv.find?_snoc] at h
      by_cases hhere : (ε (.here : Var (Δ ▻ B) B) == o) = true
      · simp only [hhere, ↓reduceIte] at h
        cases h
        exact beq_iff_eq.mp hhere
      · simp only [hhere, Bool.false_eq_true, ↓reduceIte] at h
        match hfind : OriginEnv.find? (fun {_C} y => ε (.there y)) o with
        | none => simp [hfind] at h
        | some ⟨B', y⟩ =>
            simp only [hfind, Option.map] at h
            cases h
            exact ih (fun {_C} y => ε (.there y)) y hfind

/-- Under well-formedness, `find?` recovers the unique carrier of `o`. -/
theorem OriginEnv.find?_eq_some_of_wellFormed {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) (x : Var Γ A)
    (hwf : OriginEnv.WellFormed ε) (hx : ε x = o) :
    OriginEnv.find? ε o = some ⟨A, x⟩ := by
  induction Γ generalizing A with
  | empty => nomatch x
  | snoc Δ B ih =>
      rw [OriginEnv.find?_snoc]
      cases x with
      | here =>
          have : (ε (.here : Var (Δ ▻ B) B) == o) = true :=
            beq_iff_eq.mpr hx
          simp [this]
      | there y =>
          have hne : ¬ (ε (.here : Var (Δ ▻ B) B) == o) = true := by
            intro hhit
            have heq : ε (.here : Var (Δ ▻ B) B) = o := beq_iff_eq.mp hhit
            have : ε (.here : Var (Δ ▻ B) B) = ε (.there y) := by
              simp [heq, hx]
            obtain ⟨hAB, hEq⟩ := hwf.injective (.here) (.there y) this
            cases hAB
            cases hEq
          simp only [hne, ↓reduceIte]
          let ε' : OriginEnv Δ := fun {_} z => ε (.there z)
          have hwf' : OriginEnv.WellFormed ε' := OriginEnv.WellFormed.there ε hwf
          have hy : ε' y = o := hx
          have hfind : OriginEnv.find? ε' o = some ⟨A, y⟩ := ih ε' y hwf' hy
          simp [ε', hfind]

/-- Well-formed lookup is a two-sided characterization. -/
theorem OriginEnv.find?_eq_some_iff_wellFormed {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) (x : Var Γ A)
    (hwf : OriginEnv.WellFormed ε) :
    OriginEnv.find? ε o = some ⟨A, x⟩ ↔ ε x = o :=
  ⟨fun h => OriginEnv.find?_eq_some_eq ε o x h,
    fun hx => OriginEnv.find?_eq_some_of_wellFormed ε o x hwf hx⟩

/-- Looking past a fresh newest binder recovers the older carrier. -/
theorem OriginEnv.find?_weaken_there {Γ : Ctx sig} {A B : Object sig.nBases}
    (ε : OriginEnv Γ) (oFresh o : Origin sig) (x : Var Γ A)
    (hwf : OriginEnv.WellFormed ε) (hfresh : OriginEnv.Fresh ε oFresh)
    (h : OriginEnv.find? ε o = some ⟨A, x⟩) :
    OriginEnv.find? (OriginEnv.weaken (A := B) ε oFresh) o =
      some ⟨A, .there x⟩ := by
  have hx : ε x = o := OriginEnv.find?_eq_some_eq ε o x h
  exact OriginEnv.find?_eq_some_of_wellFormed
    (OriginEnv.weaken (A := B) ε oFresh) o (.there x)
    (OriginEnv.WellFormed.weaken ε oFresh hwf hfresh)
    (by simpa [OriginEnv.weaken, OriginEnv.snoc] using hx)

/-- Newest binder is recovered by `find?` at the origin assigned by `weaken`. -/
theorem OriginEnv.find?_weaken_here {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) :
    OriginEnv.find? (OriginEnv.weaken (A := A) ε o) o = some ⟨A, .here⟩ := by
  rw [OriginEnv.find?_snoc]
  simp [OriginEnv.weaken, OriginEnv.snoc, BEq.rfl]

/-- `find?` is invariant under simultaneous rekey of the environment and query. -/
theorem OriginEnv.find?_rekeyHypToObs {Γ : Ctx sig} (ε : OriginEnv Γ)
    (hypIdx k : Nat) (o : Origin sig) :
    OriginEnv.find?
        (fun {_B} x => Origin.rekeyHypToObs hypIdx k (ε x))
        (Origin.rekeyHypToObs hypIdx k o) =
      OriginEnv.find? ε o := by
  induction Γ with
  | empty =>
      rw [OriginEnv.find?_empty, OriginEnv.find?_empty]
  | snoc Δ A ih =>
      rw [OriginEnv.find?_snoc, OriginEnv.find?_snoc, Origin.beq_rekeyHypToObs]
      split
      · rfl
      · rw [ih]

/-- `find?` depends only on the pointwise environment. -/
theorem OriginEnv.find?_env_eq {Γ : Ctx sig} {ε ε' : OriginEnv Γ}
    (o : Origin sig) (hε : ∀ {B} (x : Var Γ B), ε x = ε' x) :
    OriginEnv.find? ε o = OriginEnv.find? ε' o := by
  induction Γ with
  | empty => rw [OriginEnv.find?_empty, OriginEnv.find?_empty]
  | snoc Δ A ih =>
      rw [OriginEnv.find?_snoc, OriginEnv.find?_snoc]
      have hbeq : (ε (Var.here : Var (Δ ▻ A) A) == o) =
          (ε' (Var.here : Var (Δ ▻ A) A) == o) := by rw [hε Var.here]
      rw [hbeq]
      split
      · rfl
      · rw [ih (fun {_} y => hε (Var.there y))]

/-- Next observation slot after rekeying `hypIdx ↦ obs k` (obs indices `≥ k` shift). -/
def Origin.obsSlotAfterRekey (k obsSlot : Nat) : Nat :=
  if obsSlot < k then obsSlot else obsSlot + 1

@[simp] theorem Origin.obsSlotAfterRekey_zero (obsSlot : Nat) :
    Origin.obsSlotAfterRekey 0 obsSlot = obsSlot + 1 := by
  simp [Origin.obsSlotAfterRekey]

@[simp] theorem Origin.rekeyHypToObs_obs (hypIdx k j : Nat) :
    Origin.rekeyHypToObs (sig := sig) hypIdx k (.obs j) =
      .obs (if j < k then j else j + 1) := rfl

@[simp] theorem Origin.rekeyHypToObs_dom (hypIdx k n : Nat) :
    Origin.rekeyHypToObs (sig := sig) hypIdx k (.dom n) = .dom n := rfl

@[simp] theorem Origin.rekeyHypToObs_split (hypIdx k : Nat) (p : Origin sig) (s : Bool) :
    Origin.rekeyHypToObs hypIdx k (.split p s) =
      .split (Origin.rekeyHypToObs hypIdx k p) s := rfl

theorem OriginEnv.weaken_rekeyHypToObs {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (o : Origin sig) (hypIdx k : Nat)
    {B : Object sig.nBases} (x : Var (Γ ▻ A) B) :
    Origin.rekeyHypToObs hypIdx k (OriginEnv.weaken (A := A) ε o x) =
      OriginEnv.weaken (A := A)
        (fun {C} y => Origin.rekeyHypToObs hypIdx k (ε y))
        (Origin.rekeyHypToObs hypIdx k o) x := by
  cases x <;> rfl

/-- All `hyp` indices in `o` are `≤ bound` (true for `ofHyps` / newest-hyp rekey). -/
def Origin.hypIdxLe (o : Origin sig) (bound : Nat) : Prop :=
  match o with
  | .hyp i => i ≤ bound
  | .obs _ | .dom _ => True
  | .split p _ => Origin.hypIdxLe p bound

theorem Origin.hypIdxLe_ofHyps (hyps : Array (Object sig.nBases))
    {A : Object sig.nBases} (x : Var (Ctx.ofHyps hyps) A) :
    Origin.hypIdxLe (OriginEnv.ofHyps hyps x) (hyps.size - 1) ∨
      hyps.size = 0 := by
  by_cases hsz : hyps.size = 0
  · exact Or.inr hsz
  · refine Or.inl ?_
    simp only [OriginEnv.ofHyps, Origin.hypIdxLe]
    have hraw : Var.toRawIdx x < hyps.size := by
      have := Var.toRawIdx_lt_length x
      simpa [Ctx.length_ofHyps] using this
    omega

theorem Origin.hypIdxLe_ofHyps_le_size (hyps : Array (Object sig.nBases))
    {A : Object sig.nBases} (x : Var (Ctx.ofHyps hyps) A) :
    Origin.hypIdxLe (OriginEnv.ofHyps hyps x) hyps.size := by
  simp only [OriginEnv.ofHyps, Origin.hypIdxLe]
  have hraw : Var.toRawIdx x < hyps.size := by
    have := Var.toRawIdx_lt_length x
    simpa [Ctx.length_ofHyps] using this
  omega

theorem Origin.hypIdxLe_ofHyps_push (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases) {A : Object sig.nBases}
    (x : Var (Ctx.ofHyps hyps ▻ P) A) :
    Origin.hypIdxLe
      (OriginEnv.ofHyps (hyps.push P) ((Ctx.ofHyps_push hyps P).symm ▸ x))
      hyps.size := by
  have h := OriginEnv.ofHyps_push_eq_weaken_hyp hyps P x
  rw [h]
  cases x with
  | here => simp [OriginEnv.weaken, Origin.hypIdxLe]
  | there y =>
      simp only [OriginEnv.weaken, OriginEnv.snoc, OriginEnv.ofHyps, Origin.hypIdxLe]
      have hraw : Var.toRawIdx y < hyps.size := by
        have := Var.toRawIdx_lt_length y
        simpa [Ctx.length_ofHyps] using this
      omega

theorem Origin.cmp_rekeyHypToObs_zero_of_hypIdxLe (hypIdx : Nat)
    {o₁ o₂ : Origin sig}
    (h₁ : Origin.hypIdxLe o₁ hypIdx) (h₂ : Origin.hypIdxLe o₂ hypIdx) :
    Origin.cmp (Origin.rekeyHypToObs hypIdx 0 o₁)
      (Origin.rekeyHypToObs hypIdx 0 o₂) =
      Origin.cmp o₁ o₂ := by
  induction o₁ generalizing o₂ with
  | hyp i =>
      cases o₂ with
      | hyp j =>
          have hi : i ≤ hypIdx := h₁
          have hj : j ≤ hypIdx := h₂
          dsimp only [Origin.rekeyHypToObs]
          by_cases h_i : i = hypIdx <;> by_cases h_j : j = hypIdx
          · -- both renamed
            simp [h_i, h_j, Origin.cmp_self]
          · -- i renamed, j not: obs 0 vs hyp j, and compare hypIdx j = gt
            have hjlt : j < hypIdx := Nat.lt_of_le_of_ne hj h_j
            simp only [h_i, h_j, beq_iff_eq, ↓reduceIte, Origin.cmp, Origin.cmp_hyp_hyp]
            exact (Nat.compare_eq_gt.mpr hjlt).symm
          · have hilt : i < hypIdx := Nat.lt_of_le_of_ne hi h_i
            simp only [h_i, h_j, beq_iff_eq, ↓reduceIte, Origin.cmp, Origin.cmp_hyp_hyp]
            exact (Nat.compare_eq_lt.mpr hilt).symm
          · simp [h_i, h_j]
      | obs j =>
          dsimp only [Origin.rekeyHypToObs]
          by_cases h_i : i = hypIdx
          · simp only [h_i, beq_iff_eq, ↓reduceIte, Origin.cmp_hyp_obs, Origin.cmp]
            exact Nat.compare_eq_lt.mpr (Nat.zero_lt_succ j)
          · simp [h_i, Origin.cmp]
      | dom _ =>
          dsimp only [Origin.rekeyHypToObs]
          by_cases h_i : i = hypIdx <;> simp [h_i, Origin.cmp]
      | split _ _ =>
          dsimp only [Origin.rekeyHypToObs]
          by_cases h_i : i = hypIdx <;> simp [h_i, Origin.cmp]
  | obs i =>
      cases o₂ with
      | hyp j =>
          dsimp only [Origin.rekeyHypToObs]
          by_cases h_j : j = hypIdx
          · simp only [h_j, beq_iff_eq, ↓reduceIte, Origin.cmp_obs_hyp, Origin.cmp]
            exact (Nat.compare_eq_gt.mpr (Nat.zero_lt_succ i)).symm
          · simp [h_j, Origin.cmp]
      | obs j =>
          dsimp only [Origin.rekeyHypToObs, Origin.cmp]
          have hi0 : ¬ i < 0 := Nat.not_lt_zero i
          have hj0 : ¬ j < 0 := Nat.not_lt_zero j
          simp only [hi0, hj0, ↓reduceIte]
          rcases Nat.lt_trichotomy i j with hlt | heq | hgt
          · have hlt' : i + 1 < j + 1 := Nat.add_lt_add_right hlt 1
            rw [Nat.compare_eq_lt.mpr hlt', Nat.compare_eq_lt.mpr hlt]
          · subst heq
            rw [Nat.compare_eq_eq.mpr rfl, Nat.compare_eq_eq.mpr rfl]
          · have hgt' : j + 1 < i + 1 := Nat.add_lt_add_right hgt 1
            rw [Nat.compare_eq_gt.mpr hgt', Nat.compare_eq_gt.mpr hgt]
      | dom _ => simp [Origin.rekeyHypToObs, Origin.cmp]
      | split _ _ => simp [Origin.rekeyHypToObs, Origin.cmp]
  | dom n =>
      cases o₂ with
      | hyp j =>
          dsimp only [Origin.rekeyHypToObs]
          by_cases h_j : j = hypIdx <;> simp [h_j, Origin.cmp]
      | obs _ => simp [Origin.rekeyHypToObs, Origin.cmp]
      | dom m => simp [Origin.rekeyHypToObs, Origin.cmp]
      | split _ _ => simp [Origin.rekeyHypToObs, Origin.cmp]
  | split p side ih =>
      cases o₂ with
      | hyp j =>
          dsimp only [Origin.rekeyHypToObs]
          by_cases h_j : j = hypIdx <;> simp [h_j, Origin.cmp]
      | obs _ => simp [Origin.rekeyHypToObs, Origin.cmp]
      | dom _ => simp [Origin.rekeyHypToObs, Origin.cmp]
      | split q side' =>
          have hp : Origin.hypIdxLe p hypIdx := h₁
          have hq : Origin.hypIdxLe q hypIdx := h₂
          cases side <;> cases side' <;>
            simp [Origin.rekeyHypToObs, Origin.cmp, ih hp hq]

theorem Origin.ble_rekeyHypToObs_zero_of_hypIdxLe (hypIdx : Nat)
    {o₁ o₂ : Origin sig}
    (h₁ : Origin.hypIdxLe o₁ hypIdx) (h₂ : Origin.hypIdxLe o₂ hypIdx) :
    Origin.ble (Origin.rekeyHypToObs hypIdx 0 o₁)
      (Origin.rekeyHypToObs hypIdx 0 o₂) =
      Origin.ble o₁ o₂ := by
  simp only [Origin.ble, Origin.cmp_rekeyHypToObs_zero_of_hypIdxLe hypIdx h₁ h₂]


/-! ### Origin.ble total / transitive (for mergeSort) -/

theorem Origin.cmp_swap (o₁ o₂ : Origin sig) :
    Origin.cmp o₂ o₁ = (Origin.cmp o₁ o₂).swap := by
  induction o₁ generalizing o₂ with
  | hyp i =>
      cases o₂ with
      | hyp j => simp only [Origin.cmp]; exact (Nat.compare_swap i j).symm
      | obs _ | dom _ | split _ _ => rfl
  | obs i =>
      cases o₂ with
      | hyp _ => rfl
      | obs j => simp only [Origin.cmp]; exact (Nat.compare_swap i j).symm
      | dom _ | split _ _ => rfl
  | dom i =>
      cases o₂ with
      | hyp _ | obs _ => rfl
      | dom j => simp only [Origin.cmp]; exact (Nat.compare_swap i j).symm
      | split _ _ => rfl
  | split p s ih =>
      cases o₂ with
      | hyp _ | obs _ | dom _ => rfl
      | split q t =>
          cases s <;> cases t
          · simpa [Origin.cmp] using ih q
          · simp only [Origin.cmp]; have h := ih q; cases hc : Origin.cmp p q <;> simp [hc, h]
          · simp only [Origin.cmp]; have h := ih q; cases hc : Origin.cmp p q <;> simp [hc, h]
          · simpa [Origin.cmp] using ih q

theorem Origin.eq_of_cmp_eq {o₁ o₂ : Origin sig}
    (h : Origin.cmp o₁ o₂ = .eq) : o₁ = o₂ := by
  induction o₁ generalizing o₂ with
  | hyp i =>
      cases o₂ with
      | hyp j =>
          simp only [Origin.cmp] at h
          exact congrArg Origin.hyp (Nat.compare_eq_eq.mp h)
      | obs _ | dom _ | split _ _ => cases h
  | obs i =>
      cases o₂ with
      | hyp _ => cases h
      | obs j =>
          simp only [Origin.cmp] at h
          exact congrArg Origin.obs (Nat.compare_eq_eq.mp h)
      | dom _ | split _ _ => cases h
  | dom i =>
      cases o₂ with
      | hyp _ | obs _ => cases h
      | dom j =>
          simp only [Origin.cmp] at h
          exact congrArg Origin.dom (Nat.compare_eq_eq.mp h)
      | split _ _ => cases h
  | split p s ih =>
      cases o₂ with
      | hyp _ | obs _ | dom _ => cases h
      | split q t =>
          cases s <;> cases t
          · simp only [Origin.cmp] at h; have := ih h; subst this; rfl
          · simp only [Origin.cmp] at h; cases hc : Origin.cmp p q <;> simp [hc] at h
          · simp only [Origin.cmp] at h; cases hc : Origin.cmp p q <;> simp [hc] at h
          · simp only [Origin.cmp] at h; have := ih h; subst this; rfl

/-- Canonical form of split/split comparison. -/
def Origin.splitCmp (p : Origin sig) (s : Bool) (q : Origin sig) (t : Bool) : Ordering :=
  match s, t with
  | false, false | true, true => Origin.cmp p q
  | false, true => match Origin.cmp p q with | .eq => .lt | o => o
  | true, false => match Origin.cmp p q with | .eq => .gt | o => o

theorem Origin.cmp_split_eq (p q : Origin sig) (s t : Bool) :
    Origin.cmp (.split p s) (.split q t) = Origin.splitCmp p s q t := by
  cases s <;> cases t <;> rfl

theorem Origin.splitCmp_lt_trans (p q r : Origin sig) (s t u : Bool)
    (h₁₂ : Origin.splitCmp p s q t = .lt) (h₂₃ : Origin.splitCmp q t r u = .lt)
    (ih : ∀ {q r : Origin sig}, Origin.cmp p q = .lt → Origin.cmp q r = .lt → Origin.cmp p r = .lt) :
    Origin.splitCmp p s r u = .lt := by
  cases s <;> cases t <;> cases u <;> simp only [Origin.splitCmp] at h₁₂ h₂₃ ⊢
  · exact ih h₁₂ h₂₃
  · -- f f t
    cases hr : Origin.cmp q r with
    | lt =>
        have := ih h₁₂ hr
        simp [this]
    | eq =>
        simp [hr] at h₂₃
        have := Origin.eq_of_cmp_eq hr; subst this
        simp [h₁₂]
    | gt => simp [hr] at h₂₃
  · -- f t f
    cases hpq : Origin.cmp p q with
    | lt =>
        simp [hpq] at h₁₂
        cases hqr : Origin.cmp q r with
        | lt =>
            simp [hqr] at h₂₃
            have := ih hpq hqr
            simp [this]
        | eq => simp [hqr] at h₂₃
        | gt => simp [hqr] at h₂₃
    | eq =>
        simp [hpq] at h₁₂
        cases hqr : Origin.cmp q r with
        | lt =>
            simp [hqr] at h₂₃
            have := Origin.eq_of_cmp_eq hpq; subst this
            simp [hqr]
        | eq => simp [hqr] at h₂₃
        | gt => simp [hqr] at h₂₃
    | gt => simp [hpq] at h₁₂
  · -- f t t
    cases hpq : Origin.cmp p q with
    | lt =>
        simp [hpq] at h₁₂
        cases hqr : Origin.cmp q r with
        | lt =>
            have := ih hpq hqr
            simp [this]
        | eq =>
            have := Origin.eq_of_cmp_eq hqr; subst this
            simp [hpq]
        | gt => simp [hqr] at h₂₃
    | eq =>
        simp [hpq] at h₁₂
        cases hqr : Origin.cmp q r with
        | lt =>
            have := Origin.eq_of_cmp_eq hpq; subst this
            simp [hqr]
        | eq =>
            have hp := Origin.eq_of_cmp_eq hpq
            have hq := Origin.eq_of_cmp_eq hqr
            subst hp; subst hq
            simp [Origin.cmp_self]
        | gt => simp [hqr] at h₂₃
    | gt => simp [hpq] at h₁₂
  · -- t f f
    cases hpq : Origin.cmp p q with
    | lt =>
        simp [hpq] at h₁₂
        cases hqr : Origin.cmp q r with
        | lt =>
            have := ih hpq hqr
            simp [this]
        | eq =>
            have := Origin.eq_of_cmp_eq hqr; subst this
            simp [hpq]
        | gt => simp [hqr] at h₂₃
    | eq => simp [hpq] at h₁₂
    | gt => simp [hpq] at h₁₂
  · -- t f t
    cases hpq : Origin.cmp p q with
    | lt =>
        simp [hpq] at h₁₂
        cases hqr : Origin.cmp q r with
        | lt => exact ih hpq hqr
        | eq =>
            simp [hqr] at h₂₃
            have := Origin.eq_of_cmp_eq hqr; subst this
            exact hpq
        | gt => simp [hqr] at h₂₃
    | eq => simp [hpq] at h₁₂
    | gt => simp [hpq] at h₁₂
  · -- t t f
    cases hpq : Origin.cmp p q with
    | lt =>
        simp [hpq] at h₁₂
        cases hqr : Origin.cmp q r with
        | lt =>
            simp [hqr] at h₂₃
            have := ih hpq hqr
            simp [this]
        | eq => simp [hqr] at h₂₃
        | gt => simp [hqr] at h₂₃
    | eq => simp [hpq] at h₁₂
    | gt => simp [hpq] at h₁₂
  · exact ih h₁₂ h₂₃

theorem Origin.cmp_lt_trans {o₁ o₂ o₃ : Origin sig}
    (h₁₂ : Origin.cmp o₁ o₂ = .lt) (h₂₃ : Origin.cmp o₂ o₃ = .lt) :
    Origin.cmp o₁ o₃ = .lt := by
  induction o₁ generalizing o₂ o₃ with
  | hyp i =>
      cases o₂ with
      | hyp j =>
          cases o₃ with
          | hyp k =>
              simp only [Origin.cmp, Nat.compare_eq_lt] at h₁₂ h₂₃ ⊢; omega
          | obs _ | dom _ | split _ _ => rfl
      | obs j =>
          cases o₃ with
          | hyp _ => cases h₂₃
          | obs _ | dom _ | split _ _ => rfl
      | dom j =>
          cases o₃ with
          | hyp _ | obs _ => cases h₂₃
          | dom _ | split _ _ => rfl
      | split _ _ =>
          cases o₃ with
          | hyp _ | obs _ | dom _ => cases h₂₃
          | split _ _ => rfl
  | obs i =>
      cases o₂ with
      | hyp _ => cases h₁₂
      | obs j =>
          cases o₃ with
          | hyp _ => cases h₂₃
          | obs k =>
              simp only [Origin.cmp, Nat.compare_eq_lt] at h₁₂ h₂₃ ⊢; omega
          | dom _ | split _ _ => rfl
      | dom _ =>
          cases o₃ with
          | hyp _ | obs _ => cases h₂₃
          | dom _ | split _ _ => rfl
      | split _ _ =>
          cases o₃ with
          | hyp _ | obs _ | dom _ => cases h₂₃
          | split _ _ => rfl
  | dom i =>
      cases o₂ with
      | hyp _ | obs _ => cases h₁₂
      | dom j =>
          cases o₃ with
          | hyp _ | obs _ => cases h₂₃
          | dom k =>
              simp only [Origin.cmp, Nat.compare_eq_lt] at h₁₂ h₂₃ ⊢; omega
          | split _ _ => rfl
      | split _ _ =>
          cases o₃ with
          | hyp _ | obs _ | dom _ => cases h₂₃
          | split _ _ => rfl
  | split p s ih =>
      cases o₂ with
      | hyp _ | obs _ | dom _ => cases h₁₂
      | split q t =>
          cases o₃ with
          | hyp _ | obs _ | dom _ => cases h₂₃
          | split r u =>
              rw [Origin.cmp_split_eq] at h₁₂ h₂₃ ⊢
              exact Origin.splitCmp_lt_trans p q r s t u h₁₂ h₂₃ ih

theorem Origin.ble_total (o₁ o₂ : Origin sig) :
    (Origin.ble o₁ o₂ || Origin.ble o₂ o₁) = true := by
  cases hc : Origin.cmp o₁ o₂ with
  | lt =>
      have : Origin.cmp o₂ o₁ = .gt := by rw [Origin.cmp_swap, hc]; rfl
      simp [Origin.ble, hc, this]
  | eq =>
      have : Origin.cmp o₂ o₁ = .eq := by rw [Origin.cmp_swap, hc]; rfl
      simp [Origin.ble, hc, this]
  | gt =>
      have : Origin.cmp o₂ o₁ = .lt := by rw [Origin.cmp_swap, hc]; rfl
      simp [Origin.ble, hc, this]

theorem Origin.ble_trans (a b c : Origin sig)
    (hab : Origin.ble a b = true) (hbc : Origin.ble b c = true) :
    Origin.ble a c = true := by
  simp only [Origin.ble, Bool.or_eq_true, beq_iff_eq] at hab hbc ⊢
  cases hab with
  | inl hab =>
      cases hbc with
      | inl hbc => exact Or.inl (Origin.cmp_lt_trans hab hbc)
      | inr hbc => exact Or.inl (Origin.eq_of_cmp_eq hbc ▸ hab)
  | inr hab =>
      cases hbc with
      | inl hbc => exact Or.inl (Origin.eq_of_cmp_eq hab ▸ hbc)
      | inr hbc =>
          rw [Origin.eq_of_cmp_eq hab, Origin.eq_of_cmp_eq hbc]
          exact Or.inr (Origin.cmp_self _)

@[simp] theorem Origin.cmp_hyp_split (i : Nat) (p : Origin sig) (side : Bool) :
    Origin.cmp (.hyp (sig := sig) i) (.split p side) = .lt := rfl

@[simp] theorem Origin.cmp_obs_split (k : Nat) (p : Origin sig) (side : Bool) :
    Origin.cmp (.obs (sig := sig) k) (.split p side) = .lt := rfl

@[simp] theorem Origin.cmp_dom_split (n : Nat) (p : Origin sig) (side : Bool) :
    Origin.cmp (.dom (sig := sig) n) (.split p side) = .lt := rfl

@[simp] theorem Origin.blt_hyp_split (i : Nat) (p : Origin sig) (side : Bool) :
    Origin.blt (.hyp (sig := sig) i) (.split p side) = true := by
  simp [Origin.blt]

@[simp] theorem Origin.blt_obs_split (k : Nat) (p : Origin sig) (side : Bool) :
    Origin.blt (.obs (sig := sig) k) (.split p side) = true := by
  simp [Origin.blt]

@[simp] theorem Origin.blt_dom_split (n : Nat) (p : Origin sig) (side : Bool) :
    Origin.blt (.dom (sig := sig) n) (.split p side) = true := by
  simp [Origin.blt]

theorem Origin.ble_of_blt {o₁ o₂ : Origin sig}
    (h : Origin.blt o₁ o₂ = true) : Origin.ble o₁ o₂ = true := by
  simp only [Origin.blt, beq_iff_eq] at h
  simp [Origin.ble, h]

theorem Origin.not_ble_of_blt_symm {o₁ o₂ : Origin sig}
    (h : Origin.blt o₁ o₂ = true) : Origin.ble o₂ o₁ = false := by
  simp only [Origin.blt, beq_iff_eq] at h
  have hswap : Origin.cmp o₂ o₁ = .gt := by rw [Origin.cmp_swap, h]; rfl
  simp [Origin.ble, hswap]


/-! ### posCollect structural lemmas -/

theorem posCollect_snoc {Δ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv (Δ ▻ A)) :
    OriginEnv.posCollect ε =
      let rest := OriginEnv.posCollect (fun {B} x => ε (.there x))
      if objectPolarity A == .pos then
        ({ origin := ε (.here : Var (Δ ▻ A) A), ty := A } : PosEntry sig) :: rest
      else rest := by
  rfl

theorem posCollect_empty (ε : OriginEnv (Ctx.empty : Ctx sig)) :
    OriginEnv.posCollect ε = [] := rfl

theorem posCollect_env_eq {Γ : Ctx sig} {ε ε' : OriginEnv Γ}
    (hε : ∀ {A} (x : Var Γ A), ε x = ε' x) :
    OriginEnv.posCollect ε = OriginEnv.posCollect ε' := by
  induction Γ with
  | empty => rw [posCollect_empty, posCollect_empty]
  | snoc Δ A ih =>
      rw [posCollect_snoc, posCollect_snoc]
      have hrest := ih (fun {B} x => hε (.there x))
      split <;> simp [hε, hrest]

theorem posCollect_origin_of_env {Γ : Ctx sig} (ε : OriginEnv Γ)
    (hε : ∀ {A} (x : Var Γ A), ∃ i, ε x = .hyp (sig := sig) i)
    {e : PosEntry sig} (he : e ∈ OriginEnv.posCollect ε) :
    ∃ i, e.origin = .hyp (sig := sig) i := by
  induction Γ with
  | empty =>
      rw [posCollect_empty] at he; cases he
  | snoc Δ A ih =>
      rw [posCollect_snoc] at he
      split at he
      · cases he with
        | head =>
            have ⟨i, hi⟩ := hε (.here : Var (Δ ▻ A) A)
            exact ⟨i, hi⟩
        | tail _ hmem =>
            exact ih (fun {B} x => ε (.there x))
              (fun {B} x => hε (.there x)) hmem
      · exact ih (fun {B} x => ε (.there x))
          (fun {B} x => hε (.there x)) he

theorem posCollect_ofHyps_origin_hyp (hyps : Array (Object sig.nBases))
    {e : PosEntry sig} (he : e ∈ OriginEnv.posCollect (OriginEnv.ofHyps hyps)) :
    ∃ i, e.origin = .hyp (sig := sig) i := by
  refine posCollect_origin_of_env (OriginEnv.ofHyps hyps) ?_ he
  intro A x
  exact ⟨hyps.size - 1 - Var.toRawIdx x, rfl⟩

theorem posCollect_weaken_hyp (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases) :
    OriginEnv.posCollect
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size)) =
      if objectPolarity P == .pos then
        ({ origin := .hyp (sig := sig) hyps.size, ty := P } : PosEntry sig) ::
          OriginEnv.posCollect (OriginEnv.ofHyps hyps)
      else
        OriginEnv.posCollect (OriginEnv.ofHyps hyps) := by
  rw [posCollect_snoc]
  have hrest :=
    posCollect_env_eq
      (ε := fun {B} x =>
        OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size) (.there x))
      (ε' := OriginEnv.ofHyps hyps)
      (fun {B} x => rfl)
  cases hpol : objectPolarity P == Polarity.pos <;>
    simp [hpol, OriginEnv.weaken, OriginEnv.snoc, hrest]

/-- `posCollect` is invariant under context cast when environments agree. -/
theorem posCollect_castCtx {Γ Δ : Ctx sig} (hΓ : Γ = Δ)
    (ε : OriginEnv Γ) (ε' : OriginEnv Δ)
    (hε : ∀ {A} (x : Var Γ A), ε x = ε' (hΓ ▸ x)) :
    OriginEnv.posCollect ε = OriginEnv.posCollect ε' := by
  subst hΓ
  exact posCollect_env_eq hε

/-- Phase worklists agree across `Ctx.ofHyps_push`. -/
theorem posWorklist_ofHyps_push (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases) :
    OriginEnv.posWorklist (OriginEnv.ofHyps (hyps.push P)) =
      OriginEnv.posWorklist
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size)) := by
  dsimp only [OriginEnv.posWorklist]
  congr 1
  exact posCollect_castCtx (Ctx.ofHyps_push hyps P)
    (OriginEnv.ofHyps (hyps.push P))
    (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
      (.hyp (sig := sig) hyps.size))
    (fun {A} y => OriginEnv.ofHyps_eq_weaken_hyp_cast hyps P y)

/--
Rename newest-hyp tag `hyp hypIdx` to `.split parent side`. Unlike
`rekeyHypToObs`, does not shift obs indices. Used to align `ofHyps.push`
binder tags with encode's left-coprod branch origins (after the left-coprod
head has already been dropped from the worklist).
-/
def Origin.rekeyHypToSplit (hypIdx : Nat) (parent : Origin sig) (side : Bool) :
    Origin sig → Origin sig
  | .hyp i => if i == hypIdx then .split parent side else .hyp i
  | .obs j => .obs j
  | .dom n => .dom n
  | .split p s => .split (Origin.rekeyHypToSplit hypIdx parent side p) s

def PosEntry.rekeyHypToSplit (hypIdx : Nat) (parent : Origin sig) (side : Bool)
    (e : PosEntry sig) : PosEntry sig :=
  { origin := Origin.rekeyHypToSplit hypIdx parent side e.origin, ty := e.ty }

@[simp] theorem Origin.rekeyHypToSplit_hyp_exact (hypIdx : Nat)
    (parent : Origin sig) (side : Bool) :
    Origin.rekeyHypToSplit (sig := sig) hypIdx parent side (.hyp hypIdx) =
      .split parent side := by
  simp [Origin.rekeyHypToSplit]

@[simp] theorem Origin.rekeyHypToSplit_hyp_ne (hypIdx : Nat)
    (parent : Origin sig) (side : Bool) (i : Nat) (hne : i ≠ hypIdx) :
    Origin.rekeyHypToSplit (sig := sig) hypIdx parent side (.hyp i) = .hyp i := by
  simp [Origin.rekeyHypToSplit, hne]

@[simp] theorem Origin.rekeyHypToSplit_obs (hypIdx : Nat)
    (parent : Origin sig) (side : Bool) (j : Nat) :
    Origin.rekeyHypToSplit (sig := sig) hypIdx parent side (.obs j) = .obs j := by
  simp [Origin.rekeyHypToSplit]

@[simp] theorem Origin.rekeyHypToSplit_dom (hypIdx : Nat)
    (parent : Origin sig) (side : Bool) (n : Nat) :
    Origin.rekeyHypToSplit (sig := sig) hypIdx parent side (.dom n) = .dom n := by
  simp [Origin.rekeyHypToSplit]

@[simp] theorem Origin.rekeyHypToSplit_split (hypIdx : Nat)
    (parent : Origin sig) (side : Bool) (p : Origin sig) (s : Bool) :
    Origin.rekeyHypToSplit (sig := sig) hypIdx parent side (.split p s) =
      .split (Origin.rekeyHypToSplit hypIdx parent side p) s := by
  simp [Origin.rekeyHypToSplit]

@[simp] theorem PosEntry.rekeyHypToSplit_ty (hypIdx : Nat)
    (parent : Origin sig) (side : Bool) (e : PosEntry sig) :
    (PosEntry.rekeyHypToSplit hypIdx parent side e).ty = e.ty := rfl

@[simp] theorem PosEntry.rekeyHypToSplit_origin (hypIdx : Nat)
    (parent : Origin sig) (side : Bool) (e : PosEntry sig) :
    (PosEntry.rekeyHypToSplit hypIdx parent side e).origin =
      Origin.rekeyHypToSplit hypIdx parent side e.origin := rfl

/-- Rekey turns `weaken (ofHyps) (.hyp size)` into `weaken (ofHyps) (.split …)`. -/
theorem OriginEnv.rekey_ofHyps_weaken_to_split (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases) (parent : Origin sig) (side : Bool)
    {A : Object sig.nBases} (x : Var (Ctx.ofHyps hyps ▻ P) A) :
    Origin.rekeyHypToSplit hyps.size parent side
        (OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
          (.hyp (sig := sig) hyps.size) x) =
      OriginEnv.weaken (A := P) (OriginEnv.ofHyps hyps)
        (.split parent side) x := by
  cases x with
  | here => simp [OriginEnv.weaken, Origin.rekeyHypToSplit]
  | there y =>
      have hne : OriginEnv.ofHyps hyps y ≠ .hyp (sig := sig) hyps.size :=
        OriginEnv.ofHyps_ne_size hyps y
      simp only [OriginEnv.weaken, OriginEnv.snoc]
      dsimp only [OriginEnv.ofHyps] at hne ⊢
      have hne' : hyps.size - 1 - Var.toRawIdx y ≠ hyps.size := by
        intro hi; exact hne (by rw [hi])
      simp [Origin.rekeyHypToSplit, hne']

end Equality
end Gimbal
