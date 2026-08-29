/-
  Direct executable production from public intrinsic terms into the ordinary
  Scherer focused calculus. Principal reductions are delegated to the
  already-total ordinary cut operation.
-/

import Gimbal.Equality.Scherer.OrdinaryCutProto

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

abbrev RootEnv (Γ : Ctx sig) (Δ : StableCtx sig) : Type :=
  ∀ {A : Object sig.nBases}, Var Γ A → PosNeu Δ (asPos A)

namespace RootEnv

def empty {Δ : StableCtx sig} : RootEnv (.empty : Ctx sig) Δ :=
  fun x => nomatch x

def rename {Γ : Ctx sig} {Δ Ε : StableCtx sig}
    (ε : RootEnv Γ Δ) (ρ : StableRename Δ Ε) : RootEnv Γ Ε :=
  fun x => PosNeu.rename ρ (ε x)

def snoc {Γ : Ctx sig} {Δ : StableCtx sig} {A : Object sig.nBases}
    (ε : RootEnv Γ Δ) (p : PosNeu Δ (asPos A)) : RootEnv (Γ.snoc A) Δ :=
  fun {_} x =>
    match x with
    | .here => p
    | .there y => ε y

end RootEnv

namespace Pending

/-- Put the positive polarizations of `Γ`, oldest first, before `tail`. -/
def rootThen : Ctx sig → Pending sig → Pending sig
  | .empty, tail => tail
  | .snoc Γ A, tail => rootThen Γ (.cons (asPos A) tail)

theorem rootThen_concat (Γ : Ctx sig) (tail : Pending sig)
    (P : Pos sig.nBases) :
    rootThen Γ (Pending.concat tail P) =
      Pending.concat (rootThen Γ tail) P := by
  induction Γ generalizing tail with
  | empty => rfl
  | snoc Γ A ih =>
      simp only [rootThen]
      exact ih (.cons (asPos A) tail)

@[simp] theorem rootThen_empty (Γ : Ctx sig) :
    rootThen Γ .empty = asPending Γ := by
  induction Γ with
  | empty => rfl
  | snoc Γ A ih =>
      simp only [rootThen, asPending_snoc]
      rw [← Pending.concat_empty (asPos A), rootThen_concat, ih]

end Pending

def Inv.castPending {Γ : StableCtx sig} {ps qs : Pending sig}
    {G : Goal sig.nBases} (h : ps = qs) (t : Inv Γ ps G) : Inv Γ qs G :=
  h ▸ t

/-- Reflect a source-variable representation into the negative public goal. -/
def reflectObject {Γ : StableCtx sig} :
    (A : Object sig.nBases) →
      PosNeu Γ (asPos A) → Inv Γ .empty (.neg (asNeg A))
  | .base _, p => .focusShift (.up p)
  | .never, p => .focusShift (.up p)
  | .coprod _ _, p => .focusShift (.up p)
  | .unit, .shift t => t
  | .prod _ _, .shift t => t
  | .exp _ _, .shift t => t

/-- Invert one positive pending head while retaining an arbitrary tail. -/
def withPendingPosTail {Γ : StableCtx sig} {G : Goal sig.nBases}
    (P : Pos sig.nBases) (tail : Pending sig)
    (k : ∀ {Δ : StableCtx sig}, StableRename Γ Δ →
      PosNeu Δ P → Inv Δ tail G) :
    Inv Γ (.cons P tail) G :=
  match P with
  | .atom _ => .storeAtom (k StableRename.weaken (.atom .here))
  | .zero => .abort
  | .sum A B =>
      .caseSum
        (withPendingPosTail A tail fun ρ p => k ρ (.inl p))
        (withPendingPosTail B tail fun ρ p => k ρ (.inr p))
  | .shift N =>
      .storeShift
        (k StableRename.weaken (.shift (etaNeg N (.var .here))))
termination_by posCutSize P
decreasing_by all_goals simp [posCutSize] <;> omega

/-- Invert every source hypothesis, producing its branch-local environment. -/
def withRootContext {G : Goal sig.nBases} :
    (Γ : Ctx sig) → (tail : Pending sig) →
    (k : ∀ {Δ : StableCtx sig}, RootEnv Γ Δ → Inv Δ tail G) →
      Inv (.empty : StableCtx sig) (Pending.rootThen Γ tail) G
  | .empty, _, k => k RootEnv.empty
  | .snoc Γ A, tail, k =>
      withRootContext Γ (.cons (asPos A) tail) fun ε =>
        withPendingPosTail (asPos A) tail fun ρ p =>
          k (RootEnv.snoc (RootEnv.rename ε ρ) p)

/-! ### Direct production -/

/-- Compile directly under a branch-local representation of source variables. -/
def focusOpen {Γ : Ctx sig} {Δ : StableCtx sig}
    (ε : RootEnv Γ Δ) :
    {A : Object sig.nBases} → Tm Γ A → Inv Δ .empty (.neg (asNeg A))
  | _, .var x => reflectObject _ (ε x)
  | _, .unit => .unit
  | _, .abort t => cutObject (focusOpen ε t) .abort
  | _, .pair t u => .pair (focusOpen ε t) (focusOpen ε u)
  | _, .fst t => (focusOpen ε t).pendingFst
  | _, .snd t => (focusOpen ε t).pendingSnd
  | _, .inl (B := B) t =>
      cutObject (focusOpen ε t)
        (withPendingPos (asPos _) fun _ p =>
          .focusShift (.up (.inl (B := asPos B) p)))
  | _, .inr (A := A) t =>
      cutObject (focusOpen ε t)
        (withPendingPos (asPos _) fun _ p =>
          .focusShift (.up (.inr (A := asPos A) p)))
  | _, .case (A := A) (B := B) s l r =>
      cutObject (focusOpen ε s)
        (.caseSum
          (withPendingPos (asPos A) fun ρ p =>
            focusOpen (RootEnv.snoc (RootEnv.rename ε ρ) p) l)
          (withPendingPos (asPos B) fun ρ p =>
            focusOpen (RootEnv.snoc (RootEnv.rename ε ρ) p) r))
  | _, .lam (A := A) t =>
      .lam (withPendingPos (asPos A) fun ρ p =>
        focusOpen (RootEnv.snoc (RootEnv.rename ε ρ) p) t)
  | _, .app f a =>
      cutObject (focusOpen ε a) (Inv.asLam (focusOpen ε f))

/-- Every public term has a directly computed ordinary Scherer derivation. -/
def focusRoot {Γ : Ctx sig} {A : Object sig.nBases}
    (t : Tm Γ A) :
    Inv (.empty : StableCtx sig) (asPending Γ) (.neg (asNeg A)) :=
  Inv.castPending (Pending.rootThen_empty Γ)
    (withRootContext Γ .empty fun ε => focusOpen ε t)

/-! ### Executable producer fixtures -/

namespace FocusRootFixtures

open Fixtures

abbrev UnitObj : Object 0 := .unit
abbrev SumUnit : Object 0 := .coprod .unit .unit
abbrev ArrUnit : Object 0 := .exp .unit .unit

def isClosedUnit :
    Inv (sig := sig0) .empty .empty (.neg .one) → Bool
  | .unit => true

def betaIdentityTm : Tm (sig := sig0) .empty UnitObj :=
  .app (.lam (.var .here)) .unit

theorem beta_identity :
    isClosedUnit (focusRoot betaIdentityTm) = true := by
  native_decide

def pairProjectionTm : Tm (sig := sig0) .empty UnitObj :=
  .fst (.pair .unit .unit)

theorem pair_projection :
    isClosedUnit (focusRoot pairProjectionTm) = true := by
  native_decide

def caseInlTm : Tm (sig := sig0) .empty SumUnit :=
  .case
    (.inl (B := .unit) .unit)
    (.inl (B := .unit) .unit)
    (.inr (A := .unit) .unit)

def isClosedSumLeft :
    Inv (sig := sig0) .empty .empty (.neg (asNeg SumUnit)) → Bool
  | .focusShift (.up (.inl (.shift .unit))) => true
  | _ => false

theorem case_on_inl :
    isClosedSumLeft (focusRoot caseInlTm) = true := by
  native_decide

abbrev NeverCtx : Ctx sig0 := .empty ▻ .never

def abortNeverTm : Tm (sig := sig0) NeverCtx UnitObj :=
  .abort (.var .here)

def isRootAbort :
    Inv (sig := sig0) .empty (asPending NeverCtx) (.neg .one) → Bool
  | .abort => true

theorem abort_from_never_hypothesis :
    isRootAbort (focusRoot abortNeverTm) = true := by
  native_decide

def sigOpaque : Signature :=
  { nBases := 1
    generators := #[
      { source := .unit
        target := .base ⟨0, by omega⟩ }] }

abbrev OpaqueX : Object sigOpaque.nBases := .base ⟨0, by decide⟩

def opaqueGeneratorAppTm :
    Tm (genCtx sigOpaque) OpaqueX :=
  .app (.var (genVar sigOpaque ⟨0, by decide⟩)) .unit

def isOpaqueGeneratorApp :
    Inv (sig := sigOpaque) .empty (asPending (genCtx sigOpaque))
      (.neg (asNeg OpaqueX)) → Bool
  | .storeShift (.focusShift (.letShift (.app (.var .here) _) _)) => true
  | _ => false

/-- The generator remains an opaque neutral application; no body is unfolded. -/
theorem opaque_generator_application :
    isOpaqueGeneratorApp (focusRoot opaqueGeneratorAppTm) = true := by
  native_decide

def sigComputed : Signature :=
  { nBases := 1
    generators := #[
      { source := .unit
        target := .base ⟨0, by omega⟩ },
      { source := .base ⟨0, by omega⟩
        target := .unit }] }

abbrev ComputedX : Object sigComputed.nBases := .base ⟨0, by decide⟩

def computedShiftedArgumentTm :
    Tm (genCtx sigComputed) .unit :=
  .app
    (.var (genVar sigComputed ⟨1, by decide⟩))
    (.app (.var (genVar sigComputed ⟨0, by decide⟩)) .unit)

def isStoredTwiceUnit :
    Inv (sig := sigComputed) .empty (asPending (genCtx sigComputed))
      (.neg .one) → Bool
  | .storeShift (.storeShift .unit) => true
  | _ => false

/-- The result of the first opaque application crosses a `letShift` as the
positive argument of the second application. -/
theorem computed_shifted_argument :
    isStoredTwiceUnit (focusRoot computedShiftedArgumentTm) = true := by
  native_decide

def caseFunctionTm : Tm (sig := sig0) .empty ArrUnit :=
  .case
    (.inl (B := .unit) .unit)
    (.lam .unit)
    (.lam .unit)

def caseFunctionAppliedTm : Tm (sig := sig0) .empty UnitObj :=
  .app caseFunctionTm .unit

/-- A case-produced negative arrow crosses the case boundary and then applies. -/
theorem case_function_then_application :
    isClosedUnit (focusRoot caseFunctionAppliedTm) = true := by
  native_decide

end FocusRootFixtures

end Gimbal.Equality.Scherer
