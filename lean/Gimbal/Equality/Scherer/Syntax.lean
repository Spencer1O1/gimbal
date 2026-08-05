/-
  Scherer-core polarized telescopes and context indices (S1 + S2 indices).

  Unpolarized contexts are `Gimbal.Equality.Ctx`. Goals are `neg N | pos P`.
  Arbitrary hypotheses enter the ordered `Pending` worklist via `asPending`.
  `NegCtx` is only a telescope of `Neg` (not the stable context).
-/

import Gimbal.Equality.LambdaSyntax
import Gimbal.Equality.Scherer.Polarized

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-- Invertible / saturated goal: negative formula or positive formula. -/
inductive Goal (n : Nat) : Type where
  | neg : Neg n → Goal n
  | pos : Pos n → Goal n

/-- Erase a goal to an unpolarized object. -/
def Goal.erase {n : Nat} : Goal n → Object n
  | .neg N => N.erase
  | .pos P => P.erase

@[simp] theorem Goal.erase_neg {n : Nat} (N : Neg n) :
    Goal.erase (.neg N) = N.erase := rfl

@[simp] theorem Goal.erase_pos {n : Nat} (P : Pos n) :
    Goal.erase (.pos P) = P.erase := rfl

/-- Telescope of negative polarized types. Not the Scherer stable context. -/
inductive NegCtx (sig : Signature) : Type where
  | empty : NegCtx sig
  | snoc : NegCtx sig → Neg sig.nBases → NegCtx sig

/-- Telescope of positive polarized types (snoc shape; not the forced worklist). -/
inductive PosCtx (sig : Signature) : Type where
  | empty : PosCtx sig
  | snoc : PosCtx sig → Pos sig.nBases → PosCtx sig

/-- Telescope of stable formula kinds (`StableTy`). -/
inductive StableCtx (sig : Signature) : Type where
  | empty : StableCtx sig
  | snoc : StableCtx sig → StableTy sig.nBases → StableCtx sig

/--
Ordered pending-positive worklist. The `cons` head is the next forced left
rule (pending-head variable).
-/
inductive Pending (sig : Signature) : Type where
  | empty : Pending sig
  | cons : Pos sig.nBases → Pending sig → Pending sig

/-- Membership of a stable formula in a stable context. -/
inductive StableVar {sig : Signature} : StableCtx sig → StableTy sig.nBases → Type where
  | here {Γ S} : StableVar (StableCtx.snoc Γ S) S
  | there {Γ S S'} : StableVar Γ S → StableVar (StableCtx.snoc Γ S') S

namespace NegCtx

def length : NegCtx sig → Nat
  | .empty => 0
  | .snoc Γ _ => Γ.length + 1

def erase : NegCtx sig → Ctx sig
  | .empty => .empty
  | .snoc Γ N => .snoc (erase Γ) N.erase

end NegCtx

namespace PosCtx

def length : PosCtx sig → Nat
  | .empty => 0
  | .snoc Γ _ => Γ.length + 1

def erase : PosCtx sig → Ctx sig
  | .empty => .empty
  | .snoc Γ P => .snoc (erase Γ) P.erase

end PosCtx

namespace StableCtx

def length : StableCtx sig → Nat
  | .empty => 0
  | .snoc Γ _ => Γ.length + 1

def erase : StableCtx sig → Ctx sig
  | .empty => .empty
  | .snoc Γ S => .snoc (erase Γ) S.erase

/-- Append `Δ` to the right of `Γ` (order-preserving). -/
def append : StableCtx sig → StableCtx sig → StableCtx sig
  | Γ, .empty => Γ
  | Γ, .snoc Δ S => (append Γ Δ).snoc S

end StableCtx

namespace Pending

def length : Pending sig → Nat
  | .empty => 0
  | .cons _ ps => ps.length + 1

/-- Append one positive at the right end (newest). Head/oldest is unchanged. -/
def concat : Pending sig → Pos sig.nBases → Pending sig
  | .empty, P => .cons P .empty
  | .cons Q qs, P => .cons Q (concat qs P)

/-- Auxiliary erasure: walk head-to-tail, snoc'ing onto an accumulator. -/
def eraseAux : Pending sig → Ctx sig → Ctx sig
  | .empty, acc => acc
  | .cons P ps, acc => eraseAux ps (acc.snoc P.erase)

/--
Erase pending to an object context. Head is oldest, so it becomes the
leftmost (oldest) binder of the resulting `Ctx`.
-/
def erase (ps : Pending sig) : Ctx sig :=
  eraseAux ps .empty

end Pending

/-- Weaken a stable variable across an appended right context. -/
def StableVar.weakenAppend {Γ : StableCtx sig} {S : StableTy sig.nBases} :
    (Δ : StableCtx sig) → StableVar Γ S → StableVar (Γ.append Δ) S
  | .empty, x => by simpa [StableCtx.append] using x
  | .snoc Δ' _, x => .there (StableVar.weakenAppend Δ' x)

/--
Translate an unpolarized context into a snoc positive telescope (S1 bridge).
-/
def asPosCtx : Ctx sig → PosCtx sig
  | .empty => .empty
  | .snoc Γ A => .snoc (asPosCtx Γ) (asPos A)

/--
Order-preserving root translation `Ctx → Pending`: oldest hypothesis becomes
the pending head (next forced left rule).
-/
def asPending : Ctx sig → Pending sig
  | .empty => .empty
  | .snoc Γ A => Pending.concat (asPending Γ) (asPos A)

@[simp] theorem NegCtx.erase_empty :
    (NegCtx.empty : NegCtx sig).erase = .empty := rfl

@[simp] theorem NegCtx.erase_snoc (Γ : NegCtx sig) (N : Neg sig.nBases) :
    (Γ.snoc N).erase = Γ.erase.snoc N.erase := rfl

@[simp] theorem PosCtx.erase_empty :
    (PosCtx.empty : PosCtx sig).erase = .empty := rfl

@[simp] theorem PosCtx.erase_snoc (Γ : PosCtx sig) (P : Pos sig.nBases) :
    (Γ.snoc P).erase = Γ.erase.snoc P.erase := rfl

@[simp] theorem StableCtx.erase_empty :
    (StableCtx.empty : StableCtx sig).erase = .empty := rfl

@[simp] theorem StableCtx.erase_snoc (Γ : StableCtx sig) (S : StableTy sig.nBases) :
    (Γ.snoc S).erase = Γ.erase.snoc S.erase := rfl

@[simp] theorem StableCtx.append_empty (Γ : StableCtx sig) :
    Γ.append .empty = Γ := rfl

@[simp] theorem StableCtx.append_snoc (Γ Δ : StableCtx sig) (S : StableTy sig.nBases) :
    Γ.append (Δ.snoc S) = (Γ.append Δ).snoc S := rfl

@[simp] theorem Pending.concat_empty (P : Pos sig.nBases) :
    Pending.concat (.empty : Pending sig) P = .cons P .empty := rfl

@[simp] theorem Pending.concat_cons (Q : Pos sig.nBases) (qs : Pending sig)
    (P : Pos sig.nBases) :
    Pending.concat (.cons Q qs) P = .cons Q (Pending.concat qs P) := rfl

@[simp] theorem asPosCtx_empty :
    asPosCtx (Ctx.empty : Ctx sig) = .empty := rfl

@[simp] theorem asPosCtx_snoc (Γ : Ctx sig) (A : Object sig.nBases) :
    asPosCtx (Γ.snoc A) = (asPosCtx Γ).snoc (asPos A) := rfl

@[simp] theorem asPending_empty :
    asPending (Ctx.empty : Ctx sig) = .empty := rfl

@[simp] theorem asPending_snoc (Γ : Ctx sig) (A : Object sig.nBases) :
    asPending (Γ.snoc A) = Pending.concat (asPending Γ) (asPos A) := rfl

@[simp] theorem erase_asPosCtx (Γ : Ctx sig) :
    (asPosCtx Γ).erase = Γ := by
  induction Γ with
  | empty => rfl
  | snoc Γ A ih =>
    simp only [asPosCtx_snoc, PosCtx.erase_snoc, erase_asPos, ih]

theorem length_asPosCtx (Γ : Ctx sig) :
    (asPosCtx Γ).length = Γ.length := by
  induction Γ with
  | empty => rfl
  | snoc Γ A ih =>
    simp only [asPosCtx, PosCtx.length, Ctx.length, ih]

theorem length_PosCtx_erase (Γ : PosCtx sig) :
    Γ.erase.length = Γ.length := by
  induction Γ with
  | empty => rfl
  | snoc Γ P ih =>
    simp only [PosCtx.erase, Ctx.length, PosCtx.length, ih]

theorem length_NegCtx_erase (Γ : NegCtx sig) :
    Γ.erase.length = Γ.length := by
  induction Γ with
  | empty => rfl
  | snoc Γ N ih =>
    simp only [NegCtx.erase, Ctx.length, NegCtx.length, ih]

theorem length_StableCtx_erase (Γ : StableCtx sig) :
    Γ.erase.length = Γ.length := by
  induction Γ with
  | empty => rfl
  | snoc Γ S ih =>
    simp only [StableCtx.erase, Ctx.length, StableCtx.length, ih]

theorem length_StableCtx_append (Γ Δ : StableCtx sig) :
    (Γ.append Δ).length = Γ.length + Δ.length := by
  induction Δ with
  | empty => simp [StableCtx.append, StableCtx.length]
  | snoc Δ S ih =>
    simp only [StableCtx.append_snoc, StableCtx.length, ih, Nat.add_assoc]

theorem length_Pending_concat (ps : Pending sig) (P : Pos sig.nBases) :
    (Pending.concat ps P).length = ps.length + 1 := by
  induction ps with
  | empty => rfl
  | cons Q qs ih =>
    simp only [Pending.concat_cons, Pending.length, ih]

theorem length_asPending (Γ : Ctx sig) :
    (asPending Γ).length = Γ.length := by
  induction Γ with
  | empty => rfl
  | snoc Γ A ih =>
    simp only [asPending_snoc, length_Pending_concat, Ctx.length, ih]

private theorem Pending.eraseAux_concat (ps : Pending sig) (P : Pos sig.nBases)
    (acc : Ctx sig) :
    Pending.eraseAux (Pending.concat ps P) acc =
      (Pending.eraseAux ps acc).snoc P.erase := by
  induction ps generalizing acc with
  | empty => rfl
  | cons Q qs ih =>
    simp only [Pending.concat_cons, Pending.eraseAux, ih]

/-- Erasure of `asPending` recovers the object context exactly (order-preserving). -/
@[simp] theorem erase_asPending (Γ : Ctx sig) :
    (asPending Γ).erase = Γ := by
  induction Γ with
  | empty => rfl
  | snoc Γ A ih =>
    simp only [asPending_snoc, Pending.erase] at ih ⊢
    rw [Pending.eraseAux_concat, erase_asPos, ih]

/-- Erase a stable variable to an unpolarized de Bruijn variable. -/
def StableVar.erase {Γ : StableCtx sig} {S : StableTy sig.nBases} :
    StableVar Γ S → Var Γ.erase S.erase
  | .here => .here
  | .there x => .there (StableVar.erase x)

/--
Exact erasure context for an invertible judgment: stable binders, then pending
binders with pending-head oldest among the pending segment.
-/
def eraseInvCtx (Γ : StableCtx sig) (ps : Pending sig) : Ctx sig :=
  Pending.eraseAux ps Γ.erase

/-- Exact erasure context for saturated judgments: `old ++ new ++ pending`. -/
def eraseSInvCtx (Old New : StableCtx sig) (ps : Pending sig) : Ctx sig :=
  Pending.eraseAux ps (Old.append New).erase

@[simp] theorem eraseInvCtx_empty (Γ : StableCtx sig) :
    eraseInvCtx Γ .empty = Γ.erase := rfl

@[simp] theorem eraseInvCtx_cons (Γ : StableCtx sig) (P : Pos sig.nBases)
    (ps : Pending sig) :
    eraseInvCtx Γ (.cons P ps) = Pending.eraseAux ps (Γ.erase.snoc P.erase) :=
  rfl

@[simp] theorem eraseSInvCtx_empty_new (Old : StableCtx sig) (ps : Pending sig) :
    eraseSInvCtx Old .empty ps = eraseInvCtx Old ps := by
  simp only [eraseSInvCtx, eraseInvCtx, StableCtx.append_empty]

/-- Append object contexts (order-preserving). -/
def Ctx.append : Ctx sig → Ctx sig → Ctx sig
  | Γ, .empty => Γ
  | Γ, .snoc Δ A => (Ctx.append Γ Δ).snoc A

@[simp] theorem Ctx.append_empty (Γ : Ctx sig) : Ctx.append Γ .empty = Γ := rfl

@[simp] theorem Ctx.append_snoc (Γ Δ : Ctx sig) (A : Object sig.nBases) :
    Ctx.append Γ (Δ.snoc A) = (Ctx.append Γ Δ).snoc A := rfl

theorem StableCtx.erase_append (Γ Δ : StableCtx sig) :
    (Γ.append Δ).erase = Ctx.append Γ.erase Δ.erase := by
  induction Δ with
  | empty => rfl
  | snoc Δ S ih =>
    simp only [StableCtx.append_snoc, StableCtx.erase, Ctx.append_snoc, ih]

end Gimbal.Equality.Scherer
