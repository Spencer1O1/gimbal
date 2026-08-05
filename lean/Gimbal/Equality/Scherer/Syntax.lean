/-
  Scherer-core polarized telescopes and context translation (S1).

  Unpolarized contexts are the existing `Gimbal.Equality.Ctx`. Arbitrary
  hypotheses polarize into the pending-positive telescope via `asPos`.
  `NegCtx` is only a telescope of `Neg` (not the stable context).
  `StableCtx` carries `StableTy` entries (`neg` or unshifted `atom`).
-/

import Gimbal.Equality.LambdaSyntax
import Gimbal.Equality.Scherer.Polarized

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-- Telescope of negative polarized types. Not the Scherer stable context. -/
inductive NegCtx (sig : Signature) : Type where
  | empty : NegCtx sig
  | snoc : NegCtx sig → Neg sig.nBases → NegCtx sig

/-- Telescope of positive polarized types (pending-positive / worklist shape). -/
inductive PosCtx (sig : Signature) : Type where
  | empty : PosCtx sig
  | snoc : PosCtx sig → Pos sig.nBases → PosCtx sig

/-- Telescope of stable formula kinds (`StableTy`). -/
inductive StableCtx (sig : Signature) : Type where
  | empty : StableCtx sig
  | snoc : StableCtx sig → StableTy sig.nBases → StableCtx sig

namespace NegCtx

def length : NegCtx sig → Nat
  | .empty => 0
  | .snoc Γ _ => Γ.length + 1

/-- Pointwise erasure of a negative telescope. -/
def erase : NegCtx sig → Ctx sig
  | .empty => .empty
  | .snoc Γ N => .snoc (erase Γ) N.erase

end NegCtx

namespace PosCtx

def length : PosCtx sig → Nat
  | .empty => 0
  | .snoc Γ _ => Γ.length + 1

/-- Pointwise erasure of a positive telescope. -/
def erase : PosCtx sig → Ctx sig
  | .empty => .empty
  | .snoc Γ P => .snoc (erase Γ) P.erase

end PosCtx

namespace StableCtx

def length : StableCtx sig → Nat
  | .empty => 0
  | .snoc Γ _ => Γ.length + 1

/-- Pointwise erasure of a stable telescope. -/
def erase : StableCtx sig → Ctx sig
  | .empty => .empty
  | .snoc Γ S => .snoc (erase Γ) S.erase

end StableCtx

/--
Translate an unpolarized context into the pending-positive telescope.
Initial arbitrary hypotheses enter here via `asPos`, not as stable/negative.
-/
def asPosCtx : Ctx sig → PosCtx sig
  | .empty => .empty
  | .snoc Γ A => .snoc (asPosCtx Γ) (asPos A)

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

@[simp] theorem asPosCtx_empty :
    asPosCtx (Ctx.empty : Ctx sig) = .empty := rfl

@[simp] theorem asPosCtx_snoc (Γ : Ctx sig) (A : Object sig.nBases) :
    asPosCtx (Γ.snoc A) = (asPosCtx Γ).snoc (asPos A) := rfl

/-- Erasure after pending-positive translation recovers the unpolarized context. -/
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

end Gimbal.Equality.Scherer
