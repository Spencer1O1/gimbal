/-
  Finite atom registries and exhaustive source-context inhabitation analysis.

  Atom liveness is not monotone through function domains. Consequently the
  analyzer enumerates every finite mask; it does not grow a mask greedily.
-/

import Gimbal.Equality.Scherer.PairOrigin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Terminal atomic representatives -/

/-- The finite terminal representatives that require distinct base values. -/
structure AtomRegistry (R : AliasResolver sig) where
  refs : (q : Fin sig.nBases) → Finset (ResolvedRef R (.base q))

namespace AtomRegistry

variable {R : AliasResolver sig}

def empty (R : AliasResolver sig) : AtomRegistry R where
  refs := fun _ => ∅

def resolvedAtomCount (atoms : AtomRegistry R) (q : Fin sig.nBases) : Nat :=
  (atoms.refs q).card

@[simp] theorem resolvedAtomCount_empty (q : Fin sig.nBases) :
    (empty R).resolvedAtomCount q = 0 := by
  simp [resolvedAtomCount, empty]

end AtomRegistry

/-! ### Boolean inhabitation under an atom mask -/

end Gimbal.Equality.Scherer

namespace Gimbal.Object

/--
Whether the finite-set interpretation of an object is inhabited when exactly
the atoms in `live` are interpreted by nonempty sets.
-/
def inhabitedUnder {n : Nat} (live : Finset (Fin n)) : Object n → Bool
  | .base q => decide (q ∈ live)
  | .unit => true
  | .never => false
  | .prod A B => inhabitedUnder live A && inhabitedUnder live B
  | .coprod A B => inhabitedUnder live A || inhabitedUnder live B
  | .exp A B => !inhabitedUnder live A || inhabitedUnder live B

@[simp] theorem inhabitedUnder_base {n : Nat} (live : Finset (Fin n))
    (q : Fin n) :
    inhabitedUnder live (.base q) = decide (q ∈ live) := rfl

@[simp] theorem inhabitedUnder_unit {n : Nat} (live : Finset (Fin n)) :
    inhabitedUnder live (.unit : Object n) = true := rfl

@[simp] theorem inhabitedUnder_never {n : Nat} (live : Finset (Fin n)) :
    inhabitedUnder live (.never : Object n) = false := rfl

@[simp] theorem inhabitedUnder_prod {n : Nat} (live : Finset (Fin n))
    (A B : Object n) :
    inhabitedUnder live (.prod A B) =
      (inhabitedUnder live A && inhabitedUnder live B) := rfl

@[simp] theorem inhabitedUnder_coprod {n : Nat} (live : Finset (Fin n))
    (A B : Object n) :
    inhabitedUnder live (.coprod A B) =
      (inhabitedUnder live A || inhabitedUnder live B) := rfl

@[simp] theorem inhabitedUnder_exp {n : Nat} (live : Finset (Fin n))
    (A B : Object n) :
    inhabitedUnder live (.exp A B) =
      (!inhabitedUnder live A || inhabitedUnder live B) := rfl

end Gimbal.Object

namespace Gimbal.Equality.Scherer

variable {sig : Signature} {R : AliasResolver sig}

namespace StableCtx

/-- Every stable binder has an inhabited finite-set interpretation. -/
def inhabitedUnder (live : Finset (Fin sig.nBases)) : StableCtx sig → Bool
  | .empty => true
  | .snoc Γ S => inhabitedUnder live Γ && Object.inhabitedUnder live S.erase

@[simp] theorem inhabitedUnder_empty (live : Finset (Fin sig.nBases)) :
    inhabitedUnder live (StableCtx.empty : StableCtx sig) = true := rfl

@[simp] theorem inhabitedUnder_snoc (live : Finset (Fin sig.nBases))
    (Γ : StableCtx sig) (S : StableTy sig.nBases) :
    inhabitedUnder live (Γ.snoc S) =
      (inhabitedUnder live Γ && Object.inhabitedUnder live S.erase) := rfl

theorem binder_inhabited {live : Finset (Fin sig.nBases)}
    {Γ : StableCtx sig} (h : Γ.inhabitedUnder live = true)
    {S : StableTy sig.nBases} (x : StableVar Γ S) :
    Object.inhabitedUnder live S.erase = true := by
  induction x with
  | here => simpa using (Bool.and_eq_true_iff.mp h).2
  | there x ih => exact ih (Bool.and_eq_true_iff.mp h).1

end StableCtx

/-! ### Simultaneous live-support validity -/

def AtomRegistry.coveredBy (atoms : AtomRegistry R)
    (live : Finset (Fin sig.nBases)) : Bool :=
  decide (∀ q, (atoms.refs q).Nonempty → q ∈ live)

def supportsB (Γ : StableCtx sig) (atoms : AtomRegistry R)
    (live : Finset (Fin sig.nBases)) : Bool :=
  atoms.coveredBy live && Γ.inhabitedUnder live

/-- A simultaneous atom mask realizing every registered atom and stable type. -/
structure LiveSupport (Γ : StableCtx sig) (atoms : AtomRegistry R) where
  live : Finset (Fin sig.nBases)
  valid : supportsB Γ atoms live = true

namespace LiveSupport

variable {R : AliasResolver sig} {Γ : StableCtx sig}
  {atoms : AtomRegistry R}

theorem covered (L : LiveSupport Γ atoms) :
    atoms.coveredBy L.live = true :=
  (Bool.and_eq_true_iff.mp L.valid).1

theorem contextInhabited (L : LiveSupport Γ atoms) :
    Γ.inhabitedUnder L.live = true :=
  (Bool.and_eq_true_iff.mp L.valid).2

theorem registered_live (L : LiveSupport Γ atoms) (q : Fin sig.nBases)
    (h : (atoms.refs q).Nonempty) : q ∈ L.live := by
  have hc := L.covered
  simp only [AtomRegistry.coveredBy, decide_eq_true_eq] at hc
  exact hc q h

theorem binder_inhabited (L : LiveSupport Γ atoms)
    {S : StableTy sig.nBases} (x : StableVar Γ S) :
    Object.inhabitedUnder L.live S.erase = true :=
  StableCtx.binder_inhabited L.contextInhabited x

end LiveSupport

/-! ### Exhaustive executable analysis -/

/-- Every atom mask, in the deterministic order inherited from `Finset.univ`. -/
noncomputable def allAtomMasks (sig : Signature) : List (Finset (Fin sig.nBases)) :=
  (Finset.univ : Finset (Finset (Fin sig.nBases))).toList

@[simp] theorem mem_allAtomMasks (live : Finset (Fin sig.nBases)) :
    live ∈ allAtomMasks sig := by
  simp [allAtomMasks]

private def supportOfMask? (Γ : StableCtx sig) (atoms : AtomRegistry R)
    (live : Finset (Fin sig.nBases)) : Option (LiveSupport Γ atoms) :=
  if h : supportsB Γ atoms live = true then
    some ⟨live, h⟩
  else
    none

@[simp] private theorem supportOfMask?_isSome
    (Γ : StableCtx sig) (atoms : AtomRegistry R)
    (live : Finset (Fin sig.nBases)) :
    (supportOfMask? Γ atoms live).isSome = supportsB Γ atoms live := by
  unfold supportOfMask?
  split <;> simp_all

/-- Exhaustively search all atom masks and return the first valid support. -/
noncomputable def analyzeContext? (Γ : StableCtx sig) (atoms : AtomRegistry R) :
    Option (LiveSupport Γ atoms) :=
  ((allAtomMasks sig).filterMap (supportOfMask? Γ atoms)).head?

private theorem filterMap_support_nonempty_iff
    (masks : List (Finset (Fin sig.nBases))) :
    ((masks.filterMap (supportOfMask? Γ atoms)).head?).isSome = true ↔
      ∃ live ∈ masks, supportsB Γ atoms live = true := by
  induction masks with
  | nil => simp
    | cons live rest ih =>
      by_cases h : supportsB Γ atoms live = true
      · simp [supportOfMask?, h]
      · simp [supportOfMask?, h]

/-- Exhaustive analysis succeeds exactly when a live support exists. -/
theorem analyzeContext?_isSome_iff
    (Γ : StableCtx sig) (atoms : AtomRegistry R) :
    (analyzeContext? Γ atoms).isSome = true ↔
      Nonempty (LiveSupport Γ atoms) := by
  rw [analyzeContext?, filterMap_support_nonempty_iff]
  constructor
  · rintro ⟨live, _, h⟩
    exact ⟨⟨live, h⟩⟩
  · rintro ⟨L⟩
    exact ⟨L.live, mem_allAtomMasks L.live, L.valid⟩

/-- A returned analysis is itself the requested proof-relevant realization. -/
theorem analyzeContext?_eq_some_realizes
    {Γ : StableCtx sig} {atoms : AtomRegistry R}
    {L : LiveSupport Γ atoms} (_h : analyzeContext? Γ atoms = some L) :
    supportsB Γ atoms L.live = true := by
  exact L.valid

/-! ### Separator cardinalities and registered atom codes -/

variable {Γ : StableCtx sig} {atoms : AtomRegistry R}

def separatorCard (L : LiveSupport Γ atoms) (q : Fin sig.nBases) : Nat :=
  if q ∈ L.live then max 1 (atoms.resolvedAtomCount q) else 0

theorem separatorCard_pos_iff_live (L : LiveSupport Γ atoms)
    (q : Fin sig.nBases) :
    0 < separatorCard L q ↔ q ∈ L.live := by
  by_cases hq : q ∈ L.live
  · simp [separatorCard, hq]
  · simp [separatorCard, hq]

theorem resolvedAtomCount_le_separatorCard (L : LiveSupport Γ atoms)
    (q : Fin sig.nBases) :
    atoms.resolvedAtomCount q ≤ separatorCard L q := by
  by_cases hne : (atoms.refs q).Nonempty
  · have hq := L.registered_live q hne
    simp only [separatorCard, if_pos hq]
    exact Nat.le_max_right _ _
  · have hz : atoms.resolvedAtomCount q = 0 := by
      rw [AtomRegistry.resolvedAtomCount, Finset.card_eq_zero]
      exact Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hz]

/-- The registered representative's injective code in its separator carrier. -/
noncomputable def atomCode (L : LiveSupport Γ atoms) {q : Fin sig.nBases}
    (r : ResolvedRef R (.base q)) (hr : r ∈ atoms.refs q) :
    Fin (separatorCard L q) :=
  Fin.castLE (resolvedAtomCount_le_separatorCard L q)
    ((atoms.refs q).equivFin ⟨r, hr⟩)

theorem atomCode_injective (L : LiveSupport Γ atoms) {q : Fin sig.nBases}
    {r s : ResolvedRef R (.base q)}
    (hr : r ∈ atoms.refs q) (hs : s ∈ atoms.refs q)
    (h : atomCode L r hr = atomCode L s hs) : r = s := by
  have hv : ((atoms.refs q).equivFin ⟨r, hr⟩).val =
      ((atoms.refs q).equivFin ⟨s, hs⟩).val := by
    have := congrArg Fin.val h
    simpa [atomCode, Fin.castLE] using this
  have he : (atoms.refs q).equivFin ⟨r, hr⟩ =
      (atoms.refs q).equivFin ⟨s, hs⟩ := Fin.ext hv
  exact congrArg Subtype.val ((atoms.refs q).equivFin.injective he)

/-! ### Boundary fixtures -/

namespace LiveSupportFixtures

abbrev sig1 : Signature := ⟨1, #[]⟩
def q : Fin sig1.nBases := ⟨0, by decide⟩
def R0 : AliasResolver sig1 := AliasResolver.identity sig1
def emptyAtoms : AtomRegistry R0 := AtomRegistry.empty R0

abbrev Q : Object sig1.nBases := .base q
abbrev NotQ : Object sig1.nBases := .exp Q .never
abbrev NotNotQ : Object sig1.nBases := .exp NotQ .never

abbrev fTy : StableTy sig1.nBases := .neg (asNeg NotQ)
abbrev zTy : StableTy sig1.nBases := .neg (asNeg NotNotQ)
abbrev fCtx : StableCtx sig1 := .snoc .empty fTy
abbrev zCtx : StableCtx sig1 := .snoc .empty zTy
abbrev fzCtx : StableCtx sig1 := .snoc fCtx zTy

theorem f_forces_q_dead (L : LiveSupport fCtx emptyAtoms) : q ∉ L.live := by
  intro hq
  have h := L.binder_inhabited (.here : StableVar fCtx fTy)
  change Object.inhabitedUnder L.live (asNeg NotQ).erase = true at h
  rw [erase_asNeg] at h
  change Object.inhabitedUnder L.live NotQ = true at h
  simp [Object.inhabitedUnder, hq] at h

theorem z_forces_q_live (L : LiveSupport zCtx emptyAtoms) : q ∈ L.live := by
  by_contra hq
  have h := L.binder_inhabited (.here : StableVar zCtx zTy)
  change Object.inhabitedUnder L.live (asNeg NotNotQ).erase = true at h
  rw [erase_asNeg] at h
  change Object.inhabitedUnder L.live NotNotQ = true at h
  simp [Object.inhabitedUnder, hq] at h

theorem f_and_z_no_liveSupport :
    ¬ Nonempty (LiveSupport fzCtx emptyAtoms) := by
  rintro ⟨L⟩
  have hz : q ∈ L.live := by
    by_contra hq
    have h := L.binder_inhabited (.here : StableVar fzCtx zTy)
    change Object.inhabitedUnder L.live (asNeg NotNotQ).erase = true at h
    rw [erase_asNeg] at h
    change Object.inhabitedUnder L.live NotNotQ = true at h
    simp [Object.inhabitedUnder, hq] at h
  have hf := L.binder_inhabited
    (.there .here : StableVar fzCtx fTy)
  change Object.inhabitedUnder L.live (asNeg NotQ).erase = true at hf
  rw [erase_asNeg] at hf
  change Object.inhabitedUnder L.live NotQ = true at hf
  simp [Object.inhabitedUnder, hz] at hf

def zSupport : LiveSupport zCtx emptyAtoms where
  live := {q}
  valid := by native_decide

theorem zero_count_live_atom_gets_one : separatorCard zSupport q = 1 := by
  native_decide

def atom0 : ResolvedRef R0 Q := ResolvedRef.of R0 (rootOrigin sig1 Q 10 0)
def atom1 : ResolvedRef R0 Q := ResolvedRef.of R0 (rootOrigin sig1 Q 11 0)

def twoAtoms : AtomRegistry R0 where
  refs i := if h : i = q then
      h ▸ ({atom0, atom1} : Finset (ResolvedRef R0 Q))
    else ∅

abbrev atomCtx : StableCtx sig1 := .snoc .empty (.atom q)

def twoAtomSupport : LiveSupport atomCtx twoAtoms where
  live := {q}
  valid := by native_decide

theorem registered_atom_forces_live
    (L : LiveSupport atomCtx twoAtoms) : q ∈ L.live := by
  apply L.registered_live q
  refine ⟨atom0, ?_⟩
  simp [twoAtoms]

theorem atom0_mem : atom0 ∈ twoAtoms.refs q := by simp [twoAtoms]
theorem atom1_mem : atom1 ∈ twoAtoms.refs q := by simp [twoAtoms]

theorem distinct_registered_atoms : atom0 ≠ atom1 := by
  native_decide

theorem distinct_registered_codes :
    atomCode twoAtomSupport atom0 atom0_mem ≠
      atomCode twoAtomSupport atom1 atom1_mem := by
  intro h
  exact distinct_registered_atoms
    (atomCode_injective twoAtomSupport atom0_mem atom1_mem h)

/-- Interpreting every atom as nonempty already fails for `q → 0`. -/
theorem all_atoms_positive_shortcut_fails :
    supportsB fCtx emptyAtoms (Finset.univ : Finset (Fin sig1.nBases)) = false := by
  native_decide

theorem analyzer_rejects_f_and_z :
    (analyzeContext? fzCtx emptyAtoms).isSome = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  exact f_and_z_no_liveSupport
    ((analyzeContext?_isSome_iff fzCtx emptyAtoms).mp h)

end LiveSupportFixtures

end Gimbal.Equality.Scherer
