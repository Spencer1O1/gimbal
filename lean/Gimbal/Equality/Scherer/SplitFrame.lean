/-
  Proof-relevant old/new frames for the count-two selector.

  Intrinsic contexts, resolved supports, and origin assignments are never
  capped.  Only the provider registries are capped, and their projection is
  the type-only `Ctx2` recurrence state.
-/

import Gimbal.Equality.Scherer.RetainedCtx
import Gimbal.Equality.Scherer.ElimObligation
import Mathlib.Data.Finset.Sort

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

theorem StableCtx.length_le_append (Old New : StableCtx sig) :
    Old.length ≤ (Old.append New).length := by
  induction New with
  | empty => simp
  | snoc New T ih => simpa [StableCtx.length] using Nat.le.step ih

namespace Plur

theorem mem_insert_cases {α : Type} [DecidableEq α]
    {a x : α} {p : Plur α} (h : x ∈ (insert a p).1) : x = a ∨ x ∈ p.1 := by
  unfold insert at h
  split at h
  · exact Or.inr h
  · split at h
    · simpa [Finset.mem_cons] using h
    · exact Or.inr h

theorem addAfter_empty {α : Type} [DecidableEq α] [LinearOrder α]
    (p : Plur α) : addAfter p empty = p := by
  apply Subtype.ext
  rw [coe_addAfter]
  have hq : quotient empty p = empty := by
    unfold quotient
    split
    · rfl
    · split
      · apply Subtype.ext
        simp [takeOldest, without]
      · rfl
  rw [hq]
  simp

end Plur

/-! ### Split frames -/

/--
An intrinsic frame together with old/new capped provider registries.  Side
invariants remember which side of `Old.append New` every retained variable
came from; support and origin data remain on the uncapped intrinsic context.
-/
structure SplitFrame (U : TypeUniverse sig) (R : AliasResolver sig) (O : Type)
    (Old New : StableCtx sig) where
  env : ResolvedEnv (Old.append New) O
  origins : OriginAssignment R (Old.append New)
  old : RetainedCtx U (Old.append New)
  new : RetainedCtx U (Old.append New)
  old_side : ∀ (S : ↥U.stable) (x : StableVar (Old.append New) S.1),
    x ∈ (old.slots S).1 → (x.level : Nat) < Old.length
  new_side : ∀ (S : ↥U.stable) (x : StableVar (Old.append New) S.1),
    x ∈ (new.slots S).1 → Old.length ≤ (x.level : Nat)

namespace SplitFrame

variable {U : TypeUniverse sig} {R : AliasResolver sig} {O : Type}
  {Old New : StableCtx sig}

/-- Start a round: every supplied provider is old and the new side is empty. -/
def start (env : ResolvedEnv Old O) (origins : OriginAssignment R Old)
    (providers : RetainedCtx U Old) : SplitFrame U R O Old .empty where
  env := env
  origins := origins
  old := providers
  new := RetainedCtx.empty
  old_side := fun _ x _ => x.level.isLt
  new_side := by
    intro _ _ hx
    exact (Finset.notMem_empty _ hx).elim

/-- Effective genuinely-new providers after old-priority capping. -/
def effectiveNew (f : SplitFrame U R O Old New) :
    RetainedCtx U (Old.append New) :=
  f.new.quotient f.old

/-- Providers visible at the boundary, with old representatives first. -/
def selected (f : SplitFrame U R O Old New) :
    RetainedCtx U (Old.append New) :=
  f.old.addAfter f.new

def before (f : SplitFrame U R O Old New) : Ctx2 U := f.old.toCtx2
def after (f : SplitFrame U R O Old New) : Ctx2 U := f.selected.toCtx2

theorem before_le_after (f : SplitFrame U R O Old New) :
    f.before.LE f.after :=
  RetainedCtx.old_le_addAfter f.old f.new

theorem strictGrow_iff_effectiveNew_nonempty (f : SplitFrame U R O Old New) :
    f.before.StrictGrow f.after ↔
      ∃ S, ((f.effectiveNew.slots S).1).Nonempty := by
  simpa [before, after, selected, effectiveNew] using
    RetainedCtx.strictGrow_addAfter_iff f.old f.new

theorem before_eq_after_iff_effectiveNew_empty
    (f : SplitFrame U R O Old New) :
    f.before = f.after ↔ ∀ S, f.effectiveNew.slots S = Plur.empty := by
  constructor
  · intro heq S
    apply Subtype.ext
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hg : f.before.StrictGrow f.after :=
      (strictGrow_iff_effectiveNew_nonempty f).mpr ⟨S, ⟨x, hx⟩⟩
    exact hg.2 heq
  · intro h
    have hs : f.selected = f.old :=
      (RetainedCtx.addAfter_eq_iff_quotient_empty f.old f.new).mpr h
    simp [before, after, hs]

/-! ### Intrinsic growth and round reset -/

/-- Store one stable binder.  Intrinsic data grows; only the new registry is inserted. -/
def push (f : SplitFrame U R O Old New) (S : ↥U.stable)
    (K : DepSupport O) (source : ResolvedRef R S.1.erase) :
    SplitFrame U R O Old (New.snoc S.1) where
  env := ResolvedEnv.extend f.env K
  origins := f.origins.snoc source
  old := f.old.weaken S.1
  new := f.new.push S
  old_side := by
    intro T x hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
    subst x
    exact f.old_side T y hy
  new_side := by
    intro T x hx
    by_cases hT : T = S
    · subst T
      have hx0 := hx
      simp only [RetainedCtx.push, RetainedCtx.insert,
        Function.update_self] at hx0
      have hx' := Plur.mem_insert_cases hx0
      rcases hx' with rfl | hx'
      · simpa [StableVar.level, StableCtx.length] using
          StableCtx.length_le_append Old New
      · obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx'
        subst x
        exact f.new_side S y hy
    · have hx' : x ∈ ((f.new.weaken S.1).slots T).1 := by
        change x ∈ (Function.update (f.new.weaken S.1).slots S
          (Plur.insert .here ((f.new.weaken S.1).slots S)) T).1 at hx
        simpa [hT] using hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx'
      subst x
      exact f.new_side T y hy

theorem push_env_preserves (f : SplitFrame U R O Old New) (S : ↥U.stable)
    (K : DepSupport O) (source : ResolvedRef R S.1.erase) :
    ResolvedEnv.Preserves StableRename.weaken f.env (f.push S K source).env := by
  intro _ x
  rfl

theorem push_origins_preserves (f : SplitFrame U R O Old New)
    (S : ↥U.stable) (K : DepSupport O) (source : ResolvedRef R S.1.erase) :
    OriginAssignment.Preserves StableRename.weaken f.origins
      (f.push S K source).origins := by
  intro _ x
  rfl

@[simp] theorem push_env_here (f : SplitFrame U R O Old New)
    (S : ↥U.stable) (K : DepSupport O) (source : ResolvedRef R S.1.erase) :
    (f.push S K source).env S.1 .here = K := rfl

@[simp] theorem push_origin_here (f : SplitFrame U R O Old New)
    (S : ↥U.stable) (K : DepSupport O) (source : ResolvedRef R S.1.erase) :
    (f.push S K source).origins.ref (.here :
      StableVar ((Old.append New).snoc S.1) S.1) = source := rfl

/-- Promote exactly the selected providers; begin the next round with no new providers. -/
def reset (f : SplitFrame U R O Old New) :
    SplitFrame U R O (Old.append New) .empty where
  env := f.env
  origins := f.origins
  old := f.selected
  new := RetainedCtx.empty
  old_side := fun _ x _ => x.level.isLt
  new_side := by
    intro _ _ hx
    exact (Finset.notMem_empty _ hx).elim

@[simp] theorem reset_env (f : SplitFrame U R O Old New) :
    f.reset.env = f.env := rfl

@[simp] theorem reset_origins (f : SplitFrame U R O Old New) :
    f.reset.origins = f.origins := rfl

@[simp] theorem reset_old (f : SplitFrame U R O Old New) :
    f.reset.old = f.selected := rfl

theorem reset_effectiveNew_empty (f : SplitFrame U R O Old New) :
    ∀ S, f.reset.effectiveNew.slots S = Plur.empty := by
  intro S
  change Plur.quotient Plur.empty (f.selected.slots S) = Plur.empty
  unfold Plur.quotient
  split
  · rfl
  · split
    · apply Subtype.ext
      simp [Plur.takeOldest, Plur.without]
    · rfl

@[simp] theorem reset_selected (f : SplitFrame U R O Old New) :
    f.reset.selected = f.selected := by
  apply RetainedCtx.ext
  intro S
  exact Plur.addAfter_empty (f.selected.slots S)

/-! ### Store and pending boundaries -/

def storeAtom (f : SplitFrame U R O Old New) (hq : StableTy.atom q ∈ U.stable)
    (K : DepSupport O) (pending : PendingAssignment R (.cons (.atom q) ps)) :
    SplitFrame U R O Old (New.snoc (.atom q)) :=
  f.push ⟨.atom q, hq⟩ K (pending.ref .here)

def storeShift (f : SplitFrame U R O Old New) (hN : StableTy.neg N ∈ U.stable)
    (K : DepSupport O) (pending : PendingAssignment R (.cons (.shift N) ps)) :
    SplitFrame U R O Old (New.snoc (.neg N)) :=
  f.push ⟨.neg N, hN⟩ K (pending.ref .here)

@[simp] theorem storeAtom_origin_here (f : SplitFrame U R O Old New)
    (hq : StableTy.atom q ∈ U.stable) (K : DepSupport O)
    (pending : PendingAssignment R (.cons (.atom q) ps)) :
    (f.storeAtom hq K pending).origins.ref .here = pending.ref .here := rfl

@[simp] theorem storeShift_origin_here (f : SplitFrame U R O Old New)
    (hN : StableTy.neg N ∈ U.stable) (K : DepSupport O)
    (pending : PendingAssignment R (.cons (.shift N) ps)) :
    (f.storeShift hN K pending).origins.ref .here = pending.ref .here := rfl

/-- Pending lambda/case/batch results do not alter the stable frame before a store. -/
def pending (f : SplitFrame U R O Old New) (_ps : Pending sig) := f
def lambdaPending (f : SplitFrame U R O Old New) (P : Pos sig.nBases) :=
  f.pending (.cons P .empty)
def casePending (f : SplitFrame U R O Old New) (P : Pos sig.nBases) :=
  f.pending (.cons P .empty)
def batchPending (f : SplitFrame U R O Old New) (ps : Pending sig) := f.pending ps

@[simp] theorem pending_eq (f : SplitFrame U R O Old New) (ps : Pending sig) :
    f.pending ps = f := rfl

/-! ### Sealed provider enumeration -/

/-- A selected representative sealed by its registry membership proof. -/
abbrev Rep (f : SplitFrame U R O Old New) (S : ↥U.stable) :=
  {x : StableVar (Old.append New) S.1 // x ∈ (f.selected.slots S).1}

def reps (f : SplitFrame U R O Old New) (S : ↥U.stable) : List (Rep f S) :=
  (f.selected.slots S).1.attach.sort (· ≤ ·)

namespace Rep

variable {f : SplitFrame U R O Old New} {S : ↥U.stable}

def support (r : Rep f S) : DepSupport O := f.env S.1 r.1
def origin (r : Rep f S) : ResolvedRef R S.1.erase := f.origins.ref r.1

def toFreshSNeg (r : Rep f ⟨.neg N, hN⟩) :
    FreshSNeg (Old.append New) N := ⟨.var r.1, rfl⟩

def toFreshSAtom (r : Rep f ⟨.atom q, hq⟩) :
    FreshSPos (Old.append New) (.atom q) := ⟨.atom r.1, rfl⟩

@[simp] theorem toFreshSNeg_support [DecidableEq O]
    (r : Rep f ⟨.neg N, hN⟩) :
    r.toFreshSNeg.neutral.resolvedSupport f.env = r.support := rfl

@[simp] theorem toFreshSAtom_support [DecidableEq O]
    (r : Rep f ⟨.atom q, hq⟩) :
    r.toFreshSAtom.neutral.resolvedSupport f.env = r.support := rfl

end Rep

def selectedNegatives (f : SplitFrame U R O Old New)
    (N : Neg sig.nBases) (hN : StableTy.neg N ∈ U.stable) :
    List (FreshSNeg (Old.append New) N) :=
  (f.reps ⟨.neg N, hN⟩).map Rep.toFreshSNeg

def selectedAtoms (f : SplitFrame U R O Old New)
    (q : Fin sig.nBases) (hq : StableTy.atom q ∈ U.stable) :
    List (FreshSPos (Old.append New) (.atom q)) :=
  (f.reps ⟨.atom q, hq⟩).map Rep.toFreshSAtom

theorem mem_selectedNegatives_sealed {f : SplitFrame U R O Old New}
    {N : Neg sig.nBases} {hN : StableTy.neg N ∈ U.stable}
    {n : FreshSNeg (Old.append New) N} (hn : n ∈ f.selectedNegatives N hN) :
    ∃ r : Rep f ⟨.neg N, hN⟩, r ∈ f.reps _ ∧ n.neutral = .var r.1 := by
  simp only [selectedNegatives, List.mem_map] at hn
  obtain ⟨r, hr, rfl⟩ := hn
  exact ⟨r, hr, rfl⟩

theorem mem_selectedAtoms_sealed {f : SplitFrame U R O Old New}
    {q : Fin sig.nBases} {hq : StableTy.atom q ∈ U.stable}
    {p : FreshSPos (Old.append New) (.atom q)} (hp : p ∈ f.selectedAtoms q hq) :
    ∃ r : Rep f ⟨.atom q, hq⟩, r ∈ f.reps _ ∧ p.neutral = .atom r.1 := by
  simp only [selectedAtoms, List.mem_map] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  exact ⟨r, hr, rfl⟩

/-! ### Search-boundary bridge -/

def enterBoundary (f : SplitFrame U R O Old New) (P : BoundedPos U)
    (memo : VisitMemory U) : Option (VisitMemory U) :=
  Gimbal.Equality.Scherer.enterBoundary f.before f.after f.before_le_after P memo

theorem enterBoundary_of_effectiveNew_nonempty
    (f : SplitFrame U R O Old New) (P : BoundedPos U) (memo : VisitMemory U)
    (hne : ∃ S, (f.effectiveNew.slots S).1.Nonempty) :
    f.enterBoundary P memo = some memo := by
  exact Gimbal.Equality.Scherer.enterBoundary_of_strictGrow
    ((strictGrow_iff_effectiveNew_nonempty f).mpr hne) P memo

theorem enterBoundary_of_effectiveNew_empty
    (f : SplitFrame U R O Old New) (P : BoundedPos U) (memo : VisitMemory U)
    (hempty : ∀ S, f.effectiveNew.slots S = Plur.empty) :
    f.enterBoundary P memo =
      memo.visitEmpty (MemoryKey.ofPos f.after P) := by
  simp [enterBoundary, Gimbal.Equality.Scherer.enterBoundary,
    (before_eq_after_iff_effectiveNew_empty f).mpr hempty]

end SplitFrame

/-! ### Boundary fixtures -/

namespace SplitFrameFixtures

open RetainedCtxFixtures

abbrev U0 := RetainedCtxFixtures.U
abbrev slot0 := RetainedCtxFixtures.slot
abbrev G0 : StableCtx sig0 := .empty
abbrev R0 := RetainedCtxFixtures.R

def F0 : SplitFrame U0 R0 O3 G0 .empty :=
  SplitFrame.start env0 E0 C0
def F1 : SplitFrame U0 R0 O3 G0 G1 := F0.push slot0 K0 r0
def F2 : SplitFrame U0 R0 O3 G0 G2 := F1.push slot0 K1 r1
def F3 : SplitFrame U0 R0 O3 G0 G3 := F2.push slot0 K2 r2

theorem duplicate_same_rep :
    F1.selected.insert slot0 (.here : StableVar G1 S) = F1.selected := by
  apply RetainedCtx.insert_of_mem
  native_decide

theorem first_push_one : F1.after slot0 = .one := by native_decide
theorem second_push_two : F2.after slot0 = .two := by native_decide
theorem third_push_capped : F3.after = F2.after := by native_decide

/-- The first two distinct labels remain attached to their actual variables. -/
theorem two_distinct_labels_retained :
    let newest : StableVar G2 S := .here
    let oldest : StableVar G2 S := .there .here
    newest ∈ (F2.selected.slots slot0).1 ∧
      oldest ∈ (F2.selected.slots slot0).1 ∧
      F2.env S newest = K1 ∧ F2.env S oldest = K0 ∧
      F2.origins.ref newest = r1 ∧ F2.origins.ref oldest = r0 := by
  native_decide

/-- The third intrinsic variable exists with its label but is outside the capped provider set. -/
theorem third_label_not_provided :
    F3.env S (.here : StableVar G3 S) = K2 ∧
      F3.origins.ref (.here : StableVar G3 S) = r2 ∧
      (.here : StableVar G3 S) ∉ (F3.selected.slots slot0).1 := by
  native_decide

def F2reset : SplitFrame U0 R0 O3 G2 .empty := F2.reset

theorem reset_promotes_selected : F2reset.old = F2.selected := rfl
theorem reset_clears_effectiveNew :
    ∀ T, F2reset.effectiveNew.slots T = Plur.empty :=
  SplitFrame.reset_effectiveNew_empty F2

def pendingShift : PendingAssignment R0
    (.cons (.shift (.shift .zero)) .empty) :=
  PendingAssignment.cons r0 (PendingAssignment.empty R0)

def storedShift := F0.storeShift Smem K0 pendingShift

theorem storeShift_reuses_origin :
    storedShift.origins.ref (.here : StableVar G1 S) = r0 := by
  exact SplitFrame.storeShift_origin_here F0 Smem K0 pendingShift

theorem pending_lambda_no_push : F0.lambdaPending .zero = F0 := rfl
theorem pending_case_no_push : F0.casePending .zero = F0 := rfl

/- Atomic batch-result storage uses the same store path after pending creation. -/
def UA : TypeUniverse PairTraceFixtures.TwoGenSig where
  positive := {PairOriginFixtures.AtomP}
  stable := {PairOriginFixtures.AtomS}

theorem atom_mem : PairOriginFixtures.AtomS ∈ UA.stable := by simp [UA]

def FA0 : SplitFrame UA
    (AliasResolver.identity PairTraceFixtures.TwoGenSig) O3 .empty .empty :=
  SplitFrame.start (ResolvedEnv.empty O3) (OriginAssignment.empty _)
    RetainedCtx.empty

def storedBatchAtom :=
  (FA0.batchPending PairOriginFixtures.OnePending).storeAtom atom_mem K0
    PairOriginFixtures.batchOne.resolved

theorem batch_result_stores_later :
    storedBatchAtom.origins.ref
      (.here : StableVar
        ((StableCtx.empty : StableCtx PairTraceFixtures.TwoGenSig).snoc
          PairOriginFixtures.AtomS) PairOriginFixtures.AtomS) =
      PairOriginFixtures.atomRef := by
  exact SplitFrame.storeAtom_origin_here FA0 atom_mem K0
    PairOriginFixtures.batchOne.resolved

/-- Once two old representatives are promoted, a capped third spends memory. -/
def cappedThird : SplitFrame U0 R0 O3 G2 G1 :=
  F2reset.push slot0 K2 r2

def zeroPos : BoundedPos U0 := ⟨.zero, by simp [U0, RetainedCtxFixtures.U]⟩

theorem cappedThird_effective_empty :
    ∀ T, cappedThird.effectiveNew.slots T = Plur.empty := by
  intro T
  have hT : T = slot0 := by
    apply Subtype.ext
    exact Finset.mem_singleton.mp
      (by simpa [U0, RetainedCtxFixtures.U] using T.2)
  subst T
  native_decide

theorem capped_third_spends_visit :
    cappedThird.enterBoundary zeroPos VisitMemory.empty =
      some (VisitMemory.empty.set
        (MemoryKey.ofPos cappedThird.after zeroPos) .one) := by
  unfold SplitFrame.enterBoundary
  apply Gimbal.Equality.Scherer.enterBoundary_eq_zero
  · exact (SplitFrame.before_eq_after_iff_effectiveNew_empty cappedThird).mpr
      cappedThird_effective_empty
  · rfl

end SplitFrameFixtures

end Gimbal.Equality.Scherer
