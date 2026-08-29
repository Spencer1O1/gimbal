/-
  Realized scopes for Scherer-core consistency synthesis.

  A scope keeps the bounded resolved state, its intrinsic environment, the
  exact outer/current provenance realization, and the consumed-obligation
  coverage together.  The two transitions here are the only context changes
  needed by the later consistency derivation: reset a round, or append a
  resolved batch result.  No derivation, policy, selector, capacity bound, or
  executable oracle is defined in this module.
-/

import Mathlib.Data.Bool.Basic
import Gimbal.Equality.Scherer.ConsistencyQuery

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-- All realized data against which one consistency query is interpreted. -/
structure ConsistencyScope (U : SearchUniverse sig) (O : Type) (B : Nat)
    (Γ : StableCtx sig) where
  state : ResolvedState U O B
  env : ResolvedEnv Γ O
  frameInput : RealizedFrameInput state
  outer : VarMask Γ
  current : VarMask Γ
  realizes : FrameRealizes state frameInput Γ env outer current
  coverage : Finset (Obligation U O)

namespace ConsistencyScope

variable {U : SearchUniverse sig} {O : Type} {B : Nat} {Γ : StableCtx sig}

/-- Project a scope and requested output into the existing intrinsic query. -/
def query (s : ConsistencyScope U O B Γ) (target : Obligation U O)
    (useSig : UseSig) :
    IntrinsicResolvedQuery U O B Γ s.env s.outer s.current where
  query :=
    { state := s.state
      realizedFrame := s.frameInput
      coverage := s.coverage
      target := target
      useSig := useSig }
  realizes := s.realizes

@[simp] theorem query_state (s : ConsistencyScope U O B Γ)
    (target : Obligation U O) (useSig : UseSig) :
    (s.query target useSig).query.state = s.state := rfl

@[simp] theorem query_frameInput (s : ConsistencyScope U O B Γ)
    (target : Obligation U O) (useSig : UseSig) :
    (s.query target useSig).query.realizedFrame = s.frameInput := rfl

@[simp] theorem query_coverage (s : ConsistencyScope U O B Γ)
    (target : Obligation U O) (useSig : UseSig) :
    (s.query target useSig).query.coverage = s.coverage := rfl

@[simp] theorem query_target (s : ConsistencyScope U O B Γ)
    (target : Obligation U O) (useSig : UseSig) :
    (s.query target useSig).query.target = target := rfl

@[simp] theorem query_useSig (s : ConsistencyScope U O B Γ)
    (target : Obligation U O) (useSig : UseSig) :
    (s.query target useSig).query.useSig = useSig := rfl

/-! ### Round reset -/

/-- Reset preserves the explicit outer-provenance input pointwise. -/
def resetInput (s : ConsistencyScope U O B Γ) :
    RealizedFrameInput s.state.resetRound :=
  ⟨s.frameInput.outerNewAt⟩

/-- End a saturation round: keep types, supports, environment, outer
provenance, and coverage; clear current-round provenance. -/
def resetRound (s : ConsistencyScope U O B Γ) : ConsistencyScope U O B Γ :=
  let hR := s.realizes.toCtxRealizes.resetRound
  let input := s.resetInput
  { state := s.state.resetRound
    env := s.env
    frameInput := input
    outer := FrameRealizes.outerMask hR input
    current := FrameRealizes.currentMask hR
    realizes := FrameRealizes.canonical hR input
    coverage := s.coverage }

@[simp] theorem resetRound_state (s : ConsistencyScope U O B Γ) :
    s.resetRound.state = s.state.resetRound := rfl

@[simp] theorem resetRound_env (s : ConsistencyScope U O B Γ) :
    s.resetRound.env = s.env := rfl

@[simp] theorem resetRound_coverage (s : ConsistencyScope U O B Γ) :
    s.resetRound.coverage = s.coverage := rfl

@[simp] theorem resetRound_outer_input (s : ConsistencyScope U O B Γ)
    (i : Fin s.state.depth) :
    s.resetRound.frameInput.outerNewAt i = s.frameInput.outerNewAt i := rfl

theorem resetRound_outer (s : ConsistencyScope U O B Γ)
    {S : StableTy sig.nBases} (x : StableVar Γ S) :
    s.resetRound.outer S x = s.outer S x := by
  rw [s.resetRound.realizes.outer_eq S x, s.realizes.outer_eq S x]
  rfl

theorem resetRound_current_false (s : ConsistencyScope U O B Γ)
    {S : StableTy sig.nBases} (x : StableVar Γ S) :
    s.resetRound.current S x = false := by
  rw [s.resetRound.realizes.current_eq S x]
  have hEmpty := ResolvedState.currentRaw_resetRound_empty s.state
  change decide (_ ∈ s.state.resetRound.currentRaw) = false
  rw [hEmpty]
  simp
  exact Finset.notMem_empty _

/-! ### Resolved-result push -/

/-- A resolved result keeps all old outer bits and is not itself outer-new. -/
def pushInput (s : ConsistencyScope U O B Γ) (hd : s.state.depth < B)
    (S : UStable U) (K : DepSupport O) :
    RealizedFrameInput (s.state.pushResolved hd S K) where
  outerNewAt := Fin.lastCases false s.frameInput.outerNewAt

/-- Append one batch result.  It inherits exact resolved support `K`, is raw
current for this round, and is not outer-new. -/
def pushResolved (s : ConsistencyScope U O B Γ) (hd : s.state.depth < B)
    (S : UStable U) (K : DepSupport O) :
    ConsistencyScope U O B (Γ.snoc S.val) :=
  let hR : CtxRealizes (s.state.pushResolved hd S K) (Γ.snoc S.val)
      (ResolvedEnv.extend (S := S.val) s.env K) := by
    simpa [ResolvedState.pushResolved] using
      CtxRealizes.push s.realizes.toCtxRealizes hd S K
  let input := s.pushInput hd S K
  { state := s.state.pushResolved hd S K
    env := ResolvedEnv.extend (S := S.val) s.env K
    frameInput := input
    outer := FrameRealizes.outerMask hR input
    current := FrameRealizes.currentMask hR
    realizes := FrameRealizes.canonical hR input
    coverage := s.coverage }

@[simp] theorem pushResolved_state (s : ConsistencyScope U O B Γ)
    (hd : s.state.depth < B) (S : UStable U) (K : DepSupport O) :
    (s.pushResolved hd S K).state = s.state.pushResolved hd S K := rfl

@[simp] theorem pushResolved_env (s : ConsistencyScope U O B Γ)
    (hd : s.state.depth < B) (S : UStable U) (K : DepSupport O) :
    (s.pushResolved hd S K).env =
      ResolvedEnv.extend (S := S.val) s.env K := rfl

@[simp] theorem pushResolved_coverage (s : ConsistencyScope U O B Γ)
    (hd : s.state.depth < B) (S : UStable U) (K : DepSupport O) :
    (s.pushResolved hd S K).coverage = s.coverage := rfl

theorem pushResolved_new_support (s : ConsistencyScope U O B Γ)
    (hd : s.state.depth < B) (S : UStable U) (K : DepSupport O) :
    (s.pushResolved hd S K).state.depAt (Fin.last s.state.depth) = K :=
  ResolvedState.pushResolved_new_support s.state hd S K

theorem pushResolved_outer_here (s : ConsistencyScope U O B Γ)
    (hd : s.state.depth < B) (S : UStable U) (K : DepSupport O) :
    (s.pushResolved hd S K).outer S.val .here = false := by
  rw [(s.pushResolved hd S K).realizes.outer_eq S.val .here]
  have hidx :
      (s.pushResolved hd S K).realizes.toCtxRealizes.ofLevel
          (StableVar.level (.here : StableVar (Γ.snoc S.val) S.val)) =
        Fin.last s.state.depth := by
    apply Fin.ext
    simpa [CtxRealizes.ofLevel, StableVar.level, Fin.val_last] using
      s.realizes.toCtxRealizes.length_eq
  rw [hidx]
  simp [pushResolved, pushInput]

theorem pushResolved_current_here (s : ConsistencyScope U O B Γ)
    (hd : s.state.depth < B) (S : UStable U) (K : DepSupport O) :
    (s.pushResolved hd S K).current S.val .here = true := by
  rw [(s.pushResolved hd S K).realizes.current_eq S.val .here]
  have hidx :
      (s.pushResolved hd S K).realizes.toCtxRealizes.ofLevel
          (StableVar.level (.here : StableVar (Γ.snoc S.val) S.val)) =
        Fin.last s.state.depth := by
    apply Fin.ext
    simpa [CtxRealizes.ofLevel, StableVar.level, Fin.val_last] using
      s.realizes.toCtxRealizes.length_eq
  rw [hidx]
  exact decide_eq_true (ResolvedState.push_new_current s.state hd S K)

theorem pushResolved_outer_there (s : ConsistencyScope U O B Γ)
    (hd : s.state.depth < B) (S : UStable U) (K : DepSupport O)
    {T : StableTy sig.nBases} (x : StableVar Γ T) :
    (s.pushResolved hd S K).outer T (.there x) = s.outer T x := by
  rw [(s.pushResolved hd S K).realizes.outer_eq T (.there x),
    s.realizes.outer_eq T x]
  have hidx :
      (s.pushResolved hd S K).realizes.toCtxRealizes.ofLevel
          (StableVar.level (.there x : StableVar (Γ.snoc S.val) T)) =
        (s.realizes.toCtxRealizes.ofLevel x.level).castSucc := by
    apply Fin.ext
    rfl
  rw [hidx]
  simp [pushResolved, pushInput]

theorem pushResolved_current_there (s : ConsistencyScope U O B Γ)
    (hd : s.state.depth < B) (S : UStable U) (K : DepSupport O)
    {T : StableTy sig.nBases} (x : StableVar Γ T) :
    (s.pushResolved hd S K).current T (.there x) = s.current T x := by
  rw [(s.pushResolved hd S K).realizes.current_eq T (.there x),
    s.realizes.current_eq T x]
  have hidx :
      (s.pushResolved hd S K).realizes.toCtxRealizes.ofLevel
          (StableVar.level (.there x : StableVar (Γ.snoc S.val) T)) =
        (s.realizes.toCtxRealizes.ofLevel x.level).castSucc := by
    apply Fin.ext
    rfl
  rw [hidx]
  change decide ((s.realizes.toCtxRealizes.ofLevel x.level).castSucc ∈
      (s.state.push hd S K).currentRaw) =
    decide (s.realizes.toCtxRealizes.ofLevel x.level ∈ s.state.currentRaw)
  let i := s.realizes.toCtxRealizes.ofLevel x.level
  have hmem := ResolvedState.push_old_current_iff s.state hd S K i
  exact Bool.decide_congr hmem

theorem frameLabelAt_of_var (s : ConsistencyScope U O B Γ)
    {S : StableTy sig.nBases} (x : StableVar Γ S) :
    s.state.frameLabelAt s.frameInput
        (s.realizes.toCtxRealizes.ofLevel x.level) =
      (⟨S, s.realizes.stable_mem x⟩, s.env S x,
        ⟨s.outer S x, s.current S x⟩) :=
  s.realizes.frameLabelAt_of_var x

/-- Exact complete label of an old variable after a round reset. -/
theorem resetRound_frameLabelAt_of_var (s : ConsistencyScope U O B Γ)
    {S : StableTy sig.nBases} (x : StableVar Γ S) :
    s.resetRound.state.frameLabelAt s.resetRound.frameInput
        (s.resetRound.realizes.toCtxRealizes.ofLevel x.level) =
      (⟨S, s.resetRound.realizes.stable_mem x⟩, s.env S x,
        ⟨s.outer S x, false⟩) := by
  rw [s.resetRound.frameLabelAt_of_var x]
  simp only [resetRound_env, resetRound_outer, resetRound_current_false]

/-- Exact complete label of the freshly appended resolved result. -/
theorem pushResolved_frameLabelAt_here (s : ConsistencyScope U O B Γ)
    (hd : s.state.depth < B) (S : UStable U) (K : DepSupport O) :
    (s.pushResolved hd S K).state.frameLabelAt
        (s.pushResolved hd S K).frameInput
        ((s.pushResolved hd S K).realizes.toCtxRealizes.ofLevel
          (StableVar.level (.here : StableVar (Γ.snoc S.val) S.val))) =
      (⟨S.val, (s.pushResolved hd S K).realizes.stable_mem .here⟩, K,
        ⟨false, true⟩) := by
  rw [(s.pushResolved hd S K).frameLabelAt_of_var
    (.here : StableVar (Γ.snoc S.val) S.val)]
  simp only [pushResolved_env, ResolvedEnv.extend_here,
    pushResolved_outer_here, pushResolved_current_here]

/-- Every pre-existing variable retains its exact complete label after a
resolved-result push. -/
theorem pushResolved_frameLabelAt_there (s : ConsistencyScope U O B Γ)
    (hd : s.state.depth < B) (S : UStable U) (K : DepSupport O)
    {T : StableTy sig.nBases} (x : StableVar Γ T) :
    (s.pushResolved hd S K).state.frameLabelAt
        (s.pushResolved hd S K).frameInput
        ((s.pushResolved hd S K).realizes.toCtxRealizes.ofLevel
          (StableVar.level (.there x : StableVar (Γ.snoc S.val) T))) =
      (⟨T, (s.pushResolved hd S K).realizes.stable_mem (.there x)⟩,
        s.env T x, ⟨s.outer T x, s.current T x⟩) := by
  rw [(s.pushResolved hd S K).frameLabelAt_of_var
    (.there x : StableVar (Γ.snoc S.val) T)]
  simp only [pushResolved_env, ResolvedEnv.extend_there,
    pushResolved_outer_there, pushResolved_current_there]

/-! ### Exact strong-retrieval invariance of contracted frames -/

private theorem matchingLevel_of_frame_eq [DecidableEq O]
    {B₁ B₂ : Nat} {st₁ : ResolvedState U O B₁}
    {st₂ : ResolvedState U O B₂}
    {input₁ : RealizedFrameInput st₁} {input₂ : RealizedFrameInput st₂}
    (hframe : st₁.contractedFrame input₁ = st₂.contractedFrame input₂)
    (i : Fin st₁.depth) :
    ∃ j : Fin st₂.depth,
      (st₂.tyAt j).val = (st₁.tyAt i).val ∧ st₂.depAt j = st₁.depAt i := by
  have hmem : st₁.frameLabelAt input₁ i ∈ st₁.contractedFrame input₁ :=
    (st₁.mem_contractedFrame_iff input₁ _).2 ⟨i, rfl⟩
  rw [hframe] at hmem
  obtain ⟨j, hj⟩ := (st₂.mem_contractedFrame_iff input₂ _).1 hmem
  exact ⟨j, congrArg (fun label : FrameLabel U O => label.1.val) hj,
    congrArg (fun label : FrameLabel U O => label.2.1) hj⟩

/-- Equal contracted frames preserve exact-support strong retrieval. -/
theorem StrongAt.of_contractedFrame_eq [DecidableEq O]
    {B₁ B₂ : Nat} {st₁ : ResolvedState U O B₁}
    {st₂ : ResolvedState U O B₂}
    {input₁ : RealizedFrameInput st₁} {input₂ : RealizedFrameInput st₂}
    (hframe : st₁.contractedFrame input₁ = st₂.contractedFrame input₂)
    {P : Pos sig.nBases} {K : DepSupport O} :
    StrongAt st₁ P K → StrongAt st₂ P K := by
  rintro ⟨⟨sp, hK⟩⟩
  induction sp generalizing K with
  | negVar i hty =>
      obtain ⟨j, hjty, hjdep⟩ := matchingLevel_of_frame_eq hframe i
      exact (StrongAt.of_negVar j (hjty.trans hty)).exact (hjdep.trans hK)
  | atomVar i hty =>
      obtain ⟨j, hjty, hjdep⟩ := matchingLevel_of_frame_eq hframe i
      exact (StrongAt.of_atomVar j (hjty.trans hty)).exact (hjdep.trans hK)
  | inl sp ih => exact StrongAt.of_inl (ih hK)
  | inr sp ih => exact StrongAt.of_inr (ih hK)

/-- Exact-support strong retrieval depends only on the contracted frame. -/
theorem StrongAt.iff_of_contractedFrame_eq [DecidableEq O]
    {B₁ B₂ : Nat} {st₁ : ResolvedState U O B₁}
    {st₂ : ResolvedState U O B₂}
    {input₁ : RealizedFrameInput st₁} {input₂ : RealizedFrameInput st₂}
    (hframe : st₁.contractedFrame input₁ = st₂.contractedFrame input₂)
    (P : Pos sig.nBases) (K : DepSupport O) :
    StrongAt st₁ P K ↔ StrongAt st₂ P K :=
  ⟨StrongAt.of_contractedFrame_eq hframe,
    StrongAt.of_contractedFrame_eq hframe.symm⟩

/-- Scope-level form used by later query contraction and splice proofs. -/
theorem strongAt_iff_of_frame_eq [DecidableEq O]
    {B₁ B₂ : Nat} {Γ₁ Γ₂ : StableCtx sig}
    (s₁ : ConsistencyScope U O B₁ Γ₁)
    (s₂ : ConsistencyScope U O B₂ Γ₂)
    (hframe : s₁.state.contractedFrame s₁.frameInput =
      s₂.state.contractedFrame s₂.frameInput)
    (P : Pos sig.nBases) (K : DepSupport O) :
    StrongAt s₁.state P K ↔ StrongAt s₂.state P K :=
  StrongAt.iff_of_contractedFrame_eq hframe P K

end ConsistencyScope

/-! ### Boundary fixtures -/

namespace ConsistencyScopeFixtures

open FrameContractionFixtures

def scope0 : ConsistencyScope U0 O1 2 (.empty : StableCtx sig0) where
  state := st0
  env := env0
  frameInput := ⟨Fin.elim0⟩
  outer := FrameRealizes.outerMask (root_realizes U0 O1 2) ⟨Fin.elim0⟩
  current := FrameRealizes.currentMask (root_realizes U0 O1 2)
  realizes := FrameRealizes.canonical (root_realizes U0 O1 2) ⟨Fin.elim0⟩
  coverage := ∅

def pushedScope : ConsistencyScope U0 O1 2 Γ1 :=
  scope0.pushResolved hd0 US {o}

/-- A resolved result inherits support, is current, and is not outer-new. -/
theorem pushed_result_provenance :
    pushedScope.state.depAt (Fin.last 0) = ({o} : DepSupport O1) ∧
      pushedScope.outer US.val .here = false ∧
      pushedScope.current US.val .here = true := by
  exact ⟨scope0.pushResolved_new_support hd0 US {o},
    scope0.pushResolved_outer_here hd0 US {o},
    scope0.pushResolved_current_here hd0 US {o}⟩

/-- Round reset retains the inherited outer bit and clears current use. -/
theorem reset_preserves_outer_clears_current :
    let s : ConsistencyScope U0 O1 2 Γ1 :=
      { state := st1
        env := env1
        frameInput := input1
        outer := FrameRealizes.outerMask realizes1 input1
        current := FrameRealizes.currentMask realizes1
        realizes := frame1
        coverage := ∅ }
    s.resetRound.outer US.val .here = s.outer US.val .here ∧
      s.resetRound.current US.val .here = false := by
  intro s
  exact ⟨s.resetRound_outer .here, s.resetRound_current_false .here⟩

/-- Popping a local store level cannot manufacture a new outer dependency. -/
theorem store_pop_preserves_preexisting
    (K : RawSupport Γ1) : popSupport (wkSupport (S := US.val) K) = K :=
  pop_wkSupport K

def scope1 : ConsistencyScope U0 O1 2 Γ1 where
  state := st1
  env := env1
  frameInput := input1
  outer := FrameRealizes.outerMask realizes1 input1
  current := FrameRealizes.currentMask realizes1
  realizes := frame1
  coverage := ∅

def scope2 : ConsistencyScope U0 O1 2 Γ2 where
  state := st2
  env := env2
  frameInput := input2
  outer := FrameRealizes.outerMask realizes2 input2
  current := FrameRealizes.currentMask realizes2
  realizes := frame2
  coverage := ∅

/-- Duplicate occurrences with identical complete labels have identical
exact-support strong-retrieval behavior after frame contraction. -/
theorem equal_frame_strongAt :
    StrongAt scope2.state (.shift (.shift (.zero : Pos 0)))
        ({o} : DepSupport O1) ↔
      StrongAt scope1.state (.shift (.shift (.zero : Pos 0)))
        ({o} : DepSupport O1) :=
  ConsistencyScope.strongAt_iff_of_frame_eq scope2 scope1
    duplicate_identical_labels_contract _ _

end ConsistencyScopeFixtures

end Gimbal.Equality.Scherer
