/-
  Contraction of realized Scherer search frames.

  Equality of the existing `ContractedFrame` projections supplies, for every
  source occurrence, a target occurrence with the same complete label.  The
  resulting stable renaming may be many-to-one.  Its construction preserves
  stable type intrinsically, and the complete-label equality proves exact
  preservation of resolved support and both provenance masks.

  This is only the frame-contraction gate.  No splice, capacity, selector, S4,
  or public-comparator claim is made here.
-/

import Gimbal.Equality.Scherer.SearchNormalQuery

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Intrinsic realizations of explicit frame provenance -/

/--
An intrinsic context realizes both the resolved state and the explicit
outer/current provenance used by its contracted-frame projection.
-/
structure FrameRealizes {U : SearchUniverse sig} {O : Type} {B : Nat}
    (st : ResolvedState U O B) (input : RealizedFrameInput st)
    (Γ : StableCtx sig) (env : ResolvedEnv Γ O)
    (outer current : VarMask Γ) : Prop extends CtxRealizes st Γ env where
  outer_eq : ∀ (S : StableTy sig.nBases) (x : StableVar Γ S),
    outer S x = input.outerNewAt (toCtxRealizes.ofLevel x.level)
  current_eq : ∀ (S : StableTy sig.nBases) (x : StableVar Γ S),
    current S x = decide
      (toCtxRealizes.ofLevel x.level ∈ st.currentRaw)

namespace FrameRealizes

variable {U : SearchUniverse sig} {O : Type} {B : Nat}
  {st : ResolvedState U O B} {input : RealizedFrameInput st}
  {Γ : StableCtx sig} {env : ResolvedEnv Γ O}
  {outer current : VarMask Γ}

/-- Intrinsic outer mask induced by a context realization and frame input. -/
def outerMask (h : CtxRealizes st Γ env) (input : RealizedFrameInput st) :
    VarMask Γ := fun _ x => input.outerNewAt (h.ofLevel x.level)

/-- Intrinsic current mask induced by the resolved state's current levels. -/
def currentMask (h : CtxRealizes st Γ env) : VarMask Γ :=
  fun _ x => decide (h.ofLevel x.level ∈ st.currentRaw)

/-- Every ordinary context realization canonically realizes the explicit
frame input with its induced provenance masks. -/
theorem canonical (h : CtxRealizes st Γ env) (input : RealizedFrameInput st) :
    FrameRealizes st input Γ env (outerMask h input) (currentMask h) where
  toCtxRealizes := h
  outer_eq := by intro _ _; rfl
  current_eq := by intro _ _; rfl

private theorem toLevel_ofLevel (h : FrameRealizes st input Γ env outer current)
    (i : StableLevel Γ) :
    h.toCtxRealizes.toLevel (h.toCtxRealizes.ofLevel i) = i := by
  apply Fin.ext
  rfl

private theorem ofLevel_toLevel (h : FrameRealizes st input Γ env outer current)
    (i : Fin st.depth) :
    h.toCtxRealizes.ofLevel (h.toCtxRealizes.toLevel i) = i := by
  apply Fin.ext
  rfl

/-- Every intrinsic variable's stable type occurs in the search universe. -/
theorem stable_mem (h : FrameRealizes st input Γ env outer current)
    {S : StableTy sig.nBases} (x : StableVar Γ S) : S ∈ U.stable := by
  have hty := h.toCtxRealizes.ty_eq
    (h.toCtxRealizes.ofLevel x.level)
  change (st.tyAt (h.toCtxRealizes.ofLevel x.level)).val =
    Γ.typeAtLevel
      (h.toCtxRealizes.toLevel (h.toCtxRealizes.ofLevel x.level)) at hty
  have hlevel :
      h.toCtxRealizes.toLevel (h.toCtxRealizes.ofLevel x.level) = x.level :=
    toLevel_ofLevel h x.level
  rw [hlevel, StableCtx.typeAtLevel_level x] at hty
  exact hty ▸ (st.tyAt (h.toCtxRealizes.ofLevel x.level)).property

/-- The abstract complete label at an intrinsic variable is exactly its type,
resolved support, and the two intrinsic provenance masks. -/
theorem frameLabelAt_of_var
    (h : FrameRealizes st input Γ env outer current)
    {S : StableTy sig.nBases} (x : StableVar Γ S) :
    st.frameLabelAt input (h.toCtxRealizes.ofLevel x.level) =
      (⟨S, h.stable_mem x⟩, env S x, ⟨outer S x, current S x⟩) := by
  apply Prod.ext
  · apply Subtype.ext
    have hty := h.toCtxRealizes.ty_eq
      (h.toCtxRealizes.ofLevel x.level)
    change (st.tyAt (h.toCtxRealizes.ofLevel x.level)).val =
      Γ.typeAtLevel
        (h.toCtxRealizes.toLevel (h.toCtxRealizes.ofLevel x.level)) at hty
    rw [toLevel_ofLevel h x.level, StableCtx.typeAtLevel_level x] at hty
    exact hty
  · apply Prod.ext
    · exact h.toCtxRealizes.dep_eq S x
    · exact congrArg₂ (fun o c => (⟨o, c⟩ : SearchProv))
        (h.outer_eq S x).symm (h.current_eq S x).symm

/-- Reconstruct the exact intrinsic target variable at an abstract level. -/
noncomputable def varAt
    (h : FrameRealizes st input Γ env outer current) (i : Fin st.depth) :
    StableVar Γ (st.tyAt i).val := by
  let lev := h.toCtxRealizes.toLevel i
  have hty : (st.tyAt i).val = Γ.typeAtLevel lev :=
    h.toCtxRealizes.ty_eq i
  exact cast (congrArg (StableVar Γ) hty.symm) (StableVar.atLevel Γ lev)

private theorem level_cast {Γ : StableCtx sig} {S T : StableTy sig.nBases}
    (hST : S = T) (x : StableVar Γ S) :
    (cast (congrArg (StableVar Γ) hST) x).level = x.level := by
  cases hST
  rfl

@[simp] theorem level_varAt
    (h : FrameRealizes st input Γ env outer current) (i : Fin st.depth) :
    (h.varAt i).level = h.toCtxRealizes.toLevel i := by
  unfold varAt
  exact (level_cast (h.toCtxRealizes.ty_eq i).symm
    (StableVar.atLevel Γ (h.toCtxRealizes.toLevel i))).trans
      (StableVar.level_atLevel Γ (h.toCtxRealizes.toLevel i))

@[simp] theorem ofLevel_level_varAt
    (h : FrameRealizes st input Γ env outer current) (i : Fin st.depth) :
    h.toCtxRealizes.ofLevel (h.varAt i).level = i := by
  rw [level_varAt]
  exact ofLevel_toLevel h i

theorem env_varAt
    (h : FrameRealizes st input Γ env outer current) (i : Fin st.depth) :
    env (st.tyAt i).val (h.varAt i) = st.depAt i := by
  rw [← h.toCtxRealizes.depAt_eq_env (h.varAt i)]
  rw [ofLevel_level_varAt]

theorem outer_varAt
    (h : FrameRealizes st input Γ env outer current) (i : Fin st.depth) :
    outer (st.tyAt i).val (h.varAt i) = input.outerNewAt i := by
  rw [h.outer_eq]
  rw [ofLevel_level_varAt]

theorem current_varAt
    (h : FrameRealizes st input Γ env outer current) (i : Fin st.depth) :
    current (st.tyAt i).val (h.varAt i) = decide (i ∈ st.currentRaw) := by
  rw [h.current_eq]
  rw [ofLevel_level_varAt]

end FrameRealizes

/-! ### Equality-induced many-to-one contractions -/

/-- A stable renaming bundled with the three complete-label invariants. -/
structure FrameContraction {O : Type} {Γ Δ : StableCtx sig}
    (envΓ : ResolvedEnv Γ O) (envΔ : ResolvedEnv Δ O)
    (outerΓ currentΓ : VarMask Γ) (outerΔ currentΔ : VarMask Δ) where
  rename : StableRename Γ Δ
  env_preserves : ResolvedEnv.Preserves rename envΓ envΔ
  outer_preserves : MaskPreserves rename outerΓ outerΔ
  current_preserves : MaskPreserves rename currentΓ currentΔ

namespace FrameContraction

variable {U : SearchUniverse sig} {O : Type} [DecidableEq O]
  {BΓ BΔ : Nat}
  {stΓ : ResolvedState U O BΓ} {stΔ : ResolvedState U O BΔ}
  {inputΓ : RealizedFrameInput stΓ} {inputΔ : RealizedFrameInput stΔ}
  {Γ Δ : StableCtx sig}
  {envΓ : ResolvedEnv Γ O} {envΔ : ResolvedEnv Δ O}
  {outerΓ currentΓ : VarMask Γ} {outerΔ currentΔ : VarMask Δ}

/-- All saturated-neutral invariants used by normalized-query contraction are
immediate instances of the existing renaming naturality API. -/
theorem sneg_naturality
    (c : FrameContraction envΓ envΔ outerΓ currentΓ outerΔ currentΔ)
    {N : Neg sig.nBases} (n : SNegNeu Γ N) :
    (n.rename c.rename).resolvedSupport envΔ = n.resolvedSupport envΓ ∧
      (n.rename c.rename).useSig outerΔ currentΔ =
        n.useSig outerΓ currentΓ ∧
      (n.rename c.rename).freshValid = n.freshValid ∧
      (n.rename c.rename).rawSupport =
        StableRename.mapRaw c.rename n.rawSupport ∧
      (n.rename c.rename).nodeSize = n.nodeSize := by
  exact ⟨SNegNeu.resolvedSupport_rename c.rename c.env_preserves n,
    SNegNeu.useSig_rename c.rename outerΓ currentΓ outerΔ currentΔ
      c.outer_preserves c.current_preserves n,
    SNegNeu.freshValid_rename c.rename n,
    SNegNeu.rawSupport_rename c.rename n,
    SNegNeu.nodeSize_rename c.rename n⟩

private theorem target_exists
    (hΓ : FrameRealizes stΓ inputΓ Γ envΓ outerΓ currentΓ)
    (hframe : stΓ.contractedFrame inputΓ = stΔ.contractedFrame inputΔ)
    {S : StableTy sig.nBases} (x : StableVar Γ S) :
    ∃ j : Fin stΔ.depth,
      stΔ.frameLabelAt inputΔ j =
        stΓ.frameLabelAt inputΓ (hΓ.toCtxRealizes.ofLevel x.level) := by
  have hmem :
      stΓ.frameLabelAt inputΓ (hΓ.toCtxRealizes.ofLevel x.level) ∈
        stΓ.contractedFrame inputΓ := by
    exact (stΓ.mem_contractedFrame_iff inputΓ _).2
      ⟨hΓ.toCtxRealizes.ofLevel x.level, rfl⟩
  rw [hframe] at hmem
  obtain ⟨j, hj⟩ := (stΔ.mem_contractedFrame_iff inputΔ _).1 hmem
  exact ⟨j, hj⟩

private noncomputable def targetLevel
    (hΓ : FrameRealizes stΓ inputΓ Γ envΓ outerΓ currentΓ)
    (hframe : stΓ.contractedFrame inputΓ = stΔ.contractedFrame inputΔ)
    {S : StableTy sig.nBases} (x : StableVar Γ S) : Fin stΔ.depth :=
  Classical.choose (target_exists hΓ hframe x)

private theorem targetLevel_label
    (hΓ : FrameRealizes stΓ inputΓ Γ envΓ outerΓ currentΓ)
    (hframe : stΓ.contractedFrame inputΓ = stΔ.contractedFrame inputΔ)
    {S : StableTy sig.nBases} (x : StableVar Γ S) :
    stΔ.frameLabelAt inputΔ (targetLevel hΓ hframe x) =
      stΓ.frameLabelAt inputΓ (hΓ.toCtxRealizes.ofLevel x.level) :=
  Classical.choose_spec (target_exists hΓ hframe x)

private theorem targetLevel_type
    (hΓ : FrameRealizes stΓ inputΓ Γ envΓ outerΓ currentΓ)
    (hframe : stΓ.contractedFrame inputΓ = stΔ.contractedFrame inputΔ)
    {S : StableTy sig.nBases} (x : StableVar Γ S) :
    (stΔ.tyAt (targetLevel hΓ hframe x)).val = S := by
  have hlabel := targetLevel_label hΓ hframe x
  have htype := congrArg (fun label : FrameLabel U O => label.1.val) hlabel
  have hsource := hΓ.frameLabelAt_of_var x
  rw [hsource] at htype
  exact htype

/-- Pick one target occurrence with the same complete label for every source
occurrence. Duplicate identical source labels may pick the same target. -/
noncomputable def renameOfFrameEq
    (hΓ : FrameRealizes stΓ inputΓ Γ envΓ outerΓ currentΓ)
    (hΔ : FrameRealizes stΔ inputΔ Δ envΔ outerΔ currentΔ)
    (hframe : stΓ.contractedFrame inputΓ = stΔ.contractedFrame inputΔ) :
    StableRename Γ Δ := fun {S} x => by
  let j := targetLevel hΓ hframe x
  have y : StableVar Δ (stΔ.tyAt j).val := hΔ.varAt j
  exact cast (congrArg (StableVar Δ) (targetLevel_type hΓ hframe x)) y

private theorem renameOfFrameEq_level
    (hΓ : FrameRealizes stΓ inputΓ Γ envΓ outerΓ currentΓ)
    (hΔ : FrameRealizes stΔ inputΔ Δ envΔ outerΔ currentΔ)
    (hframe : stΓ.contractedFrame inputΓ = stΔ.contractedFrame inputΔ)
    {S : StableTy sig.nBases} (x : StableVar Γ S) :
    (renameOfFrameEq hΓ hΔ hframe x).level =
      hΔ.toCtxRealizes.toLevel (targetLevel hΓ hframe x) := by
  unfold renameOfFrameEq
  exact (FrameRealizes.level_cast (targetLevel_type hΓ hframe x)
    (hΔ.varAt (targetLevel hΓ hframe x))).trans
      (hΔ.level_varAt (targetLevel hΓ hframe x))

private theorem renameOfFrameEq_label
    (hΓ : FrameRealizes stΓ inputΓ Γ envΓ outerΓ currentΓ)
    (hΔ : FrameRealizes stΔ inputΔ Δ envΔ outerΔ currentΔ)
    (hframe : stΓ.contractedFrame inputΓ = stΔ.contractedFrame inputΔ)
    {S : StableTy sig.nBases} (x : StableVar Γ S) :
    stΔ.frameLabelAt inputΔ
        (hΔ.toCtxRealizes.ofLevel (renameOfFrameEq hΓ hΔ hframe x).level) =
      stΓ.frameLabelAt inputΓ (hΓ.toCtxRealizes.ofLevel x.level) := by
  rw [renameOfFrameEq_level hΓ hΔ hframe x]
  have hi : hΔ.toCtxRealizes.ofLevel
      (hΔ.toCtxRealizes.toLevel (targetLevel hΓ hframe x)) =
      targetLevel hΓ hframe x := by
    apply Fin.ext
    rfl
  rw [hi]
  exact targetLevel_label hΓ hframe x

/-- Equality of realized contracted frames constructs the complete invariant
package required by saturated renaming naturality. -/
noncomputable def of_frame_eq
    (hΓ : FrameRealizes stΓ inputΓ Γ envΓ outerΓ currentΓ)
    (hΔ : FrameRealizes stΔ inputΔ Δ envΔ outerΔ currentΔ)
    (hframe : stΓ.contractedFrame inputΓ = stΔ.contractedFrame inputΔ) :
    FrameContraction envΓ envΔ outerΓ currentΓ outerΔ currentΔ where
  rename := renameOfFrameEq hΓ hΔ hframe
  env_preserves := by
    intro S x
    have hlabel := renameOfFrameEq_label hΓ hΔ hframe x
    rw [hΓ.frameLabelAt_of_var x] at hlabel
    have htarget := hΔ.frameLabelAt_of_var
      (renameOfFrameEq hΓ hΔ hframe x)
    rw [htarget] at hlabel
    exact congrArg (fun label => label.2.1) hlabel
  outer_preserves := by
    intro S x
    have hlabel := renameOfFrameEq_label hΓ hΔ hframe x
    rw [hΓ.frameLabelAt_of_var x] at hlabel
    have htarget := hΔ.frameLabelAt_of_var
      (renameOfFrameEq hΓ hΔ hframe x)
    rw [htarget] at hlabel
    exact congrArg (fun label => label.2.2.outerNew) hlabel
  current_preserves := by
    intro S x
    have hlabel := renameOfFrameEq_label hΓ hΔ hframe x
    rw [hΓ.frameLabelAt_of_var x] at hlabel
    have htarget := hΔ.frameLabelAt_of_var
      (renameOfFrameEq hΓ hΔ hframe x)
    rw [htarget] at hlabel
    exact congrArg (fun label => label.2.2.currentNew) hlabel

/-- Normal-query equality exposes the same frame-contraction package. -/
noncomputable def of_normalize_eq
    (qΓ : ResolvedQuery U O BΓ) (qΔ : ResolvedQuery U O BΔ)
    (hΓ : FrameRealizes qΓ.state qΓ.realizedFrame Γ envΓ outerΓ currentΓ)
    (hΔ : FrameRealizes qΔ.state qΔ.realizedFrame Δ envΔ outerΔ currentΔ)
    (hq : qΓ.normalize = qΔ.normalize) :
    FrameContraction envΓ envΔ outerΓ currentΓ outerΔ currentΔ :=
  of_frame_eq hΓ hΔ (congrArg NormalQuery.frame hq)

end FrameContraction

/-! ### Adversarial contraction fixtures -/

namespace FrameContractionFixtures

def sig0 : Signature := ⟨0, #[]⟩
abbrev O1 := Fin 1
def o : O1 := ⟨0, by decide⟩
def S : StableTy 0 := .neg (.shift .zero)
def U0 : SearchUniverse sig0 := ⟨∅, ∅, {S}⟩
def US : UStable U0 := ⟨S, Finset.mem_singleton_self S⟩

def st0 : ResolvedState U0 O1 2 := rootState U0 O1 2
theorem hd0 : st0.depth < 2 := by decide
def st1 : ResolvedState U0 O1 2 := st0.pushResolved hd0 US {o}
theorem hd1 : st1.depth < 2 := by decide
def st2 : ResolvedState U0 O1 2 := st1.pushResolved hd1 US {o}

def Γ1 : StableCtx sig0 := .snoc .empty US.val
def Γ2 : StableCtx sig0 := .snoc Γ1 US.val
def env0 : ResolvedEnv (.empty : StableCtx sig0) O1 := ResolvedEnv.empty O1
def env1 : ResolvedEnv Γ1 O1 := ResolvedEnv.extend env0 {o}
def env2 : ResolvedEnv Γ2 O1 := ResolvedEnv.extend env1 {o}

theorem split1 : SplitRealizes st1 (.empty : StableCtx sig0) Γ1 env1 := by
  simpa [st0, st1, Γ1, env0, env1] using
    (SplitRealizes.of_root U0 O1 2).pushResolved hd0 US {o}

theorem split2 : SplitRealizes st2 (.empty : StableCtx sig0) Γ2 env2 := by
  change SplitRealizes (st1.pushResolved hd1 US {o})
    (.empty : StableCtx sig0) (Γ1.snoc US.val)
      (ResolvedEnv.extend env1 {o})
  exact split1.pushResolved hd1 US {o}

theorem realizes1 : CtxRealizes st1 Γ1 env1 := by
  simpa [Γ1] using split1.realizes

theorem realizes2 : CtxRealizes st2 Γ2 env2 := by
  simpa [Γ2, Γ1, StableCtx.append] using split2.realizes

def input1 : RealizedFrameInput st1 := ⟨fun _ => true⟩
def input2 : RealizedFrameInput st2 := ⟨fun _ => true⟩

theorem duplicate_identical_labels_contract :
    st2.contractedFrame input2 = st1.contractedFrame input1 := by
  native_decide

theorem frame1 : FrameRealizes st1 input1 Γ1 env1
    (FrameRealizes.outerMask realizes1 input1)
    (FrameRealizes.currentMask realizes1) :=
  FrameRealizes.canonical realizes1 input1

theorem frame2 : FrameRealizes st2 input2 Γ2 env2
    (FrameRealizes.outerMask realizes2 input2)
    (FrameRealizes.currentMask realizes2) :=
  FrameRealizes.canonical realizes2 input2

noncomputable def duplicateContraction : FrameContraction env2 env1
    (FrameRealizes.outerMask realizes2 input2)
    (FrameRealizes.currentMask realizes2)
    (FrameRealizes.outerMask realizes1 input1)
    (FrameRealizes.currentMask realizes1) :=
  FrameContraction.of_frame_eq frame2 frame1 duplicate_identical_labels_contract

/-- Both identical source labels necessarily land on the sole target level. -/
theorem duplicate_sources_contract_to_one :
    duplicateContraction.rename (.here : StableVar Γ2 US.val) =
      duplicateContraction.rename (.there (.here : StableVar Γ1 US.val)) := by
  apply StableVar.eq_of_level_eq
  apply Fin.ext
  have hleft := (duplicateContraction.rename
    (.here : StableVar Γ2 US.val)).level.isLt
  have hright := (duplicateContraction.rename
    (.there (.here : StableVar Γ1 US.val))).level.isLt
  simp [Γ1, StableCtx.length] at hleft hright ⊢

def twoVarsObs : NonemptyBatchObs (sig := sig0) Γ2
    (.cons .zero (.cons .zero .empty)) :=
  .cons (.var .here) (.one (.var (.there .here)))

def newestNeg : SNegNeu (sig := sig0) Γ2 (.shift .zero) := .var .here

theorem duplicate_neutral_five_invariants :
    let c := duplicateContraction
    (newestNeg.rename c.rename).resolvedSupport env1 =
        newestNeg.resolvedSupport env2 ∧
      (newestNeg.rename c.rename).useSig
          (FrameRealizes.outerMask realizes1 input1)
          (FrameRealizes.currentMask realizes1) =
        newestNeg.useSig
          (FrameRealizes.outerMask realizes2 input2)
          (FrameRealizes.currentMask realizes2) ∧
      (newestNeg.rename c.rename).freshValid = newestNeg.freshValid ∧
      (newestNeg.rename c.rename).rawSupport =
        StableRename.mapRaw c.rename newestNeg.rawSupport ∧
      (newestNeg.rename c.rename).nodeSize = newestNeg.nodeSize := by
  exact FrameContraction.sneg_naturality duplicateContraction newestNeg

/-- The equality-induced contraction feeds all five saturated-neutral
naturality results without a second bespoke transport proof. -/
theorem duplicate_contraction_naturality :
    let c := duplicateContraction
    (twoVarsObs.rename c.rename).resolvedSupport env1 =
        twoVarsObs.resolvedSupport env2 ∧
      (twoVarsObs.rename c.rename).allFreshValid = twoVarsObs.allFreshValid ∧
      (twoVarsObs.rename c.rename).rawSupport =
        StableRename.mapRaw c.rename twoVarsObs.rawSupport ∧
      (twoVarsObs.rename c.rename).nodeSize = twoVarsObs.nodeSize := by
  dsimp only
  exact ⟨NonemptyBatchObs.resolvedSupport_rename _
      duplicateContraction.env_preserves _,
    NonemptyBatchObs.allFreshValid_rename _ _,
    NonemptyBatchObs.rawSupport_rename _ _,
    NonemptyBatchObs.nodeSize_rename _ _⟩

/-- If the two otherwise identical source occurrences have different outer
provenance, their complete labels no longer contract to the one-entry frame. -/
def splitOuterInput2 : RealizedFrameInput st2 :=
  ⟨fun i => decide (i.val = 1)⟩

theorem distinguishing_outer_mask_rejected :
    st2.contractedFrame splitOuterInput2 ≠ st1.contractedFrame input1 := by
  native_decide

/-- Current-round provenance is equally non-collapsible. -/
def splitCurrentState2 : ResolvedState U0 O1 2 where
  depth := st2.depth
  depth_le := st2.depth_le
  tyAt := st2.tyAt
  depAt := st2.depAt
  roundStart := 1
  round_le := by decide

def splitCurrentInput2 : RealizedFrameInput splitCurrentState2 :=
  ⟨fun _ => true⟩

theorem distinguishing_current_mask_rejected :
    splitCurrentState2.contractedFrame splitCurrentInput2 ≠
      st1.contractedFrame input1 := by
  native_decide

end FrameContractionFixtures

end Gimbal.Equality.Scherer
