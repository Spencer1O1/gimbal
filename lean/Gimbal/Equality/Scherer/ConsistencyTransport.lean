/-
  Contraction transport for generative Scherer consistency derivations.

  Equality of normalized queries deliberately forgets duplicate multiplicity,
  so it does not imply spare target capacity.  The transport package therefore
  carries the exact additional invariant needed by store steps: source
  headroom is bounded by target headroom.  This is local infrastructure, not a
  proof that any global search bound supplies the invariant.
-/

import Gimbal.Equality.Scherer.ConsistencyDeriv

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Exact scope transport -/

/-- A proof-only contraction between flattened realized scopes.  The forward
renaming is an index so saturated `Old/New` renaming remains definitionally
aligned through recursive constructors. -/
structure ScopeTransport {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {BΓ BΔ : Nat} {Γ Δ : StableCtx sig}
    (ρ : StableRename Γ Δ)
    (desc : ConsistencyScope U O BΓ Γ)
    (ancestor : ConsistencyScope U O BΔ Δ) : Type where
  env_preserves : ResolvedEnv.Preserves ρ desc.env ancestor.env
  outer_preserves : MaskPreserves ρ desc.outer ancestor.outer
  current_preserves : MaskPreserves ρ desc.current ancestor.current
  backward : FrameContraction ancestor.env desc.env
    ancestor.outer ancestor.current desc.outer desc.current
  coverage_eq : desc.coverage = ancestor.coverage
  headroom : BΓ - desc.state.depth ≤ BΔ - ancestor.state.depth

namespace ScopeTransport

variable {U : SearchUniverse sig} {O : Type} [DecidableEq O]
  {BΓ BΔ : Nat} {Γ Δ : StableCtx sig}
  {desc : ConsistencyScope U O BΓ Γ}
  {ancestor : ConsistencyScope U O BΔ Δ}
  {ρ : StableRename Γ Δ}

/-- Forward `FrameContraction` exposed from the indexed fields. -/
def forward (tr : ScopeTransport ρ desc ancestor) :
    FrameContraction desc.env ancestor.env desc.outer desc.current
      ancestor.outer ancestor.current where
  rename := ρ
  env_preserves := tr.env_preserves
  outer_preserves := tr.outer_preserves
  current_preserves := tr.current_preserves

/-- Build the transport package from normalized-query equality plus the
separate, honest headroom premise. -/
noncomputable def of_normalize_eq
    (target : Obligation U O) (useSig : UseSig)
    (hquery : (desc.query target useSig).normalize =
      (ancestor.query target useSig).normalize)
    (hhead : BΓ - desc.state.depth ≤ BΔ - ancestor.state.depth) :
    let c := (desc.query target useSig).contractionTo
      (ancestor.query target useSig) hquery
    ScopeTransport c.rename desc ancestor := by
  let c := (desc.query target useSig).contractionTo
    (ancestor.query target useSig) hquery
  let back := (ancestor.query target useSig).contractionTo
    (desc.query target useSig) hquery.symm
  exact {
    env_preserves := c.env_preserves
    outer_preserves := c.outer_preserves
    current_preserves := c.current_preserves
    backward := back
    coverage_eq := congrArg NormalQuery.coverage hquery
    headroom := hhead
  }

/-! ### Exact-support strong transport -/

private def renameStrongPos {Γ Δ : StableCtx sig} (ρ : StableRename Γ Δ) :
    {P : Pos sig.nBases} → StrongPos Γ P → StrongPos Δ P
  | _, .negVar x => .negVar (ρ x)
  | _, .atomVar x => .atomVar (ρ x)
  | _, .inl p => .inl (renameStrongPos ρ p)
  | _, .inr p => .inr (renameStrongPos ρ p)

omit [DecidableEq O] in
private theorem renameStrongPos_support
    {Γ Δ : StableCtx sig} {envΓ : ResolvedEnv Γ O}
    {envΔ : ResolvedEnv Δ O} (ρ : StableRename Γ Δ)
    (hEnv : ResolvedEnv.Preserves ρ envΓ envΔ) :
    ∀ {P : Pos sig.nBases} (p : StrongPos Γ P),
      StrongPos.depSupport envΔ (renameStrongPos ρ p) =
        StrongPos.depSupport envΓ p
  | _, .negVar x => hEnv _ x
  | _, .atomVar x => hEnv _ x
  | _, .inl p => renameStrongPos_support ρ hEnv p
  | _, .inr p => renameStrongPos_support ρ hEnv p

omit [DecidableEq O] in
private theorem strongAt_of_contraction
    {B₁ B₂ : Nat} {Γ₁ Γ₂ : StableCtx sig}
    (s₁ : ConsistencyScope U O B₁ Γ₁)
    (s₂ : ConsistencyScope U O B₂ Γ₂)
    (c : FrameContraction s₁.env s₂.env s₁.outer s₁.current
      s₂.outer s₂.current)
    {P : Pos sig.nBases} {K : DepSupport O} :
    StrongAt s₁.state P K → StrongAt s₂.state P K := by
  intro h
  obtain ⟨⟨p, hp⟩⟩ := StrongAt.reify s₁.realizes.toCtxRealizes h
  apply StrongAt.reflect s₂.realizes.toCtxRealizes
  exact ⟨⟨renameStrongPos c.rename p, by
    rw [renameStrongPos_support c.rename c.env_preserves, hp]⟩⟩

theorem strongAt_forward (tr : ScopeTransport ρ desc ancestor)
    {P : Pos sig.nBases} {K : DepSupport O} :
    StrongAt desc.state P K → StrongAt ancestor.state P K :=
  strongAt_of_contraction desc ancestor tr.forward

theorem strongAt_backward (tr : ScopeTransport ρ desc ancestor)
    {P : Pos sig.nBases} {K : DepSupport O} :
    StrongAt ancestor.state P K → StrongAt desc.state P K :=
  strongAt_of_contraction ancestor desc tr.backward

theorem strongAt_iff (tr : ScopeTransport ρ desc ancestor)
    (P : Pos sig.nBases) (K : DepSupport O) :
    StrongAt desc.state P K ↔ StrongAt ancestor.state P K :=
  ⟨tr.strongAt_forward, tr.strongAt_backward⟩

/-! ### Scope transitions -/

/-- Headroom dominance turns every source store capacity proof into the target
capacity proof needed by the transported store. -/
theorem target_capacity (tr : ScopeTransport ρ desc ancestor)
    (hd : desc.state.depth < BΓ) : ancestor.state.depth < BΔ := by
  have hs : 0 < BΓ - desc.state.depth := Nat.sub_pos_iff_lt.mpr hd
  have ht : 0 < BΔ - ancestor.state.depth := lt_of_lt_of_le hs tr.headroom
  exact Nat.sub_pos_iff_lt.mp ht

/-- Round reset keeps the forward renaming, reverse contraction, coverage, and
headroom. -/
def resetRound (tr : ScopeTransport ρ desc ancestor) :
    ScopeTransport ρ desc.resetRound ancestor.resetRound where
  env_preserves := tr.env_preserves
  outer_preserves := by
    intro S x
    rw [ancestor.resetRound_outer, desc.resetRound_outer]
    exact tr.outer_preserves S x
  current_preserves := by
    intro S x
    rw [ancestor.resetRound_current_false, desc.resetRound_current_false]
  backward := {
    rename := tr.backward.rename
    env_preserves := tr.backward.env_preserves
    outer_preserves := by
      intro S x
      rw [desc.resetRound_outer, ancestor.resetRound_outer]
      exact tr.backward.outer_preserves S x
    current_preserves := by
      intro S x
      rw [desc.resetRound_current_false, ancestor.resetRound_current_false]
  }
  coverage_eq := tr.coverage_eq
  headroom := by simpa using tr.headroom

/-- Replace both coverages by the corresponding union with the same exact
obligation list. -/
def unionCoverage (tr : ScopeTransport ρ desc ancestor)
    (xs : List (Obligation U O)) :
    ScopeTransport ρ
      (desc.withCoverage (desc.coverage ∪ xs.toFinset))
      (ancestor.withCoverage (ancestor.coverage ∪ xs.toFinset)) where
  env_preserves := tr.env_preserves
  outer_preserves := tr.outer_preserves
  current_preserves := tr.current_preserves
  backward := tr.backward
  coverage_eq := by
    simpa only [ConsistencyScope.withCoverage_coverage] using
      congrArg (fun coverage => coverage ∪ xs.toFinset) tr.coverage_eq
  headroom := tr.headroom

/-- Paired resolved pushes preserve all transport data.  The target capacity
proof is explicit because it is not a consequence of normalization. -/
def pushResolved (tr : ScopeTransport ρ desc ancestor)
    (hdΓ : desc.state.depth < BΓ) (S : UStable U) (K : DepSupport O) :
    let hdΔ := tr.target_capacity hdΓ
    ScopeTransport (StableRename.ext ρ)
      (desc.pushResolved hdΓ S K) (ancestor.pushResolved hdΔ S K) := by
  let hdΔ := tr.target_capacity hdΓ
  exact {
    env_preserves := ResolvedEnv.Preserves.ext tr.env_preserves K
    outer_preserves := by
      intro T x
      cases x with
      | here =>
          change (ancestor.pushResolved hdΔ S K).outer S.val .here =
            (desc.pushResolved hdΓ S K).outer S.val .here
          rw [ancestor.pushResolved_outer_here, desc.pushResolved_outer_here]
      | there x =>
          change (ancestor.pushResolved hdΔ S K).outer T (.there (ρ x)) =
            (desc.pushResolved hdΓ S K).outer T (.there x)
          rw [ancestor.pushResolved_outer_there, desc.pushResolved_outer_there]
          exact tr.outer_preserves _ x
    current_preserves := by
      intro T x
      cases x with
      | here =>
          change (ancestor.pushResolved hdΔ S K).current S.val .here =
            (desc.pushResolved hdΓ S K).current S.val .here
          rw [ancestor.pushResolved_current_here,
            desc.pushResolved_current_here]
      | there x =>
          change (ancestor.pushResolved hdΔ S K).current T (.there (ρ x)) =
            (desc.pushResolved hdΓ S K).current T (.there x)
          rw [ancestor.pushResolved_current_there,
            desc.pushResolved_current_there]
          exact tr.current_preserves _ x
    backward := {
      rename := StableRename.ext tr.backward.rename
      env_preserves := ResolvedEnv.Preserves.ext tr.backward.env_preserves K
      outer_preserves := by
        intro T x
        cases x with
        | here =>
            change (desc.pushResolved hdΓ S K).outer S.val .here =
              (ancestor.pushResolved hdΔ S K).outer S.val .here
            rw [desc.pushResolved_outer_here, ancestor.pushResolved_outer_here]
        | there x =>
            change (desc.pushResolved hdΓ S K).outer T
                (.there (tr.backward.rename x)) =
              (ancestor.pushResolved hdΔ S K).outer T (.there x)
            rw [desc.pushResolved_outer_there,
              ancestor.pushResolved_outer_there]
            exact tr.backward.outer_preserves _ x
      current_preserves := by
        intro T x
        cases x with
        | here =>
            change (desc.pushResolved hdΓ S K).current S.val .here =
              (ancestor.pushResolved hdΔ S K).current S.val .here
            rw [desc.pushResolved_current_here,
              ancestor.pushResolved_current_here]
        | there x =>
            change (desc.pushResolved hdΓ S K).current T
                (.there (tr.backward.rename x)) =
              (ancestor.pushResolved hdΔ S K).current T (.there x)
            rw [desc.pushResolved_current_there,
              ancestor.pushResolved_current_there]
            exact tr.backward.current_preserves _ x
    }
    coverage_eq := tr.coverage_eq
    headroom := by
      simp only [ConsistencyScope.pushResolved_state,
        ResolvedState.pushResolved, ResolvedState.push_depth]
      simpa [Nat.sub_sub] using Nat.sub_le_sub_right tr.headroom 1
  }

end ScopeTransport

/-! ### Request preservation -/

namespace FreshRequest

variable {U : SearchUniverse sig} {O : Type} [DecidableEq O]
  {BΓ BΔ : Nat} {Γ Δ : StableCtx sig}
  {desc : ConsistencyScope U O BΓ Γ}
  {ancestor : ConsistencyScope U O BΔ Δ}
  {ρ : StableRename Γ Δ} {target : Obligation U O} {useSig : UseSig}

theorem contract (tr : ScopeTransport ρ desc ancestor)
    (request : FreshRequest desc target useSig) :
    FreshRequest ancestor target useSig where
  nonzero := request.nonzero
  uncovered := by simpa [← tr.coverage_eq] using request.uncovered
  currentUse := request.currentUse
  notStrong := fun h => request.notStrong (tr.strongAt_backward h)

end FreshRequest

namespace ZeroRequest

variable {U : SearchUniverse sig} {O : Type} [DecidableEq O]
  {BΓ BΔ : Nat} {Γ Δ : StableCtx sig}
  {desc : ConsistencyScope U O BΓ Γ}
  {ancestor : ConsistencyScope U O BΔ Δ}
  {ρ : StableRename Γ Δ} {K : DepSupport O} {useSig : UseSig}

theorem contract (_tr : ScopeTransport ρ desc ancestor)
    (request : ZeroRequest desc K useSig) : ZeroRequest ancestor K useSig where
  zero_mem := request.zero_mem

end ZeroRequest

/-! ### Mutual transport of generated syntax -/

mutual

noncomputable def CNeg.contract
    {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {BΓ BΔ : Nat} {Γ Δ : StableCtx sig}
    {desc : ConsistencyScope U O BΓ Γ}
    {ancestor : ConsistencyScope U O BΔ Δ}
    {ρ : StableRename Γ Δ} {N : Neg sig.nBases} {n : SNegNeu Γ N}
    (tr : ScopeTransport ρ desc ancestor) :
    CNeg desc n → CNeg ancestor (n.rename ρ)
  | .var x => .var (ρ x)
  | .fst d => .fst (CNeg.contract tr d)
  | .snd d => .snd (CNeg.contract tr d)
  | .app dn dp => .app (CNeg.contract tr dn) (CPos.contract tr dp)

noncomputable def CPos.contract
    {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {BΓ BΔ : Nat} {Γ Δ : StableCtx sig}
    {desc : ConsistencyScope U O BΓ Γ}
    {ancestor : ConsistencyScope U O BΔ Δ}
    {ρ : StableRename Γ Δ} {P : Pos sig.nBases} {p : SPosNeu Γ P}
    (tr : ScopeTransport ρ desc ancestor) :
    CPos desc p → CPos ancestor (p.rename ρ)
  | .atom x => .atom (ρ x)
  | @CPos.inl _ _ _ _ _ _ _ _ _ B _ d =>
      @CPos.inl sig U O _ BΔ _ Δ ancestor _ B _
        (CPos.contract tr d)
  | @CPos.inr _ _ _ _ _ _ _ _ A _ _ d =>
      @CPos.inr sig U O _ BΔ _ Δ ancestor A _ _
        (CPos.contract tr d)
  | .shift d => by
      let tr' : ScopeTransport (StableRename.keepLeft ρ .empty)
          desc.resetRound ancestor.resetRound := by
        simpa [StableRename.keepLeft] using tr.resetRound
      exact .shift (CInv.contract ρ tr'
        (SplitConsistencyScope.resetRound ancestor) d)

noncomputable def CInv.contract
    {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {BΓ BΔ : Nat} {Old Old' New : StableCtx sig}
    {desc : ConsistencyScope U O BΓ (Old.append New)}
    {ancestor : ConsistencyScope U O BΔ (Old'.append New)}
    (ρ : StableRename Old Old')
    (tr : ScopeTransport (StableRename.keepLeft ρ New) desc ancestor)
    (split : SplitConsistencyScope Old' New ancestor)
    {pending : ResolvedPending U O} {G : Goal sig.nBases}
    {t : SInv Old New pending.erase G} :
    CInv desc pending t → CInv ancestor pending (t.rename ρ)
  | .caseSum dl dr =>
      .caseSum (CInv.contract ρ tr split dl)
        (CInv.contract ρ tr split dr)
  | @CInv.abort _ _ _ _ _ _ _ _ _ hZero K rest G =>
      @CInv.abort sig U O _ BΔ _ Old' New ancestor hZero K rest G
  | .storeAtom (q := q) (hStable := hStable) (K := K) hd d => by
      let hd' := tr.target_capacity hd
      let tr' : ScopeTransport
          (StableRename.keepLeft ρ (New.snoc (.atom q)))
          (desc.pushResolved hd ⟨.atom q, hStable⟩ K)
          (ancestor.pushResolved hd' ⟨.atom q, hStable⟩ K) := by
        simpa [StableRename.keepLeft] using
          (tr.pushResolved hd ⟨.atom q, hStable⟩ K)
      refine .storeAtom (hStable := hStable) hd' ?_
      exact CInv.contract ρ tr'
        (split.pushResolved hd' ⟨.atom q, hStable⟩ K) d
  | .storeShift (N := N) (hStable := hStable) (K := K) hd d => by
      let hd' := tr.target_capacity hd
      let tr' : ScopeTransport
          (StableRename.keepLeft ρ (New.snoc (.neg N)))
          (desc.pushResolved hd ⟨.neg N, hStable⟩ K)
          (ancestor.pushResolved hd' ⟨.neg N, hStable⟩ K) := by
        simpa [StableRename.keepLeft] using
          (tr.pushResolved hd ⟨.neg N, hStable⟩ K)
      refine .storeShift (hStable := hStable) hd' ?_
      exact CInv.contract ρ tr'
        (split.pushResolved hd' ⟨.neg N, hStable⟩ K) d
  | .unit => .unit
  | .pair dl dr => .pair (CInv.contract ρ tr split dl)
      (CInv.contract ρ tr split dr)
  | .lam d => .lam (CInv.contract ρ tr split d)
  | .satShift d => .satShift (CSat.contract ρ tr split d)
  | .satPos d => .satPos (CSat.contract ρ tr split d)

noncomputable def CSat.contract
    {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {BΓ BΔ : Nat} {Old Old' New : StableCtx sig}
    {desc : ConsistencyScope U O BΓ (Old.append New)}
    {ancestor : ConsistencyScope U O BΔ (Old'.append New)}
    (ρ : StableRename Old Old')
    (tr : ScopeTransport (StableRename.keepLeft ρ New) desc ancestor)
    (split : SplitConsistencyScope Old' New ancestor)
    {P : Pos sig.nBases} {sat : Sat Old New P} :
    CSat desc sat → CSat ancestor (sat.rename ρ)
  | .inconsistent request query =>
      .inconsistent (request.contract tr) (CQuery.contract tr query)
  | .done d => .done (CPos.contract tr d)
  | @CSat.batch _ _ _ _ _ _ _ _ _ xs _ _ db di => by
      let tr' := tr.resetRound.unionCoverage xs
      let tr'' : ScopeTransport
          (StableRename.keepLeft (StableRename.keepLeft ρ New) .empty)
          (desc.resetRound.withCoverage (desc.coverage ∪ xs.toFinset))
          (ancestor.resetRound.withCoverage
            (ancestor.coverage ∪ xs.toFinset)) := by
        simpa [StableRename.keepLeft] using tr'
      let bodySplit : SplitConsistencyScope (Old'.append New) .empty
          (ancestor.resetRound.withCoverage
            (ancestor.coverage ∪ xs.toFinset)) :=
        (SplitConsistencyScope.resetRound ancestor).withCoverage _
      exact .batch (CBatch.contract ρ tr split db)
        (CInv.contract (StableRename.keepLeft ρ New) tr'' bodySplit di)

noncomputable def CBatch.contract
    {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {BΓ BΔ : Nat} {Old Old' New : StableCtx sig}
    {desc : ConsistencyScope U O BΓ (Old.append New)}
    {ancestor : ConsistencyScope U O BΔ (Old'.append New)}
    (ρ : StableRename Old Old')
    (tr : ScopeTransport (StableRename.keepLeft ρ New) desc ancestor)
    (split : SplitConsistencyScope Old' New ancestor)
    {xs : List (Obligation U O)}
    {obs : NonemptyBatchObs (Old.append New) (obligationPending xs).erase} :
    CBatch desc xs obs →
      CBatch ancestor xs (obs.rename (StableRename.keepLeft ρ New))
  | .one query request _ =>
      .one (CQuery.contract tr query) (request.contract tr) split
  | .cons query request _ hNotMem rest =>
      .cons (CQuery.contract tr query) (request.contract tr) split
        hNotMem (CBatch.contract ρ tr split rest)

noncomputable def CQuery.contract
    {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {BΓ BΔ : Nat} {Γ Δ : StableCtx sig}
    {desc : ConsistencyScope U O BΓ Γ}
    {ancestor : ConsistencyScope U O BΔ Δ}
    {ρ : StableRename Γ Δ} {target : Obligation U O} {useSig : UseSig}
    {n : SNegNeu Γ (.shift target.result.val)}
    (tr : ScopeTransport ρ desc ancestor) :
    CQuery desc target useSig n → CQuery ancestor target useSig (n.rename ρ)
  | .intro d hSupport hUse =>
      .intro (CNeg.contract tr d)
        ((SNegNeu.resolvedSupport_rename ρ tr.env_preserves _).trans hSupport)
        ((SNegNeu.useSig_rename ρ desc.outer desc.current
          ancestor.outer ancestor.current tr.outer_preserves
          tr.current_preserves _).trans hUse)

end

/-! ### Split-aware query freshness transport -/

/-- Once the target scope is tied to its syntax split, ordinary normalized
scope transport preserves precisely the `usesNew` fact needed to rebuild a
batch entry.  No Old/New data is added to `NormalQuery`. -/
theorem CQuery.contract_usesNew
    {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {BΓ BΔ : Nat} {Γ Old New : StableCtx sig}
    {desc : ConsistencyScope U O BΓ Γ}
    {ancestor : ConsistencyScope U O BΔ (Old.append New)}
    {ρ : StableRename Γ (Old.append New)}
    {target : Obligation U O} {u : UseSig}
    {n : SNegNeu Γ (.shift target.result.val)}
    (tr : ScopeTransport ρ desc ancestor)
    (query : CQuery desc target u n)
    (request : FreshRequest desc target u)
    (split : SplitConsistencyScope Old New ancestor) :
    (n.rename ρ).uses (newMask Old New) = true :=
  (CQuery.contract tr query).usesNew (request.contract tr) split

/-! ### Packaged derivation transport -/

namespace ConsistencyDeriv

variable {U : SearchUniverse sig} {O : Type} [DecidableEq O]
  {BΓ BΔ : Nat} {Γ Δ : StableCtx sig}
  {desc : ConsistencyScope U O BΓ Γ}
  {ancestor : ConsistencyScope U O BΔ Δ}
  {ρ : StableRename Γ Δ} {target target' : Obligation U O}
  {useSig useSig' : UseSig}

/-- Package the mutually transported query derivation. -/
noncomputable def contract (tr : ScopeTransport ρ desc ancestor)
    (d : ConsistencyDeriv desc target useSig) :
    ConsistencyDeriv ancestor target useSig where
  neutral := d.neutral.rename ρ
  query := CQuery.contract tr d.query

/-- A full generated derivation contracts along an equal normalized query once
the separately required target headroom dominance is supplied. -/
noncomputable def contract_of_normalize_eq
    (hquery : (desc.query target useSig).normalize =
      (ancestor.query target' useSig').normalize)
    (hhead : BΓ - desc.state.depth ≤ BΔ - ancestor.state.depth)
    (d : ConsistencyDeriv desc target useSig) :
    ConsistencyDeriv ancestor target' useSig' := by
  have ht : target = target' := congrArg NormalQuery.target hquery
  have hu : useSig = useSig' := congrArg NormalQuery.useSig hquery
  subst target'
  subst useSig'
  let c := (desc.query target useSig).contractionTo
    (ancestor.query target useSig) hquery
  let tr : ScopeTransport c.rename desc ancestor :=
    ScopeTransport.of_normalize_eq target useSig hquery hhead
  exact d.contract tr

/-- Full derivation contraction preserves the custom syntax-node size used by
the later minimality argument. -/
theorem contract_of_normalize_eq_nodeSize
    (hquery : (desc.query target useSig).normalize =
      (ancestor.query target' useSig').normalize)
    (hhead : BΓ - desc.state.depth ≤ BΔ - ancestor.state.depth)
    (d : ConsistencyDeriv desc target useSig) :
    (contract_of_normalize_eq hquery hhead d).neutral.nodeSize =
      d.neutral.nodeSize := by
  have ht : target = target' := congrArg NormalQuery.target hquery
  have hu : useSig = useSig' := congrArg NormalQuery.useSig hquery
  subst target'
  subst useSig'
  simp only [contract_of_normalize_eq, contract]
  exact SNegNeu.nodeSize_rename
    ((desc.query target useSig).contractionTo
      (ancestor.query target useSig) hquery).rename d.neutral

/-- The normalized contraction is immediately admissible at a split-aware
target batch boundary; no extra proof about the replacement neutral is needed. -/
theorem contract_of_normalize_eq_usesNew
    {Old New : StableCtx sig}
    {ancestor : ConsistencyScope U O BΔ (Old.append New)}
    (hquery : (desc.query target useSig).normalize =
      (ancestor.query target' useSig').normalize)
    (hhead : BΓ - desc.state.depth ≤ BΔ - ancestor.state.depth)
    (d : ConsistencyDeriv desc target useSig)
    (request : FreshRequest ancestor target' useSig')
    (split : SplitConsistencyScope Old New ancestor) :
    (contract_of_normalize_eq hquery hhead d).neutral.uses
      (newMask Old New) = true :=
  (contract_of_normalize_eq hquery hhead d).query.usesNew request split

private theorem witness_eq_of_neutral_eq
    {B : Nat} {Θ : StableCtx sig} {s : ConsistencyScope U O B Θ}
    {t : Obligation U O} {u : UseSig}
    (a b : ConsistencyWitness (s.query t u))
    (h : a.neutral = b.neutral) : a = b := by
  cases a with
  | mk an ar au af =>
      cases b with
      | mk bn br bu bf =>
          cases h
          rfl

/-- Forgetting the transported generative derivation agrees exactly with the
previous witness-level contraction (proof fields are propositionally
irrelevant). -/
theorem toWitness_contract_of_normalize_eq
    (hquery : (desc.query target useSig).normalize =
      (ancestor.query target' useSig').normalize)
    (hhead : BΓ - desc.state.depth ≤ BΔ - ancestor.state.depth)
    (d : ConsistencyDeriv desc target useSig) :
    (contract_of_normalize_eq hquery hhead d).toWitness =
      ConsistencyWitness.contract_of_normalize_eq
        (desc.query target useSig) (ancestor.query target' useSig')
        hquery d.toWitness := by
  have ht : target = target' := congrArg NormalQuery.target hquery
  have hu : useSig = useSig' := congrArg NormalQuery.useSig hquery
  subst target'
  subst useSig'
  change (desc.query target useSig).query.normalize =
    (ancestor.query target useSig).query.normalize at hquery
  apply witness_eq_of_neutral_eq
  simp only [contract_of_normalize_eq, contract,
    ConsistencyWitness.contract_of_normalize_eq]
  generalize_proofs hcast
  cases hcast
  rfl

end ConsistencyDeriv

/-! ### Headroom boundary fixtures -/

namespace ScopeTransportFixtures

open FrameContractionFixtures

/-- The counterexample universe contains an actual query target in addition to
the duplicated stable label from the frame-contraction fixture. -/
def Uc : SearchUniverse sig0 := ⟨{.zero}, ∅, {S}⟩
def USc : UStable Uc := ⟨S, Finset.mem_singleton_self S⟩
def target : Obligation Uc O1 := ⟨⟨.zero, by simp [Uc]⟩, ∅⟩
def useSig : UseSig := ⟨true, true⟩

def cst0 : ResolvedState Uc O1 2 := rootState Uc O1 2
theorem chd0 : cst0.depth < 2 := by decide
def cst1 : ResolvedState Uc O1 2 := cst0.pushResolved chd0 USc {o}
theorem chd1 : cst1.depth < 2 := by decide
def cst2 : ResolvedState Uc O1 2 := cst1.pushResolved chd1 USc {o}

def CΓ1 : StableCtx sig0 := .snoc .empty S
def CΓ2 : StableCtx sig0 := .snoc CΓ1 S
def cenv0 : ResolvedEnv (.empty : StableCtx sig0) O1 := ResolvedEnv.empty O1
def cenv1 : ResolvedEnv CΓ1 O1 := ResolvedEnv.extend cenv0 {o}
def cenv2 : ResolvedEnv CΓ2 O1 := ResolvedEnv.extend cenv1 {o}

theorem csplit1 : SplitRealizes cst1 (.empty : StableCtx sig0) CΓ1 cenv1 := by
  simpa [cst0, cst1, CΓ1, cenv0, cenv1, USc] using
    (SplitRealizes.of_root Uc O1 2).pushResolved chd0 USc {o}

theorem csplit2 : SplitRealizes cst2 (.empty : StableCtx sig0) CΓ2 cenv2 := by
  change SplitRealizes (cst1.pushResolved chd1 USc {o})
    (.empty : StableCtx sig0) (CΓ1.snoc USc.val)
      (ResolvedEnv.extend cenv1 {o})
  exact csplit1.pushResolved chd1 USc {o}

theorem crealizes1 : CtxRealizes cst1 CΓ1 cenv1 := by
  simpa [CΓ1] using csplit1.realizes

theorem crealizes2 : CtxRealizes cst2 CΓ2 cenv2 := by
  simpa [CΓ2, CΓ1, StableCtx.append] using csplit2.realizes

def cinput1 : RealizedFrameInput cst1 := ⟨fun _ => true⟩
def cinput2 : RealizedFrameInput cst2 := ⟨fun _ => true⟩

def shallow : ConsistencyScope Uc O1 2 CΓ1 where
  state := cst1
  env := cenv1
  frameInput := cinput1
  outer := FrameRealizes.outerMask crealizes1 cinput1
  current := FrameRealizes.currentMask crealizes1
  realizes := FrameRealizes.canonical crealizes1 cinput1
  coverage := ∅

def full : ConsistencyScope Uc O1 2 CΓ2 where
  state := cst2
  env := cenv2
  frameInput := cinput2
  outer := FrameRealizes.outerMask crealizes2 cinput2
  current := FrameRealizes.currentMask crealizes2
  realizes := FrameRealizes.canonical crealizes2 cinput2
  coverage := ∅

/-- Equal normalization alone is genuinely insufficient: the shallower source
has one free store slot while the equal-frame target has none. -/
theorem equal_normalized_query_without_headroom :
    (shallow.query target useSig).normalize =
        (full.query target useSig).normalize ∧
      ¬ (2 - shallow.state.depth ≤ 2 - full.state.depth) := by
  native_decide

/-! The same duplicated frame at bound three has exactly the target headroom
needed to transport from the bound-two shallow scope. -/

def cst30 : ResolvedState Uc O1 3 := rootState Uc O1 3
theorem chd30 : cst30.depth < 3 := by decide
def cst31 : ResolvedState Uc O1 3 := cst30.pushResolved chd30 USc {o}
theorem chd31 : cst31.depth < 3 := by decide
def cst32 : ResolvedState Uc O1 3 := cst31.pushResolved chd31 USc {o}

theorem csplit32 : SplitRealizes cst32 (.empty : StableCtx sig0) CΓ2 cenv2 := by
  have h1 := (SplitRealizes.of_root Uc O1 3).pushResolved chd30 USc {o}
  have h2 := h1.pushResolved chd31 USc {o}
  simpa [cst30, cst31, cst32, CΓ1, CΓ2, cenv0, cenv1, cenv2, USc,
    StableCtx.append] using h2

theorem crealizes32 : CtxRealizes cst32 CΓ2 cenv2 := by
  simpa [CΓ2, CΓ1, StableCtx.append] using csplit32.realizes

def cinput32 : RealizedFrameInput cst32 := ⟨fun _ => true⟩

def roomy : ConsistencyScope Uc O1 3 CΓ2 where
  state := cst32
  env := cenv2
  frameInput := cinput32
  outer := FrameRealizes.outerMask crealizes32 cinput32
  current := FrameRealizes.currentMask crealizes32
  realizes := FrameRealizes.canonical crealizes32 cinput32
  coverage := ∅

theorem shallow_roomy_normalize_eq :
    (shallow.query target useSig).normalize =
      (roomy.query target useSig).normalize := by
  native_decide

theorem shallow_roomy_headroom :
    2 - shallow.state.depth ≤ 3 - roomy.state.depth := by decide

/-- Positive same-lineage fixture: duplicate contraction plus the honest
headroom premise constructs the exact transport package. -/
noncomputable def shallowToRoomy :
    let c := (shallow.query target useSig).contractionTo
      (roomy.query target useSig) shallow_roomy_normalize_eq
    ScopeTransport c.rename shallow roomy :=
  ScopeTransport.of_normalize_eq target useSig shallow_roomy_normalize_eq
    shallow_roomy_headroom

/-- The positive fixture really transports the source's available store slot. -/
theorem shallow_capacity_transports : roomy.state.depth < 3 :=
  shallowToRoomy.target_capacity chd1

end ScopeTransportFixtures

namespace SplitConsistencyScopeFixtures

open FrameContractionFixtures ScopeTransportFixtures

def LastOnly : StableCtx sig0 := .snoc .empty S

/-- Two identical realized labels can inhabit the same flattened context while
different Old/New cuts disagree about whether the older occurrence is new.
The flat scope and its normalized query cannot distinguish these cuts. -/
theorem duplicate_labels_split_differ :
    newMask (.empty : StableCtx sig0) CΓ2 S
        (.there .here : StableVar CΓ2 S) = true ∧
      newMask CΓ1 LastOnly S
        (.there .here : StableVar (CΓ1.append LastOnly) S) = false ∧
      full.current S (.there .here : StableVar CΓ2 S) = true := by
  native_decide

/-- Consequently the same flat scope is not split-realized by the cut that
places only the newest duplicate in `New`. -/
theorem full_not_lastOnly_split :
    ¬ SplitConsistencyScope CΓ1 LastOnly full := by
  intro split
  have h := split.current_eq
    (.there .here : StableVar (CΓ1.append LastOnly) S)
  change true = false at h
  exact Bool.noConfusion h

theorem shallow_allNew_split :
    SplitConsistencyScope (.empty : StableCtx sig0) CΓ1 shallow := by
  constructor
  intro T x
  cases x with
  | here => native_decide
  | there x => nomatch x

theorem roomy_allNew_split :
    SplitConsistencyScope (.empty : StableCtx sig0) CΓ2 roomy := by
  constructor
  intro T x
  cases x with
  | here => native_decide
  | there x =>
      cases x with
      | here => native_decide
      | there x => nomatch x

def sourceNeutral : SNegNeu CΓ1 (.shift (.zero : Pos 0)) := .var .here

theorem sourceNeutral_uses_current :
    sourceNeutral.uses shallow.current = true := by
  native_decide

/-- Positive split-aware fixture: the normalized-query contraction from the
one-label scope to the roomy duplicate-label scope lands in syntax `New`,
because the target's all-New split identifies `current` with `newMask`. -/
theorem positive_split_aware_transport :
    let tr := shallowToRoomy
    (sourceNeutral.rename tr.forward.rename).uses
      (newMask (.empty : StableCtx sig0) CΓ2) = true := by
  intro tr
  rw [← roomy_allNew_split.current_mask_eq]
  exact (SNegNeu.uses_rename tr.forward.rename shallow.current roomy.current
    tr.current_preserves sourceNeutral).trans sourceNeutral_uses_current

end SplitConsistencyScopeFixtures

end Gimbal.Equality.Scherer
