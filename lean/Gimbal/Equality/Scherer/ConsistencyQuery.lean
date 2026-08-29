/-
  Intrinsic consistency-query witnesses for the Scherer-core search.

  This module connects the finite `ResolvedQuery.normalize` boundary to an
  actual saturated negative neutral in a realized intrinsic context. Equal
  normalized queries induce the existing many-to-one `FrameContraction`, so a
  descendant witness can be renamed into the ancestor context without changing
  its resolved support, two-bit usage signature, freshness, or constructor
  size.

  This is a relational boundary only. It does not choose a witness, allocate
  work tokens, enumerate source sites, splice arbitrary saturated derivations,
  prove a capacity bound, or impose the future local-inconsistency policy.
-/

import Gimbal.Equality.Scherer.FrameContraction

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Intrinsic realized queries -/

/--
A resolved query together with one intrinsic realization of its exact state,
environment, and outer/current provenance masks. `FrameRealizes` remains the
single realization predicate; this structure merely packages it with the
query whose normalization is used by finite search.
-/
structure IntrinsicResolvedQuery (U : SearchUniverse sig) (O : Type) (B : Nat)
    (Γ : StableCtx sig) (env : ResolvedEnv Γ O)
    (outer current : VarMask Γ) where
  query : ResolvedQuery U O B
  realizes : FrameRealizes query.state query.realizedFrame Γ env outer current

namespace IntrinsicResolvedQuery

variable {U : SearchUniverse sig} {O : Type} [DecidableEq O]
  {BΓ BΔ : Nat} {Γ Δ : StableCtx sig}
  {envΓ : ResolvedEnv Γ O} {envΔ : ResolvedEnv Δ O}
  {outerΓ currentΓ : VarMask Γ} {outerΔ currentΔ : VarMask Δ}

/-- The finite normal form represented by an intrinsic query package. -/
def normalize
    (q : IntrinsicResolvedQuery U O BΓ Γ envΓ outerΓ currentΓ) :
    NormalQuery U O :=
  q.query.normalize

@[simp] theorem normalize_eq
    (q : IntrinsicResolvedQuery U O BΓ Γ envΓ outerΓ currentΓ) :
    q.normalize = q.query.normalize := rfl

/--
Contract a descendant intrinsic frame into an ancestor intrinsic frame when
their resolved queries have the same finite normal form.
-/
noncomputable def contractionTo
    (desc : IntrinsicResolvedQuery U O BΓ Γ envΓ outerΓ currentΓ)
    (ancestor : IntrinsicResolvedQuery U O BΔ Δ envΔ outerΔ currentΔ)
    (h : desc.query.normalize = ancestor.query.normalize) :
    FrameContraction envΓ envΔ outerΓ currentΓ outerΔ currentΔ :=
  FrameContraction.of_normalize_eq desc.query ancestor.query
    desc.realizes ancestor.realizes h

end IntrinsicResolvedQuery

/-! ### Exact consistency witnesses -/

/--
An actual consistency neutral for an intrinsic query. Its result type,
resolved dependency support, and two-bit provenance signature are exactly the
query target, while `freshValid` rules out invalid nested batches.
-/
structure ConsistencyWitness {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {B : Nat} {Γ : StableCtx sig} {env : ResolvedEnv Γ O}
    {outer current : VarMask Γ}
    (q : IntrinsicResolvedQuery U O B Γ env outer current) where
  neutral : SNegNeu Γ (.shift q.query.target.result.val)
  resolvedSupport_eq : neutral.resolvedSupport env = q.query.target.support
  useSig_eq : neutral.useSig outer current = q.query.useSig
  freshValid_eq : neutral.freshValid = true

namespace ConsistencyWitness

variable {U : SearchUniverse sig} {O : Type} [DecidableEq O]
  {BΓ BΔ : Nat} {Γ Δ : StableCtx sig}
  {envΓ : ResolvedEnv Γ O} {envΔ : ResolvedEnv Δ O}
  {outerΓ currentΓ : VarMask Γ} {outerΔ currentΔ : VarMask Δ}

/-- Equality of normalized queries fixes their exact target obligation. -/
theorem target_eq
    (desc : IntrinsicResolvedQuery U O BΓ Γ envΓ outerΓ currentΓ)
    (ancestor : IntrinsicResolvedQuery U O BΔ Δ envΔ outerΔ currentΔ)
    (h : desc.query.normalize = ancestor.query.normalize) :
    desc.query.target = ancestor.query.target :=
  congrArg NormalQuery.target h

/-- Equality of normalized queries fixes the requested output-usage signature. -/
theorem query_useSig_eq
    (desc : IntrinsicResolvedQuery U O BΓ Γ envΓ outerΓ currentΓ)
    (ancestor : IntrinsicResolvedQuery U O BΔ Δ envΔ outerΔ currentΔ)
    (h : desc.query.normalize = ancestor.query.normalize) :
    desc.query.useSig = ancestor.query.useSig :=
  congrArg NormalQuery.useSig h

/-- Transport only the result index of a saturated consistency neutral. -/
private def castResult {Γ : StableCtx sig} {P Q : Pos sig.nBases}
    (h : P = Q) (n : SNegNeu Γ (.shift P)) : SNegNeu Γ (.shift Q) :=
  h ▸ n

@[simp] private theorem castResult_resolvedSupport
    {Γ : StableCtx sig} {P Q : Pos sig.nBases} (h : P = Q)
    (n : SNegNeu Γ (.shift P)) (env : ResolvedEnv Γ O) :
    (castResult h n).resolvedSupport env = n.resolvedSupport env := by
  cases h
  rfl

@[simp] private theorem castResult_useSig
    {Γ : StableCtx sig} {P Q : Pos sig.nBases} (h : P = Q)
    (n : SNegNeu Γ (.shift P)) (outer current : VarMask Γ) :
    (castResult h n).useSig outer current = n.useSig outer current := by
  cases h
  rfl

@[simp] private theorem castResult_freshValid
    {Γ : StableCtx sig} {P Q : Pos sig.nBases} (h : P = Q)
    (n : SNegNeu Γ (.shift P)) :
    (castResult h n).freshValid = n.freshValid := by
  cases h
  rfl

@[simp] private theorem castResult_rawSupport
    {Γ : StableCtx sig} {P Q : Pos sig.nBases} (h : P = Q)
    (n : SNegNeu Γ (.shift P)) :
    (castResult h n).rawSupport = n.rawSupport := by
  cases h
  rfl

@[simp] private theorem castResult_nodeSize
    {Γ : StableCtx sig} {P Q : Pos sig.nBases} (h : P = Q)
    (n : SNegNeu Γ (.shift P)) :
    (castResult h n).nodeSize = n.nodeSize := by
  cases h
  rfl

/--
Rename a descendant consistency witness into an ancestor context. This is the
witness-level form of repeated-normal-query contraction; it deliberately does
not yet claim a general derivation splice.
-/
noncomputable def contract_of_normalize_eq
    (desc : IntrinsicResolvedQuery U O BΓ Γ envΓ outerΓ currentΓ)
    (ancestor : IntrinsicResolvedQuery U O BΔ Δ envΔ outerΔ currentΔ)
    (h : desc.query.normalize = ancestor.query.normalize)
    (w : ConsistencyWitness desc) : ConsistencyWitness ancestor := by
  have hP : desc.query.target.result.val = ancestor.query.target.result.val :=
    congrArg (fun q : NormalQuery U O => q.target.result.val) h
  have hK : desc.query.target.support = ancestor.query.target.support :=
    congrArg (fun q : NormalQuery U O => q.target.support) h
  have hu : desc.query.useSig = ancestor.query.useSig :=
    query_useSig_eq desc ancestor h
  let c := desc.contractionTo ancestor h
  refine {
    neutral := castResult hP (w.neutral.rename c.rename)
    resolvedSupport_eq := ?_
    useSig_eq := ?_
    freshValid_eq := ?_
  }
  · rw [castResult_resolvedSupport,
      SNegNeu.resolvedSupport_rename c.rename c.env_preserves w.neutral,
      w.resolvedSupport_eq, hK]
  · rw [castResult_useSig,
      SNegNeu.useSig_rename c.rename outerΓ currentΓ outerΔ currentΔ
        c.outer_preserves c.current_preserves w.neutral,
      w.useSig_eq, hu]
  · rw [castResult_freshValid,
      SNegNeu.freshValid_rename c.rename w.neutral, w.freshValid_eq]

/-- Contracting a witness preserves its exact custom constructor size. -/
theorem contract_nodeSize
    (desc : IntrinsicResolvedQuery U O BΓ Γ envΓ outerΓ currentΓ)
    (ancestor : IntrinsicResolvedQuery U O BΔ Δ envΔ outerΔ currentΔ)
    (h : desc.query.normalize = ancestor.query.normalize)
    (w : ConsistencyWitness desc) :
    (contract_of_normalize_eq desc ancestor h w).neutral.nodeSize =
      w.neutral.nodeSize := by
  simp only [contract_of_normalize_eq, castResult_nodeSize]
  exact SNegNeu.nodeSize_rename (desc.contractionTo ancestor h).rename w.neutral

/-- The contracted witness retains exact resolved dependency support. -/
theorem contract_resolvedSupport
    (desc : IntrinsicResolvedQuery U O BΓ Γ envΓ outerΓ currentΓ)
    (ancestor : IntrinsicResolvedQuery U O BΔ Δ envΔ outerΔ currentΔ)
    (h : desc.query.normalize = ancestor.query.normalize)
    (w : ConsistencyWitness desc) :
    (contract_of_normalize_eq desc ancestor h w).neutral.resolvedSupport envΔ =
      ancestor.query.target.support :=
  (contract_of_normalize_eq desc ancestor h w).resolvedSupport_eq

/-- The contracted witness retains the exact requested usage signature. -/
theorem contract_useSig
    (desc : IntrinsicResolvedQuery U O BΓ Γ envΓ outerΓ currentΓ)
    (ancestor : IntrinsicResolvedQuery U O BΔ Δ envΔ outerΔ currentΔ)
    (h : desc.query.normalize = ancestor.query.normalize)
    (w : ConsistencyWitness desc) :
    (contract_of_normalize_eq desc ancestor h w).neutral.useSig outerΔ currentΔ =
      ancestor.query.useSig :=
  (contract_of_normalize_eq desc ancestor h w).useSig_eq

/-- The contracted witness remains recursively fresh-valid. -/
theorem contract_freshValid
    (desc : IntrinsicResolvedQuery U O BΓ Γ envΓ outerΓ currentΓ)
    (ancestor : IntrinsicResolvedQuery U O BΔ Δ envΔ outerΔ currentΔ)
    (h : desc.query.normalize = ancestor.query.normalize)
    (w : ConsistencyWitness desc) :
    (contract_of_normalize_eq desc ancestor h w).neutral.freshValid = true :=
  (contract_of_normalize_eq desc ancestor h w).freshValid_eq

/-- Raw occurrence support is transported by the contraction renaming's image. -/
theorem contract_rawSupport
    (desc : IntrinsicResolvedQuery U O BΓ Γ envΓ outerΓ currentΓ)
    (ancestor : IntrinsicResolvedQuery U O BΔ Δ envΔ outerΔ currentΔ)
    (h : desc.query.normalize = ancestor.query.normalize)
    (w : ConsistencyWitness desc) :
    (contract_of_normalize_eq desc ancestor h w).neutral.rawSupport =
      StableRename.mapRaw (desc.contractionTo ancestor h).rename
        w.neutral.rawSupport := by
  simp only [contract_of_normalize_eq, castResult_rawSupport]
  exact SNegNeu.rawSupport_rename (desc.contractionTo ancestor h).rename w.neutral

end ConsistencyWitness

/-! ### Boundary fixtures -/

namespace ConsistencyQueryFixtures

def sig0 : Signature := ⟨0, #[]⟩
abbrev O1 := Fin 1
def o : O1 := ⟨0, by decide⟩
def P : Pos 0 := .zero
def S : StableTy 0 := .neg (.shift P)
def U : SearchUniverse sig0 := ⟨{P}, ∅, {S}⟩
def UP : UPos U := ⟨P, Finset.mem_singleton_self P⟩
def US : UStable U := ⟨S, Finset.mem_singleton_self S⟩

def st0 : ResolvedState U O1 2 := rootState U O1 2
theorem hd0 : st0.depth < 2 := by decide
def st1 : ResolvedState U O1 2 := st0.pushResolved hd0 US {o}
theorem hd1 : st1.depth < 2 := by decide
def st2 : ResolvedState U O1 2 := st1.pushResolved hd1 US {o}

def Γ1 : StableCtx sig0 := .snoc .empty US.val
def Γ2 : StableCtx sig0 := .snoc Γ1 US.val
def env0 : ResolvedEnv (.empty : StableCtx sig0) O1 := ResolvedEnv.empty O1
def env1 : ResolvedEnv Γ1 O1 := ResolvedEnv.extend env0 {o}
def env2 : ResolvedEnv Γ2 O1 := ResolvedEnv.extend env1 {o}

theorem split1 : SplitRealizes st1 (.empty : StableCtx sig0) Γ1 env1 := by
  simpa [st0, st1, Γ1, env0, env1] using
    (SplitRealizes.of_root U O1 2).pushResolved hd0 US {o}

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

def outer1 : VarMask Γ1 := FrameRealizes.outerMask realizes1 input1
def current1 : VarMask Γ1 := FrameRealizes.currentMask realizes1
def outer2 : VarMask Γ2 := FrameRealizes.outerMask realizes2 input2
def current2 : VarMask Γ2 := FrameRealizes.currentMask realizes2

theorem frame1 : FrameRealizes st1 input1 Γ1 env1 outer1 current1 :=
  FrameRealizes.canonical realizes1 input1

theorem frame2 : FrameRealizes st2 input2 Γ2 env2 outer2 current2 :=
  FrameRealizes.canonical realizes2 input2

def target : Obligation U O1 := ⟨UP, {o}⟩
def requestedUse : UseSig := ⟨true, true⟩

def resolved1 : ResolvedQuery U O1 2 where
  state := st1
  realizedFrame := input1
  coverage := ∅
  target := target
  useSig := requestedUse

def resolved2 : ResolvedQuery U O1 2 where
  state := st2
  realizedFrame := input2
  coverage := ∅
  target := target
  useSig := requestedUse

def query1 : IntrinsicResolvedQuery U O1 2 Γ1 env1 outer1 current1 :=
  ⟨resolved1, frame1⟩

def query2 : IntrinsicResolvedQuery U O1 2 Γ2 env2 outer2 current2 :=
  ⟨resolved2, frame2⟩

/-- Duplicate complete labels contract even though the descendant has two
intrinsic occurrences and the ancestor only one. -/
theorem duplicate_label_normalize_eq :
    query2.query.normalize = query1.query.normalize := by
  native_decide

def descendantWitness : ConsistencyWitness query2 where
  neutral := .var .here
  resolvedSupport_eq := by native_decide
  useSig_eq := by native_decide
  freshValid_eq := rfl

noncomputable def ancestorWitness : ConsistencyWitness query1 :=
  descendantWitness.contract_of_normalize_eq query2 query1
    duplicate_label_normalize_eq

theorem duplicate_label_witness_size_preserved :
    ancestorWitness.neutral.nodeSize = descendantWitness.neutral.nodeSize := by
  exact descendantWitness.contract_nodeSize query2 query1
    duplicate_label_normalize_eq

def resolvedWrongUse : ResolvedQuery U O1 2 where
  state := st1
  realizedFrame := input1
  coverage := ∅
  target := target
  useSig := ⟨true, false⟩

/-- Equal frames and targets do not erase the output provenance requirement. -/
theorem differing_useSig_rejected :
    resolved2.normalize ≠ resolvedWrongUse.normalize := by
  native_decide

end ConsistencyQueryFixtures

end Gimbal.Equality.Scherer
