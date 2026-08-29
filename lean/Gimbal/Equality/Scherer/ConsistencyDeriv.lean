/-
  Generative, work-free consistency derivations for the Scherer core.

  This layer describes only legitimate saturated syntax.  It deliberately
  contains no source-site scheduling, search policy, recursion fuel, oracle,
  or global forest.  Every selected observation carries its own recursively
  generated query derivation and the exact local freshness side conditions.
-/

import Gimbal.Equality.Scherer.ConsistencyScope

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Requests and exact resolved pending -/

/-- A nonzero, uncovered consistency request which genuinely uses the current
round and is not already discharged by exact-support strong retrieval. -/
structure FreshRequest {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {B : Nat} {Γ : StableCtx sig} (s : ConsistencyScope U O B Γ)
    (target : Obligation U O) (useSig : UseSig) : Prop where
  nonzero : target.result.val ≠ .zero
  uncovered : target ∉ s.coverage
  currentUse : useSig.usesCurrent = true
  notStrong : ¬ StrongAt s.state target.result.val target.support

/-- A local inconsistency request.  Zero is intentionally separate from
`FreshRequest`: it needs neither coverage consumption nor a strong block. -/
structure ZeroRequest {U : SearchUniverse sig} {O : Type}
    {B : Nat} {Γ : StableCtx sig} (_s : ConsistencyScope U O B Γ)
    (_K : DepSupport O) (_useSig : UseSig) : Prop where
  zero_mem : (.zero : Pos sig.nBases) ∈ U.pos

/-- Turn an exact obligation list into the occurrence-sensitive pending
annotations consumed by the batch body. -/
def obligationPending {U : SearchUniverse sig} {O : Type}
    (xs : List (Obligation U O)) : ResolvedPending U O :=
  ResolvedPending.pendingFromObligations (xs.map fun o => (o.result, o.support))

@[simp] theorem obligationPending_nil {U : SearchUniverse sig} {O : Type} :
    obligationPending ([] : List (Obligation U O)) = [] := rfl

@[simp] theorem obligationPending_cons {U : SearchUniverse sig} {O : Type}
    (o : Obligation U O) (rest : List (Obligation U O)) :
    obligationPending (o :: rest) =
      ⟨o.result, o.support⟩ :: obligationPending rest := rfl

@[simp] theorem obligationPending_length {U : SearchUniverse sig} {O : Type}
    (xs : List (Obligation U O)) :
    (obligationPending xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons o rest ih =>
      change (obligationPending rest).length + 1 = rest.length + 1
      rw [ih]

/-- Change only consumed coverage.  Realized state, environment, and masks are
definitionally unchanged. -/
def ConsistencyScope.withCoverage {U : SearchUniverse sig} {O : Type}
    {B : Nat} {Γ : StableCtx sig} (s : ConsistencyScope U O B Γ)
    (coverage : Finset (Obligation U O)) : ConsistencyScope U O B Γ :=
  { s with coverage := coverage }

@[simp] theorem ConsistencyScope.withCoverage_state
    {U : SearchUniverse sig} {O : Type} {B : Nat} {Γ : StableCtx sig}
    (s : ConsistencyScope U O B Γ) (coverage : Finset (Obligation U O)) :
    (s.withCoverage coverage).state = s.state := rfl

@[simp] theorem ConsistencyScope.withCoverage_env
    {U : SearchUniverse sig} {O : Type} {B : Nat} {Γ : StableCtx sig}
    (s : ConsistencyScope U O B Γ) (coverage : Finset (Obligation U O)) :
    (s.withCoverage coverage).env = s.env := rfl

@[simp] theorem ConsistencyScope.withCoverage_outer
    {U : SearchUniverse sig} {O : Type} {B : Nat} {Γ : StableCtx sig}
    (s : ConsistencyScope U O B Γ) (coverage : Finset (Obligation U O)) :
    (s.withCoverage coverage).outer = s.outer := rfl

@[simp] theorem ConsistencyScope.withCoverage_current
    {U : SearchUniverse sig} {O : Type} {B : Nat} {Γ : StableCtx sig}
    (s : ConsistencyScope U O B Γ) (coverage : Finset (Obligation U O)) :
    (s.withCoverage coverage).current = s.current := rfl

@[simp] theorem ConsistencyScope.withCoverage_coverage
    {U : SearchUniverse sig} {O : Type} {B : Nat} {Γ : StableCtx sig}
    (s : ConsistencyScope U O B Γ) (coverage : Finset (Obligation U O)) :
    (s.withCoverage coverage).coverage = coverage := rfl

/-! ### Generative work-free judgments -/

mutual

/-- Generated saturated negative neutrals. -/
inductive CNeg {U : SearchUniverse sig} {O : Type} [DecidableEq O] {B : Nat}
    : {Γ : StableCtx sig} → (s : ConsistencyScope U O B Γ) →
      {N : Neg sig.nBases} → SNegNeu Γ N → Type where
  | var {N : Neg sig.nBases} (x : StableVar Γ (.neg N)) : CNeg s (.var x)
  | fst {A B : Neg sig.nBases} {n : SNegNeu Γ (.prod A B)} :
      CNeg s n → CNeg s (.fst n)
  | snd {A B : Neg sig.nBases} {n : SNegNeu Γ (.prod A B)} :
      CNeg s n → CNeg s (.snd n)
  | app {A : Pos sig.nBases} {N : Neg sig.nBases}
      {n : SNegNeu Γ (.arr A N)} {p : SPosNeu Γ A} :
      CNeg s n → CPos s p → CNeg s (.app n p)

/-- Generated saturated positive neutrals.  Entering a shifted invertible
subderivation resets the current round exactly once. -/
inductive CPos {U : SearchUniverse sig} {O : Type} [DecidableEq O] {B : Nat}
    : {Γ : StableCtx sig} → (s : ConsistencyScope U O B Γ) →
      {P : Pos sig.nBases} → SPosNeu Γ P → Type where
  | atom {q : Fin sig.nBases} (x : StableVar Γ (.atom q)) : CPos s (.atom x)
  | inl {A B : Pos sig.nBases} {p : SPosNeu Γ A} :
      CPos s p → CPos s (.inl p)
  | inr {A B : Pos sig.nBases} {p : SPosNeu Γ B} :
      CPos s p → CPos s (.inr p)
  | shift {N : Neg sig.nBases} {t : SInv Γ .empty .empty (.neg N)} :
      CInv s.resetRound ([] : ResolvedPending U O) t → CPos s (.shift t)

/-- Generated invertible derivations indexed by exact resolved annotations for
every pending occurrence. -/
inductive CInv {U : SearchUniverse sig} {O : Type} [DecidableEq O] {B : Nat} :
    {Old New : StableCtx sig} →
    (s : ConsistencyScope U O B (Old.append New)) →
    (pending : ResolvedPending U O) →
    {G : Goal sig.nBases} →
    SInv Old New pending.erase G → Type where
  | caseSum {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)}
      {A Bp : Pos sig.nBases} {hSum : Pos.sum A Bp ∈ U.pos}
      {hA : A ∈ U.pos} {hB : Bp ∈ U.pos} {K : DepSupport O}
      {rest : ResolvedPending U O} {G : Goal sig.nBases}
      {l : SInv Old New (ResolvedPending.erase (⟨⟨A, hA⟩, K⟩ :: rest)) G}
      {r : SInv Old New (ResolvedPending.erase (⟨⟨Bp, hB⟩, K⟩ :: rest)) G} :
      CInv s (⟨⟨A, hA⟩, K⟩ :: rest) l →
      CInv s (⟨⟨Bp, hB⟩, K⟩ :: rest) r →
      CInv s (⟨⟨.sum A Bp, hSum⟩, K⟩ :: rest) (.caseSum l r)
  | abort {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)}
      {hZero : (.zero : Pos sig.nBases) ∈ U.pos} {K : DepSupport O}
      {rest : ResolvedPending U O} {G : Goal sig.nBases} :
      CInv s (⟨⟨.zero, hZero⟩, K⟩ :: rest) (.abort)
  | storeAtom {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)}
      {q : Fin sig.nBases} {hPos : Pos.atom q ∈ U.pos}
      {hStable : StableTy.atom q ∈ U.stable} {K : DepSupport O}
      {rest : ResolvedPending U O} {G : Goal sig.nBases}
      (hd : s.state.depth < B)
      {t : SInv Old (New.snoc (.atom q)) rest.erase G} :
      CInv (s.pushResolved hd ⟨.atom q, hStable⟩ K) rest t →
      CInv s (⟨⟨.atom q, hPos⟩, K⟩ :: rest) (.storeAtom t)
  | storeShift {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)}
      {N : Neg sig.nBases} {hPos : Pos.shift N ∈ U.pos}
      {hStable : StableTy.neg N ∈ U.stable} {K : DepSupport O}
      {rest : ResolvedPending U O} {G : Goal sig.nBases}
      (hd : s.state.depth < B)
      {t : SInv Old (New.snoc (.neg N)) rest.erase G} :
      CInv (s.pushResolved hd ⟨.neg N, hStable⟩ K) rest t →
      CInv s (⟨⟨.shift N, hPos⟩, K⟩ :: rest) (.storeShift t)
  | unit {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)} :
      CInv s ([] : ResolvedPending U O) (.unit)
  | pair {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)}
      {A Bn : Neg sig.nBases}
      {l : SInv Old New .empty (.neg A)} {r : SInv Old New .empty (.neg Bn)} :
      CInv s [] l → CInv s [] r → CInv s [] (.pair l r)
  | lam {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)}
      {A : Pos sig.nBases} {hA : A ∈ U.pos} {N : Neg sig.nBases}
      {t : SInv Old New (ResolvedPending.lambdaPending (O := O) ⟨A, hA⟩).erase
        (.neg N)} :
      CInv s (ResolvedPending.lambdaPending (O := O) ⟨A, hA⟩) t →
      CInv s [] (.lam t)
  | satShift {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)}
      {P : Pos sig.nBases} {sat : Sat Old New P} :
      CSat s sat → CInv s [] (.satShift sat)
  | satPos {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)}
      {P : Pos sig.nBases} {sat : Sat Old New P} :
      CSat s sat → CInv s [] (.satPos sat)

/-- Generated saturation.  A batch body runs after a round reset with exactly
the newly consumed obligation set added to coverage. -/
inductive CSat {U : SearchUniverse sig} {O : Type} [DecidableEq O] {B : Nat} :
    {Old New : StableCtx sig} →
    (s : ConsistencyScope U O B (Old.append New)) →
    {P : Pos sig.nBases} → Sat Old New P → Type where
  | inconsistent {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)}
      {P : Pos sig.nBases} {K : DepSupport O} {u : UseSig}
      (request : ZeroRequest s K u)
      {z : SNegNeu (Old.append New) (.shift .zero)}
      (query : CQuery s ⟨⟨.zero, request.zero_mem⟩, K⟩ u z) :
      CSat s (P := P) (.inconsistent z)
  | done {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)}
      {P : Pos sig.nBases} {v : SPosNeu (Old.append New) P} :
      CPos s v → CSat s (.done v)
  | batch {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)}
      {P : Pos sig.nBases} {xs : List (Obligation U O)}
      {obs : NonemptyBatchObs (Old.append New) (obligationPending xs).erase}
      {body : SInv (Old.append New) .empty (obligationPending xs).erase (.pos P)} :
      CBatch s xs obs →
      CInv (Old := Old.append New) (New := .empty)
        (s.resetRound.withCoverage (s.coverage ∪ xs.toFinset))
        (obligationPending xs) body →
      CSat s (.batch obs body)

/-- A nonempty selected batch.  Each occurrence carries an exact recursive
query, all local request gates, and syntax-split freshness.  `notMem` enforces
Nodup on full `(P,K)` obligations while permitting equal `P` at distinct `K`. -/
inductive CBatch {U : SearchUniverse sig} {O : Type} [DecidableEq O] {B : Nat} :
    {Old New : StableCtx sig} →
    (s : ConsistencyScope U O B (Old.append New)) →
    (xs : List (Obligation U O)) →
    NonemptyBatchObs (Old.append New) (obligationPending xs).erase → Type where
  | one {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)}
      {target : Obligation U O} {u : UseSig}
      {n : SNegNeu (Old.append New) (.shift target.result.val)} :
      CQuery s target u n → FreshRequest s target u →
      n.uses (newMask Old New) = true →
      CBatch s [target] (.one n)
  | cons {Old New : StableCtx sig}
      {s : ConsistencyScope U O B (Old.append New)}
      {target : Obligation U O} {u : UseSig}
      {n : SNegNeu (Old.append New) (.shift target.result.val)}
      {rest : List (Obligation U O)}
      {obs : NonemptyBatchObs (Old.append New) (obligationPending rest).erase} :
      CQuery s target u n → FreshRequest s target u →
      n.uses (newMask Old New) = true → target ∉ rest →
      CBatch s rest obs → CBatch s (target :: rest) (.cons n obs)

/-- Exact recursive query evidence used at every observation occurrence. -/
inductive CQuery {U : SearchUniverse sig} {O : Type} [DecidableEq O] {B : Nat}
    : {Γ : StableCtx sig} → (s : ConsistencyScope U O B Γ) →
      (target : Obligation U O) → (useSig : UseSig) →
      SNegNeu Γ (.shift target.result.val) → Type where
  | intro {n : SNegNeu Γ (.shift target.result.val)} :
      CNeg s n →
      n.resolvedSupport s.env = target.support →
      n.useSig s.outer s.current = useSig →
      CQuery s target useSig n

end

/-! ### Packaged root derivations -/

/-- A generated consistency derivation packages the generated neutral but no
search schedule or executable choice. -/
structure ConsistencyDeriv {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {B : Nat} {Γ : StableCtx sig} (s : ConsistencyScope U O B Γ)
    (target : Obligation U O) (useSig : UseSig) where
  neutral : SNegNeu Γ (.shift target.result.val)
  query : CQuery s target useSig neutral

/-- One selected observation with all query and freshness data exposed. -/
structure FreshEntry {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {B : Nat} (Old New : StableCtx sig)
    (s : ConsistencyScope U O B (Old.append New))
    (target : Obligation U O) where
  useSig : UseSig
  neutral : SNegNeu (Old.append New) (.shift target.result.val)
  query : CQuery s target useSig neutral
  request : FreshRequest s target useSig
  usesNew : neutral.uses (newMask Old New) = true

/-! ### Structural soundness -/

mutual

/-- Every generated negative neutral is recursively fresh-valid. -/
theorem CNeg.freshValid {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {B : Nat} {Γ : StableCtx sig} {s : ConsistencyScope U O B Γ}
    {N : Neg sig.nBases} {n : SNegNeu Γ N} :
    CNeg s n → n.freshValid = true
  | .var _ => rfl
  | .fst d => by
      simpa only [SNegNeu.freshValid] using CNeg.freshValid (s := s) d
  | .snd d => by
      simpa only [SNegNeu.freshValid] using CNeg.freshValid (s := s) d
  | .app dn dp => by
      simp only [SNegNeu.freshValid, CNeg.freshValid dn, CPos.freshValid dp,
        Bool.true_and]

/-- Every generated positive neutral is recursively fresh-valid. -/
theorem CPos.freshValid {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {B : Nat} {Γ : StableCtx sig} {s : ConsistencyScope U O B Γ}
    {P : Pos sig.nBases} {p : SPosNeu Γ P} :
    CPos s p → p.freshValid = true
  | .atom _ => rfl
  | .inl d => by
      simpa only [SPosNeu.freshValid] using CPos.freshValid (s := s) d
  | .inr d => by
      simpa only [SPosNeu.freshValid] using CPos.freshValid (s := s) d
  | .shift d => CInv.freshValid d

/-- Every generated invertible derivation is recursively fresh-valid. -/
theorem CInv.freshValid {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {B : Nat} {Old New : StableCtx sig}
    {s : ConsistencyScope U O B (Old.append New)}
    {pending : ResolvedPending U O} {G : Goal sig.nBases}
    {t : SInv Old New pending.erase G} :
    CInv s pending t → t.freshValid = true
  | .caseSum dl dr => by
      change (_ && _) = true
      exact Bool.and_eq_true_iff.mpr
        ⟨CInv.freshValid (Old := Old) (New := New) (s := s) dl,
          CInv.freshValid (Old := Old) (New := New) (s := s) dr⟩
  | .abort => rfl
  | .storeAtom _ d => CInv.freshValid d
  | .storeShift _ d => CInv.freshValid d
  | .unit => rfl
  | .pair dl dr => by
      change (_ && _) = true
      exact Bool.and_eq_true_iff.mpr
        ⟨CInv.freshValid (Old := Old) (New := New) (s := s) dl,
          CInv.freshValid (Old := Old) (New := New) (s := s) dr⟩
  | .lam d => CInv.freshValid d
  | .satShift d => CSat.freshValid d
  | .satPos d => CSat.freshValid d

/-- Every generated saturation is recursively fresh-valid. -/
theorem CSat.freshValid {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {B : Nat} {Old New : StableCtx sig}
    {s : ConsistencyScope U O B (Old.append New)}
    {P : Pos sig.nBases} {sat : Sat Old New P} :
    CSat s sat → sat.freshValid = true
  | .inconsistent _ q => CQuery.freshValid q
  | .done d => CPos.freshValid d
  | .batch db di => by
      simp only [Sat.freshValid, CBatch.allUses db, CBatch.allFreshValid db,
        CInv.freshValid di, Bool.true_and]

/-- Every generated batch entry uses the syntax-level shared `New`. -/
theorem CBatch.allUses {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {B : Nat} {Old New : StableCtx sig}
    {s : ConsistencyScope U O B (Old.append New)}
    {xs : List (Obligation U O)}
    {obs : NonemptyBatchObs (Old.append New) (obligationPending xs).erase} :
    CBatch s xs obs → NonemptyBatchObs.allUses (newMask Old New) obs = true
  | .one _ _ hUses => hUses
  | .cons _ _ hUses _ rest => by
      change (_ && _) = true
      exact Bool.and_eq_true_iff.mpr
        ⟨hUses, CBatch.allUses (Old := Old) (New := New) (s := s) rest⟩

/-- Every generated batch entry is itself recursively fresh-valid. -/
theorem CBatch.allFreshValid {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {B : Nat} {Old New : StableCtx sig}
    {s : ConsistencyScope U O B (Old.append New)}
    {xs : List (Obligation U O)}
    {obs : NonemptyBatchObs (Old.append New) (obligationPending xs).erase} :
    CBatch s xs obs → NonemptyBatchObs.allFreshValid obs = true
  | .one q _ _ => CQuery.freshValid q
  | .cons q _ _ _ rest => by
      change (_ && _) = true
      exact Bool.and_eq_true_iff.mpr
        ⟨CQuery.freshValid q,
          CBatch.allFreshValid (Old := Old) (New := New) (s := s) rest⟩

/-- Exact query evidence inherits recursive freshness from its generated
neutral. -/
theorem CQuery.freshValid {U : SearchUniverse sig} {O : Type} [DecidableEq O]
    {B : Nat} {Γ : StableCtx sig} {s : ConsistencyScope U O B Γ}
    {target : Obligation U O} {useSig : UseSig}
    {n : SNegNeu Γ (.shift target.result.val)} :
    CQuery s target useSig n → n.freshValid = true
  | .intro d _ _ => CNeg.freshValid d

end

namespace CQuery

variable {U : SearchUniverse sig} {O : Type} [DecidableEq O] {B : Nat}
  {Γ : StableCtx sig} {s : ConsistencyScope U O B Γ}
  {target : Obligation U O} {useSig : UseSig}
  {n : SNegNeu Γ (.shift target.result.val)}

theorem resolvedSupport_eq (d : CQuery s target useSig n) :
    n.resolvedSupport s.env = target.support := by
  cases d with
  | intro _ hSupport _ => exact hSupport

theorem useSig_eq (d : CQuery s target useSig n) :
    n.useSig s.outer s.current = useSig := by
  cases d with
  | intro _ _ hUse => exact hUse

theorem usesCurrent (d : CQuery s target useSig n)
    (request : FreshRequest s target useSig) :
    n.uses s.current = true := by
  have h := congrArg UseSig.usesCurrent d.useSig_eq
  exact h.trans request.currentUse

end CQuery

namespace ConsistencyDeriv

variable {U : SearchUniverse sig} {O : Type} [DecidableEq O] {B : Nat}
  {Γ : StableCtx sig} {s : ConsistencyScope U O B Γ}
  {target : Obligation U O} {useSig : UseSig}

/-- Forget generative structure to the previously landed exact witness. -/
def toWitness (d : ConsistencyDeriv s target useSig) :
    ConsistencyWitness (s.query target useSig) where
  neutral := d.neutral
  resolvedSupport_eq := d.query.resolvedSupport_eq
  useSig_eq := d.query.useSig_eq
  freshValid_eq := d.query.freshValid

theorem freshValid (d : ConsistencyDeriv s target useSig) :
    d.neutral.freshValid = true :=
  d.query.freshValid

/-- A generated query neutral with syntax-split use evidence is a `FreshObs`.
The extra premise is intentional: the flat realized scope does not identify
its current mask with an arbitrary `Old.append New` split. -/
def toFreshObs {Old New : StableCtx sig}
    {s : ConsistencyScope U O B (Old.append New)}
    {target : Obligation U O} {useSig : UseSig}
    (d : ConsistencyDeriv s target useSig)
    (usesNew : d.neutral.uses (newMask Old New) = true) :
    FreshObs Old New target.result.val where
  neu := d.neutral
  usesNew := usesNew
  valid := d.query.freshValid

end ConsistencyDeriv

namespace FreshEntry

variable {U : SearchUniverse sig} {O : Type} [DecidableEq O] {B : Nat}
  {Old New : StableCtx sig} {s : ConsistencyScope U O B (Old.append New)}
  {target : Obligation U O}

def toDeriv (e : FreshEntry Old New s target) :
    ConsistencyDeriv s target e.useSig where
  neutral := e.neutral
  query := e.query

def toFreshObs (e : FreshEntry Old New s target) :
    FreshObs Old New target.result.val :=
  e.toDeriv.toFreshObs e.usesNew

theorem usesCurrent (e : FreshEntry Old New s target) :
    e.neutral.uses s.current = true :=
  e.query.usesCurrent e.request

theorem nonzero (e : FreshEntry Old New s target) :
    target.result.val ≠ .zero :=
  e.request.nonzero

theorem uncovered (e : FreshEntry Old New s target) :
    target ∉ s.coverage :=
  e.request.uncovered

theorem notStrong (e : FreshEntry Old New s target) :
    ¬ StrongAt s.state target.result.val target.support :=
  e.request.notStrong

end FreshEntry

namespace CBatch

variable {U : SearchUniverse sig} {O : Type} [DecidableEq O] {B : Nat}
  {Old New : StableCtx sig} {s : ConsistencyScope U O B (Old.append New)}

/-- Exact obligation identities are duplicate-free. -/
theorem obligations_nodup {xs : List (Obligation U O)}
    {obs : NonemptyBatchObs (Old.append New) (obligationPending xs).erase}
    : (d : CBatch s xs obs) → xs.Nodup
  | .one _ _ _ => by simp
  | .cons _ _ _ hNotMem rest =>
      List.nodup_cons.mpr ⟨hNotMem,
        obligations_nodup (xs := _) (obs := _) rest⟩

/-- The generative batch is nonempty at the exact obligation level. -/
theorem obligations_nonempty {xs : List (Obligation U O)}
    {obs : NonemptyBatchObs (Old.append New) (obligationPending xs).erase}
    (d : CBatch s xs obs) : xs ≠ [] := by
  cases d <;> simp

theorem obligations_length_pos {xs : List (Obligation U O)}
    {obs : NonemptyBatchObs (Old.append New) (obligationPending xs).erase}
    (d : CBatch s xs obs) : 0 < xs.length := by
  exact Nat.zero_lt_of_ne_zero fun h =>
    obligations_nonempty d (List.length_eq_zero_iff.mp h)

/-- Forget exact requests/support annotations to the established selected-batch
freshness carrier. -/
def toSelectedBatch {xs : List (Obligation U O)}
    {obs : NonemptyBatchObs (Old.append New) (obligationPending xs).erase} :
    (d : CBatch s xs obs) → SelectedBatch Old New (obligationPending xs).erase
  | .one q _ hUses =>
      .one { neu := _
             usesNew := hUses
             valid := q.freshValid }
  | .cons q _ hUses _ rest =>
      .cons { neu := _
              usesNew := hUses
              valid := q.freshValid }
        (toSelectedBatch rest)

end CBatch

/-! ### Boundary regressions -/

/-- Full obligations, rather than result types alone, are the duplicate key. -/
theorem obligation_ne_of_support_ne {U : SearchUniverse sig} {O : Type}
    {a b : Obligation U O} (hSupport : a.support ≠ b.support) : a ≠ b := by
  intro h
  exact hSupport (congrArg Obligation.support h)

/-- A recursively invalid nested batch cannot be generated. -/
theorem CNeg.not_of_freshValid_false
    {U : SearchUniverse sig} {O : Type} [DecidableEq O] {B : Nat}
    {Γ : StableCtx sig} {s : ConsistencyScope U O B Γ}
    {N : Neg sig.nBases} {n : SNegNeu Γ N}
    (hBad : n.freshValid = false) : IsEmpty (CNeg s n) :=
  ⟨fun d => Bool.noConfusion (d.freshValid.symm.trans hBad)⟩

/-- The same exclusion holds at the whole saturated derivation boundary. -/
theorem CSat.not_of_freshValid_false
    {U : SearchUniverse sig} {O : Type} [DecidableEq O] {B : Nat}
    {Old New : StableCtx sig} {s : ConsistencyScope U O B (Old.append New)}
    {P : Pos sig.nBases} {sat : Sat Old New P}
    (hBad : sat.freshValid = false) : IsEmpty (CSat s sat) :=
  ⟨fun d => Bool.noConfusion (d.freshValid.symm.trans hBad)⟩

/-- Concrete adversarial regression: using the outer `New` is insufficient
when an observation hides an old-only nested batch. -/
theorem nested_bad_freshness_uninhabited
    {U : SearchUniverse Fixtures.sig0} {O : Type} [DecidableEq O]
    {B : Nat}
    (s : ConsistencyScope U O B
      ((StableCtx.snoc .empty (.neg (.shift .zero))).append
        (StableCtx.snoc .empty
          (.neg (.arr (.shift (.shift (.shift .one))) (.shift .zero)))))) :
    IsEmpty (CSat s FreshnessFixtures.usesNew_but_nested_oldOnly_invalid) :=
  CSat.not_of_freshValid_false
    FreshnessFixtures.usesNew_but_nested_oldOnly_invalid_freshValid_false

end Gimbal.Equality.Scherer
