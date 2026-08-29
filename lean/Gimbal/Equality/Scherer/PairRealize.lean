/-
  Realization of locally bound structural-code references and resolver-indexed
  exact traces.  This is the leaf bridge used before pair comparison: no
  comparison, trace extension, scheduling, or separation is defined here.
-/

import Gimbal.Equality.Scherer.ExactTrace

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Resolver-indexed exact traces -/

/-- An exact trace with its resolver fixed in the type. -/
structure ExactTraceAt (R : AliasResolver sig) where
  steps : List (TraceStep (exactObsKeys R))
  isWellFormed :
    ({ resolver := R, steps := steps } :
      TypedTrace (exactObsKeys R)).WellFormed

namespace ExactTraceAt

variable {sig : Signature} {R : AliasResolver sig}

def toTypedTrace (T : ExactTraceAt R) : TypedTrace (exactObsKeys R) where
  resolver := R
  steps := T.steps

@[simp] theorem toTypedTrace_resolver (T : ExactTraceAt R) :
    T.toTypedTrace.resolver = R := rfl

@[simp] theorem toTypedTrace_steps (T : ExactTraceAt R) :
    T.toTypedTrace.steps = T.steps := rfl

theorem wellFormed (T : ExactTraceAt R) : T.toTypedTrace.WellFormed :=
  T.isWellFormed

/-- Package an indexed trace back into the existing resolver-owned interface. -/
def pack (T : ExactTraceAt R) : ExactTrace sig where
  resolver := R
  steps := T.steps
  isWellFormed := T.isWellFormed

@[simp] theorem pack_resolver (T : ExactTraceAt R) : T.pack.resolver = R := rfl

@[simp] theorem pack_steps (T : ExactTraceAt R) : T.pack.steps = T.steps := rfl

end ExactTraceAt

/-- Expose an existing exact trace at its definitionally owned resolver. -/
def ExactTrace.asAt (T : ExactTrace sig) : ExactTraceAt T.resolver where
  steps := T.steps
  isWellFormed := T.isWellFormed

@[simp] theorem ExactTrace.asAt_steps (T : ExactTrace sig) :
    T.asAt.steps = T.steps := rfl

@[simp] theorem ExactTraceAt.pack_asAt (T : ExactTrace sig) :
    T.asAt.pack = T := by
  cases T
  congr

/-! ### Realizing locally nameless references -/

/-- Terminal representatives assigned to the locally bound context `Δ`. -/
structure BoundOrigins (R : AliasResolver sig) (Δ : Ctx sig) where
  ref : ∀ {A}, Var Δ A → ResolvedRef R A

namespace BoundOrigins

variable {R : AliasResolver sig} {Δ Ε : Ctx sig}

def empty (R : AliasResolver sig) :
    BoundOrigins R (Ctx.empty : Ctx sig) where
  ref := fun x => nomatch x

/-- Extend under a lambda or sum payload with one explicit common source. -/
def snoc (D : BoundOrigins R Δ) (source : ResolvedRef R A) :
    BoundOrigins R (Δ.snoc A) where
  ref := by
    intro B x
    cases x with
    | here => exact source
    | there x => exact D.ref x

@[simp] theorem snoc_here (D : BoundOrigins R Δ) (source : ResolvedRef R A) :
    (D.snoc source).ref (.here : Var (Δ.snoc A) A) = source := rfl

@[simp] theorem snoc_there (D : BoundOrigins R Δ)
    (source : ResolvedRef R A) (x : Var Δ B) :
    (D.snoc source).ref (.there x : Var (Δ.snoc A) B) = D.ref x := rfl

/-- A renaming preserves the representatives assigned to its variables. -/
def Respects (D : BoundOrigins R Δ) (ρ : Rename sig Δ Ε)
    (D' : BoundOrigins R Ε) : Prop :=
  ∀ {A} (x : Var Δ A), D'.ref (ρ x) = D.ref x

theorem respects_id (D : BoundOrigins R Δ) :
    D.Respects Rename.id D := by
  intro A x
  rfl

theorem respects_weaken (D : BoundOrigins R Δ) (source : ResolvedRef R A) :
    D.Respects Rename.weaken (D.snoc source) := by
  intro B x
  rfl

theorem Respects.ext {D : BoundOrigins R Δ} {D' : BoundOrigins R Ε}
    {ρ : Rename sig Δ Ε} (h : D.Respects ρ D')
    (source : ResolvedRef R A) :
    (D.snoc source).Respects (Rename.ext ρ) (D'.snoc source) := by
  intro B x
  cases x with
  | here => rfl
  | there x => exact h x

/-- Every locally assigned representative is terminal by construction. -/
theorem ref_terminal (D : BoundOrigins R Δ) (x : Var Δ A) :
    R.target (D.ref x).origin.raw = none :=
  (D.ref x).terminal

def Scoped (pre : OriginScope) (D : BoundOrigins R Δ) : Prop :=
  ∀ {A} (x : Var Δ A), pre.Contains (D.ref x).origin.raw

theorem empty_scoped : (empty R).Scoped pre := by
  intro A x
  nomatch x

theorem snoc_scoped {D : BoundOrigins R Δ} (hD : D.Scoped pre)
    {source : ResolvedRef R A} (hsource : pre.Contains source.origin.raw) :
    (D.snoc source).Scoped pre := by
  intro B x
  cases x with
  | here => exact hsource
  | there x => exact hD x

end BoundOrigins

namespace CanonRef

def realize (D : BoundOrigins R Δ) : CanonRef R Δ A → ResolvedRef R A
  | .bound x => D.ref x
  | .free r => r

@[simp] theorem realize_bound (D : BoundOrigins R Δ) (x : Var Δ A) :
    (CanonRef.bound x : CanonRef R Δ A).realize D = D.ref x := rfl

@[simp] theorem realize_free (D : BoundOrigins R Δ) (r : ResolvedRef R A) :
    (CanonRef.free r : CanonRef R Δ A).realize D = r := rfl

theorem realize_rename {D : BoundOrigins R Δ} {D' : BoundOrigins R Ε}
    {ρ : Rename sig Δ Ε} (h : D.Respects ρ D') (x : CanonRef R Δ A) :
    (x.rename ρ).realize D' = x.realize D := by
  cases x with
  | bound x => exact h x
  | free r => rfl

@[simp] theorem realize_rename_weaken (D : BoundOrigins R Δ)
    (source : ResolvedRef R B) (x : CanonRef R Δ A) :
    (x.rename (Rename.weaken : Rename sig Δ (Δ.snoc B))).realize
        (D.snoc source) = x.realize D :=
  realize_rename (D.respects_weaken source) x

theorem realize_terminal (D : BoundOrigins R Δ) (x : CanonRef R Δ A) :
    R.target (x.realize D).origin.raw = none :=
  (x.realize D).terminal

theorem realize_scoped {D : BoundOrigins R Δ} (hD : D.Scoped pre)
    {x : CanonRef R Δ A} (hx : x.Scoped pre) :
    pre.Contains (x.realize D).origin.raw := by
  cases x with
  | bound x => exact hD x
  | free r => exact hx

end CanonRef

namespace CodeOriginAssignment

/-- Close a locally nameless assignment by realizing every bound reference. -/
def realize (D : BoundOrigins R Δ) (E : CodeOriginAssignment R Δ Γ) :
    OriginAssignment R Γ where
  ref x := (E.ref x).realize D

@[simp] theorem realize_ref (D : BoundOrigins R Δ)
    (E : CodeOriginAssignment R Δ Γ) (x : StableVar Γ S) :
    (E.realize D).ref x = (E.ref x).realize D := rfl

theorem realize_rename_ref {D : BoundOrigins R Δ} {D' : BoundOrigins R Ε}
    {ρ : Rename sig Δ Ε} (h : D.Respects ρ D')
    (E : CodeOriginAssignment R Δ Γ) (x : StableVar Γ S) :
    ((E.rename ρ).realize D').ref x = (E.realize D).ref x :=
  CanonRef.realize_rename h (E.ref x)

@[simp] theorem realize_rename_weaken_ref (D : BoundOrigins R Δ)
    (source : ResolvedRef R A) (E : CodeOriginAssignment R Δ Γ)
    (x : StableVar Γ S) :
    ((E.rename (Rename.weaken : Rename sig Δ (Δ.snoc A))).realize
      (D.snoc source)).ref x = (E.realize D).ref x :=
  CanonRef.realize_rename_weaken D source (E.ref x)

theorem realize_ref_terminal (D : BoundOrigins R Δ)
    (E : CodeOriginAssignment R Δ Γ) (x : StableVar Γ S) :
    R.target ((E.realize D).ref x).origin.raw = none :=
  ((E.realize D).ref x).terminal

theorem realize_ref_scoped {D : BoundOrigins R Δ} (hD : D.Scoped pre)
    {E : CodeOriginAssignment R Δ Γ} (hE : E.Scoped pre)
    (x : StableVar Γ S) :
    pre.Contains ((E.realize D).ref x).origin.raw :=
  CanonRef.realize_scoped hD (hE x)

end CodeOriginAssignment

/-! ### Pending telescope realization -/

namespace PendingAssignment

def tail (E : PendingAssignment R (.cons P ps)) : PendingAssignment R ps where
  ref x := E.ref (.there x)

@[simp] theorem tail_ref (E : PendingAssignment R (.cons P ps))
    (x : PendingVar ps Q) : E.tail.ref x = E.ref (.there x) := rfl

def Scoped (pre : OriginScope) (E : PendingAssignment R ps) : Prop :=
  ∀ {P} (x : PendingVar ps P), pre.Contains (E.ref x).origin.raw

theorem empty_scoped : (PendingAssignment.empty R).Scoped pre := by
  intro P x
  nomatch x

theorem tail_scoped {E : PendingAssignment R (.cons P ps)}
    (hE : E.Scoped pre) : E.tail.Scoped pre := by
  intro Q x
  exact hE (.there x)

end PendingAssignment

namespace BoundOrigins

/-- Realize a selected pending telescope as newest locally bound origins. -/
def pushPending : {Δ : Ctx sig} → {ps : Pending sig} → BoundOrigins R Δ →
    PendingAssignment R ps → BoundOrigins R (Pending.eraseAux ps Δ)
  | _, .empty, D, _ => D
  | Δ, .cons P rest, D, E =>
      pushPending (Δ := Δ.snoc P.erase) (ps := rest)
        (D.snoc (E.ref (.here : PendingVar (.cons P rest) P))) E.tail

theorem pushPending_base (D : BoundOrigins R Δ) (E : PendingAssignment R ps)
    (x : Var Δ A) :
    (D.pushPending E).ref (Pending.weakenCodeBase ps Δ x) = D.ref x := by
  induction ps generalizing Δ with
  | empty =>
      change D.ref x = D.ref x
      rfl
  | cons P rest ih =>
      simpa [pushPending, Pending.weakenCodeBase, Rename.weaken,
        BoundOrigins.snoc] using
        ih (D := D.snoc (E.ref (.here : PendingVar (.cons P rest) P)))
          (E := E.tail) (x := Rename.weaken x)

private theorem weakenCodeBase_natural
    (ps : Pending sig) (ρ : Rename sig Δ Ε) (x : Var Δ A) :
    renameEraseAux ρ ps (Pending.weakenCodeBase ps Δ x) =
      Pending.weakenCodeBase ps Ε (ρ x) := by
  induction ps generalizing Δ Ε with
  | empty => rfl
  | cons P rest ih =>
      exact ih (ρ := Rename.ext ρ) (x := Rename.weaken x)

private theorem pendingHeadVar_eq_weakenCodeBase
    (rest : Pending sig) (Δ : Ctx sig) (H : Object sig.nBases) :
    pendingHeadVar (Δ := Δ) (H := H) rest =
      Pending.weakenCodeBase rest (Δ.snoc H) (.here : Var (Δ.snoc H) H) := by
  induction rest generalizing Δ with
  | empty => rfl
  | cons P rest ih =>
      simp only [pendingHeadVar, Pending.weakenCodeBase]
      rw [ih]
      exact weakenCodeBase_natural rest Rename.exchange
        (.here : Var ((Δ.snoc P.erase).snoc H) H)

theorem pushPending_entry (D : BoundOrigins R Δ) (E : PendingAssignment R ps)
    (x : PendingVar ps P) :
    (D.pushPending E).ref (PendingVar.eraseAux Δ x) = E.ref x := by
  induction ps generalizing Δ with
  | empty => nomatch x
  | cons Q rest ih =>
      cases x with
      | here =>
          rw [PendingVar.eraseAux, pendingHeadVar_eq_weakenCodeBase]
          exact pushPending_base
            (D.snoc (E.ref .here)) E.tail .here
      | there x =>
          simpa [pushPending, PendingVar.eraseAux, PendingAssignment.tail] using
            ih (D := D.snoc (E.ref .here))
              (E := E.tail) (x := x)

theorem respects_weakenCodeBase (D : BoundOrigins R Δ)
    (E : PendingAssignment R ps) :
    D.Respects (Pending.weakenCodeBase ps Δ) (D.pushPending E) :=
  D.pushPending_base E

theorem pushPending_scoped {D : BoundOrigins R Δ} (hD : D.Scoped pre)
    {E : PendingAssignment R ps} (hE : E.Scoped pre) :
    (D.pushPending E).Scoped pre := by
  induction ps generalizing Δ with
  | empty =>
      intro A x
      exact hD x
  | cons P rest ih =>
      change ((D.snoc (E.ref .here)).pushPending E.tail).Scoped pre
      exact ih (snoc_scoped hD (hE .here))
        (PendingAssignment.tail_scoped hE)

end BoundOrigins

namespace CodePendingAssignment

/-- Realize a code-pending assignment against its local binder environment. -/
def realize (D : BoundOrigins R Δ) (E : CodePendingAssignment R Δ ps) :
    PendingAssignment R ps where
  ref x := (E.ref x).realize D

@[simp] theorem realize_ref (D : BoundOrigins R Δ)
    (E : CodePendingAssignment R Δ ps) (x : PendingVar ps P) :
    (E.realize D).ref x = (E.ref x).realize D := rfl

theorem realize_boundBatch (D : BoundOrigins R Δ)
    (B : BatchResultAssignment R selected) (x : PendingVar selected P) :
    ((CodePendingAssignment.boundBatch B Δ).ref x).realize
        (D.pushPending B.resolved) = B.resolved.ref x := by
  exact D.pushPending_entry B.resolved x

theorem realize_ref_terminal (D : BoundOrigins R Δ)
    (E : CodePendingAssignment R Δ ps) (x : PendingVar ps P) :
    R.target ((E.realize D).ref x).origin.raw = none :=
  ((E.realize D).ref x).terminal

theorem realize_ref_scoped {D : BoundOrigins R Δ} (hD : D.Scoped pre)
    {E : CodePendingAssignment R Δ ps} (hE : E.Scoped pre)
    (x : PendingVar ps P) :
    pre.Contains ((E.realize D).ref x).origin.raw :=
  CanonRef.realize_scoped hD (hE x)

end CodePendingAssignment

/-! ### Boundary fixtures -/

namespace PairRealizeFixtures

open PairTraceFixtures PairOriginFixtures

abbrev TwoQCtx : Ctx TwoGenSig :=
  (Ctx.empty : Ctx TwoGenSig).snoc Q |>.snoc Q

def aliasBounds : BoundOrigins chainResolver TwoQCtx :=
  ((BoundOrigins.empty chainResolver).snoc (ResolvedRef.of chainResolver atom0)).snoc
    (ResolvedRef.of chainResolver store2)

/-- Different binders may intentionally realize to one alias representative. -/
theorem distinct_bound_indices_alias_equal :
    (CanonRef.bound (.here : Var TwoQCtx Q)).realize aliasBounds =
      (CanonRef.bound (.there .here : Var TwoQCtx Q)).realize aliasBounds := by
  change ResolvedRef.of chainResolver store2 = ResolvedRef.of chainResolver atom0
  exact PairOriginFixtures.alias_chain_collapses.1.trans
    PairOriginFixtures.alias_chain_collapses.2

def distinctBounds : BoundOrigins (AliasResolver.identity TwoGenSig) TwoQCtx :=
  ((BoundOrigins.empty _).snoc atomRef).snoc
    (ResolvedRef.of _ terminalB)

/-- Distinct terminal free/bound representatives remain distinct. -/
theorem distinct_terminal_bounds_apart :
    (CanonRef.bound (.here : Var TwoQCtx Q)).realize distinctBounds ≠
      (CanonRef.bound (.there .here : Var TwoQCtx Q)).realize distinctBounds := by
  exact Ne.symm PairOriginFixtures.distinct_terminal_same_type

/-- Lambda/sum binder extension maps `here` to the supplied source. -/
theorem snoc_here_there :
    (aliasBounds.snoc (ResolvedRef.of chainResolver store1)).ref
        (.here : Var (TwoQCtx.snoc Q) Q) = ResolvedRef.of chainResolver store1 ∧
      (aliasBounds.snoc (ResolvedRef.of chainResolver store1)).ref
        (.there .here : Var (TwoQCtx.snoc Q) Q) = aliasBounds.ref .here := by
  exact ⟨rfl, rfl⟩

abbrev TwoPending : Pending TwoGenSig := .cons AtomP (.cons AtomP .empty)

def orderedPending : PendingAssignment (AliasResolver.identity TwoGenSig) TwoPending :=
  PendingAssignment.cons atomRef
    (PendingAssignment.cons (ResolvedRef.of _ terminalB)
      (PendingAssignment.empty _))

def aliasPending : PendingAssignment chainResolver TwoPending :=
  PendingAssignment.cons (ResolvedRef.of chainResolver store2)
    (PendingAssignment.cons (ResolvedRef.of chainResolver store1)
      (PendingAssignment.empty _))

/-- Two pending entries retain their head-to-tail order under `eraseAux`. -/
theorem push_two_pending_order :
    let D := (BoundOrigins.empty (AliasResolver.identity TwoGenSig)).pushPending
      orderedPending
    D.ref (PendingVar.eraseAux (Ctx.empty : Ctx TwoGenSig)
        (.here : PendingVar TwoPending AtomP)) = atomRef ∧
      D.ref (PendingVar.eraseAux (Ctx.empty : Ctx TwoGenSig)
        (.there .here : PendingVar TwoPending AtomP)) =
          ResolvedRef.of _ terminalB ∧
      D.ref (PendingVar.eraseAux (Ctx.empty : Ctx TwoGenSig)
        (.here : PendingVar TwoPending AtomP)) ≠
        D.ref (PendingVar.eraseAux (Ctx.empty : Ctx TwoGenSig)
          (.there .here : PendingVar TwoPending AtomP)) := by
  dsimp only
  constructor
  · apply BoundOrigins.pushPending_entry
  · constructor
    · apply BoundOrigins.pushPending_entry
    · rw [BoundOrigins.pushPending_entry, BoundOrigins.pushPending_entry]
      exact PairOriginFixtures.distinct_terminal_same_type

/-- Alias chains remain normalized after passage through pending binders. -/
theorem push_pending_alias_chain_collapses :
    let D := (BoundOrigins.empty chainResolver).pushPending aliasPending
    D.ref (PendingVar.eraseAux (Ctx.empty : Ctx TwoGenSig)
        (.here : PendingVar TwoPending AtomP)) =
      D.ref (PendingVar.eraseAux (Ctx.empty : Ctx TwoGenSig)
        (.there .here : PendingVar TwoPending AtomP)) := by
  dsimp only
  rw [BoundOrigins.pushPending_entry, BoundOrigins.pushPending_entry]
  exact PairOriginFixtures.alias_chain_collapses.1

def twoBatch : BatchResultAssignment chainResolver TwoPending where
  origin := by
    intro P x
    cases x with
    | here => exact store2
    | there x =>
        cases x with
        | here => exact store1
        | there x => nomatch x

/-- `boundBatch` is realized by the same ordered pending assignment. -/
theorem boundBatch_realizes_results (x : PendingVar TwoPending AtomP) :
    ((CodePendingAssignment.boundBatch twoBatch (Ctx.empty : Ctx TwoGenSig)).ref x).realize
        ((BoundOrigins.empty chainResolver).pushPending twoBatch.resolved) =
      twoBatch.resolved.ref x := by
  apply CodePendingAssignment.realize_boundBatch

end PairRealizeFixtures

end Gimbal.Equality.Scherer
