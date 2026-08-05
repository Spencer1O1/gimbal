/-
  Reordering and repeating observations.

  The schedule is operational metadata: it steers which strong positive cuts
  are made, but it is not part of the answer. This module makes that precise in
  the two ways the pipeline depends on.

  Admissibility only reads the *set* of entries, so it survives permutation,
  repetition, and any rearrangement that invents nothing. Meaning does not
  depend on the schedule at all: every application of every schedule returns a
  term with the meaning of the continuation it was handed, so two schedules
  applied to one continuation always agree.

  Note on the ICC class: the corresponding *syntactic* claim is false, and
  deliberately so. Two observations bound in the opposite order give genuinely
  different `letPos` nesting, and repeating an observation leaves a vacuous
  binder behind, because the second abstraction finds no occurrences left to
  replace. `ICCEq` has neither a `letPos` exchange rule nor a rule discarding an
  unused binder, and adding them would enlarge the relation the canonicalizer
  has to be complete for. What the comparator actually relies on is weaker and
  is supplied by construction: both inputs are saturated under one shared
  schedule, and `canonicalizeFoc` drops the schedule annotation before any
  structural comparison.
-/

import Gimbal.Equality.SatPreserve
import Gimbal.Equality.SatWell

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Admissibility depends only on the set of entries -/

/-- A schedule that invents no entry inherits admissibility. -/
theorem wellEntries_of_subset {hyps : Array (Object sig.nBases)}
    {es fs : List (PairEntry sig hyps)} (hsub : ∀ e ∈ fs, e ∈ es)
    (h : WellEntries es) : WellEntries fs :=
  fun e he => h e (hsub e he)

/-- Reordering a schedule keeps it admissible. -/
theorem wellEntries_perm {hyps : Array (Object sig.nBases)}
    {es fs : List (PairEntry sig hyps)} (hp : es.Perm fs) (h : WellEntries es) :
    WellEntries fs :=
  wellEntries_of_subset (fun _ he => hp.mem_iff.2 he) h

/-- Repeating entries keeps a schedule admissible. -/
theorem wellEntries_dup {hyps : Array (Object sig.nBases)}
    {es : List (PairEntry sig hyps)} (h : WellEntries es) :
    WellEntries (es ++ es) :=
  wellEntries_append h h

/-- Dropping entries keeps a schedule admissible. -/
theorem wellEntries_sublist {hyps : Array (Object sig.nBases)}
    {es fs : List (PairEntry sig hyps)} (hsub : fs.Sublist es)
    (h : WellEntries es) : WellEntries fs :=
  wellEntries_of_subset (fun _ he => hsub.mem he) h

/-- Filtering a schedule keeps it admissible. -/
theorem wellEntries_filter {hyps : Array (Object sig.nBases)}
    {es : List (PairEntry sig hyps)} (p : PairEntry sig hyps → Bool)
    (h : WellEntries es) : WellEntries (es.filter p) :=
  wellEntries_of_subset (fun _ he => List.mem_of_mem_filter he) h

/-! ### Meaning does not depend on the schedule -/

/--
Two schedules applied to one continuation produce terms with the same meaning.

Nothing relates the schedules: each application separately preserves the
meaning of the continuation, so they meet in the middle. Permutation and
repetition are the special cases the saturation calculus needs.
-/
theorem tmEq_applyPairObs_congr {fuel₁ fuel₂ : Nat}
    {σ₁ : ReachState sig.nBases} {cert₁ : ReachRankCert σ₁}
    {σ₂ : ReachState sig.nBases} {cert₂ : ReachRankCert σ₂}
    {hyps : Array (Object sig.nBases)}
    {entries₁ entries₂ : Array (PairEntry sig hyps)} {A : Object sig.nBases}
    {cont t₁ t₂ : InvTm (Ctx.ofHyps hyps) A}
    (h₁ : applyPairObs fuel₁ cert₁ hyps entries₁ cont = .ok t₁)
    (h₂ : applyPairObs fuel₂ cert₂ hyps entries₂ cont = .ok t₂) :
    TmEq t₁.erase t₂.erase :=
  (tmEq_applyPairObs _ _ _ _ h₁).trans (tmEq_applyPairObs _ _ _ _ h₂).symm

/-- Permuting the schedule does not change the meaning of the saturated form. -/
theorem tmEq_applyPairObs_perm {fuel : Nat} {σ : ReachState sig.nBases}
    {cert : ReachRankCert σ} {hyps : Array (Object sig.nBases)}
    {entries₁ entries₂ : Array (PairEntry sig hyps)} {A : Object sig.nBases}
    {cont t₁ t₂ : InvTm (Ctx.ofHyps hyps) A}
    (_hp : entries₁.toList.Perm entries₂.toList)
    (h₁ : applyPairObs fuel cert hyps entries₁ cont = .ok t₁)
    (h₂ : applyPairObs fuel cert hyps entries₂ cont = .ok t₂) :
    TmEq t₁.erase t₂.erase :=
  tmEq_applyPairObs_congr h₁ h₂

/-- Repeating an observation does not change the meaning of the saturated form. -/
theorem tmEq_applyPairObs_dup {fuel : Nat} {σ : ReachState sig.nBases}
    {cert : ReachRankCert σ} {hyps : Array (Object sig.nBases)}
    {entries : Array (PairEntry sig hyps)}
    {A : Object sig.nBases} {cont t₁ t₂ : InvTm (Ctx.ofHyps hyps) A}
    (h₁ : applyPairObs fuel cert hyps entries cont = .ok t₁)
    (h₂ : applyPairObs fuel cert hyps (entries ++ entries) cont = .ok t₂) :
    TmEq t₁.erase t₂.erase :=
  tmEq_applyPairObs_congr h₁ h₂

/--
Reordering an admissible schedule is inert: the saturated form is still well
focused and still means what the continuation meant.
-/
theorem applyPairObs_perm_ok {fuel : Nat} {σ : ReachState sig.nBases}
    {cert : ReachRankCert σ} {hyps : Array (Object sig.nBases)}
    {entries₁ entries₂ : Array (PairEntry sig hyps)} {A : Object sig.nBases}
    {cont t₁ t₂ : InvTm (Ctx.ofHyps hyps) A}
    (hp : entries₁.toList.Perm entries₂.toList)
    (hentries : WellEntries entries₁.toList) (hcont : WellInv cont)
    (h₁ : applyPairObs fuel cert hyps entries₁ cont = .ok t₁)
    (h₂ : applyPairObs fuel cert hyps entries₂ cont = .ok t₂) :
    WellInv t₁ ∧ WellInv t₂ ∧ TmEq t₁.erase t₂.erase :=
  ⟨wellInv_applyPairObs _ _ _ _ hentries hcont h₁,
    wellInv_applyPairObs _ _ _ _ (wellEntries_perm hp hentries) hcont h₂,
    tmEq_applyPairObs_congr h₁ h₂⟩

/-- Repeating observations is inert in the same sense. -/
theorem applyPairObs_dup_ok {fuel : Nat} {σ : ReachState sig.nBases}
    {cert : ReachRankCert σ} {hyps : Array (Object sig.nBases)}
    {entries : Array (PairEntry sig hyps)}
    {A : Object sig.nBases} {cont t₁ t₂ : InvTm (Ctx.ofHyps hyps) A}
    (hentries : WellEntries entries.toList) (hcont : WellInv cont)
    (h₁ : applyPairObs fuel cert hyps entries cont = .ok t₁)
    (h₂ : applyPairObs fuel cert hyps (entries ++ entries) cont = .ok t₂) :
    WellInv t₁ ∧ WellInv t₂ ∧ TmEq t₁.erase t₂.erase := by
  refine ⟨wellInv_applyPairObs _ _ _ _ hentries hcont h₁, ?_,
    tmEq_applyPairObs_congr h₁ h₂⟩
  refine wellInv_applyPairObs _ _ _ _ ?_ hcont h₂
  simpa using wellEntries_dup hentries

/-! ### Duplication is already removed from the pair schedule

Exact demands are inserted up to observation identity, so a demand collected
twice — by both inputs, or twice inside one input — contributes one entry. This
is the syntactic half of duplication-inertness, and it is what keeps the shared
schedule independent of which side an observation came from.
-/

theorem memI_unionExact_self_iff {Γ : Ctx sig} (a : Array (Exact Γ)) (e : Exact Γ) :
    MemI (unionExact a a) e ↔ MemI a e :=
  unionExact_idem a e

/-- The shared schedule sees the same demands whichever way the pair is given. -/
theorem memI_pairSelection_symm
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t u : InvTm (Ctx.ofHyps hyps) A) (e : Exact (Ctx.ofHyps hyps)) :
    MemI (unionExact (collectExact t) (collectExact u)) e ↔
      MemI (unionExact (collectExact u) (collectExact t)) e :=
  unionExact_comm _ _ e

end Equality
end Gimbal
