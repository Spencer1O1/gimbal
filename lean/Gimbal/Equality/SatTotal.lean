/-
  Saturation never runs out of fuel.

  `applyPairObsGo` consumes one schedule entry per two units of fuel: one to
  enter the entry, one to apply the observation it names. So the numeric bound
  is not a semantic parameter at all — any budget above twice the length of the
  schedule behaves identically, and the `exhausted` result is unreachable there.
  That is what lets the reference comparator treat exhaustion as an operational
  failure rather than an answer.

  `invariantFailure` is a different obligation. Split by path:

  * **Retained ordered-code / EncodeIx reference path blockers:**
    `reconstructWitness = none`, reconstructed type mismatch, and inconsistent
    `neuOfType … .never = none`. These are the 8D reconstruction-totality gate
    (`ReconstructTotal.lean`); blocked on a missing discovery-rank field.
  * **Deferred `compareSatRec` only:** `checkOldInvariant` / old-only exact
    checks. These must not be treated as blockers for the retained ordered-code
    path once reconstruction totality closes.
-/

import Gimbal.Equality.Reference

namespace Gimbal
namespace Equality

variable {sig : Signature}

/--
Applying one observation, and applying a whole schedule, cannot exhaust a
budget that covers two units per entry.
-/
theorem applyObs_ne_exhausted : ∀ fuel : Nat,
    (∀ (σ : ReachState sig.nBases) (hyps : Array (Object sig.nBases))
        (P : Object sig.nBases) (nP : NegNeu (Ctx.ofHyps hyps) P)
        (rest : List (PairEntry sig hyps)) {A : Object sig.nBases}
        (cont : InvTm (Ctx.ofHyps hyps) A),
        2 * rest.length + 1 < fuel →
        applyObsNeu fuel σ hyps P nP rest cont ≠ .exhausted) ∧
    (∀ (σ : ReachState sig.nBases) (hyps : Array (Object sig.nBases))
        (entries : List (PairEntry sig hyps)) {A : Object sig.nBases}
        (cont : InvTm (Ctx.ofHyps hyps) A),
        2 * entries.length < fuel →
        applyPairObsGo fuel σ hyps entries cont ≠ .exhausted)
  | 0 => by constructor <;> intros <;> omega
  | fuel + 1 => by
      obtain ⟨ihObs, ihGo⟩ := applyObs_ne_exhausted fuel
      constructor
      · intro σ hyps P nP rest A cont hlen
        rw [applyObsNeu.eq_def]
        dsimp only
        split
        · simp
        · -- the observation splits the schedule but never lengthens it
          have hgo : ∀ (hyps' : Array (Object sig.nBases))
              (l : List (PairEntry sig hyps')) {B : Object sig.nBases}
              (c : InvTm (Ctx.ofHyps hyps') B), l.length = rest.length →
              applyPairObsGo fuel σ hyps' l c ≠ .exhausted := by
            intro hyps' l B c hl
            exact ihGo σ hyps' l c (by omega)
          split <;> split <;>
            first
              | (rename_i h; exact absurd h (hgo _ _ _ (by simp)))
              | (rename_i h _; exact absurd h (hgo _ _ _ (by simp)))
              | simp
      · intro σ hyps entries A cont hlen
        rw [applyPairObsGo.eq_def]
        dsimp only
        cases entries with
        | nil => simp
        | cons e rest =>
          have hlen' : 2 * rest.length + 1 < fuel := by
            simp only [List.length_cons] at hlen; omega
          dsimp only
          cases e with
          | consistency P w =>
            dsimp only
            split
            · simp
            · split
              · exact ihObs σ hyps _ _ rest cont hlen'
              · simp
          | exact P n => exact ihObs σ hyps _ _ rest cont hlen'

/-- The schedule application in the reference pipeline never reports exhaustion. -/
theorem applyPairObs_ne_exhausted (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (entries : Array (PairEntry sig hyps))
    {A : Object sig.nBases} (cont : InvTm (Ctx.ofHyps hyps) A)
    (hfuel : 2 * entries.size < fuel) :
    applyPairObs fuel σ hyps entries cont ≠ .exhausted := by
  rw [applyPairObs]
  split
  · split <;> simp
  · exact (applyObs_ne_exhausted fuel).2 σ hyps entries.toList cont (by simpa using hfuel)

/--
The saturation stage of the reference comparator is exhaustion-free by
construction: it is called with `saturationBudget`, which always covers the
schedule it is handed.
-/
theorem applyPairObs_saturationBudget_ne_exhausted (fuel : Nat)
    (σ : ReachState sig.nBases) (hyps : Array (Object sig.nBases))
    (entries : Array (PairEntry sig hyps)) {A : Object sig.nBases}
    (cont : InvTm (Ctx.ofHyps hyps) A) :
    applyPairObs (saturationBudget fuel entries.size) σ hyps entries cont
      ≠ .exhausted :=
  applyPairObs_ne_exhausted _ σ hyps entries cont (lt_saturationBudget fuel entries.size)

end Equality
end Gimbal
