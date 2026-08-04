/-
  8D reconstruction-totality gate.

  Typing of successful reconstruction is already proved
  (`wellNeg_reconstructWitness` / `wellNeg_neuOfType`). This module states the
  *totality* obligation for stored witnesses in a completed reachability state,
  audits every `reconstructGo` recursive edge, and records why well-founded
  recursion is blocked until a discovery-rank / parent-DAG package exists.

  **Gate status: BLOCKED — missing provenance rank.**
  Do not feed an `Option`-propagating reachability adapter into EncodeTotal
  until this gate closes.
-/

import Gimbal.Equality.ReachComplete
import Gimbal.Equality.ReachSound
import Gimbal.Equality.Saturation
import Gimbal.Equality.SatTotal

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ## Failure accounting (retained ordered-code path)

| Source | Blocks retained EncodeIx / ordered-code reference? |
|---|---|
| `reconstructWitness = none` | **Yes** — genuine reference-path blocker |
| reconstructed type `P' ≠ P` | **Yes** — genuine reference-path blocker |
| inconsistent `neuOfType … .never = none` | **Yes** — genuine reference-path blocker |
| `checkOldInvariant` / `exactsAllUseNew` | **No** — deferred `compareSatRec` only; not on the retained ordered-code path |

`SatTotal` discharges schedule **exhaustion** only. Reconstruction failures remain
open here; old-invariant failure must not be treated as a retained-path blocker.
-/

/-! ## Recursive edges of `reconstructGo`

Worker: `Saturation.reconstructGo`. Wrappers: `neuOfType` → `.neuOf`,
`reconstructWitness` → `.witness`. Every call decrements fuel by 1; fuel is the
**only** decrease present in the implementation.

### `.neuOf hyps A`
* `findHypVar` hit → `.var` (terminal).
* else `σ.findTypeIdx A` / `getCell.witness` → recurse `.witness hyps w`.

### `.witness hyps w`
* `.ctxVar hypIdx` → `Ctx.varOldest` (terminal).
* `.fst` / `.snd pIdx` → `σ.typeAt pIdx` (expect prod) → `.neuOf hyps (.prod L R)`
  (**type size increases** toward the parent product).
* `.app fnHypIdx argIdx` → hyps + `σ.typeAt argIdx` → `.invOf hyps Arg`.
* `.appTy fnTypeIdx argIdx` → `σ.typeAt` → `.neuOf hyps (.exp …)` and `.invOf hyps Arg`.
* `.unit` / `.inl` / `.inr` / `.eta` → always `none` (intro forms; not neutrals).

### `.invOf hyps A`
* prefer `.neuOf hyps A`, else:
  * `.unit` terminal; `.prod` / `.coprod` → `.invOf` on components (`objectSize` ↓);
  * `.exp` → `.invOf (hyps.push Arg) Ret` (`objectSize Ret` ↓).

**Structural decrease that works locally:** `objectSize` on intro `invOf` splits.
**Structural decrease that fails on witness→parent edges:** type size goes *up*
to the parent connective. Termination of those edges needs a rank on the
**stored witness graph** (discovery generation or proved parent-DAG path length).
-/

/-! ## Fixed-point invariant required (not yet proved as a reconstruction package)

For a completed `runReachability Γ goal` state `σ` (`runReachability_fixed`,
`runReachability_sound`), every *stored* witness used by reconstruction must
satisfy:

1. **Index range:** every `hypIdx` / `ofTypeIdx` / `fnTypeIdx` / `argTypeIdx` in
   `w` is in range for `Γ.hyps` / `σ.types`.
2. **Parent deducible:** every parent cell referred to by `w` is simply
   deducible (or retrievable) in `σ`.
3. **Type match:** witness shape matches the owning / requested cell type
   (e.g. `.fst i` only if `typeAt i = some (.prod …)`; reconstructed head type
   equals the cell / schedule entry type).
4. **Well-founded dependencies:** the parent-pointer graph on cells is
   well-founded (acyclic with a finite rank).

Existing theorems give `ReachFixed` / `ReachSound` / sized tables / subformula
closure. They do **not** yet package (1)–(4) for `reconstructGo`.
-/

/-! ## Missing provenance / rank field

`Witness` carries untyped parent indices only (`Reachability.lean`).
`ReachCell` stores `retrievable` / `oldWitness` / `newWitness` — first discovery
is operational (`record` keeps the first witness) but **no `discoverGen : Nat`**
(or equivalent) is retained.

Without an explicit generation (or a proved longest-path measure on the parent
DAG derived from the discover rules), witness→parent edges have **no** semantic
decrease: `objectSize` increases, and fuel is not an invariant of the state.

**Gate decision:** stop. Do not attempt well-founded `reconstructGo` on the
current layout. Preferred sticky fix: record `discoverGen` at `discover` /
`markHyp` time with the invariant that every parent index has strictly smaller
gen and a simply-deducible cell of the expected shape. Alternative: prove
parent-DAG acyclicity + path-length from the rule set without a stored field
(larger sticky obligation; same conceptual gap).
-/

/-! ## Corrected totality statement (open)

The previous `ReconstructWitnessTotal` in `ICCEncodeScheduleIx` quantified over
all fuel (including 0), all states, and all witnesses (including intro forms that
always fail). That Prop is uninhabited and is replaced by the scoped form below.
-/

/--
A stored neutral witness reconstructs at its owning cell type under matching
hyps, for some fuel (to be replaced by well-founded recursion once a rank
exists).
-/
def StoredWitnessReconstructs (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (i : Nat) (w : Witness) : Prop :=
  ∃ (A : Object sig.nBases) (n : NegNeu (Ctx.ofHyps (sig := sig) hyps) A),
    σ.typeAt i = some A ∧
      Witness.isNeutral w = true ∧
      ∃ fuel, reconstructWitness (sig := sig) fuel σ hyps w = some ⟨A, n⟩

/--
8D gate (open / blocked on discovery rank): every stored *neutral* witness in a
completed reachability state reconstructs at its cell type under `Γ.hyps`.
-/
def ReconstructWitnessTotal (sig : Signature) : Prop :=
  ∀ (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases),
    let σ := runReachability (n := sig.nBases) Γ goal
    ∀ (i : Nat) (w : Witness),
      i < σ.cells.size →
        ((σ.getCell i).oldWitness = some w ∨ (σ.getCell i).newWitness = some w) →
          Witness.isNeutral w = true →
            StoredWitnessReconstructs (sig := sig) σ Γ.hyps i w

/-- Schedule consistency entries reconstruct at the declared type. -/
def ConsistencyWitnessTotal (sig : Signature) : Prop :=
  ∀ (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases),
    let σ := runReachability (n := sig.nBases) Γ goal
    ∀ (P : Object sig.nBases) (w : Witness),
      (buildSchedule σ).entries.any (fun e => e.1 == P && e.2 == w) = true →
        ∃ (n : NegNeu (Ctx.ofHyps (sig := sig) Γ.hyps) P) (fuel : Nat),
          reconstructWitness (sig := sig) fuel σ Γ.hyps w = some ⟨P, n⟩

/-- Inconsistent completed states supply a reconstructable `.never` neutral. -/
def InconsistentNeverTotal (sig : Signature) : Prop :=
  ∀ (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases),
    let σ := runReachability (n := sig.nBases) Γ goal
    σ.inconsistent = true →
      ∃ (n : NegNeu (Ctx.ofHyps (sig := sig) Γ.hyps) .never) (fuel : Nat),
        neuOfType (sig := sig) fuel σ Γ.hyps .never = some n

/--
Derived package once `ReconstructWitnessTotal` / `InconsistentNeverTotal` close:
consistency witnesses succeed at the declared type; inconsistent `neuOfType`
cannot return `none` on valid completed states. Correctness
(`wellNeg_reconstructWitness`) stays separate — reuse after existence.
-/
def ReconstructTotalityPackage (sig : Signature) : Prop :=
  ReconstructWitnessTotal sig ∧
    ConsistencyWitnessTotal sig ∧
    InconsistentNeverTotal sig

/-! ## Status

* **Correctness (success ⇒ WellNeg):** proved (`wellNeg_reconstructWitness`).
* **Totality (existence):** blocked — missing `discoverGen` / parent-DAG rank.
* **Fuel:** implementation artifact; not an invariant of `σ`. Replace with WF
  recursion after the rank lands; a derived finite bound is acceptable only if
  proved from the state invariant (no fixed constant).
* **Next:** add discovery rank (or prove parent-DAG WF), then prove
  `ReconstructTotalityPackage`, then make the reachability adapter total and
  feed EncodeTotal.
-/

end Equality
end Gimbal
