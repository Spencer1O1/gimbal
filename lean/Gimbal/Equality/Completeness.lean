/-
  Theorem interfaces for the remaining Milestone 8 completeness obligations.

  Soundness of the reference comparator is proved (`defEq_of_referenceCompare`).
  Completeness is retargeted to ordered-phase codes (design E):

      ICCEq t u ↔ encodeICC ε t = encodeICC ε u

  once encode is total on the saturated well-focused fragment. The old
  `canonicalize`-based unique-NF path is frozen; do not extend `NegNeu.blt`
  orientation or re-canonicalize after exchange.

  WIP placeholders that must be discharged before claiming M8 complete are
  listed as goal Props below (`OriginCollisionFree`, `EncodeTotal`,
  `ReferenceCompareTotal`, `DefEqDecidable`). Do not paper over them with
  `Origin.obs 0`, reused `.split (.hyp 0)`, quantifying completeness over
  arbitrary fuel, or baking `2048` into decidability.
-/

import Gimbal.Equality.ICCCanon
import Gimbal.Equality.ICCCode
import Gimbal.Equality.ICCEncode
import Gimbal.Equality.ICCIdem
import Gimbal.Equality.ICCPeel
import Gimbal.Equality.Reference
import Gimbal.Equality.ReferenceSound

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### ICC completeness via codes (design E) -/

/-- Primary characterization — see also `IccEqIffEncodeEqGoal` in `ICCCode`. -/
abbrev ICCCompleteness : Prop := IccEqIffEncodeEqGoal (sig := sig)

/-- Generator-wise code invariance. -/
abbrev EncodeIccInvariant : Prop := EncodeIccInvariantGoal (sig := sig)

/-- Legacy InvTm-canonicalizer completeness (frozen; not the active target). -/
def CanonicalizeIffIccEq : Prop :=
  ∀ {Γ : Ctx sig} {A : Object sig.nBases} (t u : InvTm Γ A),
    ICCEq t u ↔ canonicalize t = canonicalize u

/-! ### Origin collision-freedom -/

/--
Every processable binder and scheduled observation receives a stable,
collision-free `Origin`.

API discharge (design E):

* `encodeFocGo` assigns `Origin.obs obsSlot` and increments the slot
* λ-domain binders use `Origin.dom domNest` (encode and peel-through-λ)
* case payloads keep `.split parent side`

Remaining: a formal injectivity / non-collision theorem for a well-formed
phase-entry environment (distinct binders ⇒ distinct origins under weaken).
The Prop marks that obligation; do not reintroduce constant `obs 0` or
reused `.split (.hyp 0) false` for unrelated λ binders.
-/
def OriginCollisionFree : Prop := True

/-! ### Totality of encode (no correctness-critical fuel) -/

/--
`encodeICC` must succeed on every well-focused saturated invertible term under
a well-formed phase-entry origin environment.

The present `encodeICCGo` recursion is bounded by candidate `encodeMeasure`.
That bound is a proof device, not a semantic parameter: either

* prove adequacy (`encodeMeasure` never hits zero on legal peels), then erase
  the fuel in favour of well-founded recursion on the measure; or
* refactor to structural/WF recursion over worklist + goal weight directly.

`none` from fuel exhaustion must not appear in the proof-critical path.
-/
def EncodeTotal : Prop :=
  ∀ {Γ : Ctx sig} {A : Object sig.nBases} (ε : OriginEnv Γ) (t : InvTm Γ A),
    -- eventual statement restricts to WellInv / saturated phase-entry ε
    (encodeICC ε t).isSome

/-! ### Reference completeness and decidability (fuel-free) -/

/--
Whether a candidate result is resource exhaustion (any stage).
-/
def CandidateResult.isExhausted : CandidateResult → Bool
  | .exhausted _ => true
  | _ => false

/--
Completeness for the **total** reference comparator.

Do **not** state this as `∀ fuel, DefEq → referenceCompare … fuel = .equal`:
fuel `0` is exhaustion (fixture `fuelZeroIsExhausted`), so quantifying over
arbitrary fuel makes completeness false and invites a fake `2048` bound.

The final API should be an unfueled (or measure-proved) function
`referenceCompare f g : CandidateResult` with no exhaustion branch reachable
on well-formed inputs. Until that lands, this obligation stays open.
-/
def ReferenceCompareComplete : Prop :=
  ∀ {X Y : Object sig.nBases} (f g : IntrinsicMorphism sig X Y),
    IntrinsicDefEq f g →
      -- placeholder: replace body with `referenceCompareTotal f g = .equal`
      True

/-- Full M8 equivalence for the total comparator (no fuel parameter). -/
def ReferenceCompareIffDefEq : Prop :=
  ∀ {X Y : Object sig.nBases} (f g : IntrinsicMorphism sig X Y),
    -- placeholder until `referenceCompare` is total:
    -- `referenceCompareTotal f g = .equal ↔ IntrinsicDefEq f g`
    True

/--
The final reference comparator is total on intrinsic morphisms: it returns
`.equal` or `.different` (or a non-resource invariant failure), never
`.exhausted`, without a caller-supplied fuel budget.
-/
def ReferenceCompareTotal : Prop :=
  ∀ {X Y : Object sig.nBases} (f g : IntrinsicMorphism sig X Y),
    -- placeholder: `¬ (referenceCompareTotal f g).isExhausted`
    True

/-- Lives in `Type` because `Decidable` does. -/
def DefEqDecidable : Type :=
  ∀ {X Y : Object sig.nBases} (f g : IntrinsicMorphism sig X Y),
    Decidable (IntrinsicDefEq f g)

/--
Package decidability from a proved total equivalence.

**Forbidden:** `decidable_of_iff _ (h f g 2048)` — a fixed fuel is not a
completeness bound (handoff: “A fixed fuel such as `2048` cannot be justified
as a completeness bound”). Decidability must use the total comparator (or an
equivalent measure-bounded procedure with a proved adequate bound).
-/
def DefEqDecidableFromTotal : Prop :=
  ReferenceCompareTotal (sig := sig) →
    ReferenceCompareIffDefEq (sig := sig) →
    Nonempty (DefEqDecidable (sig := sig))

/-! ### Dependency summary

Active path: collision-free `Origin` → worklist `forcedRule` → total `encodeICC`
→ code equality → total `referenceCompare` → `Decidable DefEq`.

Blocked / WIP:

1. ~~Peel soundness (`peelCaseOuter_icc`)~~ **Done** (`ICCPeel`)
2. ~~`OriginCollisionFree` API~~ **Done** (`Origin.dom` + `obsSlot`/`domNest`);
   formal injectivity theorem still open
3. `EncodeTotal` / measure adequacy — no proof-critical fuel exhaustion
4. `EncodeIccInvariant` / rigidity / `ICCCompleteness` (uses peel soundness)
5. `ReferenceCompareTotal` + iff — erase `2048` from decidability
6. 8G packaging

Fallback if ordered-phase reification proves infeasible: `decideICCEq`, not a
return to the unsourced local rewrite loop.
-/

end Equality
end Gimbal
