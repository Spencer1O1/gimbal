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
import Gimbal.Equality.ICCFragment
import Gimbal.Equality.ICCTotal
import Gimbal.Equality.ICCReflect
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

/--
Every ICC conversion is an `EncodeIccStep` under the phase-entry origin
environment: domain preserved both ways, and codes agree if either endpoint
encodes.

`ValidEncodeFragment` is **not** required on `ICCEq.trans` intermediates
(reference provenance need not survive ICC rearrangement). Use
`ValidEncodeFragment` only via `EncodeTotal` to obtain an initial
`EncodableICC`; then propagate encodability and code equality through
`EncodeIccStep` (see `EncodeIccStep.trans`).
-/
def EncodeIccInvariantGoal : Prop :=
  ∀ {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    {t u : InvTm (Ctx.ofHyps hyps) A},
    ICCEq t u → EncodeIccStep (OriginEnv.ofHyps hyps) t u

/-- Generator-wise code invariance (`EncodeIccStep`: domain both ways). -/
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
`encodeICC` must succeed on every term in the **valid fragment**, returning a
concrete code witness (prefer `∃ c, … = some c` over bare `isSome`).

It is not required for arbitrary `InvTm`. The candidate adequate bound is
`encodeFuel` (measure + `posPushBudget` + `2 * InvTm.size`); the runner still
uses `encodeMeasure` until fuel mono lifts commute across unequal sizes.
Positive `letPos` is why measure alone is insufficient. Fuel exhaustion must
not appear on the proof-critical path.
-/
def EncodeTotal : Prop :=
  ∀ {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A),
    ValidEncodeFragment t →
      ∃ c, encodeICC (OriginEnv.ofHyps hyps) t = some c

/--
`EncodeTotal` from readiness of every valid-fragment term under `ofHyps`.

`EncodableICC.of_encodeReady` / `encodeReady_go_some` discharge the
computational half. The remaining obligation is inhabiting `EncodeReady`
from `ValidEncodeFragment` (peel/left-η alignment for every positive
worklist head under `OriginEnv.ofHyps`).
-/
theorem EncodeTotal_of_ready
    (hready : ∀ {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
      (t : InvTm (Ctx.ofHyps hyps) A),
      ValidEncodeFragment t →
        EncodeReady (OriginEnv.posWorklist (OriginEnv.ofHyps hyps))
          (OriginEnv.ofHyps hyps) 0 0 t) :
    EncodeTotal (sig := sig) := by
  intro hyps A t hv
  exact encode_of_encodeReady (OriginEnv.ofHyps hyps)
    (OriginEnv.posWorklist (OriginEnv.ofHyps hyps)) rfl (hready t hv)

/--
**Provisional** `EncodeTotal`: projects the stashed `ValidEncodeFragment.ready`
field. Logically valid, but not semantic totality — readiness must still be
derived by `RawReferenceProduced → PhaseEncodeReady` /
`certifyReferenceProduced`. Do **not** use this to switch `referenceCompare`,
prove characterization, or drop failure cases.
-/
theorem EncodeTotal_holds_provisional : EncodeTotal (sig := sig) :=
  EncodeTotal_of_ready fun {_hyps} {_A} _t hv => encodeReady_of_validEncodeFragment hv

/-- Historical name for the provisional theorem; prefer `EncodeTotal_holds_provisional`. -/
abbrev EncodeTotal_holds : EncodeTotal (sig := sig) := EncodeTotal_holds_provisional

/-- Reflection / common-code soundness (design-E rigidity). -/
abbrev EncodeIccReflect : Prop := EncodeIccReflectGoal (sig := sig)

/-- Alias: rigidity means reflection, not encoder determinism alone. -/
abbrev EncodeIccRigidity : Prop := EncodeIccRigidityGoal (sig := sig)

/--
If invariance (on `ofHyps` phase-entry envs) and reflection both hold, the
characterization holds for those environments. Reflection is stated for
arbitrary `OriginEnv`; invariance is the `ofHyps` fragment used by the
reference pipeline.
-/
theorem iccEq_iff_encode_eq_of_inv_reflect
    (hInv : EncodeIccInvariantGoal (sig := sig))
    (hRefl : EncodeIccReflectGoal (sig := sig)) :
    ∀ {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
      (t u : InvTm (Ctx.ofHyps hyps) A),
      EncodableICC (OriginEnv.ofHyps hyps) t →
      EncodableICC (OriginEnv.ofHyps hyps) u →
        (ICCEq t u ↔
          encodeICC (OriginEnv.ofHyps hyps) t =
            encodeICC (OriginEnv.ofHyps hyps) u) := by
  intro hyps A t u ht hu
  constructor
  · intro heq
    exact (hInv heq).2 ht
  · intro hcode
    obtain ⟨c, hc⟩ := EncodableICC.exists ht
    have hu' : encodeICC (OriginEnv.ofHyps hyps) u = some c := hcode ▸ hc
    exact hRefl (OriginEnv.ofHyps hyps) hc hu'

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

1. ~~Peel soundness (`peelCaseOuter_icc`)~~ **Done** (`ICCPeel`); peel digs under
   `.foc (.sat …)` / `.foc (.letPos …)` so hyp left-coprod can surface despite
   `Origin.cmp` ordering hyp < obs while `applyPairObs` nests atom obs outer
2. ~~`OriginCollisionFree` API~~ **Done** (`Origin.dom` + `obsSlot`/`domNest`);
   formal injectivity theorem still open
3. `EncodeTotal` — **provisional only** (`EncodeTotal_holds_provisional` projects
   stashed `ValidEncodeFragment.ready`). Required bridge:
   `RawReferenceProduced → PhaseEncodeReady` (equivalently raw →
   `CertifiedReferenceProduced`). Do not switch `referenceCompare` or claim
   characterization until the stash is eliminated. WIP: `encodeReady_applyPairObs`
   (~~ofHyps_push~~ / ~~peel rekey~~ / ~~full `encodeReady_rekeyHypToObs`~~ /
   ~~leftCoprod under letPos via push-body ready~~ /
   ~~coprod obs outer `case` (var) packaging~~ /
   ~~branch schedule algebra (`rekeyHypToSplit`,
   `posWorklist_rekey_weaken_hyp_to_split`, `pushPos_cons_of_blt_head`,
   `leftCoprod_branch_schedule_gap` → `e :: leftCoprodBranchWs`)~~ /
   ~~branch EncodeReady unit/foc under `leftCoprodBranchWs`
   (`encodeReady_unit_leftCoprodBranch`, `*_cast_unit`)~~ /
   ~~base-only pair/lam/sat under branch schedule
   (`encodeReady_pair/lam/foc_sat_leftCoprodBranch`)~~ /
   ~~partial enlarged with bases-only unit cast arm~~ /
   ~~narrow raw→ready slices (`encodeReady_of_rawReferenceProduced_unit_nil`,
   `*_foc_pos_bases`)~~ /
   ~~never-payload branch abort (`encodeReady_abort_leftCoprodBranch_never`)~~ /
   ~~nested-coprod unit-η/peel under branch schedule
   (`encodeReady_unit_leftCoprodBranch_nested`, `*_case_here_*`)~~ /
   ~~`EncodeReadyRawCase` + `certifyReferenceProduced_of_EncodeReadyRawCase`~~ /
   ~~exact-never / exactNeverOnly / atom-nil-rest Go steps~~ /
   ~~restricted Raw→ready `EncodeReadyOfRawGoal_emptyOrExactNever_holds`~~ /
   ~~atom+coprod nil-rest Go inversion (`*_nil_rest_ok_inv`, `*_of_go`)~~ /
   ~~enlarged restricted Raw→ready
   `EncodeReadyOfRawGoal_emptyNeverOrNilRestObs_holds`~~ /
   ~~derived nil-rest push/branch readiness (foc-done / sat / base-letPos atom,
   unit + foc-done/sat `CoprodDerivedBranchShape` coprod-var)
   `EncodeReadyOfRawGoal_emptyNeverOrDerivedNilRest_holds`~~ /
   ~~empty-schedule WellInv intro→ready (no stash) + combined Raw fragment
   `EncodeReadyOfRawGoal_emptyWellInvIntroOrDerived_holds`~~ /
   ~~empty-schedule unit/foc-done shapes~~ landed; same-term
   `encodeReady_ofHyps_push_to_leftCoprodBranch` blocked (keep parent left-coprod
   head); still need full unrestricted `encodeReady_of_rawReferenceProduced`
   (derive branch shape from non-unit parent `coprodPushCont`; pair/lam /
   abort-never branches; consistency / mixed multi-entry; general
   WellInv→ready / deeper letPos bodies))
4. `EncodeIccInvariant` (`ICCEq` → `EncodeIccStep`) and
   `EncodeIccReflect` / rigidity (common code → `ICCEq`; peel-backed).
   Commute gens packaged under forced-head hyps; cong Go lifts landed;
   full `ofHyps` induction and reflection beyond unit/abort remain.
   `ICCCompleteness` needs both + encodability — never `none = none` as ICC.
   New gens ~~`case_letPos`~~ packaged (`encodeIccStep_case_letPos`); `sat_body`
   **blocked** as `EncodeIccStep` (`encodeICCGo_sat_body_codes`; encode keeps
   `.foc (.body _)` shell — sticky to erase).
5. Switch `referenceStructEq` / `referenceCompare` to `ICCCode` equality
   (`beq_iff_eq`) only after EncodeTotal + both characterization directions;
   erase public `2048` / fuel from the total API
6. 8G packaging (`DefEqDecidable` from total comparator)

Fallback if ordered-phase reification proves infeasible: `decideICCEq`, not a
return to the unsourced local rewrite loop.
-/

end Equality
end Gimbal
