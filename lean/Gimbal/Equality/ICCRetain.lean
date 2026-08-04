/-
  Retained-binder coproduct observation — semantic compatibility gate (M8).

  After the EncodeIx vertical slice (`ICCEncodeIx`), the next bounded gate is
  to show that replacing the current contracted saturation output
      `.case n uL uR`
  with the retained-binder form
      `.foc (.letPos n (.case (.var .here) (rename skip1 uL) (rename skip1 uR)))`
  preserves the erasure equality that `SatPreserve` / `ReferenceSound` use
  (`TmEq` on erasures → `IntrinsicDefEq`).

  This module does **not** edit `applyObsNeu`, totality, RawReference, or
  `referenceCompare`.
-/

import Gimbal.Equality.Abstract
import Gimbal.Equality.Hereditary
import Gimbal.Equality.SatPreserve

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Erasure bridge: retained `letPos` vs contracted `case`

**Verdict on the equality kind:** the comparison used by M8 reference soundness
is `TmEq` on erasures (see `tmEq_applySchedule` / `tmEq_of_referenceCompareTm` →
`IntrinsicDefEq`). At the raw `Tm` level the retained/contracted erasures are
related by **definitional `Eq`** (via `subst0` / `subst_exts_single_rename_skip1`);
no new semantic assumption and no extra `DefEq` bridge beyond packaging that `Eq`
as `TmEq.of_eq`.
-/

/--
General cut form (arbitrary branches under the sum binder): retained `letPos`
erases by unfolding to a contracted `Tm.case` whose branches are the
`exts (single ·)` instances of the binder-body erasures.
-/
theorem erase_letPos_case_var_here {Γ : Ctx sig} {L R A : Object sig.nBases}
    (n : NegNeu Γ (.coprod L R))
    (tL : InvTm (Γ ▻ .coprod L R ▻ L) A)
    (tR : InvTm (Γ ▻ .coprod L R ▻ R) A) :
    (FocTm.letPos n (.case (.var .here) tL tR)).erase =
      Tm.case n.erase
        (subst (Subst.exts (Subst.single n.erase)) tL.erase)
        (subst (Subst.exts (Subst.single n.erase)) tR.erase) := by
  -- `FocTm.erase (.letPos n t) = subst0 t.erase n.erase`, and `subst0` on
  -- `Tm.case (.var .here) …` is the contracted case with `exts (single _)`.
  change
      subst0
        (Tm.case (NegNeu.erase (NegNeu.var (Var.here (A := .coprod L R))))
          tL.erase tR.erase)
        n.erase =
      _
  simp only [subst0, subst, NegNeu.erase, Subst.single]

/--
Producer-shaped retained form: branches are the contracted `uL`/`uR` pushed
under the fresh sum binder via `Rename.skip1`. Erasures agree **definitionally**
with the bare `.case n uL uR` output.
-/
theorem erase_retained_coprod_obs {Γ : Ctx sig} {L R A : Object sig.nBases}
    (n : NegNeu Γ (.coprod L R))
    (uL : InvTm (Γ ▻ L) A) (uR : InvTm (Γ ▻ R) A) :
    (FocTm.letPos n
        (.case (.var .here)
          (InvTm.rename (Rename.skip1 (B := .coprod L R)) uL)
          (InvTm.rename (Rename.skip1 (B := .coprod L R)) uR))).erase =
      (InvTm.case n uL uR).erase := by
  have h := erase_letPos_case_var_here n
      (InvTm.rename (Rename.skip1 (B := .coprod L R)) uL)
      (InvTm.rename (Rename.skip1 (B := .coprod L R)) uR)
  simp only [InvTm.erase, h, InvTm.erase_rename, subst_exts_single_rename_skip1]

theorem tmEq_retained_coprod_obs {Γ : Ctx sig} {L R A : Object sig.nBases}
    (n : NegNeu Γ (.coprod L R))
    (uL : InvTm (Γ ▻ L) A) (uR : InvTm (Γ ▻ R) A) :
    TmEq
      (InvTm.foc
        (.letPos n
          (.case (.var .here)
            (InvTm.rename (Rename.skip1 (B := .coprod L R)) uL)
            (InvTm.rename (Rename.skip1 (B := .coprod L R)) uR)))).erase
      (InvTm.case n uL uR).erase :=
  TmEq.of_eq (by
    simpa [InvTm.erase, FocTm.erase] using erase_retained_coprod_obs n uL uR)

/--
**Implication needed by reference / schedule soundness:** if the contracted
`.case n uL uR` already preserves `cont` at erasure (`TmEq`), so does the
retained-binder form. Instantiates the SatPreserve obligation after a
producer migration that wraps the existing coproduct result in `letPos`.
-/
theorem tmEq_retained_coprod_obs_of_contracted {Γ : Ctx sig}
    {L R A : Object sig.nBases}
    (n : NegNeu Γ (.coprod L R))
    (uL : InvTm (Γ ▻ L) A) (uR : InvTm (Γ ▻ R) A)
    (cont : InvTm Γ A)
    (h : TmEq (InvTm.case n uL uR).erase cont.erase) :
    TmEq
      (InvTm.foc
        (.letPos n
          (.case (.var .here)
            (InvTm.rename (Rename.skip1 (B := .coprod L R)) uL)
            (InvTm.rename (Rename.skip1 (B := .coprod L R)) uR)))).erase
      cont.erase :=
  (tmEq_retained_coprod_obs n uL uR).trans h

/--
Specialization to the empty-rest abstr/η producer shape already proved
sound in `tmEq_case_abstr`.
-/
theorem tmEq_retained_coprod_obs_abstr {Γ : Ctx sig} {L R A : Object sig.nBases}
    (m : NegNeu Γ (.coprod L R)) (cont : InvTm Γ A) :
    TmEq
      (InvTm.foc
        (.letPos m
          (.case (.var .here)
            (InvTm.rename (Rename.skip1 (B := .coprod L R))
              (hsubstInv (InvTm.rename Rename.skip1
                (InvTm.abstr .here (NegNeu.weaken m) (InvTm.weaken cont)))
                (InvTm.etaInl L R)))
            (InvTm.rename (Rename.skip1 (B := .coprod L R))
              (hsubstInv (InvTm.rename Rename.skip1
                (InvTm.abstr .here (NegNeu.weaken m) (InvTm.weaken cont)))
                (InvTm.etaInr L R)))))).erase
      cont.erase :=
  tmEq_retained_coprod_obs_of_contracted m _ _ cont (tmEq_case_abstr m cont)

/-! ### WellInv / WellFoc for the retained constructor -/

theorem wellInv_retained_coprod_obs {Γ : Ctx sig} {L R A : Object sig.nBases}
    (n : NegNeu Γ (.coprod L R))
    (uL : InvTm (Γ ▻ L) A) (uR : InvTm (Γ ▻ R) A)
    (hn : WellNeg n) (hL : WellInv uL) (hR : WellInv uR) :
    WellInv
      (.foc
        (.letPos n
          (.case (.var .here)
            (InvTm.rename (Rename.skip1 (B := .coprod L R)) uL)
            (InvTm.rename (Rename.skip1 (B := .coprod L R)) uR)))) :=
  .foc (.letPos (by simp [objectPolarity_coprod]) hn
    (.case .var (wellInv_rename _ hL) (wellInv_rename _ hR)))

/-! ### Consumer audit + migration checklist (no evaluator edits)

Consumers of the current bare `.case n …` coproduct observation result:

| Module | Dependence | Migration note |
|---|---|---|
| `Saturation.applyObsNeu` | Emits `.case nSum …` | Change last; wrap or rebuild as retained `letPos` |
| `SatPreserve` | `tmEq_case_abstr` + schedule IH | Use `tmEq_retained_coprod_obs_of_contracted` (or collapse to atom `erase_letPos_abstr` if producer unifies with atom abstr) |
| `SatWell` | `.case hnP …` on ok result | Use `wellInv_retained_coprod_obs` (or atom `.letPos` rule) |
| Raw production / `ICCTotal` | Shape lemmas about bare case / η-hsubst | Re-target retained form; drop shape predicates where EncodeIx replaces them |
| `SatSymm` / schedule | Mostly entry mapping, not result shape | Expect light touch |
| Erasure soundness (`Abstract`/`Preserve`) | Already supplies `erase_letPos_abstr`, `sum_eta`, skip1 laws | **Done for this gate** via theorems above |
| `Reference` / compare | Recursive on `.case` / `.letPos` | Retained form already has a compare arm for `letPos`; case-inside is under binder |
| Fixtures | May assume bare case shapes | Update expected terms after producer change |

**Dependency order (do not start until this gate is accepted):**
1. ~~Generic retained↔contracted erasure + WellInv~~ (this module)
2. Change `applyObsNeu` coprod producer to retained binder
3. Repair `SatPreserve` / `SatWell` (thin wrappers over this bridge)
4. Extend certified production via `EncodeIx`
5. Derive readiness without provisional stash
6. Resume characterization / `referenceCompare` switch

**Stop criterion:** satisfied — equality is definitional `Eq` packaged as `TmEq.of_eq`;
feeds the existing `TmEq` → `IntrinsicDefEq` chain with no new semantic assumption.
-/

end Equality
end Gimbal
