/-
  Phase-indexed encode state (`EncodeIx`) — Milestone 8F vertical slice.

  Bounded experiment from checkpoint `cdb1160` / audit recommendation:
  certificates are indexed by the threaded encoder state, not by
  `OriginEnv.ofHyps` recomputed from raw hyps after the fact.

  This module does **not** modify `applyObsNeu` / `RawReferenceProduced` /
  totality / `referenceCompare`. No result-shape predicates.

  Vertical slice target:
      λ d. let z = f d in case z of inl q₁ => q₁ | inr q₂ => q₂
  with the coproduct observation retained as
      .foc (.letPos n (.case (.var .here) …))
  (not prematurely contracted to a bare `.case n …`).
-/

import Gimbal.Equality.Abstract
import Gimbal.Equality.ICCCode
import Gimbal.Equality.ICCOrigin
import Gimbal.Equality.ICCRetain
import Gimbal.Equality.ICCTotal
import Gimbal.Equality.Preserve
import Gimbal.Equality.TmEq

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Phase-indexed encoder state

Wraps the same ingredients `encodeICCGo` already threads: worklist, origin
environment, `domNest`, `obsSlot`. Binder transitions reuse `pushPos` and
`OriginEnv.weaken` — no duplicate worklist/env implementations.
-/

/-- Encoder state at context `Γ`. -/
structure EncodeIx (Γ : Ctx sig) where
  ws : List (PosEntry sig)
  env : OriginEnv Γ
  domNext : Nat
  obsNext : Nat

namespace EncodeIx

/-- Phase entry under `ofHyps` (empty dom/obs counters). -/
def entry (hyps : Array (Object sig.nBases)) : EncodeIx (Ctx.ofHyps hyps) where
  ws := OriginEnv.posWorklist (OriginEnv.ofHyps hyps)
  env := OriginEnv.ofHyps hyps
  domNext := 0
  obsNext := 0

/-- Consume the current positive head (`moveStable` / after left rule). -/
def pop (s : EncodeIx (sig := sig) Γ) : EncodeIx Γ where
  ws := s.ws.tail
  env := s.env
  domNext := s.domNext
  obsNext := s.obsNext

/--
Enter a λ-domain binder. Matches `encodeICCGo` / `EncodeReady.rightExp_lam`:
`pushPos` + `OriginEnv.weaken (.dom domNext)`.
-/
def bindDom (s : EncodeIx (sig := sig) Γ) (A : Object sig.nBases) :
    EncodeIx (Γ ▻ A) where
  ws := pushPos s.ws (.dom (sig := sig) s.domNext) A
  env := OriginEnv.weaken (A := A) s.env (.dom (sig := sig) s.domNext)
  domNext := s.domNext + 1
  obsNext := s.obsNext

/--
Retain an observation binder (`letPos`). Matches `EncodeReadyFoc.letPos`:
`pushPos` + `OriginEnv.weaken (.obs obsNext)`.
-/
def bindObs (s : EncodeIx (sig := sig) Γ) (P : Object sig.nBases) :
    EncodeIx (Γ ▻ P) where
  ws := pushPos s.ws (.obs (sig := sig) s.obsNext) P
  env := OriginEnv.weaken (A := P) s.env (.obs (sig := sig) s.obsNext)
  domNext := s.domNext
  obsNext := s.obsNext + 1

/--
Left branch after consuming left-coprod head `e` (encode’s
`pushPos ws.tail (.split e.origin false)`).
-/
def splitL (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (L : Object sig.nBases) : EncodeIx (Γ ▻ L) where
  ws := pushPos s.ws.tail (.split e.origin false) L
  env := OriginEnv.weaken (A := L) s.env (.split e.origin false)
  domNext := s.domNext
  obsNext := s.obsNext

/-- Right branch after consuming left-coprod head `e`. -/
def splitR (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (R : Object sig.nBases) : EncodeIx (Γ ▻ R) where
  ws := pushPos s.ws.tail (.split e.origin true) R
  env := OriginEnv.weaken (A := R) s.env (.split e.origin true)
  domNext := s.domNext
  obsNext := s.obsNext

/-- `bindDom` is definitionally the encode λ transition. -/
theorem bindDom_ws (s : EncodeIx (sig := sig) Γ) (A : Object sig.nBases) :
    (s.bindDom A).ws = pushPos s.ws (.dom (sig := sig) s.domNext) A := rfl

theorem bindObs_ws (s : EncodeIx (sig := sig) Γ) (P : Object sig.nBases) :
    (s.bindObs P).ws = pushPos s.ws (.obs (sig := sig) s.obsNext) P := rfl

end EncodeIx

/-! ### Certificates indexed by `EncodeIx` -/

/-- Invertible readiness at an explicit encoder state. -/
def InvCert {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx Γ) (t : InvTm Γ A) : Prop :=
  EncodeReady s.ws s.env s.domNext s.obsNext t

/-- Focused readiness; requires an empty worklist (rejection criterion). -/
def FocCert {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx Γ) (f : FocTm Γ A) : Prop :=
  s.ws = [] ∧ EncodeReadyFoc s.ws s.env s.domNext s.obsNext f

structure Produced {Γ : Ctx sig} (s : EncodeIx Γ) (A : Object sig.nBases) where
  term : InvTm Γ A
  cert : InvCert s term

/-- Cast a `Produced` package along an EncodeIx state equality. -/
def Produced.castState {Γ : Ctx sig} {s s' : EncodeIx (sig := sig) Γ}
    {A : Object sig.nBases} (h : s = s') (p : Produced s A) : Produced s' A :=
  h ▸ p

/-- Phase-entry specialization (may use `ofHyps`; intermediates must not). -/
abbrev EntryReady {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps hyps) A) : Prop :=
  InvCert (EncodeIx.entry hyps) t

/-! ### Producer-facing packaging (state transitions, not shape search) -/

theorem invCert_lam {Γ : Ctx sig} {Arg Ret : Object sig.nBases}
    (s : EncodeIx Γ) (body : InvTm (Γ ▻ Arg) Ret)
    (hfr : forcedRule s.ws (.exp Arg Ret) = .rightExp Arg Ret)
    (hb : InvCert (s.bindDom Arg) body) :
    InvCert s (.lam body) :=
  .rightExp_lam hfr hb

theorem invCert_moveStable {Γ : Ctx sig} {A : Object sig.nBases}
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ} {d o : Nat}
    (e : PosEntry sig) (t : InvTm Γ A)
    (hfr : forcedRule (e :: ws) A = .moveStable e)
    (ht : EncodeReady ws ε d o t) :
    InvCert ⟨e :: ws, ε, d, o⟩ t :=
  .moveStable hfr ht

theorem invCert_focus {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx Γ) (f : FocTm Γ A)
    (hfr : forcedRule s.ws A = .focus)
    (hf : EncodeReadyFoc s.ws s.env s.domNext s.obsNext f) :
    InvCert s (.foc f) :=
  .focus hfr hf

theorem focCert_letPos {Γ : Ctx sig} {P A : Object sig.nBases}
    {ε : OriginEnv Γ} {d o : Nat}
    (n : NegNeu Γ P) (t : InvTm (Γ ▻ P) A)
    (ht : EncodeReady
      (pushPos ([] : List (PosEntry sig)) (.obs (sig := sig) o) P)
      (OriginEnv.weaken (A := P) ε (.obs (sig := sig) o))
      d (o + 1) t) :
    EncodeReadyFoc ([] : List (PosEntry sig)) ε d o (.letPos n t) :=
  .letPos ht

theorem invCert_leftCoprod_peel {Γ : Ctx sig} {A L R : Object sig.nBases}
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ} {d o : Nat}
    (e : PosEntry sig)
    (n : NegNeu Γ (.coprod L R))
    (tL : InvTm (Γ ▻ L) A) (tR : InvTm (Γ ▻ R) A) (t : InvTm Γ A)
    (hfr : forcedRule (e :: ws) A = .leftCoprod e L R)
    (hpeel : peelCaseOuter ε e.origin t = some ⟨L, R, n, tL, tR⟩)
    (hL : EncodeReady (pushPos ws (.split e.origin false) L)
      (OriginEnv.weaken (A := L) ε (.split e.origin false)) d o tL)
    (hR : EncodeReady (pushPos ws (.split e.origin true) R)
      (OriginEnv.weaken (A := R) ε (.split e.origin true)) d o tR) :
    InvCert ⟨e :: ws, ε, d, o⟩ t :=
  .leftCoprod_peel hfr hpeel hL hR

/-- Phase-indexed readiness implies a successful `encodeICCGo` at the state's counters. -/
theorem invCert_encodeGo_some {Γ : Ctx sig} {A : Object sig.nBases}
    (s : EncodeIx Γ) (t : InvTm Γ A) (h : InvCert s t) :
    ∃ c, encodeICCGo (encodeFuel s.ws t) s.ws s.env s.domNext s.obsNext t =
      some c :=
  encodeReady_go_some h

/-- Entry readiness implies a concrete `encodeICC` code under `ofHyps`. -/
theorem entryReady_encode_some {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps) A}
    (h : EntryReady (sig := sig) t) :
    ∃ c, encodeICC (OriginEnv.ofHyps hyps) t = some c :=
  encode_of_encodeReady (OriginEnv.ofHyps hyps) (EncodeIx.entry (sig := sig) hyps).ws
    rfl (by simpa [EntryReady, InvCert, EncodeIx.entry] using h)

/-! ### Saturation boundary and retained observation producers

Saturation introduces an observation only after the current invertible worklist
is exhausted (`forcedRule` is `focus` / right rule). `bindObs` then creates a
singleton worklist, which inversion consumes before the next observation.
`AtSaturationBoundary` names that empty-worklist invariant; we do **not**
generalize `retainedCoprodObsCertified` to nonempty parents.
-/

/-- Empty invertible worklist: ready for a saturation observation. -/
abbrev AtSaturationBoundary {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ) : Prop :=
  s.ws = []

/-- `focus` (and thus observation introduction via `EncodeReady.focus`) only
fires on an empty worklist. -/
theorem forcedRule_eq_focus_ws_nil {ws : List (PosEntry sig)}
    {A : Object sig.nBases} (h : forcedRule (sig := sig) ws A = .focus) :
    ws = [] := by
  cases ws with
  | nil => rfl
  | cons e tail =>
      simp only [forcedRule] at h
      split at h <;> cases h

theorem atSaturationBoundary_of_forcedRule_focus {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) {A : Object sig.nBases}
    (h : forcedRule (sig := sig) s.ws A = .focus) :
    AtSaturationBoundary s :=
  forcedRule_eq_focus_ws_nil h

/-- Observation entry introduced by `bindObs` at counter `s.obsNext`. -/
def obsEntryOf (s : EncodeIx (sig := sig) Γ) (P : Object sig.nBases) :
    PosEntry sig :=
  ⟨.obs (sig := sig) s.obsNext, P⟩

theorem bindObs_ws_of_boundary {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ)
    (P : Object sig.nBases) (hbound : AtSaturationBoundary s)
    (hpos : objectPolarity P = .pos) :
    (s.bindObs P).ws = [obsEntryOf s P] := by
  simp only [EncodeIx.bindObs, obsEntryOf, AtSaturationBoundary] at hbound ⊢
  simp only [hbound, pushPos, hpos, BEq.rfl, ↓reduceIte]
  exact List.mergeSort_singleton _

/-- After retaining a positive observation at the boundary, `pop` restores the
boundary (singleton obs worklist fully consumed). -/
theorem bindObs_pop_boundary {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ)
    (P : Object sig.nBases) (hbound : AtSaturationBoundary s)
    (hpos : objectPolarity P = .pos) :
    AtSaturationBoundary ((s.bindObs P).pop) := by
  simp only [AtSaturationBoundary, EncodeIx.pop,
    bindObs_ws_of_boundary s P hbound hpos, List.tail_cons]

theorem bindObs_env_here {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ)
    (P : Object sig.nBases) :
    (s.bindObs P).env (Var.here : Var (sig := sig) (Γ ▻ P) P) =
      (.obs (sig := sig) s.obsNext : Origin sig) := by
  simp [EncodeIx.bindObs, OriginEnv.weaken, OriginEnv.snoc]

theorem forcedRule_leftCoprod_obsEntry {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ)
    (L R X : Object sig.nBases) :
    forcedRule (sig := sig) [obsEntryOf s (.coprod L R)] X =
      .leftCoprod (obsEntryOf s (.coprod L R)) L R := by
  simp [forcedRule, obsEntryOf]

theorem forcedRule_moveStable_obsEntry_base {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (i : Fin sig.nBases) (X : Object sig.nBases) :
    forcedRule (sig := sig) [obsEntryOf s (.base i)] X =
      .moveStable (obsEntryOf s (.base i)) := by
  simp [forcedRule, obsEntryOf]

/-- Lift a continuation certified after `pop` through `moveStable` at a
singleton worklist head. -/
def produced_moveStable_singleton {Γ : Ctx sig} {X : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ) (e : PosEntry sig)
    (hws : s.ws = [e])
    (hfr : forcedRule (sig := sig) [e] X = .moveStable e)
    (cont : Produced s.pop X) : Produced s X where
  term := cont.term
  cert := by
    have ht : EncodeReady (sig := sig) [] s.env s.domNext s.obsNext cont.term := by
      simpa [EncodeIx.pop, InvCert, hws, List.tail_cons] using cont.cert
    have hmove : EncodeReady (sig := sig) [e] s.env s.domNext s.obsNext cont.term :=
      EncodeReady.moveStable hfr ht
    change EncodeReady s.ws s.env s.domNext s.obsNext cont.term
    rw [hws]
    exact hmove

/--
Retained coproduct observation: term and certificate constructed together.
Branch `Produced` values live at the split states of `bindObs s`.

Consumes `AtSaturationBoundary` (empty parent worklist) — the phase invariant
for saturation observation introduction. Not generalized to nonempty parents.
-/
def retainedCoprodObsCertified {Γ : Ctx sig} {L R X : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (n : NegNeu Γ (.coprod L R))
    (hbound : AtSaturationBoundary s)
    (hfr : forcedRule (sig := sig) s.ws X = .focus)
    (left : Produced
      ((s.bindObs (.coprod L R)).splitL (obsEntryOf s (.coprod L R)) L) X)
    (right : Produced
      ((s.bindObs (.coprod L R)).splitR (obsEntryOf s (.coprod L R)) R) X) :
    Produced s X where
  term :=
    .foc (.letPos n
      (.case (.var .here) left.term right.term))
  cert := by
    let P : Object sig.nBases := .coprod L R
    let e : PosEntry sig := obsEntryOf s P
    let sObs : EncodeIx (sig := sig) (Γ ▻ P) := s.bindObs P
    let body : InvTm (Γ ▻ P) X := .case (.var .here) left.term right.term
    have hposP : objectPolarity P = .pos := by
      simp [P, objectPolarity_coprod]
    have hwsObs : sObs.ws = [e] :=
      bindObs_ws_of_boundary s P hbound hposP
    have htail : sObs.ws.tail = ([] : List (PosEntry sig)) := by
      rw [hwsObs]; rfl
    have hpeel :
        peelCaseOuter (sig := sig) sObs.env e.origin body =
          some ⟨L, R, .var .here, left.term, right.term⟩ := by
      simpa [body, e, obsEntryOf] using
        (peelCaseOuter_case_var_hit (sig := sig) sObs.env
          (.obs (sig := sig) s.obsNext)
          (Var.here : Var (sig := sig) (Γ ▻ P) P)
          left.term right.term (bindObs_env_here s P))
    have hL : EncodeReady (sig := sig)
        (pushPos ([] : List (PosEntry sig)) (.split e.origin false) L)
        (OriginEnv.weaken (A := L) sObs.env (.split e.origin false))
        sObs.domNext sObs.obsNext left.term := by
      have htail' : (s.bindObs (.coprod L R)).ws.tail = [] := by
        simpa [sObs, P] using htail
      simpa [EncodeIx.splitL, InvCert, htail', e, sObs, P, obsEntryOf] using
        left.cert
    have hR : EncodeReady (sig := sig)
        (pushPos ([] : List (PosEntry sig)) (.split e.origin true) R)
        (OriginEnv.weaken (A := R) sObs.env (.split e.origin true))
        sObs.domNext sObs.obsNext right.term := by
      have htail' : (s.bindObs (.coprod L R)).ws.tail = [] := by
        simpa [sObs, P] using htail
      simpa [EncodeIx.splitR, InvCert, htail', e, sObs, P, obsEntryOf] using
        right.cert
    have hbody : InvCert sObs body := by
      change EncodeReady sObs.ws sObs.env sObs.domNext sObs.obsNext body
      rw [hwsObs]
      exact
        (invCert_leftCoprod_peel (sig := sig) (ws := []) e
          (.var (Var.here : Var (sig := sig) (Γ ▻ P) P))
          left.term right.term body
          (by simpa [e, P] using forcedRule_leftCoprod_obsEntry s L R X)
          hpeel hL hR)
    have ht : EncodeReady (sig := sig)
        (pushPos ([] : List (PosEntry sig)) (.obs (sig := sig) s.obsNext) P)
        (OriginEnv.weaken (A := P) s.env (.obs (sig := sig) s.obsNext))
        s.domNext (s.obsNext + 1) body := by
      simpa [InvCert, sObs, EncodeIx.bindObs, AtSaturationBoundary, hbound] using
        hbody
    have hterm : InvCert s (.foc (.letPos n body)) := by
      refine invCert_focus s (.letPos n body) hfr ?_
      rw [show s.ws = [] from hbound]
      exact focCert_letPos (sig := sig) n body ht
    simpa [body] using hterm

/-- Retained producer term erases like the contracted `.case` when branches are
`Rename.skip1` of the contracted arms (generic erasure bridge). -/
theorem retainedCoprodObsCertified_erase {Γ : Ctx sig} {L R X : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (n : NegNeu Γ (.coprod L R))
    (uL : InvTm (Γ ▻ L) X) (uR : InvTm (Γ ▻ R) X)
    (hbound : AtSaturationBoundary s)
    (hfr : forcedRule (sig := sig) s.ws X = .focus)
    (left : Produced
      ((s.bindObs (.coprod L R)).splitL (obsEntryOf s (.coprod L R)) L) X)
    (right : Produced
      ((s.bindObs (.coprod L R)).splitR (obsEntryOf s (.coprod L R)) R) X)
    (hL : left.term = InvTm.rename (Rename.skip1 (B := .coprod L R)) uL)
    (hR : right.term = InvTm.rename (Rename.skip1 (B := .coprod L R)) uR) :
    (retainedCoprodObsCertified s n hbound hfr left right).term.erase =
      (InvTm.case n uL uR).erase := by
  simp only [retainedCoprodObsCertified, hL, hR, InvTm.erase, FocTm.erase]
  exact erase_retained_coprod_obs n uL uR

/--
Retained atomic observation at the saturation boundary: `letPos` then
`moveStable` restores the boundary for a nested continuation.
-/
def retainedAtomObsCertified {Γ : Ctx sig} {i : Fin sig.nBases}
    {X : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (n : NegNeu Γ (.base i))
    (hbound : AtSaturationBoundary s)
    (hfr : forcedRule (sig := sig) s.ws X = .focus)
    (cont : Produced (s.bindObs (.base i)).pop X) :
    Produced s X where
  term := .foc (.letPos n cont.term)
  cert := by
    let P : Object sig.nBases := .base i
    let e : PosEntry sig := obsEntryOf s P
    let sObs := s.bindObs P
    have hposP : objectPolarity P = .pos := rfl
    have hwsObs : sObs.ws = [e] := bindObs_ws_of_boundary s P hbound hposP
    let pMove := produced_moveStable_singleton sObs e hwsObs
      (by simpa [e, P] using forcedRule_moveStable_obsEntry_base s i X) cont
    have ht : EncodeReady (sig := sig)
        (pushPos ([] : List (PosEntry sig)) (.obs (sig := sig) s.obsNext) P)
        (OriginEnv.weaken (A := P) s.env (.obs (sig := sig) s.obsNext))
        s.domNext (s.obsNext + 1) cont.term := by
      simpa [InvCert, sObs, EncodeIx.bindObs, AtSaturationBoundary, hbound,
        pMove, produced_moveStable_singleton] using pMove.cert
    refine invCert_focus s (.letPos n cont.term) hfr ?_
    rw [show s.ws = [] from hbound]
    exact focCert_letPos (sig := sig) n cont.term ht

/-!
### Schedule / encode observation-boundary audit

`forcedRule_eq_focus_ws_nil`: every `forcedRule _ = .focus` path has `ws = []`.
`encodeICCGo` enters `encodeFocGo` (hence `letPos` / observation push) only under
`focus` or right-foc rules, which also require empty `ws`. So every encode-side
observation introduction is at `AtSaturationBoundary`.

`EncodeReadyFoc.letPos`’s inductive type allows a nonempty `ws` parameter, but no
`forcedRule`-gated encode/cert entry point uses that case. Saturation’s
`applyObsNeu` sequences schedule `rest` after binding; that list is not the
EncodeIx worklist — invertible EncodeIx work is emptied before the next
`bindObs`. **No real path found that introduces an EncodeIx observation with a
nonempty parent worklist.** Constructor left on the boundary invariant.
-/

/-! ## Vertical slice: `λ d. let z = f d in case z of …`

Signature fragment: one hypothesis `f : D → Q + Q`, goal `D → Q`.
Observation of `f d` retained as `.letPos`; scrutinee is the fresh obs var.
-/

/-- Slice signature: two bases `D`, `Q`. -/
def SliceSig : Signature where
  nBases := 2
  generators := #[]

private abbrev D : Object 2 := .base 0
private abbrev Q : Object 2 := .base 1
private abbrev SumQ : Object 2 := .coprod Q Q
private abbrev Fty : Object 2 := .exp D SumQ

/-- Phase hyps: only `f : D → Q + Q`. -/
def sliceHyps : Array (Object 2) := #[Fty]

def sliceΓ : Ctx SliceSig := Ctx.ofHyps (sig := SliceSig) sliceHyps

/-- `f` as a variable in `sliceΓ`. -/
def sliceF : Var sliceΓ Fty := .here

/-- Entry state for the slice. -/
def sliceEntry : EncodeIx (sig := SliceSig) sliceΓ :=
  EncodeIx.entry (sig := SliceSig) sliceHyps

/-- After binding `d : D`. -/
def sliceAfterDom : EncodeIx (sig := SliceSig) (sliceΓ ▻ D) :=
  sliceEntry.bindDom D

/-- Neutral `f d` under `Γ ▻ D` (`d` is a positive atom → focused neu). -/
def sliceApp :
    NegNeu (sig := SliceSig) (sliceΓ ▻ D) SumQ :=
  .app (.var (.there sliceF))
    (.foc (.pos (.done (.neu (.var .here)))))

/-- After `moveStable` pops `d`, retain observation `z` of type `Q + Q`. -/
def sliceAfterObs : EncodeIx (sig := SliceSig) (sliceΓ ▻ D ▻ SumQ) :=
  sliceAfterDom.pop.bindObs SumQ

/-- Branch bodies: return the payload `q : Q` (η-style identity on summands). -/
def sliceBranchL : InvTm (sig := SliceSig) (sliceΓ ▻ D ▻ SumQ ▻ Q) Q :=
  .foc (.pos (.done (.neu (.var .here))))

def sliceBranchR : InvTm (sig := SliceSig) (sliceΓ ▻ D ▻ SumQ ▻ Q) Q :=
  .foc (.pos (.done (.neu (.var .here))))

/-- Retained-binder body: `case z of inl q => q | inr q => q`. -/
def sliceCaseBody : InvTm (sig := SliceSig) (sliceΓ ▻ D ▻ SumQ) Q :=
  .case (.var .here) sliceBranchL sliceBranchR

/-- Retained observation form (audit requirement). -/
def sliceRetainedBody : InvTm (sig := SliceSig) (sliceΓ ▻ D) Q :=
  .foc (.letPos sliceApp sliceCaseBody)

/-- Full slice term. -/
def sliceTerm : InvTm (sig := SliceSig) sliceΓ (.exp D Q) :=
  .lam sliceRetainedBody

/-! ### Erasure relationship: retained `letPos` vs contracted cut

**Relation used: `TmEq` on erasures**, via the definitional strong-cut clause

    FocTm.erase (.letPos n t) = subst0 (InvTm.erase t) (NegNeu.erase n)

This is **not** `ICCEq` (no ICC generator equates retained `letPos`/`case`
with a bare `.case n`). It is the same cut that `tmEq_letPos_abstr` packages
for the abstr-weaken special case. Here the body is already a `case` on `.here`.
-/

theorem sliceRetainedBody_erase_is_subst0 :
    sliceRetainedBody.erase =
      subst0 sliceCaseBody.erase sliceApp.erase := by
  simp only [sliceRetainedBody, InvTm.erase, FocTm.erase]

/--
Contracted comparison object at the raw/`Tm` level: cut the retained binder.
-/
def sliceContractedErase : Tm (sig := SliceSig) (sliceΓ ▻ D) Q :=
  subst0 sliceCaseBody.erase sliceApp.erase

theorem sliceRetained_erase_eq_contracted_erase :
    sliceRetainedBody.erase = sliceContractedErase :=
  sliceRetainedBody_erase_is_subst0

theorem sliceRetained_tmEq_contracted_erase :
    TmEq sliceRetainedBody.erase sliceContractedErase :=
  TmEq.of_eq sliceRetained_erase_eq_contracted_erase

/-! ### Worklist layout facts (before certificates that depend on them) -/

/-- Entry worklist is empty (`f` is negative). -/
theorem sliceEntry_ws_nil : sliceEntry.ws = [] := by
  simp only [sliceEntry, EncodeIx.entry, sliceHyps, OriginEnv.posWorklist,
    OriginEnv.posCollect]
  native_decide

theorem slice_forcedRule_entry :
    forcedRule (sig := SliceSig) sliceEntry.ws (.exp D Q) = .rightExp D Q := by
  simp only [sliceEntry_ws_nil, forcedRule]

theorem sliceAfterDom_ws :
    sliceAfterDom.ws =
      [{ origin := .dom (sig := SliceSig) 0, ty := D }] := by
  simp only [sliceAfterDom, EncodeIx.bindDom, sliceEntry, EncodeIx.entry,
    sliceHyps, pushPos]
  native_decide

theorem sliceAfterDom_pop_ws_nil : sliceAfterDom.pop.ws = [] := by
  simp only [EncodeIx.pop, sliceAfterDom_ws, List.tail_cons]

theorem slice_bindObs_after_pop_ws :
    sliceAfterObs.ws =
      [{ origin := .obs (sig := SliceSig) 0, ty := SumQ }] := by
  simp only [sliceAfterObs, EncodeIx.bindObs, EncodeIx.pop, sliceAfterDom_ws, pushPos,
    List.tail_cons]
  native_decide

def sliceObsEntry : PosEntry SliceSig :=
  ⟨.obs (sig := SliceSig) 0, SumQ⟩

theorem sliceAfterDom_pop_obsNext :
    sliceAfterDom.pop.obsNext = 0 :=
  rfl

theorem slice_bindObs_ws_eq_obsEntry :
    sliceAfterObs.ws = [sliceObsEntry] := by
  simpa [sliceObsEntry] using slice_bindObs_after_pop_ws

theorem slice_forcedRule_leftCoprod_at_obs :
    forcedRule (sig := SliceSig) [sliceObsEntry] Q =
      .leftCoprod sliceObsEntry Q Q := by
  simp [forcedRule, sliceObsEntry, SumQ]

theorem slice_splitL_ws_eq :
    (sliceAfterObs.splitL sliceObsEntry Q).ws =
      [{ origin := .split (.obs (sig := SliceSig) 0) false, ty := Q }] := by
  simp only [EncodeIx.splitL, slice_bindObs_ws_eq_obsEntry, pushPos, List.tail_cons]
  native_decide

theorem slice_splitR_ws_eq :
    (sliceAfterObs.splitR sliceObsEntry Q).ws =
      [{ origin := .split (.obs (sig := SliceSig) 0) true, ty := Q }] := by
  simp only [EncodeIx.splitR, slice_bindObs_ws_eq_obsEntry, pushPos, List.tail_cons]
  native_decide

theorem slice_env_here_is_obs :
    sliceAfterObs.env
        (Var.here : Var (sig := SliceSig) (sliceΓ ▻ D ▻ SumQ) SumQ) =
      (.obs (sig := SliceSig) 0 : Origin SliceSig) := by
  simp [sliceAfterObs, EncodeIx.bindObs, EncodeIx.pop, OriginEnv.weaken, OriginEnv.snoc,
    sliceAfterDom, EncodeIx.bindDom, sliceEntry, EncodeIx.entry]

/-! ### Compositional certificates at exact `EncodeIx` states -/

/--
`bindDom` matches encode’s λ transition; body certificate is at `sliceAfterDom`,
not reconstructed from `ofHyps (hyps.push D)`.
-/
theorem slice_invCert_afterDom_moveStable_of_focus
    (hbody : InvCert (sig := SliceSig) sliceAfterDom.pop sliceRetainedBody) :
    InvCert sliceAfterDom sliceRetainedBody := by
  have hws := sliceAfterDom_ws
  have hbody' : EncodeReady (sig := SliceSig) [] sliceAfterDom.env
      sliceAfterDom.domNext sliceAfterDom.obsNext sliceRetainedBody := by
    simpa [EncodeIx.pop, hws, InvCert] using hbody
  have hfr : forcedRule (sig := SliceSig)
      ([{ origin := .dom (sig := SliceSig) 0, ty := D }] : List (PosEntry SliceSig)) Q =
      .moveStable ⟨.dom (sig := SliceSig) 0, D⟩ := by
    simp [forcedRule]
  change EncodeReady sliceAfterDom.ws sliceAfterDom.env
    sliceAfterDom.domNext sliceAfterDom.obsNext sliceRetainedBody
  rw [hws]
  exact EncodeReady.moveStable (e := ⟨.dom (sig := SliceSig) 0, D⟩)
    (ws := ([] : List (PosEntry SliceSig))) hfr hbody'

theorem slice_focCert_letPos_at_poppedDom
    (ht : InvCert (sig := SliceSig) sliceAfterObs sliceCaseBody) :
    EncodeReadyFoc (sig := SliceSig)
      sliceAfterDom.pop.ws sliceAfterDom.pop.env
      sliceAfterDom.pop.domNext sliceAfterDom.pop.obsNext
      (.letPos sliceApp sliceCaseBody) := by
  have hnil := sliceAfterDom_pop_ws_nil
  have hobs := sliceAfterDom_pop_obsNext
  have ht' : EncodeReady (sig := SliceSig)
      (pushPos ([] : List (PosEntry SliceSig)) (.obs (sig := SliceSig) 0) SumQ)
      (OriginEnv.weaken (A := SumQ) sliceAfterDom.pop.env (.obs (sig := SliceSig) 0))
      sliceAfterDom.pop.domNext 1 sliceCaseBody := by
    simpa [InvCert, sliceAfterObs, EncodeIx.bindObs, hnil, hobs] using ht
  rw [hnil, hobs]
  exact EncodeReadyFoc.letPos (n := sliceApp) ht'

theorem sliceTerm_invCert_of_body
    (hbody : InvCert (sig := SliceSig) sliceAfterDom sliceRetainedBody) :
    InvCert sliceEntry sliceTerm :=
  invCert_lam (sig := SliceSig) sliceEntry sliceRetainedBody
    slice_forcedRule_entry (by simpa [sliceAfterDom] using hbody)

theorem slice_branchL_cert :
    InvCert (sliceAfterObs.splitL sliceObsEntry Q)
      sliceBranchL := by
  set s := sliceAfterObs.splitL sliceObsEntry Q
  have hws : s.ws =
      [{ origin := .split (.obs (sig := SliceSig) 0) false, ty := Q }] :=
    slice_splitL_ws_eq
  have hnil : EncodeReady (sig := SliceSig) [] s.env s.domNext s.obsNext
      sliceBranchL :=
    .focus (by simp [forcedRule]) .pos
  have hfr : forcedRule (sig := SliceSig)
      ([{ origin := .split (.obs (sig := SliceSig) 0) false, ty := Q }] :
        List (PosEntry SliceSig)) Q =
      .moveStable ⟨.split (.obs (sig := SliceSig) 0) false, Q⟩ := by
    simp [forcedRule]
  have hmove : EncodeReady (sig := SliceSig)
      [{ origin := .split (.obs (sig := SliceSig) 0) false, ty := Q }]
      s.env s.domNext s.obsNext sliceBranchL :=
    EncodeReady.moveStable hfr hnil
  change EncodeReady s.ws s.env s.domNext s.obsNext sliceBranchL
  rw [hws]
  exact hmove

theorem slice_branchR_cert :
    InvCert (sliceAfterObs.splitR sliceObsEntry Q)
      sliceBranchR := by
  set s := sliceAfterObs.splitR sliceObsEntry Q
  have hws : s.ws =
      [{ origin := .split (.obs (sig := SliceSig) 0) true, ty := Q }] :=
    slice_splitR_ws_eq
  have hnil : EncodeReady (sig := SliceSig) [] s.env s.domNext s.obsNext
      sliceBranchR :=
    .focus (by simp [forcedRule]) .pos
  have hfr : forcedRule (sig := SliceSig)
      ([{ origin := .split (.obs (sig := SliceSig) 0) true, ty := Q }] :
        List (PosEntry SliceSig)) Q =
      .moveStable ⟨.split (.obs (sig := SliceSig) 0) true, Q⟩ := by
    simp [forcedRule]
  have hmove : EncodeReady (sig := SliceSig)
      [{ origin := .split (.obs (sig := SliceSig) 0) true, ty := Q }]
      s.env s.domNext s.obsNext sliceBranchR :=
    EncodeReady.moveStable hfr hnil
  change EncodeReady s.ws s.env s.domNext s.obsNext sliceBranchR
  rw [hws]
  exact hmove

theorem slice_peel_case :
    peelCaseOuter (sig := SliceSig)
      sliceAfterObs.env
      sliceObsEntry.origin
      sliceCaseBody =
      some ⟨Q, Q, .var .here, sliceBranchL, sliceBranchR⟩ := by
  simpa [sliceCaseBody, sliceObsEntry] using
    (peelCaseOuter_case_var_hit (sig := SliceSig)
      sliceAfterObs.env
      (.obs (sig := SliceSig) 0)
      (Var.here : Var (sig := SliceSig) (sliceΓ ▻ D ▻ SumQ) SumQ)
      sliceBranchL sliceBranchR slice_env_here_is_obs)

theorem slice_caseBody_invCert :
    InvCert sliceAfterObs sliceCaseBody := by
  have hws := slice_bindObs_ws_eq_obsEntry
  have hL : EncodeReady (sig := SliceSig)
      (pushPos ([] : List (PosEntry SliceSig))
        (.split sliceObsEntry.origin false) Q)
      (OriginEnv.weaken (A := Q) sliceAfterObs.env
        (.split sliceObsEntry.origin false))
      sliceAfterObs.domNext
      sliceAfterObs.obsNext
      sliceBranchL := by
    simpa [EncodeIx.splitL, hws, InvCert, List.tail_cons] using slice_branchL_cert
  have hR : EncodeReady (sig := SliceSig)
      (pushPos ([] : List (PosEntry SliceSig))
        (.split sliceObsEntry.origin true) Q)
      (OriginEnv.weaken (A := Q) sliceAfterObs.env
        (.split sliceObsEntry.origin true))
      sliceAfterObs.domNext
      sliceAfterObs.obsNext
      sliceBranchR := by
    simpa [EncodeIx.splitR, hws, InvCert, List.tail_cons] using slice_branchR_cert
  change EncodeReady sliceAfterObs.ws
    sliceAfterObs.env
    sliceAfterObs.domNext
    sliceAfterObs.obsNext sliceCaseBody
  rw [hws]
  exact
    (invCert_leftCoprod_peel (sig := SliceSig) (ws := []) sliceObsEntry
      (.var (Var.here : Var (sig := SliceSig) (sliceΓ ▻ D ▻ SumQ) SumQ))
      sliceBranchL sliceBranchR sliceCaseBody
      slice_forcedRule_leftCoprod_at_obs slice_peel_case hL hR)

theorem slice_retained_at_poppedDom :
    InvCert sliceAfterDom.pop sliceRetainedBody := by
  have hfr : forcedRule (sig := SliceSig) sliceAfterDom.pop.ws Q = .focus := by
    simp only [sliceAfterDom_pop_ws_nil, forcedRule]
  refine invCert_focus sliceAfterDom.pop (.letPos sliceApp sliceCaseBody) hfr ?_
  exact slice_focCert_letPos_at_poppedDom slice_caseBody_invCert

theorem slice_retained_at_afterDom :
    InvCert sliceAfterDom sliceRetainedBody :=
  slice_invCert_afterDom_moveStable_of_focus slice_retained_at_poppedDom

/-- **Acceptance for the vertical slice:** entry cert from compositional states. -/
theorem sliceTerm_entryReady : EntryReady (sig := SliceSig) sliceTerm :=
  sliceTerm_invCert_of_body slice_retained_at_afterDom

/-!
## Vertical-slice stop report (do not start evaluator migration here)

**Succeeded compositionally** at `EncodeIx` states; no reconstruction of
`OriginEnv.ofHyps` mid-flight; no result-shape predicates; production
`applyObsNeu` / `RawReferenceProduced` / totality / `referenceCompare` untouched.

### Relation used (retained vs contracted)
`TmEq` on erasures via definitional cut
`FocTm.erase (.letPos n t) = subst0 (erase t) (erase n)`.
Not `ICCEq` — no ICC generator equates retained `letPos`/`case` with bare `.case n`.

### Naturality / infrastructure
See chat stop report: mostly generic `EncodeReady` packaging +
`peelCaseOuter_case_var_hit` / `OriginEnv.snoc`; example-specific worklist
layout facts only. `pushPos` / `OriginEnv.weaken` reused; heavy
`rekeyHypToObs` not required for this slice.

### Next (proposed, not started)
Staged `applyObsNeu` migration is **deferred** until ordered-code comparison is
the public path (`compareSatRec` is optional optimization — see
`Completeness.lean`). Parallel path: EncodeIx-certified retained Hof codes
(`ICCHofRetain.lean`) → total encode → code equality → then atomic producer
switch. Do not repair `checkOldInvariant` for retained binders now.
-/

end Equality
end Gimbal
