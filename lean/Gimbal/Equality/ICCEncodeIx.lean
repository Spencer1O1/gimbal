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
import Gimbal.Equality.ICCEncodeReady
import Gimbal.Equality.ICCOrigin
import Gimbal.Equality.ICCRetain
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

/-! ### `EncodeIx.WellFormed` — counter-bounded collision freedom -/

/--
Persistent state invariant: live origins are injective, counter indices stay
strictly below `domNext` / `obsNext`, worklist origins are realized in the
environment without duplication, worklist heads have not yet been split, and
every live split retains a live parent (refinement, not a fresh counter).

Implies `Fresh (.dom s.domNext)` and `Fresh (.obs s.obsNext)` automatically.
-/
structure WellFormed {Γ : Ctx sig} (s : EncodeIx (sig := sig) Γ) : Prop where
  env_wf : OriginEnv.WellFormed s.env
  env_bounded :
    ∀ {A : Object sig.nBases} (x : Var Γ A),
      Origin.counterBounded (s.env x) s.domNext s.obsNext
  ws_bounded :
    ∀ {e : PosEntry sig}, e ∈ s.ws →
      Origin.counterBounded e.origin s.domNext s.obsNext
  ws_in_env :
    ∀ {e : PosEntry sig}, e ∈ s.ws →
      ∃ (A : Object sig.nBases) (x : Var Γ A), s.env x = e.origin
  ws_nodup : (s.ws.map (·.origin)).Nodup
  ws_split_fresh :
    ∀ {e : PosEntry sig}, e ∈ s.ws → ∀ side : Bool,
      OriginEnv.Fresh s.env (.split e.origin side)
  split_parent_live :
    ∀ {A : Object sig.nBases} (x : Var Γ A) (p : Origin sig) (side : Bool),
      s.env x = .split p side →
        ∃ (B : Object sig.nBases) (y : Var Γ B), s.env y = p

theorem WellFormed.fresh_dom {Γ : Ctx sig}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s) :
    OriginEnv.Fresh s.env (.dom (sig := sig) s.domNext) := by
  intro A x hx
  have hb : Origin.counterBounded (.dom (sig := sig) s.domNext) s.domNext s.obsNext := by
    simpa [hx] using hwf.env_bounded x
  exact Origin.not_counterBounded_dom_eq _ _ hb

theorem WellFormed.fresh_obs {Γ : Ctx sig}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s) :
    OriginEnv.Fresh s.env (.obs (sig := sig) s.obsNext) := by
  intro A x hx
  have hb : Origin.counterBounded (.obs (sig := sig) s.obsNext) s.domNext s.obsNext := by
    simpa [hx] using hwf.env_bounded x
  exact Origin.not_counterBounded_obs_eq _ _ hb

theorem WellFormed.fresh_split {Γ : Ctx sig}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s)
    {e : PosEntry sig} (he : e ∈ s.ws) (side : Bool) :
    OriginEnv.Fresh s.env (.split e.origin side) :=
  hwf.ws_split_fresh he side

private theorem nodup_ofHyps_posWorklist (hyps : Array (Object sig.nBases)) :
    ((OriginEnv.posWorklist (OriginEnv.ofHyps (sig := sig) hyps)).map
      (·.origin)).Nodup := by
  have hperm :=
    List.mergeSort_perm (OriginEnv.posCollect (OriginEnv.ofHyps (sig := sig) hyps))
      (fun e₁ e₂ => Origin.ble e₁.origin e₂.origin)
  refine (List.Perm.nodup_iff (hperm.map (·.origin))).2 ?_
  exact posCollect_origins_nodup _ (OriginEnv.ofHyps_wellFormed hyps)

/-- Freshness of `o` plus live-parent closure implies nested splits are fresh. -/
theorem WellFormed.fresh_of_fresh_parent {Γ : Ctx sig}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s)
    {o : Origin sig} (hfresh : OriginEnv.Fresh s.env o) (side : Bool) :
    OriginEnv.Fresh s.env (.split o side) := by
  intro A x hx
  obtain ⟨B, y, hy⟩ := hwf.split_parent_live x o side hx
  exact hfresh y hy

/-- Worklist origins are absent from a fresh environment origin. -/
theorem WellFormed.ws_origin_ne_fresh {Γ : Ctx sig}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s)
    {o : Origin sig} (hfresh : OriginEnv.Fresh s.env o)
    {e : PosEntry sig} (he : e ∈ s.ws) : e.origin ≠ o := by
  intro ho
  obtain ⟨A, x, hx⟩ := hwf.ws_in_env he
  exact hfresh x (hx.trans ho)

/-- Phase entry is well-formed (only `hyp` origins; counters at 0). -/
theorem entry_wellFormed (hyps : Array (Object sig.nBases)) :
    WellFormed (entry (sig := sig) hyps) where
  env_wf := OriginEnv.ofHyps_wellFormed hyps
  env_bounded := by
    intro A x
    simp only [entry, OriginEnv.ofHyps]
    exact Origin.counterBounded_hyp _ _ _
  ws_bounded := by
    intro e he
    simp only [entry] at he
    have he' : e ∈ OriginEnv.posCollect (OriginEnv.ofHyps (sig := sig) hyps) :=
      (List.mergeSort_perm _ _).mem_iff.mp he
    obtain ⟨i, hi⟩ := posCollect_ofHyps_origin_hyp hyps he'
    simpa [hi, entry] using Origin.counterBounded_hyp i 0 0
  ws_in_env := by
    intro e he
    simp only [entry] at he ⊢
    have he' : e ∈ OriginEnv.posCollect (OriginEnv.ofHyps (sig := sig) hyps) :=
      (List.mergeSort_perm _ _).mem_iff.mp he
    obtain ⟨A, x, hx, _⟩ := posCollect_mem_exists (OriginEnv.ofHyps hyps) he'
    exact ⟨A, x, hx⟩
  ws_nodup := nodup_ofHyps_posWorklist hyps
  ws_split_fresh := by
    intro e he side A x hx
    simp only [entry, OriginEnv.ofHyps] at hx
    cases hx
  split_parent_live := by
    intro A x p side hx
    simp only [entry, OriginEnv.ofHyps] at hx
    cases hx

/-- `pop` preserves well-formedness (drops a worklist head). -/
theorem WellFormed.pop {Γ : Ctx sig}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s) :
    WellFormed s.pop where
  env_wf := hwf.env_wf
  env_bounded := hwf.env_bounded
  ws_bounded := fun he => hwf.ws_bounded (List.mem_of_mem_tail he)
  ws_in_env := fun he => hwf.ws_in_env (List.mem_of_mem_tail he)
  ws_nodup := by
    simp only [EncodeIx.pop]
    have h := hwf.ws_nodup
    cases hws : s.ws with
    | nil =>
        simpa [hws] using h
    | cons head tail =>
        simp only [hws, List.tail_cons]
        rw [hws, List.map_cons, List.nodup_cons] at h
        exact h.2
  ws_split_fresh := fun he side => hwf.ws_split_fresh (List.mem_of_mem_tail he) side
  split_parent_live := hwf.split_parent_live

/-- Emptying the worklist preserves the environment invariant. -/
theorem WellFormed.emptyWs {Γ : Ctx sig}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s) :
    WellFormed (⟨[], s.env, s.domNext, s.obsNext⟩ : EncodeIx (sig := sig) Γ) where
  env_wf := hwf.env_wf
  env_bounded := hwf.env_bounded
  ws_bounded := fun he => by cases he
  ws_in_env := fun he => by cases he
  ws_nodup := List.nodup_nil
  ws_split_fresh := fun he _ => by cases he
  split_parent_live := hwf.split_parent_live

/--
Unused-binder push: same worklist/counters, environment extended by a bounded
fresh origin that does not collide with worklist split-freshness obligations.
-/
theorem WellFormed.weaken_unused {Γ : Ctx sig} {B : Object sig.nBases}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s) (o : Origin sig)
    (hfresh : OriginEnv.Fresh s.env o)
    (hb : Origin.counterBounded o s.domNext s.obsNext)
    (_hsplit : ∀ side : Bool, OriginEnv.Fresh s.env (.split o side))
    (hparent :
      ∀ (p : Origin sig) (side : Bool), o = .split p side →
        ∃ (C : Object sig.nBases) (y : Var Γ C), s.env y = p)
    (hcoll : ∀ {e : PosEntry sig}, e ∈ s.ws → ∀ side : Bool, o ≠ .split e.origin side) :
    WellFormed
      (⟨s.ws, OriginEnv.weaken (A := B) s.env o, s.domNext, s.obsNext⟩ :
        EncodeIx (sig := sig) (Γ ▻ B)) where
  env_wf := OriginEnv.WellFormed.weaken s.env o hwf.env_wf hfresh
  env_bounded := by
    intro C x
    cases x with
    | here =>
        simpa [OriginEnv.weaken, OriginEnv.snoc] using hb
    | there y =>
        simpa [OriginEnv.weaken, OriginEnv.snoc] using hwf.env_bounded y
  ws_bounded := hwf.ws_bounded
  ws_in_env := by
    intro e he
    obtain ⟨C, x, hx⟩ := hwf.ws_in_env he
    exact ⟨C, .there x, by simpa [OriginEnv.weaken, OriginEnv.snoc] using hx⟩
  ws_nodup := hwf.ws_nodup
  ws_split_fresh := by
    intro e he side C x
    cases x with
    | here =>
        simpa [OriginEnv.weaken, OriginEnv.snoc] using hcoll he side
    | there y =>
        simpa [OriginEnv.weaken, OriginEnv.snoc] using hwf.ws_split_fresh he side y
  split_parent_live := by
    intro C x p side hx
    cases x with
    | here =>
        simp [OriginEnv.weaken, OriginEnv.snoc] at hx
        obtain ⟨D, y, hy⟩ := hparent p side hx
        exact ⟨D, .there y, by simpa [OriginEnv.weaken, OriginEnv.snoc] using hy⟩
    | there y =>
        simp [OriginEnv.weaken, OriginEnv.snoc] at hx
        obtain ⟨D, z, hz⟩ := hwf.split_parent_live y p side hx
        exact ⟨D, .there z, by simpa [OriginEnv.weaken, OriginEnv.snoc] using hz⟩

/-- `bindDom` preserves well-formedness (allocates `.dom domNext`). -/
theorem WellFormed.bindDom {Γ : Ctx sig}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s)
    (A : Object sig.nBases) :
    WellFormed (s.bindDom A) where
  env_wf :=
    OriginEnv.WellFormed.weaken s.env (.dom (sig := sig) s.domNext)
      hwf.env_wf hwf.fresh_dom
  env_bounded := by
    intro B x
    cases x with
    | here =>
        simp [EncodeIx.bindDom, OriginEnv.weaken, OriginEnv.snoc]
        exact Nat.lt_succ_self _
    | there y =>
        simp [EncodeIx.bindDom, OriginEnv.weaken, OriginEnv.snoc]
        exact Origin.counterBounded_mono_dom (hwf.env_bounded y) (Nat.le_succ _)
  ws_bounded := by
    intro e he
    simp only [EncodeIx.bindDom] at he
    rw [mem_pushPos_iff] at he
    cases he with
    | inl h =>
        obtain ⟨_, rfl⟩ := h
        simp [EncodeIx.bindDom]
        exact Nat.lt_succ_self _
    | inr hmem =>
        simp [EncodeIx.bindDom]
        exact Origin.counterBounded_mono_dom (hwf.ws_bounded hmem) (Nat.le_succ _)
  ws_in_env := by
    intro e he
    simp only [EncodeIx.bindDom] at he ⊢
    rw [mem_pushPos_iff] at he
    cases he with
    | inl h =>
        obtain ⟨_, rfl⟩ := h
        exact ⟨A, .here, rfl⟩
    | inr hmem =>
        obtain ⟨B, x, hx⟩ := hwf.ws_in_env hmem
        exact ⟨B, .there x, by simpa [OriginEnv.weaken, OriginEnv.snoc] using hx⟩
  ws_nodup := by
    simp only [EncodeIx.bindDom]
    refine nodup_pushPos s.ws (.dom (sig := sig) s.domNext) A hwf.ws_nodup ?_
    intro e he
    exact hwf.ws_origin_ne_fresh hwf.fresh_dom he
  ws_split_fresh := by
    intro e he side B x
    simp only [EncodeIx.bindDom] at he
    rw [mem_pushPos_iff] at he
    cases x with
    | here =>
        simp [EncodeIx.bindDom, OriginEnv.weaken, OriginEnv.snoc]
    | there y =>
        cases he with
        | inl h =>
            obtain ⟨_, rfl⟩ := h
            simpa [EncodeIx.bindDom, OriginEnv.weaken, OriginEnv.snoc] using
              hwf.fresh_of_fresh_parent hwf.fresh_dom side y
        | inr hmem =>
            simpa [EncodeIx.bindDom, OriginEnv.weaken, OriginEnv.snoc] using
              hwf.ws_split_fresh hmem side y
  split_parent_live := by
    intro B x p side hx
    cases x with
    | here =>
        simp [EncodeIx.bindDom, OriginEnv.weaken, OriginEnv.snoc] at hx
    | there y =>
        simp [EncodeIx.bindDom, OriginEnv.weaken, OriginEnv.snoc] at hx
        obtain ⟨C, z, hz⟩ := hwf.split_parent_live y p side hx
        exact ⟨C, .there z, by simpa [EncodeIx.bindDom, OriginEnv.weaken, OriginEnv.snoc] using hz⟩

/-- `bindObs` preserves well-formedness (allocates `.obs obsNext`). -/
theorem WellFormed.bindObs {Γ : Ctx sig}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s)
    (P : Object sig.nBases) :
    WellFormed (s.bindObs P) where
  env_wf :=
    OriginEnv.WellFormed.weaken s.env (.obs (sig := sig) s.obsNext)
      hwf.env_wf hwf.fresh_obs
  env_bounded := by
    intro B x
    cases x with
    | here =>
        simp [EncodeIx.bindObs, OriginEnv.weaken, OriginEnv.snoc]
        exact Nat.lt_succ_self _
    | there y =>
        simp [EncodeIx.bindObs, OriginEnv.weaken, OriginEnv.snoc]
        exact Origin.counterBounded_mono_obs (hwf.env_bounded y) (Nat.le_succ _)
  ws_bounded := by
    intro e he
    simp only [EncodeIx.bindObs] at he
    rw [mem_pushPos_iff] at he
    cases he with
    | inl h =>
        obtain ⟨_, rfl⟩ := h
        simp [EncodeIx.bindObs]
        exact Nat.lt_succ_self _
    | inr hmem =>
        simp [EncodeIx.bindObs]
        exact Origin.counterBounded_mono_obs (hwf.ws_bounded hmem) (Nat.le_succ _)
  ws_in_env := by
    intro e he
    simp only [EncodeIx.bindObs] at he ⊢
    rw [mem_pushPos_iff] at he
    cases he with
    | inl h =>
        obtain ⟨_, rfl⟩ := h
        exact ⟨P, .here, rfl⟩
    | inr hmem =>
        obtain ⟨B, x, hx⟩ := hwf.ws_in_env hmem
        exact ⟨B, .there x, by simpa [OriginEnv.weaken, OriginEnv.snoc] using hx⟩
  ws_nodup := by
    simp only [EncodeIx.bindObs]
    refine nodup_pushPos s.ws (.obs (sig := sig) s.obsNext) P hwf.ws_nodup ?_
    intro e he
    exact hwf.ws_origin_ne_fresh hwf.fresh_obs he
  ws_split_fresh := by
    intro e he side B x
    simp only [EncodeIx.bindObs] at he
    rw [mem_pushPos_iff] at he
    cases x with
    | here =>
        simp [EncodeIx.bindObs, OriginEnv.weaken, OriginEnv.snoc]
    | there y =>
        cases he with
        | inl h =>
            obtain ⟨_, rfl⟩ := h
            simpa [EncodeIx.bindObs, OriginEnv.weaken, OriginEnv.snoc] using
              hwf.fresh_of_fresh_parent hwf.fresh_obs side y
        | inr hmem =>
            simpa [EncodeIx.bindObs, OriginEnv.weaken, OriginEnv.snoc] using
              hwf.ws_split_fresh hmem side y
  split_parent_live := by
    intro B x p side hx
    cases x with
    | here =>
        simp [EncodeIx.bindObs, OriginEnv.weaken, OriginEnv.snoc] at hx
    | there y =>
        simp [EncodeIx.bindObs, OriginEnv.weaken, OriginEnv.snoc] at hx
        obtain ⟨C, z, hz⟩ := hwf.split_parent_live y p side hx
        exact ⟨C, .there z, by simpa [EncodeIx.bindObs, OriginEnv.weaken, OriginEnv.snoc] using hz⟩

private theorem split_side_wellFormed {Γ : Ctx sig}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s)
    (e : PosEntry sig) (tail : List (PosEntry sig))
    (side₀ : Bool) (P : Object sig.nBases)
    (hws : s.ws = e :: tail) :
    WellFormed
      (⟨pushPos tail (.split e.origin side₀) P,
        OriginEnv.weaken (A := P) s.env (.split e.origin side₀),
        s.domNext, s.obsNext⟩ : EncodeIx (sig := sig) (Γ ▻ P)) where
  env_wf :=
    OriginEnv.WellFormed.weaken s.env (.split e.origin side₀)
      hwf.env_wf (hwf.fresh_split (by simp [hws]) side₀)
  env_bounded := by
    intro B x
    cases x with
    | here =>
        change Origin.counterBounded (.split e.origin side₀) s.domNext s.obsNext
        exact hwf.ws_bounded (show e ∈ s.ws by simp [hws])
    | there y =>
        simpa [OriginEnv.weaken, OriginEnv.snoc] using hwf.env_bounded y
  ws_bounded := by
    intro e' he'
    rw [mem_pushPos_iff] at he'
    cases he' with
    | inl h =>
        obtain ⟨_, rfl⟩ := h
        change Origin.counterBounded (.split e.origin side₀) s.domNext s.obsNext
        exact hwf.ws_bounded (show e ∈ s.ws by simp [hws])
    | inr hmem =>
        exact hwf.ws_bounded (by rw [hws]; exact List.Mem.tail _ hmem)
  ws_in_env := by
    intro e' he'
    rw [mem_pushPos_iff] at he'
    cases he' with
    | inl h =>
        obtain ⟨_, rfl⟩ := h
        exact ⟨P, .here, rfl⟩
    | inr hmem =>
        obtain ⟨B, x, hx⟩ := hwf.ws_in_env (by rw [hws]; exact List.Mem.tail _ hmem)
        exact ⟨B, .there x, by simpa [OriginEnv.weaken, OriginEnv.snoc] using hx⟩
  ws_nodup := by
    refine nodup_pushPos tail (.split e.origin side₀) P ?_ ?_
    · have h := hwf.ws_nodup
      rw [hws, List.map_cons, List.nodup_cons] at h
      exact h.2
    · intro e' he'
      exact hwf.ws_origin_ne_fresh
        (hwf.fresh_split (by simp [hws]) side₀)
        (by rw [hws]; exact List.Mem.tail _ he')
  ws_split_fresh := by
    intro e' he' side B x
    have hfresh₀ : OriginEnv.Fresh s.env (.split e.origin side₀) :=
      hwf.fresh_split (by simp [hws]) side₀
    have hne_head_tail : ∀ e' ∈ tail, e'.origin ≠ e.origin := by
      intro e' he' ho
      have h := hwf.ws_nodup
      rw [hws, List.map_cons, List.nodup_cons] at h
      exact h.1 (List.mem_map.2 ⟨e', he', ho⟩)
    rw [mem_pushPos_iff] at he'
    cases x with
    | here =>
        intro h
        simp [OriginEnv.weaken, OriginEnv.snoc] at h
        cases he' with
        | inl hpos =>
            obtain ⟨_, rfl⟩ := hpos
            obtain ⟨hp, _⟩ := h
            exact Origin.ne_split_self e.origin side₀ (by simpa using hp)
        | inr hmem =>
            obtain ⟨hp, _⟩ := h
            exact hne_head_tail e' hmem (by simpa using hp.symm)
    | there y =>
        cases he' with
        | inl hpos =>
            obtain ⟨_, rfl⟩ := hpos
            simpa [OriginEnv.weaken, OriginEnv.snoc] using
              hwf.fresh_of_fresh_parent hfresh₀ side y
        | inr hmem =>
            have hold : OriginEnv.Fresh s.env (Origin.split e'.origin side) :=
              hwf.ws_split_fresh (by rw [hws]; exact List.Mem.tail _ hmem) side
            simpa [OriginEnv.weaken, OriginEnv.snoc] using hold y
  split_parent_live := by
    intro B x p side hx
    cases x with
    | here =>
        simp [OriginEnv.weaken, OriginEnv.snoc] at hx
        obtain ⟨hp, _⟩ := hx
        obtain ⟨C, y, hy⟩ := hwf.ws_in_env (show e ∈ s.ws by simp [hws])
        refine ⟨C, .there y, ?_⟩
        simpa [OriginEnv.weaken, OriginEnv.snoc, hp] using hy
    | there y =>
        simp [OriginEnv.weaken, OriginEnv.snoc] at hx
        obtain ⟨C, z, hz⟩ := hwf.split_parent_live y p side hx
        exact ⟨C, .there z, by simpa [OriginEnv.weaken, OriginEnv.snoc] using hz⟩

/--
`splitL` preserves well-formedness when consuming the worklist head
(`s.ws = e :: tail`); parent identity is refined by `.split … false`.
-/
theorem WellFormed.splitL {Γ : Ctx sig}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s)
    (e : PosEntry sig) (tail : List (PosEntry sig)) (L : Object sig.nBases)
    (hws : s.ws = e :: tail) :
    WellFormed (s.splitL e L) := by
  simpa [EncodeIx.splitL, hws] using split_side_wellFormed hwf e tail false L hws

/--
`splitR` preserves well-formedness when consuming the worklist head
(`s.ws = e :: tail`); parent identity is refined by `.split … true`.
-/
theorem WellFormed.splitR {Γ : Ctx sig}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s)
    (e : PosEntry sig) (tail : List (PosEntry sig)) (R : Object sig.nBases)
    (hws : s.ws = e :: tail) :
    WellFormed (s.splitR e R) := by
  simpa [EncodeIx.splitR, hws] using split_side_wellFormed hwf e tail true R hws

/--
Push a fresh, already-bounded origin onto the worklist (counters unchanged).
Used by embedding `extPush` / `extSplit` when the origin is not a counter
allocation (`bindDom` / `bindObs`) and not a head-consuming split.
-/
theorem WellFormed.pushPos_fresh {Γ : Ctx sig} {P : Object sig.nBases}
    {s : EncodeIx (sig := sig) Γ} (hwf : WellFormed s) (o : Origin sig)
    (hfresh : OriginEnv.Fresh s.env o)
    (hb : Origin.counterBounded o s.domNext s.obsNext)
    (hparent :
      ∀ (p : Origin sig) (side : Bool), o = .split p side →
        ∃ (C : Object sig.nBases) (y : Var Γ C), s.env y = p)
    (hcoll : ∀ {e : PosEntry sig}, e ∈ s.ws → ∀ side : Bool, o ≠ .split e.origin side) :
    WellFormed
      (⟨pushPos s.ws o P,
        OriginEnv.weaken (A := P) s.env o, s.domNext, s.obsNext⟩ :
        EncodeIx (sig := sig) (Γ ▻ P)) where
  env_wf := OriginEnv.WellFormed.weaken s.env o hwf.env_wf hfresh
  env_bounded := by
    intro B x
    cases x with
    | here =>
        simpa [OriginEnv.weaken, OriginEnv.snoc] using hb
    | there y =>
        simpa [OriginEnv.weaken, OriginEnv.snoc] using hwf.env_bounded y
  ws_bounded := by
    intro e he
    rw [mem_pushPos_iff] at he
    cases he with
    | inl h =>
        obtain ⟨_, rfl⟩ := h
        exact hb
    | inr hmem =>
        exact hwf.ws_bounded hmem
  ws_in_env := by
    intro e he
    rw [mem_pushPos_iff] at he
    cases he with
    | inl h =>
        obtain ⟨_, rfl⟩ := h
        exact ⟨P, .here, rfl⟩
    | inr hmem =>
        obtain ⟨B, x, hx⟩ := hwf.ws_in_env hmem
        exact ⟨B, .there x, by simpa [OriginEnv.weaken, OriginEnv.snoc] using hx⟩
  ws_nodup := by
    refine nodup_pushPos s.ws o P hwf.ws_nodup ?_
    intro e he
    exact hwf.ws_origin_ne_fresh hfresh he
  ws_split_fresh := by
    intro e he side B x
    rw [mem_pushPos_iff] at he
    cases x with
    | here =>
        intro hx
        simp [OriginEnv.weaken, OriginEnv.snoc] at hx
        cases he with
        | inl hpos =>
            obtain ⟨_, rfl⟩ := hpos
            exact Origin.ne_split_self o side hx
        | inr hmem =>
            exact hcoll hmem side hx
    | there y =>
        cases he with
        | inl hpos =>
            obtain ⟨_, rfl⟩ := hpos
            simpa [OriginEnv.weaken, OriginEnv.snoc] using
              hwf.fresh_of_fresh_parent hfresh side y
        | inr hmem =>
            simpa [OriginEnv.weaken, OriginEnv.snoc] using
              hwf.ws_split_fresh hmem side y
  split_parent_live := by
    intro B x p side hx
    cases x with
    | here =>
        simp [OriginEnv.weaken, OriginEnv.snoc] at hx
        obtain ⟨C, y, hy⟩ := hparent p side hx
        exact ⟨C, .there y, by simpa [OriginEnv.weaken, OriginEnv.snoc] using hy⟩
    | there y =>
        simp [OriginEnv.weaken, OriginEnv.snoc] at hx
        obtain ⟨C, z, hz⟩ := hwf.split_parent_live y p side hx
        exact ⟨C, .there z, by simpa [OriginEnv.weaken, OriginEnv.snoc] using hz⟩

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
Retained never observation at the saturation boundary: canonical `.abort`,
matching `applyObsNeu`'s never arm. Does not bind an observation or recurse on
a continuation — remaining schedule entries are irrelevant.
-/
def retainedNeverObsCertified {Γ : Ctx sig} {X : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ)
    (n : NegNeu Γ .never)
    (_hbound : AtSaturationBoundary s)
    (hfr : forcedRule (sig := sig) s.ws X = .focus) :
    Produced s X where
  term := .abort n
  cert := by
    change EncodeReady s.ws s.env s.domNext s.obsNext (.abort (A := X) n)
    exact encodeReady_abort_focus s.env s.ws s.domNext s.obsNext n hfr

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
