/-
  EncodeIx state embeddings (Milestone 8F weakening/naturality spike).

  A morphism between encoder states along a context renaming `ρ : Γ → Δ`.
  Used to transport certificates when a target binder is intentionally unused by
  the source term (e.g. unused branch binder under forced `leftCoprod`).

  Does **not** infer the target state from the renamed term.
-/

import Gimbal.Equality.ICCEncodeIx
import Gimbal.Equality.ICCPeel

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ## State embedding -/

/--
Morphism of encoder states along `ρ : Rename Γ Δ`.

* `env_commute` — old-origin slots commute with `ρ`
* `source_wf` / `target_wf` — full `EncodeIx.WellFormed` on both sides
  (injectivity, counter bounds, worklist/env agreement, split freshness)
* `ws_eq` — source worklist equals target worklist (origins are absolute;
  fresh target binders may exist but need not occur in this shared worklist)
* `domNext_eq` / `obsNext_eq` — counter evolution is explicit (not reset)
-/
structure EncodeIxEmbedding {Γ Δ : Ctx sig}
    (ρ : Rename sig Γ Δ)
    (s : EncodeIx (sig := sig) Γ)
    (t : EncodeIx (sig := sig) Δ) : Prop where
  env_commute : ∀ {A : Object sig.nBases} (x : Var Γ A), t.env (ρ x) = s.env x
  source_wf : EncodeIx.WellFormed s
  target_wf : EncodeIx.WellFormed t
  respectsRawIdx : Rename.RespectsRawIdx ρ
  ws_eq : s.ws = t.ws
  domNext_eq : t.domNext = s.domNext
  obsNext_eq : t.obsNext = s.obsNext

/-- Lookup naturality: well-formed embeddings transport `find?` along `ρ`. -/
theorem EncodeIxEmbedding.find?_eq {Γ Δ : Ctx sig}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t)
    (o : Origin sig) {A : Object sig.nBases} (x : Var Γ A)
    (h : OriginEnv.find? s.env o = some ⟨A, x⟩) :
    OriginEnv.find? t.env o = some ⟨A, ρ x⟩ := by
  have hx : s.env x = o := OriginEnv.find?_eq_some_eq s.env o x h
  have : t.env (ρ x) = o := by rw [emb.env_commute x, hx]
  exact OriginEnv.find?_eq_some_of_wellFormed t.env o (ρ x) emb.target_wf.env_wf this

/-- Existing origins remain collision-free on the image of `ρ`. -/
theorem EncodeIxEmbedding.origin_inj_image {Γ Δ : Ctx sig}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t)
    {A B : Object sig.nBases} (x : Var Γ A) (y : Var Γ B)
    (heq : t.env (ρ x) = t.env (ρ y)) :
    ∃ _hAB : A = B, HEq x y := by
  have : s.env x = s.env y := by
    simpa [emb.env_commute x, emb.env_commute y] using heq
  exact emb.source_wf.env_wf.injective x y this

/-! ## Unused-binder weaken embedding -/

/--
Unused newest binder: `Rename.weaken` into `OriginEnv.weaken … o` with
identical worklist and counters.

Side conditions match `EncodeIx.WellFormed.weaken_unused` (fresh, bounded,
parent-live for splits, no collision with worklist split-freshness).
-/
theorem encodeIxEmbedding_weaken {Γ : Ctx sig} {B : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ) (o : Origin sig)
    (hwf : EncodeIx.WellFormed s)
    (hfresh : OriginEnv.Fresh s.env o)
    (hb : Origin.counterBounded o s.domNext s.obsNext)
    (hsplit : ∀ side : Bool, OriginEnv.Fresh s.env (.split o side))
    (hparent :
      ∀ (p : Origin sig) (side : Bool), o = .split p side →
        ∃ (C : Object sig.nBases) (y : Var Γ C), s.env y = p)
    (hcoll : ∀ {e : PosEntry sig}, e ∈ s.ws → ∀ side : Bool, o ≠ .split e.origin side) :
    EncodeIxEmbedding (Rename.weaken (A := B)) s
      ⟨s.ws, OriginEnv.weaken (A := B) s.env o, s.domNext, s.obsNext⟩ where
  env_commute := by
    intro A x
    simp [Rename.weaken, OriginEnv.weaken, OriginEnv.snoc]
  source_wf := hwf
  target_wf := EncodeIx.WellFormed.weaken_unused hwf o hfresh hb hsplit hparent hcoll
  respectsRawIdx := Rename.weaken_respectsRawIdx
  ws_eq := rfl
  domNext_eq := rfl
  obsNext_eq := rfl

/-! ## Extending embeddings under binder push -/

/-- Same absolute origin `o` pushed on both sides; counters taken from `emb`. -/
theorem EncodeIxEmbedding.extPush {Γ Δ : Ctx sig} {P : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t) (o : Origin sig)
    (hsFresh : OriginEnv.Fresh s.env o) (htFresh : OriginEnv.Fresh t.env o)
    (hb : Origin.counterBounded o s.domNext s.obsNext)
    (hparent :
      ∀ (p : Origin sig) (side : Bool), o = .split p side →
        ∃ (C : Object sig.nBases) (y : Var Γ C), s.env y = p)
    (hcoll : ∀ {e : PosEntry sig}, e ∈ s.ws → ∀ side : Bool, o ≠ .split e.origin side) :
    EncodeIxEmbedding (Rename.ext ρ)
      ⟨pushPos s.ws o P,
        OriginEnv.weaken (A := P) s.env o, s.domNext, s.obsNext⟩
      ⟨pushPos t.ws o P,
        OriginEnv.weaken (A := P) t.env o, t.domNext, t.obsNext⟩ where
  env_commute := by
    intro A x
    cases x with
    | here => simp [Rename.ext, OriginEnv.weaken, OriginEnv.snoc]
    | there y =>
        simpa [Rename.ext, OriginEnv.weaken, OriginEnv.snoc] using emb.env_commute y
  source_wf := EncodeIx.WellFormed.pushPos_fresh emb.source_wf o hsFresh hb hparent hcoll
  target_wf := by
    have hb' : Origin.counterBounded o t.domNext t.obsNext := by
      simpa [emb.domNext_eq, emb.obsNext_eq] using hb
    have hparent' :
        ∀ (p : Origin sig) (side : Bool), o = .split p side →
          ∃ (C : Object sig.nBases) (y : Var Δ C), t.env y = p := by
      intro p side ho
      obtain ⟨C, y, hy⟩ := hparent p side ho
      exact ⟨C, ρ y, by simpa [emb.env_commute y] using hy⟩
    have hcoll' :
        ∀ {e : PosEntry sig}, e ∈ t.ws → ∀ side : Bool, o ≠ .split e.origin side := by
      intro e he side
      have : e ∈ s.ws := by simpa [emb.ws_eq] using he
      exact hcoll this side
    simpa [emb.ws_eq, emb.domNext_eq, emb.obsNext_eq] using
      EncodeIx.WellFormed.pushPos_fresh emb.target_wf o htFresh hb' hparent' hcoll'
  respectsRawIdx := Rename.ext_respectsRawIdx emb.respectsRawIdx
  ws_eq := by simp [emb.ws_eq]
  domNext_eq := emb.domNext_eq
  obsNext_eq := emb.obsNext_eq

/-- Obs-push at the shared `obsNext` (stepped on both sides). -/
theorem EncodeIxEmbedding.extObs {Γ Δ : Ctx sig} {P : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t) :
    EncodeIxEmbedding (Rename.ext ρ)
      (s.bindObs P) (t.bindObs P) := by
  have hobs : t.obsNext = s.obsNext := emb.obsNext_eq
  have hdom : t.domNext = s.domNext := emb.domNext_eq
  refine
    { env_commute := ?_
      source_wf := EncodeIx.WellFormed.bindObs emb.source_wf P
      target_wf := by
        simpa [EncodeIx.bindObs, hobs, hdom, emb.ws_eq] using
          EncodeIx.WellFormed.bindObs emb.target_wf P
      respectsRawIdx := Rename.ext_respectsRawIdx emb.respectsRawIdx
      ws_eq := ?_
      domNext_eq := by simp [EncodeIx.bindObs, hdom]
      obsNext_eq := by simp [EncodeIx.bindObs, hobs] }
  · intro A x
    cases x with
    | here => simp [Rename.ext, EncodeIx.bindObs, OriginEnv.weaken, OriginEnv.snoc, hobs]
    | there y =>
        simpa [Rename.ext, EncodeIx.bindObs, OriginEnv.weaken, OriginEnv.snoc] using
          emb.env_commute y
  · simp [EncodeIx.bindObs, hobs, emb.ws_eq]

/-- Dom-push at the shared `domNext` (stepped on both sides). -/
theorem EncodeIxEmbedding.extDom {Γ Δ : Ctx sig} {Arg : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t) :
    EncodeIxEmbedding (Rename.ext ρ)
      (s.bindDom Arg) (t.bindDom Arg) := by
  have hobs : t.obsNext = s.obsNext := emb.obsNext_eq
  have hdom : t.domNext = s.domNext := emb.domNext_eq
  refine
    { env_commute := ?_
      source_wf := EncodeIx.WellFormed.bindDom emb.source_wf Arg
      target_wf := by
        simpa [EncodeIx.bindDom, hobs, hdom, emb.ws_eq] using
          EncodeIx.WellFormed.bindDom emb.target_wf Arg
      respectsRawIdx := Rename.ext_respectsRawIdx emb.respectsRawIdx
      ws_eq := ?_
      domNext_eq := by simp [EncodeIx.bindDom, hdom]
      obsNext_eq := by simp [EncodeIx.bindDom, hobs] }
  · intro A x
    cases x with
    | here => simp [Rename.ext, EncodeIx.bindDom, OriginEnv.weaken, OriginEnv.snoc, hdom]
    | there y =>
        simpa [Rename.ext, EncodeIx.bindDom, OriginEnv.weaken, OriginEnv.snoc] using
          emb.env_commute y
  · simp [EncodeIx.bindDom, hdom, emb.ws_eq]

/-- Split-push with the same parent origin/side on both sides. -/
theorem EncodeIxEmbedding.extSplit {Γ Δ : Ctx sig} {P : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t) (parent : Origin sig) (side : Bool)
    (hsFresh : OriginEnv.Fresh s.env (.split parent side))
    (htFresh : OriginEnv.Fresh t.env (.split parent side))
    (hb : Origin.counterBounded (.split parent side) s.domNext s.obsNext)
    (hparentLive : ∃ (C : Object sig.nBases) (y : Var Γ C), s.env y = parent)
    (hcoll : ∀ {e : PosEntry sig}, e ∈ s.ws → ∀ side' : Bool,
      (.split parent side : Origin sig) ≠ .split e.origin side') :
    EncodeIxEmbedding (Rename.ext ρ)
      ⟨pushPos s.ws (.split parent side) P,
        OriginEnv.weaken (A := P) s.env (.split parent side),
        s.domNext, s.obsNext⟩
      ⟨pushPos t.ws (.split parent side) P,
        OriginEnv.weaken (A := P) t.env (.split parent side),
        t.domNext, t.obsNext⟩ :=
  EncodeIxEmbedding.extPush (P := P) emb (.split parent side) hsFresh htFresh hb
    (fun p side' heq => by
      cases heq
      exact hparentLive)
    hcoll

/-! ## Full `EncodeReady` transport

Binder Fresh for λ / `letPos` / peel branches is derived only from threaded
`EncodeIx.WellFormed` (via `bindDom` / `bindObs` / `splitL`/`splitR`).
-/

private theorem encodeReady_of_embedding_aux {Γ : Ctx sig} {A : Object sig.nBases}
    {ws : List (PosEntry sig)} {ε : OriginEnv Γ} {d o : Nat} {body : InvTm Γ A}
    (h : EncodeReady ws ε d o body) :
    ∀ {Δ : Ctx sig} (ρ : Rename sig Γ Δ) (ε' : OriginEnv Δ),
      EncodeIx.WellFormed (⟨ws, ε, d, o⟩ : EncodeIx (sig := sig) Γ) →
      EncodeIx.WellFormed (⟨ws, ε', d, o⟩ : EncodeIx (sig := sig) Δ) →
      (∀ {B} (x : Var Γ B), ε' (ρ x) = ε x) →
      Rename.RespectsRawIdx ρ →
      EncodeReady ws ε' d o (InvTm.rename ρ body) := by
  refine
    (EncodeReady.rec
      (motive_1 := fun {Γ} ws ε d o {A} body _ =>
        ∀ {Δ : Ctx sig} (ρ : Rename sig Γ Δ) (ε' : OriginEnv Δ),
          EncodeIx.WellFormed (⟨ws, ε, d, o⟩ : EncodeIx (sig := sig) Γ) →
          EncodeIx.WellFormed (⟨ws, ε', d, o⟩ : EncodeIx (sig := sig) Δ) →
          (∀ {B} (x : Var Γ B), ε' (ρ x) = ε x) →
          Rename.RespectsRawIdx ρ →
          EncodeReady ws ε' d o (InvTm.rename ρ body))
      (motive_2 := fun {Γ} ws ε d o {A} f _ =>
        ∀ {Δ : Ctx sig} (ρ : Rename sig Γ Δ) (ε' : OriginEnv Δ),
          EncodeIx.WellFormed (⟨ws, ε, d, o⟩ : EncodeIx (sig := sig) Γ) →
          EncodeIx.WellFormed (⟨ws, ε', d, o⟩ : EncodeIx (sig := sig) Δ) →
          (∀ {B} (x : Var Γ B), ε' (ρ x) = ε x) →
          Rename.RespectsRawIdx ρ →
          EncodeReadyFoc ws ε' d o (FocTm.rename ρ f))
      (fun {Γ} A e ws ε d o t hfr _ ih {_Δ} ρ ε' hswf htwf hε hρ =>
        have hswf' : EncodeIx.WellFormed (⟨ws, ε, d, o⟩ : EncodeIx (sig := sig) Γ) := by
          simpa [EncodeIx.pop] using
            EncodeIx.WellFormed.pop (s := ⟨e :: ws, ε, d, o⟩) hswf
        have htwf' : EncodeIx.WellFormed (⟨ws, ε', d, o⟩ : EncodeIx (sig := sig) _) := by
          simpa [EncodeIx.pop] using
            EncodeIx.WellFormed.pop (s := ⟨e :: ws, ε', d, o⟩) htwf
        .moveStable hfr (ih ρ ε' hswf' htwf' hε hρ))
      (fun {Γ} A e _ws _ε _d _o n hty {_Δ} ρ _ε' _hswf _htwf _hε _hρ =>
        .leftNever (n := NegNeu.rename ρ n) hty)
      (fun {Γ} A ws _ε _d _o n hfr {_Δ} ρ ε' _hswf _htwf _hε _hρ =>
        .abortFocus (n := NegNeu.rename ρ n) (ε := ε') hfr)
      (fun {Γ} ws _ε d o hfr {_Δ} ρ ε' _hswf _htwf _hε _hρ =>
        by simpa [InvTm.rename] using EncodeReady.rightUnit (ε := ε') hfr)
      (fun {Γ} L R ws ε d o t u hfr _ _ iht ihu {_Δ} ρ ε' hswf htwf hε hρ =>
        .rightProd_pair hfr (iht ρ ε' hswf htwf hε hρ) (ihu ρ ε' hswf htwf hε hρ))
      (fun {Γ} L R ws ε d o f hfr _ ihf {_Δ} ρ ε' hswf htwf hε hρ =>
        .rightProd_foc hfr (ihf ρ ε' hswf htwf hε hρ))
      (fun {Γ} Arg Ret ws ε d o body hfr _ ihb {_Δ} ρ ε' hswf htwf hε hρ =>
        .rightExp_lam hfr (ihb (Rename.ext ρ)
          (OriginEnv.weaken (A := Arg) ε' (.dom (sig := sig) d))
          (by simpa [EncodeIx.bindDom] using EncodeIx.WellFormed.bindDom hswf Arg)
          (by simpa [EncodeIx.bindDom] using EncodeIx.WellFormed.bindDom htwf Arg)
          (fun {B} x => by
            cases x with
            | here => rfl
            | there y => exact hε y)
          (Rename.ext_respectsRawIdx hρ)))
      (fun {Γ} Arg Ret ws ε d o f hfr _ ihf {_Δ} ρ ε' hswf htwf hε hρ =>
        .rightExp_foc hfr (ihf ρ ε' hswf htwf hε hρ))
      (fun {Γ} A L R e ws ε d o n tL tR t hfr hpeel _ _ ihL ihR {_Δ} ρ ε' hswf htwf hε hρ =>
        have hpeel' :
            peelCaseOuter ε' e.origin (InvTm.rename ρ t) =
              some ⟨L, R, NegNeu.rename ρ n,
                InvTm.rename (Rename.ext ρ) tL, InvTm.rename (Rename.ext ρ) tR⟩ :=
          peelCaseOuter_rename ρ ε ε' e.origin t hε hρ hpeel
        .leftCoprod_peel hfr hpeel'
          (ihL (Rename.ext ρ)
            (OriginEnv.weaken (A := L) ε' (.split e.origin false))
            (by simpa [EncodeIx.splitL] using
              EncodeIx.WellFormed.splitL hswf e ws L rfl)
            (by simpa [EncodeIx.splitL] using
              EncodeIx.WellFormed.splitL htwf e ws L rfl)
            (fun {B} x => by
              cases x with
              | here => rfl
              | there y => exact hε y)
            (Rename.ext_respectsRawIdx hρ))
          (ihR (Rename.ext ρ)
            (OriginEnv.weaken (A := R) ε' (.split e.origin true))
            (by simpa [EncodeIx.splitR] using
              EncodeIx.WellFormed.splitR hswf e ws R rfl)
            (by simpa [EncodeIx.splitR] using
              EncodeIx.WellFormed.splitR htwf e ws R rfl)
            (fun {B} x => by
              cases x with
              | here => rfl
              | there y => exact hε y)
            (Rename.ext_respectsRawIdx hρ)))
      (fun {Γ} L R e ws ε d o x hfr hfind hit _ _ ihL ihR {_Δ} ρ ε' hswf htwf hε hρ =>
        have hερ : ε' (ρ x) = e.origin := by
          have hx := beq_iff_eq.mp hit
          simpa [hε x] using hx
        have hfind' : OriginEnv.find? ε' e.origin = some ⟨.coprod L R, ρ x⟩ :=
          OriginEnv.find?_eq_some_of_wellFormed ε' e.origin (ρ x) htwf.env_wf hερ
        have hit' : (ε' (ρ x) == e.origin) = true := beq_iff_eq.mpr hερ
        .leftCoprod_unitEta hfr hfind' hit'
          (ihL (Rename.ext ρ)
            (OriginEnv.weaken (A := L) ε' (.split e.origin false))
            (by simpa [EncodeIx.splitL] using
              EncodeIx.WellFormed.splitL hswf e ws L rfl)
            (by simpa [EncodeIx.splitL] using
              EncodeIx.WellFormed.splitL htwf e ws L rfl)
            (fun {B} y => by
              cases y with
              | here => rfl
              | there z => exact hε z)
            (Rename.ext_respectsRawIdx hρ))
          (ihR (Rename.ext ρ)
            (OriginEnv.weaken (A := R) ε' (.split e.origin true))
            (by simpa [EncodeIx.splitR] using
              EncodeIx.WellFormed.splitR hswf e ws R rfl)
            (by simpa [EncodeIx.splitR] using
              EncodeIx.WellFormed.splitR htwf e ws R rfl)
            (fun {B} y => by
              cases y with
              | here => rfl
              | there z => exact hε z)
            (Rename.ext_respectsRawIdx hρ)))
      (fun {Γ} A ws ε d o f hfr _ ihf {_Δ} ρ ε' hswf htwf hε hρ =>
        .focus hfr (ihf ρ ε' hswf htwf hε hρ))
      (fun {Γ} A _ws _ε _d _o p {_Δ} ρ _ε' _hswf _htwf _hε _hρ => .pos)
      (fun {Γ} A _ws _ε _d _o n {_Δ} ρ _ε' _hswf _htwf _hε _hρ => .neg)
      (fun {Γ} P A ws ε d o n t _ iht {_Δ} ρ ε' hswf htwf hε hρ =>
        .letPos (n := NegNeu.rename ρ n) (iht (Rename.ext ρ)
          (OriginEnv.weaken (A := P) ε' (.obs (sig := sig) o))
          (by simpa [EncodeIx.bindObs] using EncodeIx.WellFormed.bindObs hswf P)
          (by simpa [EncodeIx.bindObs] using EncodeIx.WellFormed.bindObs htwf P)
          (fun {B} x => by
            cases x with
            | here => rfl
            | there y => exact hε y)
          (Rename.ext_respectsRawIdx hρ)))
      (fun {Γ} A ws ε d o _sch body _ iht {_Δ} ρ ε' hswf htwf hε hρ =>
        .sat (iht ρ ε' hswf htwf hε hρ))
      h)

/-- Full `EncodeReady` transport along an embedding. -/
theorem encodeReady_of_embedding {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t)
    {body : InvTm Γ A}
    (h : EncodeReady (sig := sig) s.ws s.env s.domNext s.obsNext body) :
    EncodeReady (sig := sig) t.ws t.env t.domNext t.obsNext
      (InvTm.rename ρ body) := by
  have htwf : EncodeIx.WellFormed
      (⟨s.ws, t.env, s.domNext, s.obsNext⟩ : EncodeIx (sig := sig) Δ) := by
    have hws := emb.ws_eq
    have hdom := emb.domNext_eq
    have hobs := emb.obsNext_eq
    have htwf0 := emb.target_wf
    revert hws hdom hobs htwf0
    cases t
    intro hws hdom hobs htwf0
    simp only at hws hdom hobs
    subst hws; subst hdom; subst hobs
    exact htwf0
  rw [← emb.ws_eq, emb.domNext_eq, emb.obsNext_eq]
  exact encodeReady_of_embedding_aux h ρ t.env emb.source_wf htwf emb.env_commute
    emb.respectsRawIdx

/-! ## Peel-free certificate transport (legacy path) -/

theorem encodeReadyNoPeel_of_embedding {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t)
    {body : InvTm Γ A}
    (h : EncodeReadyNoPeel (sig := sig) s.ws s.env s.domNext s.obsNext body) :
    EncodeReadyNoPeel (sig := sig) t.ws t.env t.domNext t.obsNext
      (InvTm.rename ρ body) := by
  rw [← emb.ws_eq, emb.domNext_eq, emb.obsNext_eq]
  exact
    (EncodeReadyNoPeel.rec
      (motive_1 := fun {Γ} ws ε d o {A} body _ =>
        ∀ {Δ : Ctx sig} (ρ : Rename sig Γ Δ) (ε' : OriginEnv Δ),
          (∀ {B} (x : Var Γ B), ε' (ρ x) = ε x) →
          EncodeReadyNoPeel ws ε' d o (InvTm.rename ρ body))
      (motive_2 := fun {Γ} ws ε d o {A} f _ =>
        ∀ {Δ : Ctx sig} (ρ : Rename sig Γ Δ) (ε' : OriginEnv Δ),
          (∀ {B} (x : Var Γ B), ε' (ρ x) = ε x) →
          EncodeReadyFocNoPeel ws ε' d o (FocTm.rename ρ f))
      (fun {Γ} A e ws ε d o body hfr _ ih {_Δ} ρ ε' hε =>
        .moveStable hfr (ih ρ ε' hε))
      (fun {Γ} A e _ws _ε _d _o n hty {_Δ} ρ _ε' _hε =>
        .leftNever (n := NegNeu.rename ρ n) hty)
      (fun {Γ} A ws _ε _d _o n hfr {_Δ} ρ ε' _hε =>
        .abortFocus (n := NegNeu.rename ρ n) (ε := ε') hfr)
      (fun {Γ} ws _ε d o hfr {_Δ} ρ ε' _hε =>
        by simpa [InvTm.rename] using EncodeReadyNoPeel.rightUnit (ε := ε') hfr)
      (fun {Γ} L R ws ε d o t u hfr _ _ iht ihu {_Δ} ρ ε' hε =>
        .rightProd_pair hfr (iht ρ ε' hε) (ihu ρ ε' hε))
      (fun {Γ} L R ws ε d o f hfr _ ihf {_Δ} ρ ε' hε =>
        .rightProd_foc hfr (ihf ρ ε' hε))
      (fun {Γ} Arg Ret ws ε d o body hfr _ ihb {_Δ} ρ ε' hε =>
        .rightExp_lam hfr (ihb (Rename.ext ρ)
          (OriginEnv.weaken (A := Arg) ε' (.dom (sig := sig) d))
          (fun {B} x => by
            cases x with
            | here => rfl
            | there y => exact hε y)))
      (fun {Γ} Arg Ret ws ε d o f hfr _ ihf {_Δ} ρ ε' hε =>
        .rightExp_foc hfr (ihf ρ ε' hε))
      (fun {Γ} A ws ε d o f hfr _ ihf {_Δ} ρ ε' hε =>
        .focus hfr (ihf ρ ε' hε))
      (fun {Γ} A _ws _ε _d _o p {_Δ} ρ _ε' _hε => .pos)
      (fun {Γ} A _ws _ε _d _o n {_Δ} ρ _ε' _hε => .neg)
      (fun {Γ} P A ws ε d o n body _ iht {_Δ} ρ ε' hε =>
        .letPos (n := NegNeu.rename ρ n) (iht (Rename.ext ρ)
          (OriginEnv.weaken (A := P) ε' (.obs (sig := sig) o))
          (fun {B} x => by
            cases x with
            | here => rfl
            | there y => exact hε y)))
      (fun {Γ} A ws ε d o _sch body _ iht {_Δ} ρ ε' hε =>
        .sat (iht ρ ε' hε))
      h) ρ t.env emb.env_commute

/-- Peel-free `EncodeReady` transport (via `encodeReady_of_noPeel`). -/
theorem encodeReady_of_embedding_noPeel {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t)
    {body : InvTm Γ A}
    (h : EncodeReadyNoPeel (sig := sig) s.ws s.env s.domNext s.obsNext body) :
    EncodeReady (sig := sig) t.ws t.env t.domNext t.obsNext
      (InvTm.rename ρ body) :=
  encodeReady_of_noPeel (encodeReadyNoPeel_of_embedding emb h)

/-- `InvCert` transport for peel-free certificates. -/
theorem invCert_of_embedding_noPeel {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t)
    {body : InvTm Γ A}
    (h : EncodeReadyNoPeel (sig := sig) s.ws s.env s.domNext s.obsNext body) :
    InvCert t (InvTm.rename ρ body) :=
  encodeReady_of_embedding_noPeel emb h

/-- `Produced` transport for peel-free certificates. -/
def produced_of_embedding_noPeel {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t)
    (p : Produced s A)
    (h : EncodeReadyNoPeel (sig := sig) s.ws s.env s.domNext s.obsNext p.term) :
    Produced t A where
  term := InvTm.rename ρ p.term
  cert := invCert_of_embedding_noPeel emb h

/-- `InvCert` transport under a full embedding. -/
theorem invCert_of_embedding {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t)
    {body : InvTm Γ A}
    (h : EncodeReady (sig := sig) s.ws s.env s.domNext s.obsNext body) :
    InvCert t (InvTm.rename ρ body) :=
  encodeReady_of_embedding emb h

/-- `Produced` transport under a full embedding. -/
def produced_of_embedding {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t)
    (p : Produced s A) :
    Produced t A where
  term := InvTm.rename ρ p.term
  cert := invCert_of_embedding emb p.cert

/-! ## Exercise: λ, retained `letPos`, and outer coprod peel under weaken -/

def EmbedExSig : Signature where
  nBases := 1
  generators := #[]

private abbrev EmbedAtom : Object EmbedExSig.nBases := .base ⟨0, by decide⟩

private abbrev EmbedSum : Object EmbedExSig.nBases := .coprod EmbedAtom EmbedAtom

private abbrev EmbedFty : Object EmbedExSig.nBases := .exp EmbedAtom EmbedSum

def embedExEntry : EncodeIx (sig := EmbedExSig) Ctx.empty where
  ws := []
  env := OriginEnv.empty
  domNext := 0
  obsNext := 0

private theorem embedExEntry_wf : EncodeIx.WellFormed embedExEntry where
  env_wf := OriginEnv.WellFormed.empty
  env_bounded := fun x => nomatch x
  ws_bounded := fun he => by cases he
  ws_in_env := fun he => by cases he
  ws_nodup := List.nodup_nil
  ws_split_fresh := fun he _ => by cases he
  split_parent_live := fun x _ _ _ => nomatch x

/-- Goal `Atom → Atom` via λ (exercises `rightExp_lam` / dom-push). -/
def embedExLam : InvTm (sig := EmbedExSig) Ctx.empty (.exp EmbedAtom EmbedAtom) :=
  .lam (.foc (.pos (.done (.neu (.var .here)))))

theorem embedExLam_noPeel :
    EncodeReadyNoPeel (sig := EmbedExSig) embedExEntry.ws embedExEntry.env
      embedExEntry.domNext embedExEntry.obsNext embedExLam := by
  have hfr : forcedRule (sig := EmbedExSig) ([] : List (PosEntry EmbedExSig))
      (.exp EmbedAtom EmbedAtom) = .rightExp EmbedAtom EmbedAtom := rfl
  refine .rightExp_lam hfr ?_
  change EncodeReadyNoPeel
    (pushPos ([] : List (PosEntry EmbedExSig)) (.dom (sig := EmbedExSig) 0) EmbedAtom)
    (OriginEnv.weaken (A := EmbedAtom) OriginEnv.empty (.dom (sig := EmbedExSig) 0))
    1 0 _
  have hpush :
      pushPos ([] : List (PosEntry EmbedExSig)) (.dom (sig := EmbedExSig) 0) EmbedAtom =
        [{ origin := .dom (sig := EmbedExSig) 0, ty := EmbedAtom }] := by
    simp [pushPos, EmbedAtom, objectPolarity, List.mergeSort_singleton]
  rw [hpush]
  let e : PosEntry EmbedExSig := ⟨.dom (sig := EmbedExSig) 0, EmbedAtom⟩
  have hfrM : forcedRule (sig := EmbedExSig) [e] EmbedAtom = .moveStable e := rfl
  have hfrF : forcedRule (sig := EmbedExSig) ([] : List (PosEntry EmbedExSig))
      EmbedAtom = .focus := rfl
  exact .moveStable hfrM (.focus hfrF (.pos (p := .neu (.var .here))))

def embedExLamProduced : Produced embedExEntry (.exp EmbedAtom EmbedAtom) where
  term := embedExLam
  cert := encodeReady_of_noPeel embedExLam_noPeel

def embedExLamProduced_weaken : Produced
    ⟨embedExEntry.ws,
      OriginEnv.weaken (A := EmbedAtom) embedExEntry.env
        (.hyp (sig := EmbedExSig) 0),
      embedExEntry.domNext, embedExEntry.obsNext⟩
    (.exp EmbedAtom EmbedAtom) :=
  produced_of_embedding_noPeel
    (encodeIxEmbedding_weaken embedExEntry (.hyp (sig := EmbedExSig) 0)
      embedExEntry_wf
      (OriginEnv.Fresh.empty _)
      (Origin.counterBounded_hyp (sig := EmbedExSig) 0 0 0)
      (fun _ => OriginEnv.Fresh.empty _)
      (fun _ _ heq => by cases heq)
      (fun he => by cases he))
    embedExLamProduced embedExLam_noPeel

def embedExΓBase : Ctx EmbedExSig := Ctx.empty ▻ EmbedAtom

def embedExStateBase : EncodeIx (sig := EmbedExSig) embedExΓBase where
  ws := []
  env := OriginEnv.weaken (A := EmbedAtom) OriginEnv.empty (.hyp (sig := EmbedExSig) 0)
  domNext := 0
  obsNext := 0

private theorem embedExStateBase_wf : EncodeIx.WellFormed embedExStateBase :=
  EncodeIx.WellFormed.weaken_unused (B := EmbedAtom) embedExEntry_wf
    (.hyp (sig := EmbedExSig) 0)
    (OriginEnv.Fresh.empty _)
    (Origin.counterBounded_hyp (sig := EmbedExSig) 0 0 0)
    (fun _ => OriginEnv.Fresh.empty _)
    (fun _ _ heq => by cases heq)
    (fun he => by cases he)

/-- Retained `letPos` of a base hyp (exercises `EncodeReadyFoc.letPos` / obs-push). -/
def embedExLetPosBase : InvTm embedExΓBase EmbedAtom :=
  .foc (.letPos (.var .here) (.foc (.pos (.done (.neu (.var .here))))))

theorem embedExLetPosBase_noPeel :
    EncodeReadyNoPeel (sig := EmbedExSig) embedExStateBase.ws embedExStateBase.env
      embedExStateBase.domNext embedExStateBase.obsNext embedExLetPosBase := by
  have hfrF : forcedRule (sig := EmbedExSig) ([] : List (PosEntry EmbedExSig))
      EmbedAtom = .focus := rfl
  refine .focus hfrF ?_
  refine .letPos ?_
  change EncodeReadyNoPeel
    (pushPos ([] : List (PosEntry EmbedExSig)) (.obs (sig := EmbedExSig) 0) EmbedAtom)
    (OriginEnv.weaken (A := EmbedAtom) embedExStateBase.env (.obs (sig := EmbedExSig) 0))
    0 1 _
  have hpush :
      pushPos ([] : List (PosEntry EmbedExSig)) (.obs (sig := EmbedExSig) 0) EmbedAtom =
        [{ origin := .obs (sig := EmbedExSig) 0, ty := EmbedAtom }] := by
    simp [pushPos, EmbedAtom, objectPolarity, List.mergeSort_singleton]
  rw [hpush]
  let e : PosEntry EmbedExSig := ⟨.obs (sig := EmbedExSig) 0, EmbedAtom⟩
  have hfrM : forcedRule (sig := EmbedExSig) [e] EmbedAtom = .moveStable e := rfl
  exact .moveStable hfrM (.focus hfrF (.pos (p := .neu (.var .here))))

def embedExTargetBase : EncodeIx (sig := EmbedExSig) (embedExΓBase ▻ EmbedAtom) :=
  ⟨embedExStateBase.ws,
    OriginEnv.weaken (A := EmbedAtom) embedExStateBase.env
      (.split (.hyp (sig := EmbedExSig) 0) false),
    embedExStateBase.domNext, embedExStateBase.obsNext⟩

theorem embedEx_weaken_embedding :
    EncodeIxEmbedding (Rename.weaken (A := EmbedAtom))
      embedExStateBase embedExTargetBase :=
  encodeIxEmbedding_weaken embedExStateBase (.split (.hyp (sig := EmbedExSig) 0) false)
    embedExStateBase_wf
    (by
      intro A x
      cases x with
      | here =>
          simp [embedExStateBase, OriginEnv.weaken, OriginEnv.snoc]
      | there y => nomatch y)
    (by
      change Origin.counterBounded
        (.split (.hyp (sig := EmbedExSig) 0) false) 0 0
      exact Origin.counterBounded_hyp (sig := EmbedExSig) 0 0 0)
    (by
      intro side A x
      cases x with
      | here =>
          simp [embedExStateBase, OriginEnv.weaken, OriginEnv.snoc]
      | there y => nomatch y)
    (fun p side heq => by
      cases heq
      exact ⟨EmbedAtom, .here, by simp [embedExStateBase, OriginEnv.weaken, OriginEnv.snoc]⟩)
    (fun he => by cases he)

def embedExLetPosProduced : Produced embedExStateBase EmbedAtom where
  term := embedExLetPosBase
  cert := encodeReady_of_noPeel embedExLetPosBase_noPeel

def embedExLetPosProduced_weaken : Produced embedExTargetBase EmbedAtom :=
  produced_of_embedding_noPeel embedEx_weaken_embedding
    embedExLetPosProduced embedExLetPosBase_noPeel

/-! ## Vertical-slice exercise: λ + `letPos` + outer peel -/

/-- Context with negative function hyp `f : Atom → Atom + Atom`. -/
def embedExSliceHyps : Array (Object EmbedExSig.nBases) := #[EmbedFty]

def embedExSliceΓ : Ctx EmbedExSig := Ctx.ofHyps (sig := EmbedExSig) embedExSliceHyps

def embedExSliceEntry : EncodeIx (sig := EmbedExSig) embedExSliceΓ :=
  EncodeIx.entry (sig := EmbedExSig) embedExSliceHyps

private theorem embedExSliceEntry_wf : EncodeIx.WellFormed embedExSliceEntry :=
  EncodeIx.entry_wellFormed embedExSliceHyps

def embedExSliceF : Var embedExSliceΓ EmbedFty := .here

def embedExSliceAfterDom : EncodeIx (sig := EmbedExSig) (embedExSliceΓ ▻ EmbedAtom) :=
  embedExSliceEntry.bindDom EmbedAtom

def embedExSliceApp :
    NegNeu (sig := EmbedExSig) (embedExSliceΓ ▻ EmbedAtom) EmbedSum :=
  .app (.var (.there embedExSliceF))
    (.foc (.pos (.done (.neu (.var .here)))))

def embedExSliceAfterObs :
    EncodeIx (sig := EmbedExSig) (embedExSliceΓ ▻ EmbedAtom ▻ EmbedSum) :=
  embedExSliceAfterDom.pop.bindObs EmbedSum

def embedExSliceBranchL :
    InvTm (sig := EmbedExSig) (embedExSliceΓ ▻ EmbedAtom ▻ EmbedSum ▻ EmbedAtom)
      EmbedAtom :=
  .foc (.pos (.done (.neu (.var .here))))

def embedExSliceBranchR :
    InvTm (sig := EmbedExSig) (embedExSliceΓ ▻ EmbedAtom ▻ EmbedSum ▻ EmbedAtom)
      EmbedAtom :=
  .foc (.pos (.done (.neu (.var .here))))

def embedExSliceCaseBody :
    InvTm (sig := EmbedExSig) (embedExSliceΓ ▻ EmbedAtom ▻ EmbedSum) EmbedAtom :=
  .case (.var .here) embedExSliceBranchL embedExSliceBranchR

def embedExSliceRetained :
    InvTm (sig := EmbedExSig) (embedExSliceΓ ▻ EmbedAtom) EmbedAtom :=
  .foc (.letPos embedExSliceApp embedExSliceCaseBody)

def embedExSliceTerm :
    InvTm (sig := EmbedExSig) embedExSliceΓ (.exp EmbedAtom EmbedAtom) :=
  .lam embedExSliceRetained

private theorem embedExSliceEntry_ws_nil : embedExSliceEntry.ws = [] := by
  simp only [embedExSliceEntry, EncodeIx.entry, embedExSliceHyps, OriginEnv.posWorklist,
    OriginEnv.posCollect]
  native_decide

private theorem embedExSliceAfterDom_ws :
    embedExSliceAfterDom.ws =
      [{ origin := .dom (sig := EmbedExSig) 0, ty := EmbedAtom }] := by
  simp only [embedExSliceAfterDom, EncodeIx.bindDom, embedExSliceEntry, EncodeIx.entry,
    embedExSliceHyps, pushPos]
  native_decide

private theorem embedExSliceAfterDom_pop_ws_nil :
    embedExSliceAfterDom.pop.ws = [] := by
  simp only [EncodeIx.pop, embedExSliceAfterDom_ws, List.tail_cons]

private def embedExSliceObsEntry : PosEntry EmbedExSig :=
  ⟨.obs (sig := EmbedExSig) 0, EmbedSum⟩

private theorem embedExSlice_bindObs_ws :
    embedExSliceAfterObs.ws = [embedExSliceObsEntry] := by
  simp only [embedExSliceAfterObs, EncodeIx.bindObs, EncodeIx.pop, embedExSliceAfterDom_ws,
    pushPos, List.tail_cons, embedExSliceObsEntry]
  native_decide

private theorem embedExSlice_env_here_is_obs :
    embedExSliceAfterObs.env
        (Var.here : Var (sig := EmbedExSig)
          (embedExSliceΓ ▻ EmbedAtom ▻ EmbedSum) EmbedSum) =
      (.obs (sig := EmbedExSig) 0 : Origin EmbedExSig) := by
  simp [embedExSliceAfterObs, EncodeIx.bindObs, EncodeIx.pop, OriginEnv.weaken, OriginEnv.snoc,
    embedExSliceAfterDom, EncodeIx.bindDom, embedExSliceEntry, EncodeIx.entry]

private theorem embedExSlice_splitL_ws :
    (embedExSliceAfterObs.splitL embedExSliceObsEntry EmbedAtom).ws =
      [{ origin := .split (.obs (sig := EmbedExSig) 0) false, ty := EmbedAtom }] := by
  simp only [EncodeIx.splitL, embedExSlice_bindObs_ws, pushPos, List.tail_cons,
    embedExSliceObsEntry]
  native_decide

private theorem embedExSlice_splitR_ws :
    (embedExSliceAfterObs.splitR embedExSliceObsEntry EmbedAtom).ws =
      [{ origin := .split (.obs (sig := EmbedExSig) 0) true, ty := EmbedAtom }] := by
  simp only [EncodeIx.splitR, embedExSlice_bindObs_ws, pushPos, List.tail_cons,
    embedExSliceObsEntry]
  native_decide

private theorem embedExSlice_branchL_cert :
    InvCert (embedExSliceAfterObs.splitL embedExSliceObsEntry EmbedAtom)
      embedExSliceBranchL := by
  set s := embedExSliceAfterObs.splitL embedExSliceObsEntry EmbedAtom
  have hws := embedExSlice_splitL_ws
  have hnil : EncodeReady (sig := EmbedExSig) [] s.env s.domNext s.obsNext
      embedExSliceBranchL :=
    .focus (by rfl) .pos
  have hfr : forcedRule (sig := EmbedExSig)
      ([{ origin := .split (.obs (sig := EmbedExSig) 0) false, ty := EmbedAtom }] :
        List (PosEntry EmbedExSig)) EmbedAtom =
      .moveStable ⟨.split (.obs (sig := EmbedExSig) 0) false, EmbedAtom⟩ := rfl
  have hmove : EncodeReady (sig := EmbedExSig)
      [{ origin := .split (.obs (sig := EmbedExSig) 0) false, ty := EmbedAtom }]
      s.env s.domNext s.obsNext embedExSliceBranchL :=
    EncodeReady.moveStable hfr hnil
  change EncodeReady s.ws s.env s.domNext s.obsNext embedExSliceBranchL
  rw [hws]
  exact hmove

private theorem embedExSlice_branchR_cert :
    InvCert (embedExSliceAfterObs.splitR embedExSliceObsEntry EmbedAtom)
      embedExSliceBranchR := by
  set s := embedExSliceAfterObs.splitR embedExSliceObsEntry EmbedAtom
  have hws := embedExSlice_splitR_ws
  have hnil : EncodeReady (sig := EmbedExSig) [] s.env s.domNext s.obsNext
      embedExSliceBranchR :=
    .focus (by rfl) .pos
  have hfr : forcedRule (sig := EmbedExSig)
      ([{ origin := .split (.obs (sig := EmbedExSig) 0) true, ty := EmbedAtom }] :
        List (PosEntry EmbedExSig)) EmbedAtom =
      .moveStable ⟨.split (.obs (sig := EmbedExSig) 0) true, EmbedAtom⟩ := rfl
  have hmove : EncodeReady (sig := EmbedExSig)
      [{ origin := .split (.obs (sig := EmbedExSig) 0) true, ty := EmbedAtom }]
      s.env s.domNext s.obsNext embedExSliceBranchR :=
    EncodeReady.moveStable hfr hnil
  change EncodeReady s.ws s.env s.domNext s.obsNext embedExSliceBranchR
  rw [hws]
  exact hmove

private theorem embedExSlice_peel_case :
    peelCaseOuter (sig := EmbedExSig)
      embedExSliceAfterObs.env
      embedExSliceObsEntry.origin
      embedExSliceCaseBody =
      some ⟨EmbedAtom, EmbedAtom, .var .here, embedExSliceBranchL, embedExSliceBranchR⟩ := by
  simpa [embedExSliceCaseBody, embedExSliceObsEntry] using
    (peelCaseOuter_case_var_hit (sig := EmbedExSig)
      embedExSliceAfterObs.env
      (.obs (sig := EmbedExSig) 0)
      (Var.here : Var (sig := EmbedExSig)
        (embedExSliceΓ ▻ EmbedAtom ▻ EmbedSum) EmbedSum)
      embedExSliceBranchL embedExSliceBranchR embedExSlice_env_here_is_obs)

private theorem embedExSlice_caseBody_invCert :
    InvCert embedExSliceAfterObs embedExSliceCaseBody := by
  have hws := embedExSlice_bindObs_ws
  have hL : EncodeReady (sig := EmbedExSig)
      (pushPos ([] : List (PosEntry EmbedExSig))
        (.split embedExSliceObsEntry.origin false) EmbedAtom)
      (OriginEnv.weaken (A := EmbedAtom) embedExSliceAfterObs.env
        (.split embedExSliceObsEntry.origin false))
      embedExSliceAfterObs.domNext
      embedExSliceAfterObs.obsNext
      embedExSliceBranchL := by
    simpa [EncodeIx.splitL, hws, InvCert, List.tail_cons] using embedExSlice_branchL_cert
  have hR : EncodeReady (sig := EmbedExSig)
      (pushPos ([] : List (PosEntry EmbedExSig))
        (.split embedExSliceObsEntry.origin true) EmbedAtom)
      (OriginEnv.weaken (A := EmbedAtom) embedExSliceAfterObs.env
        (.split embedExSliceObsEntry.origin true))
      embedExSliceAfterObs.domNext
      embedExSliceAfterObs.obsNext
      embedExSliceBranchR := by
    simpa [EncodeIx.splitR, hws, InvCert, List.tail_cons] using embedExSlice_branchR_cert
  have hfr : forcedRule (sig := EmbedExSig) [embedExSliceObsEntry] EmbedAtom =
      .leftCoprod embedExSliceObsEntry EmbedAtom EmbedAtom := by
    simp [forcedRule, embedExSliceObsEntry, EmbedSum]
  change EncodeReady embedExSliceAfterObs.ws
    embedExSliceAfterObs.env
    embedExSliceAfterObs.domNext
    embedExSliceAfterObs.obsNext embedExSliceCaseBody
  rw [hws]
  exact
    (invCert_leftCoprod_peel (sig := EmbedExSig) (ws := []) embedExSliceObsEntry
      (.var (Var.here : Var (sig := EmbedExSig)
        (embedExSliceΓ ▻ EmbedAtom ▻ EmbedSum) EmbedSum))
      embedExSliceBranchL embedExSliceBranchR embedExSliceCaseBody
      hfr embedExSlice_peel_case hL hR)

private theorem embedExSlice_retained_at_poppedDom :
    InvCert embedExSliceAfterDom.pop embedExSliceRetained := by
  have hfr : forcedRule (sig := EmbedExSig) embedExSliceAfterDom.pop.ws EmbedAtom =
      .focus := by
    simp only [embedExSliceAfterDom_pop_ws_nil, forcedRule]
  refine invCert_focus embedExSliceAfterDom.pop (.letPos embedExSliceApp embedExSliceCaseBody)
    hfr ?_
  have hnil := embedExSliceAfterDom_pop_ws_nil
  have hobs : embedExSliceAfterDom.pop.obsNext = 0 := rfl
  have ht : EncodeReady (sig := EmbedExSig)
      (pushPos ([] : List (PosEntry EmbedExSig)) (.obs (sig := EmbedExSig) 0) EmbedSum)
      (OriginEnv.weaken (A := EmbedSum) embedExSliceAfterDom.pop.env
        (.obs (sig := EmbedExSig) 0))
      embedExSliceAfterDom.pop.domNext 1 embedExSliceCaseBody := by
    simpa [InvCert, embedExSliceAfterObs, EncodeIx.bindObs, hnil, hobs] using
      embedExSlice_caseBody_invCert
  rw [hnil, hobs]
  exact EncodeReadyFoc.letPos (n := embedExSliceApp) ht

private theorem embedExSlice_retained_at_afterDom :
    InvCert embedExSliceAfterDom embedExSliceRetained := by
  have hws := embedExSliceAfterDom_ws
  have hbody : EncodeReady (sig := EmbedExSig) [] embedExSliceAfterDom.env
      embedExSliceAfterDom.domNext embedExSliceAfterDom.obsNext embedExSliceRetained := by
    simpa [EncodeIx.pop, hws, InvCert] using embedExSlice_retained_at_poppedDom
  have hfr : forcedRule (sig := EmbedExSig)
      ([{ origin := .dom (sig := EmbedExSig) 0, ty := EmbedAtom }] :
        List (PosEntry EmbedExSig)) EmbedAtom =
      .moveStable ⟨.dom (sig := EmbedExSig) 0, EmbedAtom⟩ := rfl
  change EncodeReady embedExSliceAfterDom.ws embedExSliceAfterDom.env
    embedExSliceAfterDom.domNext embedExSliceAfterDom.obsNext embedExSliceRetained
  rw [hws]
  exact EncodeReady.moveStable (e := ⟨.dom (sig := EmbedExSig) 0, EmbedAtom⟩)
    (ws := ([] : List (PosEntry EmbedExSig))) hfr hbody

theorem embedExSliceTerm_ready :
    EncodeReady (sig := EmbedExSig) embedExSliceEntry.ws embedExSliceEntry.env
      embedExSliceEntry.domNext embedExSliceEntry.obsNext embedExSliceTerm := by
  have hfr : forcedRule (sig := EmbedExSig) embedExSliceEntry.ws
      (.exp EmbedAtom EmbedAtom) = .rightExp EmbedAtom EmbedAtom := by
    simp only [embedExSliceEntry_ws_nil, forcedRule]
  refine invCert_lam (sig := EmbedExSig) embedExSliceEntry embedExSliceRetained hfr ?_
  simpa [embedExSliceAfterDom] using embedExSlice_retained_at_afterDom

def embedExSliceProduced : Produced embedExSliceEntry (.exp EmbedAtom EmbedAtom) where
  term := embedExSliceTerm
  cert := embedExSliceTerm_ready

/-- Unused-binder weaken of the slice entry (split of the live function hyp). -/
def embedExSliceTarget : EncodeIx (sig := EmbedExSig) (embedExSliceΓ ▻ EmbedAtom) :=
  ⟨embedExSliceEntry.ws,
    OriginEnv.weaken (A := EmbedAtom) embedExSliceEntry.env
      (.split (.hyp (sig := EmbedExSig) 0) false),
    embedExSliceEntry.domNext, embedExSliceEntry.obsNext⟩

theorem embedExSlice_weaken_embedding :
    EncodeIxEmbedding (Rename.weaken (A := EmbedAtom))
      embedExSliceEntry embedExSliceTarget :=
  encodeIxEmbedding_weaken embedExSliceEntry
    (.split (.hyp (sig := EmbedExSig) 0) false)
    embedExSliceEntry_wf
    (by
      intro A x
      have : embedExSliceEntry.env x = .hyp (sig := EmbedExSig) 0 := by
        simp only [embedExSliceEntry, EncodeIx.entry, OriginEnv.ofHyps, embedExSliceHyps]
        cases x with
        | here => rfl
        | there y => nomatch y
      intro hx
      simp [this] at hx)
    (Origin.counterBounded_hyp (sig := EmbedExSig) 0 0 0)
    (by
      intro side A x
      have : embedExSliceEntry.env x = .hyp (sig := EmbedExSig) 0 := by
        simp only [embedExSliceEntry, EncodeIx.entry, OriginEnv.ofHyps, embedExSliceHyps]
        cases x with
        | here => rfl
        | there y => nomatch y
      intro hx
      simp [this] at hx)
    (fun p side heq => by
      cases heq
      exact ⟨EmbedFty, .here, by
        simp [embedExSliceEntry, EncodeIx.entry, OriginEnv.ofHyps, embedExSliceHyps]⟩)
    (fun he => by
      rw [embedExSliceEntry_ws_nil] at he
      cases he)

/-- Full readiness + `Produced` transport for the vertical-slice term under weaken. -/
theorem embedExSlice_ready_of_embedding :
    EncodeReady (sig := EmbedExSig) embedExSliceTarget.ws embedExSliceTarget.env
      embedExSliceTarget.domNext embedExSliceTarget.obsNext
      (InvTm.rename (Rename.weaken (A := EmbedAtom)) embedExSliceTerm) :=
  encodeReady_of_embedding embedExSlice_weaken_embedding embedExSliceTerm_ready

def embedExSliceProduced_weaken : Produced embedExSliceTarget
    (.exp EmbedAtom EmbedAtom) :=
  produced_of_embedding embedExSlice_weaken_embedding embedExSliceProduced

/-! ## Lookup naturality under embedding constructors -/

/-- Identity embedding (same state). -/
theorem encodeIxEmbedding_id {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (hwf : EncodeIx.WellFormed s) :
    EncodeIxEmbedding (Rename.id (Γ := Γ)) s s where
  env_commute := fun _ => rfl
  source_wf := hwf
  target_wf := hwf
  respectsRawIdx := Rename.id_respectsRawIdx
  ws_eq := rfl
  domNext_eq := rfl
  obsNext_eq := rfl

private theorem embedExStateBase_fresh_obs :
    OriginEnv.Fresh embedExStateBase.env (.obs (sig := EmbedExSig) 0) :=
  embedExStateBase_wf.fresh_obs

private theorem embedExStateBase_fresh_dom :
    OriginEnv.Fresh embedExStateBase.env (.dom (sig := EmbedExSig) 0) :=
  embedExStateBase_wf.fresh_dom

private theorem embedExStateBase_fresh_split (side : Bool) :
    OriginEnv.Fresh embedExStateBase.env
      (.split (.hyp (sig := EmbedExSig) 0) side) := by
  intro A x
  cases x with
  | here => simp [embedExStateBase, OriginEnv.weaken, OriginEnv.snoc]
  | there y => nomatch y

/-- `find?` for the base hyp survives unused-binder weaken. -/
theorem embedEx_find?_weaken :
    let o := Origin.hyp (sig := EmbedExSig) 0
    OriginEnv.find? embedExStateBase.env o = some ⟨EmbedAtom, .here⟩ ∧
    OriginEnv.find? embedExTargetBase.env o =
      some ⟨EmbedAtom, Rename.weaken (A := EmbedAtom) (.here : Var embedExΓBase EmbedAtom)⟩ := by
  refine ⟨?_, ?_⟩
  · exact OriginEnv.find?_eq_some_of_wellFormed _ _ _ embedExStateBase_wf.env_wf rfl
  · exact EncodeIxEmbedding.find?_eq embedEx_weaken_embedding _ _
      (OriginEnv.find?_eq_some_of_wellFormed _ _ _ embedExStateBase_wf.env_wf rfl)

/-- `find?` naturality for `extPush`. -/
theorem embedEx_find?_extPush
    (h : OriginEnv.find? embedExStateBase.env (.hyp (sig := EmbedExSig) 0) =
      some ⟨EmbedAtom, .here⟩) :
    OriginEnv.find? (OriginEnv.weaken (A := EmbedAtom) embedExStateBase.env
        (.split (.hyp (sig := EmbedExSig) 0) true))
      (.hyp (sig := EmbedExSig) 0) =
      some ⟨EmbedAtom, Rename.ext (Rename.id (Γ := embedExΓBase)) (.there .here)⟩ :=
  EncodeIxEmbedding.find?_eq
    (EncodeIxEmbedding.extPush (P := EmbedAtom)
      (encodeIxEmbedding_id embedExStateBase embedExStateBase_wf)
      (.split (.hyp (sig := EmbedExSig) 0) true)
      (embedExStateBase_fresh_split true) (embedExStateBase_fresh_split true)
      (Origin.counterBounded_hyp (sig := EmbedExSig) 0 0 0)
      (fun p side heq => by
        cases heq
        exact ⟨EmbedAtom, .here, by simp [embedExStateBase, OriginEnv.weaken, OriginEnv.snoc]⟩)
      (fun he => by cases he))
    (.hyp (sig := EmbedExSig) 0) (.there .here)
    (OriginEnv.find?_weaken_there embedExStateBase.env
      (.split (.hyp (sig := EmbedExSig) 0) true) (.hyp (sig := EmbedExSig) 0) .here
      embedExStateBase_wf.env_wf (embedExStateBase_fresh_split true) h)

/-- `find?` naturality for `extSplit`. -/
theorem embedEx_find?_extSplit
    (h : OriginEnv.find? embedExStateBase.env (.hyp (sig := EmbedExSig) 0) =
      some ⟨EmbedAtom, .here⟩) :
    OriginEnv.find? (OriginEnv.weaken (A := EmbedAtom) embedExStateBase.env
        (.split (.hyp (sig := EmbedExSig) 0) false))
      (.hyp (sig := EmbedExSig) 0) =
      some ⟨EmbedAtom, Rename.ext (Rename.id (Γ := embedExΓBase)) (.there .here)⟩ :=
  EncodeIxEmbedding.find?_eq
    (EncodeIxEmbedding.extSplit (P := EmbedAtom)
      (encodeIxEmbedding_id embedExStateBase embedExStateBase_wf)
      (.hyp (sig := EmbedExSig) 0) false
      (embedExStateBase_fresh_split false) (embedExStateBase_fresh_split false)
      (Origin.counterBounded_hyp (sig := EmbedExSig) 0 0 0)
      ⟨EmbedAtom, .here, by simp [embedExStateBase, OriginEnv.weaken, OriginEnv.snoc]⟩
      (fun he _ => by cases he))
    (.hyp (sig := EmbedExSig) 0) (.there .here)
    (OriginEnv.find?_weaken_there embedExStateBase.env
      (.split (.hyp (sig := EmbedExSig) 0) false) (.hyp (sig := EmbedExSig) 0) .here
      embedExStateBase_wf.env_wf (embedExStateBase_fresh_split false) h)

/-- `find?` naturality for `extObs`. -/
theorem embedEx_find?_extObs
    (h : OriginEnv.find? embedExStateBase.env (.hyp (sig := EmbedExSig) 0) =
      some ⟨EmbedAtom, .here⟩) :
    OriginEnv.find? (OriginEnv.weaken (A := EmbedAtom) embedExStateBase.env
        (.obs (sig := EmbedExSig) 0))
      (.hyp (sig := EmbedExSig) 0) =
      some ⟨EmbedAtom, Rename.ext (Rename.id (Γ := embedExΓBase)) (.there .here)⟩ :=
  EncodeIxEmbedding.find?_eq
    (EncodeIxEmbedding.extObs (P := EmbedAtom)
      (encodeIxEmbedding_id embedExStateBase embedExStateBase_wf))
    (.hyp (sig := EmbedExSig) 0) (.there .here)
    (OriginEnv.find?_weaken_there embedExStateBase.env
      (.obs (sig := EmbedExSig) 0) (.hyp (sig := EmbedExSig) 0) .here
      embedExStateBase_wf.env_wf embedExStateBase_fresh_obs h)

/-- `find?` naturality for `extDom`. -/
theorem embedEx_find?_extDom
    (h : OriginEnv.find? embedExStateBase.env (.hyp (sig := EmbedExSig) 0) =
      some ⟨EmbedAtom, .here⟩) :
    OriginEnv.find? (OriginEnv.weaken (A := EmbedAtom) embedExStateBase.env
        (.dom (sig := EmbedExSig) 0))
      (.hyp (sig := EmbedExSig) 0) =
      some ⟨EmbedAtom, Rename.ext (Rename.id (Γ := embedExΓBase)) (.there .here)⟩ :=
  EncodeIxEmbedding.find?_eq
    (EncodeIxEmbedding.extDom (Arg := EmbedAtom)
      (encodeIxEmbedding_id embedExStateBase embedExStateBase_wf))
    (.hyp (sig := EmbedExSig) 0) (.there .here)
    (OriginEnv.find?_weaken_there embedExStateBase.env
      (.dom (sig := EmbedExSig) 0) (.hyp (sig := EmbedExSig) 0) .here
      embedExStateBase_wf.env_wf embedExStateBase_fresh_dom h)

/-- Lookup + hit transport for `leftCoprod_unitEta` under an embedding. -/
theorem EncodeIxEmbedding.unitEta_find? {Γ Δ : Ctx sig}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t)
    (o : Origin sig) {L R : Object sig.nBases} (x : Var Γ (.coprod L R))
    (hfind : OriginEnv.find? s.env o = some ⟨.coprod L R, x⟩)
    (hit : (s.env x == o) = true) :
    OriginEnv.find? t.env o = some ⟨.coprod L R, ρ x⟩ ∧
      (t.env (ρ x) == o) = true :=
  ⟨EncodeIxEmbedding.find?_eq emb o x hfind,
    by
      have hx := beq_iff_eq.mp hit
      exact beq_iff_eq.mpr (by simpa [emb.env_commute x] using hx)⟩

/-- Peel success packaged via `PeelCase.rename`. -/
theorem EncodeIxEmbedding.peelCase_rename {Γ Δ : Ctx sig} {C : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t)
    (o : Origin sig) (tm : InvTm Γ C) (p : PeelCase Γ C)
    (h : peelCaseOuter s.env o tm = some p.toSigma) :
    peelCaseOuter t.env o (InvTm.rename ρ tm) = some (p.rename ρ).toSigma := by
  rcases p with ⟨A, B, n, tL, tR⟩
  simpa [PeelCase.toSigma, PeelCase.rename] using
    peelCaseOuter_rename ρ s.env t.env o tm emb.env_commute emb.respectsRawIdx h

end Equality
end Gimbal
