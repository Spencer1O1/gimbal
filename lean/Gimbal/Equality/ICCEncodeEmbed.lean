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
* `source_wf` / `target_wf` — live origins are pairwise distinct on both sides
  (so `find?` recovers a unique carrier; a fresher target binder cannot steal
  a mapped source origin)
* `ws_eq` — source worklist equals target worklist (origins are absolute;
  fresh target binders may exist but need not occur in this shared worklist)
* `domNext_eq` / `obsNext_eq` — counter evolution is explicit (not reset)
-/
structure EncodeIxEmbedding {Γ Δ : Ctx sig}
    (ρ : Rename sig Γ Δ)
    (s : EncodeIx (sig := sig) Γ)
    (t : EncodeIx (sig := sig) Δ) : Prop where
  env_commute : ∀ {A : Object sig.nBases} (x : Var Γ A), t.env (ρ x) = s.env x
  source_wf : OriginEnv.WellFormed s.env
  target_wf : OriginEnv.WellFormed t.env
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
  exact OriginEnv.find?_eq_some_of_wellFormed t.env o (ρ x) emb.target_wf this

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
  exact emb.source_wf.injective x y this

/-! ## Unused-binder weaken embedding -/

/--
Unused newest binder: `Rename.weaken` into `OriginEnv.weaken … o` with
identical worklist and counters.

Requires `o` fresh in the source environment (otherwise the target is not
well-formed / `find?` would prefer the colliding newest binder).
-/
theorem encodeIxEmbedding_weaken {Γ : Ctx sig} {B : Object sig.nBases}
    (s : EncodeIx (sig := sig) Γ) (o : Origin sig)
    (hwf : OriginEnv.WellFormed s.env) (hfresh : OriginEnv.Fresh s.env o) :
    EncodeIxEmbedding (Rename.weaken (A := B)) s
      ⟨s.ws, OriginEnv.weaken (A := B) s.env o, s.domNext, s.obsNext⟩ where
  env_commute := by
    intro A x
    simp [Rename.weaken, OriginEnv.weaken, OriginEnv.snoc]
  source_wf := hwf
  target_wf := OriginEnv.WellFormed.weaken s.env o hwf hfresh
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
    (hsFresh : OriginEnv.Fresh s.env o) (htFresh : OriginEnv.Fresh t.env o) :
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
  source_wf := OriginEnv.WellFormed.weaken s.env o emb.source_wf hsFresh
  target_wf := OriginEnv.WellFormed.weaken t.env o emb.target_wf htFresh
  respectsRawIdx := Rename.ext_respectsRawIdx emb.respectsRawIdx
  ws_eq := by simp [emb.ws_eq]
  domNext_eq := emb.domNext_eq
  obsNext_eq := emb.obsNext_eq

/-- Obs-push at the shared `obsNext` (stepped on both sides). -/
theorem EncodeIxEmbedding.extObs {Γ Δ : Ctx sig} {P : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t)
    (hsFresh : OriginEnv.Fresh s.env (.obs (sig := sig) s.obsNext))
    (htFresh : OriginEnv.Fresh t.env (.obs (sig := sig) t.obsNext)) :
    EncodeIxEmbedding (Rename.ext ρ)
      ⟨pushPos s.ws (.obs (sig := sig) s.obsNext) P,
        OriginEnv.weaken (A := P) s.env (.obs (sig := sig) s.obsNext),
        s.domNext, s.obsNext + 1⟩
      ⟨pushPos t.ws (.obs (sig := sig) t.obsNext) P,
        OriginEnv.weaken (A := P) t.env (.obs (sig := sig) t.obsNext),
        t.domNext, t.obsNext + 1⟩ := by
  have hobs : t.obsNext = s.obsNext := emb.obsNext_eq
  have hdom : t.domNext = s.domNext := emb.domNext_eq
  refine
    { env_commute := ?_
      source_wf := OriginEnv.WellFormed.weaken s.env (.obs (sig := sig) s.obsNext)
        emb.source_wf hsFresh
      target_wf := OriginEnv.WellFormed.weaken t.env (.obs (sig := sig) t.obsNext)
        emb.target_wf htFresh
      respectsRawIdx := Rename.ext_respectsRawIdx emb.respectsRawIdx
      ws_eq := ?_
      domNext_eq := by simp [hdom]
      obsNext_eq := by simp [hobs] }
  · intro A x
    cases x with
    | here => simp [Rename.ext, OriginEnv.weaken, OriginEnv.snoc, hobs]
    | there y =>
        simpa [Rename.ext, OriginEnv.weaken, OriginEnv.snoc] using emb.env_commute y
  · simp [hobs, emb.ws_eq]

/-- Dom-push at the shared `domNext` (stepped on both sides). -/
theorem EncodeIxEmbedding.extDom {Γ Δ : Ctx sig} {Arg : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t)
    (hsFresh : OriginEnv.Fresh s.env (.dom (sig := sig) s.domNext))
    (htFresh : OriginEnv.Fresh t.env (.dom (sig := sig) t.domNext)) :
    EncodeIxEmbedding (Rename.ext ρ)
      ⟨pushPos s.ws (.dom (sig := sig) s.domNext) Arg,
        OriginEnv.weaken (A := Arg) s.env (.dom (sig := sig) s.domNext),
        s.domNext + 1, s.obsNext⟩
      ⟨pushPos t.ws (.dom (sig := sig) t.domNext) Arg,
        OriginEnv.weaken (A := Arg) t.env (.dom (sig := sig) t.domNext),
        t.domNext + 1, t.obsNext⟩ := by
  have hobs : t.obsNext = s.obsNext := emb.obsNext_eq
  have hdom : t.domNext = s.domNext := emb.domNext_eq
  refine
    { env_commute := ?_
      source_wf := OriginEnv.WellFormed.weaken s.env (.dom (sig := sig) s.domNext)
        emb.source_wf hsFresh
      target_wf := OriginEnv.WellFormed.weaken t.env (.dom (sig := sig) t.domNext)
        emb.target_wf htFresh
      respectsRawIdx := Rename.ext_respectsRawIdx emb.respectsRawIdx
      ws_eq := ?_
      domNext_eq := by simp [hdom]
      obsNext_eq := by simp [hobs] }
  · intro A x
    cases x with
    | here => simp [Rename.ext, OriginEnv.weaken, OriginEnv.snoc, hdom]
    | there y =>
        simpa [Rename.ext, OriginEnv.weaken, OriginEnv.snoc] using emb.env_commute y
  · simp [hdom, emb.ws_eq]

/-- Split-push with the same parent origin/side on both sides. -/
theorem EncodeIxEmbedding.extSplit {Γ Δ : Ctx sig} {P : Object sig.nBases}
    {ρ : Rename sig Γ Δ}
    {s : EncodeIx (sig := sig) Γ} {t : EncodeIx (sig := sig) Δ}
    (emb : EncodeIxEmbedding ρ s t) (parent : Origin sig) (side : Bool)
    (hsFresh : OriginEnv.Fresh s.env (.split parent side))
    (htFresh : OriginEnv.Fresh t.env (.split parent side)) :
    EncodeIxEmbedding (Rename.ext ρ)
      ⟨pushPos s.ws (.split parent side) P,
        OriginEnv.weaken (A := P) s.env (.split parent side),
        s.domNext, s.obsNext⟩
      ⟨pushPos t.ws (.split parent side) P,
        OriginEnv.weaken (A := P) t.env (.split parent side),
        t.domNext, t.obsNext⟩ :=
  EncodeIxEmbedding.extPush (P := P) emb (.split parent side) hsFresh htFresh

/-! ## Peel-free certificate transport

`EncodeReadyFoc.letPos` allocates `.obs obsSlot` from the **state counter**.
Under an embedding, `obsNext` is shared (`obsNext_eq`), so origin allocation
does **not** change — `extObs` is the compositional counter/origin law.

Full `EncodeReady` (with `leftCoprod_peel` / `leftCoprod_unitEta`) additionally
needs binder-step `Fresh` for counter/split origins when threading
`WellFormed` (peel/`find?` rename laws themselves are available).
-/

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

/-! ## Exercise: λ and retained `letPos` under unused-binder weaken -/

def EmbedExSig : Signature where
  nBases := 1
  generators := #[]

private abbrev EmbedAtom : Object EmbedExSig.nBases := .base ⟨0, by decide⟩

def embedExEntry : EncodeIx (sig := EmbedExSig) Ctx.empty where
  ws := []
  env := OriginEnv.empty
  domNext := 0
  obsNext := 0

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
        (.split (.hyp (sig := EmbedExSig) 0) false),
      embedExEntry.domNext, embedExEntry.obsNext⟩
    (.exp EmbedAtom EmbedAtom) :=
  produced_of_embedding_noPeel
    (encodeIxEmbedding_weaken embedExEntry (.split (.hyp (sig := EmbedExSig) 0) false)
      OriginEnv.WellFormed.empty (OriginEnv.Fresh.empty _))
    embedExLamProduced embedExLam_noPeel

def embedExΓBase : Ctx EmbedExSig := Ctx.empty ▻ EmbedAtom

def embedExStateBase : EncodeIx (sig := EmbedExSig) embedExΓBase where
  ws := []
  env := OriginEnv.weaken (A := EmbedAtom) OriginEnv.empty (.hyp (sig := EmbedExSig) 0)
  domNext := 0
  obsNext := 0

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
    (OriginEnv.WellFormed.weaken OriginEnv.empty (.hyp (sig := EmbedExSig) 0)
      OriginEnv.WellFormed.empty (OriginEnv.Fresh.empty _))
    (by
      intro A x
      cases x with
      | here =>
          simp [embedExStateBase, OriginEnv.weaken, OriginEnv.snoc]
      | there y => nomatch y)

def embedExLetPosProduced : Produced embedExStateBase EmbedAtom where
  term := embedExLetPosBase
  cert := encodeReady_of_noPeel embedExLetPosBase_noPeel

def embedExLetPosProduced_weaken : Produced embedExTargetBase EmbedAtom :=
  produced_of_embedding_noPeel embedEx_weaken_embedding
    embedExLetPosProduced embedExLetPosBase_noPeel

/-! ## Lookup naturality under embedding constructors -/

/-- Identity embedding (same state). -/
theorem encodeIxEmbedding_id {Γ : Ctx sig}
    (s : EncodeIx (sig := sig) Γ) (hwf : OriginEnv.WellFormed s.env) :
    EncodeIxEmbedding (Rename.id (Γ := Γ)) s s where
  env_commute := fun _ => rfl
  source_wf := hwf
  target_wf := hwf
  respectsRawIdx := Rename.id_respectsRawIdx
  ws_eq := rfl
  domNext_eq := rfl
  obsNext_eq := rfl

private theorem embedExStateBase_wf :
    OriginEnv.WellFormed embedExStateBase.env :=
  OriginEnv.WellFormed.weaken OriginEnv.empty (.hyp (sig := EmbedExSig) 0)
    OriginEnv.WellFormed.empty (OriginEnv.Fresh.empty _)

private theorem embedExStateBase_fresh_obs :
    OriginEnv.Fresh embedExStateBase.env (.obs (sig := EmbedExSig) 0) := by
  intro A x
  cases x with
  | here => simp [embedExStateBase, OriginEnv.weaken, OriginEnv.snoc]
  | there y => nomatch y

private theorem embedExStateBase_fresh_dom :
    OriginEnv.Fresh embedExStateBase.env (.dom (sig := EmbedExSig) 0) := by
  intro A x
  cases x with
  | here => simp [embedExStateBase, OriginEnv.weaken, OriginEnv.snoc]
  | there y => nomatch y

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
  · exact OriginEnv.find?_eq_some_of_wellFormed _ _ _ embedExStateBase_wf rfl
  · exact EncodeIxEmbedding.find?_eq embedEx_weaken_embedding _ _
      (OriginEnv.find?_eq_some_of_wellFormed _ _ _ embedExStateBase_wf rfl)

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
      (embedExStateBase_fresh_split true) (embedExStateBase_fresh_split true))
    (.hyp (sig := EmbedExSig) 0) (.there .here)
    (OriginEnv.find?_weaken_there embedExStateBase.env
      (.split (.hyp (sig := EmbedExSig) 0) true) (.hyp (sig := EmbedExSig) 0) .here
      embedExStateBase_wf (embedExStateBase_fresh_split true) h)

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
      (embedExStateBase_fresh_split false) (embedExStateBase_fresh_split false))
    (.hyp (sig := EmbedExSig) 0) (.there .here)
    (OriginEnv.find?_weaken_there embedExStateBase.env
      (.split (.hyp (sig := EmbedExSig) 0) false) (.hyp (sig := EmbedExSig) 0) .here
      embedExStateBase_wf (embedExStateBase_fresh_split false) h)

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
      (encodeIxEmbedding_id embedExStateBase embedExStateBase_wf)
      embedExStateBase_fresh_obs embedExStateBase_fresh_obs)
    (.hyp (sig := EmbedExSig) 0) (.there .here)
    (OriginEnv.find?_weaken_there embedExStateBase.env
      (.obs (sig := EmbedExSig) 0) (.hyp (sig := EmbedExSig) 0) .here
      embedExStateBase_wf embedExStateBase_fresh_obs h)

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
      (encodeIxEmbedding_id embedExStateBase embedExStateBase_wf)
      embedExStateBase_fresh_dom embedExStateBase_fresh_dom)
    (.hyp (sig := EmbedExSig) 0) (.there .here)
    (OriginEnv.find?_weaken_there embedExStateBase.env
      (.dom (sig := EmbedExSig) 0) (.hyp (sig := EmbedExSig) 0) .here
      embedExStateBase_wf embedExStateBase_fresh_dom h)

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

/-!
### STOP — full `EncodeReady` transport (`leftCoprod_peel` / unit-η)

**Discharged:**
* `OriginEnv.WellFormed` / `Fresh` / `ofHyps_wellFormed` / `OriginCollisionFree`
* `EncodeIxEmbedding.find?_eq` under `source_wf` + `target_wf`
* Lookup tests for `weaken` / `extPush` / `extObs` / `extDom` / `extSplit`
  (colliding push blocked by `Fresh`, not by changing `find?` order)
* `PeelCase` + `peelCaseOuter_rename` / `peelCaseOuterGo_rename`
  (requires `Rename.RespectsRawIdx`, carried by embeddings)

**Remaining for readiness transport:**
Lift peel-free transport to full `EncodeReady`. Binder steps (`rightExp_lam`,
`letPos`, `leftCoprod_*` branches) push origins; threading `WellFormed` through
the motive needs `Fresh` for `.dom` / `.obs` / `.split` on **both** sides
(`EncodeIx` counter-freshness invariant). Unit-η then uses `find?_eq` + hit
via `env_commute`. Then retry non-unit nested-coprod forced inversion.

Do not add unit-only / atomic-leaf / nesting-depth cases.
-/

end Equality
end Gimbal
