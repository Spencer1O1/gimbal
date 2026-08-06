/-
  Scherer-core intrinsic realization of resolved support states.

  A `ResolvedEnv` assigns each intrinsic stable variable a dependency support.
  `CtxRealizes` / `SplitRealizes` tie bounded abstract states to live contexts,
  transporting `RStrongPos` ↔ `StrongPos` with exact support `K`.
-/

import Gimbal.Equality.Scherer.ResolvedSupport
import Gimbal.Equality.Scherer.RawSupport

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Resolved environments -/

/-- Assign resolved dependency support to every intrinsic stable variable. -/
abbrev ResolvedEnv (Γ : StableCtx sig) (O : Type) : Type :=
  ∀ (S : StableTy sig.nBases), StableVar Γ S → DepSupport O

namespace ResolvedEnv

variable {O : Type}

/-- Extend under a newest binder with support `K`. -/
def extend {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (env : ResolvedEnv Γ O) (K : DepSupport O) :
    ResolvedEnv (Γ.snoc S) O
  | _, .here => K
  | T, .there x => env T x

@[simp] theorem extend_here {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (env : ResolvedEnv Γ O) (K : DepSupport O) :
    extend (S := S) env K _ .here = K := rfl

@[simp] theorem extend_there {Γ : StableCtx sig} {S S' : StableTy sig.nBases}
    (env : ResolvedEnv Γ O) (K : DepSupport O) (x : StableVar Γ S') :
    extend (S := S) env K _ (.there x) = env S' x := rfl

/-- Empty environment on the empty context. -/
def empty (O : Type) : ResolvedEnv (.empty : StableCtx sig) O :=
  fun _ x => nomatch x

end ResolvedEnv

/-! ### newLevels ↔ Old.length suffix -/

theorem mem_newLevels_iff (Old : StableCtx sig) :
    ∀ (New : StableCtx sig) (i : Fin (Old.append New).length),
      i ∈ newLevels Old New ↔ Old.length ≤ (i : Nat)
  | .empty, i => by
      constructor
      · intro hi
        exact (Finset.notMem_empty i hi).elim
      · intro hi
        exact (not_le_of_gt i.isLt hi).elim
  | .snoc Δ S, i => by
      -- `append_snoc` is `rfl`, so `i` already inhabits the snoc-length Fin.
      change i ∈ insert (Fin.last (Old.append Δ).length)
          (wkSupport (S := S) (newLevels Old Δ)) ↔ Old.length ≤ (i : Nat)
      refine Fin.lastCases ?last ?cast i
      · constructor
        · intro _
          simp only [Fin.val_last, length_StableCtx_append]
          exact Nat.le_add_right _ _
        · intro _
          exact Finset.mem_insert_self _ _
      · intro j
        have ih := mem_newLevels_iff Old Δ j
        have hwk : (j.castSucc : Fin ((Old.append Δ).length + 1)) =
            wkLevel (S := S) j := Fin.ext rfl
        constructor
        · intro hj
          have hj' : j.castSucc ∈ wkSupport (S := S) (newLevels Old Δ) :=
            (Finset.mem_insert.mp hj).resolve_left (Fin.castSucc_ne_last _)
          have : Old.length ≤ (j : Nat) :=
            ih.mp ((mem_wkSupport (S := S) (newLevels Old Δ) j).mpr (hwk ▸ hj'))
          simpa [Fin.val_castSucc] using this
        · intro hj
          have : j ∈ newLevels Old Δ := ih.mpr (by simpa [Fin.val_castSucc] using hj)
          exact Finset.mem_insert_of_mem
            (hwk ▸ (mem_wkSupport (S := S) (newLevels Old Δ) j).mp this)

/-! ### Context realization -/

/--
Abstract state realizes an intrinsic context under `env`:
same length, matching stable types at each level, and `depAt = env`.
-/
structure CtxRealizes {U : SearchUniverse sig} {O : Type} {B : Nat}
    (st : ResolvedState U O B) (Γ : StableCtx sig)
    (env : ResolvedEnv Γ O) : Prop where
  length_eq : Γ.length = st.depth
  ty_eq : ∀ (i : Fin st.depth),
    (st.tyAt i).val =
      Γ.typeAtLevel ⟨i.val, by rw [length_eq]; exact i.isLt⟩
  dep_eq : ∀ (S : StableTy sig.nBases) (x : StableVar Γ S),
    st.depAt ⟨x.level.val, by rw [← length_eq]; exact x.level.isLt⟩ = env S x

namespace CtxRealizes

variable {U : SearchUniverse sig} {O : Type} {B : Nat}

def toLevel {st : ResolvedState U O B} {Γ : StableCtx sig}
    {env : ResolvedEnv Γ O} (h : CtxRealizes st Γ env)
    (i : Fin st.depth) : StableLevel Γ :=
  ⟨i.val, by rw [h.length_eq]; exact i.isLt⟩

def ofLevel {st : ResolvedState U O B} {Γ : StableCtx sig}
    {env : ResolvedEnv Γ O} (h : CtxRealizes st Γ env)
    (i : StableLevel Γ) : Fin st.depth :=
  ⟨i.val, by rw [← h.length_eq]; exact i.isLt⟩

theorem depAt_eq_env {st : ResolvedState U O B} {Γ : StableCtx sig}
    {env : ResolvedEnv Γ O} (h : CtxRealizes st Γ env)
    {S : StableTy sig.nBases} (x : StableVar Γ S) :
    st.depAt (h.ofLevel x.level) = env S x :=
  h.dep_eq S x

end CtxRealizes

/-- Realization of a split `Old / New` with `roundStart = Old.length`. -/
structure SplitRealizes {U : SearchUniverse sig} {O : Type} {B : Nat}
    (st : ResolvedState U O B) (Old New : StableCtx sig)
    (env : ResolvedEnv (Old.append New) O) : Prop where
  realizes : CtxRealizes st (Old.append New) env
  round : st.roundStart = Old.length

/-! ### Root / push / reset -/

def rootState (U : SearchUniverse sig) (O : Type) (B : Nat) :
    ResolvedState U O B :=
  ResolvedState.empty U O B

theorem root_realizes (U : SearchUniverse sig) (O : Type) (B : Nat) :
    CtxRealizes (rootState U O B) (.empty : StableCtx sig)
      (ResolvedEnv.empty O) where
  length_eq := rfl
  ty_eq := fun i => nomatch i
  dep_eq := fun _ x => nomatch x

theorem SplitRealizes.of_root (U : SearchUniverse sig) (O : Type) (B : Nat) :
    SplitRealizes (rootState U O B) (.empty : StableCtx sig) .empty
      (ResolvedEnv.empty O) where
  realizes := root_realizes U O B
  round := rfl

theorem SplitRealizes.resetRound {U : SearchUniverse sig} {O : Type} {B : Nat}
    {st : ResolvedState U O B} {Old New : StableCtx sig}
    {env : ResolvedEnv (Old.append New) O}
    (h : SplitRealizes st Old New env) :
    SplitRealizes (st.resetRound) (Old.append New) .empty
      (by simpa [StableCtx.append_empty] using env) where
  realizes := by
    have hR := h.realizes
    refine ⟨by simpa [ResolvedState.resetRound, StableCtx.append_empty]
      using hR.length_eq, ?_, ?_⟩
    · intro i
      simpa [ResolvedState.resetRound, StableCtx.append_empty] using hR.ty_eq i
    · intro S x
      simpa [ResolvedState.resetRound, StableCtx.append_empty] using hR.dep_eq S x
  round := by
    simp only [ResolvedState.resetRound]
    simpa [StableCtx.append_empty] using h.realizes.length_eq.symm

private theorem typeAtLevel_snoc_last (Γ : StableCtx sig) (S : StableTy sig.nBases) :
    (Γ.snoc S).typeAtLevel (Fin.last Γ.length) = S := by
  simp [StableCtx.typeAtLevel, Fin.val_last]

private theorem typeAtLevel_snoc_castSucc (Γ : StableCtx sig) (S : StableTy sig.nBases)
    (i : Fin Γ.length) :
    (Γ.snoc S).typeAtLevel i.castSucc = Γ.typeAtLevel i := by
  have hne : (i : Nat) ≠ Γ.length := Nat.ne_of_lt i.isLt
  simp only [StableCtx.typeAtLevel, Fin.val_castSucc, dif_neg hne]

private theorem level_eqRec {Γ : StableCtx sig} {S S' : StableTy sig.nBases}
    (e : S = S') (x : StableVar Γ S) :
    StableVar.level (e ▸ x) = StableVar.level x := by
  cases e; rfl

private theorem push_realizes {U : SearchUniverse sig} {O : Type} {B : Nat}
    {st : ResolvedState U O B} {Γ : StableCtx sig} {env : ResolvedEnv Γ O}
    (hR : CtxRealizes st Γ env) (hd : st.depth < B) (S : UStable U)
    (K : DepSupport O) :
    CtxRealizes (st.push hd S K) (Γ.snoc S.val)
      (ResolvedEnv.extend (S := S.val) env K) where
  length_eq := by
    simp only [StableCtx.length, ResolvedState.push_depth, hR.length_eq]
  ty_eq := by
    intro i
    refine Fin.lastCases ?new ?old i
    · have hlen : st.depth = Γ.length := hR.length_eq.symm
      have hnew := congrArg Subtype.val (ResolvedState.push_new_type st hd S K)
      have hlast := typeAtLevel_snoc_last Γ S.val
      refine hnew.trans ?_
      convert hlast.symm
      exact Fin.ext (by simp [hlen, Fin.val_last])
    · intro j
      have hold := congrArg Subtype.val (ResolvedState.push_old_type st hd S K j)
      have hty := hR.ty_eq j
      have hcast := typeAtLevel_snoc_castSucc Γ S.val
        ⟨j.val, by rw [hR.length_eq]; exact j.isLt⟩
      refine hold.trans (hty.trans ?_)
      convert hcast.symm
      exact Fin.ext (by simp [Fin.val_castSucc])
  dep_eq := by
    intro T x
    cases x with
    | here =>
      have hnew := ResolvedState.push_new_support st hd S K
      simp only [ResolvedEnv.extend, StableVar.level, Fin.val_last]
      have hidx : (⟨Γ.length,
            by simp [ResolvedState.push_depth, hR.length_eq]⟩ :
          Fin (st.push hd S K).depth) = Fin.last st.depth :=
        Fin.ext (by simp [hR.length_eq, Fin.val_last])
      exact hidx ▸ hnew
    | there y =>
      have hlen := hR.length_eq
      let j : Fin st.depth :=
        ⟨y.level.val, by rw [← hlen]; exact y.level.isLt⟩
      have hidx : (⟨y.level.val,
            by
              simp only [ResolvedState.push_depth]
              have := y.level.isLt
              omega⟩ :
          Fin (st.push hd S K).depth) = j.castSucc :=
        Fin.ext rfl
      simp only [ResolvedEnv.extend, StableVar.level, Fin.val_castSucc]
      exact hidx ▸
        (ResolvedState.push_old_support st hd S K j).trans (hR.dep_eq T y)

theorem SplitRealizes.pushLexical {U : SearchUniverse sig} {O : Type} {B : Nat}
    {st : ResolvedState U O B} {Old New : StableCtx sig}
    {env : ResolvedEnv (Old.append New) O}
    (h : SplitRealizes st Old New env) (hd : st.depth < B)
    (S : UStable U) :
    SplitRealizes (st.pushLexical hd S) Old (New.snoc S.val)
      (ResolvedEnv.extend (S := S.val) env ∅) where
  realizes := by
    simpa [ResolvedState.pushLexical, StableCtx.append_snoc] using
      push_realizes h.realizes hd S ∅
  round := by
    simp only [ResolvedState.pushLexical, ResolvedState.push_roundStart, h.round]

theorem SplitRealizes.pushResolved {U : SearchUniverse sig} {O : Type} {B : Nat}
    {st : ResolvedState U O B} {Old New : StableCtx sig}
    {env : ResolvedEnv (Old.append New) O}
    (h : SplitRealizes st Old New env) (hd : st.depth < B)
    (S : UStable U) (K : DepSupport O) :
    SplitRealizes (st.pushResolved hd S K) Old (New.snoc S.val)
      (ResolvedEnv.extend (S := S.val) env K) where
  realizes := by
    simpa [ResolvedState.pushResolved, StableCtx.append_snoc] using
      push_realizes h.realizes hd S K
  round := by
    simp only [ResolvedState.pushResolved, ResolvedState.push_roundStart, h.round]

/-! ### currentRaw ↔ newLevels -/

theorem SplitRealizes.currentRaw_iff_newLevels
    {U : SearchUniverse sig} {O : Type} {B : Nat}
    {st : ResolvedState U O B} {Old New : StableCtx sig}
    {env : ResolvedEnv (Old.append New) O}
    (h : SplitRealizes st Old New env) (i : Fin st.depth) :
    i ∈ st.currentRaw ↔
      (⟨i.val, Nat.lt_of_lt_of_eq i.isLt h.realizes.length_eq.symm⟩ :
        Fin (Old.append New).length) ∈ newLevels Old New := by
  have hmem := mem_newLevels_iff Old New
    ⟨i.val, Nat.lt_of_lt_of_eq i.isLt h.realizes.length_eq.symm⟩
  simp only [ResolvedState.currentRaw, Finset.mem_filter, Finset.mem_univ, true_and,
    h.round, hmem]

/-! ### Intrinsic strong-positive support -/

namespace StrongPos

/-- Resolved dependency support of an intrinsic strong pattern under `env`. -/
def depSupport {Γ : StableCtx sig} {O : Type} (env : ResolvedEnv Γ O)
    {P : Pos sig.nBases} : StrongPos Γ P → DepSupport O
  | .negVar x => env _ x
  | .atomVar x => env _ x
  | .inl sp => depSupport env sp
  | .inr sp => depSupport env sp

@[simp] theorem depSupport_negVar {Γ : StableCtx sig} {O : Type}
    (env : ResolvedEnv Γ O) {N} (x : StableVar Γ (.neg N)) :
    depSupport env (.negVar x) = env _ x := rfl

@[simp] theorem depSupport_atomVar {Γ : StableCtx sig} {O : Type}
    (env : ResolvedEnv Γ O) {q} (x : StableVar Γ (.atom q)) :
    depSupport env (.atomVar x) = env _ x := rfl

@[simp] theorem depSupport_inl {Γ : StableCtx sig} {O : Type}
    (env : ResolvedEnv Γ O) {P Q} (sp : StrongPos Γ P) :
    depSupport env (.inl (Q := Q) sp) = depSupport env sp := rfl

@[simp] theorem depSupport_inr {Γ : StableCtx sig} {O : Type}
    (env : ResolvedEnv Γ O) {P Q} (sp : StrongPos Γ Q) :
    depSupport env (.inr (P := P) sp) = depSupport env sp := rfl

end StrongPos

/-! ### Reify / reflect -/

namespace RStrongPos

variable {U : SearchUniverse sig} {O : Type} {B : Nat}

/-- Reify an abstract strong pattern into an intrinsic `StrongPos`. -/
def reify {st : ResolvedState U O B} {Γ : StableCtx sig}
    {env : ResolvedEnv Γ O} (h : CtxRealizes st Γ env) {P : Pos sig.nBases} :
    (sp : RStrongPos st P) →
      { sp' : StrongPos Γ P // StrongPos.depSupport env sp' = sp.depSupport }
  | .negVar i hty =>
      let lev : StableLevel Γ := h.toLevel i
      have htyΓ : Γ.typeAtLevel lev = .neg _ := (h.ty_eq i).symm.trans hty
      let x : StableVar Γ (.neg _) := htyΓ ▸ StableVar.atLevel Γ lev
      ⟨.negVar x, by
        change env _ x = st.depAt i
        have hlev : x.level = lev :=
          (level_eqRec htyΓ (StableVar.atLevel Γ lev)).trans
            (StableVar.level_atLevel Γ lev)
        have hdep := h.dep_eq _ x
        have hidx : (⟨x.level.val,
              by rw [← h.length_eq]; exact x.level.isLt⟩ : Fin st.depth) = i :=
          Fin.ext (by rw [hlev]; rfl)
        exact hidx ▸ hdep.symm⟩
  | .atomVar i hty =>
      let lev : StableLevel Γ := h.toLevel i
      have htyΓ : Γ.typeAtLevel lev = .atom _ := (h.ty_eq i).symm.trans hty
      let x : StableVar Γ (.atom _) := htyΓ ▸ StableVar.atLevel Γ lev
      ⟨.atomVar x, by
        change env _ x = st.depAt i
        have hlev : x.level = lev :=
          (level_eqRec htyΓ (StableVar.atLevel Γ lev)).trans
            (StableVar.level_atLevel Γ lev)
        have hdep := h.dep_eq _ x
        have hidx : (⟨x.level.val,
              by rw [← h.length_eq]; exact x.level.isLt⟩ : Fin st.depth) = i :=
          Fin.ext (by rw [hlev]; rfl)
        exact hidx ▸ hdep.symm⟩
  | .inl sp =>
      let r := reify h sp
      ⟨.inl r.1, by simp [r.2]⟩
  | .inr sp =>
      let r := reify h sp
      ⟨.inr r.1, by simp [r.2]⟩

/-- Reflect an intrinsic strong pattern into an abstract `RStrongPos`. -/
def reflect {st : ResolvedState U O B} {Γ : StableCtx sig}
    {env : ResolvedEnv Γ O} (h : CtxRealizes st Γ env) {P : Pos sig.nBases} :
    (sp : StrongPos Γ P) →
      { sp' : RStrongPos st P // sp'.depSupport = StrongPos.depSupport env sp }
  | .negVar x =>
      let i : Fin st.depth := h.ofLevel x.level
      have hty : (st.tyAt i).val = .neg _ :=
        (h.ty_eq i).trans <| by
          have : (⟨i.val, by rw [h.length_eq]; exact i.isLt⟩ : StableLevel Γ) =
              x.level := Fin.ext rfl
          simpa [this] using StableCtx.typeAtLevel_level x
      ⟨.negVar i hty, by
        simp only [depSupport_negVar, StrongPos.depSupport_negVar]
        exact h.dep_eq _ x⟩
  | .atomVar x =>
      let i : Fin st.depth := h.ofLevel x.level
      have hty : (st.tyAt i).val = .atom _ :=
        (h.ty_eq i).trans <| by
          have : (⟨i.val, by rw [h.length_eq]; exact i.isLt⟩ : StableLevel Γ) =
              x.level := Fin.ext rfl
          simpa [this] using StableCtx.typeAtLevel_level x
      ⟨.atomVar i hty, by
        simp only [depSupport_atomVar, StrongPos.depSupport_atomVar]
        exact h.dep_eq _ x⟩
  | .inl sp =>
      let r := reflect h sp
      ⟨.inl r.1, by simp [r.2]⟩
  | .inr sp =>
      let r := reflect h sp
      ⟨.inr r.1, by simp [r.2]⟩

end RStrongPos

/-! ### Exact StrongAt transport -/

namespace StrongAt

variable {U : SearchUniverse sig} {O : Type} {B : Nat}

/-- Reify preserves exact support `K`. -/
theorem reify {st : ResolvedState U O B} {Γ : StableCtx sig}
    {env : ResolvedEnv Γ O} (h : CtxRealizes st Γ env)
    {P : Pos sig.nBases} {K : DepSupport O} (hs : StrongAt st P K) :
    Nonempty { sp : StrongPos Γ P // StrongPos.depSupport env sp = K } := by
  rcases hs with ⟨⟨rsp, heq⟩⟩
  let r := RStrongPos.reify h rsp
  exact ⟨⟨r.1, by rw [r.2, heq]⟩⟩

/-- Reflect preserves exact support `K`. -/
theorem reflect {st : ResolvedState U O B} {Γ : StableCtx sig}
    {env : ResolvedEnv Γ O} (h : CtxRealizes st Γ env)
    {P : Pos sig.nBases} {K : DepSupport O}
    (hs : Nonempty { sp : StrongPos Γ P // StrongPos.depSupport env sp = K }) :
    StrongAt st P K := by
  rcases hs with ⟨⟨sp, heq⟩⟩
  let r := RStrongPos.reflect h sp
  exact ⟨⟨r.1, by rw [r.2, heq]⟩⟩

/-- Exactness in `K`: rewriting the support label after reify. -/
theorem reify_exact {st : ResolvedState U O B} {Γ : StableCtx sig}
    {env : ResolvedEnv Γ O} (h : CtxRealizes st Γ env)
    {P : Pos sig.nBases} {K K' : DepSupport O}
    (hs : StrongAt st P K) (heq : K = K') :
    Nonempty { sp : StrongPos Γ P // StrongPos.depSupport env sp = K' } :=
  heq ▸ reify h hs

/-- A witness at a different support does not discharge `StrongAt` at `K`. -/
theorem not_discharge {Γ : StableCtx sig} {env : ResolvedEnv Γ O}
    {P : Pos sig.nBases} {K K' : DepSupport O}
    (sp : StrongPos Γ P) (hsp : StrongPos.depSupport env sp = K')
    (hne : K ≠ K') :
    ¬ StrongPos.depSupport env sp = K := by
  intro h
  exact hne (h.symm.trans hsp)

end StrongAt

/-! ### Pending realization helpers -/

namespace ResolvedPending

variable {U : SearchUniverse sig} {O : Type}

/-- Lambda pending introduces empty resolved support and erases to a cons. -/
theorem lambdaPending_introduces_empty (P : UPos U) :
    (∃ c, lambdaPending (O := O) P = [c] ∧ c.support = ∅) ∧
      erase (lambdaPending (O := O) P) = .cons P.val .empty :=
  ⟨⟨⟨P, ∅⟩, rfl, rfl⟩, erase_lambdaPending P⟩

/-- Sum decomposition preserves head support `K`. -/
theorem sum_preserves_K (A B : Pos sig.nBases) (hA : A ∈ U.pos) (hB : B ∈ U.pos)
    {K : DepSupport O} {rest : ResolvedPending U O}
    {hSum : Pos.sum A B ∈ U.pos} :
    sumLeft A B hA (⟨⟨.sum A B, hSum⟩, K⟩ :: rest) =
      some (⟨⟨A, hA⟩, K⟩ :: rest) ∧
    sumRight A B hB (⟨⟨.sum A B, hSum⟩, K⟩ :: rest) =
      some (⟨⟨B, hB⟩, K⟩ :: rest) :=
  ⟨sumLeft_preserves_support A B hA, sumRight_preserves_support A B hB⟩

/-- Erase recovers the intrinsic pending spine from obligation lists. -/
theorem erase_recovers (obs : List (UPos U × DepSupport O)) :
    erase (pendingFromObligations obs) =
      obs.foldr (fun pk acc => .cons pk.1.val acc) .empty :=
  erase_pendingFromObligations obs

end ResolvedPending

/-- Batch-result push under realization inherits support `K`. -/
theorem SplitRealizes.pushResolved_inherits_K
    {U : SearchUniverse sig} {O : Type} {B : Nat}
    {st : ResolvedState U O B} {Old New : StableCtx sig}
    {env : ResolvedEnv (Old.append New) O}
    (_h : SplitRealizes st Old New env) (hd : st.depth < B)
    (S : UStable U) (K : DepSupport O) :
    (st.pushResolved hd S K).depAt (Fin.last st.depth) = K ∧
      ResolvedEnv.extend (S := S.val) env K _ .here = K :=
  ⟨ResolvedState.pushResolved_new_support st hd S K, rfl⟩

/-! ### Adversarial fixtures -/

namespace ResolvedRealizeFixtures

def sig0 : Signature := ⟨0, #[]⟩
abbrev O2 := Fin 2
def x0 : O2 := ⟨0, by decide⟩
def zOrigin : O2 := ⟨1, by decide⟩

def U0 : SearchUniverse sig0 :=
  SearchUniverse.fromInputs
    (StableCtx.snoc (.empty : StableCtx sig0) (.neg (.shift .zero)))
    .empty (.pos (.shift .one)) []

def Sneg0 : UStable U0 :=
  ⟨.neg (.shift .zero),
    SearchUniverse.stable_of_context
      (Γ := StableCtx.snoc (.empty : StableCtx sig0) (.neg (.shift .zero)))
      .empty (.pos (.shift .one)) [] ⟨.here⟩⟩

def X : Pos 0 := .shift (.shift .zero)

def stX0 : ResolvedState U0 O2 2 :=
  (rootState U0 O2 2).pushResolved (by decide) Sneg0 ({x0} : DepSupport O2)

theorem hX0 : SplitRealizes stX0 (.empty : StableCtx sig0)
    (.snoc .empty Sneg0.val)
    (ResolvedEnv.extend (S := Sneg0.val) (ResolvedEnv.empty O2) {x0}) :=
  (SplitRealizes.of_root U0 O2 2).pushResolved (by decide) Sneg0 {x0}

/-- Old `x0:X` with support `{x0}` does not realize `StrongAt X {z}` for `z ≠ x0`. -/
theorem old_x0_not_strongAt_z :
    StrongAt stX0 X ({x0} : DepSupport O2) ∧
      ¬ StrongAt stX0 X ({zOrigin} : DepSupport O2) := by
  refine ⟨?pos, ?neg⟩
  · have hty : (stX0.tyAt ⟨0, by decide⟩).val =
        StableTy.neg (Neg.shift (.zero : Pos 0)) := by
      have hL := ResolvedState.push_new_type (rootState U0 O2 2) (by decide) Sneg0
        ({x0} : DepSupport O2)
      simp only [stX0, rootState, ResolvedState.pushResolved, Sneg0] at hL ⊢
      exact congrArg Subtype.val hL
    have h := StrongAt.of_negVar (st := stX0) ⟨0, by decide⟩ hty
    have hdep : stX0.depAt ⟨0, by decide⟩ = ({x0} : DepSupport O2) := by
      have hL := ResolvedState.pushResolved_new_support
        (rootState U0 O2 2) (by decide) Sneg0 ({x0} : DepSupport O2)
      simp only [stX0, rootState, ResolvedState.pushResolved] at hL ⊢
      exact hL
    rwa [hdep] at h
  · intro ⟨⟨sp, heq⟩⟩
    match sp with
    | .negVar i _ =>
      have hi : i = (⟨0, by decide⟩ : Fin 1) :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      have hdep : stX0.depAt i = ({x0} : DepSupport O2) := by
        subst hi
        have hL := ResolvedState.pushResolved_new_support
          (rootState U0 O2 2) (by decide) Sneg0 ({x0} : DepSupport O2)
        simp only [stX0, rootState, ResolvedState.pushResolved] at hL ⊢
        exact hL
      have hne : ({x0} : DepSupport O2) ≠ {zOrigin} := by
        intro h
        exact absurd (Finset.singleton_inj.mp h) (by decide : x0 ≠ zOrigin)
      exact hne (hdep ▸ heq)

/-- Promoted batch entry with support `{z}` realizes `StrongAt X {z}`. -/
theorem promoted_z_strongAt_z :
    let st := (rootState U0 O2 1).pushResolved (by decide) Sneg0
      ({zOrigin} : DepSupport O2)
    StrongAt st X ({zOrigin} : DepSupport O2) := by
  intro st
  have hty : (st.tyAt ⟨0, by decide⟩).val =
      StableTy.neg (Neg.shift (.zero : Pos 0)) := by
    have hL := ResolvedState.push_new_type (rootState U0 O2 1) (by decide) Sneg0
      ({zOrigin} : DepSupport O2)
    simp only [st, rootState, ResolvedState.pushResolved, Sneg0] at hL ⊢
    exact congrArg Subtype.val hL
  have h := StrongAt.of_negVar (st := st) ⟨0, by decide⟩ hty
  have hdep : st.depAt ⟨0, by decide⟩ = ({zOrigin} : DepSupport O2) := by
    have hL := ResolvedState.pushResolved_new_support
      (rootState U0 O2 1) (by decide) Sneg0 ({zOrigin} : DepSupport O2)
    simp only [st, rootState, ResolvedState.pushResolved] at hL ⊢
    exact hL
  rwa [hdep] at h

/-- Lexical binder has empty resolved support but remains in `currentRaw`. -/
theorem lexical_empty_but_raw_current :
    let st := (rootState U0 O2 1).pushLexical (by decide) Sneg0
    (⟨0, by decide⟩ : Fin 1) ∈ st.currentRaw ∧
      st.depAt ⟨0, by decide⟩ = ∅ ∧
      ResolvedEnv.extend (S := Sneg0.val) (ResolvedEnv.empty O2) ∅ _ .here = ∅ := by
  intro st
  refine ⟨?_, ?_, rfl⟩
  · have hL := ResolvedState.push_new_current (rootState U0 O2 1) (by decide) Sneg0
      (∅ : DepSupport O2)
    simp only [st, rootState, ResolvedState.pushLexical] at hL ⊢
    exact hL
  · have hL := ResolvedState.pushLexical_new_support_empty
      (rootState U0 O2 1) (by decide) Sneg0
    simp only [st, rootState, ResolvedState.pushLexical] at hL ⊢
    exact hL

/-- `resetRound` moves the split to `(Old.append New, empty)` without changing supports. -/
theorem resetRound_split_preserves_dep :
    let h0 := SplitRealizes.of_root U0 O2 2
    let h1 := h0.pushResolved (by decide) Sneg0 ({x0} : DepSupport O2)
    let h2 := h1.pushLexical (by decide) Sneg0
    let st := (rootState U0 O2 2).pushResolved (by decide) Sneg0 ({x0} : DepSupport O2)
      |>.pushLexical (by decide) Sneg0
    -- `h2.resetRound` realizes `(Old.append New, empty)`; supports unchanged.
    let _hR := h2.resetRound
    (st.resetRound).depAt = st.depAt ∧
      (st.resetRound).roundStart = st.depth ∧
      (st.resetRound).currentRaw = ∅ := by
  intro _ _ _ st _hR
  exact ⟨ResolvedState.resetRound_depAt _, rfl,
    ResolvedState.currentRaw_resetRound_empty _⟩

end ResolvedRealizeFixtures

end Gimbal.Equality.Scherer
