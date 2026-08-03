/-
  Completeness of the reachability worklist (Milestone 8D).

  The closure stops at a state the sweep cannot change. Because every rule is
  monotone, a sweep that returns its input is pointwise the identity: each
  individual rule already holds at the fixed point. Reading those equations
  backwards turns each declarative rule into a recorded fact, which is exactly
  completeness for the fragment the finite table can represent.
-/

import Gimbal.Equality.ReachSound

namespace Gimbal
namespace Equality

variable {n : Nat}

/-! ### Antisymmetry of the extension order -/

theorem ReachState.le_antisymm {σ τ : ReachState n} (h₁ : ReachState.Le σ τ)
    (h₂ : ReachState.Le τ σ) : σ = τ :=
  ReachState.eq_of_le_of_weight_le h₁ (ReachState.weight_le_of_le h₂)

/-- A monotone step that lands back where it started did nothing. -/
theorem ReachState.eq_of_sandwich {σ τ : ReachState n} (h₁ : ReachState.Le σ τ)
    (h₂ : ReachState.Le τ σ) : τ = σ :=
  (ReachState.le_antisymm h₁ h₂).symm

/-- At a fixed point of a monotone fold, every single step is already stable. -/
theorem foldl_fix {α : Type} (f : ReachState n → α → ReachState n)
    (hf : ∀ σ a, ReachState.Le σ (f σ a)) :
    ∀ (l : List α) (σ : ReachState n), l.foldl f σ = σ → ∀ a ∈ l, f σ a = σ
  | [], _, _ => by simp
  | a :: l, σ, hfold => by
      simp only [List.foldl_cons] at hfold
      have h₂ := foldl_le f hf l (f σ a)
      rw [hfold] at h₂
      have hfa : f σ a = σ := ReachState.eq_of_sandwich (hf σ a) h₂
      rw [hfa] at hfold
      have ih := foldl_fix f hf l σ hfold
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hfa
      · exact ih b hb

/-! ### Table and array lookup helpers -/

theorem lt_size_of_getElem? {α : Type} {a : Array α} {i : Nat} {x : α}
    (h : a[i]? = some x) : i < a.size := by
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp h
  exact hlt

theorem mem_of_getElem? {α : Type} {a : Array α} {i : Nat} {x : α}
    (h : a[i]? = some x) : x ∈ a := by
  obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp h
  exact hx ▸ Array.getElem_mem hlt

theorem lt_types_of_typeAt {σ : ReachState n} {i : Nat} {A : Object n}
    (h : σ.typeAt i = some A) : i < σ.types.size :=
  lt_size_of_getElem? h

theorem exists_findTypeIdx {σ : ReachState n} {A : Object n} (h : A ∈ σ.types) :
    ∃ i, σ.findTypeIdx A = some i :=
  Option.isSome_iff_exists.mp (findIdx?_isSome_of_mem h)

theorem isSimplyDeducible_of_index {σ : ReachState n} {A : Object n} {i : Nat}
    (hi : σ.findTypeIdx A = some i) (hc : (σ.getCell i).simplyDeducible = true) :
    isSimplyDeducible σ A = true := by
  unfold isSimplyDeducible; rw [hi]; exact hc

theorem index_deducible {σ : ReachState n} {A : Object n} {i : Nat}
    (hi : σ.findTypeIdx A = some i) (h : isSimplyDeducible σ A = true) :
    (σ.getCell i).simplyDeducible = true := by
  unfold isSimplyDeducible at h; rw [hi] at h; exact h

/-! ### Size invariant

`cells` and `types` are allocated together and only ever updated in place, so
every reachable state indexes cells by subformula-table index.
-/

/-- One cell per subformula-table entry. -/
def ReachState.Sized (σ : ReachState n) : Prop :=
  σ.cells.size = σ.types.size

theorem ReachState.Sized.mono {σ τ : ReachState n} (h : ReachState.Le σ τ)
    (hs : ReachState.Sized σ) : ReachState.Sized τ := by
  unfold ReachState.Sized at hs ⊢
  rw [← h.size, ← h.types]
  exact hs

theorem lt_cells_of_typeAt {σ : ReachState n} {i : Nat} {A : Object n}
    (hsz : ReachState.Sized σ) (h : σ.typeAt i = some A) : i < σ.cells.size := by
  rw [ReachState.Sized] at hsz
  rw [hsz]
  exact lt_types_of_typeAt h

/-! ### Reading a stable update backwards -/

/-- If recording changed nothing, the slot it targets was already inhabited. -/
theorem ReachCell.simplyDeducible_of_record_eq {c : ReachCell} {b : Bool} {w : Witness}
    (h : c.record b w = c) : c.simplyDeducible = true := by
  have hw := ReachCell.record_witnessed c b w
  rw [h] at hw
  unfold ReachCell.simplyDeducible
  rcases hw with hw | hw <;> simp [hw]

theorem ReachState.getCell_discover_self {σ : ReachState n} {i : Nat} {b : Bool}
    {w : Witness} {A : Object n} (hlt : i < σ.cells.size) (hty : σ.typeAt i = some A) :
    (σ.discover i b w).getCell i = (σ.getCell i).record b w := by
  unfold ReachState.discover
  rw [hty]
  rw [ReachState.getCell_markInconsistentIf]
  exact ReachState.getCell_setCell_self hlt

/-- A discovery the state absorbs must have found the fact already there. -/
theorem ReachState.simplyDeducible_of_discover_eq {σ : ReachState n} {i : Nat}
    {b : Bool} {w : Witness} {A : Object n} (hsz : ReachState.Sized σ)
    (hty : σ.typeAt i = some A) (h : σ.discover i b w = σ) :
    (σ.getCell i).simplyDeducible = true := by
  have hg := ReachState.getCell_discover_self (b := b) (w := w)
    (lt_cells_of_typeAt hsz hty) hty
  rw [h] at hg
  exact ReachCell.simplyDeducible_of_record_eq hg.symm

theorem ReachState.getCell_markHyp_self {σ : ReachState n} {Γ : ReachCtx n} {k i : Nat}
    {A : Object n} (hlt : i < σ.cells.size) (hA : Γ.hyps[k]? = some A)
    (hi : σ.findTypeIdx A = some i) :
    (σ.markHyp Γ k).getCell i = (σ.getCell i).recordHyp (Γ.isNew k) (.ctxVar k) := by
  unfold ReachState.markHyp
  rw [hA]
  dsimp only
  rw [hi]
  rw [ReachState.getCell_markInconsistentIf]
  exact ReachState.getCell_setCell_self hlt

/-- A hypothesis marking the state absorbs was already retrievable. -/
theorem ReachState.retrievable_of_markHyp_eq {σ : ReachState n} {Γ : ReachCtx n}
    {k i : Nat} {A : Object n} (hsz : ReachState.Sized σ) (hA : Γ.hyps[k]? = some A)
    (hi : σ.findTypeIdx A = some i) (h : σ.markHyp Γ k = σ) :
    (σ.getCell i).retrievable = true := by
  have hlt := lt_cells_of_typeAt hsz (ReachState.typeAt_of_findTypeIdx hi)
  have hg := ReachState.getCell_markHyp_self hlt hA hi
  rw [h] at hg
  simpa using congrArg ReachCell.retrievable hg

/-! ### The fixed point of the sweep -/

/-- Every rule of the sweep is stable at `σ`. -/
structure ReachFix (Γ : ReachCtx n) (σ : ReachState n) : Prop where
  seed : ∀ k, k < Γ.hyps.size → seedHypRule Γ σ k = σ
  unitEta : unitEtaRule σ = σ
  hyp : ∀ k, k < Γ.hyps.size → hypRule Γ σ k = σ
  type : ∀ i, i < σ.types.size → typeRule σ i = σ

/-- The state after the seeding pass of one sweep. -/
private def sweepSeed (Γ : ReachCtx n) (σ : ReachState n) : ReachState n :=
  (List.range Γ.hyps.size).foldl (seedHypRule Γ) σ

theorem reachFix_of_reachStep_eq {Γ : ReachCtx n} {σ : ReachState n}
    (h : reachStep Γ σ = σ) : ReachFix Γ σ := by
  have le01 : ReachState.Le σ (sweepSeed Γ σ) :=
    foldl_le (seedHypRule Γ) (fun σ i => seedHypRule_le Γ σ i) _ σ
  have le12 : ReachState.Le (sweepSeed Γ σ) (unitEtaRule (sweepSeed Γ σ)) :=
    unitEtaRule_le _
  have le23 : ReachState.Le (unitEtaRule (sweepSeed Γ σ)) (reachSweep Γ σ) :=
    foldl_le (hypRule Γ) (fun σ i => hypRule_le Γ σ i) _ _
  have le3f : ReachState.Le (reachSweep Γ σ) σ := by
    have h2 : ReachState.Le (reachSweep Γ σ) (reachStep Γ σ) :=
      foldl_le typeRule (fun σ i => typeRule_le σ i) _ _
    rw [h] at h2
    exact h2
  have e1 : sweepSeed Γ σ = σ :=
    ReachState.eq_of_sandwich le01 ((le12.trans le23).trans le3f)
  have e2 : unitEtaRule (sweepSeed Γ σ) = σ :=
    ReachState.eq_of_sandwich (le01.trans le12) (le23.trans le3f)
  have esweep : reachSweep Γ σ = σ :=
    ReachState.eq_of_sandwich ((le01.trans le12).trans le23) le3f
  have hstep : (List.range σ.types.size).foldl typeRule σ = σ := by
    have hs : (List.range (reachSweep Γ σ).types.size).foldl typeRule (reachSweep Γ σ)
        = σ := h
    rw [esweep] at hs
    exact hs
  rw [e1] at e2
  have e3 : (List.range Γ.hyps.size).foldl (hypRule Γ) σ = σ := by
    have h3 : (List.range Γ.hyps.size).foldl (hypRule Γ)
        (unitEtaRule (sweepSeed Γ σ)) = σ := esweep
    rw [e1, e2] at h3
    exact h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    exact foldl_fix (seedHypRule Γ) (fun σ i => seedHypRule_le Γ σ i) _ σ e1 k
      (List.mem_range.mpr hk)
  · exact e2
  · intro k hk
    exact foldl_fix (hypRule Γ) (fun σ i => hypRule_le Γ σ i) _ σ e3 k
      (List.mem_range.mpr hk)
  · intro i hi
    exact foldl_fix typeRule (fun σ i => typeRule_le σ i) _ σ hstep i
      (List.mem_range.mpr hi)

/-! ### Everything the rules need is in the table -/

/-- Closure invariants of the state a run is performed on. -/
structure ReachFixed (Γ : ReachCtx n) (σ : ReachState n) : Prop where
  fix : ReachFix Γ σ
  sized : ReachState.Sized σ
  hypsMem : ∀ (k : Nat) (A : Object n), Γ.hyps[k]? = some A → A ∈ σ.types
  stepMem : ∀ A ∈ σ.types, ∀ B ∈ subformulaStep A, B ∈ σ.types

namespace ReachFixed

variable {Γ : ReachCtx n} {σ : ReachState n}

theorem prodTypeRule_eq (hf : ReachFixed Γ σ) {i : Nat} {L R : Object n}
    (hty : σ.typeAt i = some (.prod L R)) : prodTypeRule σ i L R = σ := by
  have ht := hf.fix.type i (lt_types_of_typeAt hty)
  unfold typeRule at ht
  rw [hty] at ht
  exact ht

theorem coprodTypeRule_eq (hf : ReachFixed Γ σ) {i : Nat} {L R : Object n}
    (hty : σ.typeAt i = some (.coprod L R)) : coprodTypeRule σ i L R = σ := by
  have ht := hf.fix.type i (lt_types_of_typeAt hty)
  unfold typeRule at ht
  rw [hty] at ht
  exact ht

theorem expRules_eq (hf : ReachFixed Γ σ) {i : Nat} {Arg Ret : Object n}
    (hty : σ.typeAt i = some (.exp Arg Ret)) :
    expEtaRule σ i Ret = σ ∧ expAppRule σ i Arg Ret = σ := by
  have ht0 := hf.fix.type i (lt_types_of_typeAt hty)
  unfold typeRule at ht0
  rw [hty] at ht0
  have ht : expAppRule (expEtaRule σ i Ret) i Arg Ret = σ := ht0
  have hle : ReachState.Le (expEtaRule σ i Ret) σ := by
    have h2 := expAppRule_le (expEtaRule σ i Ret) i Arg Ret
    rw [ht] at h2
    exact h2
  have he : expEtaRule σ i Ret = σ :=
    ReachState.eq_of_sandwich (expEtaRule_le σ i Ret) hle
  rw [he] at ht
  exact ⟨he, ht⟩

theorem expEtaRule_eq (hf : ReachFixed Γ σ) {i : Nat} {Arg Ret : Object n}
    (hty : σ.typeAt i = some (.exp Arg Ret)) : expEtaRule σ i Ret = σ :=
  (hf.expRules_eq hty).1

theorem expAppRule_eq (hf : ReachFixed Γ σ) {i : Nat} {Arg Ret : Object n}
    (hty : σ.typeAt i = some (.exp Arg Ret)) : expAppRule σ i Arg Ret = σ :=
  (hf.expRules_eq hty).2

theorem hypProdRule_eq (hf : ReachFixed Γ σ) {k : Nat} {L R : Object n}
    (hk : Γ.hyps[k]? = some (.prod L R)) : hypProdRule Γ σ k L R = σ := by
  have ht := hf.fix.hyp k (lt_size_of_getElem? hk)
  unfold hypRule at ht
  rw [hk] at ht
  exact ht

theorem hypAppRule_eq (hf : ReachFixed Γ σ) {k : Nat} {Arg Ret : Object n}
    (hk : Γ.hyps[k]? = some (.exp Arg Ret)) : hypAppRule Γ σ k Arg Ret = σ := by
  have ht := hf.fix.hyp k (lt_size_of_getElem? hk)
  unfold hypRule at ht
  rw [hk] at ht
  exact ht

theorem markHyp_eq (hf : ReachFixed Γ σ) {k : Nat} {A : Object n}
    (hk : Γ.hyps[k]? = some A) (hp : objectPolarity A = .pos) : σ.markHyp Γ k = σ := by
  have ht := hf.fix.seed k (lt_size_of_getElem? hk)
  unfold seedHypRule at ht
  rw [hk] at ht
  simpa [hp] using ht

/-- Both immediate subformulas of a table entry are in the table. -/
theorem memL (hf : ReachFixed Γ σ) {L R : Object n}
    (h : (.prod L R : Object n) ∈ σ.types) : L ∈ σ.types :=
  hf.stepMem _ h L (by simp [subformulaStep])

theorem memR (hf : ReachFixed Γ σ) {L R : Object n}
    (h : (.prod L R : Object n) ∈ σ.types) : R ∈ σ.types :=
  hf.stepMem _ h R (by simp [subformulaStep])

theorem memCoL (hf : ReachFixed Γ σ) {L R : Object n}
    (h : (.coprod L R : Object n) ∈ σ.types) : L ∈ σ.types :=
  hf.stepMem _ h L (by simp [subformulaStep])

theorem memCoR (hf : ReachFixed Γ σ) {L R : Object n}
    (h : (.coprod L R : Object n) ∈ σ.types) : R ∈ σ.types :=
  hf.stepMem _ h R (by simp [subformulaStep])

theorem memArg (hf : ReachFixed Γ σ) {Arg Ret : Object n}
    (h : (.exp Arg Ret : Object n) ∈ σ.types) : Arg ∈ σ.types :=
  hf.stepMem _ h Arg (by simp [subformulaStep])

theorem memRet (hf : ReachFixed Γ σ) {Arg Ret : Object n}
    (h : (.exp Arg Ret : Object n) ∈ σ.types) : Ret ∈ σ.types :=
  hf.stepMem _ h Ret (by simp [subformulaStep])

end ReachFixed

/-! ### Completeness -/

/-- Every derivation stays inside the formula universe it is restricted to. -/
theorem Deduce.univ {Γ : ReachCtx n} {ok : Nat → Prop} {U : Object n → Prop}
    {A : Object n} (d : Deduce Γ ok U A) : U A := by
  cases d <;> assumption

/--
Completeness for the fragment the finite table represents: in a consistent
fixed point, every subformula-restricted derivation has already been recorded.
-/
theorem complete_of_fixed {Γ : ReachCtx n} {σ : ReachState n} (hf : ReachFixed Γ σ)
    (hs : ReachSound Γ σ) (hcon : σ.inconsistent = false) {A : Object n}
    (d : SubDeduction (fun B => B ∈ σ.types) Γ A) : isSimplyDeducible σ A = true := by
  induction d with
  | @hyp A k hk hp _ hu =>
      obtain ⟨i, hi⟩ := exists_findTypeIdx hu
      have hret := ReachState.retrievable_of_markHyp_eq hf.sized hk hi
        (hf.markHyp_eq hk hp)
      exact isSimplyDeducible_of_index hi (by simp [ReachCell.simplyDeducible, hret])
  | @unit hu =>
      obtain ⟨i, hi⟩ := exists_findTypeIdx hu
      have hrule := hf.fix.unitEta
      unfold unitEtaRule at hrule
      rw [hi] at hrule
      exact isSimplyDeducible_of_index hi
        (ReachState.simplyDeducible_of_discover_eq hf.sized
          (ReachState.typeAt_of_findTypeIdx hi) hrule)
  | @fstHyp L R k hk _ hu =>
      have hprod := hf.hypsMem k _ hk
      obtain ⟨p, hp⟩ := exists_findTypeIdx hprod
      obtain ⟨l, hl⟩ := exists_findTypeIdx hu
      obtain ⟨r, hr⟩ := exists_findTypeIdx (hf.memR hprod)
      have hrule := hf.hypProdRule_eq hk
      unfold hypProdRule at hrule
      rw [hp, hl, hr] at hrule
      dsimp only at hrule
      have h2 := ReachState.le_discover (σ.discover l (Γ.isNew k) (.fst p)) r
        (Γ.isNew k) (.snd p)
      rw [hrule] at h2
      have h1 := ReachState.eq_of_sandwich
        (ReachState.le_discover σ l (Γ.isNew k) (.fst p)) h2
      exact isSimplyDeducible_of_index hl
        (ReachState.simplyDeducible_of_discover_eq hf.sized
          (ReachState.typeAt_of_findTypeIdx hl) h1)
  | @sndHyp L R k hk _ hu =>
      have hprod := hf.hypsMem k _ hk
      obtain ⟨p, hp⟩ := exists_findTypeIdx hprod
      obtain ⟨l, hl⟩ := exists_findTypeIdx (hf.memL hprod)
      obtain ⟨r, hr⟩ := exists_findTypeIdx hu
      have hrule := hf.hypProdRule_eq hk
      unfold hypProdRule at hrule
      rw [hp, hl, hr] at hrule
      dsimp only at hrule
      have h2 := ReachState.le_discover (σ.discover l (Γ.isNew k) (.fst p)) r
        (Γ.isNew k) (.snd p)
      rw [hrule] at h2
      have h1 := ReachState.eq_of_sandwich
        (ReachState.le_discover σ l (Γ.isNew k) (.fst p)) h2
      rw [h1] at hrule
      exact isSimplyDeducible_of_index hr
        (ReachState.simplyDeducible_of_discover_eq hf.sized
          (ReachState.typeAt_of_findTypeIdx hr) hrule)
  | @fst L R hd hu ih =>
      have hprod := hd.univ
      obtain ⟨p, hp⟩ := exists_findTypeIdx hprod
      obtain ⟨l, hl⟩ := exists_findTypeIdx hu
      obtain ⟨r, hr⟩ := exists_findTypeIdx (hf.memR hprod)
      have hdec := index_deducible hp ih
      have hrule := hf.prodTypeRule_eq (ReachState.typeAt_of_findTypeIdx hp)
      unfold prodTypeRule at hrule
      rw [if_pos hdec, hl, hr] at hrule
      dsimp only at hrule
      have h2 := ReachState.le_discover (σ.discover l (σ.getCell p).usesNew (.fst p)) r
        (σ.getCell p).usesNew (.snd p)
      rw [hrule] at h2
      have h1 := ReachState.eq_of_sandwich
        (ReachState.le_discover σ l (σ.getCell p).usesNew (.fst p)) h2
      exact isSimplyDeducible_of_index hl
        (ReachState.simplyDeducible_of_discover_eq hf.sized
          (ReachState.typeAt_of_findTypeIdx hl) h1)
  | @snd L R hd hu ih =>
      have hprod := hd.univ
      obtain ⟨p, hp⟩ := exists_findTypeIdx hprod
      obtain ⟨l, hl⟩ := exists_findTypeIdx (hf.memL hprod)
      obtain ⟨r, hr⟩ := exists_findTypeIdx hu
      have hdec := index_deducible hp ih
      have hrule := hf.prodTypeRule_eq (ReachState.typeAt_of_findTypeIdx hp)
      unfold prodTypeRule at hrule
      rw [if_pos hdec, hl, hr] at hrule
      dsimp only at hrule
      have h2 := ReachState.le_discover (σ.discover l (σ.getCell p).usesNew (.fst p)) r
        (σ.getCell p).usesNew (.snd p)
      rw [hrule] at h2
      have h1 := ReachState.eq_of_sandwich
        (ReachState.le_discover σ l (σ.getCell p).usesNew (.fst p)) h2
      rw [h1] at hrule
      exact isSimplyDeducible_of_index hr
        (ReachState.simplyDeducible_of_discover_eq hf.sized
          (ReachState.typeAt_of_findTypeIdx hr) hrule)
  | @pair L R hdl hdr hu ihl ihr =>
      obtain ⟨p, hp⟩ := exists_findTypeIdx hu
      by_cases hdec : (σ.getCell p).simplyDeducible = true
      · exact isSimplyDeducible_of_index hp hdec
      · obtain ⟨l, hl⟩ := exists_findTypeIdx hdl.univ
        obtain ⟨r, hr⟩ := exists_findTypeIdx hdr.univ
        have hrule := hf.prodTypeRule_eq (ReachState.typeAt_of_findTypeIdx hp)
        unfold prodTypeRule at hrule
        rw [if_neg hdec, hl, hr] at hrule
        dsimp only at hrule
        have hb : ((σ.getCell l).simplyDeducible && (σ.getCell r).simplyDeducible) = true := by
          simp [index_deducible hl ihl, index_deducible hr ihr]
        rw [if_pos hb] at hrule
        exact isSimplyDeducible_of_index hp
          (ReachState.simplyDeducible_of_discover_eq hf.sized
            (ReachState.typeAt_of_findTypeIdx hp) hrule)
  | @inl L R hd hu ih =>
      obtain ⟨p, hp⟩ := exists_findTypeIdx hu
      by_cases hdec : (σ.getCell p).simplyDeducible = true
      · exact isSimplyDeducible_of_index hp hdec
      · obtain ⟨l, hl⟩ := exists_findTypeIdx hd.univ
        obtain ⟨r, hr⟩ := exists_findTypeIdx (hf.memCoR hu)
        have hrule := hf.coprodTypeRule_eq (ReachState.typeAt_of_findTypeIdx hp)
        unfold coprodTypeRule at hrule
        rw [if_pos (by simp [hdec] : (!(σ.getCell p).simplyDeducible) = true), hl, hr]
          at hrule
        dsimp only at hrule
        rw [if_pos (index_deducible hl ih)] at hrule
        exact isSimplyDeducible_of_index hp
          (ReachState.simplyDeducible_of_discover_eq hf.sized
            (ReachState.typeAt_of_findTypeIdx hp) hrule)
  | @inr L R hd hu ih =>
      obtain ⟨p, hp⟩ := exists_findTypeIdx hu
      by_cases hdec : (σ.getCell p).simplyDeducible = true
      · exact isSimplyDeducible_of_index hp hdec
      · obtain ⟨l, hl⟩ := exists_findTypeIdx (hf.memCoL hu)
        obtain ⟨r, hr⟩ := exists_findTypeIdx hd.univ
        have hrule := hf.coprodTypeRule_eq (ReachState.typeAt_of_findTypeIdx hp)
        unfold coprodTypeRule at hrule
        rw [if_pos (by simp [hdec] : (!(σ.getCell p).simplyDeducible) = true), hl, hr]
          at hrule
        dsimp only at hrule
        by_cases hlft : (σ.getCell l).simplyDeducible = true
        · rw [if_pos hlft] at hrule
          exact isSimplyDeducible_of_index hp
            (ReachState.simplyDeducible_of_discover_eq hf.sized
              (ReachState.typeAt_of_findTypeIdx hp) hrule)
        · rw [if_neg hlft, if_pos (index_deducible hr ih)] at hrule
          exact isSimplyDeducible_of_index hp
            (ReachState.simplyDeducible_of_discover_eq hf.sized
              (ReachState.typeAt_of_findTypeIdx hp) hrule)
  | @appHyp Arg Ret k hk _ hd hu ih =>
      have hexp := hf.hypsMem k _ hk
      obtain ⟨a, ha⟩ := exists_findTypeIdx (hf.memArg hexp)
      obtain ⟨r, hr⟩ := exists_findTypeIdx hu
      have hrule := hf.hypAppRule_eq hk
      unfold hypAppRule at hrule
      rw [ha, hr] at hrule
      dsimp only at hrule
      rw [if_pos (index_deducible ha ih)] at hrule
      exact isSimplyDeducible_of_index hr
        (ReachState.simplyDeducible_of_discover_eq hf.sized
          (ReachState.typeAt_of_findTypeIdx hr) hrule)
  | @appTy Arg Ret hdf hda hu ihf iha =>
      have hexp := hdf.univ
      obtain ⟨t, ht⟩ := exists_findTypeIdx hexp
      obtain ⟨a, ha⟩ := exists_findTypeIdx hda.univ
      obtain ⟨r, hr⟩ := exists_findTypeIdx hu
      have hrule := hf.expAppRule_eq (ReachState.typeAt_of_findTypeIdx ht)
      unfold expAppRule at hrule
      rw [if_pos (index_deducible ht ihf), ha, hr] at hrule
      dsimp only at hrule
      rw [if_pos (index_deducible ha iha)] at hrule
      exact isSimplyDeducible_of_index hr
        (ReachState.simplyDeducible_of_discover_eq hf.sized
          (ReachState.typeAt_of_findTypeIdx hr) hrule)
  | @expEta Arg Ret hd hu ih =>
      obtain ⟨t, ht⟩ := exists_findTypeIdx hu
      by_cases hdec : (σ.getCell t).simplyDeducible = true
      · exact isSimplyDeducible_of_index ht hdec
      · obtain ⟨r, hr⟩ := exists_findTypeIdx hd.univ
        have hrule := hf.expEtaRule_eq (ReachState.typeAt_of_findTypeIdx ht)
        unfold expEtaRule at hrule
        rw [if_pos (by simp [hdec] : (!(σ.getCell t).simplyDeducible) = true), hr]
          at hrule
        dsimp only at hrule
        rw [if_pos (index_deducible hr ih)] at hrule
        exact isSimplyDeducible_of_index ht
          (ReachState.simplyDeducible_of_discover_eq hf.sized
            (ReachState.typeAt_of_findTypeIdx ht) hrule)
  | @exFalso A hd hu ih =>
      obtain ⟨j, hj⟩ := exists_findTypeIdx hd.univ
      have hbad := hs.neverFlagged j (ReachState.typeAt_of_findTypeIdx hj)
        (index_deducible hj ih)
      rw [hcon] at hbad
      exact absurd hbad (by simp)

/-! ### The run is a fixed point with a closed table -/

theorem mkReachState_types (Γ : ReachCtx n) (goal : Object n) :
    (mkReachState Γ goal).types = subformulaClosure (Γ.roots goal) :=
  ((foldl_le (seedHypRule Γ) (fun σ i => seedHypRule_le Γ σ i) _ _).types).symm

theorem mkReachState_sized (Γ : ReachCtx n) (goal : Object n) :
    ReachState.Sized (mkReachState Γ goal) := by
  refine ReachState.Sized.mono
    (foldl_le (seedHypRule Γ) (fun σ i => seedHypRule_le Γ σ i) _ _) ?_
  show (Array.replicate (subformulaClosure (Γ.roots goal)).size ReachCell.empty).size = _
  simp

theorem runReachability_types (Γ : ReachCtx n) (goal : Object n) :
    (runReachability Γ goal).types = subformulaClosure (Γ.roots goal) :=
  ((le_runReachabilityFrom Γ _).types).symm.trans (mkReachState_types Γ goal)

theorem runReachability_sized (Γ : ReachCtx n) (goal : Object n) :
    ReachState.Sized (runReachability Γ goal) :=
  ReachState.Sized.mono (le_runReachabilityFrom Γ _) (mkReachState_sized Γ goal)

/-- The finite table is closed under everything the rules look up. -/
theorem runReachability_fixed (Γ : ReachCtx n) (goal : Object n) :
    ReachFixed Γ (runReachability Γ goal) := by
  refine ⟨reachFix_of_reachStep_eq (reachStep_runReachability Γ goal),
    runReachability_sized Γ goal, ?_, ?_⟩
  · intro k A hk
    rw [runReachability_types]
    refine mem_subformulaClosure_of_mem_roots ?_
    exact List.mem_cons_of_mem _ (by simpa using mem_of_getElem? hk)
  · intro A hA B hB
    rw [runReachability_types] at hA ⊢
    exact mem_subformulaClosure_of_step hA hB

/-! ### Headline completeness statements -/

/--
Every fact derivable inside the subformula universe is discovered, unless the
closure has already detected that the context is inconsistent.
-/
theorem runReachability_complete (Γ : ReachCtx n) (goal : Object n) {A : Object n}
    (d : SubDeduction (fun B => B ∈ (runReachability Γ goal).types) Γ A) :
    isSimplyDeducible (runReachability Γ goal) A = true ∨
      (runReachability Γ goal).inconsistent = true := by
  cases hcon : (runReachability Γ goal).inconsistent with
  | true => exact Or.inr rfl
  | false =>
      exact Or.inl (complete_of_fixed (runReachability_fixed Γ goal)
        (runReachability_sound Γ goal) hcon d)

/-- `0` is discovered whenever the context is inconsistent inside the table. -/
theorem inconsistent_of_never_derivable (Γ : ReachCtx n) (goal : Object n)
    (d : SubDeduction (fun B => B ∈ (runReachability Γ goal).types) Γ
      (.never : Object n)) :
    (runReachability Γ goal).inconsistent = true := by
  rcases runReachability_complete Γ goal d with h | h
  · exact inconsistent_of_never_deducible h
  · exact h

/--
Soundness and completeness meet on the subformula fragment of a consistent
context: there, `isSimplyDeducible` is exactly derivability.
-/
theorem isSimplyDeducible_iff_subDeduction (Γ : ReachCtx n) (goal : Object n)
    {A : Object n} (hcon : (runReachability Γ goal).inconsistent = false)
    (hclosed : ∀ B, SimpleDeduction Γ B →
      SubDeduction (fun C => C ∈ (runReachability Γ goal).types) Γ B) :
    isSimplyDeducible (runReachability Γ goal) A = true ↔ SimpleDeduction Γ A :=
  ⟨isSimplyDeducible_sound, fun h =>
    complete_of_fixed (runReachability_fixed Γ goal) (runReachability_sound Γ goal)
      hcon (hclosed A h)⟩

end Equality
end Gimbal
