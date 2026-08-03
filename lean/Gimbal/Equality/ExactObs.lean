/-
  Exact-observation collection, union and selection (Milestone 8D).

  Schedule entries are compared up to observation identity (`exactIdEq`: same
  result type and same raw spine), which is an equivalence. Every collector in
  the pair-directed pipeline is a fold over `insertExact`, so its content is
  characterised by a single membership equation. From that equation the union
  is symmetric and idempotent, complete for both focused inputs, preserved by
  selection, and new-dependence is upward closed.
-/

import Gimbal.Equality.Saturation

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- A collected exact observation: a positive result type and its spine. -/
abbrev Exact (Γ : Ctx sig) := (P : Object sig.nBases) × NegNeu Γ P

variable {Γ : Ctx sig}

/-! ### Observation identity is an equivalence -/

theorem exactIdEq_iff (e f : Exact Γ) :
    exactIdEq e f = true ↔ e.1 = f.1 ∧ NegNeu.toRaw e.2 = NegNeu.toRaw f.2 := by
  simp [exactIdEq]

@[simp] theorem exactIdEq_refl (e : Exact Γ) : exactIdEq e e = true := by
  simp [exactIdEq]

theorem exactIdEq_symm {e f : Exact Γ} (h : exactIdEq e f = true) :
    exactIdEq f e = true := by
  rw [exactIdEq_iff] at h ⊢
  exact ⟨h.1.symm, h.2.symm⟩

theorem exactIdEq_trans {e f g : Exact Γ} (h₁ : exactIdEq e f = true)
    (h₂ : exactIdEq f g = true) : exactIdEq e g = true := by
  rw [exactIdEq_iff] at h₁ h₂ ⊢
  exact ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- Identity of spines settles whether an observation is a bare hypothesis. -/
theorem isVar_congr {A B : Object sig.nBases} {n : NegNeu Γ A} {m : NegNeu Γ B}
    (h : NegNeu.toRaw n = NegNeu.toRaw m) : n.isVar = m.isVar := by
  cases n <;> cases m <;> simp_all [NegNeu.isVar, NegNeu.toRaw]

/-! ### Membership up to identity -/

/-- `e` has already been observed by `s`, up to observation identity. -/
def MemI (s : Array (Exact Γ)) (e : Exact Γ) : Prop :=
  s.any (exactIdEq e) = true

theorem memI_iff {s : Array (Exact Γ)} {e : Exact Γ} :
    MemI s e ↔ ∃ x ∈ s, exactIdEq e x = true :=
  Array.any_eq_true'

theorem memI_of_mem {s : Array (Exact Γ)} {e : Exact Γ} (h : e ∈ s) : MemI s e :=
  memI_iff.mpr ⟨e, h, exactIdEq_refl e⟩

theorem memI_congr {s : Array (Exact Γ)} {e f : Exact Γ} (h : MemI s e)
    (hef : exactIdEq f e = true) : MemI s f := by
  obtain ⟨x, hx, hex⟩ := memI_iff.mp h
  exact memI_iff.mpr ⟨x, hx, exactIdEq_trans hef hex⟩

theorem memI_push {s : Array (Exact Γ)} {e x : Exact Γ} :
    MemI (s.push x) e ↔ MemI s e ∨ exactIdEq e x = true := by
  simp only [memI_iff, Array.mem_push]
  constructor
  · rintro ⟨y, hy | rfl, h⟩
    · exact Or.inl ⟨y, hy, h⟩
    · exact Or.inr h
  · rintro (⟨y, hy, h⟩ | h)
    · exact ⟨y, Or.inl hy, h⟩
    · exact ⟨x, Or.inr rfl, h⟩

@[simp] theorem memI_insertExact {s : Array (Exact Γ)} {e x : Exact Γ} :
    MemI (insertExact s x) e ↔ MemI s e ∨ exactIdEq e x = true := by
  unfold insertExact
  split
  · rename_i hx
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · exact memI_congr (show MemI s x from hx) h
  · exact memI_push

theorem memI_insertExact_self (s : Array (Exact Γ)) (x : Exact Γ) :
    MemI (insertExact s x) x :=
  memI_insertExact.mpr (Or.inr (exactIdEq_refl x))

theorem memI_insertExact_of_memI {s : Array (Exact Γ)} {e x : Exact Γ}
    (h : MemI s e) : MemI (insertExact s x) e :=
  memI_insertExact.mpr (Or.inl h)

/-- Insertion never invents an entry. -/
theorem mem_insertExact {s : Array (Exact Γ)} {e x : Exact Γ}
    (h : e ∈ insertExact s x) : e ∈ s ∨ e = x := by
  unfold insertExact at h
  split at h
  · exact Or.inl h
  · rcases Array.mem_push.mp h with h | h
    · exact Or.inl h
    · exact Or.inr h

/-! ### Folding the insertion step -/

theorem memI_foldl_insert :
    ∀ (l : List (Exact Γ)) (acc : Array (Exact Γ)) (e : Exact Γ),
      MemI (l.foldl insertExact acc) e ↔
        MemI acc e ∨ ∃ x ∈ l, exactIdEq e x = true
  | [], acc, e => by simp
  | a :: l, acc, e => by
      rw [List.foldl_cons, memI_foldl_insert l (insertExact acc a) e]
      simp only [memI_insertExact, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨x, hx, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨a, Or.inl rfl, h⟩
        · exact Or.inr ⟨x, Or.inr hx, h⟩
      · rintro (h | ⟨x, rfl | hx, h⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨x, hx, h⟩

theorem mem_foldl_insert :
    ∀ (l : List (Exact Γ)) (acc : Array (Exact Γ)) (e : Exact Γ),
      e ∈ l.foldl insertExact acc → e ∈ acc ∨ e ∈ l
  | [], _, _, h => Or.inl h
  | a :: l, acc, e, h => by
      rw [List.foldl_cons] at h
      rcases mem_foldl_insert l (insertExact acc a) e h with h | h
      · rcases mem_insertExact h with h | rfl
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem memI_array_foldl_insert (s : Array (Exact Γ)) (acc : Array (Exact Γ))
    (e : Exact Γ) :
    MemI (s.foldl insertExact acc) e ↔ MemI acc e ∨ MemI s e := by
  rw [← Array.foldl_toList, memI_foldl_insert]
  constructor
  · rintro (h | ⟨x, hx, hex⟩)
    · exact Or.inl h
    · exact Or.inr (memI_iff.mpr ⟨x, Array.mem_toList_iff.mp hx, hex⟩)
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨x, hx, hex⟩ := memI_iff.mp h
      exact Or.inr ⟨x, Array.mem_toList_iff.mpr hx, hex⟩

theorem mem_array_foldl_insert {s acc : Array (Exact Γ)} {e : Exact Γ}
    (h : e ∈ s.foldl insertExact acc) : e ∈ acc ∨ e ∈ s := by
  rw [← Array.foldl_toList] at h
  simpa using mem_foldl_insert _ _ _ h

/-! ### The collector only ever adds -/

theorem memI_pushExact {A : Object sig.nBases} {acc : Array (Exact Γ)}
    {n : NegNeu Γ A} {e : Exact Γ} (h : MemI acc e) : MemI (pushExact acc n) e := by
  unfold pushExact
  split
  · exact memI_insertExact_of_memI h
  · exact h

theorem memI_pushExact_self {A : Object sig.nBases} (acc : Array (Exact Γ))
    (n : NegNeu Γ A) (hp : objectPolarity A = .pos) :
    MemI (pushExact acc n) ⟨A, n⟩ := by
  unfold pushExact
  rw [if_pos (by simp [hp])]
  exact memI_insertExact_self _ _

mutual

theorem memI_exactNegNeu {A : Object sig.nBases} (n : NegNeu Γ A)
    (acc : Array (Exact Γ)) (e : Exact Γ) (h : MemI acc e) :
    MemI (exactNegNeu n acc) e :=
  match n with
  | .var x => memI_pushExact (n := (.var x : NegNeu Γ A)) h
  | .app f t =>
      memI_exactInvTm t _ e (memI_exactNegNeu f _ e (memI_pushExact h))
  | .fst f => memI_exactNegNeu f _ e (memI_pushExact h)
  | .snd f => memI_exactNegNeu f _ e (memI_pushExact h)

theorem memI_exactPosNeu {A : Object sig.nBases} (p : PosNeu Γ A)
    (acc : Array (Exact Γ)) (e : Exact Γ) (h : MemI acc e) :
    MemI (exactPosNeu p acc) e :=
  match p with
  | .neu m => memI_exactNegNeu m _ e h
  | .inl q => memI_exactPosNeu q _ e h
  | .inr q => memI_exactPosNeu q _ e h
  | .val t => memI_exactInvTm t _ e h

theorem memI_exactInvTm {A : Object sig.nBases} (t : InvTm Γ A)
    (acc : Array (Exact Γ)) (e : Exact Γ) (h : MemI acc e) :
    MemI (exactInvTm t acc) e :=
  match t with
  | .unit => h
  | .pair t u => memI_exactInvTm u _ e (memI_exactInvTm t _ e h)
  | .lam _ => h
  | .case m _ _ => memI_exactNegNeu m _ e h
  | .abort m => memI_exactNegNeu m _ e h
  | .foc f => memI_exactFocTm f _ e h

theorem memI_exactFocTm {A : Object sig.nBases} (f : FocTm Γ A)
    (acc : Array (Exact Γ)) (e : Exact Γ) (h : MemI acc e) :
    MemI (exactFocTm f acc) e :=
  match f with
  | .pos (.done p) => memI_exactPosNeu p _ e h
  | .neg (.done m) => memI_exactNegNeu m _ e h
  | .letPos m _ => memI_exactNegNeu m _ e h
  | .sat (.mk _ t) => memI_exactInvTm t _ e h

end

/-- A positive-typed neutral always observes itself. -/
theorem memI_exactNegNeu_self {A : Object sig.nBases} (n : NegNeu Γ A)
    (acc : Array (Exact Γ)) (hp : objectPolarity A = .pos) :
    MemI (exactNegNeu n acc) ⟨A, n⟩ := by
  match n with
  | .var x => exact memI_pushExact_self acc (.var x) hp
  | .app f t =>
      exact memI_exactInvTm t _ _
        (memI_exactNegNeu f _ _ (memI_pushExact_self acc (.app f t) hp))
  | .fst f => exact memI_exactNegNeu f _ _ (memI_pushExact_self acc (.fst f) hp)
  | .snd f => exact memI_exactNegNeu f _ _ (memI_pushExact_self acc (.snd f) hp)

/-! ### Spine completeness

Every positive-typed neutral inside a spine is collected when the spine is.
-/

/-- `m` occurs in the spine of `n`. -/
inductive SpineObs {Γ : Ctx sig} :
    ∀ {A P : Object sig.nBases}, NegNeu Γ A → NegNeu Γ P → Prop where
  | self {P : Object sig.nBases} (m : NegNeu Γ P) : SpineObs m m
  | app {A B P : Object sig.nBases} {f : NegNeu Γ (.exp A B)} {t : InvTm Γ A}
      {m : NegNeu Γ P} : SpineObs f m → SpineObs (.app f t) m
  | fst {A B P : Object sig.nBases} {f : NegNeu Γ (.prod A B)} {m : NegNeu Γ P} :
      SpineObs f m → SpineObs (.fst f) m
  | snd {A B P : Object sig.nBases} {f : NegNeu Γ (.prod A B)} {m : NegNeu Γ P} :
      SpineObs f m → SpineObs (.snd f) m

theorem memI_exactNegNeu_of_spineObs {A P : Object sig.nBases} {n : NegNeu Γ A}
    {m : NegNeu Γ P} (h : SpineObs n m) :
    objectPolarity P = .pos → ∀ acc : Array (Exact Γ),
      MemI (exactNegNeu n acc) ⟨P, m⟩ := by
  induction h with
  | self m => exact fun hp acc => memI_exactNegNeu_self m acc hp
  | app _ ih =>
      exact fun hp acc => memI_exactInvTm _ _ _ (ih hp (pushExact acc _))
  | fst _ ih => exact fun hp acc => ih hp (pushExact acc _)
  | snd _ ih => exact fun hp acc => ih hp (pushExact acc _)

/-! ### The canonical union of exact observations -/

/-- The union observes exactly what either side observes. -/
@[simp] theorem memI_unionExact {a b : Array (Exact Γ)} {e : Exact Γ} :
    MemI (unionExact a b) e ↔ MemI a e ∨ MemI b e := by
  unfold unionExact
  rw [memI_array_foldl_insert, memI_array_foldl_insert]
  have : ¬ MemI (#[] : Array (Exact Γ)) e := by simp [MemI]
  tauto

/-- Completeness for the left focused input. -/
theorem memI_unionExact_left {a b : Array (Exact Γ)} {e : Exact Γ} (h : MemI a e) :
    MemI (unionExact a b) e :=
  memI_unionExact.mpr (Or.inl h)

/-- Completeness for the right focused input. -/
theorem memI_unionExact_right {a b : Array (Exact Γ)} {e : Exact Γ} (h : MemI b e) :
    MemI (unionExact a b) e :=
  memI_unionExact.mpr (Or.inr h)

/-- Symmetry: the union observes the same set from either side. -/
theorem unionExact_comm (a b : Array (Exact Γ)) (e : Exact Γ) :
    MemI (unionExact a b) e ↔ MemI (unionExact b a) e := by
  simp only [memI_unionExact]
  tauto

/-- Idempotence. -/
theorem unionExact_idem (a : Array (Exact Γ)) (e : Exact Γ) :
    MemI (unionExact a a) e ↔ MemI a e := by
  simp only [memI_unionExact]
  tauto

/-- Associativity, as observation sets. -/
theorem unionExact_assoc (a b c : Array (Exact Γ)) (e : Exact Γ) :
    MemI (unionExact (unionExact a b) c) e ↔ MemI (unionExact a (unionExact b c)) e := by
  simp only [memI_unionExact]
  tauto

/-- The union invents nothing: every entry came from one of the inputs. -/
theorem mem_unionExact {a b : Array (Exact Γ)} {e : Exact Γ}
    (h : e ∈ unionExact a b) : e ∈ a ∨ e ∈ b := by
  unfold unionExact at h
  rcases mem_array_foldl_insert h with h | h
  · rcases mem_array_foldl_insert h with h | h
    · exact absurd h (by simp)
    · exact Or.inl h
  · exact Or.inr h

/-! ### New-dependence is preserved -/

theorem exactsAllUseNew_iff {hypsSize newFrom : Nat} {s : Array (Exact Γ)} :
    exactsAllUseNew hypsSize newFrom s = true ↔
      ∀ e ∈ s, NegNeu.mentionsNew hypsSize newFrom e.2 = true :=
  Array.all_eq_true'

/-- New-dependence is upward closed along the canonical union. -/
theorem exactsAllUseNew_unionExact {hypsSize newFrom : Nat} {a b : Array (Exact Γ)}
    (ha : exactsAllUseNew hypsSize newFrom a = true)
    (hb : exactsAllUseNew hypsSize newFrom b = true) :
    exactsAllUseNew hypsSize newFrom (unionExact a b) = true := by
  rw [exactsAllUseNew_iff] at ha hb ⊢
  intro e he
  rcases mem_unionExact he with h | h
  · exact ha e h
  · exact hb e h

/-! ### Selection -/

theorem mem_foldl_select :
    ∀ (l : List (Exact Γ)) (acc : Array (Exact Γ)) (e : Exact Γ),
      e ∈ l.foldl selectExactStep acc → e ∈ acc ∨ e ∈ l
  | [], _, _, h => Or.inl h
  | a :: l, acc, e, h => by
      rw [List.foldl_cons] at h
      rcases mem_foldl_select l (selectExactStep acc a) e h with h | h
      · unfold selectExactStep at h
        split at h
        · rcases mem_insertExact h with h | rfl
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem memI_foldl_select :
    ∀ (l : List (Exact Γ)) (acc : Array (Exact Γ)) (e : Exact Γ),
      MemI (l.foldl selectExactStep acc) e ↔
        MemI acc e ∨ ∃ x ∈ l, (objectPolarity x.1 == .pos && !x.2.isVar) = true ∧
          exactIdEq e x = true
  | [], acc, e => by simp
  | a :: l, acc, e => by
      rw [List.foldl_cons, memI_foldl_select l (selectExactStep acc a) e]
      unfold selectExactStep
      split
      · rename_i hkeep
        simp only [memI_insertExact, List.mem_cons]
        constructor
        · rintro ((h | h) | ⟨x, hx, hk, h⟩)
          · exact Or.inl h
          · exact Or.inr ⟨a, Or.inl rfl, hkeep, h⟩
          · exact Or.inr ⟨x, Or.inr hx, hk, h⟩
        · rintro (h | ⟨x, rfl | hx, hk, h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨x, hx, hk, h⟩
      · rename_i hdrop
        simp only [List.mem_cons]
        constructor
        · rintro (h | ⟨x, hx, hk, h⟩)
          · exact Or.inl h
          · exact Or.inr ⟨x, Or.inr hx, hk, h⟩
        · rintro (h | ⟨x, rfl | hx, hk, h⟩)
          · exact Or.inl h
          · exact absurd hk hdrop
          · exact Or.inr ⟨x, hx, hk, h⟩

theorem mem_selectExactObs {σ : ReachState sig.nBases}
    {hyps : Array (Object sig.nBases)}
    {ex : Array (Exact (Ctx.ofHyps hyps))} {e : Exact (Ctx.ofHyps hyps)}
    (h : e ∈ selectExactObs σ hyps ex) : e ∈ ex := by
  unfold selectExactObs at h
  rw [← Array.foldl_toList] at h
  rcases mem_foldl_select _ _ _ h with h | h
  · exact absurd h (by simp)
  · simpa using h

/-- Selection keeps every observation that still needs a strong positive cut. -/
theorem memI_selectExactObs {σ : ReachState sig.nBases}
    {hyps : Array (Object sig.nBases)}
    {ex : Array (Exact (Ctx.ofHyps hyps))} {e : Exact (Ctx.ofHyps hyps)}
    (hmem : MemI ex e) (hpos : objectPolarity e.1 = .pos) (hvar : e.2.isVar = false) :
    MemI (selectExactObs σ hyps ex) e := by
  unfold selectExactObs
  rw [← Array.foldl_toList, memI_foldl_select]
  refine Or.inr ?_
  obtain ⟨x, hx, hex⟩ := memI_iff.mp hmem
  obtain ⟨h1, h2⟩ := (exactIdEq_iff e x).mp hex
  exact ⟨x, by simpa using hx, by simp [← h1, hpos, isVar_congr h2.symm, hvar], hex⟩

/-- Selection is a subset, so validity of the input is inherited. -/
theorem exactsAllUseNew_selectExactObs {hypsSize newFrom : Nat}
    {σ : ReachState sig.nBases} {hyps : Array (Object sig.nBases)}
    {ex : Array (Exact (Ctx.ofHyps hyps))}
    (h : exactsAllUseNew hypsSize newFrom ex = true) :
    exactsAllUseNew hypsSize newFrom (selectExactObs σ hyps ex) = true := by
  rw [exactsAllUseNew_iff] at h ⊢
  exact fun e he => h e (mem_selectExactObs he)

/-! ### Completeness for both focused inputs -/

variable {A : Object sig.nBases}

/-- Nothing the left input demands is dropped by the union. -/
theorem memI_unionExact_collectExact_left (t u : InvTm Γ A) {e : Exact Γ}
    (h : MemI (collectExact t) e) :
    MemI (unionExact (collectExact t) (collectExact u)) e :=
  memI_unionExact_left h

/-- Nothing the right input demands is dropped by the union. -/
theorem memI_unionExact_collectExact_right (t u : InvTm Γ A) {e : Exact Γ}
    (h : MemI (collectExact u) e) :
    MemI (unionExact (collectExact t) (collectExact u)) e :=
  memI_unionExact_right h

/--
Exact-observation collection is complete for both focused inputs: an
observation demanded by either term and still needing a cut survives the
union and the selection filter.
-/
theorem memI_pairSelection {σ : ReachState sig.nBases}
    {hyps : Array (Object sig.nBases)} {A : Object sig.nBases}
    (t u : InvTm (Ctx.ofHyps hyps) A) {e : Exact (Ctx.ofHyps hyps)}
    (h : MemI (collectExact t) e ∨ MemI (collectExact u) e)
    (hpos : objectPolarity e.1 = .pos) (hvar : e.2.isVar = false) :
    MemI (selectExactObs σ hyps (unionExact (collectExact t) (collectExact u))) e :=
  memI_selectExactObs (memI_unionExact.mpr h) hpos hvar

/-- The pair-directed observation list only rejects genuinely old-only demands. -/
theorem pairObs_ok_of_allUseNew (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases)
    {A : Object sig.nBases} (t u : InvTm (Ctx.ofHyps Γ.hyps) A)
    (ht : exactsAllUseNew Γ.hyps.size Γ.newFrom (collectExact t) = true)
    (hu : exactsAllUseNew Γ.hyps.size Γ.newFrom (collectExact u) = true) :
    pairObs Γ goal t u =
      .ok
        (mergePairObs (runReachability Γ goal) Γ.hyps
          (buildSchedule (runReachability Γ goal))
          (selectExactObs (runReachability Γ goal) Γ.hyps
            (unionExact (collectExact t) (collectExact u))))
        (runReachability Γ goal) := by
  unfold pairObs
  rw [if_neg (by
    simp [exactsAllUseNew_selectExactObs (exactsAllUseNew_unionExact ht hu)])]

end Equality
end Gimbal
