/-
  Saturation returns a well-focused term.

  The saturated form is built from three kinds of material: the continuation it
  was handed, the observations in the schedule, and the binders it introduces
  for them. The first two are legal by hypothesis (and, for consistency
  observations, by `wellNeg_reconstructWitnessWF_ofCell`); this module
  supplies the third, i.e. that abstraction, the coproduct branches, and the
  schedule remapping all preserve phase legality.
-/

import Gimbal.Equality.ExactObs

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ### Raw abstraction preserves legality

Occurrence sites are replaced by a variable, which is legal at any type, and
everything else is congruence.
-/

mutual
theorem wellNeg_abstractAtom {Γ : Ctx sig} {P A : Object sig.nBases}
    (x : Var Γ P) (target : RawNeu) :
    ∀ {n : NegNeu Γ A}, WellNeg n → WellNeg (NegNeu.abstractAtom x target n)
  | .var _, _ => by
      rw [NegNeu.abstractAtom]
      split
      · split
        · rename_i hA hEq; clear hEq; cases hA; exact .var
        · exact .var
      · exact .var
  | .app _ _, .app hf ha => by
      rw [NegNeu.abstractAtom]
      split
      · split
        · rename_i hA hEq; clear hEq; cases hA; exact .var
        · exact .app (wellNeg_abstractAtom x target hf)
            (wellInv_abstractAtom x target ha)
      · exact .app (wellNeg_abstractAtom x target hf)
          (wellInv_abstractAtom x target ha)
  | .fst _, .fst hn => by
      rw [NegNeu.abstractAtom]
      split
      · split
        · rename_i hA hEq; clear hEq; cases hA; exact .var
        · exact .fst (wellNeg_abstractAtom x target hn)
      · exact .fst (wellNeg_abstractAtom x target hn)
  | .snd _, .snd hn => by
      rw [NegNeu.abstractAtom]
      split
      · split
        · rename_i hA hEq; clear hEq; cases hA; exact .var
        · exact .snd (wellNeg_abstractAtom x target hn)
      · exact .snd (wellNeg_abstractAtom x target hn)
termination_by n => NegNeu.size n

theorem wellPos_abstractAtom {Γ : Ctx sig} {P A : Object sig.nBases}
    (x : Var Γ P) (target : RawNeu) :
    ∀ {p : PosNeu Γ A}, WellPos p → WellPos (PosNeu.abstractAtom x target p)
  | .neu _, .neu hpol hn => .neu hpol (wellNeg_abstractAtom x target hn)
  | .inl _, .inl hp => .inl (wellPos_abstractAtom x target hp)
  | .inr _, .inr hp => .inr (wellPos_abstractAtom x target hp)
  | .val _, .val hpol ht => .val hpol (wellInv_abstractAtom x target ht)
termination_by p => PosNeu.size p

theorem wellInv_abstractAtom {Γ : Ctx sig} {P A : Object sig.nBases}
    (x : Var Γ P) (target : RawNeu) :
    ∀ {t : InvTm Γ A}, WellInv t → WellInv (InvTm.abstractAtom x target t)
  | .unit, _ => .unit
  | .pair _ _, .pair ht hu =>
      .pair (wellInv_abstractAtom x target ht) (wellInv_abstractAtom x target hu)
  | .lam _, .lam ht => .lam (wellInv_abstractAtom _ _ ht)
  | .case _ _ _, .case hn ht hu =>
      .case (wellNeg_abstractAtom x target hn)
        (wellInv_abstractAtom _ _ ht) (wellInv_abstractAtom _ _ hu)
  | .abort _, .abort hn => .abort (wellNeg_abstractAtom x target hn)
  | .foc _, .foc hf => .foc (wellFoc_abstractAtom x target hf)
termination_by t => InvTm.size t

theorem wellFoc_abstractAtom {Γ : Ctx sig} {P A : Object sig.nBases}
    (x : Var Γ P) (target : RawNeu) :
    ∀ {f : FocTm Γ A}, WellFoc f → WellFoc (FocTm.abstractAtom x target f)
  | .pos (.done _), .pos hpol hp => .pos hpol (wellPos_abstractAtom x target hp)
  | .neg (.done _), .neg hpol hn => .neg hpol (wellNeg_abstractAtom x target hn)
  | .letPos _ _, .letPos hpol hn ht =>
      .letPos hpol (wellNeg_abstractAtom x target hn)
        (wellInv_abstractAtom _ _ ht)
  | .sat (.mk _ _), .sat ht => .sat (wellInv_abstractAtom x target ht)
termination_by f => FocTm.size f
end

mutual
theorem wellNeg_abstractSum {Γ : Ctx sig} {B A : Object sig.nBases}
    (x : Var Γ B) (target : RawNeu) :
    ∀ {n : NegNeu Γ A}, WellNeg n → WellNeg (NegNeu.abstractSum x target n)
  | .var _, _ => .var
  | .app _ _, .app hf ha =>
      .app (wellNeg_abstractSum x target hf) (wellInv_abstractSumWalk x target ha)
  | .fst _, .fst hn => .fst (wellNeg_abstractSum x target hn)
  | .snd _, .snd hn => .snd (wellNeg_abstractSum x target hn)
termination_by n => NegNeu.size n

theorem wellPos_abstractSumWalk {Γ : Ctx sig} {B A : Object sig.nBases}
    (x : Var Γ B) (target : RawNeu) :
    ∀ {p : PosNeu Γ A}, WellPos p → WellPos (PosNeu.abstractSumWalk x target p)
  | .neu _, .neu hpol hn => .neu hpol (wellNeg_abstractSum x target hn)
  | .inl _, .inl hp => .inl (wellPos_abstractSumWalk x target hp)
  | .inr _, .inr hp => .inr (wellPos_abstractSumWalk x target hp)
  | .val _, .val hpol ht => .val hpol (wellInv_abstractSumWalk x target ht)
termination_by p => PosNeu.size p

theorem wellInv_abstractSumWalk {Γ : Ctx sig} {B A : Object sig.nBases}
    (x : Var Γ B) (target : RawNeu) :
    ∀ {t : InvTm Γ A}, WellInv t → WellInv (InvTm.abstractSumWalk x target t)
  | .unit, _ => .unit
  | .pair _ _, .pair ht hu =>
      .pair (wellInv_abstractSumWalk x target ht)
        (wellInv_abstractSumWalk x target hu)
  | .lam _, .lam ht => .lam (wellInv_abstractSumWalk _ _ ht)
  | .case _ _ _, .case hn ht hu =>
      .case (wellNeg_abstractSum x target hn)
        (wellInv_abstractSumWalk _ _ ht) (wellInv_abstractSumWalk _ _ hu)
  | .abort _, .abort hn => .abort (wellNeg_abstractSum x target hn)
  | .foc _, .foc hf => .foc (wellFoc_abstractSumWalk x target hf)
termination_by t => InvTm.size t

theorem wellFoc_abstractSumWalk {Γ : Ctx sig} {B A : Object sig.nBases}
    (x : Var Γ B) (target : RawNeu) :
    ∀ {f : FocTm Γ A}, WellFoc f → WellFoc (FocTm.abstractSumWalk x target f)
  | .pos (.done _), .pos hpol hp =>
      .pos hpol (wellPos_abstractSumWalk x target hp)
  | .neg (.done _), .neg hpol hn => .neg hpol (wellNeg_abstractSum x target hn)
  | .letPos _ _, .letPos hpol hn ht =>
      .letPos hpol (wellNeg_abstractSum x target hn)
        (wellInv_abstractSumWalk _ _ ht)
  | .sat (.mk _ _), .sat ht => .sat (wellInv_abstractSumWalk x target ht)
termination_by f => FocTm.size f
end

theorem wellNeg_weaken {Γ : Ctx sig} {A B : Object sig.nBases} {n : NegNeu Γ A}
    (h : WellNeg n) : WellNeg (NegNeu.weaken (B := B) n) :=
  wellNeg_rename _ h

/-! ### Admissible schedules -/

/--
An entry is admissible when it observes a positive type, and (for an exact
demand) the neutral it observes is a legal spine. Consistency entries carry a
witness rather than a neutral; `wellNeg_reconstructWitnessWF_ofCell` supplies
legality for those.
-/
inductive WellEntry {hyps : Array (Object sig.nBases)} :
    PairEntry sig hyps → Prop where
  | consistency {P : Object sig.nBases} {w : Witness} :
      objectPolarity P = .pos → WellEntry (.consistency P w)
  | exact {P : Object sig.nBases} {n : NegNeu (Ctx.ofHyps hyps) P} :
      objectPolarity P = .pos → WellNeg n → WellEntry (.exact P n)

/-- Every entry of the schedule is admissible. -/
def WellEntries {hyps : Array (Object sig.nBases)}
    (entries : List (PairEntry sig hyps)) : Prop :=
  ∀ e ∈ entries, WellEntry e

theorem wellEntry_mapRestAbstractAtom {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ)
    (hyps : Array (Object sig.nBases)) (P : Object sig.nBases)
    (hctx : Ctx.ofHyps (hyps.push P) = Ctx.ofHyps hyps ▻ P) (target : RawNeu)
    {e : PairEntry sig hyps} (he : WellEntry e) :
    WellEntry (mapRestAbstractAtom cert hyps P hctx target e) := by
  cases he with
  | exact hpol hn =>
      exact .exact hpol
        (wellNeg_castCtx _ (wellNeg_abstractAtom _ _ (wellNeg_weaken hn)))
  | consistency hpol =>
      rw [mapRestAbstractAtom]
      split
      · split
        · split
          · rename_i hRec hQ
            cases hQ
            exact .exact hpol
              (wellNeg_castCtx _ (wellNeg_abstractAtom _ _ (wellNeg_weaken
                (wellNeg_reconstructWitnessWF_ofCell cert _ hyps _ hRec))))
          · exact .consistency hpol
        · exact .consistency hpol
      · exact .consistency hpol

theorem wellEntry_mapRestAbstractSumInl {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases)
    (hL : Ctx.ofHyps (hyps.push L) = Ctx.ofHyps hyps ▻ L) (target : RawNeu)
    {e : PairEntry sig hyps} (he : WellEntry e) :
    WellEntry (mapRestAbstractSumInl cert hyps L R hL target e) := by
  cases he with
  | exact hpol hn =>
      exact .exact hpol
        (wellNeg_castCtx _ (wellNeg_abstractSum _ _ (wellNeg_weaken hn)))
  | consistency hpol =>
      rw [mapRestAbstractSumInl]
      split
      · split
        · split
          · rename_i hRec hQ
            cases hQ
            exact .exact hpol
              (wellNeg_castCtx _ (wellNeg_abstractSum _ _ (wellNeg_weaken
                (wellNeg_reconstructWitnessWF_ofCell cert _ hyps _ hRec))))
          · exact .consistency hpol
        · exact .consistency hpol
      · exact .consistency hpol

theorem wellEntry_mapRestAbstractSumInr {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ)
    (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases)
    (hR : Ctx.ofHyps (hyps.push R) = Ctx.ofHyps hyps ▻ R) (target : RawNeu)
    {e : PairEntry sig hyps} (he : WellEntry e) :
    WellEntry (mapRestAbstractSumInr cert hyps L R hR target e) := by
  cases he with
  | exact hpol hn =>
      exact .exact hpol
        (wellNeg_castCtx _ (wellNeg_abstractSum _ _ (wellNeg_weaken hn)))
  | consistency hpol =>
      rw [mapRestAbstractSumInr]
      split
      · split
        · split
          · rename_i hRec hQ
            cases hQ
            exact .exact hpol
              (wellNeg_castCtx _ (wellNeg_abstractSum _ _ (wellNeg_weaken
                (wellNeg_reconstructWitnessWF_ofCell cert _ hyps _ hRec))))
          · exact .consistency hpol
        · exact .consistency hpol
      · exact .consistency hpol

theorem wellEntries_map {hyps hyps' : Array (Object sig.nBases)}
    {es : List (PairEntry sig hyps)} (f : PairEntry sig hyps → PairEntry sig hyps')
    (hf : ∀ e, WellEntry e → WellEntry (f e)) (h : WellEntries es) :
    WellEntries (es.map f) := by
  intro e he
  obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
  exact hf e' (h e' he')

/-! ### The collected exact demands are admissible -/

/-- A collected observation: a legal spine at a positive result type. -/
def ExactOk {Γ : Ctx sig}
    (e : (P : Object sig.nBases) × NegNeu Γ P) : Prop :=
  objectPolarity e.1 = .pos ∧ WellNeg e.2

theorem exactOk_insertExact {Γ : Ctx sig}
    {acc : Array ((P : Object sig.nBases) × NegNeu Γ P)}
    {a : (P : Object sig.nBases) × NegNeu Γ P}
    (hacc : ∀ e ∈ acc, ExactOk e) (ha : ExactOk a) :
    ∀ e ∈ insertExact acc a, ExactOk e := by
  intro e he
  rw [insertExact] at he
  split at he
  · exact hacc e he
  · rcases Array.mem_push.1 he with h | h
    · exact hacc e h
    · exact h ▸ ha

theorem exactOk_pushExact {Γ : Ctx sig} {A : Object sig.nBases}
    {acc : Array ((P : Object sig.nBases) × NegNeu Γ P)} {n : NegNeu Γ A}
    (hacc : ∀ e ∈ acc, ExactOk e) (hn : WellNeg n) :
    ∀ e ∈ pushExact acc n, ExactOk e := by
  intro e he
  rw [pushExact] at he
  split at he
  · rename_i hpol
    exact exactOk_insertExact hacc ⟨by simpa using hpol, hn⟩ e he
  · exact hacc e he

mutual
theorem exactOk_exactNegNeu {Γ : Ctx sig} {A : Object sig.nBases} :
    ∀ {n : NegNeu Γ A} {acc : Array ((P : Object sig.nBases) × NegNeu Γ P)},
      WellNeg n → (∀ e ∈ acc, ExactOk e) → ∀ e ∈ exactNegNeu n acc, ExactOk e
  | .var _, _, hn, hacc => by
      rw [exactNegNeu]; exact exactOk_pushExact hacc hn
  | .app _ _, _, .app hf ht, hacc => by
      rw [exactNegNeu]
      exact exactOk_exactInvTm ht
        (exactOk_exactNegNeu hf (exactOk_pushExact hacc (.app hf ht)))
  | .fst _, _, .fst hf, hacc => by
      rw [exactNegNeu]
      exact exactOk_exactNegNeu hf (exactOk_pushExact hacc (.fst hf))
  | .snd _, _, .snd hf, hacc => by
      rw [exactNegNeu]
      exact exactOk_exactNegNeu hf (exactOk_pushExact hacc (.snd hf))
termination_by n => NegNeu.size n

theorem exactOk_exactPosNeu {Γ : Ctx sig} {A : Object sig.nBases} :
    ∀ {p : PosNeu Γ A} {acc : Array ((P : Object sig.nBases) × NegNeu Γ P)},
      WellPos p → (∀ e ∈ acc, ExactOk e) → ∀ e ∈ exactPosNeu p acc, ExactOk e
  | .neu _, _, .neu _ hn, hacc => by
      rw [exactPosNeu]; exact exactOk_exactNegNeu hn hacc
  | .inl _, _, .inl hp, hacc => by
      rw [exactPosNeu]; exact exactOk_exactPosNeu hp hacc
  | .inr _, _, .inr hp, hacc => by
      rw [exactPosNeu]; exact exactOk_exactPosNeu hp hacc
  | .val _, _, .val _ ht, hacc => by
      rw [exactPosNeu]; exact exactOk_exactInvTm ht hacc
termination_by p => PosNeu.size p

theorem exactOk_exactInvTm {Γ : Ctx sig} {A : Object sig.nBases} :
    ∀ {t : InvTm Γ A} {acc : Array ((P : Object sig.nBases) × NegNeu Γ P)},
      WellInv t → (∀ e ∈ acc, ExactOk e) → ∀ e ∈ exactInvTm t acc, ExactOk e
  | .unit, _, _, hacc => by rw [exactInvTm]; exact hacc
  | .pair _ _, _, .pair ht hu, hacc => by
      rw [exactInvTm]
      exact exactOk_exactInvTm hu (exactOk_exactInvTm ht hacc)
  | .lam _, _, _, hacc => by rw [exactInvTm]; exact hacc
  | .case _ _ _, _, .case hn _ _, hacc => by
      rw [exactInvTm]; exact exactOk_exactNegNeu hn hacc
  | .abort _, _, .abort hn, hacc => by
      rw [exactInvTm]; exact exactOk_exactNegNeu hn hacc
  | .foc _, _, .foc hf, hacc => by
      rw [exactInvTm]; exact exactOk_exactFocTm hf hacc
termination_by t => InvTm.size t

theorem exactOk_exactFocTm {Γ : Ctx sig} {A : Object sig.nBases} :
    ∀ {f : FocTm Γ A} {acc : Array ((P : Object sig.nBases) × NegNeu Γ P)},
      WellFoc f → (∀ e ∈ acc, ExactOk e) → ∀ e ∈ exactFocTm f acc, ExactOk e
  | .pos (.done _), _, .pos _ hp, hacc => by
      rw [exactFocTm]; exact exactOk_exactPosNeu hp hacc
  | .neg (.done _), _, .neg _ hn, hacc => by
      rw [exactFocTm]; exact exactOk_exactNegNeu hn hacc
  | .letPos _ _, _, .letPos _ hn _, hacc => by
      rw [exactFocTm]; exact exactOk_exactNegNeu hn hacc
  | .sat (.mk _ _), _, .sat ht, hacc => by
      rw [exactFocTm]; exact exactOk_exactInvTm ht hacc
termination_by f => FocTm.size f
end

theorem exactOk_collectExact {Γ : Ctx sig} {A : Object sig.nBases}
    {t : InvTm Γ A} (ht : WellInv t) : ∀ e ∈ collectExact t, ExactOk e :=
  exactOk_exactInvTm ht (by simp)

/-- Folding admissible observations into an accumulator keeps it admissible. -/
theorem exactOk_foldl_insertExact {Γ : Ctx sig}
    {a : Array ((P : Object sig.nBases) × NegNeu Γ P)}
    {init : Array ((P : Object sig.nBases) × NegNeu Γ P)}
    (ha : ∀ e ∈ a, ExactOk e) (hinit : ∀ e ∈ init, ExactOk e) :
    ∀ e ∈ a.foldl insertExact init, ExactOk e := by
  refine Array.foldl_induction (as := a)
    (motive := fun _ acc => ∀ e ∈ acc, ExactOk e) hinit ?_
  intro i acc hacc
  exact exactOk_insertExact hacc (ha _ (a.getElem_mem i.2))

theorem exactOk_unionExact {Γ : Ctx sig}
    {a b : Array ((P : Object sig.nBases) × NegNeu Γ P)}
    (ha : ∀ e ∈ a, ExactOk e) (hb : ∀ e ∈ b, ExactOk e) :
    ∀ e ∈ unionExact a b, ExactOk e :=
  exactOk_foldl_insertExact hb (exactOk_foldl_insertExact ha (by simp))

theorem exactOk_selectExactObs {hyps : Array (Object sig.nBases)}
    {σ : ReachState sig.nBases}
    {a : Array ((P : Object sig.nBases) × NegNeu (Ctx.ofHyps hyps) P)}
    (ha : ∀ e ∈ a, ExactOk e) :
    ∀ e ∈ selectExactObs σ hyps a, ExactOk e := by
  refine Array.foldl_induction (as := a)
    (motive := fun _ acc => ∀ e ∈ acc, ExactOk e) (by simp) ?_
  intro i acc hacc
  rw [selectExactStep]
  split
  · exact exactOk_insertExact hacc (ha _ (a.getElem_mem i.2))
  · exact hacc

/-! ### The shared schedule is admissible -/

theorem wellEntry_of_mem_mergePairObs {σ : ReachState sig.nBases}
    {hyps : Array (Object sig.nBases)} {consistency : Schedule sig.nBases}
    {exactSrc : Array ((P : Object sig.nBases) × NegNeu (Ctx.ofHyps hyps) P)}
    (hcons : ∀ e ∈ consistency.entries, objectPolarity e.1 = .pos)
    (hexact : ∀ e ∈ exactSrc, ExactOk e) {e : PairEntry sig hyps}
    (h : e ∈ mergePairObs σ hyps consistency exactSrc) : WellEntry e := by
  simp only [mergePairObs] at h
  rcases Array.mem_append.1 (mem_of_mem_canonicalizePairObsOrder h) with hm | hm
  · obtain ⟨a, ha, rfl⟩ := Array.mem_map.1 hm
    exact .exact (hexact a ha).1 (hexact a ha).2
  · revert hm
    refine Array.foldl_induction (as := consistency.entries)
      (motive := fun _ acc => e ∈ acc → WellEntry e) (by simp) ?_
    intro i acc hacc
    split
    · intro hmem
      rcases Array.mem_push.1 hmem with h1 | h1
      · exact hacc h1
      · exact h1 ▸ .consistency (hcons _ (consistency.entries.getElem_mem i.2))
    · exact hacc

/-- Admissibility is stable under reordering, so canonicalization preserves it. -/
theorem wellEntries_canonicalizePairObsOrder {σ : ReachState sig.nBases}
    {hyps : Array (Object sig.nBases)} {entries : Array (PairEntry sig hyps)}
    (h : WellEntries entries.toList) :
    WellEntries (canonicalizePairObsOrder σ entries).toList := fun _ he =>
  h _ (Array.mem_def.1 (mem_of_mem_canonicalizePairObsOrder (Array.mem_def.2 he)))

/-- Extending an admissible schedule with an admissible entry keeps it admissible. -/
theorem wellEntries_append {hyps : Array (Object sig.nBases)}
    {es fs : List (PairEntry sig hyps)} (hes : WellEntries es) (hfs : WellEntries fs) :
    WellEntries (es ++ fs) := fun e he =>
  (List.mem_append.1 he).elim (hes e) (hfs e)

/--
The schedule built for a pair of well-focused terms is admissible: every
observation is a legal spine at a positive type.
-/
theorem wellEntries_pairObs {Γ : ReachCtx sig.nBases} {goal : Object sig.nBases}
    {A : Object sig.nBases} {t u : InvTm (Ctx.ofHyps Γ.hyps) A}
    (ht : WellInv t) (hu : WellInv u)
    {entries : Array (PairEntry sig Γ.hyps)} {c : CertifiedReachResult sig.nBases}
    (h : pairObs Γ goal t u = .ok entries c) : WellEntries entries.toList := by
  rw [pairObs] at h
  split at h
  · exact absurd h (by simp)
  · simp only [PairObsResult.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro e he
    exact wellEntry_of_mem_mergePairObs
      (fun _ hm => objectPolarity_of_mem_buildSchedule hm)
      (exactOk_selectExactObs
        (exactOk_unionExact (exactOk_collectExact ht) (exactOk_collectExact hu)))
      (Array.mem_def.2 he)

/-- Exact demands survive the merge and the ordering unchanged. -/
theorem mem_mergePairObs_of_mem_exact {σ : ReachState sig.nBases}
    {hyps : Array (Object sig.nBases)} {consistency : Schedule sig.nBases}
    {exactSrc : Array ((P : Object sig.nBases) × NegNeu (Ctx.ofHyps hyps) P)}
    {e : (P : Object sig.nBases) × NegNeu (Ctx.ofHyps hyps) P} (he : e ∈ exactSrc) :
    PairEntry.exact e.1 e.2 ∈ mergePairObs σ hyps consistency exactSrc := by
  simp only [mergePairObs]
  exact mem_canonicalizePairObsOrder
    (Array.mem_append.2 (.inl (Array.mem_map.2 ⟨e, he, rfl⟩)))

/--
Completeness of the shared schedule: every exact demand of *either* term that
is eligible for observation is scheduled, up to spine identity. Both sides feed
the same list, so saturation cannot favour one argument over the other.
-/
theorem exact_complete_pairObs {Γ : ReachCtx sig.nBases} {goal A : Object sig.nBases}
    {t u : InvTm (Ctx.ofHyps Γ.hyps) A} {entries : Array (PairEntry sig Γ.hyps)}
    {c : CertifiedReachResult sig.nBases} (h : pairObs Γ goal t u = .ok entries c)
    {e : Exact (Ctx.ofHyps Γ.hyps)}
    (he : MemI (collectExact t) e ∨ MemI (collectExact u) e)
    (hpol : objectPolarity e.1 = .pos) (hvar : e.2.isVar = false) :
    ∃ e', exactIdEq e e' = true ∧ PairEntry.exact e'.1 e'.2 ∈ entries := by
  rw [pairObs] at h
  split at h
  · exact absurd h (by simp)
  · simp only [PairObsResult.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨e', he', hid⟩ := memI_iff.1 (memI_pairSelection t u he hpol hvar)
    exact ⟨e', hid, mem_mergePairObs_of_mem_exact he'⟩

/-! ### Applying an admissible schedule stays well focused -/

/--
Applying one observation, and applying a whole admissible schedule, return a
well-focused term whenever the continuation was one.
-/
theorem wellInv_applySchedule : ∀ fuel : Nat,
    (∀ {σ : ReachState sig.nBases} (cert : ReachRankCert σ)
        (hyps : Array (Object sig.nBases))
        (P : Object sig.nBases) (nP : NegNeu (Ctx.ofHyps hyps) P)
        (rest : List (PairEntry sig hyps)) {A : Object sig.nBases}
        {cont t' : InvTm (Ctx.ofHyps hyps) A},
        objectPolarity P = .pos → WellNeg nP → WellEntries rest → WellInv cont →
        applyObsNeu fuel cert hyps P nP rest cont = .ok t' → WellInv t') ∧
    (∀ {σ : ReachState sig.nBases} (cert : ReachRankCert σ)
        (hyps : Array (Object sig.nBases))
        (entries : List (PairEntry sig hyps)) {A : Object sig.nBases}
        {cont t' : InvTm (Ctx.ofHyps hyps) A},
        WellEntries entries → WellInv cont →
        applyPairObsGo fuel cert hyps entries cont = .ok t' → WellInv t')
  | 0 => by
      constructor <;> intros <;>
        simp_all [applyObsNeu, applyPairObsGo]
  | fuel + 1 => by
      obtain ⟨ihObs, ihGo⟩ := wellInv_applySchedule fuel
      constructor
      · intro σ cert hyps P nP rest A cont t' hpol hnP hrest hcont h
        rw [applyObsNeu] at h
        dsimp only at h
        split at h
        · -- a proof of `never` collapses to `abort`
          cases h
          exact .abort (wellNeg_cast _ hnP)
        · split at h
          · -- coproduct: split on the observation
            rename_i L R _
            have hbody : WellInv (InvTm.abstr (P := .coprod L R) .here
                (NegNeu.weaken nP) (InvTm.weaken cont)) :=
              wellInv_abstr _ _ (wellInv_weaken hcont)
            split at h
            case h_1 =>
              cases h
              refine .case hnP (wellInv_castCtx _ ?_) (wellInv_castCtx _ ?_)
              · exact ihGo _ _ _
                  (wellEntries_map _
                    (fun _ he => wellEntry_mapRestAbstractSumInl _ _ _ _ _ _ he)
                    hrest)
                  (wellInv_castCtx _
                    (wellInv_hsubstInv (wellInv_rename _ hbody)
                      (wellInv_etaInl L R)))
                  (by assumption)
              · exact ihGo _ _ _
                  (wellEntries_map _
                    (fun _ he => wellEntry_mapRestAbstractSumInr _ _ _ _ _ _ he)
                    hrest)
                  (wellInv_castCtx _
                    (wellInv_hsubstInv (wellInv_rename _ hbody)
                      (wellInv_etaInr L R)))
                  (by assumption)
            all_goals exact absurd h (by simp)
          · -- atom: bind the observation with `letPos`
            split at h
            case h_1 =>
              cases h
              refine .foc (.letPos hpol hnP (wellInv_castCtx _ ?_))
              exact ihGo _ _ _
                (wellEntries_map _
                  (fun _ he => wellEntry_mapRestAbstractAtom _ _ _ _ _ he)
                  hrest)
                (wellInv_castCtx _
                  (wellInv_abstr _ _ (wellInv_weaken hcont)))
                (by assumption)
            all_goals exact absurd h (by simp)
      · intro σ cert hyps entries A cont t' hentries hcont h
        rw [applyPairObsGo.eq_def] at h
        dsimp only at h
        split at h
        · cases h; exact hcont
        · rename_i e rest
          have he := hentries e (by simp)
          have hrest : WellEntries rest := fun e' he' => hentries e' (by simp [he'])
          split at h
          · -- consistency: reconstruct the witness, then observe it
            rename_i Q w
            split at h
            · exact absurd h (by simp)
            · split at h
              · exact absurd h (by simp)
              · split at h
                · rename_i hRec hQ
                  cases hQ
                  cases he with
                  | consistency hpol =>
                      exact ihObs _ _ _ _ _ hpol
                        (wellNeg_reconstructWitnessWF_ofCell _ _ _ _ hRec)
                        hrest hcont h
                · exact absurd h (by simp)
          · -- exact demand: observe the recorded neutral
            cases he with
            | exact hpol hn => exact ihObs _ _ _ _ _ hpol hn hrest hcont h

/-- The saturated form of a well-focused term is well focused. -/
theorem wellInv_applyPairObs (fuel : Nat) {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ)
    (hyps : Array (Object sig.nBases)) (entries : Array (PairEntry sig hyps))
    {A : Object sig.nBases} {cont t' : InvTm (Ctx.ofHyps hyps) A}
    (hentries : WellEntries entries.toList) (hcont : WellInv cont)
    (h : applyPairObs fuel cert hyps entries cont = .ok t') : WellInv t' := by
  rw [applyPairObs] at h
  split at h
  · split at h
    · cases h
      exact .abort (wellNeg_neuOfTypeWF _ _ _ (by assumption))
    · exact absurd h (by simp)
  · exact (wellInv_applySchedule fuel).2 _ _ _ hentries hcont h

/--
End to end: the shared schedule built from two well-focused terms saturates a
well-focused continuation to a well-focused term.
-/
theorem wellInv_saturate_pairObs (fuel : Nat) {Γ : ReachCtx sig.nBases}
    {goal A : Object sig.nBases} {t u : InvTm (Ctx.ofHyps Γ.hyps) A}
    {entries : Array (PairEntry sig Γ.hyps)} {c : CertifiedReachResult sig.nBases}
    {B : Object sig.nBases} {cont t' : InvTm (Ctx.ofHyps Γ.hyps) B}
    (ht : WellInv t) (hu : WellInv u) (hobs : pairObs Γ goal t u = .ok entries c)
    (hcont : WellInv cont)
    (h : applyPairObs fuel c.cert Γ.hyps entries cont = .ok t') : WellInv t' :=
  wellInv_applyPairObs fuel c.cert Γ.hyps entries (wellEntries_pairObs ht hu hobs) hcont h

/--
An inconsistent context collapses to the canonical absurd branch: saturation
either finds the discovered proof of `0` and aborts on it, or reports the
invariant failure that a missing reconstruction is.
-/
theorem applyPairObs_absurd_of_inconsistent (fuel : Nat)
    {σ : ReachState sig.nBases} (cert : ReachRankCert σ)
    (hyps : Array (Object sig.nBases))
    (entries : Array (PairEntry sig hyps)) {A : Object sig.nBases}
    (cont : InvTm (Ctx.ofHyps hyps) A) (hinc : σ.inconsistent = true) :
    (∃ n : NegNeu (Ctx.ofHyps hyps) .never,
        applyPairObs fuel cert hyps entries cont = .ok (.abort n)) ∨
      applyPairObs fuel cert hyps entries cont = .invariantFailure := by
  rw [applyPairObs, if_pos hinc]
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inr rfl

end Equality
end Gimbal
