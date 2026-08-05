/-
  The shared schedule does not depend on which side an input was passed.

  `pairObs` feeds both terms into one canonical union of exact demands, so the
  schedule it produces for `(t, u)` and for `(u, t)` must observe the same
  things. Order is not preserved on the nose — the union is built by insertion
  and the two insertion orders differ — but observation identity is exactly the
  granularity saturation consumes, so that is the level the symmetry is stated
  at: the two schedules have the same entries up to `PairEntry.idEq`.
-/

import Gimbal.Equality.ExactObs

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- Some entry of the schedule has the identity of `x`. -/
def MemIdEq {hyps : Array (Object sig.nBases)} (es : Array (PairEntry sig hyps))
    (x : PairEntry sig hyps) : Prop :=
  ∃ y ∈ es, PairEntry.idEq x y = true

/-! ### Selection sees the same demands from equivalent collections -/

theorem memI_selectExactObs_iff {hyps : Array (Object sig.nBases)}
    {σ : ReachState sig.nBases} {ex : Array (Exact (Ctx.ofHyps hyps))}
    {e : Exact (Ctx.ofHyps hyps)} :
    MemI (selectExactObs σ hyps ex) e ↔
      ∃ x ∈ ex, (objectPolarity x.1 == .pos && !x.2.isVar) = true ∧
        exactIdEq e x = true := by
  unfold selectExactObs
  rw [← Array.foldl_toList, memI_foldl_select]
  constructor
  · rintro (h | ⟨x, hx, hk, hex⟩)
    · exact absurd h (by simp [MemI])
    · exact ⟨x, Array.mem_toList_iff.mp hx, hk, hex⟩
  · rintro ⟨x, hx, hk, hex⟩
    exact Or.inr ⟨x, Array.mem_toList_iff.mpr hx, hk, hex⟩

/-- Collections with the same observations select the same observations. -/
theorem memI_selectExactObs_congr {hyps : Array (Object sig.nBases)}
    {σ : ReachState sig.nBases} {a b : Array (Exact (Ctx.ofHyps hyps))}
    (hab : ∀ e, MemI a e → MemI b e) {e : Exact (Ctx.ofHyps hyps)}
    (h : MemI (selectExactObs σ hyps a) e) : MemI (selectExactObs σ hyps b) e := by
  obtain ⟨x, hx, hk, hex⟩ := memI_selectExactObs_iff.1 h
  obtain ⟨y, hy, hxy⟩ := memI_iff.1 (hab x (memI_of_mem hx))
  obtain ⟨h1, h2⟩ := (exactIdEq_iff x y).1 hxy
  refine memI_selectExactObs_iff.2 ⟨y, hy, ?_, exactIdEq_trans hex hxy⟩
  simpa [← h1, ← isVar_congr h2] using hk

/-! ### The consistency half is literally the same array -/

/-- Equivalent collections observe the same result types. -/
theorem exactTys_congr {hyps : Array (Object sig.nBases)}
    {a b : Array (Exact (Ctx.ofHyps hyps))} (hab : ∀ e, MemI a e ↔ MemI b e) :
    exactTys a = exactTys b := by
  have key : ∀ (c d : Array (Exact (Ctx.ofHyps hyps))),
      (∀ e, MemI c e → MemI d e) → ∀ A, exactTys c A = true → exactTys d A = true := by
    intro c d hcd A hA
    obtain ⟨i, hi, hty⟩ := Array.any_eq_true.1 hA
    obtain ⟨y, hy, hxy⟩ := memI_iff.1 (hcd _ (memI_of_mem (c.getElem_mem hi)))
    refine Array.any_eq_true.2 ?_
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hy
    exact ⟨j, hj, by simpa [← (exactIdEq_iff _ _).1 hxy |>.1] using hty⟩
  funext A
  cases hA : exactTys a A with
  | true => exact (key a b (fun e => (hab e).1) A hA).symm ▸ rfl
  | false =>
      cases hB : exactTys b A with
      | true => exact absurd (key b a (fun e => (hab e).2) A hB) (by simp [hA])
      | false => rfl

/-! ### Symmetry of the merged schedule -/

theorem memIdEq_canonicalizePairObsOrder {hyps : Array (Object sig.nBases)}
    {σ : ReachState sig.nBases} {es : Array (PairEntry sig hyps)}
    {x : PairEntry sig hyps} :
    MemIdEq (canonicalizePairObsOrder σ es) x ↔ MemIdEq es x := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, mem_of_mem_canonicalizePairObsOrder hy, hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, mem_canonicalizePairObsOrder hy, hxy⟩

/--
Two collections with the same exact observations produce the same schedule, up
to observation identity.
-/
theorem memIdEq_mergePairObs_congr {hyps : Array (Object sig.nBases)}
    {σ : ReachState sig.nBases} {consistency : Schedule sig.nBases}
    {a b : Array (Exact (Ctx.ofHyps hyps))} (hab : ∀ e, MemI a e ↔ MemI b e)
    (x : PairEntry sig hyps) :
    MemIdEq (mergePairObs σ hyps consistency a) x ↔
      MemIdEq (mergePairObs σ hyps consistency b) x := by
  have hcons : consistencyBag (hyps := hyps) (exactTys a) consistency =
      consistencyBag (exactTys b) consistency := by
    rw [exactTys_congr hab]
  have hexact : ∀ (c d : Array (Exact (Ctx.ofHyps hyps))),
      (∀ e, MemI c e → MemI d e) →
      MemIdEq (c.map fun e => .exact e.1 e.2) x →
        MemIdEq ((d.map fun e => .exact e.1 e.2) : Array (PairEntry sig hyps)) x := by
    rintro c d hcd ⟨y, hy, hxy⟩
    obtain ⟨e, he, rfl⟩ := Array.mem_map.1 hy
    match x, hxy with
    | .exact P n, hxy =>
        obtain ⟨z, hz, hez⟩ := memI_iff.1 (hcd e (memI_of_mem he))
        exact ⟨.exact z.1 z.2, Array.mem_map.2 ⟨z, hz, rfl⟩,
          exactIdEq_trans (e := ⟨P, n⟩) hxy hez⟩
  simp only [mergePairObs, memIdEq_canonicalizePairObsOrder, hcons]
  constructor <;> rintro ⟨y, hy, hxy⟩ <;>
    rcases Array.mem_append.1 hy with h | h
  · exact (hexact a b (fun e => (hab e).1) ⟨y, h, hxy⟩).elim
      fun z hz => ⟨z, Array.mem_append.2 (.inl hz.1), hz.2⟩
  · exact ⟨y, Array.mem_append.2 (.inr h), hxy⟩
  · exact (hexact b a (fun e => (hab e).2) ⟨y, h, hxy⟩).elim
      fun z hz => ⟨z, Array.mem_append.2 (.inl hz.1), hz.2⟩
  · exact ⟨y, Array.mem_append.2 (.inr h), hxy⟩

/--
Swapping the two inputs produces the same shared schedule, up to observation
identity. Both calls must succeed; the old-only check is a property of the
demands, not of the order they were collected in.
-/
theorem pairObs_symm {Γ : ReachCtx sig.nBases} {goal A : Object sig.nBases}
    {t u : InvTm (Ctx.ofHyps Γ.hyps) A}
    {e₁ e₂ : Array (PairEntry sig Γ.hyps)}
    {c₁ c₂ : CertifiedReachResult sig.nBases}
    (h₁ : pairObs Γ goal t u = .ok e₁ c₁) (h₂ : pairObs Γ goal u t = .ok e₂ c₂)
    (x : PairEntry sig Γ.hyps) : MemIdEq e₁ x ↔ MemIdEq e₂ x := by
  rw [pairObs] at h₁ h₂
  split at h₁
  · exact absurd h₁ (by simp)
  · split at h₂
    · exact absurd h₂ (by simp)
    · simp only [PairObsResult.ok.injEq] at h₁ h₂
      obtain ⟨rfl, -⟩ := h₁
      obtain ⟨rfl, -⟩ := h₂
      exact memIdEq_mergePairObs_congr
        (fun e => ⟨fun h => memI_selectExactObs_congr
            (fun _ hx => (unionExact_comm _ _ _).1 hx) h,
          fun h => memI_selectExactObs_congr
            (fun _ hx => (unionExact_comm _ _ _).1 hx) h⟩) x

end Equality
end Gimbal
