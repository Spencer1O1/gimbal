/-
  Soundness of the reachability worklist against the declarative judgments
  (Milestone 8D).

  Every fact the finite closure records is backed by a derivation:

  * an old-only witness gives an `OldDeduction` (no hypothesis from `Γnew`);
  * a uses-new witness gives a `UsesNew` derivation;
  * `retrievable` means the type really is bound in the context;
  * the inconsistency flag means `0` itself is derivable, and conversely the
    flag is raised as soon as `0` becomes deducible.
-/

import Gimbal.Equality.Deduction

namespace Gimbal
namespace Equality

variable {n : Nat}

/-! ### Table lookup -/

theorem ReachState.typeAt_of_findTypeIdx {σ : ReachState n} {A : Object n} {i : Nat}
    (h : σ.findTypeIdx A = some i) : σ.typeAt i = some A :=
  getElem?_of_findIdx? h

theorem ReachState.typeAt_inj {σ : ReachState n} {i : Nat} {A B : Object n}
    (hA : σ.typeAt i = some A) (hB : σ.typeAt i = some B) : A = B := by
  rw [hA] at hB; exact Option.some.inj hB

/-! ### Cell record equations -/

@[simp] theorem ReachCell.record_retrievable (c : ReachCell) (b : Bool) (w : Witness) :
    (c.record b w).retrievable = c.retrievable := by
  unfold ReachCell.record; split <;> split <;> rfl

theorem ReachCell.record_old_of_new (c : ReachCell) (w : Witness) :
    (c.record true w).oldWitness = c.oldWitness := by
  unfold ReachCell.record; simp; split <;> rfl

theorem ReachCell.record_new_of_old (c : ReachCell) (w : Witness) :
    (c.record false w).newWitness = c.newWitness := by
  unfold ReachCell.record; simp; split <;> rfl

/-- Recording always leaves at least one provenance slot inhabited. -/
theorem ReachCell.record_witnessed (c : ReachCell) (b : Bool) (w : Witness) :
    (c.record b w).oldWitness.isSome = true ∨ (c.record b w).newWitness.isSome = true := by
  unfold ReachCell.record
  split
  · split
    · rename_i h; exact Or.inr (by simp [h])
    · exact Or.inr (by simp)
  · split
    · rename_i h; exact Or.inl (by simp [h])
    · exact Or.inl (by simp)

@[simp] theorem ReachCell.recordHyp_retrievable (c : ReachCell) (b : Bool) (w : Witness) :
    (c.recordHyp b w).retrievable = true := rfl

@[simp] theorem ReachCell.recordHyp_old (c : ReachCell) (b : Bool) (w : Witness) :
    (c.recordHyp b w).oldWitness = (c.record b w).oldWitness := rfl

@[simp] theorem ReachCell.recordHyp_new (c : ReachCell) (b : Bool) (w : Witness) :
    (c.recordHyp b w).newWitness = (c.record b w).newWitness := rfl

/-! ### Where a discovery lands -/

@[simp] theorem ReachState.getCell_markInconsistentIf (σ : ReachState n)
    (A : Object n) (j : Nat) : (σ.markInconsistentIf A).getCell j = σ.getCell j := by
  unfold ReachState.markInconsistentIf; split <;> rfl

@[simp] theorem ReachState.types_markInconsistentIf (σ : ReachState n) (A : Object n) :
    (σ.markInconsistentIf A).types = σ.types := by
  unfold ReachState.markInconsistentIf; split <;> rfl

theorem ReachState.inconsistent_markInconsistentIf {σ : ReachState n} {A : Object n}
    (h : (σ.markInconsistentIf A).inconsistent = true) :
    σ.inconsistent = true ∨ A = (.never : Object n) := by
  unfold ReachState.markInconsistentIf at h
  split at h
  · rename_i he; exact Or.inr (by simpa using he)
  · exact Or.inl h

theorem ReachState.typeAt_discover (σ : ReachState n) (i : Nat) (b : Bool)
    (w : Witness) (j : Nat) : (σ.discover i b w).typeAt j = σ.typeAt j := by
  simp [ReachState.typeAt, ← (σ.le_discover i b w).types]

theorem ReachState.getCell_discover (σ : ReachState n) (i : Nat) (b : Bool)
    (w : Witness) (j : Nat) :
    (σ.discover i b w).getCell j = σ.getCell j ∨
      (j = i ∧ (σ.discover i b w).getCell j = (σ.getCell i).record b w) := by
  unfold ReachState.discover
  split
  · exact Or.inl rfl
  · rw [ReachState.getCell_markInconsistentIf]
    by_cases hj : i = j
    · subst hj
      by_cases hlt : i < σ.cells.size
      · exact Or.inr ⟨rfl, ReachState.getCell_setCell_self hlt⟩
      · exact Or.inl (by simp [ReachState.setCell, dif_neg hlt])
    · exact Or.inl (ReachState.getCell_setCell_ne hj)

theorem ReachState.inconsistent_discover {σ : ReachState n} {i : Nat} {b : Bool}
    {w : Witness} (h : (σ.discover i b w).inconsistent = true) :
    σ.inconsistent = true ∨ σ.typeAt i = some (.never : Object n) := by
  unfold ReachState.discover at h
  split at h
  · exact Or.inl h
  · rename_i A hA
    rcases ReachState.inconsistent_markInconsistentIf h with h' | rfl
    · exact Or.inl (by simpa using h')
    · exact Or.inr hA

theorem ReachState.discover_inconsistent_of_never (σ : ReachState n) (i : Nat)
    (b : Bool) (w : Witness) (h : σ.typeAt i = some (.never : Object n)) :
    (σ.discover i b w).inconsistent = true := by
  unfold ReachState.discover
  rw [h]
  simp [ReachState.markInconsistentIf]

theorem ReachState.typeAt_markHyp (σ : ReachState n) (Γ : ReachCtx n) (k j : Nat) :
    (σ.markHyp Γ k).typeAt j = σ.typeAt j := by
  simp [ReachState.typeAt, ← (σ.le_markHyp Γ k).types]

theorem ReachState.getCell_markHyp (σ : ReachState n) (Γ : ReachCtx n) (k j : Nat) :
    (σ.markHyp Γ k).getCell j = σ.getCell j ∨
      (∃ A i, Γ.hyps[k]? = some A ∧ σ.findTypeIdx A = some i ∧ j = i ∧
        (σ.markHyp Γ k).getCell j =
          (σ.getCell i).recordHyp (Γ.isNew k) (.ctxVar k)) := by
  unfold ReachState.markHyp
  split
  · exact Or.inl rfl
  · rename_i A hA
    split
    · exact Or.inl rfl
    · rename_i i hi
      rw [ReachState.getCell_markInconsistentIf]
      by_cases hj : i = j
      · subst hj
        by_cases hlt : i < σ.cells.size
        · exact Or.inr ⟨A, i, hA, hi, rfl, ReachState.getCell_setCell_self hlt⟩
        · exact Or.inl (by simp [ReachState.setCell, dif_neg hlt])
      · exact Or.inl (ReachState.getCell_setCell_ne hj)

theorem ReachState.inconsistent_markHyp {σ : ReachState n} {Γ : ReachCtx n} {k : Nat}
    (h : (σ.markHyp Γ k).inconsistent = true) :
    σ.inconsistent = true ∨ Γ.hyps[k]? = some (.never : Object n) := by
  unfold ReachState.markHyp at h
  split at h
  · exact Or.inl h
  · rename_i A hA
    split at h
    · exact Or.inl h
    · rcases ReachState.inconsistent_markInconsistentIf h with h' | rfl
      · exact Or.inl (by simpa using h')
      · exact Or.inr hA

theorem ReachState.markHyp_inconsistent_of_never (σ : ReachState n) (Γ : ReachCtx n)
    (k i : Nat) (hA : Γ.hyps[k]? = some (.never : Object n))
    (hi : σ.findTypeIdx (.never : Object n) = some i) :
    (σ.markHyp Γ k).inconsistent = true := by
  unfold ReachState.markHyp
  rw [hA]
  simp only []
  rw [hi]
  simp [ReachState.markInconsistentIf]

/-! ### The soundness invariant -/

/-- Every recorded fact is backed by a derivation of the right provenance. -/
structure ReachSound (Γ : ReachCtx n) (σ : ReachState n) : Prop where
  old : ∀ i A, σ.typeAt i = some A → (σ.getCell i).oldWitness.isSome = true →
    OldDeduction Γ A
  new : ∀ i A, σ.typeAt i = some A → (σ.getCell i).newWitness.isSome = true →
    UsesNew Γ A
  bound : ∀ i A, σ.typeAt i = some A → (σ.getCell i).retrievable = true →
    ∃ j : Nat, Γ.hyps[j]? = some A
  witnessed : ∀ i, (σ.getCell i).retrievable = true →
    (σ.getCell i).oldWitness.isSome = true ∨ (σ.getCell i).newWitness.isSome = true
  neverFlagged : ∀ i, σ.typeAt i = some (.never : Object n) →
    (σ.getCell i).simplyDeducible = true → σ.inconsistent = true
  inconsistent : σ.inconsistent = true → SimpleDeduction Γ (.never : Object n)

namespace ReachSound

variable {Γ : ReachCtx n} {σ : ReachState n}

/-- Anything simply deducible in the table is derivable. -/
theorem deducible (h : ReachSound Γ σ) (i : Nat) (A : Object n)
    (hA : σ.typeAt i = some A) (hd : (σ.getCell i).simplyDeducible = true) :
    SimpleDeduction Γ A := by
  unfold ReachCell.simplyDeducible at hd
  rcases Bool.or_eq_true_iff.mp hd with hd | hd
  · rcases Bool.or_eq_true_iff.mp hd with hr | ho
    · rcases h.witnessed i hr with ho | hn
      · exact (h.old i A hA ho).toSimple
      · exact (h.new i A hA hn).toSimple
    · exact (h.old i A hA ho).toSimple
  · exact (h.new i A hA hd).toSimple

/-- Deducible without any uses-new witness means deducible from `Γold` alone. -/
theorem oldOf (h : ReachSound Γ σ) (i : Nat) (A : Object n)
    (hA : σ.typeAt i = some A) (hd : (σ.getCell i).simplyDeducible = true)
    (hn : (σ.getCell i).usesNew = false) : OldDeduction Γ A := by
  have hnew : (σ.getCell i).newWitness.isSome = false := hn
  unfold ReachCell.simplyDeducible at hd
  rcases Bool.or_eq_true_iff.mp hd with hd | hd
  · rcases Bool.or_eq_true_iff.mp hd with hr | ho
    · rcases h.witnessed i hr with ho | hn'
      · exact h.old i A hA ho
      · rw [hnew] at hn'; exact absurd hn' (by simp)
    · exact h.old i A hA ho
  · rw [hnew] at hd; exact absurd hd (by simp)

end ReachSound

/-! ### Preservation by a single discovery -/

theorem ReachSound.discoverAt {Γ : ReachCtx n} {σ : ReachState n}
    (h : ReachSound Γ σ) {i : Nat} {b : Bool} {w : Witness} {A : Object n}
    (hA : σ.typeAt i = some A)
    (hold : b = false → OldDeduction Γ A) (hnew : b = true → UsesNew Γ A) :
    ReachSound Γ (σ.discover i b w) := by
  have hle := σ.le_discover i b w
  have hAsimple : SimpleDeduction Γ A := by
    cases hb : b
    · exact (hold hb).toSimple
    · exact (hnew hb).toSimple
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j B hB hsome
    rw [ReachState.typeAt_discover] at hB
    rcases ReachState.getCell_discover σ i b w j with heq | ⟨rfl, heq⟩
    · exact h.old j B hB (by rwa [heq] at hsome)
    · have hAB : A = B := ReachState.typeAt_inj hA hB
      subst hAB
      rw [heq] at hsome
      cases hb : b
      · exact hold hb
      · rw [hb, ReachCell.record_old_of_new] at hsome
        exact h.old j A hA hsome
  · intro j B hB hsome
    rw [ReachState.typeAt_discover] at hB
    rcases ReachState.getCell_discover σ i b w j with heq | ⟨rfl, heq⟩
    · exact h.new j B hB (by rwa [heq] at hsome)
    · have hAB : A = B := ReachState.typeAt_inj hA hB
      subst hAB
      rw [heq] at hsome
      cases hb : b
      · rw [hb, ReachCell.record_new_of_old] at hsome
        exact h.new j A hA hsome
      · exact hnew hb
  · intro j B hB hr
    rw [ReachState.typeAt_discover] at hB
    rcases ReachState.getCell_discover σ i b w j with heq | ⟨rfl, heq⟩
    · exact h.bound j B hB (by rwa [heq] at hr)
    · rw [heq, ReachCell.record_retrievable] at hr
      exact h.bound j B hB hr
  · intro j hr
    rcases ReachState.getCell_discover σ i b w j with heq | ⟨rfl, heq⟩
    · rw [heq]; exact h.witnessed j (by rwa [heq] at hr)
    · rw [heq]; exact ReachCell.record_witnessed _ _ _
  · intro j hB hd
    rw [ReachState.typeAt_discover] at hB
    rcases ReachState.getCell_discover σ i b w j with heq | ⟨rfl, heq⟩
    · exact hle.inconsistent (h.neverFlagged j hB (by rwa [heq] at hd))
    · exact ReachState.discover_inconsistent_of_never σ j b w hB
  · intro hinc
    rcases ReachState.inconsistent_discover hinc with hinc | hnever
    · exact h.inconsistent hinc
    · have : A = (.never : Object n) := ReachState.typeAt_inj hA hnever
      exact this ▸ hAsimple

theorem ReachSound.markHypAt {Γ : ReachCtx n} {σ : ReachState n}
    (h : ReachSound Γ σ) (k : Nat)
    (hpos : ∀ A, Γ.hyps[k]? = some A → objectPolarity A = .pos) :
    ReachSound Γ (σ.markHyp Γ k) := by
  have hle := σ.le_markHyp Γ k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j B hB hsome
    rw [ReachState.typeAt_markHyp] at hB
    rcases ReachState.getCell_markHyp σ Γ k j with heq | ⟨A, i, hA, hi, rfl, heq⟩
    · exact h.old j B hB (by rwa [heq] at hsome)
    · have hAB : A = B := ReachState.typeAt_inj (ReachState.typeAt_of_findTypeIdx hi) hB
      subst hAB
      rw [heq, ReachCell.recordHyp_old] at hsome
      cases hb : Γ.isNew k
      · exact .hyp k hA (hpos A hA) hb trivial
      · rw [hb, ReachCell.record_old_of_new] at hsome
        exact h.old _ A (ReachState.typeAt_of_findTypeIdx hi) hsome
  · intro j B hB hsome
    rw [ReachState.typeAt_markHyp] at hB
    rcases ReachState.getCell_markHyp σ Γ k j with heq | ⟨A, i, hA, hi, rfl, heq⟩
    · exact h.new j B hB (by rwa [heq] at hsome)
    · have hAB : A = B := ReachState.typeAt_inj (ReachState.typeAt_of_findTypeIdx hi) hB
      subst hAB
      rw [heq, ReachCell.recordHyp_new] at hsome
      cases hb : Γ.isNew k
      · rw [hb, ReachCell.record_new_of_old] at hsome
        exact h.new _ A (ReachState.typeAt_of_findTypeIdx hi) hsome
      · exact .hyp k hA (hpos A hA) hb
  · intro j B hB hr
    rw [ReachState.typeAt_markHyp] at hB
    rcases ReachState.getCell_markHyp σ Γ k j with heq | ⟨A, i, hA, hi, rfl, heq⟩
    · exact h.bound j B hB (by rwa [heq] at hr)
    · have hAB : A = B := ReachState.typeAt_inj (ReachState.typeAt_of_findTypeIdx hi) hB
      exact ⟨k, hAB ▸ hA⟩
  · intro j hr
    rcases ReachState.getCell_markHyp σ Γ k j with heq | ⟨A, i, hA, hi, rfl, heq⟩
    · rw [heq]; exact h.witnessed j (by rwa [heq] at hr)
    · rw [heq, ReachCell.recordHyp_old, ReachCell.recordHyp_new]
      exact ReachCell.record_witnessed _ _ _
  · intro j hB hd
    rcases ReachState.getCell_markHyp σ Γ k j with heq | ⟨A, i, hA, hi, rfl, heq⟩
    · rw [ReachState.typeAt_markHyp] at hB
      exact hle.inconsistent (h.neverFlagged j hB (by rwa [heq] at hd))
    · rw [ReachState.typeAt_markHyp] at hB
      have hAB : A = (.never : Object n) :=
        ReachState.typeAt_inj (ReachState.typeAt_of_findTypeIdx hi) hB
      subst hAB
      exact ReachState.markHyp_inconsistent_of_never σ Γ k _ hA hi
  · intro hinc
    rcases ReachState.inconsistent_markHyp hinc with hinc | hnever
    · exact h.inconsistent hinc
    · exact .hyp k hnever rfl trivial trivial

/-! ### Preservation by each forward-chaining rule -/

theorem ReachState.typeAt_of_le {σ τ : ReachState n} (h : ReachState.Le σ τ) (j : Nat) :
    τ.typeAt j = σ.typeAt j := by
  simp [ReachState.typeAt, h.types]

variable {Γ : ReachCtx n} {σ : ReachState n}

theorem seedHypRule_sound (h : ReachSound Γ σ) (k : Nat) :
    ReachSound Γ (seedHypRule Γ σ k) := by
  unfold seedHypRule
  split
  · rename_i A hA
    split
    · rename_i hp
      refine h.markHypAt k ?_
      intro B hB
      rw [hA] at hB
      cases Option.some.inj hB
      simpa using hp
    · exact h
  · exact h

theorem unitEtaRule_sound (h : ReachSound Γ σ) : ReachSound Γ (unitEtaRule σ) := by
  unfold unitEtaRule
  split
  · rename_i uIdx hu
    exact h.discoverAt (ReachState.typeAt_of_findTypeIdx hu)
      (fun _ => .unit trivial) (fun hb => by simp at hb)
  · exact h

theorem hypProdRule_sound (h : ReachSound Γ σ) (k : Nat) (L R : Object n)
    (hk : Γ.hyps[k]? = some (.prod L R)) :
    ReachSound Γ (hypProdRule Γ σ k L R) := by
  unfold hypProdRule
  cases hp : σ.findTypeIdx (.prod L R) with
  | none => simpa [hp] using h
  | some pIdx =>
    cases hl : σ.findTypeIdx L with
    | none => simpa [hp, hl] using h
    | some lIdx =>
      cases hr : σ.findTypeIdx R with
      | none => simpa [hp, hl, hr] using h
      | some rIdx =>
        dsimp only
        have h1 := h.discoverAt (b := Γ.isNew k) (w := .fst pIdx)
          (ReachState.typeAt_of_findTypeIdx hl)
          (fun hb => .fstHyp k hk hb trivial) (fun hb => .fstHyp k hk hb)
        refine h1.discoverAt (w := .snd pIdx) ?_
          (fun hb => .sndHyp k hk hb trivial) (fun hb => .sndHyp k hk hb)
        rw [ReachState.typeAt_discover]
        exact ReachState.typeAt_of_findTypeIdx hr

theorem hypAppRule_sound (h : ReachSound Γ σ) (k : Nat) (Arg Ret : Object n)
    (hk : Γ.hyps[k]? = some (.exp Arg Ret)) :
    ReachSound Γ (hypAppRule Γ σ k Arg Ret) := by
  unfold hypAppRule
  cases ha : σ.findTypeIdx Arg with
  | none => simpa [ha] using h
  | some aIdx =>
    cases hr : σ.findTypeIdx Ret with
    | none => simpa [ha, hr] using h
    | some rIdx =>
      dsimp only
      split
      · rename_i hdec
        have hA : σ.typeAt aIdx = some Arg := ReachState.typeAt_of_findTypeIdx ha
        have hR : σ.typeAt rIdx = some Ret := ReachState.typeAt_of_findTypeIdx hr
        refine h.discoverAt hR ?_ ?_
        · intro hb
          obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp hb
          exact .appHyp k hk h2 (h.oldOf aIdx Arg hA hdec h1) trivial
        · intro hb
          cases hu : (σ.getCell aIdx).usesNew
          · rw [hu] at hb
            exact .appHypFn k hk (by simpa using hb) (h.deducible aIdx Arg hA hdec)
          · exact .appHypArg k hk (h.new aIdx Arg hA hu)
      · exact h

theorem hypRule_sound (h : ReachSound Γ σ) (k : Nat) :
    ReachSound Γ (hypRule Γ σ k) := by
  unfold hypRule
  split
  · next L R hk => exact hypProdRule_sound h k L R hk
  · next Arg Ret hk => exact hypAppRule_sound h k Arg Ret hk
  · exact h

theorem prodTypeRule_sound (h : ReachSound Γ σ) (ti : Nat) (L R : Object n)
    (hti : σ.typeAt ti = some (.prod L R)) :
    ReachSound Γ (prodTypeRule σ ti L R) := by
  unfold prodTypeRule
  split
  · rename_i hdec
    cases hl : σ.findTypeIdx L with
    | none => simpa [hl] using h
    | some lIdx =>
      cases hr : σ.findTypeIdx R with
      | none => simpa [hl, hr] using h
      | some rIdx =>
        dsimp only
        have hOld : (σ.getCell ti).usesNew = false → OldDeduction Γ (.prod L R) :=
          fun hb => h.oldOf ti _ hti hdec hb
        have hNew : (σ.getCell ti).usesNew = true → UsesNew Γ (.prod L R) :=
          fun hb => h.new ti _ hti hb
        have h1 := h.discoverAt (b := (σ.getCell ti).usesNew) (w := .fst ti)
          (ReachState.typeAt_of_findTypeIdx hl)
          (fun hb => .fst (hOld hb) trivial) (fun hb => .fst (hNew hb))
        refine h1.discoverAt (w := .snd ti) ?_
          (fun hb => .snd (hOld hb) trivial) (fun hb => .snd (hNew hb))
        rw [ReachState.typeAt_discover]
        exact ReachState.typeAt_of_findTypeIdx hr
  · cases hl : σ.findTypeIdx L with
    | none => simpa [hl] using h
    | some lIdx =>
      cases hr : σ.findTypeIdx R with
      | none => simpa [hl, hr] using h
      | some rIdx =>
        dsimp only
        split
        · rename_i hboth
          obtain ⟨hlc, hrc⟩ := Bool.and_eq_true_iff.mp hboth
          have hL : σ.typeAt lIdx = some L := ReachState.typeAt_of_findTypeIdx hl
          have hR : σ.typeAt rIdx = some R := ReachState.typeAt_of_findTypeIdx hr
          refine h.discoverAt hti ?_ ?_
          · intro hb
            obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp hb
            exact .pair (h.oldOf lIdx L hL hlc h1) (h.oldOf rIdx R hR hrc h2) trivial
          · intro hb
            cases hu : (σ.getCell lIdx).usesNew
            · rw [hu] at hb
              exact .pairR (h.deducible lIdx L hL hlc)
                (h.new rIdx R hR (by simpa [ReachCell.usesNew] using hb))
            · exact .pairL (h.new lIdx L hL hu) (h.deducible rIdx R hR hrc)
        · exact h

theorem expEtaRule_sound (h : ReachSound Γ σ) (ti : Nat) (Arg Ret : Object n)
    (hti : σ.typeAt ti = some (.exp Arg Ret)) :
    ReachSound Γ (expEtaRule σ ti Ret) := by
  unfold expEtaRule
  split
  · cases hr : σ.findTypeIdx Ret with
    | none => simpa [hr] using h
    | some rIdx =>
      dsimp only
      split
      · rename_i hdec
        have hR : σ.typeAt rIdx = some Ret := ReachState.typeAt_of_findTypeIdx hr
        exact h.discoverAt hti
          (fun hb => .expEta (h.oldOf rIdx Ret hR hdec hb) trivial)
          (fun hb => .expEta (h.new rIdx Ret hR hb))
      · exact h
  · exact h

theorem expAppRule_sound (h : ReachSound Γ σ) (ti : Nat) (Arg Ret : Object n)
    (hti : σ.typeAt ti = some (.exp Arg Ret)) :
    ReachSound Γ (expAppRule σ ti Arg Ret) := by
  unfold expAppRule
  split
  · rename_i hfdec
    cases ha : σ.findTypeIdx Arg with
    | none => simpa [ha] using h
    | some aIdx =>
      cases hr : σ.findTypeIdx Ret with
      | none => simpa [ha, hr] using h
      | some rIdx =>
        dsimp only
        split
        · rename_i hadec
          have hA : σ.typeAt aIdx = some Arg := ReachState.typeAt_of_findTypeIdx ha
          have hR : σ.typeAt rIdx = some Ret := ReachState.typeAt_of_findTypeIdx hr
          refine h.discoverAt hR ?_ ?_
          · intro hb
            obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp hb
            exact .appTy (h.oldOf ti _ hti hfdec h1) (h.oldOf aIdx Arg hA hadec h2)
              trivial
          · intro hb
            cases hu : (σ.getCell ti).usesNew
            · rw [hu] at hb
              exact .appTyArg (h.deducible ti _ hti hfdec)
                (h.new aIdx Arg hA (by simpa [ReachCell.usesNew] using hb))
            · exact .appTyFn (h.new ti _ hti hu) (h.deducible aIdx Arg hA hadec)
        · exact h
  · exact h

theorem coprodTypeRule_sound (h : ReachSound Γ σ) (ti : Nat) (L R : Object n)
    (hti : σ.typeAt ti = some (.coprod L R)) :
    ReachSound Γ (coprodTypeRule σ ti L R) := by
  unfold coprodTypeRule
  split
  · cases hl : σ.findTypeIdx L with
    | none => simpa [hl] using h
    | some lIdx =>
      cases hr : σ.findTypeIdx R with
      | none => simpa [hl, hr] using h
      | some rIdx =>
        dsimp only
        split
        · rename_i hlc
          have hL : σ.typeAt lIdx = some L := ReachState.typeAt_of_findTypeIdx hl
          exact h.discoverAt hti
            (fun hb => .inl (h.oldOf lIdx L hL hlc hb) trivial)
            (fun hb => .inl (h.new lIdx L hL hb))
        · split
          · rename_i hrc
            have hR : σ.typeAt rIdx = some R := ReachState.typeAt_of_findTypeIdx hr
            exact h.discoverAt hti
              (fun hb => .inr (h.oldOf rIdx R hR hrc hb) trivial)
              (fun hb => .inr (h.new rIdx R hR hb))
          · exact h
  · exact h

theorem typeRule_sound (h : ReachSound Γ σ) (ti : Nat) :
    ReachSound Γ (typeRule σ ti) := by
  unfold typeRule
  split
  · next L R hty => exact prodTypeRule_sound h ti L R hty
  · next Arg Ret hty =>
      refine expAppRule_sound (expEtaRule_sound h ti Arg Ret hty) ti Arg Ret ?_
      rw [ReachState.typeAt_of_le (expEtaRule_le σ ti Ret)]
      exact hty
  · next L R hty => exact coprodTypeRule_sound h ti L R hty
  · exact h

/-! ### Preservation by the sweep and the driver -/

private theorem foldl_sound {α : Type} (f : ReachState n → α → ReachState n)
    (hf : ∀ σ a, ReachSound Γ σ → ReachSound Γ (f σ a)) :
    ∀ (l : List α) (σ : ReachState n), ReachSound Γ σ → ReachSound Γ (l.foldl f σ)
  | [], _, h => h
  | a :: l, σ, h => foldl_sound f hf l (f σ a) (hf σ a h)

theorem reachSweep_sound (h : ReachSound Γ σ) : ReachSound Γ (reachSweep Γ σ) :=
  foldl_sound (hypRule Γ) (fun _ k hs => hypRule_sound hs k) _ _
    (unitEtaRule_sound
      (foldl_sound (seedHypRule Γ) (fun _ k hs => seedHypRule_sound hs k) _ σ h))

theorem reachStep_sound (h : ReachSound Γ σ) : ReachSound Γ (reachStep Γ σ) :=
  foldl_sound typeRule (fun _ ti hs => typeRule_sound hs ti) _ _ (reachSweep_sound h)

@[simp] theorem ReachCell.empty_retrievable : ReachCell.empty.retrievable = false := rfl
@[simp] theorem ReachCell.empty_oldWitness : ReachCell.empty.oldWitness = none := rfl
@[simp] theorem ReachCell.empty_newWitness : ReachCell.empty.newWitness = none := rfl

private theorem getCell_initial (types : Array (Object n)) (i : Nat) :
    ReachState.getCell
        { types := types, cells := Array.replicate types.size ReachCell.empty } i =
      ReachCell.empty := by
  unfold ReachState.getCell
  rw [Array.getElem?_replicate]
  by_cases hi : i < types.size
  · rw [if_pos hi]
  · rw [if_neg hi]

theorem reachSound_of_empty (Γ : ReachCtx n) (σ : ReachState n)
    (hcell : ∀ i, σ.getCell i = ReachCell.empty) (hinc : σ.inconsistent = false) :
    ReachSound Γ σ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i A _ hs; rw [hcell i] at hs; simp at hs
  · intro i A _ hs; rw [hcell i] at hs; simp at hs
  · intro i A _ hs; rw [hcell i] at hs; simp at hs
  · intro i hs; rw [hcell i] at hs; simp at hs
  · intro i _ hs; rw [hcell i] at hs; simp [ReachCell.simplyDeducible] at hs
  · intro hs; rw [hinc] at hs; simp at hs

theorem mkReachState_sound (Γ : ReachCtx n) (goal : Object n) :
    ReachSound Γ (mkReachState Γ goal) := by
  unfold mkReachState
  refine foldl_sound (seedHypRule Γ) (fun _ k hs => seedHypRule_sound hs k) _ _ ?_
  exact reachSound_of_empty Γ _ (fun i => getCell_initial _ i) rfl

theorem runReachabilityFrom_sound (Γ : ReachCtx n) (σ : ReachState n) :
    ReachSound Γ σ → ReachSound Γ (runReachabilityFrom Γ σ) := by
  induction σ using runReachabilityFrom.induct (Γ := Γ) with
  | case1 σ hlt ih =>
      intro h; rw [runReachabilityFrom, if_pos hlt]; exact ih (reachStep_sound h)
  | case2 σ hlt =>
      intro h; rw [runReachabilityFrom, if_neg hlt]; exact reachStep_sound h

/-- The finite closure only ever records derivable facts. -/
theorem runReachability_sound (Γ : ReachCtx n) (goal : Object n) :
    ReachSound Γ (runReachability Γ goal) :=
  runReachabilityFrom_sound Γ _ (mkReachState_sound Γ goal)

/-! ### Headline soundness statements -/

theorem isSimplyDeducible_sound {Γ : ReachCtx n} {goal A : Object n}
    (h : isSimplyDeducible (runReachability Γ goal) A = true) : SimpleDeduction Γ A := by
  unfold isSimplyDeducible at h
  cases hfind : (runReachability Γ goal).findTypeIdx A with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some i =>
      rw [hfind] at h
      exact (runReachability_sound Γ goal).deducible i A
        (ReachState.typeAt_of_findTypeIdx hfind) h

/-- Provenance: a uses-new witness really needs a hypothesis from `Γnew`. -/
theorem usesNew_sound {Γ : ReachCtx n} {goal A : Object n}
    (h : usesNew (runReachability Γ goal) A = true) : UsesNew Γ A := by
  unfold usesNew at h
  cases hfind : (runReachability Γ goal).findTypeIdx A with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some i =>
      rw [hfind] at h
      exact (runReachability_sound Γ goal).new i A
        (ReachState.typeAt_of_findTypeIdx hfind) h

/-- Provenance: no uses-new witness means the old fragment already suffices. -/
theorem oldOnly_sound {Γ : ReachCtx n} {goal A : Object n}
    (hd : isSimplyDeducible (runReachability Γ goal) A = true)
    (hn : usesNew (runReachability Γ goal) A = false) : OldDeduction Γ A := by
  unfold isSimplyDeducible at hd
  unfold usesNew at hn
  cases hfind : (runReachability Γ goal).findTypeIdx A with
  | none => rw [hfind] at hd; exact absurd hd (by simp)
  | some i =>
      rw [hfind] at hd hn
      exact (runReachability_sound Γ goal).oldOf i A
        (ReachState.typeAt_of_findTypeIdx hfind) hd hn

/-- Retrievability really means the type is bound in the context. -/
theorem isRetrievable_sound {Γ : ReachCtx n} {goal A : Object n}
    (h : isRetrievable (runReachability Γ goal) A = true) :
    ∃ j : Nat, Γ.hyps[j]? = some A := by
  unfold isRetrievable at h
  cases hfind : (runReachability Γ goal).findTypeIdx A with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some i =>
      rw [hfind] at h
      exact (runReachability_sound Γ goal).bound i A
        (ReachState.typeAt_of_findTypeIdx hfind) h

/-- The inconsistency flag is raised only when `0` really is derivable. -/
theorem inconsistent_sound {Γ : ReachCtx n} {goal : Object n}
    (h : (runReachability Γ goal).inconsistent = true) :
    SimpleDeduction Γ (.never : Object n) :=
  (runReachability_sound Γ goal).inconsistent h

/-- Conversely, `0` becoming deducible always raises the flag. -/
theorem inconsistent_of_never_deducible {Γ : ReachCtx n} {goal : Object n}
    (h : isSimplyDeducible (runReachability Γ goal) (.never : Object n) = true) :
    (runReachability Γ goal).inconsistent = true := by
  unfold isSimplyDeducible at h
  cases hfind : (runReachability Γ goal).findTypeIdx (.never : Object n) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some i =>
      rw [hfind] at h
      exact (runReachability_sound Γ goal).neverFlagged i
        (ReachState.typeAt_of_findTypeIdx hfind) h

end Equality
end Gimbal
