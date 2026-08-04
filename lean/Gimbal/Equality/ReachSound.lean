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

theorem ReachState.typeAt_discoverDual (σ : ReachState n) (i : Nat)
    (oldOk newOk : Bool) (w : Witness) (j : Nat) :
    (σ.discoverDual i oldOk newOk w).typeAt j = σ.typeAt j := by
  simp [ReachState.typeAt, ← (σ.le_discoverDual i oldOk newOk w).types]

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
  /-- An η witness on a product was written from already-SD components. -/
  etaProd : ∀ i L R, σ.typeAt i = some (.prod L R) →
    ((σ.getCell i).oldWitness = some .eta ∨ (σ.getCell i).newWitness = some .eta) →
    isSimplyDeducible σ L = true ∧ isSimplyDeducible σ R = true
  fitsOk : ∀ i A w, σ.typeAt i = some A →
    ((σ.getCell i).oldWitness = some w ∨ (σ.getCell i).newWitness = some w) →
    Witness.fits w A = true
  /-- Neutral witnesses agree on hyp/type indices and reconstructed result type. -/
  reconOk : ∀ i A w, σ.typeAt i = some A →
    ((σ.getCell i).oldWitness = some w ∨ (σ.getCell i).newWitness = some w) →
      Witness.isNeutral w = true →
        WitnessReconShape σ Γ.hyps A w

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

/-- Simply deducible and not uses-new implies the old slot is inhabited. -/
theorem oldDeducible_of (h : ReachSound Γ σ) (i : Nat) (A : Object n)
    (hA : σ.typeAt i = some A) (hd : (σ.getCell i).simplyDeducible = true)
    (hn : (σ.getCell i).usesNew = false) :
    (σ.getCell i).oldDeducible = true := by
  have hnew : (σ.getCell i).newWitness.isSome = false := hn
  unfold ReachCell.simplyDeducible ReachCell.oldDeducible at *
  rcases Bool.or_eq_true_iff.mp hd with hd | hd
  · rcases Bool.or_eq_true_iff.mp hd with hr | ho
    · rcases h.witnessed i hr with ho | hn'
      · exact ho
      · rw [hnew] at hn'; exact absurd hn' (by simp)
    · exact ho
  · rw [hnew] at hd; exact absurd hd (by simp)

/-- A simply deducible cell fires at least one dual-discover branch. -/
theorem fires_of_simplyDeducible (h : ReachSound Γ σ) (i : Nat) (A : Object n)
    (hA : σ.typeAt i = some A) (hd : (σ.getCell i).simplyDeducible = true) :
    (σ.getCell i).oldDeducible = true ∨ (σ.getCell i).usesNew = true := by
  cases hu : (σ.getCell i).usesNew
  · exact Or.inl (h.oldDeducible_of i A hA hd hu)
  · exact Or.inr rfl

end ReachSound

/-! ### Preservation by a single discovery -/



/-- A simply-deducible non-neutral product cell stores `.eta` (intro mismatches
are ruled out by `fitsOk`). -/
theorem eta_of_nonneutral_prod {Γ : ReachCtx n} {σ : ReachState n}
    (hs : ReachSound Γ σ) {i : Nat} {L R : Object n}
    (hty : σ.typeAt i = some (.prod L R))
    (hsd : (σ.getCell i).simplyDeducible = true)
    (hNeu : ¬((σ.getCell i).oldNeutral = true ∨ (σ.getCell i).newNeutral = true)) :
    (σ.getCell i).oldWitness = some .eta ∨ (σ.getCell i).newWitness = some .eta := by
  have slot : (σ.getCell i).oldWitness.isSome = true ∨
      (σ.getCell i).newWitness.isSome = true := by
    unfold ReachCell.simplyDeducible at hsd
    rcases Bool.or_eq_true_iff.mp hsd with h' | hn
    · rcases Bool.or_eq_true_iff.mp h' with hr | ho
      · exact hs.witnessed i hr
      · exact Or.inl ho
    · exact Or.inr hn
  cases ho : (σ.getCell i).oldWitness with
  | some w =>
    have hnn : Witness.isNeutral w = false := by
      have : (σ.getCell i).oldNeutral = false := by
        cases h : (σ.getCell i).oldNeutral
        · rfl
        · exact False.elim (hNeu (Or.inl h))
      simpa [ReachCell.oldNeutral, ho] using this
    have hfit : Witness.fits w (.prod L R) = true :=
      hs.fitsOk i (.prod L R) w hty (Or.inl ho)
    cases w with
    | eta => exact Or.inl rfl
    | unit | inl _ | inr _ =>
        simp [Witness.fits] at hfit
    | ctxVar _ | fstHyp _ | sndHyp _ | fstType _ | sndType _
    | app _ _ | appTy _ _ =>
        simp [Witness.isNeutral] at hnn
  | none =>
    cases hn : (σ.getCell i).newWitness with
    | some w =>
      have hnn : Witness.isNeutral w = false := by
        have : (σ.getCell i).newNeutral = false := by
          cases h : (σ.getCell i).newNeutral
          · rfl
          · exact False.elim (hNeu (Or.inr h))
        simpa [ReachCell.newNeutral, hn] using this
      have hfit : Witness.fits w (.prod L R) = true :=
        hs.fitsOk i (.prod L R) w hty (Or.inr hn)
      cases w with
      | eta => exact Or.inr rfl
      | unit | inl _ | inr _ =>
          simp [Witness.fits] at hfit
      | ctxVar _ | fstHyp _ | sndHyp _ | fstType _ | sndType _
      | app _ _ | appTy _ _ =>
          simp [Witness.isNeutral] at hnn
    | none =>
      cases slot with
      | inl h => simp [ho] at h
      | inr h => simp [hn] at h

theorem ReachCell.simplyDeducible_of_le {c d : ReachCell} (h : ReachCell.Le c d)
    (hc : c.simplyDeducible = true) : d.simplyDeducible = true := by
  unfold ReachCell.simplyDeducible at *
  rcases Bool.or_eq_true_iff.mp hc with h' | hn
  · rcases Bool.or_eq_true_iff.mp h' with hr | ho
    · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl (h.retrievable hr))))
    · have ⟨w, hw⟩ := Option.isSome_iff_exists.mp ho
      exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inr
        (Option.isSome_iff_exists.mpr ⟨w, h.old w hw⟩))))
  · have ⟨w, hw⟩ := Option.isSome_iff_exists.mp hn
    exact Bool.or_eq_true_iff.mpr (Or.inr
      (Option.isSome_iff_exists.mpr ⟨w, h.new w hw⟩))

theorem isSimplyDeducible_of_le {σ τ : ReachState n} (hle : ReachState.Le σ τ)
    {A : Object n} (h : isSimplyDeducible σ A = true) :
    isSimplyDeducible τ A = true := by
  unfold isSimplyDeducible at *
  cases hfind : σ.findTypeIdx A with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some i =>
      rw [hfind] at h
      have hfind' : τ.findTypeIdx A = some i := by
        simpa [ReachState.findTypeIdx, hle.types] using hfind
      rw [hfind']
      exact ReachCell.simplyDeducible_of_le (hle.cell i) h

theorem ReachCell.record_eta_of_ne {c : ReachCell} {b : Bool} {w : Witness}
    (hw : w ≠ .eta)
    (h : (c.record b w).oldWitness = some .eta ∨ (c.record b w).newWitness = some .eta) :
    c.oldWitness = some .eta ∨ c.newWitness = some .eta := by
  cases b with
  | false =>
    cases how : c.oldWitness with
    | none =>
      have hrec : c.record false w = { c with oldWitness := some w } := by
        unfold ReachCell.record; rw [how]; rfl
      rw [hrec] at h
      cases h with
      | inl holdW => exact (hw (Option.some.inj holdW)).elim
      | inr hnewW => exact Or.inr hnewW
    | some wOld =>
      have hrec : c.record false w = c := by
        unfold ReachCell.record; rw [how]; rfl
      rw [hrec] at h
      rw [← how]; exact h
  | true =>
    cases hn : c.newWitness with
    | none =>
      have hrec : c.record true w = { c with newWitness := some w } := by
        unfold ReachCell.record; rw [hn]; rfl
      rw [hrec] at h
      cases h with
      | inl holdW => exact Or.inl holdW
      | inr hnewW => exact (hw (Option.some.inj hnewW)).elim
    | some wNew =>
      have hrec : c.record true w = c := by
        unfold ReachCell.record; rw [hn]; rfl
      rw [hrec] at h
      rw [← hn]; exact h

theorem ReachCell.recordHyp_eta_of_ctxVar {c : ReachCell} {b : Bool} {k : Nat}
    (h : (c.recordHyp b (.ctxVar k)).oldWitness = some .eta ∨
      (c.recordHyp b (.ctxVar k)).newWitness = some .eta) :
    c.oldWitness = some .eta ∨ c.newWitness = some .eta := by
  unfold ReachCell.recordHyp at h
  refine ReachCell.record_eta_of_ne (w := .ctxVar k) ?_ h
  intro hneq; cases hneq


theorem ReachCell.fits_of_record {n : Nat} {c : ReachCell} {b : Bool} {w w' : Witness}
    {A : Object n}
    (hpre : ∀ w₀, (c.oldWitness = some w₀ ∨ c.newWitness = some w₀) →
      Witness.fits w₀ A = true)
    (hfit : Witness.fits w A = true)
    (hwit : (c.record b w).oldWitness = some w' ∨ (c.record b w).newWitness = some w') :
    Witness.fits w' A = true := by
  cases b with
  | false =>
    cases how : c.oldWitness with
    | none =>
      have hrec : c.record false w = { c with oldWitness := some w } := by
        unfold ReachCell.record; rw [how]; rfl
      rw [hrec] at hwit
      cases hwit with
      | inl holdW =>
        have : w' = w := (Option.some.inj holdW).symm
        subst this; exact hfit
      | inr hnewW =>
        exact hpre w' (Or.inr hnewW)
    | some wOld =>
      have hrec : c.record false w = c := by
        unfold ReachCell.record; rw [how]; rfl
      rw [hrec] at hwit
      exact hpre w' hwit
  | true =>
    cases hn : c.newWitness with
    | none =>
      have hrec : c.record true w = { c with newWitness := some w } := by
        unfold ReachCell.record; rw [hn]; rfl
      rw [hrec] at hwit
      cases hwit with
      | inl holdW =>
        exact hpre w' (Or.inl holdW)
      | inr hnewW =>
        have : w' = w := (Option.some.inj hnewW).symm
        subst this; exact hfit
    | some wNew =>
      have hrec : c.record true w = c := by
        unfold ReachCell.record; rw [hn]; rfl
      rw [hrec] at hwit
      exact hpre w' hwit

theorem ReachCell.shape_of_record {n : Nat} {σ : ReachState n}
    {hyps : Array (Object n)} {c : ReachCell} {b : Bool} {w w' : Witness}
    {A : Object n}
    (hpre : ∀ w₀, (c.oldWitness = some w₀ ∨ c.newWitness = some w₀) →
      Witness.isNeutral w₀ = true → WitnessReconShape σ hyps A w₀)
    (hshape : Witness.isNeutral w = true → WitnessReconShape σ hyps A w)
    (hwit : (c.record b w).oldWitness = some w' ∨ (c.record b w).newWitness = some w')
    (hneu : Witness.isNeutral w' = true) :
    WitnessReconShape σ hyps A w' := by
  cases b with
  | false =>
    cases how : c.oldWitness with
    | none =>
      have hrec : c.record false w = { c with oldWitness := some w } := by
        unfold ReachCell.record; rw [how]; rfl
      rw [hrec] at hwit
      cases hwit with
      | inl holdW =>
        have : w' = w := (Option.some.inj holdW).symm
        subst this; exact hshape hneu
      | inr hnewW =>
        exact hpre w' (Or.inr hnewW) hneu
    | some wOld =>
      have hrec : c.record false w = c := by
        unfold ReachCell.record; rw [how]; rfl
      rw [hrec] at hwit
      exact hpre w' hwit hneu
  | true =>
    cases hn : c.newWitness with
    | none =>
      have hrec : c.record true w = { c with newWitness := some w } := by
        unfold ReachCell.record; rw [hn]; rfl
      rw [hrec] at hwit
      cases hwit with
      | inl holdW =>
        exact hpre w' (Or.inl holdW) hneu
      | inr hnewW =>
        have : w' = w := (Option.some.inj hnewW).symm
        subst this; exact hshape hneu
    | some wNew =>
      have hrec : c.record true w = c := by
        unfold ReachCell.record; rw [hn]; rfl
      rw [hrec] at hwit
      exact hpre w' hwit hneu

theorem ReachSound.discoverAt {Γ : ReachCtx n} {σ : ReachState n}
    (h : ReachSound Γ σ) {i : Nat} {b : Bool} {w : Witness} {A : Object n}
    (hA : σ.typeAt i = some A)
    (hold : b = false → OldDeduction Γ A) (hnew : b = true → UsesNew Γ A)
    (heta : ∀ L R, w = .eta → A = .prod L R →
      isSimplyDeducible σ L = true ∧ isSimplyDeducible σ R = true)
    (hfit : Witness.fits w A = true)
    (hshape : Witness.isNeutral w = true → WitnessReconShape σ Γ.hyps A w) :
    ReachSound Γ (σ.discover i b w) := by
  have hle := σ.le_discover i b w
  have hAsimple : SimpleDeduction Γ A := by
    cases hb : b
    · exact (hold hb).toSimple
    · exact (hnew hb).toSimple
  have htypes : ∀ j, (σ.discover i b w).typeAt j = σ.typeAt j := by
    intro j; exact ReachState.typeAt_discover σ i b w j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro j L R hB hetaW
    rw [ReachState.typeAt_discover] at hB
    rcases ReachState.getCell_discover σ i b w j with heq | ⟨hij, heq⟩
    · have hetaW₀ : (σ.getCell j).oldWitness = some .eta ∨
          (σ.getCell j).newWitness = some .eta := by
        rw [heq] at hetaW; exact hetaW
      have ⟨hL, hR⟩ := h.etaProd j L R hB hetaW₀
      exact ⟨isSimplyDeducible_of_le hle hL, isSimplyDeducible_of_le hle hR⟩
    · subst hij
      have hAB : A = .prod L R := ReachState.typeAt_inj hA hB
      subst hAB
      have ⟨hL0, hR0⟩ : isSimplyDeducible σ L = true ∧ isSimplyDeducible σ R = true := by
        by_cases hw : w = .eta
        · exact heta L R hw rfl
        · have hetaW₀ : (σ.getCell j).oldWitness = some .eta ∨
              (σ.getCell j).newWitness = some .eta := by
            rw [heq] at hetaW
            exact ReachCell.record_eta_of_ne hw hetaW
          exact h.etaProd j L R hA hetaW₀
      exact ⟨isSimplyDeducible_of_le hle hL0, isSimplyDeducible_of_le hle hR0⟩
  · intro j B w' hB hwit
    rw [ReachState.typeAt_discover] at hB
    rcases ReachState.getCell_discover σ i b w j with heq | ⟨hij, heq⟩
    · exact h.fitsOk j B w' hB (by rw [heq] at hwit; exact hwit)
    · subst hij
      have hAB : A = B := ReachState.typeAt_inj hA hB
      subst hAB
      have hwit' :
          ((σ.getCell j).record b w).oldWitness = some w' ∨
            ((σ.getCell j).record b w).newWitness = some w' := by
        rwa [heq] at hwit
      exact ReachCell.fits_of_record
        (fun w₀ hw => h.fitsOk j A w₀ hA hw) hfit hwit'
  · intro j B w' hB hwit hneu
    rw [ReachState.typeAt_discover] at hB
    rcases ReachState.getCell_discover σ i b w j with heq | ⟨hij, heq⟩
    · exact WitnessReconShape.of_types_eq htypes
        (h.reconOk j B w' hB (by rw [heq] at hwit; exact hwit) hneu)
    · subst hij
      have hAB : A = B := ReachState.typeAt_inj hA hB
      subst hAB
      have hwit' :
          ((σ.getCell j).record b w).oldWitness = some w' ∨
            ((σ.getCell j).record b w).newWitness = some w' := by
        rwa [heq] at hwit
      exact WitnessReconShape.of_types_eq htypes
        (ReachCell.shape_of_record
          (fun w₀ hw hneu₀ => h.reconOk j A w₀ hA hw hneu₀)
          hshape hwit' hneu)

theorem ReachSound.discoverAt_not_eta {Γ : ReachCtx n} {σ : ReachState n}
    (h : ReachSound Γ σ) {i : Nat} {b : Bool} {w : Witness} {A : Object n}
    (hA : σ.typeAt i = some A)
    (hold : b = false → OldDeduction Γ A) (hnew : b = true → UsesNew Γ A)
    (hne : w ≠ .eta) (hfit : Witness.fits w A = true)
    (hshape : Witness.isNeutral w = true → WitnessReconShape σ Γ.hyps A w) :
    ReachSound Γ (σ.discover i b w) :=
  h.discoverAt hA hold hnew (fun _ _ hw => (hne hw).elim) hfit hshape

theorem ReachSound.discoverDualAt {Γ : ReachCtx n} {σ : ReachState n}
    (h : ReachSound Γ σ) {i : Nat} {oldOk newOk : Bool} {w : Witness} {A : Object n}
    (hA : σ.typeAt i = some A)
    (hold : oldOk = true → OldDeduction Γ A)
    (hnew : newOk = true → UsesNew Γ A)
    (heta : ∀ L R, w = .eta → A = .prod L R →
      isSimplyDeducible σ L = true ∧ isSimplyDeducible σ R = true)
    (hfit : Witness.fits w A = true)
    (hshape : Witness.isNeutral w = true → WitnessReconShape σ Γ.hyps A w) :
    ReachSound Γ (σ.discoverDual i oldOk newOk w) := by
  unfold ReachState.discoverDual
  cases holdOk : oldOk with
  | false =>
    cases hnewOk : newOk with
    | false => simpa [holdOk, hnewOk] using h
    | true =>
      simp only [holdOk, hnewOk, ↓reduceIte]
      exact h.discoverAt hA (fun hb => by cases hb) (fun _ => hnew hnewOk) heta hfit
        (fun hneu => WitnessReconShape.of_types_eq (fun _ => rfl) (hshape hneu))
  | true =>
    have h1 := h.discoverAt (b := false) (w := w) hA
      (fun _ => hold holdOk) (fun hb => by cases hb) heta hfit hshape
    cases hnewOk : newOk with
    | false => simpa [holdOk, hnewOk] using h1
    | true =>
      simp only [holdOk, hnewOk, ↓reduceIte]
      refine h1.discoverAt ?_ (fun hb => by cases hb) (fun _ => hnew hnewOk) ?_ hfit ?_
      · rw [ReachState.typeAt_discover]; exact hA
      · intro L R hw heq
        have ⟨hL, hR⟩ := heta L R hw heq
        exact ⟨isSimplyDeducible_of_le (σ.le_discover i false w) hL,
          isSimplyDeducible_of_le (σ.le_discover i false w) hR⟩
      · intro hneu
        exact WitnessReconShape.of_types_eq (fun j => ReachState.typeAt_discover σ i false w j)
          (hshape hneu)

theorem ReachSound.discoverDualAt_not_eta {Γ : ReachCtx n} {σ : ReachState n}
    (h : ReachSound Γ σ) {i : Nat} {oldOk newOk : Bool} {w : Witness} {A : Object n}
    (hA : σ.typeAt i = some A)
    (hold : oldOk = true → OldDeduction Γ A)
    (hnew : newOk = true → UsesNew Γ A)
    (hne : w ≠ .eta) (hfit : Witness.fits w A = true)
    (hshape : Witness.isNeutral w = true → WitnessReconShape σ Γ.hyps A w) :
    ReachSound Γ (σ.discoverDual i oldOk newOk w) :=
  h.discoverDualAt hA hold hnew (fun _ _ hw => (hne hw).elim) hfit hshape

theorem ReachSound.markHypAt {Γ : ReachCtx n} {σ : ReachState n}
    (h : ReachSound Γ σ) (k : Nat)
    (hpos : ∀ A, Γ.hyps[k]? = some A → objectPolarity A = .pos) :
    ReachSound Γ (σ.markHyp Γ k) := by
  have hle := σ.le_markHyp Γ k
  have htypes : ∀ j, (σ.markHyp Γ k).typeAt j = σ.typeAt j := by
    intro j; simp [ReachState.typeAt, ← (σ.le_markHyp Γ k).types]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro j L R hB hetaW
    rw [ReachState.typeAt_markHyp] at hB
    rcases ReachState.getCell_markHyp σ Γ k j with heq | ⟨A, idx, hA, hi, hij, heq⟩
    · have hetaW₀ : (σ.getCell j).oldWitness = some .eta ∨
          (σ.getCell j).newWitness = some .eta := by
        rw [heq] at hetaW; exact hetaW
      have ⟨hL, hR⟩ := h.etaProd j L R hB hetaW₀
      exact ⟨isSimplyDeducible_of_le hle hL, isSimplyDeducible_of_le hle hR⟩
    · subst hij
      have hty0 := ReachState.typeAt_of_findTypeIdx hi
      have hAB : A = .prod L R := ReachState.typeAt_inj hty0 hB
      subst hAB
      have hetaW₀ : (σ.getCell j).oldWitness = some .eta ∨
          (σ.getCell j).newWitness = some .eta := by
        rw [heq] at hetaW
        exact ReachCell.recordHyp_eta_of_ctxVar hetaW
      have ⟨hL, hR⟩ := h.etaProd j L R hty0 hetaW₀
      exact ⟨isSimplyDeducible_of_le hle hL, isSimplyDeducible_of_le hle hR⟩
  · intro j B w' hB hwit
    rw [ReachState.typeAt_markHyp] at hB
    rcases ReachState.getCell_markHyp σ Γ k j with heq | ⟨A, idx, hA, hi, hij, heq⟩
    · exact h.fitsOk j B w' hB (by rw [heq] at hwit; exact hwit)
    · subst hij
      have hty0 := ReachState.typeAt_of_findTypeIdx hi
      have hAB : A = B := ReachState.typeAt_inj hty0 hB
      subst hAB
      -- recordHyp writes ctxVar which fits any type
      have hfit : Witness.fits (.ctxVar k) A = true := by simp [Witness.fits]
      have hwit' : ((σ.getCell j).record (Γ.isNew k) (.ctxVar k)).oldWitness = some w' ∨
          ((σ.getCell j).record (Γ.isNew k) (.ctxVar k)).newWitness = some w' := by
        rw [heq] at hwit
        simpa [ReachCell.recordHyp] using hwit
      exact ReachCell.fits_of_record
        (fun w₀ hw => h.fitsOk j A w₀ hty0 hw) hfit hwit'
  · intro j B w' hB hwit hneu
    rw [ReachState.typeAt_markHyp] at hB
    rcases ReachState.getCell_markHyp σ Γ k j with heq | ⟨A, idx, hA, hi, hij, heq⟩
    · exact WitnessReconShape.of_types_eq htypes
        (h.reconOk j B w' hB (by rw [heq] at hwit; exact hwit) hneu)
    · subst hij
      have hty0 := ReachState.typeAt_of_findTypeIdx hi
      have hAB : A = B := ReachState.typeAt_inj hty0 hB
      subst hAB
      have hshape : Witness.isNeutral (.ctxVar k) = true →
          WitnessReconShape σ Γ.hyps A (.ctxVar k) := fun _ => hA
      have hwit' : ((σ.getCell j).record (Γ.isNew k) (.ctxVar k)).oldWitness = some w' ∨
          ((σ.getCell j).record (Γ.isNew k) (.ctxVar k)).newWitness = some w' := by
        rw [heq] at hwit
        simpa [ReachCell.recordHyp] using hwit
      exact WitnessReconShape.of_types_eq htypes
        (ReachCell.shape_of_record
          (fun w₀ hw hneu₀ => h.reconOk j A w₀ hty0 hw hneu₀)
          hshape hwit' hneu)

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
    exact h.discoverAt_not_eta (ReachState.typeAt_of_findTypeIdx hu)
      (fun _ => .unit trivial) (fun hb => by simp at hb) (fun h => by cases h)
      (by simp [Witness.fits])
      (fun hneu => by simp [Witness.isNeutral] at hneu)
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
        have h1 := h.discoverAt_not_eta (b := Γ.isNew k) (w := .fstHyp k)
          (ReachState.typeAt_of_findTypeIdx hl)
          (fun hb => .fstHyp k hk hb trivial) (fun hb => .fstHyp k hk hb)
          (fun h => by cases h) (by simp [Witness.fits])
          (fun _ => ⟨L, R, hk, rfl⟩)
        refine h1.discoverAt_not_eta (w := .sndHyp k) ?_
          (fun hb => .sndHyp k hk hb trivial) (fun hb => .sndHyp k hk hb)
          (fun h => by cases h) (by simp [Witness.fits])
          (fun _ => ⟨L, R, hk, rfl⟩)
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
      have hA : σ.typeAt aIdx = some Arg := ReachState.typeAt_of_findTypeIdx ha
      have hR : σ.typeAt rIdx = some Ret := ReachState.typeAt_of_findTypeIdx hr
      refine h.discoverDualAt_not_eta (w := .app k aIdx) hR ?_ ?_ (fun h => by cases h)
          (by simp [Witness.fits]) (fun _ => ⟨Arg, Ret, hk, hA, rfl⟩)
      · intro hold
        obtain ⟨hOld, hFn⟩ := Bool.and_eq_true_iff.mp hold
        exact .appHyp k hk (by simpa using hFn)
          (h.old aIdx Arg hA (by simpa [ReachCell.oldDeducible] using hOld)) trivial
      · intro hnew
        obtain ⟨hdec, hprov⟩ := Bool.and_eq_true_iff.mp hnew
        cases hu : (σ.getCell aIdx).usesNew
        · have hFn : Γ.isNew k = true := by
            simp [hu, Bool.or_eq_true_iff] at hprov
            exact hprov
          exact .appHypFn k hk hFn (h.deducible aIdx Arg hA hdec)
        · exact .appHypArg k hk (h.new aIdx Arg hA hu)

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
  cases hl : σ.findTypeIdx L with
  | none => simpa [hl] using h
  | some lIdx =>
    cases hr : σ.findTypeIdx R with
    | none => simpa [hl, hr] using h
    | some rIdx =>
      dsimp only
      have hL0 : σ.typeAt lIdx = some L := ReachState.typeAt_of_findTypeIdx hl
      have hR0 : σ.typeAt rIdx = some R := ReachState.typeAt_of_findTypeIdx hr
      have holdN : (σ.getCell ti).oldNeutral = true → OldDeduction Γ L := by
        intro hold
        have how : (σ.getCell ti).oldWitness.isSome = true := by
          revert hold; simp only [ReachCell.oldNeutral]
          cases (σ.getCell ti).oldWitness <;> simp
        exact .fst (h.old ti _ hti how) trivial
      have hnewN : (σ.getCell ti).newNeutral = true → UsesNew Γ L := by
        intro hnew
        have hn : (σ.getCell ti).newWitness.isSome = true := by
          revert hnew; simp only [ReachCell.newNeutral]
          cases (σ.getCell ti).newWitness <;> simp
        exact .fst (h.new ti _ hti hn)
      have h1 := h.discoverDualAt_not_eta (w := .fstType ti) hL0 holdN hnewN (fun h => by cases h)
          (by simp [Witness.fits]) (fun _ => ⟨L, R, hti, rfl⟩)
      have hRty :
          (σ.discoverDual lIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
              (.fstType ti)).typeAt rIdx = some R := by
        rw [ReachState.typeAt_discoverDual]; exact hR0
      have holdNR : (σ.getCell ti).oldNeutral = true → OldDeduction Γ R := by
        intro hold
        have how : (σ.getCell ti).oldWitness.isSome = true := by
          revert hold; simp only [ReachCell.oldNeutral]
          cases (σ.getCell ti).oldWitness <;> simp
        exact .snd (h.old ti _ hti how) trivial
      have hnewNR : (σ.getCell ti).newNeutral = true → UsesNew Γ R := by
        intro hnew
        have hn : (σ.getCell ti).newWitness.isSome = true := by
          revert hnew; simp only [ReachCell.newNeutral]
          cases (σ.getCell ti).newWitness <;> simp
        exact .snd (h.new ti _ hti hn)
      have h2 := h1.discoverDualAt_not_eta (w := .sndType ti) hRty holdNR hnewNR (fun h => by cases h)
          (by simp [Witness.fits])
          (fun _ => ⟨L, R, by
            rw [ReachState.typeAt_discoverDual]; exact hti, rfl⟩)
      split
      · -- `!simplyDeducible`: maybe η
        split
        · rename_i hboth
          obtain ⟨hlc, hrc⟩ := Bool.and_eq_true_iff.mp hboth
          have hti' :
              ((σ.discoverDual lIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
                    (.fstType ti)).discoverDual rIdx (σ.getCell ti).oldNeutral
                    (σ.getCell ti).newNeutral (.sndType ti)).typeAt ti =
                some (.prod L R) := by
            rw [ReachState.typeAt_discoverDual, ReachState.typeAt_discoverDual]
            exact hti
          have hLσ :
              ((σ.discoverDual lIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
                    (.fstType ti)).discoverDual rIdx (σ.getCell ti).oldNeutral
                    (σ.getCell ti).newNeutral (.sndType ti)).typeAt lIdx = some L := by
            rw [ReachState.typeAt_discoverDual, ReachState.typeAt_discoverDual]
            exact hL0
          have hRσ :
              ((σ.discoverDual lIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
                    (.fstType ti)).discoverDual rIdx (σ.getCell ti).oldNeutral
                    (σ.getCell ti).newNeutral (.sndType ti)).typeAt rIdx = some R := by
            rw [ReachState.typeAt_discoverDual, ReachState.typeAt_discoverDual]
            exact hR0
          refine h2.discoverDualAt (w := .eta) hti' ?_ ?_ ?_ (by simp [Witness.fits])
              (fun hneu => by simp [Witness.isNeutral] at hneu)
          · intro hold
            obtain ⟨h1o, h2o⟩ := Bool.and_eq_true_iff.mp hold
            exact .pair
              (h2.old lIdx L hLσ (by simpa [ReachCell.oldDeducible] using h1o))
              (h2.old rIdx R hRσ (by simpa [ReachCell.oldDeducible] using h2o)) trivial
          · intro hnew
            let σ₁ :=
              (σ.discoverDual lIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
                  (.fstType ti)).discoverDual rIdx (σ.getCell ti).oldNeutral
                  (σ.getCell ti).newNeutral (.sndType ti)
            cases hu : (σ₁.getCell lIdx).usesNew
            · have hrn : (σ₁.getCell rIdx).usesNew = true := by
                change ((σ₁.getCell lIdx).usesNew || (σ₁.getCell rIdx).usesNew) = true at hnew
                simpa [hu] using hnew
              exact .pairR (h2.deducible lIdx L hLσ hlc)
                (h2.new rIdx R hRσ hrn)
            · exact .pairL (h2.new lIdx L hLσ hu)
                (h2.deducible rIdx R hRσ hrc)
          · intro L' R' _ heq
            injection heq with e1 e2; subst e1; subst e2
            let σ₁ :=
              (σ.discoverDual lIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
                  (.fstType ti)).discoverDual rIdx (σ.getCell ti).oldNeutral
                  (σ.getCell ti).newNeutral (.sndType ti)
            have ht : σ₁.types = σ.types := by
              have h1 := (ReachState.le_discoverDual σ lIdx
                (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral (.fstType ti)).types
              have h2 := (ReachState.le_discoverDual
                (σ.discoverDual lIdx (σ.getCell ti).oldNeutral
                  (σ.getCell ti).newNeutral (.fstType ti))
                rIdx (σ.getCell ti).oldNeutral (σ.getCell ti).newNeutral
                (.sndType ti)).types
              exact h2.symm.trans h1.symm
            constructor
            · unfold isSimplyDeducible
              have hfind : σ₁.findTypeIdx L = some lIdx := by
                simpa [ReachState.findTypeIdx, ht] using hl
              rw [hfind]; exact hlc
            · unfold isSimplyDeducible
              have hfind : σ₁.findTypeIdx R = some rIdx := by
                simpa [ReachState.findTypeIdx, ht] using hr
              rw [hfind]; exact hrc
        · exact h2
      · exact h2

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
        exact h.discoverDualAt (w := .eta) hti
          (fun hold => .expEta
            (h.old rIdx Ret hR (by simpa [ReachCell.oldDeducible] using hold)) trivial)
          (fun hnew => .expEta (h.new rIdx Ret hR hnew))
          (fun _ _ _ heq => by cases heq)
          (by simp [Witness.fits])
          (fun hneu => by simp [Witness.isNeutral] at hneu)
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
          refine h.discoverDualAt_not_eta (w := .appTy ti aIdx) hR ?_ ?_ (fun h => by cases h)
              (by simp [Witness.fits]) (fun _ => ⟨Arg, Ret, hti, hA, rfl⟩)
          · intro hold
            obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hold
            exact .appTy
              (h.old ti _ hti (by simpa [ReachCell.oldDeducible] using h1))
              (h.old aIdx Arg hA (by simpa [ReachCell.oldDeducible] using h2)) trivial
          · intro hnew
            cases hu : (σ.getCell ti).usesNew
            · have han : (σ.getCell aIdx).usesNew = true := by
                simp [hu, Bool.or_eq_true_iff] at hnew
                exact hnew
              exact .appTyArg (h.deducible ti _ hti hfdec) (h.new aIdx Arg hA han)
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
          exact h.discoverDualAt_not_eta (w := .inl lIdx) hti
            (fun hold => .inl
              (h.old lIdx L hL (by simpa [ReachCell.oldDeducible] using hold)) trivial)
            (fun hnew => .inl (h.new lIdx L hL hnew))
            (fun h => by cases h) (by simp [Witness.fits])
            (fun hneu => by simp [Witness.isNeutral] at hneu)
        · split
          · rename_i hrc
            have hR : σ.typeAt rIdx = some R := ReachState.typeAt_of_findTypeIdx hr
            exact h.discoverDualAt_not_eta (w := .inr rIdx) hti
              (fun hold => .inr
                (h.old rIdx R hR (by simpa [ReachCell.oldDeducible] using hold)) trivial)
              (fun hnew => .inr (h.new rIdx R hR hnew))
              (fun h => by cases h) (by simp [Witness.fits])
              (fun hneu => by simp [Witness.isNeutral] at hneu)
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i A _ hs; rw [hcell i] at hs; simp at hs
  · intro i A _ hs; rw [hcell i] at hs; simp at hs
  · intro i A _ hs; rw [hcell i] at hs; simp at hs
  · intro i hs; rw [hcell i] at hs; simp at hs
  · intro i _ hs; rw [hcell i] at hs; simp [ReachCell.simplyDeducible] at hs
  · intro hs; rw [hinc] at hs; simp at hs
  · intro i L R _ hetaW; rw [hcell i] at hetaW; simp at hetaW
  · intro i A w _ hwit; rw [hcell i] at hwit; simp at hwit
  · intro i A w _ hwit _; rw [hcell i] at hwit; simp at hwit

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
