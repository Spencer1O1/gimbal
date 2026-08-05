/-
  Scherer-core strong positive retrieval and restricted cut (S3).

  `StrongPos` is the exact ledger judgment: only `negVar`, `atomVar`, `inl`,
  `inr`. No zero, no arbitrary application/projection, and no invertible proof
  beneath a shift.

  Executable retrieval decides the judgment. `strong_cut` peels a matching
  invertible pending-head using the pattern, yielding a strict focused
  subderivation (needed later for empty-consistency / saturation). This is not
  general focused substitution closure.
-/

import Gimbal.Equality.Scherer.Focused

deriving instance DecidableEq for Gimbal.Equality.Pos, Gimbal.Equality.Neg

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

deriving instance DecidableEq for StableTy

/-! ### Strong positive patterns -/

/--
Strong positive retrievability (ledger §5).

Strictly weaker than a positive neutral: variables and injections only.
-/
inductive StrongPos : StableCtx sig → Pos sig.nBases → Type where
  | negVar {Γ N} : StableVar Γ (.neg N) → StrongPos Γ (.shift N)
  | atomVar {Γ q} : StableVar Γ (.atom q) → StrongPos Γ (.atom q)
  | inl {Γ P Q} : StrongPos Γ P → StrongPos Γ (.sum P Q)
  | inr {Γ P Q} : StrongPos Γ Q → StrongPos Γ (.sum P Q)

/-! ### Context search helpers -/

namespace StableCtx

/-- Leftmost (oldest) stable variable of the given stable kind, if any. -/
def findVar? : (Γ : StableCtx sig) → (S : StableTy sig.nBases) →
    Option (StableVar Γ S)
  | .empty, _ => none
  | .snoc Γ S', S =>
      if h : S' = S then
        some (h ▸ StableVar.here (Γ := Γ) (S := S'))
      else
        (findVar? Γ S).map StableVar.there

theorem findVar?_isSome_of_var {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (x : StableVar Γ S) : (Γ.findVar? S).isSome = true := by
  induction x with
  | here => simp [findVar?]
  | there y ih =>
      simp only [findVar?]
      split
      · simp
      · simpa using ih

theorem findVar?_eq_none_not_var {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (h : Γ.findVar? S = none) (x : StableVar Γ S) : False := by
  have := findVar?_isSome_of_var x
  simp [h] at this

end StableCtx

/-! ### Executable retrieval -/

/--
Canonical strong retrieval attempt.

For sums, prefer `inl` then `inr`. Never invents a zero pattern or a shift from
an invertible derivation.
-/
def strongRetrieve? (Γ : StableCtx sig) : (P : Pos sig.nBases) → Option (StrongPos Γ P)
  | .atom q => (Γ.findVar? (.atom q)).map StrongPos.atomVar
  | .zero => none
  | .sum A B =>
      match strongRetrieve? Γ A with
      | some sp => some (.inl sp)
      | none => (strongRetrieve? Γ B).map .inr
  | .shift N => (Γ.findVar? (.neg N)).map StrongPos.negVar

/-- Boolean decision for strong retrievability. -/
def stronglyRetrievable (Γ : StableCtx sig) (P : Pos sig.nBases) : Bool :=
  (strongRetrieve? Γ P).isSome

/-- Every inhabited `StrongPos` is detected by retrieval. -/
theorem strongRetrieve?_isSome_of {Γ : StableCtx sig} {P : Pos sig.nBases}
    (sp : StrongPos Γ P) : (strongRetrieve? Γ P).isSome = true := by
  induction sp with
  | negVar x =>
      simpa [strongRetrieve?] using StableCtx.findVar?_isSome_of_var x
  | atomVar x =>
      simpa [strongRetrieve?] using StableCtx.findVar?_isSome_of_var x
  | inl _ ih =>
      simp only [strongRetrieve?]
      cases h : strongRetrieve? _ _ with
      | some _ => simp
      | none => simp [h] at ih
  | inr sp ih =>
      simp only [strongRetrieve?]
      cases hA : strongRetrieve? _ _ with
      | some _ => simp
      | none => simpa [hA] using ih

private theorem strongRetrieve?_isSome_imp {Γ : StableCtx sig} :
    ∀ {P : Pos sig.nBases}, (strongRetrieve? Γ P).isSome = true →
      Nonempty (StrongPos Γ P)
  | .atom q, h => by
      simp only [strongRetrieve?] at h
      cases hx : Γ.findVar? (.atom q) with
      | none => simp [hx] at h
      | some x => exact ⟨.atomVar x⟩
  | .zero, h => by simp [strongRetrieve?] at h
  | .sum A B, h => by
      simp only [strongRetrieve?] at h
      cases hA : strongRetrieve? Γ A with
      | some spA => exact ⟨.inl spA⟩
      | none =>
          cases hB : strongRetrieve? Γ B with
          | some spB => exact ⟨.inr spB⟩
          | none => simp [hA, hB] at h
  | .shift N, h => by
      simp only [strongRetrieve?] at h
      cases hx : Γ.findVar? (.neg N) with
      | none => simp [hx] at h
      | some x => exact ⟨.negVar x⟩

/-- Retrieval option is inhabited exactly when `StrongPos` is. -/
theorem strongRetrieve?_isSome_iff {Γ : StableCtx sig} {P : Pos sig.nBases} :
    (strongRetrieve? Γ P).isSome = true ↔ Nonempty (StrongPos Γ P) :=
  ⟨strongRetrieve?_isSome_imp, fun ⟨sp⟩ => strongRetrieve?_isSome_of sp⟩

/-- Boolean decision is faithful. -/
theorem stronglyRetrievable_iff {Γ : StableCtx sig} {P : Pos sig.nBases} :
    stronglyRetrievable Γ P = true ↔ Nonempty (StrongPos Γ P) := by
  simpa [stronglyRetrievable] using strongRetrieve?_isSome_iff (Γ := Γ) (P := P)

/-- Soundness of the executable decision procedure. -/
theorem stronglyRetrievable_sound {Γ : StableCtx sig} {P : Pos sig.nBases}
    (h : stronglyRetrievable Γ P = true) : Nonempty (StrongPos Γ P) :=
  stronglyRetrievable_iff.mp h

instance (Γ : StableCtx sig) (P : Pos sig.nBases) :
    Decidable (Nonempty (StrongPos Γ P)) :=
  decidable_of_bool (stronglyRetrievable Γ P) stronglyRetrievable_iff

/-- Canonical retrieved witness when one exists. -/
def getStrongPos (Γ : StableCtx sig) (P : Pos sig.nBases)
    (h : stronglyRetrievable Γ P = true) : StrongPos Γ P :=
  match hs : strongRetrieve? Γ P with
  | some sp => sp
  | none =>
      False.elim <| by
        have := congrArg Option.isSome hs
        simp [stronglyRetrievable, hs] at h

/-! ### Strict focused subderivations -/

/-- Structural size of an ordinary invertible derivation. -/
def invSize {Γ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases} :
    Inv Γ ps G → Nat
  | .caseSum l r => invSize l + invSize r + 1
  | .abort => 1
  | .storeAtom t => invSize t + 1
  | .storeShift t => invSize t + 1
  | .unit => 1
  | .pair t u => invSize t + invSize u + 1
  | .lam t => invSize t + 1
  | .focusShift _ => 1
  | .focusPos _ => 1

/--
Immediate premise of an ordinary invertible derivation (one constructor step).
-/
inductive InvImmediateSub (sig : Signature) :
    ∀ {Γ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
      {Γ' : StableCtx sig} {ps' : Pending sig} {G' : Goal sig.nBases},
      Inv Γ' ps' G' → Inv Γ ps G → Prop where
  | caseSum_left {Γ : StableCtx sig} {A B : Pos sig.nBases} {ps : Pending sig}
      {G : Goal sig.nBases}
      (l : Inv Γ (.cons A ps) G) (r : Inv Γ (.cons B ps) G) :
      InvImmediateSub sig l (.caseSum l r)
  | caseSum_right {Γ : StableCtx sig} {A B : Pos sig.nBases} {ps : Pending sig}
      {G : Goal sig.nBases}
      (l : Inv Γ (.cons A ps) G) (r : Inv Γ (.cons B ps) G) :
      InvImmediateSub sig r (.caseSum l r)
  | storeAtom {Γ : StableCtx sig} {q : Fin sig.nBases} {ps : Pending sig}
      {G : Goal sig.nBases}
      (t : Inv (Γ.snoc (.atom q)) ps G) :
      InvImmediateSub sig t (.storeAtom t)
  | storeShift {Γ : StableCtx sig} {N : Neg sig.nBases} {ps : Pending sig}
      {G : Goal sig.nBases}
      (t : Inv (Γ.snoc (.neg N)) ps G) :
      InvImmediateSub sig t (.storeShift t)
  | pair_left {Γ : StableCtx sig} {A B : Neg sig.nBases}
      (t : Inv Γ .empty (.neg A)) (u : Inv Γ .empty (.neg B)) :
      InvImmediateSub sig t (.pair t u)
  | pair_right {Γ : StableCtx sig} {A B : Neg sig.nBases}
      (t : Inv Γ .empty (.neg A)) (u : Inv Γ .empty (.neg B)) :
      InvImmediateSub sig u (.pair t u)
  | lam {Γ : StableCtx sig} {A : Pos sig.nBases} {B : Neg sig.nBases}
      (t : Inv Γ (.cons A .empty) (.neg B)) :
      InvImmediateSub sig t (.lam t)

/-- Transitive closure of immediate invertible premises. -/
inductive StrictFocusedSubderivation (sig : Signature) :
    ∀ {Γ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
      {Γ' : StableCtx sig} {ps' : Pending sig} {G' : Goal sig.nBases},
      Inv Γ' ps' G' → Inv Γ ps G → Prop where
  | imm {Γ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
      {Γ' : StableCtx sig} {ps' : Pending sig} {G' : Goal sig.nBases}
      {d' : Inv Γ' ps' G'} {d : Inv Γ ps G}
      (h : InvImmediateSub sig d' d) :
      StrictFocusedSubderivation sig d' d
  | step {Γ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
      {Γ₁ : StableCtx sig} {ps₁ : Pending sig} {G₁ : Goal sig.nBases}
      {Γ' : StableCtx sig} {ps' : Pending sig} {G' : Goal sig.nBases}
      {d₁ : Inv Γ₁ ps₁ G₁} {d : Inv Γ ps G} {d' : Inv Γ' ps' G'}
      (h₁ : InvImmediateSub sig d₁ d)
      (h₂ : StrictFocusedSubderivation sig d' d₁) :
      StrictFocusedSubderivation sig d' d

theorem invImmediateSub_size_lt {Γ : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} {Γ' : StableCtx sig} {ps' : Pending sig}
    {G' : Goal sig.nBases} {d' : Inv Γ' ps' G'} {d : Inv Γ ps G}
    (h : InvImmediateSub sig d' d) : invSize d' < invSize d := by
  cases h <;> simp only [invSize] <;> omega

theorem strictFocusedSubderivation_size_lt {Γ : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} {Γ' : StableCtx sig} {ps' : Pending sig}
    {G' : Goal sig.nBases} {d' : Inv Γ' ps' G'} {d : Inv Γ ps G}
    (h : StrictFocusedSubderivation sig d' d) : invSize d' < invSize d := by
  induction h with
  | imm h => exact invImmediateSub_size_lt h
  | step h₁ _ ih => exact Nat.lt_trans ih (invImmediateSub_size_lt h₁)

/-! ### Restricted strong-positive cut -/

/--
One strong-cut computation against a pending-head formula.

- injections force the matching `caseSum` branch (and may recurse);
- atom/shift patterns peel the corresponding `store*`.

Does **not** perform hereditary substitution or close under arbitrary focusing.
-/
def strongCut {Γ : StableCtx sig} {P : Pos sig.nBases} {ps : Pending sig}
    {G : Goal sig.nBases} :
    StrongPos Γ P → Inv Γ (.cons P ps) G →
      (Γ' : StableCtx sig) × (ps' : Pending sig) × Inv Γ' ps' G
  | .inl (P := A) (Q := B) sp, d =>
      strongCut sp (Inv.asCaseSum (A := A) (B := B) (ps := ps) (G := G) d).1
  | .inr (P := A) (Q := B) sp, d =>
      strongCut sp (Inv.asCaseSum (A := A) (B := B) (ps := ps) (G := G) d).2
  | .atomVar (q := q) _, d =>
      ⟨Γ.snoc (.atom q), ps, Inv.asStoreAtom (q := q) (ps := ps) (G := G) d⟩
  | .negVar (N := N) _, d =>
      ⟨Γ.snoc (.neg N), ps, Inv.asStoreShift (N := N) (ps := ps) (G := G) d⟩

private theorem strongCut_inl_imm {Γ : StableCtx sig}
    {A B : Pos sig.nBases} {ps : Pending sig} {G : Goal sig.nBases}
    (d : Inv Γ (.cons (.sum A B) ps) G) :
    InvImmediateSub sig (Inv.asCaseSum d).1 d := by
  cases d with | caseSum l r => exact .caseSum_left l r

private theorem strongCut_inr_imm {Γ : StableCtx sig}
    {A B : Pos sig.nBases} {ps : Pending sig} {G : Goal sig.nBases}
    (d : Inv Γ (.cons (.sum A B) ps) G) :
    InvImmediateSub sig (Inv.asCaseSum d).2 d := by
  cases d with | caseSum l r => exact .caseSum_right l r

private theorem strongCut_atom_imm {Γ : StableCtx sig} {q : Fin sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    (d : Inv Γ (.cons (.atom q) ps) G) :
    InvImmediateSub sig (Inv.asStoreAtom d) d := by
  cases d with | storeAtom t => exact .storeAtom t

private theorem strongCut_shift_imm {Γ : StableCtx sig} {N : Neg sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    (d : Inv Γ (.cons (.shift N) ps) G) :
    InvImmediateSub sig (Inv.asStoreShift d) d := by
  cases d with | storeShift t => exact .storeShift t

/--
Ledger `strong_cut`: cutting a strong pattern into an invertible pending head
yields a strict focused subderivation.
-/
theorem strong_cut {Γ : StableCtx sig} {P : Pos sig.nBases} {ps : Pending sig}
    {G : Goal sig.nBases} (sp : StrongPos Γ P) (d : Inv Γ (.cons P ps) G) :
    ∃ (Γ' : StableCtx sig) (ps' : Pending sig) (d' : Inv Γ' ps' G),
      StrictFocusedSubderivation sig d' d := by
  induction sp generalizing ps with
  | negVar x =>
      exact ⟨Γ.snoc (.neg _), ps, Inv.asStoreShift d, .imm (strongCut_shift_imm d)⟩
  | atomVar x =>
      exact ⟨Γ.snoc (.atom _), ps, Inv.asStoreAtom d, .imm (strongCut_atom_imm d)⟩
  | inl sp ih =>
      obtain ⟨Γ', ps', d', hs⟩ := ih (Inv.asCaseSum d).1
      exact ⟨Γ', ps', d', .step (strongCut_inl_imm d) hs⟩
  | inr sp ih =>
      obtain ⟨Γ', ps', d', hs⟩ := ih (Inv.asCaseSum d).2
      exact ⟨Γ', ps', d', .step (strongCut_inr_imm d) hs⟩

/-- Computational cut produces a strict subderivation. -/
theorem strongCut_strict {Γ : StableCtx sig} {P : Pos sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    (sp : StrongPos Γ P) (d : Inv Γ (.cons P ps) G) :
    StrictFocusedSubderivation sig (strongCut sp d).2.2 d := by
  induction sp generalizing ps with
  | negVar x =>
      simpa [strongCut] using StrictFocusedSubderivation.imm (strongCut_shift_imm d)
  | atomVar x =>
      simpa [strongCut] using StrictFocusedSubderivation.imm (strongCut_atom_imm d)
  | inl sp ih =>
      simpa [strongCut] using
        StrictFocusedSubderivation.step (strongCut_inl_imm d) (ih _)
  | inr sp ih =>
      simpa [strongCut] using
        StrictFocusedSubderivation.step (strongCut_inr_imm d) (ih _)

/-- Computational cut strictly decreases `invSize`. -/
theorem strongCut_size_lt {Γ : StableCtx sig} {P : Pos sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    (sp : StrongPos Γ P) (d : Inv Γ (.cons P ps) G) :
    invSize (strongCut sp d).2.2 < invSize d :=
  strictFocusedSubderivation_size_lt (strongCut_strict sp d)

/-- Witness package for later saturation / empty-consistency callers. -/
structure StrongCutResult {Γ : StableCtx sig} {P : Pos sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    (sp : StrongPos Γ P) (d : Inv Γ (.cons P ps) G) where
  Γ' : StableCtx sig
  ps' : Pending sig
  d' : Inv Γ' ps' G
  strict : StrictFocusedSubderivation sig d' d

def strongCutResult {Γ : StableCtx sig} {P : Pos sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases}
    (sp : StrongPos Γ P) (d : Inv Γ (.cons P ps) G) : StrongCutResult sp d where
  Γ' := (strongCut sp d).1
  ps' := (strongCut sp d).2.1
  d' := (strongCut sp d).2.2
  strict := strongCut_strict sp d

/-! ### Fixtures -/

namespace StrongRetrievalFixtures

def sig0 : Signature := ⟨0, #[]⟩
def sig1 : Signature := ⟨1, #[]⟩

/-- Atom is strongly retrievable from an atom hypothesis. -/
def strong_atom :
    StrongPos (sig := sig1)
      (StableCtx.snoc .empty (.atom ⟨0, Nat.zero_lt_one⟩))
      (.atom ⟨0, Nat.zero_lt_one⟩) :=
  .atomVar .here

theorem strongRetrieve_atom :
    stronglyRetrievable (sig := sig1)
      (StableCtx.snoc .empty (.atom ⟨0, Nat.zero_lt_one⟩))
      (.atom ⟨0, Nat.zero_lt_one⟩) = true :=
  rfl

/-- Zero is never strongly retrievable. -/
theorem strongRetrieve_zero_false :
    stronglyRetrievable (sig := sig0) .empty (.zero : Pos 0) = false :=
  rfl

/-- Injection into a sum from an atom. -/
def strong_inl_atom :
    StrongPos (sig := sig1)
      (StableCtx.snoc .empty (.atom ⟨0, Nat.zero_lt_one⟩))
      (.sum (.atom ⟨0, Nat.zero_lt_one⟩) (.atom ⟨0, Nat.zero_lt_one⟩)) :=
  .inl strong_atom

theorem strongRetrieve_sum_inl :
    stronglyRetrievable (sig := sig1)
      (StableCtx.snoc .empty (.atom ⟨0, Nat.zero_lt_one⟩))
      (.sum (.atom ⟨0, Nat.zero_lt_one⟩) (.zero : Pos 1)) = true :=
  rfl

/-- Strong cut on `inl` selects into the left `caseSum` branch. -/
theorem strong_cut_inl_example :
    ∃ (Γ' : StableCtx sig1) (ps' : Pending sig1)
      (d' : Inv (sig := sig1) Γ' ps' (.neg .one)),
      StrictFocusedSubderivation sig1 d'
        (show Inv (sig := sig1)
            (StableCtx.snoc .empty (.atom ⟨0, Nat.zero_lt_one⟩))
            (.cons (.sum (.atom ⟨0, Nat.zero_lt_one⟩) (.zero : Pos 1)) .empty)
            (.neg .one) from
          .caseSum (.storeAtom .unit) .abort) :=
  strong_cut (.inl (P := .atom ⟨0, Nat.zero_lt_one⟩) (Q := .zero) strong_atom)
    (.caseSum (.storeAtom .unit)
      (.abort :
        Inv (sig := sig1)
          (StableCtx.snoc .empty (.atom ⟨0, Nat.zero_lt_one⟩))
          (.cons .zero .empty) (.neg .one)))

end StrongRetrievalFixtures

end Gimbal.Equality.Scherer
