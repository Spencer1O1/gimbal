/-
  Erasure–renaming commutation for Scherer core (S2).

  Ordinary:
    Inv.erase (Inv.rename ρ t) =
      rename (renameEraseAux ρ.erase ps) (Inv.erase t)

  Saturated: erase `StableRename.keepLeft ρ New`, then lift over pending.
-/

import Gimbal.Equality.Scherer.Renaming
import Gimbal.Equality.Scherer.TmAlgebra
namespace Gimbal.Equality.Scherer
variable {sig : Signature}

theorem cast_var_there {Δ : Ctx sig} {S A B : Object sig.nBases}
    (h : A = B) (x : Var Δ B) :
    (h ▸ (Var.there (x) : Var (Δ.snoc S) B) : Var (Δ.snoc S) A) =
      Var.there (h ▸ x : Var Δ A) := by
  cases h; rfl

theorem StableRename.ofEraseVar_there {Γ : StableCtx sig} {S : StableTy sig.nBases}
    {A : Object sig.nBases} (y : Var Γ.erase A) :
    StableRename.ofEraseVar (Γ.snoc S) (Var.there y) =
      (⟨(StableRename.ofEraseVar Γ y).1,
        (StableRename.ofEraseVar Γ y).2.1,
        StableVar.there (StableRename.ofEraseVar Γ y).2.2⟩ :
        (S1 : StableTy sig.nBases) ×' (A = S1.erase) ×' StableVar (Γ.snoc S) S1) :=
  rfl

theorem StableRename.erase_id_apply {Γ : StableCtx sig} {A : Object sig.nBases}
    (x : Var Γ.erase A) :
    StableRename.erase (StableRename.id (Γ := Γ)) x = x := by
  induction Γ generalizing A with
  | empty => exact nomatch x
  | snoc Γ0 S ih =>
      cases x with
      | here => rfl
      | there y =>
          have ihy := ih y
          unfold StableRename.erase StableRename.id
          rw [StableRename.ofEraseVar_there (S := S) y]
          unfold StableRename.erase StableRename.id at ihy
          generalize hp : StableRename.ofEraseVar Γ0 y = p at ihy ⊢
          obtain ⟨S1, h, z⟩ := p
          dsimp only at ihy ⊢
          refine (cast_var_there (S := S.erase) h (StableVar.erase z)).trans ?_
          exact congrArg Var.there ihy

theorem ofEraseVar_erase {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (x : StableVar Γ S) :
    StableRename.ofEraseVar Γ (StableVar.erase x) = ⟨S, rfl, x⟩ := by
  induction x with
  | here => rfl
  | @there Γ0 S0 S' x ih =>
      refine Eq.trans ?_ (congrArg
        (fun p : (S1 : StableTy sig.nBases) ×' (S0.erase = S1.erase) ×' StableVar Γ0 S1 =>
          (⟨p.1, p.2.1, .there p.2.2⟩ :
            (S1 : StableTy sig.nBases) ×' (S0.erase = S1.erase) ×'
              StableVar (Γ0.snoc S') S1))
        ih)
      rfl

theorem StableVar.erase_rename {Γ Δ : StableCtx sig} {S : StableTy sig.nBases}
    (ρ : StableRename Γ Δ) (x : StableVar Γ S) :
    StableVar.erase (ρ x) = StableRename.erase ρ (StableVar.erase x) := by
  unfold StableRename.erase
  rw [ofEraseVar_erase x]

theorem StableRename.erase_ext_apply {Γ Δ : StableCtx sig} {S : StableTy sig.nBases}
    (ρ : StableRename Γ Δ) {A : Object sig.nBases}
    (x : Var (Γ.snoc S).erase A) :
    StableRename.erase (StableRename.ext (S := S) ρ) x =
      Rename.ext (StableRename.erase ρ) x := by
  cases x with
  | here => rfl
  | there y =>
      have key :
          StableRename.erase (StableRename.ext (S := S) ρ) (Var.there y) =
            Var.there (B := S.erase)
              (let ⟨S1, h, z⟩ := StableRename.ofEraseVar Γ y
               (h ▸ StableVar.erase (ρ z) : Var Δ.erase A)) := by
        unfold StableRename.erase
        rw [StableRename.ofEraseVar_there (S := S) y]
        generalize hp : StableRename.ofEraseVar Γ y = p
        obtain ⟨S1, h, z⟩ := p
        dsimp only [StableRename.ext]
        exact cast_var_there (S := S.erase) h (StableVar.erase (ρ z))
      exact key.trans (congrArg (Var.there (B := S.erase)) rfl)

theorem StableRename.erase_comp_apply {Γ Δ Ε : StableCtx sig}
    (ρ : StableRename Δ Ε) (τ : StableRename Γ Δ) {A : Object sig.nBases}
    (x : Var Γ.erase A) :
    StableRename.erase (StableRename.comp ρ τ) x =
      Rename.comp (StableRename.erase ρ) (StableRename.erase τ) x := by
  change
    (let ⟨S1, h, y⟩ := StableRename.ofEraseVar Γ x
     (h ▸ StableVar.erase (ρ (τ y)) : Var Ε.erase A)) =
      StableRename.erase ρ
        (let ⟨S1, h, y⟩ := StableRename.ofEraseVar Γ x
         (h ▸ StableVar.erase (τ y) : Var Δ.erase A))
  generalize hp : StableRename.ofEraseVar Γ x = p
  obtain ⟨S1, h, y⟩ := p
  dsimp only
  refine Eq.trans
    (congrArg (fun z : Var Ε.erase S1.erase => (h ▸ z : Var Ε.erase A))
      (StableVar.erase_rename ρ (τ y))) ?_
  cases h
  rfl

theorem StableRename.erase_weaken_apply {Γ : StableCtx sig} {S : StableTy sig.nBases}
    {A : Object sig.nBases} (x : Var Γ.erase A) :
    StableRename.erase (StableRename.weaken (Γ := Γ) (S := S)) x =
      Rename.weaken (Γ := Γ.erase) (A := S.erase) x := by
  unfold StableRename.erase StableRename.weaken
  have hid := StableRename.erase_id_apply (Γ := Γ) x
  unfold StableRename.erase StableRename.id at hid
  generalize hp : StableRename.ofEraseVar Γ x = p at hid ⊢
  obtain ⟨S1, h, y⟩ := p
  dsimp only at hid ⊢
  refine (cast_var_there (S := S.erase) h (StableVar.erase y)).trans ?_
  exact congrArg (Var.there (B := S.erase)) hid

theorem Rename.exchange_ext_apply {Γ Δ : Ctx sig} {A B C : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (x : Var (Γ ▻ A ▻ B) C) :
    Rename.ext (Rename.ext ρ) (Rename.exchange (A := A) (B := B) x) =
      Rename.exchange (A := A) (B := B) (Rename.ext (Rename.ext ρ) x) := by
  cases x with
  | here => rfl
  | there x =>
      cases x with
      | here => rfl
      | there _ => rfl

private theorem rename_ext_pw {Γ Δ : Ctx sig} {A : Object sig.nBases}
    {ρ τ : Rename sig Γ Δ}
    (h : ∀ {B : Object sig.nBases} (x : Var Γ B), ρ x = τ x)
    {B : Object sig.nBases} (x : Var (Γ ▻ A) B) :
    Rename.ext ρ x = Rename.ext τ x := by
  cases x with
  | here => rfl
  | there y => exact congrArg Var.there (h y)

theorem renameEraseAux_eq_of_pointwise {Γ Δ : Ctx sig}
    {ρ τ : Rename sig Γ Δ}
    (h : ∀ {A : Object sig.nBases} (x : Var Γ A), ρ x = τ x)
    (ps : Pending sig) {A : Object sig.nBases}
    (x : Var (Pending.eraseAux ps Γ) A) :
    renameEraseAux ρ ps x = renameEraseAux τ ps x := by
  induction ps generalizing Γ Δ with
  | empty => exact h x
  | cons Q qs ih => exact ih (fun {B} y => rename_ext_pw h y) x

theorem renameEraseAux_comp_apply {Γ Δ Ε : Ctx sig}
    (ρ : Rename sig Δ Ε) (τ : Rename sig Γ Δ) (ps : Pending sig)
    {A : Object sig.nBases} (x : Var (Pending.eraseAux ps Γ) A) :
    renameEraseAux (Rename.comp ρ τ) ps x =
      Rename.comp (renameEraseAux ρ ps) (renameEraseAux τ ps) x := by
  induction ps generalizing Γ Δ Ε A with
  | empty => rfl
  | cons Q qs ih =>
      change renameEraseAux (Rename.ext (Rename.comp ρ τ)) qs x =
        Rename.comp (renameEraseAux (Rename.ext ρ) qs)
          (renameEraseAux (Rename.ext τ) qs) x
      refine Eq.trans
        (renameEraseAux_eq_of_pointwise (Rename.ext_comp_apply (A := Q.erase) ρ τ) qs x)
        (ih (Rename.ext ρ) (Rename.ext τ) x)

theorem rotateNewestToHead_nat_apply {Γ Δ : Ctx sig} {A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (ps : Pending sig) {B : Object sig.nBases}
    (x : Var ((Pending.eraseAux ps Γ).snoc A) B) :
    Rename.comp (renameEraseAux (Rename.ext ρ) ps)
        (rotateNewestToHead (Δ := Γ) (A := A) ps) x =
      Rename.comp (rotateNewestToHead (Δ := Δ) (A := A) ps)
        (Rename.ext (renameEraseAux ρ ps)) x := by
  induction ps generalizing Γ Δ B with
  | empty => rfl
  | cons Q qs ih =>
      change
        Rename.comp (renameEraseAux (Rename.ext (Rename.ext ρ)) qs)
            (Rename.comp
              (renameEraseAux (Rename.exchange (Γ := Γ) (A := Q.erase) (B := A)) qs)
              (rotateNewestToHead (Δ := Γ.snoc Q.erase) (A := A) qs)) x =
          Rename.comp
            (Rename.comp
              (renameEraseAux (Rename.exchange (Γ := Δ) (A := Q.erase) (B := A)) qs)
              (rotateNewestToHead (Δ := Δ.snoc Q.erase) (A := A) qs))
            (Rename.ext (renameEraseAux (Rename.ext ρ) qs)) x
      have lhs_assoc :
          Rename.comp (renameEraseAux (Rename.ext (Rename.ext ρ)) qs)
              (Rename.comp
                (renameEraseAux (Rename.exchange (Γ := Γ) (A := Q.erase) (B := A)) qs)
                (rotateNewestToHead (Δ := Γ.snoc Q.erase) (A := A) qs)) x =
            renameEraseAux
              (Rename.comp (Rename.ext (Rename.ext ρ))
                (Rename.exchange (Γ := Γ) (A := Q.erase) (B := A))) qs
              (rotateNewestToHead (Δ := Γ.snoc Q.erase) (A := A) qs x) :=
        (renameEraseAux_comp_apply
          (Rename.ext (Rename.ext ρ))
          (Rename.exchange (Γ := Γ) (A := Q.erase) (B := A)) qs _).symm
      refine lhs_assoc.trans ?_
      have hex_pw : ∀ {C : Object sig.nBases} (z : Var (Γ ▻ Q.erase ▻ A) C),
          Rename.comp (Rename.ext (Rename.ext ρ))
              (Rename.exchange (Γ := Γ) (A := Q.erase) (B := A)) z =
            Rename.comp (Rename.exchange (Γ := Δ) (A := Q.erase) (B := A))
              (Rename.ext (Rename.ext ρ)) z :=
        fun {C} z => Rename.exchange_ext_apply ρ z
      refine Eq.trans (renameEraseAux_eq_of_pointwise hex_pw qs _) ?_
      refine Eq.trans (renameEraseAux_comp_apply
          (Rename.exchange (Γ := Δ) (A := Q.erase) (B := A))
          (Rename.ext (Rename.ext ρ)) qs _) ?_
      change
        renameEraseAux (Rename.exchange (Γ := Δ) (A := Q.erase) (B := A)) qs
            (renameEraseAux (Rename.ext (Rename.ext ρ)) qs
              (rotateNewestToHead (Δ := Γ.snoc Q.erase) (A := A) qs x)) =
          renameEraseAux (Rename.exchange (Γ := Δ) (A := Q.erase) (B := A)) qs
            (rotateNewestToHead (Δ := Δ.snoc Q.erase) (A := A) qs
              (Rename.ext (renameEraseAux (Rename.ext ρ) qs) x))
      exact congrArg
        (renameEraseAux (Rename.exchange (Γ := Δ) (A := Q.erase) (B := A)) qs)
        (ih (Rename.ext ρ) x)

theorem rotateHeadToNewest_nat_apply {Γ Δ : Ctx sig} {H : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (ps : Pending sig) {B : Object sig.nBases}
    (x : Var (Pending.eraseAux ps (Γ.snoc H)) B) :
    Rename.comp (Rename.ext (renameEraseAux ρ ps))
        (rotateHeadToNewest (Δ := Γ) (H := H) ps) x =
      Rename.comp (rotateHeadToNewest (Δ := Δ) (H := H) ps)
        (renameEraseAux (Rename.ext ρ) ps) x := by
  induction ps generalizing Γ Δ B with
  | empty => rfl
  | cons Q qs ih =>
      change
        Rename.comp (Rename.ext (renameEraseAux (Rename.ext ρ) qs))
            (Rename.comp
              (rotateHeadToNewest (Δ := Γ.snoc Q.erase) (H := H) qs)
              (renameEraseAux (Rename.exchange (Γ := Γ) (A := H) (B := Q.erase)) qs)) x =
          Rename.comp
            (Rename.comp
              (rotateHeadToNewest (Δ := Δ.snoc Q.erase) (H := H) qs)
              (renameEraseAux (Rename.exchange (Γ := Δ) (A := H) (B := Q.erase)) qs))
            (renameEraseAux (Rename.ext (Rename.ext ρ)) qs) x
      have step :
          Rename.comp (Rename.ext (renameEraseAux (Rename.ext ρ) qs))
              (rotateHeadToNewest (Δ := Γ.snoc Q.erase) (H := H) qs)
              (renameEraseAux (Rename.exchange (Γ := Γ) (A := H) (B := Q.erase)) qs x) =
            Rename.comp (rotateHeadToNewest (Δ := Δ.snoc Q.erase) (H := H) qs)
              (renameEraseAux (Rename.ext (Rename.ext ρ)) qs)
              (renameEraseAux (Rename.exchange (Γ := Γ) (A := H) (B := Q.erase)) qs x) :=
        ih (Rename.ext ρ) _
      refine Eq.trans step ?_
      have hex_pw : ∀ {C : Object sig.nBases} (z : Var (Γ ▻ H ▻ Q.erase) C),
          Rename.comp (Rename.ext (Rename.ext ρ))
              (Rename.exchange (Γ := Γ) (A := H) (B := Q.erase)) z =
            Rename.comp (Rename.exchange (Γ := Δ) (A := H) (B := Q.erase))
              (Rename.ext (Rename.ext ρ)) z :=
        fun {C} z => Rename.exchange_ext_apply ρ z
      change
        rotateHeadToNewest (Δ := Δ.snoc Q.erase) (H := H) qs
            (renameEraseAux (Rename.ext (Rename.ext ρ)) qs
              (renameEraseAux (Rename.exchange (Γ := Γ) (A := H) (B := Q.erase)) qs x)) =
          rotateHeadToNewest (Δ := Δ.snoc Q.erase) (H := H) qs
            (renameEraseAux (Rename.exchange (Γ := Δ) (A := H) (B := Q.erase)) qs
              (renameEraseAux (Rename.ext (Rename.ext ρ)) qs x))
      refine congrArg (rotateHeadToNewest (Δ := Δ.snoc Q.erase) (H := H) qs) ?_
      refine Eq.trans (renameEraseAux_comp_apply
          (Rename.ext (Rename.ext ρ))
          (Rename.exchange (Γ := Γ) (A := H) (B := Q.erase)) qs _).symm ?_
      refine Eq.trans (renameEraseAux_eq_of_pointwise hex_pw qs _) ?_
      exact renameEraseAux_comp_apply
        (Rename.exchange (Γ := Δ) (A := H) (B := Q.erase))
        (Rename.ext (Rename.ext ρ)) qs _

theorem Rename.skip1_ext_apply {Γ Δ : Ctx sig} {A B C : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (x : Var (Γ ▻ A) C) :
    Rename.ext (Rename.ext ρ) (Rename.skip1 (B := B) x) =
      Rename.skip1 (B := B) (Rename.ext ρ x) := by
  cases x with
  | here => rfl
  | there _ => rfl

theorem pendingHeadVar_nat_apply {Γ Δ : Ctx sig} {H : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (ps : Pending sig) :
    renameEraseAux (Rename.ext ρ) ps (pendingHeadVar (Δ := Γ) (H := H) ps) =
      pendingHeadVar (Δ := Δ) (H := H) ps := by
  induction ps generalizing Γ Δ with
  | empty => rfl
  | cons Q qs ih =>
      change
        renameEraseAux (Rename.ext (Rename.ext ρ)) qs
            (renameEraseAux (Rename.exchange (Γ := Γ) (A := Q.erase) (B := H)) qs
              (pendingHeadVar (Δ := Γ.snoc Q.erase) (H := H) qs)) =
          renameEraseAux (Rename.exchange (Γ := Δ) (A := Q.erase) (B := H)) qs
            (pendingHeadVar (Δ := Δ.snoc Q.erase) (H := H) qs)
      refine Eq.trans (renameEraseAux_comp_apply
          (Rename.ext (Rename.ext ρ))
          (Rename.exchange (Γ := Γ) (A := Q.erase) (B := H)) qs _).symm ?_
      have hex_pw : ∀ {C : Object sig.nBases} (z : Var (Γ ▻ Q.erase ▻ H) C),
          Rename.comp (Rename.ext (Rename.ext ρ))
              (Rename.exchange (Γ := Γ) (A := Q.erase) (B := H)) z =
            Rename.comp (Rename.exchange (Γ := Δ) (A := Q.erase) (B := H))
              (Rename.ext (Rename.ext ρ)) z :=
        fun {C} z => Rename.exchange_ext_apply ρ z
      refine Eq.trans (renameEraseAux_eq_of_pointwise hex_pw qs _) ?_
      refine Eq.trans (renameEraseAux_comp_apply
          (Rename.exchange (Γ := Δ) (A := Q.erase) (B := H))
          (Rename.ext (Rename.ext ρ)) qs _) ?_
      exact congrArg
        (renameEraseAux (Rename.exchange (Γ := Δ) (A := Q.erase) (B := H)) qs)
        (ih (Rename.ext ρ))


/-- `subst0` after renaming (from TmAlgebra). -/
theorem subst0_rename {Γ Δ : Ctx sig} {A B : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (t : Tm (Γ.snoc A) B) (n : Tm Γ A) :
    subst0 (rename (Rename.ext ρ) t) (rename ρ n) =
      rename ρ (subst0 t n) :=
  (rename_subst0 ρ t n).symm

/-! ### Ordinary erase–rename -/

private theorem case_branch_comm {Γ Δ : Ctx sig} {A H C : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (ps : Pending sig)
    (t : Tm (Pending.eraseAux ps (Γ.snoc A)) C) :
    rename (Rename.skip1 (Γ := Pending.eraseAux ps Δ) (A := A) (B := H))
        (rename (rotateHeadToNewest (Δ := Δ) (H := A) ps)
          (rename (renameEraseAux (Rename.ext ρ) ps) t)) =
      rename (Rename.ext (Rename.ext (renameEraseAux ρ ps)))
        (rename (Rename.skip1 (Γ := Pending.eraseAux ps Γ) (A := A) (B := H))
          (rename (rotateHeadToNewest (Δ := Γ) (H := A) ps) t)) := by
  have h1 :
      rename (rotateHeadToNewest (Δ := Δ) (H := A) ps)
          (rename (renameEraseAux (Rename.ext ρ) ps) t) =
        rename (Rename.ext (renameEraseAux ρ ps))
          (rename (rotateHeadToNewest (Δ := Γ) (H := A) ps) t) := by
    rw [rename_comp (rotateHeadToNewest (Δ := Δ) (H := A) ps)
        (renameEraseAux (Rename.ext ρ) ps) t,
        rename_comp (Rename.ext (renameEraseAux ρ ps))
        (rotateHeadToNewest (Δ := Γ) (H := A) ps) t]
    exact rename_eq_of_pointwise
      (fun {B} x => (rotateHeadToNewest_nat_apply ρ ps x).symm) t
  rw [h1]
  rw [rename_comp (Rename.skip1 (Γ := Pending.eraseAux ps Δ) (A := A) (B := H))
      (Rename.ext (renameEraseAux ρ ps))
      (rename (rotateHeadToNewest (Δ := Γ) (H := A) ps) t),
      rename_comp (Rename.ext (Rename.ext (renameEraseAux ρ ps)))
      (Rename.skip1 (Γ := Pending.eraseAux ps Γ) (A := A) (B := H))
      (rename (rotateHeadToNewest (Δ := Γ) (H := A) ps) t)]
  exact rename_eq_of_pointwise
    (fun {B} x => (Rename.skip1_ext_apply (renameEraseAux ρ ps) (B := H) x).symm)
    (rename (rotateHeadToNewest (Δ := Γ) (H := A) ps) t)


mutual
theorem NegNeu.erase_rename {Γ Δ : StableCtx sig} {N : Neg sig.nBases}
    (ρ : StableRename Γ Δ) (n : NegNeu Γ N) :
    NegNeu.erase (NegNeu.rename ρ n) =
      rename (StableRename.erase ρ) (NegNeu.erase n) :=
  match n with
  | .var x => by
      simp only [NegNeu.rename, NegNeu.erase, rename]
      exact congrArg Tm.var (StableVar.erase_rename ρ x)
  | .fst n => by
      simp [NegNeu.rename, NegNeu.erase, rename, NegNeu.erase_rename ρ n]; rfl
  | .snd n => by
      simp [NegNeu.rename, NegNeu.erase, rename, NegNeu.erase_rename ρ n]; rfl
  | .app n p => by
      simp [NegNeu.rename, NegNeu.erase, rename,
        NegNeu.erase_rename ρ n, PosNeu.erase_rename ρ p]; rfl

theorem PosNeu.erase_rename {Γ Δ : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Γ Δ) (p : PosNeu Γ P) :
    PosNeu.erase (PosNeu.rename ρ p) =
      rename (StableRename.erase ρ) (PosNeu.erase p) :=
  match p with
  | .atom x => by
      simp only [PosNeu.rename, PosNeu.erase, rename]
      exact congrArg Tm.var (StableVar.erase_rename ρ x)
  | .inl p => by
      simp [PosNeu.rename, PosNeu.erase, rename, PosNeu.erase_rename ρ p]
  | .inr p => by
      simp [PosNeu.rename, PosNeu.erase, rename, PosNeu.erase_rename ρ p]
  | .shift t => by
      simp [PosNeu.rename, PosNeu.erase, Inv.erase_rename ρ t]; rfl

theorem Foc.erase_rename {Γ Δ : StableCtx sig} {Q : Pos sig.nBases}
    (ρ : StableRename Γ Δ) (f : Foc Γ Q) :
    Foc.erase (Foc.rename ρ f) =
      rename (StableRename.erase ρ) (Foc.erase f) :=
  match f with
  | .up p => by
      simp [Foc.rename, Foc.erase, PosNeu.erase_rename ρ p]
  | .letShift n t => by
      simp only [Foc.rename, Foc.erase]
      rw [NegNeu.erase_rename ρ n, Inv.erase_rename ρ t]
      change subst0
          (rename (Rename.ext (StableRename.erase ρ)) (Inv.erase t))
          (rename (StableRename.erase ρ) (NegNeu.erase n)) =
        rename (StableRename.erase ρ) (subst0 (Inv.erase t) (NegNeu.erase n))
      exact (rename_subst0 (StableRename.erase ρ) (Inv.erase t) (NegNeu.erase n)).symm

theorem Inv.erase_rename {Γ Δ : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} (ρ : StableRename Γ Δ) (t : Inv Γ ps G) :
    Inv.erase (Inv.rename ρ t) =
      rename (renameEraseAux (StableRename.erase ρ) ps) (Inv.erase t) :=
  match t with
  | .unit => rfl
  | .pair t u => by
      simp [Inv.rename, Inv.erase, rename, Inv.erase_rename ρ t, Inv.erase_rename ρ u]; rfl
  | .lam t => by
      simp [Inv.rename, Inv.erase, rename, Inv.erase_rename ρ t]; rfl
  | .focusPos f => by
      simp [Inv.rename, Inv.erase, Foc.erase_rename ρ f]; rfl
  | .focusShift f => by
      simp [Inv.rename, Inv.erase, Foc.erase_rename ρ f]; rfl
  | .storeAtom t => by
      simp only [Inv.rename, Inv.erase]
      refine (Inv.erase_rename (StableRename.ext ρ) t).trans ?_
      exact rename_eq_of_pointwise
        (fun {A} x => renameEraseAux_eq_of_pointwise
          (StableRename.erase_ext_apply ρ) _ x) _
  | .storeShift t => by
      simp only [Inv.rename, Inv.erase]
      refine (Inv.erase_rename (StableRename.ext ρ) t).trans ?_
      exact rename_eq_of_pointwise
        (fun {A} x => renameEraseAux_eq_of_pointwise
          (StableRename.erase_ext_apply ρ) _ x) _
  | .abort => by
      rename_i rest
      let ρe : Rename sig Γ.erase Δ.erase := StableRename.erase ρ
      let H : Object sig.nBases := .never
      let abortΓ : Tm ((Pending.eraseAux rest Γ.erase).snoc H) G.erase :=
        .abort (.var .here)
      let abortΔ : Tm ((Pending.eraseAux rest Δ.erase).snoc H) G.erase :=
        .abort (.var .here)
      change
        rename (rotateNewestToHead (Δ := Δ.erase) (A := H) rest) abortΔ =
          rename (renameEraseAux ρe (.cons (.zero : Pos sig.nBases) rest))
            (rename (rotateNewestToHead (Δ := Γ.erase) (A := H) rest) abortΓ)
      have hcomp :=
        rename_comp (renameEraseAux (Rename.ext ρe) rest)
          (rotateNewestToHead (Δ := Γ.erase) (A := H) rest) abortΓ
      refine Eq.symm (hcomp.trans ?_)
      refine (rename_eq_of_pointwise
          (fun {B} x => rotateNewestToHead_nat_apply ρe rest x) abortΓ).trans ?_
      rw [← rename_comp (rotateNewestToHead (Δ := Δ.erase) (A := H) rest)
          (Rename.ext (renameEraseAux ρe rest)) abortΓ]
      rfl
  | .caseSum l r => by
      rename_i A B rest
      let ρe : Rename sig Γ.erase Δ.erase := StableRename.erase ρ
      let H : Object sig.nBases := .coprod A.erase B.erase
      have hl := Inv.erase_rename ρ l
      have hr := Inv.erase_rename ρ r
      simp only [Inv.rename, Inv.erase]
      rw [hl, hr]
      have hL :
          rename (Rename.skip1 (B := H))
              (rename (rotateHeadToNewest (Δ := Δ.erase) (H := A.erase) rest)
                (rename (renameEraseAux (StableRename.erase ρ) (.cons A rest))
                  (Inv.erase l))) =
            rename (Rename.ext (Rename.ext (renameEraseAux ρe rest)))
              (rename (Rename.skip1 (B := H))
                (rename (rotateHeadToNewest (Δ := Γ.erase) (H := A.erase) rest)
                  (Inv.erase l))) := by
        change
          rename (Rename.skip1 (B := H))
              (rename (rotateHeadToNewest (Δ := Δ.erase) (H := A.erase) rest)
                (rename (renameEraseAux (Rename.ext ρe) rest) (Inv.erase l))) = _
        exact case_branch_comm (Γ := Γ.erase) (Δ := Δ.erase) (A := A.erase) (H := H)
          (C := G.erase) ρe rest (Inv.erase l)
      have hR :
          rename (Rename.skip1 (B := H))
              (rename (rotateHeadToNewest (Δ := Δ.erase) (H := B.erase) rest)
                (rename (renameEraseAux (StableRename.erase ρ) (.cons B rest))
                  (Inv.erase r))) =
            rename (Rename.ext (Rename.ext (renameEraseAux ρe rest)))
              (rename (Rename.skip1 (B := H))
                (rename (rotateHeadToNewest (Δ := Γ.erase) (H := B.erase) rest)
                  (Inv.erase r))) := by
        change
          rename (Rename.skip1 (B := H))
              (rename (rotateHeadToNewest (Δ := Δ.erase) (H := B.erase) rest)
                (rename (renameEraseAux (Rename.ext ρe) rest) (Inv.erase r))) = _
        exact case_branch_comm (Γ := Γ.erase) (Δ := Δ.erase) (A := B.erase) (H := H)
          (C := G.erase) ρe rest (Inv.erase r)
      refine
        (congrArg (rename (rotateNewestToHead (Δ := Δ.erase) (A := H) rest))
          (congr (congrArg (Tm.case (.var .here)) hL) hR)).trans ?_
      -- After hL/hR: rename rotate_Δ (.case .here (rename (ext (ext σ)) tΓ) (rename (ext (ext σ)) uΓ))
      -- = rename (comp rotate_Δ (ext σ)) (.case .here tΓ uΓ)
      -- = rename (comp (renameEraseAux (ext ρe) rest) rotate_Γ) (.case .here tΓ uΓ)  [nat]
      -- = rename (renameEraseAux (ext ρe) rest) (rename rotate_Γ (.case .here tΓ uΓ))
      let tΓ :=
        rename (Rename.skip1 (B := H))
          (rename (rotateHeadToNewest (Δ := Γ.erase) (H := A.erase) rest) (Inv.erase l))
      let uΓ :=
        rename (Rename.skip1 (B := H))
          (rename (rotateHeadToNewest (Δ := Γ.erase) (H := B.erase) rest) (Inv.erase r))
      let σ : Rename sig (Pending.eraseAux rest Γ.erase) (Pending.eraseAux rest Δ.erase) :=
        renameEraseAux ρe rest
      have hfold :
          rename (rotateNewestToHead (Δ := Δ.erase) (A := H) rest)
              (.case (.var .here)
                (rename (Rename.ext (Rename.ext σ)) tΓ)
                (rename (Rename.ext (Rename.ext σ)) uΓ)) =
            rename
              (Rename.comp (rotateNewestToHead (Δ := Δ.erase) (A := H) rest)
                (Rename.ext σ))
              (.case (.var .here) tΓ uΓ) := by
        change
          rename (rotateNewestToHead (Δ := Δ.erase) (A := H) rest)
              (rename (Rename.ext σ) (.case (.var .here) tΓ uΓ)) =
            rename
              (Rename.comp (rotateNewestToHead (Δ := Δ.erase) (A := H) rest)
                (Rename.ext σ))
              (.case (.var .here) tΓ uΓ)
        exact rename_comp (rotateNewestToHead (Δ := Δ.erase) (A := H) rest)
          (Rename.ext σ) (.case (.var .here) tΓ uΓ)
      refine hfold.trans ?_
      refine Eq.symm ?_
      have hcomp :=
        rename_comp (renameEraseAux (Rename.ext ρe) rest)
          (rotateNewestToHead (Δ := Γ.erase) (A := H) rest)
          (.case (.var .here) tΓ uΓ)
      refine hcomp.trans ?_
      exact rename_eq_of_pointwise
        (fun {B} x => rotateNewestToHead_nat_apply ρe rest x)
        (.case (.var .here) tΓ uΓ)

end

/-! ### Weakening corollaries -/

theorem Inv.erase_weaken {Γ : StableCtx sig} {S : StableTy sig.nBases}
    {ps : Pending sig} {G : Goal sig.nBases} (t : Inv Γ ps G) :
    let ρw := @StableRename.weaken sig Γ S
    Inv.erase (Inv.weaken (S := S) t) =
      Gimbal.Equality.rename (renameEraseAux (StableRename.erase ρw) ps) (Inv.erase t) :=
  Inv.erase_rename (@StableRename.weaken sig Γ S) t

theorem NegNeu.erase_weaken {Γ : StableCtx sig} {S : StableTy sig.nBases}
    {N : Neg sig.nBases} (n : NegNeu Γ N) :
    let ρw := @StableRename.weaken sig Γ S
    NegNeu.erase (NegNeu.weaken (S := S) n) =
      Gimbal.Equality.rename (StableRename.erase ρw) (NegNeu.erase n) :=
  NegNeu.erase_rename (@StableRename.weaken sig Γ S) n

theorem Foc.erase_weaken {Γ : StableCtx sig} {S : StableTy sig.nBases}
    {Q : Pos sig.nBases} (f : Foc Γ Q) :
    let ρw := @StableRename.weaken sig Γ S
    Foc.erase (Foc.weaken (S := S) f) =
      Gimbal.Equality.rename (StableRename.erase ρw) (Foc.erase f) :=
  Foc.erase_rename (@StableRename.weaken sig Γ S) f

theorem PosNeu.erase_weaken {Γ : StableCtx sig} {S : StableTy sig.nBases}
    {P : Pos sig.nBases} (p : PosNeu Γ P) :
    let ρw := @StableRename.weaken sig Γ S
    PosNeu.erase (PosNeu.weaken (S := S) p) =
      Gimbal.Equality.rename (StableRename.erase ρw) (PosNeu.erase p) :=
  PosNeu.erase_rename (@StableRename.weaken sig Γ S) p

/-! ### SplitNewest under renaming -/

theorem splitNewest_inl_rename {Γ Δ : Ctx sig} {H A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (x : Var (Γ.snoc H) A) (h : A = H)
    (hx : splitNewest x = .inl h) :
    splitNewest (Rename.ext ρ x) = .inl h := by
  cases x with
  | here =>
      cases h
      cases hx
      rfl
  | there y =>
      cases hx

theorem splitNewest_inr_rename {Γ Δ : Ctx sig} {H A : Object sig.nBases}
    (ρ : Rename sig Γ Δ) (x : Var (Γ.snoc H) A) (z : Var Γ A)
    (hx : splitNewest x = .inr z) :
    splitNewest (Rename.ext ρ x) = .inr (ρ z) := by
  cases x with
  | here => cases hx
  | there y =>
      cases hx
      rfl

/-! ### Saturated erase–rename -/

mutual
theorem SNegNeu.erase_rename {Γ Δ : StableCtx sig} {N : Neg sig.nBases}
    (ρ : StableRename Γ Δ) (n : SNegNeu Γ N) :
    SNegNeu.erase (SNegNeu.rename ρ n) =
      Gimbal.Equality.rename (StableRename.erase ρ) (SNegNeu.erase n) :=
  match n with
  | .var x => by
      simp only [SNegNeu.rename, SNegNeu.erase, Gimbal.Equality.rename]
      exact congrArg Tm.var (StableVar.erase_rename ρ x)
  | .fst n => by
      simp [SNegNeu.rename, SNegNeu.erase, Gimbal.Equality.rename,
        SNegNeu.erase_rename ρ n]; rfl
  | .snd n => by
      simp [SNegNeu.rename, SNegNeu.erase, Gimbal.Equality.rename,
        SNegNeu.erase_rename ρ n]; rfl
  | .app n p => by
      simp [SNegNeu.rename, SNegNeu.erase, Gimbal.Equality.rename,
        SNegNeu.erase_rename ρ n, SPosNeu.erase_rename ρ p]; rfl
termination_by sizeOf n
decreasing_by
  all_goals (
    simp_wf
    (try
      let heq : _ ≍ _ := by assumption
      cases heq)
    try simp only [NonemptyBatchObs.one.sizeOf_spec, NonemptyBatchObs.cons.sizeOf_spec,
      Sat.up.sizeOf_spec, Sat.batch.sizeOf_spec]
    omega
  )

theorem SPosNeu.erase_rename {Γ Δ : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Γ Δ) (p : SPosNeu Γ P) :
    SPosNeu.erase (SPosNeu.rename ρ p) =
      Gimbal.Equality.rename (StableRename.erase ρ) (SPosNeu.erase p) :=
  match p with
  | .atom x => by
      simp only [SPosNeu.rename, SPosNeu.erase, Gimbal.Equality.rename]
      exact congrArg Tm.var (StableVar.erase_rename ρ x)
  | .inl p => by
      simp [SPosNeu.rename, SPosNeu.erase, Gimbal.Equality.rename,
        SPosNeu.erase_rename ρ p]
  | .inr p => by
      simp [SPosNeu.rename, SPosNeu.erase, Gimbal.Equality.rename,
        SPosNeu.erase_rename ρ p]
  | .shift t => by
      simp [SPosNeu.rename, SPosNeu.erase, SInv.erase_rename ρ t]; rfl
termination_by sizeOf p
decreasing_by
  all_goals (
    simp_wf
    (try
      let heq : _ ≍ _ := by assumption
      cases heq)
    try simp only [NonemptyBatchObs.one.sizeOf_spec, NonemptyBatchObs.cons.sizeOf_spec,
      Sat.up.sizeOf_spec, Sat.batch.sizeOf_spec]
    omega
  )

/-- Naturality of parallel batch lookup (mutual with saturated erase–rename). -/
theorem batchSubstLookup_rename {Γ Δ : StableCtx sig} {selected : Pending sig}
    (ρ : StableRename Γ Δ) (obs : NonemptyBatchObs Γ selected)
    {A : Object sig.nBases}
    (x : Var (Pending.eraseAux selected Γ.erase) A) :
    batchSubstLookup (NonemptyBatchObs.rename ρ obs)
        (renameEraseAux (StableRename.erase ρ) selected x) =
      Gimbal.Equality.rename (StableRename.erase ρ) (batchSubstLookup obs x) :=
  match obs, x with
  | .one n, x => by
      change Subst.single (SNegNeu.erase (SNegNeu.rename ρ n))
          (Rename.ext (StableRename.erase ρ) x) =
        Gimbal.Equality.rename (StableRename.erase ρ)
          (Subst.single (SNegNeu.erase n) x)
      rw [SNegNeu.erase_rename ρ n]
      cases x <;> rfl
  | .cons (Q := Q) (ps := rest) n σrest, x => by
      have hx :
          renameEraseAux (StableRename.erase ρ) (.cons Q rest) x =
            renameEraseAux (Rename.ext (StableRename.erase ρ)) rest x :=
        rfl
      simp only [batchSubstLookup, NonemptyBatchObs.rename, hx]
      have hrot :
          rotateHeadToNewest (Δ := Δ.erase) (H := Q.erase) rest
              (renameEraseAux (Rename.ext (StableRename.erase ρ)) rest x) =
            Rename.ext (renameEraseAux (StableRename.erase ρ) rest)
              (rotateHeadToNewest (Δ := Γ.erase) (H := Q.erase) rest x) :=
        (rotateHeadToNewest_nat_apply (StableRename.erase ρ) rest x).symm
      rw [hrot]
      cases hsplit :
          splitNewest (rotateHeadToNewest (Δ := Γ.erase) (H := Q.erase) rest x) with
      | inl h =>
          rw [splitNewest_inl_rename (renameEraseAux (StableRename.erase ρ) rest) _ h
            hsplit]
          cases h
          exact SNegNeu.erase_rename ρ n
      | inr z =>
          rw [splitNewest_inr_rename (renameEraseAux (StableRename.erase ρ) rest) _ z
            hsplit]
          exact batchSubstLookup_rename ρ σrest z
termination_by sizeOf obs
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec, NonemptyBatchObs.cons.sizeOf_spec]
    omega
  )

theorem Sat.erase_rename {Old Old' New : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Old Old') (s : Sat Old New P) :
    Sat.erase (Sat.rename ρ s) =
      Gimbal.Equality.rename
        (StableRename.erase (StableRename.keepLeft ρ New)) (Sat.erase s) :=
  match s with
  | .up v => by
      simp only [Sat.rename, Sat.erase, StableRename.keepLeft]
      exact SPosNeu.erase_rename ρ v
  | .batch obs body => by
      simp only [Sat.rename, Sat.erase]
      let κ : StableRename (Old.append New) (Old'.append New) :=
        StableRename.keepLeft ρ New
      let ρe : Rename sig (Old.append New).erase (Old'.append New).erase :=
        StableRename.erase κ
      let bodyE :=
        SInv.erase (Old := Old.append New) (New := StableCtx.empty) body
      have hbody :
          SInv.erase (Old := Old'.append New) (New := StableCtx.empty)
              (SInv.rename (Old := Old.append New) (Old' := Old'.append New)
                (New := StableCtx.empty) κ body) =
            rename (renameEraseAux ρe _) bodyE := by
        simpa [ρe, StableRename.keepLeft] using
          SInv.erase_rename (Old := Old.append New) (Old' := Old'.append New)
            (New := StableCtx.empty) κ body
      rw [hbody]
      change
        subst (batchSubst (NonemptyBatchObs.rename κ obs))
            (rename (renameEraseAux ρe _) bodyE) =
          rename ρe (subst (batchSubst obs) bodyE)
      rw [subst_rename, rename_subst]
      exact subst_eq_of_pointwise (fun {A} x => batchSubstLookup_rename κ obs x) bodyE
termination_by sizeOf s
decreasing_by
  all_goals (
    simp_wf
    (try
      let heq : _ ≍ _ := by assumption
      cases heq)
    try simp only [NonemptyBatchObs.one.sizeOf_spec, NonemptyBatchObs.cons.sizeOf_spec,
      Sat.up.sizeOf_spec, Sat.batch.sizeOf_spec]
    omega
  )

theorem SInv.erase_rename {Old Old' New : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} (ρ : StableRename Old Old')
    (t : SInv Old New ps G) :
    SInv.erase (SInv.rename ρ t) =
      Gimbal.Equality.rename
        (renameEraseAux (StableRename.erase (StableRename.keepLeft ρ New)) ps)
        (SInv.erase t) :=
  match t with
  | .unit => rfl
  | .pair t u => by
      simp [SInv.rename, SInv.erase, Gimbal.Equality.rename,
        SInv.erase_rename ρ t, SInv.erase_rename ρ u]; rfl
  | .lam t => by
      simp [SInv.rename, SInv.erase, Gimbal.Equality.rename,
        SInv.erase_rename ρ t]; rfl
  | .storeAtom t => by
      simp only [SInv.rename, SInv.erase]
      refine (SInv.erase_rename ρ t).trans ?_
      apply rename_eq_of_pointwise
      intro A x
      -- keepLeft ρ (New.snoc) = ext (keepLeft ρ New)
      exact renameEraseAux_eq_of_pointwise
        (StableRename.erase_ext_apply (StableRename.keepLeft ρ New)) _ x
  | .storeShift t => by
      simp only [SInv.rename, SInv.erase]
      refine (SInv.erase_rename ρ t).trans ?_
      apply rename_eq_of_pointwise
      intro A x
      exact renameEraseAux_eq_of_pointwise
        (StableRename.erase_ext_apply (StableRename.keepLeft ρ New)) _ x
  | .satPos s => by
      simp [SInv.rename, SInv.erase, Sat.erase_rename ρ s]; rfl
  | .satShift s => by
      simp [SInv.rename, SInv.erase, Sat.erase_rename ρ s]; rfl
  | .abort => by
      rename_i rest
      let κ : StableRename (Old.append New) (Old'.append New) :=
        StableRename.keepLeft ρ New
      let ρe : Rename sig (Old.append New).erase (Old'.append New).erase :=
        StableRename.erase κ
      let H : Object sig.nBases := .never
      let abortΓ : Tm ((Pending.eraseAux rest (Old.append New).erase).snoc H) G.erase :=
        .abort (.var .here)
      let abortΔ : Tm ((Pending.eraseAux rest (Old'.append New).erase).snoc H) G.erase :=
        .abort (.var .here)
      simp only [SInv.rename, SInv.erase]
      change
        Gimbal.Equality.rename
            (rotateNewestToHead (Δ := (Old'.append New).erase) (A := H) rest) abortΔ =
          Gimbal.Equality.rename (renameEraseAux ρe (.cons (.zero : Pos sig.nBases) rest))
            (Gimbal.Equality.rename
              (rotateNewestToHead (Δ := (Old.append New).erase) (A := H) rest) abortΓ)
      have hcomp :=
        rename_comp (renameEraseAux (Rename.ext ρe) rest)
          (rotateNewestToHead (Δ := (Old.append New).erase) (A := H) rest) abortΓ
      refine Eq.symm (hcomp.trans ?_)
      refine (rename_eq_of_pointwise
          (fun {B} x => rotateNewestToHead_nat_apply ρe rest x) abortΓ).trans ?_
      rw [← rename_comp (rotateNewestToHead (Δ := (Old'.append New).erase) (A := H) rest)
          (Rename.ext (renameEraseAux ρe rest)) abortΓ]
      rfl
  | .caseSum l r => by
      rename_i A B rest
      let κ : StableRename (Old.append New) (Old'.append New) :=
        StableRename.keepLeft ρ New
      let ρe : Rename sig (Old.append New).erase (Old'.append New).erase :=
        StableRename.erase κ
      let H : Object sig.nBases := .coprod A.erase B.erase
      have hl := SInv.erase_rename ρ l
      have hr := SInv.erase_rename ρ r
      simp only [SInv.rename, SInv.erase]
      rw [hl, hr]
      have hL :
          rename (Rename.skip1 (B := H))
              (rename (rotateHeadToNewest (Δ := (Old'.append New).erase) (H := A.erase) rest)
                (rename (renameEraseAux (StableRename.erase κ) (.cons A rest))
                  (SInv.erase l))) =
            rename (Rename.ext (Rename.ext (renameEraseAux ρe rest)))
              (rename (Rename.skip1 (B := H))
                (rename (rotateHeadToNewest (Δ := (Old.append New).erase) (H := A.erase) rest)
                  (SInv.erase l))) := by
        change
          rename (Rename.skip1 (B := H))
              (rename (rotateHeadToNewest (Δ := (Old'.append New).erase) (H := A.erase) rest)
                (rename (renameEraseAux (Rename.ext ρe) rest) (SInv.erase l))) = _
        exact case_branch_comm (Γ := (Old.append New).erase)
          (Δ := (Old'.append New).erase) (A := A.erase) (H := H)
          (C := G.erase) ρe rest (SInv.erase l)
      have hR :
          rename (Rename.skip1 (B := H))
              (rename (rotateHeadToNewest (Δ := (Old'.append New).erase) (H := B.erase) rest)
                (rename (renameEraseAux (StableRename.erase κ) (.cons B rest))
                  (SInv.erase r))) =
            rename (Rename.ext (Rename.ext (renameEraseAux ρe rest)))
              (rename (Rename.skip1 (B := H))
                (rename (rotateHeadToNewest (Δ := (Old.append New).erase) (H := B.erase) rest)
                  (SInv.erase r))) := by
        change
          rename (Rename.skip1 (B := H))
              (rename (rotateHeadToNewest (Δ := (Old'.append New).erase) (H := B.erase) rest)
                (rename (renameEraseAux (Rename.ext ρe) rest) (SInv.erase r))) = _
        exact case_branch_comm (Γ := (Old.append New).erase)
          (Δ := (Old'.append New).erase) (A := B.erase) (H := H)
          (C := G.erase) ρe rest (SInv.erase r)
      refine
        (congrArg (rename (rotateNewestToHead (Δ := (Old'.append New).erase) (A := H) rest))
          (congr (congrArg (Tm.case (.var .here)) hL) hR)).trans ?_
      let tΓ :=
        rename (Rename.skip1 (B := H))
          (rename (rotateHeadToNewest (Δ := (Old.append New).erase) (H := A.erase) rest)
            (SInv.erase l))
      let uΓ :=
        rename (Rename.skip1 (B := H))
          (rename (rotateHeadToNewest (Δ := (Old.append New).erase) (H := B.erase) rest)
            (SInv.erase r))
      let σ : Rename sig
          (Pending.eraseAux rest (Old.append New).erase)
          (Pending.eraseAux rest (Old'.append New).erase) :=
        renameEraseAux ρe rest
      have hfold :
          rename (rotateNewestToHead (Δ := (Old'.append New).erase) (A := H) rest)
              (.case (.var .here)
                (rename (Rename.ext (Rename.ext σ)) tΓ)
                (rename (Rename.ext (Rename.ext σ)) uΓ)) =
            rename
              (Rename.comp (rotateNewestToHead (Δ := (Old'.append New).erase) (A := H) rest)
                (Rename.ext σ))
              (.case (.var .here) tΓ uΓ) := by
        change
          rename (rotateNewestToHead (Δ := (Old'.append New).erase) (A := H) rest)
              (rename (Rename.ext σ) (.case (.var .here) tΓ uΓ)) =
            rename
              (Rename.comp (rotateNewestToHead (Δ := (Old'.append New).erase) (A := H) rest)
                (Rename.ext σ))
              (.case (.var .here) tΓ uΓ)
        exact rename_comp (rotateNewestToHead (Δ := (Old'.append New).erase) (A := H) rest)
          (Rename.ext σ) (.case (.var .here) tΓ uΓ)
      refine hfold.trans ?_
      refine Eq.symm ?_
      have hcomp :=
        rename_comp (renameEraseAux (Rename.ext ρe) rest)
          (rotateNewestToHead (Δ := (Old.append New).erase) (A := H) rest)
          (.case (.var .here) tΓ uΓ)
      refine hcomp.trans ?_
      exact rename_eq_of_pointwise
        (fun {B} x => rotateNewestToHead_nat_apply ρe rest x)
        (.case (.var .here) tΓ uΓ)
termination_by sizeOf t
decreasing_by
  all_goals (
    simp_wf
    (try
      let heq : _ ≍ _ := by assumption
      cases heq)
    try simp only [NonemptyBatchObs.one.sizeOf_spec, NonemptyBatchObs.cons.sizeOf_spec,
      Sat.up.sizeOf_spec, Sat.batch.sizeOf_spec]
    omega
  )
end

/-! ### Identity + non-identity fixtures -/

namespace EraseCommFixtures

open Fixtures

theorem erase_rename_id_unit :
    Inv.erase (Inv.rename StableRename.id inv_unit) = Inv.erase inv_unit :=
  rfl

theorem erase_rename_id_letShift :
    Foc.erase (Foc.rename StableRename.id foc_letShift) = Foc.erase foc_letShift :=
  rfl

theorem erase_rename_id_case :
    Inv.erase (Inv.rename StableRename.id inv_case_zero_sum) =
      Inv.erase inv_case_zero_sum :=
  rfl

theorem erase_rename_id_focusShift :
    Inv.erase (Inv.rename StableRename.id inv_focusShift) =
      Inv.erase inv_focusShift :=
  rfl

/-- Non-identity pending-case: weaken through `[0+0]` case erasure. -/
theorem erase_rename_weaken_case :
    Inv.erase (Inv.weaken (S := .neg (.one : Neg sig0.nBases)) inv_case_zero_sum) =
      Gimbal.Equality.rename
        (renameEraseAux
          (StableRename.erase (@StableRename.weaken sig0 .empty (.neg .one)))
          (.cons (.sum .zero .zero) .empty))
        (Inv.erase inv_case_zero_sum) :=
  Inv.erase_weaken (S := .neg .one) inv_case_zero_sum

/-- Non-identity two-entry batch under weakening. -/
theorem erase_rename_weaken_batch_two :
    SInv.erase
        (SInv.rename (@StableRename.weaken sig0
            (StableCtx.snoc .empty (.neg (.shift .zero))) (.neg .one))
          EraseFixtures.sinv_batch_two) =
      Gimbal.Equality.rename
        (renameEraseAux
          (StableRename.erase
            (StableRename.keepLeft
              (@StableRename.weaken sig0
                (StableCtx.snoc .empty (.neg (.shift .zero))) (.neg .one))
              .empty))
          .empty)
        (SInv.erase EraseFixtures.sinv_batch_two) :=
  SInv.erase_rename
    (@StableRename.weaken sig0
      (StableCtx.snoc .empty (.neg (.shift .zero))) (.neg .one))
    EraseFixtures.sinv_batch_two

theorem subst0_rename_smoke :
    ∀ {Γ : Ctx sig0} {A B : Object 0}
      (ρ : Rename sig0 Γ Γ) (t : Tm (Γ.snoc A) B) (n : Tm Γ A),
      subst0 (Gimbal.Equality.rename (Rename.ext ρ) t)
          (Gimbal.Equality.rename ρ n) =
        Gimbal.Equality.rename ρ (subst0 t n) :=
  fun ρ t n => subst0_rename ρ t n

end EraseCommFixtures

end Gimbal.Equality.Scherer
