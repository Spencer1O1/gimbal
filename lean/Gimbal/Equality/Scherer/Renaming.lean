/-
  Scherer-core stable renaming / weakening (S2).

  Renames act on the stable (`old`) context. Pending formulas and the saturated
  `new` telescope are unchanged by renaming; `new` grows only via `store*`.
  Focused forms are not closed under arbitrary substitution (ledger).
-/

import Gimbal.Equality.Scherer.Erase

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-- Renaming of stable variables between stable contexts. -/
def StableRename (Γ Δ : StableCtx sig) : Type :=
  ∀ {S : StableTy sig.nBases}, StableVar Γ S → StableVar Δ S

namespace StableRename

def id {Γ : StableCtx sig} : StableRename Γ Γ :=
  fun x => x

def comp {Γ Δ Ε : StableCtx sig}
    (ρ : StableRename Δ Ε) (τ : StableRename Γ Δ) : StableRename Γ Ε :=
  fun x => ρ (τ x)

/-- Extend under one newest stable binder. -/
def ext {Γ Δ : StableCtx sig} {S : StableTy sig.nBases}
    (ρ : StableRename Γ Δ) : StableRename (Γ.snoc S) (Δ.snoc S)
  | _, .here => .here
  | _, .there x => .there (ρ x)

/-- Weaken into an extended stable context. -/
def weaken {Γ : StableCtx sig} {S : StableTy sig.nBases} :
    StableRename Γ (Γ.snoc S) :=
  fun x => .there x

/-- Rename the left factor of an append; right factor unchanged. -/
def keepLeft {Γ Γ' : StableCtx sig} (ρ : StableRename Γ Γ') :
    (Δ : StableCtx sig) → StableRename (Γ.append Δ) (Γ'.append Δ)
  | .empty => ρ
  | .snoc Δ _ => StableRename.ext (keepLeft ρ Δ)

/-- Recover the stable variable witnessing an erased de Bruijn index. -/
def ofEraseVar :
    (Γ : StableCtx sig) → {A : Object sig.nBases} → Var Γ.erase A →
      (S : StableTy sig.nBases) ×' (A = S.erase) ×' StableVar Γ S
  | .empty, _, x => nomatch x
  | .snoc _ S, _, .here => ⟨S, rfl, .here⟩
  | .snoc Γ0 _, _, .there y =>
      let ⟨S', h, z⟩ := ofEraseVar Γ0 y
      ⟨S', h, .there z⟩

/-- Erase a stable renaming to an object-level renaming. -/
def erase {Γ Δ : StableCtx sig} (ρ : StableRename Γ Δ) :
    Rename sig Γ.erase Δ.erase :=
  fun {A} x =>
    let ⟨_, h, y⟩ := ofEraseVar Γ x
    (h ▸ StableVar.erase (ρ y) : Var Δ.erase A)

end StableRename

/-! ### Ordinary renaming -/

mutual
def NegNeu.rename {Γ Δ : StableCtx sig} {N : Neg sig.nBases}
    (ρ : StableRename Γ Δ) : NegNeu Γ N → NegNeu Δ N
  | .var x => .var (ρ x)
  | .fst n => .fst (NegNeu.rename ρ n)
  | .snd n => .snd (NegNeu.rename ρ n)
  | .app n p => .app (NegNeu.rename ρ n) (PosNeu.rename ρ p)

def PosNeu.rename {Γ Δ : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Γ Δ) : PosNeu Γ P → PosNeu Δ P
  | .atom x => .atom (ρ x)
  | .inl p => .inl (PosNeu.rename ρ p)
  | .inr p => .inr (PosNeu.rename ρ p)
  | .shift t => .shift (Inv.rename ρ t)

def Foc.rename {Γ Δ : StableCtx sig} {Q : Pos sig.nBases}
    (ρ : StableRename Γ Δ) : Foc Γ Q → Foc Δ Q
  | .up p => .up (PosNeu.rename ρ p)
  | .letShift n t => .letShift (NegNeu.rename ρ n) (Inv.rename ρ t)

def Inv.rename {Γ Δ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
    (ρ : StableRename Γ Δ) : Inv Γ ps G → Inv Δ ps G
  | .unit => .unit
  | .pair t u => .pair (Inv.rename ρ t) (Inv.rename ρ u)
  | .lam t => .lam (Inv.rename ρ t)
  | .focusPos f => .focusPos (Foc.rename ρ f)
  | .focusShift f => .focusShift (Foc.rename ρ f)
  | .storeAtom t => .storeAtom (Inv.rename (StableRename.ext ρ) t)
  | .storeShift t => .storeShift (Inv.rename (StableRename.ext ρ) t)
  | .abort => .abort
  | .caseSum l r => .caseSum (Inv.rename ρ l) (Inv.rename ρ r)
end

def NegNeu.weaken {Γ : StableCtx sig} {S : StableTy sig.nBases} {N : Neg sig.nBases}
    (n : NegNeu Γ N) : NegNeu (Γ.snoc S) N :=
  NegNeu.rename StableRename.weaken n

def PosNeu.weaken {Γ : StableCtx sig} {S : StableTy sig.nBases} {P : Pos sig.nBases}
    (p : PosNeu Γ P) : PosNeu (Γ.snoc S) P :=
  PosNeu.rename StableRename.weaken p

def Foc.weaken {Γ : StableCtx sig} {S : StableTy sig.nBases} {Q : Pos sig.nBases}
    (f : Foc Γ Q) : Foc (Γ.snoc S) Q :=
  Foc.rename StableRename.weaken f

def Inv.weaken {Γ : StableCtx sig} {S : StableTy sig.nBases} {ps : Pending sig}
    {G : Goal sig.nBases} (t : Inv Γ ps G) : Inv (Γ.snoc S) ps G :=
  Inv.rename StableRename.weaken t

/-! ### Saturated renaming (renames `old`; `new` shape preserved) -/

mutual
def SNegNeu.rename {Γ Δ : StableCtx sig} {N : Neg sig.nBases}
    (ρ : StableRename Γ Δ) : SNegNeu Γ N → SNegNeu Δ N
  | .var x => .var (ρ x)
  | .fst n => .fst (SNegNeu.rename ρ n)
  | .snd n => .snd (SNegNeu.rename ρ n)
  | .app n p => .app (SNegNeu.rename ρ n) (SPosNeu.rename ρ p)

def SPosNeu.rename {Γ Δ : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Γ Δ) : SPosNeu Γ P → SPosNeu Δ P
  | .atom x => .atom (ρ x)
  | .inl p => .inl (SPosNeu.rename ρ p)
  | .inr p => .inr (SPosNeu.rename ρ p)
  | .shift t => .shift (SInv.rename ρ t)

def NonemptyBatchObs.rename {Γ Δ : StableCtx sig} {selected : Pending sig}
    (ρ : StableRename Γ Δ) :
    NonemptyBatchObs Γ selected → NonemptyBatchObs Δ selected
  | .one n => .one (SNegNeu.rename ρ n)
  | .cons n rest => .cons (SNegNeu.rename ρ n) (NonemptyBatchObs.rename ρ rest)

def Sat.rename {Old Old' New : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Old Old') : Sat Old New P → Sat Old' New P
  | .inconsistent z =>
      .inconsistent (SNegNeu.rename (StableRename.keepLeft ρ New) z)
  | .done v => .done (SPosNeu.rename (StableRename.keepLeft ρ New) v)
  | .batch obs body =>
      .batch
        (NonemptyBatchObs.rename (StableRename.keepLeft ρ New) obs)
        (SInv.rename (StableRename.keepLeft ρ New) body)

def SInv.rename {Old Old' New : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} (ρ : StableRename Old Old') :
    SInv Old New ps G → SInv Old' New ps G
  | .unit => .unit
  | .pair t u => .pair (SInv.rename ρ t) (SInv.rename ρ u)
  | .lam t => .lam (SInv.rename ρ t)
  | .storeAtom t => .storeAtom (SInv.rename ρ t)
  | .storeShift t => .storeShift (SInv.rename ρ t)
  | .satPos s => .satPos (Sat.rename ρ s)
  | .satShift s => .satShift (Sat.rename ρ s)
  | .abort => .abort
  | .caseSum l r => .caseSum (SInv.rename ρ l) (SInv.rename ρ r)
end

def SNegNeu.weaken {Γ : StableCtx sig} {S : StableTy sig.nBases} {N : Neg sig.nBases}
    (n : SNegNeu Γ N) : SNegNeu (Γ.snoc S) N :=
  SNegNeu.rename StableRename.weaken n

def SPosNeu.weaken {Γ : StableCtx sig} {S : StableTy sig.nBases} {P : Pos sig.nBases}
    (p : SPosNeu Γ P) : SPosNeu (Γ.snoc S) P :=
  SPosNeu.rename StableRename.weaken p

/-! ### Fixtures -/

namespace RenameFixtures

open Fixtures

def weaken_unit :
    Inv (sig := sig0) (StableCtx.snoc .empty (.neg .one)) .empty (.neg .one) :=
  Inv.weaken (S := .neg .one) inv_unit

def rename_id_letShift :
    Foc (sig := sig0)
      (StableCtx.snoc .empty (.neg (.shift .zero))) (.shift .one) :=
  Foc.rename StableRename.id foc_letShift

theorem rename_id_letShift_eq : rename_id_letShift = foc_letShift := rfl

def weaken_sat_done :
    Sat (sig := sig0) (StableCtx.snoc .empty (.neg .one)) .empty (.shift .one) :=
  Sat.rename (StableRename.weaken (S := .neg .one)) sat_done

def weaken_sat_inconsistent_old {P : Pos 0} :
    Sat (sig := sig0)
      (StableCtx.snoc
        (StableCtx.snoc .empty (.neg (.shift .zero))) (.neg .one))
      .empty P :=
  Sat.rename (StableRename.weaken (S := .neg .one))
    (sat_inconsistent_old (P := P))

theorem rename_id_sat_inconsistent_old {P : Pos 0} :
    Sat.rename StableRename.id (sat_inconsistent_old (P := P)) =
      sat_inconsistent_old :=
  rfl

def weaken_batch_one :
    SInv (sig := sig0)
      (StableCtx.snoc (StableCtx.snoc .empty (.neg (.shift .zero))) (.neg .one))
      .empty .empty (.pos (.shift .one)) :=
  SInv.rename (StableRename.weaken (S := .neg .one)) sinv_batch_one

end RenameFixtures

end Gimbal.Equality.Scherer
