/-
  Locally nameless, alias-normalized structural codes for selected Scherer
  syntax.  Numeric encodings, exact observation keys, traces, and comparison
  remain downstream.
-/

import Gimbal.Equality.Scherer.Erase
import Gimbal.Equality.Scherer.PairOrigin

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Canonical references and internal assignments -/

/-- Internal binders are de Bruijn variables; free values are terminal refs. -/
inductive CanonRef (R : AliasResolver sig) (Δ : Ctx sig) :
    Object sig.nBases → Type where
  | bound {A} : Var Δ A → CanonRef R Δ A
  | free {A} : ResolvedRef R A → CanonRef R Δ A

namespace CanonRef

def rename {R : AliasResolver sig} {Γ Δ : Ctx sig}
    (ρ : Rename sig Γ Δ) : CanonRef R Γ A → CanonRef R Δ A
  | .bound x => .bound (ρ x)
  | .free x => .free x

def freeDeps {R : AliasResolver sig} {Δ : Ctx sig} :
    CanonRef R Δ A → List (Origin sig)
  | .bound _ => []
  | .free x => [x.origin.raw]

def Scoped {R : AliasResolver sig} {Δ : Ctx sig}
    (pre : OriginScope) : CanonRef R Δ A → Prop
  | .bound _ => True
  | .free x => pre.Contains x.origin.raw

theorem freeDeps_terminal {R : AliasResolver sig} {Δ : Ctx sig}
    (x : CanonRef R Δ A) (o : Origin sig) (ho : o ∈ x.freeDeps) :
    R.target o = none := by
  cases x with
  | bound x => simp [freeDeps] at ho
  | free x =>
      simp [freeDeps] at ho
      subst o
      exact x.terminal

@[simp] theorem scoped_rename {R : AliasResolver sig} {Γ Δ : Ctx sig}
    (ρ : Rename sig Γ Δ) (pre : OriginScope) (x : CanonRef R Γ A) :
    (x.rename ρ).Scoped pre ↔ x.Scoped pre := by
  cases x <;> rfl

theorem scoped_of_mem_freeDeps {R : AliasResolver sig} {Δ : Ctx sig}
    {x : CanonRef R Δ A} (hx : x.Scoped pre) (o : Origin sig)
    (ho : o ∈ x.freeDeps) : pre.Contains o := by
  cases x with
  | bound x => simp [freeDeps] at ho
  | free x =>
      simp [freeDeps] at ho
      subst o
      exact hx

end CanonRef

/-- Canonical references for the actual stable context during coding. -/
structure CodeOriginAssignment (R : AliasResolver sig) (Δ : Ctx sig)
    (Γ : StableCtx sig) where
  ref : ∀ {S}, StableVar Γ S → CanonRef R Δ S.erase

/-- Canonical references for the actual pending worklist during coding. -/
structure CodePendingAssignment (R : AliasResolver sig) (Δ : Ctx sig)
    (ps : Pending sig) where
  ref : ∀ {P}, PendingVar ps P → CanonRef R Δ P.erase

namespace CodeOriginAssignment

def Scoped (pre : OriginScope) (E : CodeOriginAssignment R Δ Γ) : Prop :=
  ∀ {S} (x : StableVar Γ S), (E.ref x).Scoped pre

def ofOrigin (E : OriginAssignment R Γ) :
    CodeOriginAssignment R (Ctx.empty : Ctx sig) Γ where
  ref x := .free (E.ref x)

def rename (ρ : Rename sig Δ Ε) (E : CodeOriginAssignment R Δ Γ) :
    CodeOriginAssignment R Ε Γ where
  ref x := (E.ref x).rename ρ

def snoc (E : CodeOriginAssignment R Δ Γ) {S : StableTy sig.nBases}
    (source : CanonRef R Δ S.erase) : CodeOriginAssignment R Δ (Γ.snoc S) where
  ref := by
    intro T x
    cases x with
    | here => exact source
    | there x => exact E.ref x

@[simp] theorem snoc_here (E : CodeOriginAssignment R Δ Γ)
    {S : StableTy sig.nBases} (source : CanonRef R Δ S.erase) :
    (E.snoc source).ref (.here : StableVar (Γ.snoc S) S) = source := rfl

theorem rename_scoped {E : CodeOriginAssignment R Δ Γ}
    (hE : Scoped pre E) (ρ : Rename sig Δ Ε) :
    (E.rename ρ).Scoped pre := by
  intro S x
  change CanonRef.Scoped pre ((E.ref x).rename ρ)
  exact (CanonRef.scoped_rename ρ pre (E.ref x)).2 (hE x)

theorem snoc_scoped {E : CodeOriginAssignment R Δ Γ}
    {S : StableTy sig.nBases}
    {source : CanonRef R Δ S.erase}
    (hE : Scoped pre E) (hsource : source.Scoped pre) :
    (E.snoc source).Scoped pre := by
  intro T x
  cases x with
  | here => exact hsource
  | there x => exact hE x

end CodeOriginAssignment

namespace CodePendingAssignment

def Scoped (pre : OriginScope) (E : CodePendingAssignment R Δ ps) : Prop :=
  ∀ {P} (x : PendingVar ps P), (E.ref x).Scoped pre

def ofPending (E : PendingAssignment R ps) :
    CodePendingAssignment R (Ctx.empty : Ctx sig) ps where
  ref x := .free (E.ref x)

def empty (R : AliasResolver sig) (Δ : Ctx sig) :
    CodePendingAssignment R Δ (Pending.empty : Pending sig) where
  ref := fun x => nomatch x

def rename (ρ : Rename sig Δ Ε) (E : CodePendingAssignment R Δ ps) :
    CodePendingAssignment R Ε ps where
  ref x := (E.ref x).rename ρ

def cons {P : Pos sig.nBases} (source : CanonRef R Δ P.erase)
    (rest : CodePendingAssignment R Δ ps) :
    CodePendingAssignment R Δ (.cons P ps) where
  ref := by
    intro Q x
    cases x with
    | here => exact source
    | there x => exact rest.ref x

def tail (E : CodePendingAssignment R Δ (.cons P ps)) :
    CodePendingAssignment R Δ ps where
  ref x := E.ref (.there x)

@[simp] theorem cons_here {P : Pos sig.nBases} (source : CanonRef R Δ P.erase)
    (rest : CodePendingAssignment R Δ ps) :
    (cons source rest).ref (.here : PendingVar (.cons P ps) P) = source := rfl

theorem empty_scoped : (empty R Δ).Scoped pre := by
  intro P x
  nomatch x

theorem eq_empty (E : CodePendingAssignment R Δ (Pending.empty : Pending sig)) :
    E = empty R Δ := by
  cases E with
  | mk ref =>
      congr
      funext P x
      nomatch x

theorem rename_scoped {E : CodePendingAssignment R Δ ps}
    (hE : Scoped pre E) (ρ : Rename sig Δ Ε) :
    (E.rename ρ).Scoped pre := by
  intro P x
  change CanonRef.Scoped pre ((E.ref x).rename ρ)
  exact (CanonRef.scoped_rename ρ pre (E.ref x)).2 (hE x)

theorem cons_scoped {P : Pos sig.nBases} {source : CanonRef R Δ P.erase}
    {rest : CodePendingAssignment R Δ ps}
    (hsource : source.Scoped pre) (hrest : Scoped pre rest) :
    (cons source rest).Scoped pre := by
  intro Q x
  cases x with
  | here => exact hsource
  | there x => exact hrest x

theorem tail_scoped {E : CodePendingAssignment R Δ (.cons P ps)}
    (hE : Scoped pre E) : E.tail.Scoped pre := by
  intro Q x
  exact hE (.there x)

end CodePendingAssignment

/-- Embed the base context beneath all pending binders. -/
def Pending.weakenBase (ps : Pending sig) (Δ : Ctx sig) :
    Rename sig Δ (Pending.eraseAux ps Δ) :=
  match ps with
  | .empty => Rename.id
  | .cons P rest => fun x =>
      Pending.weakenBase rest (Δ.snoc P.erase) (Rename.weaken x)

/-- Turn a pending occurrence into its locally bound erased variable. -/
def PendingVar.eraseAux (Δ : Ctx sig) :
    {ps : Pending sig} → {P : Pos sig.nBases} →
      PendingVar ps P → Var (Pending.eraseAux ps Δ) P.erase
  | .cons _ rest, _, .here => pendingHeadVar (Δ := Δ) rest
  | .cons Q _rest, _, .there x => PendingVar.eraseAux (Δ.snoc Q.erase) x

/-- Alpha-normalized references for a simultaneously introduced batch. -/
def CodePendingAssignment.boundBatch
    (_B : BatchResultAssignment R selected) (Δ : Ctx sig) :
    CodePendingAssignment R (Pending.eraseAux selected Δ) selected where
  ref x := .bound (PendingVar.eraseAux Δ x)

theorem CodePendingAssignment.boundBatch_scoped
    (B : BatchResultAssignment R selected) (Δ : Ctx sig) :
    (CodePendingAssignment.boundBatch B Δ).Scoped pre := by
  intro P x
  change CanonRef.Scoped pre (.bound (PendingVar.eraseAux Δ x))
  trivial

/-! ### Structural selected codes -/

mutual

inductive SNegCode (R : AliasResolver sig) :
    Ctx sig → Neg sig.nBases → Type where
  | var {Δ N} : CanonRef R Δ N.erase → SNegCode R Δ N
  | fst {Δ A B} : SNegCode R Δ (.prod A B) → SNegCode R Δ A
  | snd {Δ A B} : SNegCode R Δ (.prod A B) → SNegCode R Δ B
  | app {Δ A N} : SNegCode R Δ (.arr A N) → SPosCode R Δ A → SNegCode R Δ N

inductive SPosCode (R : AliasResolver sig) :
    Ctx sig → Pos sig.nBases → Type where
  | atom {Δ q} : CanonRef R Δ (.base q) → SPosCode R Δ (.atom q)
  | inl {Δ A B} : SPosCode R Δ A → SPosCode R Δ (.sum A B)
  | inr {Δ A B} : SPosCode R Δ B → SPosCode R Δ (.sum A B)
  | shift {Δ N} : BranchCode R Δ .empty (.neg N) → SPosCode R Δ (.shift N)

/-- `dead` is the canonical code for a locally contradictory branch. -/
inductive BranchCode (R : AliasResolver sig) :
    Ctx sig → Pending sig → Goal sig.nBases → Type where
  | dead {Δ ps G} : BranchCode R Δ ps G
  | caseSum {Δ A B ps G} :
      BranchCode R (Δ.snoc A.erase) (.cons A ps) G →
      BranchCode R (Δ.snoc B.erase) (.cons B ps) G →
      BranchCode R Δ (.cons (.sum A B) ps) G
  | abort {Δ ps G} : BranchCode R Δ (.cons .zero ps) G
  | storeAtom {Δ q ps G} : BranchCode R Δ ps G →
      BranchCode R Δ (.cons (.atom q) ps) G
  | storeShift {Δ N ps G} : BranchCode R Δ ps G →
      BranchCode R Δ (.cons (.shift N) ps) G
  | unit {Δ} : BranchCode R Δ .empty (.neg .one)
  | pair {Δ A B} : BranchCode R Δ .empty (.neg A) →
      BranchCode R Δ .empty (.neg B) →
      BranchCode R Δ .empty (.neg (.prod A B))
  | lam {Δ A B} : BranchCode R (Δ.snoc A.erase) (.cons A .empty) (.neg B) →
      BranchCode R Δ .empty (.neg (.arr A B))
  | satShift {Δ P} : SatCode R Δ P → BranchCode R Δ .empty (.neg (.shift P))
  | satPos {Δ P} : SatCode R Δ P → BranchCode R Δ .empty (.pos P)

inductive SatCode (R : AliasResolver sig) :
    Ctx sig → Pos sig.nBases → Type where
  | inconsistent {Δ P} : SatCode R Δ P
  | done {Δ P} : SPosCode R Δ P → SatCode R Δ P
  | batch {Δ selected P} : BatchCode R Δ selected →
      BranchCode R (Pending.eraseAux selected Δ) selected (.pos P) →
      SatCode R Δ P

inductive BatchCode (R : AliasResolver sig) :
    Ctx sig → Pending sig → Type where
  | one {Δ Q} : SNegCode R Δ (.shift Q) → BatchCode R Δ (.cons Q .empty)
  | cons {Δ Q ps} : SNegCode R Δ (.shift Q) → BatchCode R Δ ps →
      BatchCode R Δ (.cons Q ps)

end

/-! ### Explicit batch-origin supply -/

/-- Raw origins for every nested selected batch encountered during coding. -/
structure BatchResultSupply (R : AliasResolver sig) where
  results : ∀ {Γ selected}, NonemptyBatchObs Γ selected →
    BatchResultAssignment R selected

/-! ### Total normalization -/

mutual

def SNegNeu.toStructuralCode (supply : BatchResultSupply R)
    (E : CodeOriginAssignment R Δ Γ) :
    SNegNeu Γ N → SNegCode R Δ N
  | .var x => .var (E.ref x)
  | .fst n => .fst (SNegNeu.toStructuralCode supply E n)
  | .snd n => .snd (SNegNeu.toStructuralCode supply E n)
  | .app n p => .app (SNegNeu.toStructuralCode supply E n)
      (SPosNeu.toStructuralCode supply E p)

def SPosNeu.toStructuralCode (supply : BatchResultSupply R)
    (E : CodeOriginAssignment R Δ Γ) :
    SPosNeu Γ P → SPosCode R Δ P
  | .atom x => .atom (E.ref x)
  | .inl p => .inl (SPosNeu.toStructuralCode supply E p)
  | .inr p => .inr (SPosNeu.toStructuralCode supply E p)
  | .shift t => .shift (SInv.toStructuralCode (Old := Γ) (New := .empty) supply E
      (CodePendingAssignment.empty R Δ) t)

def NonemptyBatchObs.toStructuralCode (supply : BatchResultSupply R)
    (E : CodeOriginAssignment R Δ Γ) :
    NonemptyBatchObs Γ selected → BatchCode R Δ selected
  | .one n => .one (SNegNeu.toStructuralCode supply E n)
  | .cons n rest => .cons (SNegNeu.toStructuralCode supply E n)
      (NonemptyBatchObs.toStructuralCode supply E rest)

def Sat.toStructuralCode (supply : BatchResultSupply R)
    (E : CodeOriginAssignment R Δ (Old.append New)) :
    Sat Old New P → SatCode R Δ P
  | .inconsistent _ => .inconsistent
  | .done v => .done (SPosNeu.toStructuralCode supply E v)
  | .batch (selected := selected) obs body =>
      let B := supply.results obs
      let E' := E.rename (Pending.weakenBase selected Δ)
      let pending' := CodePendingAssignment.boundBatch B Δ
      .batch (NonemptyBatchObs.toStructuralCode supply E obs)
        (SInv.toStructuralCode (Old := Old.append New) (New := .empty)
          supply E' pending' body)

def SInv.toStructuralCode (supply : BatchResultSupply R)
    (E : CodeOriginAssignment R Δ (Old.append New))
    (pending : CodePendingAssignment R Δ ps) :
    SInv Old New ps G → BranchCode R Δ ps G
  | .caseSum (A := A) (B := B) left right =>
      let leftE := E.rename (Rename.weaken (A := A.erase))
      let rightE := E.rename (Rename.weaken (A := B.erase))
      let leftPending := CodePendingAssignment.cons (.bound .here)
        (pending.tail.rename (Rename.weaken (A := A.erase)))
      let rightPending := CodePendingAssignment.cons (.bound .here)
        (pending.tail.rename (Rename.weaken (A := B.erase)))
      .caseSum
        (SInv.toStructuralCode supply leftE leftPending left)
        (SInv.toStructuralCode supply rightE rightPending right)
  | .abort => .abort
  | .storeAtom (q := q) t =>
      .storeAtom (SInv.toStructuralCode (Old := Old) (New := New.snoc (.atom q)) supply
        (E.snoc (S := .atom q) (pending.ref (.here))) pending.tail t)
  | .storeShift (N := N) t =>
      .storeShift (SInv.toStructuralCode (Old := Old) (New := New.snoc (.neg N)) supply
        (E.snoc (S := .neg N) (pending.ref (.here))) pending.tail t)
  | .unit => .unit
  | .pair left right => .pair
      (SInv.toStructuralCode supply E (CodePendingAssignment.empty R Δ) left)
      (SInv.toStructuralCode supply E (CodePendingAssignment.empty R Δ) right)
  | .lam (A := A) body =>
      let E' := E.rename (Rename.weaken (A := A.erase))
      let pending' := CodePendingAssignment.cons (.bound .here)
        (CodePendingAssignment.empty R (Δ.snoc A.erase))
      .lam (SInv.toStructuralCode supply E' pending' body)
  | .satShift s => .satShift (Sat.toStructuralCode supply E s)
  | .satPos s => .satPos (Sat.toStructuralCode supply E s)

end

/-! ### Free dependency API -/

mutual

def SNegCode.freeDeps {sig : Signature} {R : AliasResolver sig}
    {Δ : Ctx sig} {N : Neg sig.nBases} : SNegCode R Δ N → List (Origin sig)
  | .var x => x.freeDeps
  | .fst n | .snd n => n.freeDeps
  | .app n p => n.freeDeps ++ p.freeDeps

def SPosCode.freeDeps {sig : Signature} {R : AliasResolver sig}
    {Δ : Ctx sig} {P : Pos sig.nBases} : SPosCode R Δ P → List (Origin sig)
  | .atom x => x.freeDeps
  | .inl p | .inr p => p.freeDeps
  | .shift t => t.freeDeps

def BranchCode.freeDeps {sig : Signature} {R : AliasResolver sig}
    {Δ : Ctx sig} {ps : Pending sig} {G : Goal sig.nBases} :
    BranchCode R Δ ps G → List (Origin sig)
  | .dead | .abort | .unit => []
  | .caseSum l r | .pair l r => l.freeDeps ++ r.freeDeps
  | .storeAtom t | .storeShift t | .lam t => t.freeDeps
  | .satShift s | .satPos s => s.freeDeps

def SatCode.freeDeps {sig : Signature} {R : AliasResolver sig}
    {Δ : Ctx sig} {P : Pos sig.nBases} : SatCode R Δ P → List (Origin sig)
  | .inconsistent => []
  | .done p => p.freeDeps
  | .batch obs body => obs.freeDeps ++ body.freeDeps

def BatchCode.freeDeps {sig : Signature} {R : AliasResolver sig}
    {Δ : Ctx sig} {selected : Pending sig} :
    BatchCode R Δ selected → List (Origin sig)
  | .one n => n.freeDeps
  | .cons n rest => n.freeDeps ++ rest.freeDeps

end

/- Every free dependency exposed by a code is already a resolver terminal. -/
mutual

theorem SNegCode.freeDeps_terminal : (c : SNegCode R Δ N) →
    ∀ o : Origin sig, o ∈ c.freeDeps → R.target o = none
  | .var x => fun o ho => x.freeDeps_terminal o ho
  | .fst n | .snd n => fun o ho => n.freeDeps_terminal o ho
  | .app n p => fun o ho => by
      rcases List.mem_append.mp ho with hn | hp
      · exact n.freeDeps_terminal o hn
      · exact p.freeDeps_terminal o hp

theorem SPosCode.freeDeps_terminal : (c : SPosCode R Δ P) →
    ∀ o : Origin sig, o ∈ c.freeDeps → R.target o = none
  | .atom x => fun o ho => x.freeDeps_terminal o ho
  | .inl p | .inr p => fun o ho => p.freeDeps_terminal o ho
  | .shift t => fun o ho => t.freeDeps_terminal o ho

theorem BranchCode.freeDeps_terminal : (c : BranchCode R Δ ps G) →
    ∀ o : Origin sig, o ∈ c.freeDeps → R.target o = none
  | .dead | .abort | .unit => fun _ ho => by simp [BranchCode.freeDeps] at ho
  | .caseSum left right | .pair left right => fun o ho => by
      rcases List.mem_append.mp ho with hl | hr
      · exact left.freeDeps_terminal o hl
      · exact right.freeDeps_terminal o hr
  | .storeAtom t | .storeShift t | .lam t => fun o ho => t.freeDeps_terminal o ho
  | .satShift s | .satPos s => fun o ho => s.freeDeps_terminal o ho

theorem SatCode.freeDeps_terminal : (c : SatCode R Δ P) →
    ∀ o : Origin sig, o ∈ c.freeDeps → R.target o = none
  | .inconsistent => fun _ ho => by simp [SatCode.freeDeps] at ho
  | .done p => fun o ho => p.freeDeps_terminal o ho
  | .batch obs body => fun o ho => by
      rcases List.mem_append.mp ho with hobs | hbody
      · exact obs.freeDeps_terminal o hobs
      · exact body.freeDeps_terminal o hbody

theorem BatchCode.freeDeps_terminal : (c : BatchCode R Δ selected) →
    ∀ o : Origin sig, o ∈ c.freeDeps → R.target o = none
  | .one n => fun o ho => n.freeDeps_terminal o ho
  | .cons n rest => fun o ho => by
      rcases List.mem_append.mp ho with hn | hrest
      · exact n.freeDeps_terminal o hn
      · exact rest.freeDeps_terminal o hrest

end

def BatchCode.length : BatchCode R Δ selected → Nat
  | .one _ => 1
  | .cons _ rest => rest.length + 1

def BranchCode.Scoped {sig : Signature} {R : AliasResolver sig}
    {Δ : Ctx sig} {ps : Pending sig} {G : Goal sig.nBases}
    (pre : OriginScope) (c : BranchCode R Δ ps G) : Prop :=
  ∀ (o : Origin sig), o ∈ c.freeDeps → pre.Contains o

def SNegCode.Scoped {sig : Signature} {R : AliasResolver sig}
    {Δ : Ctx sig} {N : Neg sig.nBases}
    (pre : OriginScope) (c : SNegCode R Δ N) : Prop :=
  ∀ (o : Origin sig), o ∈ c.freeDeps → pre.Contains o

def SPosCode.Scoped {sig : Signature} {R : AliasResolver sig}
    {Δ : Ctx sig} {P : Pos sig.nBases}
    (pre : OriginScope) (c : SPosCode R Δ P) : Prop :=
  ∀ (o : Origin sig), o ∈ c.freeDeps → pre.Contains o

def SatCode.Scoped {sig : Signature} {R : AliasResolver sig}
    {Δ : Ctx sig} {P : Pos sig.nBases}
    (pre : OriginScope) (c : SatCode R Δ P) : Prop :=
  ∀ (o : Origin sig), o ∈ c.freeDeps → pre.Contains o

def BatchCode.Scoped {sig : Signature} {R : AliasResolver sig}
    {Δ : Ctx sig} {selected : Pending sig}
    (pre : OriginScope) (c : BatchCode R Δ selected) : Prop :=
  ∀ (o : Origin sig), o ∈ c.freeDeps → pre.Contains o

/- Normalization preserves the caller's free-origin scope.  Local binders are
represented by `CanonRef.bound`, so they create no free dependency. -/
mutual

theorem SNegNeu.toStructuralCode_scoped (supply : BatchResultSupply R)
    (E : CodeOriginAssignment R Δ Γ) : (n : SNegNeu Γ N) → E.Scoped pre →
    (n.toStructuralCode supply E).Scoped pre
  | .var x => fun hE o ho => CanonRef.scoped_of_mem_freeDeps (hE x) o ho
  | .fst n | .snd n => fun hE => n.toStructuralCode_scoped supply E hE
  | .app n p => fun hE o ho => by
      rcases List.mem_append.mp ho with hn | hp
      · exact n.toStructuralCode_scoped supply E hE o hn
      · exact p.toStructuralCode_scoped supply E hE o hp

theorem SPosNeu.toStructuralCode_scoped (supply : BatchResultSupply R)
    (E : CodeOriginAssignment R Δ Γ) : (p : SPosNeu Γ P) → E.Scoped pre →
    (p.toStructuralCode supply E).Scoped pre
  | .atom x => fun hE o ho => CanonRef.scoped_of_mem_freeDeps (hE x) o ho
  | .inl p | .inr p => fun hE => p.toStructuralCode_scoped supply E hE
  | .shift t => fun hE =>
      SInv.toStructuralCode_scoped (Old := Γ) (New := .empty) supply E
        t (CodePendingAssignment.empty R Δ)
        hE CodePendingAssignment.empty_scoped

theorem NonemptyBatchObs.toStructuralCode_scoped (supply : BatchResultSupply R)
    (E : CodeOriginAssignment R Δ Γ) :
    (obs : NonemptyBatchObs Γ selected) → E.Scoped pre →
      (obs.toStructuralCode supply E).Scoped pre
  | .one n => fun hE => n.toStructuralCode_scoped supply E hE
  | .cons n rest => fun hE o ho => by
      rcases List.mem_append.mp ho with hn | hrest
      · exact n.toStructuralCode_scoped supply E hE o hn
      · exact rest.toStructuralCode_scoped supply E hE o hrest

theorem Sat.toStructuralCode_scoped (supply : BatchResultSupply R)
    (E : CodeOriginAssignment R Δ (Old.append New)) : (s : Sat Old New P) →
    E.Scoped pre → (s.toStructuralCode supply E).Scoped pre
  | .inconsistent _ => fun _ _ ho => (List.not_mem_nil ho).elim
  | .done p => fun hE => p.toStructuralCode_scoped supply E hE
  | .batch (selected := selected) obs body => fun hE o ho => by
      rcases List.mem_append.mp ho with hobs | hbody
      · exact obs.toStructuralCode_scoped supply E hE o hobs
      · let B := supply.results obs
        let E' := E.rename (Pending.weakenBase selected Δ)
        let pending' := CodePendingAssignment.boundBatch B Δ
        exact SInv.toStructuralCode_scoped (Old := Old.append New) (New := .empty)
          supply E' body pending'
          (CodeOriginAssignment.rename_scoped hE _)
          (CodePendingAssignment.boundBatch_scoped B Δ) o hbody

theorem SInv.toStructuralCode_scoped (supply : BatchResultSupply R)
    (E : CodeOriginAssignment R Δ (Old.append New)) :
    (t : SInv Old New ps G) → (pending : CodePendingAssignment R Δ ps) →
    E.Scoped pre → pending.Scoped pre →
      (t.toStructuralCode supply E pending).Scoped pre
  | .caseSum (A := A) (B := B) left right => fun pending hE hpending o ho => by
      rcases List.mem_append.mp ho with hleft | hright
      · let ρ : Rename _ Δ (Δ.snoc A.erase) := Rename.weaken
        exact left.toStructuralCode_scoped supply (E.rename ρ)
          (CodePendingAssignment.cons (.bound .here) (pending.tail.rename ρ))
          (CodeOriginAssignment.rename_scoped hE ρ)
          (CodePendingAssignment.cons_scoped (by trivial)
            (CodePendingAssignment.rename_scoped
              (CodePendingAssignment.tail_scoped hpending) ρ)) o hleft
      · let ρ : Rename _ Δ (Δ.snoc B.erase) := Rename.weaken
        exact right.toStructuralCode_scoped supply (E.rename ρ)
          (CodePendingAssignment.cons (.bound .here) (pending.tail.rename ρ))
          (CodeOriginAssignment.rename_scoped hE ρ)
          (CodePendingAssignment.cons_scoped (by trivial)
            (CodePendingAssignment.rename_scoped
              (CodePendingAssignment.tail_scoped hpending) ρ)) o hright
  | .abort => fun _ _ _ _ ho => (List.not_mem_nil ho).elim
  | .storeAtom (q := q) t => fun pending hE hpending => by
      let E' : CodeOriginAssignment R Δ (Old.append (New.snoc (.atom q))) :=
        E.snoc (S := .atom q) (pending.ref .here)
      have hE' : E'.Scoped pre := by
        intro S x
        cases x with
        | here => exact hpending .here
        | there x => exact hE x
      have ht := t.toStructuralCode_scoped supply E' pending.tail hE'
        (CodePendingAssignment.tail_scoped hpending)
      simpa only [SInv.toStructuralCode, BranchCode.Scoped,
        BranchCode.freeDeps] using ht
  | .storeShift (N := N) t => fun pending hE hpending => by
      let E' : CodeOriginAssignment R Δ (Old.append (New.snoc (.neg N))) :=
        E.snoc (S := .neg N) (pending.ref .here)
      have hE' : E'.Scoped pre := by
        intro S x
        cases x with
        | here => exact hpending .here
        | there x => exact hE x
      have ht := t.toStructuralCode_scoped supply E' pending.tail hE'
        (CodePendingAssignment.tail_scoped hpending)
      simpa only [SInv.toStructuralCode, BranchCode.Scoped,
        BranchCode.freeDeps] using ht
  | .unit => fun _ _ _ _ ho => (List.not_mem_nil ho).elim
  | .pair left right => fun _ hE _ o ho => by
      rcases List.mem_append.mp ho with hleft | hright
      · exact left.toStructuralCode_scoped supply E
          (CodePendingAssignment.empty R Δ) hE
          CodePendingAssignment.empty_scoped o hleft
      · exact right.toStructuralCode_scoped supply E
          (CodePendingAssignment.empty R Δ) hE
          CodePendingAssignment.empty_scoped o hright
  | .lam (A := A) body => fun pending hE _ => by
      let ρ : Rename _ Δ (Δ.snoc A.erase) := Rename.weaken
      let pending' := CodePendingAssignment.cons (.bound .here)
        (CodePendingAssignment.empty R (Δ.snoc A.erase))
      have hbody := body.toStructuralCode_scoped supply (E.rename ρ) pending'
        (CodeOriginAssignment.rename_scoped hE ρ)
        (CodePendingAssignment.cons_scoped (by trivial)
          CodePendingAssignment.empty_scoped)
      have hnorm : SInv.toStructuralCode supply E
          pending (.lam body) =
          .lam (SInv.toStructuralCode supply (E.rename ρ) pending' body) := rfl
      rw [hnorm]
      intro o ho
      exact hbody o ho
  | .satShift s => fun _ hE _ => s.toStructuralCode_scoped supply E hE
  | .satPos s => fun _ hE _ => s.toStructuralCode_scoped supply E hE

end

/-! ### Adversarial fixtures -/

namespace PairStructuralCodeFixtures

open PairTraceFixtures

abbrev P : Pos TwoGenSig.nBases := .atom q0
abbrev ShiftP : Neg TwoGenSig.nBases := .shift P

def idR : AliasResolver TwoGenSig := AliasResolver.identity TwoGenSig

def supply (R : AliasResolver TwoGenSig) : BatchResultSupply R where
  results := fun {_ _} _ =>
    { origin := fun {Q} _ => rootOrigin TwoGenSig Q.erase 900 0 }

def originA : TypedOrigin TwoGenSig Q := rootOrigin TwoGenSig Q 100 0
def originB : TypedOrigin TwoGenSig Q := rootOrigin TwoGenSig Q 101 0
def refA : ResolvedRef idR Q := ResolvedRef.of idR originA
def refB : ResolvedRef idR Q := ResolvedRef.of idR originB

theorem refA_ne_refB : refA ≠ refB := by
  intro h
  have heq := (ResolvedRef.of_eq_iff idR originA originB).mp h
  unfold AliasResolver.Equivalent at heq
  rw [AliasResolver.resolve_eq_self_of_target_eq_none,
    AliasResolver.resolve_eq_self_of_target_eq_none] at heq
  · exact (by decide : originA.raw ≠ originB.raw) heq
  · rfl
  · rfl

abbrev ObsCtx : StableCtx TwoGenSig :=
  ((StableCtx.empty : StableCtx TwoGenSig).snoc (.neg ShiftP)).snoc (.neg ShiftP)

def obsAssignment : OriginAssignment idR ObsCtx :=
  ((OriginAssignment.empty idR).snoc (S := .neg ShiftP) refA).snoc
    (S := .neg ShiftP) refB

def newestObs : SNegNeu ObsCtx ShiftP := .var .here
def olderObs : SNegNeu ObsCtx ShiftP := .var (.there .here)

/-- Equal result types do not identify different exact neutral sources. -/
theorem newest_older_distinct :
    newestObs.toStructuralCode (supply idR) (CodeOriginAssignment.ofOrigin obsAssignment) ≠
      olderObs.toStructuralCode (supply idR)
        (CodeOriginAssignment.ofOrigin obsAssignment) := by
  intro h
  have href := congrArg (fun c => match c with
    | SNegCode.var r => some r
    | _ => none) h
  exact (Ne.symm refA_ne_refB) (CanonRef.free.inj (Option.some.inj href))

abbrev SameProd : Neg TwoGenSig.nBases := .prod ShiftP ShiftP
abbrev ProdCtx : StableCtx TwoGenSig :=
  (StableCtx.empty : StableCtx TwoGenSig).snoc (.neg SameProd)

def prodOrigin : TypedOrigin TwoGenSig SameProd.erase :=
  rootOrigin TwoGenSig SameProd.erase 102 0
def prodAssignment : OriginAssignment idR ProdCtx :=
  (OriginAssignment.empty idR).snoc (S := .neg SameProd)
    (ResolvedRef.of idR prodOrigin)
def prodNeu : SNegNeu ProdCtx SameProd := .var .here

/-- `fst p` and `snd p` stay different even when both results have one type. -/
theorem fst_snd_same_result_distinct :
    (SNegNeu.fst prodNeu).toStructuralCode (supply idR)
        (CodeOriginAssignment.ofOrigin prodAssignment) ≠
      (SNegNeu.snd prodNeu).toStructuralCode (supply idR)
        (CodeOriginAssignment.ofOrigin prodAssignment) := by
  intro h
  cases h

abbrev FnN : Neg TwoGenSig.nBases := .arr P ShiftP
abbrev AppCtx : StableCtx TwoGenSig :=
  (((StableCtx.empty : StableCtx TwoGenSig).snoc (.neg FnN)).snoc (.atom q0)).snoc
    (.atom q0)

def fnOrigin : TypedOrigin TwoGenSig FnN.erase := rootOrigin TwoGenSig FnN.erase 103 0
def appAssignment : OriginAssignment idR AppCtx :=
  (((OriginAssignment.empty idR).snoc (S := .neg FnN)
      (ResolvedRef.of idR fnOrigin)).snoc (S := .atom q0) refA).snoc
    (S := .atom q0) refB
def fnNeu : SNegNeu AppCtx FnN := .var (.there (.there .here))
def appX : SNegNeu AppCtx ShiftP := .app fnNeu (.atom (.there .here))
def appY : SNegNeu AppCtx ShiftP := .app fnNeu (.atom .here)

def canonRefId? {A : Object TwoGenSig.nBases} :
    CanonRef idR .empty A → Option Nat
  | .bound _ => none
  | .free r => some r.origin.raw.id

def appAtomId? : SNegCode idR .empty ShiftP → Option Nat
  | .app _ (.atom r) => canonRefId? r
  | _ => none

abbrev AppDelta : Ctx TwoGenSig := AppCtx.erase

def appBoundAssignment : CodeOriginAssignment idR AppDelta AppCtx where
  ref x := .bound x.erase

def appXCode : SNegCode idR AppDelta ShiftP :=
  .app (.var (.bound (.there (.there .here))))
    (.atom (.bound (.there .here)))

def appYCode : SNegCode idR AppDelta ShiftP :=
  .app (.var (.bound (.there (.there .here)))) (.atom (.bound .here))

theorem appX_toStructuralCode :
    appX.toStructuralCode (supply idR)
        appBoundAssignment = appXCode := rfl

theorem appY_toStructuralCode :
    appY.toStructuralCode (supply idR)
        appBoundAssignment = appYCode := rfl

theorem appXCode_ne_appYCode : appXCode ≠ appYCode := by
  unfold appXCode appYCode
  intro h
  cases h

/-- Exact application keys retain their positive argument source. -/
theorem app_distinct_arguments :
    appX.toStructuralCode (supply idR) appBoundAssignment ≠
      appY.toStructuralCode (supply idR) appBoundAssignment := by
  rw [appX_toStructuralCode, appY_toStructuralCode]
  exact appXCode_ne_appYCode

abbrev AliasCtx : StableCtx TwoGenSig :=
  (StableCtx.empty : StableCtx TwoGenSig).snoc (.neg ShiftP)
def storeAssignment : OriginAssignment chainResolver AliasCtx :=
  (OriginAssignment.empty chainResolver).snoc (S := .neg ShiftP)
    (ResolvedRef.of chainResolver store2)
def rootAssignment : OriginAssignment chainResolver AliasCtx :=
  (OriginAssignment.empty chainResolver).snoc (S := .neg ShiftP)
    (ResolvedRef.of chainResolver atom0)
def aliasNeu : SNegNeu AliasCtx ShiftP := .var .here

def asShiftOrigin (x : TypedOrigin TwoGenSig Q) :
    TypedOrigin TwoGenSig ShiftP.erase :=
  ⟨x.raw, by
    change x.raw.ty = Object.base PairTraceFixtures.q0
    exact x.type_eq⟩

/-- Raw store aliases disappear before structural coding. -/
theorem alias_chain_normalizes_equal :
    aliasNeu.toStructuralCode (supply chainResolver)
        (CodeOriginAssignment.ofOrigin storeAssignment) =
      aliasNeu.toStructuralCode (supply chainResolver)
        (CodeOriginAssignment.ofOrigin rootAssignment) := by
  have href : ResolvedRef.of chainResolver (asShiftOrigin store2) =
      ResolvedRef.of chainResolver (asShiftOrigin atom0) := by
    rw [ResolvedRef.of_eq_iff]
    unfold AliasResolver.Equivalent
    change chainResolver.resolve store2.raw = chainResolver.resolve atom0.raw
    exact congrArg (fun r => r.origin.raw)
      (PairOriginFixtures.alias_chain_collapses.1.trans
        PairOriginFixtures.alias_chain_collapses.2)
  change SNegCode.var (N := ShiftP)
      (CanonRef.free (ResolvedRef.of chainResolver (asShiftOrigin store2))) =
    SNegCode.var (N := ShiftP)
      (CanonRef.free (ResolvedRef.of chainResolver (asShiftOrigin atom0)))
  rw [href]

def batchAB : NonemptyBatchObs ObsCtx (.cons P (.cons P .empty)) :=
  .cons newestObs (.one olderObs)
def batchBA : NonemptyBatchObs ObsCtx (.cons P (.cons P .empty)) :=
  .cons olderObs (.one newestObs)
def batchA : NonemptyBatchObs ObsCtx (.cons P .empty) := .one newestObs

/-- Batch codes preserve literal entry order. -/
theorem batch_order_distinct :
    batchAB.toStructuralCode (supply idR) (CodeOriginAssignment.ofOrigin obsAssignment) ≠
      batchBA.toStructuralCode (supply idR)
        (CodeOriginAssignment.ofOrigin obsAssignment) := by
  intro h
  have href := congrArg (fun c : BatchCode idR .empty (.cons P (.cons P .empty)) =>
    match c with
    | .cons (.var r) _ => some r
    | _ => none) h
  exact (Ne.symm refA_ne_refB) (CanonRef.free.inj (Option.some.inj href))

/-- Batch codes preserve multiplicity as well as membership. -/
theorem duplicate_batch_not_singleton :
    (batchAB.toStructuralCode (supply idR)
        (CodeOriginAssignment.ofOrigin obsAssignment)).length ≠
      (batchA.toStructuralCode (supply idR)
        (CodeOriginAssignment.ofOrigin obsAssignment)).length := by
  decide

def zeroOlder : SNegNeu
    (((StableCtx.empty : StableCtx TwoGenSig).snoc (.neg (.shift .zero))).snoc
      (.neg (.shift .zero))) (.shift .zero) := .var (.there .here)
def zeroNewest : SNegNeu
    (((StableCtx.empty : StableCtx TwoGenSig).snoc (.neg (.shift .zero))).snoc
      (.neg (.shift .zero))) (.shift .zero) := .var .here
abbrev ZeroCtx : StableCtx TwoGenSig :=
  ((StableCtx.empty : StableCtx TwoGenSig).snoc (.neg (.shift .zero))).snoc
    (.neg (.shift .zero))
def zeroRefA : ResolvedRef idR Object.never :=
  ResolvedRef.of idR (rootOrigin TwoGenSig .never 104 0)
def zeroRefB : ResolvedRef idR Object.never :=
  ResolvedRef.of idR (rootOrigin TwoGenSig .never 105 0)
def zeroAssignment : OriginAssignment idR ZeroCtx :=
  ((OriginAssignment.empty idR).snoc (S := .neg (.shift .zero)) zeroRefA).snoc
    (S := .neg (.shift .zero)) zeroRefB
def inconsistentOlder : Sat ZeroCtx .empty P := .inconsistent zeroOlder
def inconsistentNewest : Sat ZeroCtx .empty P := .inconsistent zeroNewest

/-- The chosen proof of local inconsistency is absent from the code. -/
theorem inconsistent_witness_irrelevant :
    Sat.toStructuralCode (Old := ZeroCtx) (New := .empty) (supply idR)
        (CodeOriginAssignment.ofOrigin zeroAssignment) inconsistentOlder =
      Sat.toStructuralCode (Old := ZeroCtx) (New := .empty) (supply idR)
        (CodeOriginAssignment.ofOrigin zeroAssignment) inconsistentNewest := rfl

def shiftedUnit : SPosNeu (sig := TwoGenSig) .empty (.shift .one) := .shift .unit
def sumLeft : SPosNeu (sig := TwoGenSig) .empty (.sum (.shift .one) (.shift .one)) :=
  .inl shiftedUnit
def sumRight : SPosNeu (sig := TwoGenSig) .empty (.sum (.shift .one) (.shift .one)) :=
  .inr shiftedUnit

/-- Opposite live coproduct tags remain a structural mismatch. -/
theorem opposite_sum_tags_distinct :
    sumLeft.toStructuralCode (supply idR)
        (CodeOriginAssignment.ofOrigin (OriginAssignment.empty idR)) ≠
      sumRight.toStructuralCode (supply idR)
        (CodeOriginAssignment.ofOrigin (OriginAssignment.empty idR)) := by
  intro h
  cases h

end PairStructuralCodeFixtures

end Gimbal.Equality.Scherer
