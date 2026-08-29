/-
  Executable prototype for ordinary positive cut in the Scherer core.

  This module deliberately contains no `Tm` recursion and no soundness proof.
  Its only purpose is to falsify (or validate) the termination architecture for
  the direct producer before that larger campaign starts.
-/

import Gimbal.Equality.Scherer.Renaming
import Gimbal.Equality.Scherer.StrongRetrieval

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Formula and syntax sizes -/

mutual
def posCutSize {n : Nat} : Pos n → Nat
  | .atom _ | .zero => 1
  | .sum P Q => posCutSize P + posCutSize Q + 1
  | .shift N => negCutSize N + 1

def negCutSize {n : Nat} : Neg n → Nat
  | .one => 1
  | .prod N M => negCutSize N + negCutSize M + 1
  | .arr P N => posCutSize P + negCutSize N + 1
  | .shift P => posCutSize P + 1
end

mutual
def NegNeu.nodeSize {Γ : StableCtx sig} {N : Neg sig.nBases} : NegNeu Γ N → Nat
  | .var _ => 1
  | .fst n | .snd n => n.nodeSize + 1
  | .app n p => n.nodeSize + p.nodeSize + 1

def PosNeu.nodeSize {Γ : StableCtx sig} {P : Pos sig.nBases} : PosNeu Γ P → Nat
  | .atom _ => 1
  | .inl p | .inr p => p.nodeSize + 1
  | .shift t => t.nodeSize + 1

def Foc.nodeSize {Γ : StableCtx sig} {P : Pos sig.nBases} : Foc Γ P → Nat
  | .up p => p.nodeSize + 1
  | .letShift n t => n.nodeSize + t.nodeSize + 1

def Inv.nodeSize {Γ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases} :
    Inv Γ ps G → Nat
  | .caseSum l r => l.nodeSize + r.nodeSize + 1
  | .abort => 1
  | .storeAtom t | .storeShift t => t.nodeSize + 1
  | .unit => 1
  | .pair t u => t.nodeSize + u.nodeSize + 1
  | .lam t => t.nodeSize + 1
  | .focusShift f | .focusPos f => f.nodeSize + 1
end

/-! ### Stable structural renamings -/

namespace StableRename

def exchange {Γ : StableCtx sig} {S T : StableTy sig.nBases} :
    StableRename (Γ.snoc S |>.snoc T) (Γ.snoc T |>.snoc S)
  | _, .here => .there .here
  | _, .there .here => .here
  | _, .there (.there x) => .there (.there x)

def diag {Γ : StableCtx sig} {S : StableTy sig.nBases} :
    StableRename (Γ.snoc S |>.snoc S) (Γ.snoc S)
  | _, .here => .here
  | _, .there .here => .here
  | _, .there (.there x) => .there x

def replaceNewestAtom {Γ : StableCtx sig} {q : Fin sig.nBases}
    (x : StableVar Γ (.atom q)) : StableRename (Γ.snoc (.atom q)) Γ
  | _, .here => x
  | _, .there y => y

def replaceNewestNeg {Γ : StableCtx sig} {N : Neg sig.nBases}
    (x : StableVar Γ (.neg N)) : StableRename (Γ.snoc (.neg N)) Γ
  | _, .here => x
  | _, .there y => y

end StableRename

/-! ### Identity expansion and pending positive reflection -/

mutual
def etaNeg {Γ : StableCtx sig} :
    (N : Neg sig.nBases) → NegNeu Γ N → Inv Γ .empty (.neg N)
  | .one, _ => .unit
  | .prod N M, n => .pair (etaNeg N (.fst n)) (etaNeg M (.snd n))
  | .arr P N, n =>
      .lam (withPendingPos P fun ρ p =>
        etaNeg N (.app (NegNeu.rename ρ n) p))
  | .shift P, n =>
      .focusShift (.letShift n
        (withPendingPos P fun _ p => .focusPos (.up p)))

def withPendingPos {Γ : StableCtx sig} {G : Goal sig.nBases}
    (P : Pos sig.nBases)
    (k : ∀ {Δ : StableCtx sig}, StableRename Γ Δ → PosNeu Δ P → Inv Δ .empty G) :
    Inv Γ (.cons P .empty) G :=
  match P with
  | .atom _ => .storeAtom (k StableRename.weaken (.atom .here))
  | .zero => .abort
  | .sum A B =>
      .caseSum
        (withPendingPos A fun ρ p => k ρ (.inl p))
        (withPendingPos B fun ρ p => k ρ (.inr p))
  | .shift N =>
      .storeShift (k StableRename.weaken (.shift (etaNeg N (.var .here))))
end

def NegNeu.eta {Γ : StableCtx sig} {N : Neg sig.nBases}
    (n : NegNeu Γ N) : Inv Γ .empty (.neg N) :=
  etaNeg N n

/-! ### Goal maps through pending inversion -/

def Inv.pendingFst {Γ : StableCtx sig} {ps : Pending sig} {A B : Neg sig.nBases} :
    Inv Γ ps (.neg (.prod A B)) → Inv Γ ps (.neg A)
  | .caseSum l r => .caseSum l.pendingFst r.pendingFst
  | .abort => .abort
  | .storeAtom t => .storeAtom t.pendingFst
  | .storeShift t => .storeShift t.pendingFst
  | .pair t _ => t

def Inv.pendingSnd {Γ : StableCtx sig} {ps : Pending sig} {A B : Neg sig.nBases} :
    Inv Γ ps (.neg (.prod A B)) → Inv Γ ps (.neg B)
  | .caseSum l r => .caseSum l.pendingSnd r.pendingSnd
  | .abort => .abort
  | .storeAtom t => .storeAtom t.pendingSnd
  | .storeShift t => .storeShift t.pendingSnd
  | .pair _ u => u

def Inv.pendingShiftToPos {Γ : StableCtx sig} {ps : Pending sig}
    {P : Pos sig.nBases} :
    Inv Γ ps (.neg (.shift P)) → Inv Γ ps (.pos P)
  | .caseSum l r => .caseSum l.pendingShiftToPos r.pendingShiftToPos
  | .abort => .abort
  | .storeAtom t => .storeAtom t.pendingShiftToPos
  | .storeShift t => .storeShift t.pendingShiftToPos
  | .focusShift f => .focusPos f

def StrongPos.rename {Γ Δ : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Γ Δ) : StrongPos Γ P → StrongPos Δ P
  | .negVar x => .negVar (ρ x)
  | .atomVar x => .atomVar (ρ x)
  | .inl p => .inl (StrongPos.rename ρ p)
  | .inr p => .inr (StrongPos.rename ρ p)

def cutStrong {Γ : StableCtx sig} {P : Pos sig.nBases} {G : Goal sig.nBases} :
    StrongPos Γ P → Inv Γ (.cons P .empty) G → Inv Γ .empty G
  | .atomVar x, k =>
      Inv.rename (StableRename.replaceNewestAtom x) (Inv.asStoreAtom k)
  | .negVar x, k =>
      Inv.rename (StableRename.replaceNewestNeg x) (Inv.asStoreShift k)
  | .inl p, k => cutStrong p (Inv.asCaseSum k).1
  | .inr p, k => cutStrong p (Inv.asCaseSum k).2

def withPendingStrong {Γ : StableCtx sig} {G : Goal sig.nBases}
    (P : Pos sig.nBases)
    (k : ∀ {Δ : StableCtx sig}, StableRename Γ Δ →
      (p : PosNeu Δ P) → StrongPos Δ P → Inv Δ .empty G) :
    Inv Γ (.cons P .empty) G :=
  match P with
  | .atom _ =>
      .storeAtom (k StableRename.weaken (.atom .here) (.atomVar .here))
  | .zero => .abort
  | .sum A B =>
      .caseSum
        (withPendingStrong A fun ρ p sp => k ρ (.inl p) (.inl sp))
        (withPendingStrong B fun ρ p sp => k ρ (.inr p) (.inr sp))
  | .shift N =>
      .storeShift (k StableRename.weaken (.shift (etaNeg N (.var .here)))
        (.negVar .here))

def pendingAppStrong {Γ : StableCtx sig} {ps : Pending sig}
    {A : Pos sig.nBases} {N : Neg sig.nBases}
    (f : Inv Γ ps (.neg (.arr A N))) (a : StrongPos Γ A) : Inv Γ ps (.neg N) :=
  match f with
  | .caseSum l r => .caseSum (pendingAppStrong l a) (pendingAppStrong r a)
  | .abort => .abort
  | .storeAtom t =>
      .storeAtom (pendingAppStrong t (StrongPos.rename StableRename.weaken a))
  | .storeShift t =>
      .storeShift (pendingAppStrong t (StrongPos.rename StableRename.weaken a))
  | .lam body => cutStrong a body

def pendingAppWith
    (bind : ∀ {Γ : StableCtx sig} {qs : Pending sig} {P : Pos sig.nBases}
      {G : Goal sig.nBases},
      Inv Γ qs (.pos P) → Inv Γ (.cons P .empty) G → Inv Γ qs G)
    {Γ : StableCtx sig} {ps : Pending sig} {A : Pos sig.nBases}
    {N : Neg sig.nBases}
    (f : Inv Γ ps (.neg (.arr A N))) (a : PosNeu Γ A) : Inv Γ ps (.neg N) :=
  match f with
  | .caseSum l r => .caseSum (pendingAppWith bind l a) (pendingAppWith bind r a)
  | .abort => .abort
  | .storeAtom t => .storeAtom (pendingAppWith bind t (PosNeu.weaken a))
  | .storeShift t => .storeShift (pendingAppWith bind t (PosNeu.weaken a))
  | .lam body => bind (.focusPos (.up a)) body

/-! ### Principal positive cut -/

inductive NegSubstResult (Γ : StableCtx sig) (Cut : Neg sig.nBases) :
    Neg sig.nBases → Type where
  | neu {N} : NegNeu Γ N → NegSubstResult Γ Cut N
  | value {N} : Inv Γ .empty (.neg N) → negCutSize N ≤ negCutSize Cut →
      NegSubstResult Γ Cut N

private inductive RenameSizeCall (sig : Signature) : Type 1 where
  | neu {Γ Δ : StableCtx sig} {N : Neg sig.nBases}
      (ρ : StableRename Γ Δ) (n : NegNeu Γ N)
  | pos {Γ Δ : StableCtx sig} {P : Pos sig.nBases}
      (ρ : StableRename Γ Δ) (p : PosNeu Γ P)
  | foc {Γ Δ : StableCtx sig} {P : Pos sig.nBases}
      (ρ : StableRename Γ Δ) (f : Foc Γ P)
  | inv {Γ Δ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
      (ρ : StableRename Γ Δ) (t : Inv Γ ps G)

private def RenameSizeCall.Result : RenameSizeCall sig → Prop
  | .neu ρ n => (n.rename ρ).nodeSize = n.nodeSize
  | .pos ρ p => (p.rename ρ).nodeSize = p.nodeSize
  | .foc ρ f => (f.rename ρ).nodeSize = f.nodeSize
  | .inv ρ t => (t.rename ρ).nodeSize = t.nodeSize

private def RenameSizeCall.measure : RenameSizeCall sig → Nat
  | .neu _ n => n.nodeSize
  | .pos _ p => p.nodeSize
  | .foc _ f => f.nodeSize
  | .inv _ t => t.nodeSize

private theorem renameSizeEval : (c : RenameSizeCall sig) → c.Result
  | .neu _ (.var _) => rfl
  | .neu ρ (.fst n) => by
      simpa [RenameSizeCall.Result, NegNeu.rename, NegNeu.nodeSize] using
        renameSizeEval (.neu ρ n)
  | .neu ρ (.snd n) => by
      simpa [RenameSizeCall.Result, NegNeu.rename, NegNeu.nodeSize] using
        renameSizeEval (.neu ρ n)
  | .neu ρ (.app n p) => by
      have hn := renameSizeEval (.neu ρ n)
      have hp := renameSizeEval (.pos ρ p)
      simp [RenameSizeCall.Result, NegNeu.rename, NegNeu.nodeSize] at hn hp ⊢
      omega
  | .pos _ (.atom _) => rfl
  | .pos ρ (.inl p) => by
      simpa [RenameSizeCall.Result, PosNeu.rename, PosNeu.nodeSize] using
        renameSizeEval (.pos ρ p)
  | .pos ρ (.inr p) => by
      simpa [RenameSizeCall.Result, PosNeu.rename, PosNeu.nodeSize] using
        renameSizeEval (.pos ρ p)
  | .pos ρ (.shift t) => by
      simpa [RenameSizeCall.Result, PosNeu.rename, PosNeu.nodeSize] using
        renameSizeEval (.inv ρ t)
  | .foc ρ (.up p) => by
      simpa [RenameSizeCall.Result, Foc.rename, Foc.nodeSize] using
        renameSizeEval (.pos ρ p)
  | .foc ρ (.letShift n t) => by
      have hn := renameSizeEval (.neu ρ n)
      have ht := renameSizeEval (.inv ρ t)
      simp [RenameSizeCall.Result, Foc.rename, Foc.nodeSize] at hn ht ⊢
      omega
  | .inv ρ (.caseSum l r) => by
      have hl := renameSizeEval (.inv ρ l)
      have hr := renameSizeEval (.inv ρ r)
      simp [RenameSizeCall.Result, Inv.rename, Inv.nodeSize] at hl hr ⊢
      omega
  | .inv _ .abort => rfl
  | .inv ρ (.storeAtom t) => by
      simpa [RenameSizeCall.Result, Inv.rename, Inv.nodeSize] using
        renameSizeEval (.inv ρ.ext t)
  | .inv ρ (.storeShift t) => by
      simpa [RenameSizeCall.Result, Inv.rename, Inv.nodeSize] using
        renameSizeEval (.inv ρ.ext t)
  | .inv _ .unit => rfl
  | .inv ρ (.pair t u) => by
      have ht := renameSizeEval (.inv ρ t)
      have hu := renameSizeEval (.inv ρ u)
      simp [RenameSizeCall.Result, Inv.rename, Inv.nodeSize] at ht hu ⊢
      omega
  | .inv ρ (.lam t) => by
      simpa [RenameSizeCall.Result, Inv.rename, Inv.nodeSize] using
        renameSizeEval (.inv ρ t)
  | .inv ρ (.focusShift f) => by
      simpa [RenameSizeCall.Result, Inv.rename, Inv.nodeSize] using
        renameSizeEval (.foc ρ f)
  | .inv ρ (.focusPos f) => by
      simpa [RenameSizeCall.Result, Inv.rename, Inv.nodeSize] using
        renameSizeEval (.foc ρ f)
termination_by c => c.measure
decreasing_by
  all_goals simp [RenameSizeCall.measure, NegNeu.nodeSize, PosNeu.nodeSize,
    Foc.nodeSize, Inv.nodeSize]
  <;> omega

@[simp] theorem Inv.nodeSize_rename {Γ Δ : StableCtx sig}
    {ps : Pending sig} {G : Goal sig.nBases}
    (ρ : StableRename Γ Δ) (t : Inv Γ ps G) :
    (t.rename ρ).nodeSize = t.nodeSize :=
  renameSizeEval (.inv ρ t)

private def composeShiftSized
    {P : Pos sig.nBases}
    (bound : Nat)
    (bind : ∀ {Γ : StableCtx sig} {qs : Pending sig} {G : Goal sig.nBases},
      (d : Inv Γ qs (.pos P)) → d.nodeSize ≤ bound →
      Inv Γ (.cons P .empty) G → Inv Γ qs G)
    {Γ : StableCtx sig} {Q : Pos sig.nBases} :
    (G : Goal sig.nBases) →
    NegNeu Γ (.shift Q) → (d : Inv Γ (.cons Q .empty) (.pos P)) →
      (h : d.nodeSize ≤ bound) → Inv Γ (.cons P .empty) G → Inv Γ .empty G
  | .pos _, n, d, h, k => .focusPos (.letShift n (bind d h k))
  | .neg .one, _, _, _, _ => .unit
  | .neg (.prod A B), n, d, h, k =>
      .pair
        (composeShiftSized bound bind (.neg A) n d h k.pendingFst)
        (composeShiftSized bound bind (.neg B) n d h k.pendingSnd)
  | .neg (.arr A N), n, d, h, k =>
      .lam (withPendingStrong A fun ρ _ sp =>
        composeShiftSized bound bind (.neg N) (NegNeu.rename ρ n)
          (Inv.rename ρ d) (by simpa using h)
          (pendingAppStrong (Inv.rename ρ k) sp))
  | .neg (.shift R), n, d, h, k =>
      .focusShift (.letShift n (bind d h k.pendingShiftToPos))

/-- Every recursive principal-cut action, indexed by its result type. -/
private inductive CutCall (sig : Signature) : Type 1 where
  | bind {Γ : StableCtx sig} {qs : Pending sig} {P : Pos sig.nBases}
      {G : Goal sig.nBases} (d : Inv Γ qs (.pos P))
      (k : Inv Γ (.cons P .empty) G)
  | appValue {Γ : StableCtx sig} {A : Pos sig.nBases} {N : Neg sig.nBases}
      (f : Inv Γ .empty (.neg (.arr A N))) (a : PosNeu Γ A)
  | neu {Γ : StableCtx sig} {Cut N : Neg sig.nBases}
      (n : NegNeu (Γ.snoc (.neg Cut)) N) (v : Inv Γ .empty (.neg Cut))
  | pos {Γ : StableCtx sig} {Cut : Neg sig.nBases} {P : Pos sig.nBases}
      (p : PosNeu (Γ.snoc (.neg Cut)) P) (v : Inv Γ .empty (.neg Cut))
  | foc {Γ : StableCtx sig} {Cut : Neg sig.nBases} {P : Pos sig.nBases}
      (f : Foc (Γ.snoc (.neg Cut)) P) (v : Inv Γ .empty (.neg Cut))
  | inv {Γ : StableCtx sig} {Cut : Neg sig.nBases} {ps : Pending sig}
      {G : Goal sig.nBases}
      (t : Inv (Γ.snoc (.neg Cut)) ps G) (v : Inv Γ .empty (.neg Cut))

private def CutCall.Result : CutCall sig → Type
  | .bind (Γ := Γ) (qs := qs) (G := G) _ _ => Inv Γ qs G
  | .appValue (Γ := Γ) (N := N) _ _ => Inv Γ .empty (.neg N)
  | .neu (Γ := Γ) (Cut := Cut) (N := N) _ _ => NegSubstResult Γ Cut N
  | .pos (Γ := Γ) (P := P) _ _ => PosNeu Γ P
  | .foc (Γ := Γ) (P := P) _ _ => Inv Γ .empty (.pos P)
  | .inv (Γ := Γ) (ps := ps) (G := G) _ _ => Inv Γ ps G

private def CutCall.rank : CutCall sig → Nat
  | .bind (P := P) _ _ => posCutSize P
  | .appValue (A := A) (N := N) _ _ => negCutSize (.arr A N)
  | .neu (Cut := Cut) _ _ | .pos (Cut := Cut) _ _ |
      .foc (Cut := Cut) _ _ | .inv (Cut := Cut) _ _ => negCutSize Cut

private def CutCall.phase : CutCall sig → Nat
  | .neu .. | .pos .. | .foc .. | .inv .. => 2
  | .appValue .. => 1
  | .bind .. => 0

private def CutCall.sourceSize : CutCall sig → Nat
  | .bind d _ => d.nodeSize
  | .appValue f _ => f.nodeSize
  | .neu n _ => n.nodeSize
  | .pos p _ => p.nodeSize
  | .foc f _ => f.nodeSize
  | .inv t _ => t.nodeSize

private def CutCall.rankPhase (c : CutCall sig) : Nat :=
  3 * c.rank + c.phase

private def cutEval : (c : CutCall sig) → c.Result
  | .neu n v =>
      match n with
      | .var .here => .value v (Nat.le_refl _)
      | .var (.there x) => .neu (.var x)
      | .fst n =>
          match cutEval (.neu n v) with
          | .neu n' => .neu (.fst n')
          | .value w h => .value w.pendingFst (by
              simp only [negCutSize] at h ⊢
              omega)
      | .snd n =>
          match cutEval (.neu n v) with
          | .neu n' => .neu (.snd n')
          | .value w h => .value w.pendingSnd (by
              simp only [negCutSize] at h ⊢
              omega)
      | .app n p =>
          let p' := cutEval (.pos p v)
          match cutEval (.neu n v) with
          | .neu n' => .neu (.app n' p')
          | .value w h => .value (cutEval (.appValue w p')) (by
              simp only [negCutSize] at h ⊢
              omega)
  | .pos p v =>
      match p with
      | .atom (.there x) => .atom x
      | .inl p => .inl (cutEval (.pos p v))
      | .inr p => .inr (cutEval (.pos p v))
      | .shift t => .shift (cutEval (.inv t v))
  | .foc f v =>
      match f with
      | .up p => .focusPos (.up (cutEval (.pos p v)))
      | .letShift n body =>
          match cutEval (.neu n v) with
          | .neu n' => .focusPos (.letShift n' (cutEval (.inv body v)))
          | .value w h =>
              match w with
              | .focusShift g =>
                  cutEval (.bind (.focusPos g) (cutEval (.inv body v)))
  | .inv t v =>
      match t with
      | .caseSum l r => .caseSum (cutEval (.inv l v)) (cutEval (.inv r v))
      | .abort => .abort
      | .storeAtom t =>
          .storeAtom (cutEval (.inv (Inv.rename StableRename.exchange t) (Inv.weaken v)))
      | .storeShift t =>
          .storeShift (cutEval (.inv (Inv.rename StableRename.exchange t) (Inv.weaken v)))
      | .unit => .unit
      | .pair t u => .pair (cutEval (.inv t v)) (cutEval (.inv u v))
      | .lam t => .lam (cutEval (.inv t v))
      | .focusPos f => cutEval (.foc f v)
      | .focusShift f =>
          match cutEval (.foc f v) with
          | .focusPos g => .focusShift g
  | .appValue f a =>
      match f with
      | .lam body => cutEval (.bind (.focusPos (.up a)) body)
  | .bind (.caseSum l r) k =>
      .caseSum (cutEval (.bind l k)) (cutEval (.bind r k))
  | .bind .abort _ => .abort
  | .bind (.storeAtom t) k => .storeAtom (cutEval (.bind t (Inv.weaken k)))
  | .bind (.storeShift t) k => .storeShift (cutEval (.bind t (Inv.weaken k)))
  | .bind (.focusPos (.up (.atom x))) k =>
      Inv.rename (StableRename.replaceNewestAtom x) (Inv.asStoreAtom k)
  | .bind (.focusPos (.up (.inl p))) k =>
      cutEval (.bind (.focusPos (.up p)) (Inv.asCaseSum k).1)
  | .bind (.focusPos (.up (.inr p))) k =>
      cutEval (.bind (.focusPos (.up p)) (Inv.asCaseSum k).2)
  | .bind (.focusPos (.up (.shift v))) k => cutEval (.inv (Inv.asStoreShift k) v)
  | .bind (.focusPos (.letShift n body)) k =>
      composeShiftSized body.nodeSize
        (fun d h k => cutEval (.bind d k)) _ n body (Nat.le_refl _) k
termination_by c => (c.rankPhase, c.sourceSize)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [CutCall.rankPhase, CutCall.rank, CutCall.phase,
    CutCall.sourceSize, NegNeu.nodeSize, PosNeu.nodeSize, Foc.nodeSize,
    Inv.nodeSize, posCutSize, negCutSize]
  <;> omega

def substNegNeu {Γ : StableCtx sig} {Cut N : Neg sig.nBases}
    (n : NegNeu (Γ.snoc (.neg Cut)) N) (v : Inv Γ .empty (.neg Cut)) :
    NegSubstResult Γ Cut N := cutEval (.neu n v)

def substPosNeu {Γ : StableCtx sig} {Cut : Neg sig.nBases} {P : Pos sig.nBases}
    (p : PosNeu (Γ.snoc (.neg Cut)) P) (v : Inv Γ .empty (.neg Cut)) :
    PosNeu Γ P := cutEval (.pos p v)

def substFoc {Γ : StableCtx sig} {Cut : Neg sig.nBases} {P : Pos sig.nBases}
    (f : Foc (Γ.snoc (.neg Cut)) P) (v : Inv Γ .empty (.neg Cut)) :
    Inv Γ .empty (.pos P) := cutEval (.foc f v)

def substInv {Γ : StableCtx sig} {Cut : Neg sig.nBases} {ps : Pending sig}
    {G : Goal sig.nBases}
    (t : Inv (Γ.snoc (.neg Cut)) ps G) (v : Inv Γ .empty (.neg Cut)) :
    Inv Γ ps G := cutEval (.inv t v)

def bindPending {Γ : StableCtx sig} {qs : Pending sig}
    {P : Pos sig.nBases} {G : Goal sig.nBases}
    (d : Inv Γ qs (.pos P)) (k : Inv Γ (.cons P .empty) G) : Inv Γ qs G :=
  cutEval (.bind d k)

def cutUp {Γ : StableCtx sig} {P : Pos sig.nBases} {G : Goal sig.nBases}
    (p : PosNeu Γ P) (k : Inv Γ (.cons P .empty) G) : Inv Γ .empty G :=
  bindPending (.focusPos (.up p)) k

/-! ### Public prototype gate -/

def cutObject {Γ : StableCtx sig} {A C : Object sig.nBases}
    (v : Inv Γ .empty (.neg (asNeg A)))
    (k : Inv Γ (.cons (asPos A) .empty) (.neg (asNeg C))) :
    Inv Γ .empty (.neg (asNeg C)) :=
  match A with
  | .base _ | .never | .coprod _ _ =>
      match v with
      | .focusShift f => bindPending (.focusPos f) k
  | .unit | .prod _ _ | .exp _ _ =>
      bindPending (.focusPos (.up (.shift v))) k

/-! ### Compile-time falsification fixtures -/

namespace OrdinaryCutProtoFixtures

open Fixtures

abbrev UnitObj : Object 0 := .unit
abbrev ArrUnit : Object 0 := .exp .unit .unit
abbrev SumUnit : Object 0 := .coprod .unit .unit
abbrev ArrNeg : Neg 0 := .arr (.shift .one) .one

def arrUnitValue :
    Inv (sig := sig0) .empty .empty (.neg (asNeg ArrUnit)) :=
  inv_lam_unit

def arrUnitIdentity :
    Inv (sig := sig0) .empty (.cons (asPos ArrUnit) .empty)
      (.neg (asNeg ArrUnit)) :=
  .storeShift (etaNeg (sig := sig0) ArrNeg (.var .here))

def isArrUnitValue : Inv (sig := sig0) .empty .empty (.neg ArrNeg) → Bool
  | .lam (.storeShift .unit) => true
  | _ => false

/-- The positive principal cut contracts an η-expanded identity. -/
theorem beta_identity :
    isArrUnitValue (cutObject arrUnitValue arrUnitIdentity) = true := by
  native_decide

def appSpine :
    NegNeu (sig := sig0) (StableCtx.snoc .empty (.neg ArrNeg)) .one :=
  .app (.var .here) (.shift .unit)

def appSpineResult : NegSubstResult (sig := sig0) .empty (asNeg ArrUnit) .one :=
  substNegNeu appSpine arrUnitValue

def isUnitValue : NegSubstResult (sig := sig0) .empty (asNeg ArrUnit) .one → Bool
  | .value .unit _ => true
  | _ => false

/-- Substituting a shifted negative function contracts its application spine. -/
theorem shifted_negative_into_app_spine :
    isUnitValue appSpineResult = true := by native_decide

def sumLeft : Inv (sig := sig0) .empty .empty (.neg (asNeg SumUnit)) :=
  .focusShift (.up (.inl (.shift .unit)))

def sumRight : Inv (sig := sig0) .empty .empty (.neg (asNeg SumUnit)) :=
  .focusShift (.up (.inr (.shift .unit)))

def sumBranches :
    Inv (sig := sig0) .empty (.cons (asPos SumUnit) .empty)
      (.neg (asNeg SumUnit)) :=
  .caseSum
    (.storeShift (Inv.weaken sumLeft))
    (.storeShift (Inv.weaken sumRight))

def isSumLeft : Inv (sig := sig0) .empty .empty (.neg (asNeg SumUnit)) → Bool
  | .focusShift (.up (.inl (.shift .unit))) => true
  | _ => false

/-- A coproduct value selects exactly its left continuation. -/
theorem coproduct_inl_selects_left :
    isSumLeft (cutObject sumLeft sumBranches) = true := by native_decide

abbrev LetCtx : StableCtx sig0 :=
  StableCtx.snoc .empty (.neg (.shift .zero))

def letShiftArg :
    Inv (sig := sig0) LetCtx .empty (.pos (.shift .one)) :=
  inv_focusPos_letShift

def letShiftUnitK :
    Inv (sig := sig0) LetCtx (.cons (.shift .one) .empty) (.neg .one) :=
  .storeShift .unit

def isUnitInv {Γ : StableCtx sig0} :
    Inv (sig := sig0) Γ .empty (.neg .one) → Bool
  | .unit => true

/-- A computed positive argument crosses its `letShift` before the cut fires. -/
theorem letShift_computed_argument :
    isUnitInv (bindPending letShiftArg letShiftUnitK) = true := by native_decide

def letShiftArrowK :
    Inv (sig := sig0) LetCtx (.cons (.shift .one) .empty)
      (.neg (.arr (.shift .one) .one)) :=
  .storeShift (.lam (.storeShift .unit))

def letShiftArrow :
    Inv (sig := sig0) LetCtx .empty (.neg (.arr (.shift .one) .one)) :=
  bindPending letShiftArg letShiftArrowK

def letShiftArrowApplied : Inv (sig := sig0) LetCtx .empty (.neg .one) :=
  pendingAppWith bindPending letShiftArrow (.shift .unit)

/-- `letShift` commutes across an arrow result, then that arrow β-reduces. -/
theorem letShift_crosses_arrow_then_app :
    isUnitInv letShiftArrowApplied = true := by native_decide

end OrdinaryCutProtoFixtures

end Gimbal.Equality.Scherer
