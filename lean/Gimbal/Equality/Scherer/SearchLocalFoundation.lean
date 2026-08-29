/- Leaf contracts shared by local saturated evaluation and boundary search. -/

import Gimbal.Equality.Scherer.SplitFrame

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

def SearchUniverse.toTypeUniverse (U : SearchUniverse sig) : TypeUniverse sig :=
  ⟨U.pos, U.stable⟩

/-- Exactly the formula-child closure used by focused recursion. -/
structure SearchUniverse.StructurallyClosed (U : SearchUniverse sig) : Prop where
  sum_left {A B} : Pos.sum A B ∈ U.pos → A ∈ U.pos
  sum_right {A B} : Pos.sum A B ∈ U.pos → B ∈ U.pos
  pos_shift {N} : Pos.shift N ∈ U.pos → N ∈ U.neg
  prod_left {A B} : Neg.prod A B ∈ U.neg → A ∈ U.neg
  prod_right {A B} : Neg.prod A B ∈ U.neg → B ∈ U.neg
  arr_dom {A N} : Neg.arr A N ∈ U.neg → A ∈ U.pos
  arr_cod {A N} : Neg.arr A N ∈ U.neg → N ∈ U.neg
  neg_shift {P} : Neg.shift P ∈ U.neg → P ∈ U.pos
  stable_atom {q} : Pos.atom q ∈ U.pos → StableTy.atom q ∈ U.stable
  stable_neg {N} : N ∈ U.neg → StableTy.neg N ∈ U.stable

namespace SearchUniverse

private theorem map_stable_uPlus {X Y : Pos sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uPlus → Y ∈ P.uPlus)
    (fn : ∀ N : Neg sig.nBases, X ∈ N.uPlus → Y ∈ N.uPlus) :
    ∀ {Γ : StableCtx sig}, X ∈ Γ.uPlus → Y ∈ Γ.uPlus
  | .empty, h => by simpa using h
  | .snoc Γ S, h => by
      simp only [StableCtx.uPlus, Finset.mem_union] at h ⊢
      exact h.elim (fun h => Or.inl (map_stable_uPlus fp fn h)) (fun h =>
        Or.inr <| match S with | .atom q => fp (Pos.atom q) h | .neg N => fn N h)

private theorem map_pending_uPlus {X Y : Pos sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uPlus → Y ∈ P.uPlus) :
    ∀ {ps : Pending sig}, X ∈ ps.uPlus → Y ∈ ps.uPlus
  | .empty, h => by simpa using h
  | .cons P ps, h => by
      simp only [Pending.uPlus, Finset.mem_union] at h ⊢
      exact h.elim (fun h => Or.inl (fp P h))
        (fun h => Or.inr (map_pending_uPlus fp h))

private theorem map_goal_uPlus {X Y : Pos sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uPlus → Y ∈ P.uPlus)
    (fn : ∀ N : Neg sig.nBases, X ∈ N.uPlus → Y ∈ N.uPlus) :
    ∀ {G : Goal sig.nBases}, X ∈ G.uPlus → Y ∈ G.uPlus
  | .pos P, h => fp P h
  | .neg N, h => fn N h

private theorem endpoints_map_uPlus {X Y : Pos sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uPlus → Y ∈ P.uPlus) :
    ∀ {rs : List (Pos sig.nBases)}, X ∈ endpointsUPlus rs → Y ∈ endpointsUPlus rs
  | [], h => by simpa using h
  | P :: rs, h => by
      simp only [endpointsUPlus, Finset.mem_union] at h ⊢
      exact h.elim (fun h => Or.inl (fp P h))
        (fun h => Or.inr (endpoints_map_uPlus fp h))

private theorem map_input_pos {X Y : Pos sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uPlus → Y ∈ P.uPlus)
    (fn : ∀ N : Neg sig.nBases, X ∈ N.uPlus → Y ∈ N.uPlus)
    {Γ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
    {rs : List (Pos sig.nBases)}
    (h : X ∈ (fromInputs Γ ps G rs).pos) : Y ∈ (fromInputs Γ ps G rs).pos := by
  simp only [fromInputs, UPlus.fromInputs, Finset.mem_union] at h ⊢
  rcases h with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (map_stable_uPlus fp fn h)))
  · exact Or.inl (Or.inl (Or.inr (map_pending_uPlus fp h)))
  · exact Or.inl (Or.inr (map_goal_uPlus fp fn h))
  · exact Or.inr (endpoints_map_uPlus fp h)

private theorem map_stable_uPlus_uNeg {X : Pos sig.nBases} {Y : Neg sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uPlus → Y ∈ P.uNeg)
    (fn : ∀ N : Neg sig.nBases, X ∈ N.uPlus → Y ∈ N.uNeg) :
    ∀ {Γ : StableCtx sig}, X ∈ Γ.uPlus → Y ∈ Γ.uNeg
  | .empty, h => by simpa using h
  | .snoc Γ S, h => by
      simp only [StableCtx.uPlus, StableCtx.uNeg, Finset.mem_union] at h ⊢
      exact h.elim (fun h => Or.inl (map_stable_uPlus_uNeg fp fn h)) (fun h =>
        Or.inr <| match S with | .atom q => fp (Pos.atom q) h | .neg N => fn N h)

private theorem map_pending_uPlus_uNeg {X : Pos sig.nBases} {Y : Neg sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uPlus → Y ∈ P.uNeg) :
    ∀ {ps : Pending sig}, X ∈ ps.uPlus → Y ∈ ps.uNeg
  | .empty, h => by simpa using h
  | .cons P ps, h => by
      simp only [Pending.uPlus, Pending.uNeg, Finset.mem_union] at h ⊢
      exact h.elim (fun h => Or.inl (fp P h))
        (fun h => Or.inr (map_pending_uPlus_uNeg fp h))

private theorem map_goal_uPlus_uNeg {X : Pos sig.nBases} {Y : Neg sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uPlus → Y ∈ P.uNeg)
    (fn : ∀ N : Neg sig.nBases, X ∈ N.uPlus → Y ∈ N.uNeg) :
    ∀ {G : Goal sig.nBases}, X ∈ G.uPlus → Y ∈ G.uNeg
  | .pos P, h => fp P h
  | .neg N, h => fn N h

private theorem endpoints_map_uPlus_uNeg {X : Pos sig.nBases} {Y : Neg sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uPlus → Y ∈ P.uNeg) :
    ∀ {rs : List (Pos sig.nBases)}, X ∈ endpointsUPlus rs → Y ∈ endpointResultsUNeg rs
  | [], h => by simpa using h
  | P :: rs, h => by
      simp only [endpointsUPlus, endpointResultsUNeg, Finset.mem_union] at h ⊢
      exact h.elim (fun h => Or.inl (fp P h))
        (fun h => Or.inr (endpoints_map_uPlus_uNeg fp h))

private theorem map_input_pos_neg {X : Pos sig.nBases} {Y : Neg sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uPlus → Y ∈ P.uNeg)
    (fn : ∀ N : Neg sig.nBases, X ∈ N.uPlus → Y ∈ N.uNeg)
    {Γ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
    {rs : List (Pos sig.nBases)}
    (h : X ∈ (fromInputs Γ ps G rs).pos) : Y ∈ (fromInputs Γ ps G rs).neg := by
  simp only [fromInputs, UPlus.fromInputs, Finset.mem_union] at h ⊢
  rcases h with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (map_stable_uPlus_uNeg fp fn h)))
  · exact Or.inl (Or.inl (Or.inr (map_pending_uPlus_uNeg fp h)))
  · exact Or.inl (Or.inr (map_goal_uPlus_uNeg fp fn h))
  · exact Or.inr (endpoints_map_uPlus_uNeg fp h)

private theorem map_stable_uNeg {X Y : Neg sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uNeg → Y ∈ P.uNeg)
    (fn : ∀ N : Neg sig.nBases, X ∈ N.uNeg → Y ∈ N.uNeg) :
    ∀ {Γ : StableCtx sig}, X ∈ Γ.uNeg → Y ∈ Γ.uNeg
  | .empty, h => by simpa using h
  | .snoc Γ S, h => by
      simp only [StableCtx.uNeg, Finset.mem_union] at h ⊢
      exact h.elim (fun h => Or.inl (map_stable_uNeg fp fn h)) (fun h =>
        Or.inr <| match S with | .atom q => fp (Pos.atom q) h | .neg N => fn N h)

private theorem map_pending_uNeg {X Y : Neg sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uNeg → Y ∈ P.uNeg) :
    ∀ {ps : Pending sig}, X ∈ ps.uNeg → Y ∈ ps.uNeg
  | .empty, h => by simpa using h
  | .cons P ps, h => by
      simp only [Pending.uNeg, Finset.mem_union] at h ⊢
      exact h.elim (fun h => Or.inl (fp P h))
        (fun h => Or.inr (map_pending_uNeg fp h))

private theorem map_goal_uNeg {X Y : Neg sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uNeg → Y ∈ P.uNeg)
    (fn : ∀ N : Neg sig.nBases, X ∈ N.uNeg → Y ∈ N.uNeg) :
    ∀ {G : Goal sig.nBases}, X ∈ G.uNeg → Y ∈ G.uNeg
  | .pos P, h => fp P h
  | .neg N, h => fn N h

private theorem endpoints_map_uNeg {X Y : Neg sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uNeg → Y ∈ P.uNeg) :
    ∀ {rs : List (Pos sig.nBases)}, X ∈ endpointResultsUNeg rs →
      Y ∈ endpointResultsUNeg rs
  | [], h => by simpa using h
  | P :: rs, h => by
      simp only [endpointResultsUNeg, Finset.mem_union] at h ⊢
      exact h.elim (fun h => Or.inl (fp P h))
        (fun h => Or.inr (endpoints_map_uNeg fp h))

private theorem map_input_neg {X Y : Neg sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uNeg → Y ∈ P.uNeg)
    (fn : ∀ N : Neg sig.nBases, X ∈ N.uNeg → Y ∈ N.uNeg)
    {Γ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
    {rs : List (Pos sig.nBases)}
    (h : X ∈ (fromInputs Γ ps G rs).neg) : Y ∈ (fromInputs Γ ps G rs).neg := by
  simp only [fromInputs, Finset.mem_union] at h ⊢
  rcases h with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (map_stable_uNeg fp fn h)))
  · exact Or.inl (Or.inl (Or.inr (map_pending_uNeg fp h)))
  · exact Or.inl (Or.inr (map_goal_uNeg fp fn h))
  · exact Or.inr (endpoints_map_uNeg fp h)

private theorem map_stable_uNeg_uPlus {X : Neg sig.nBases} {Y : Pos sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uNeg → Y ∈ P.uPlus)
    (fn : ∀ N : Neg sig.nBases, X ∈ N.uNeg → Y ∈ N.uPlus) :
    ∀ {Γ : StableCtx sig}, X ∈ Γ.uNeg → Y ∈ Γ.uPlus
  | .empty, h => by simpa using h
  | .snoc Γ S, h => by
      simp only [StableCtx.uNeg, StableCtx.uPlus, Finset.mem_union] at h ⊢
      exact h.elim (fun h => Or.inl (map_stable_uNeg_uPlus fp fn h)) (fun h =>
        Or.inr <| match S with | .atom q => fp (Pos.atom q) h | .neg N => fn N h)

private theorem map_pending_uNeg_uPlus {X : Neg sig.nBases} {Y : Pos sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uNeg → Y ∈ P.uPlus) :
    ∀ {ps : Pending sig}, X ∈ ps.uNeg → Y ∈ ps.uPlus
  | .empty, h => by simpa using h
  | .cons P ps, h => by
      simp only [Pending.uNeg, Pending.uPlus, Finset.mem_union] at h ⊢
      exact h.elim (fun h => Or.inl (fp P h))
        (fun h => Or.inr (map_pending_uNeg_uPlus fp h))

private theorem map_goal_uNeg_uPlus {X : Neg sig.nBases} {Y : Pos sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uNeg → Y ∈ P.uPlus)
    (fn : ∀ N : Neg sig.nBases, X ∈ N.uNeg → Y ∈ N.uPlus) :
    ∀ {G : Goal sig.nBases}, X ∈ G.uNeg → Y ∈ G.uPlus
  | .pos P, h => fp P h
  | .neg N, h => fn N h

private theorem endpoints_map_uNeg_uPlus {X : Neg sig.nBases} {Y : Pos sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uNeg → Y ∈ P.uPlus) :
    ∀ {rs : List (Pos sig.nBases)}, X ∈ endpointResultsUNeg rs →
      Y ∈ endpointsUPlus rs
  | [], h => by simpa using h
  | P :: rs, h => by
      simp only [endpointResultsUNeg, endpointsUPlus, Finset.mem_union] at h ⊢
      exact h.elim (fun h => Or.inl (fp P h))
        (fun h => Or.inr (endpoints_map_uNeg_uPlus fp h))

private theorem map_input_neg_pos {X : Neg sig.nBases} {Y : Pos sig.nBases}
    (fp : ∀ P : Pos sig.nBases, X ∈ P.uNeg → Y ∈ P.uPlus)
    (fn : ∀ N : Neg sig.nBases, X ∈ N.uNeg → Y ∈ N.uPlus)
    {Γ : StableCtx sig} {ps : Pending sig} {G : Goal sig.nBases}
    {rs : List (Pos sig.nBases)}
    (h : X ∈ (fromInputs Γ ps G rs).neg) : Y ∈ (fromInputs Γ ps G rs).pos := by
  simp only [fromInputs, UPlus.fromInputs, Finset.mem_union] at h ⊢
  rcases h with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (map_stable_uNeg_uPlus fp fn h)))
  · exact Or.inl (Or.inl (Or.inr (map_pending_uNeg_uPlus fp h)))
  · exact Or.inl (Or.inr (map_goal_uNeg_uPlus fp fn h))
  · exact Or.inr (endpoints_map_uNeg_uPlus fp h)

/-- The input-generated universe is structurally closed without support data. -/
theorem fromInputs_structurallyClosed (Γ : StableCtx sig) (ps : Pending sig)
    (G : Goal sig.nBases) (rs : List (Pos sig.nBases)) :
    (fromInputs Γ ps G rs).StructurallyClosed where
  sum_left h := map_input_pos (fun _ => mem_uPlus_sum_left)
    (fun _ h => (Neg.mem_uPlus_iff).mpr
      (NegOccurs.sum_left_child ((Neg.mem_uPlus_iff).mp h))) h
  sum_right h := map_input_pos (fun _ => mem_uPlus_sum_right)
    (fun _ h => (Neg.mem_uPlus_iff).mpr
      (NegOccurs.sum_right_child ((Neg.mem_uPlus_iff).mp h))) h
  pos_shift h := map_input_pos_neg (fun _ => mem_uPlus_shift_neg)
    (fun _ h => (Neg.mem_uNeg_iff).mpr
      (NegOccurs.shift_child_neg ((Neg.mem_uPlus_iff).mp h))) h
  prod_left h := map_input_neg
    (fun _ h => (Pos.mem_uNeg_iff).mpr
      (NegOccursInPos.prod_left_child ((Pos.mem_uNeg_iff).mp h)))
    (fun _ => mem_uNeg_prod_left) h
  prod_right h := map_input_neg
    (fun _ h => (Pos.mem_uNeg_iff).mpr
      (NegOccursInPos.prod_right_child ((Pos.mem_uNeg_iff).mp h)))
    (fun _ => mem_uNeg_prod_right) h
  arr_dom h := map_input_neg_pos
    (fun _ h => NegOccursInPos.arr_dom_mem_uPlus ((Pos.mem_uNeg_iff).mp h))
    (fun _ => mem_uNeg_arr_dom) h
  arr_cod h := map_input_neg
    (fun _ h => (Pos.mem_uNeg_iff).mpr
      (NegOccursInPos.arr_cod_child ((Pos.mem_uNeg_iff).mp h)))
    (fun _ => mem_uNeg_arr_cod) h
  neg_shift h := map_input_neg_pos
    (fun _ h => NegOccursInPos.shift_mem_uPlus ((Pos.mem_uNeg_iff).mp h))
    (fun _ => mem_uNeg_shift_pos) h
  stable_atom := stable_atom Γ ps G rs
  stable_neg := stable_neg Γ ps G rs

end SearchUniverse

structure PendingInput (U : SearchUniverse sig) (R : AliasResolver sig) (O : Type)
    (resolved : ResolvedPending U O) where
  sources : PendingAssignment R resolved.erase

def PendingInput.deps (_I : PendingInput U R O resolved) :
    PendingDeps O resolved.erase := PendingDeps.ofResolvedPending resolved

def PendingAssignment.dropHead (E : PendingAssignment R (.cons P ps)) :
    PendingAssignment R ps where
  ref x := E.ref (.there x)

@[simp] theorem PendingAssignment.dropHead_ref
    (E : PendingAssignment R (.cons P ps)) (x : PendingVar ps Q) :
    E.dropHead.ref x = E.ref (.there x) := rfl

inductive EvalEdge where
  | posInl | posInr | posShift | caseLeft | caseRight | storeTail
  | pairLeft | pairRight | lamBody | satShift | satPos | elimArg
  deriving DecidableEq, Repr

abbrev EvalAddr := List EvalEdge

/-- Local recursion names source sites; the caller supplies their resolved identities. -/
structure PendingFlow (R : AliasResolver sig) where
  lambdaSource : EvalAddr → (P : Pos sig.nBases) → ResolvedRef R P.erase
  splitLeftSource : EvalAddr → {A B : Pos sig.nBases} →
    ResolvedRef R (Pos.sum A B).erase → ResolvedRef R A.erase
  splitRightSource : EvalAddr → {A B : Pos sig.nBases} →
    ResolvedRef R (Pos.sum A B).erase → ResolvedRef R B.erase

namespace PendingInput

def tail (I : PendingInput U R O (c :: rest)) : PendingInput U R O rest :=
  ⟨I.sources.dropHead⟩

def sumLeft (flow : PendingFlow R) (addr : EvalAddr) (hA : A ∈ U.pos)
    (I : PendingInput U R O (⟨⟨.sum A B, hSum⟩, K⟩ :: rest)) :
    PendingInput U R O (⟨⟨A, hA⟩, K⟩ :: rest) :=
  ⟨PendingAssignment.cons (flow.splitLeftSource addr (I.sources.ref .here))
    I.sources.dropHead⟩

def sumRight (flow : PendingFlow R) (addr : EvalAddr) (hB : B ∈ U.pos)
    (I : PendingInput U R O (⟨⟨.sum A B, hSum⟩, K⟩ :: rest)) :
    PendingInput U R O (⟨⟨B, hB⟩, K⟩ :: rest) :=
  ⟨PendingAssignment.cons (flow.splitRightSource addr (I.sources.ref .here))
    I.sources.dropHead⟩

def lambda (flow : PendingFlow R) (addr : EvalAddr) (P : UPos U) :
    PendingInput U R O (ResolvedPending.lambdaPending P) :=
  ⟨PendingAssignment.cons (flow.lambdaSource addr P.1) (PendingAssignment.empty R)⟩

@[simp] theorem sumLeft_tail (flow : PendingFlow R) (addr : EvalAddr)
    (hA : A ∈ U.pos)
    (I : PendingInput U R O (⟨⟨.sum A B, hSum⟩, K⟩ :: rest)) :
    (I.sumLeft flow addr hA).sources.dropHead = I.sources.dropHead := rfl

@[simp] theorem sumRight_tail (flow : PendingFlow R) (addr : EvalAddr)
    (hB : B ∈ U.pos)
    (I : PendingInput U R O (⟨⟨.sum A B, hSum⟩, K⟩ :: rest)) :
    (I.sumRight flow addr hB).sources.dropHead = I.sources.dropHead := rfl

@[simp] theorem sumLeft_support (flow : PendingFlow R) (addr : EvalAddr)
    (hA : A ∈ U.pos)
    (I : PendingInput U R O (⟨⟨.sum A B, hSum⟩, K⟩ :: rest)) :
    (I.sumLeft flow addr hA).deps.toList = K :: I.tail.deps.toList := rfl

@[simp] theorem sumRight_support (flow : PendingFlow R) (addr : EvalAddr)
    (hB : B ∈ U.pos)
    (I : PendingInput U R O (⟨⟨.sum A B, hSum⟩, K⟩ :: rest)) :
    (I.sumRight flow addr hB).deps.toList = K :: I.tail.deps.toList := rfl

@[simp] theorem lambda_support (flow : PendingFlow R) (addr : EvalAddr) (P : UPos U) :
    (lambda (O := O) flow addr P).deps.toList = [∅] := rfl

end PendingInput

structure Segment (U : TypeUniverse sig) (R : AliasResolver sig) (O : Type)
    (Base : Ctx2 U) (Old New : StableCtx sig) where
  frame : SplitFrame U R O Old New
  before_eq : frame.before = Base

namespace SplitFrame

@[simp] theorem push_before (f : SplitFrame U R O Old New) (S : ↥U.stable)
    (K : DepSupport O) (source : ResolvedRef R S.1.erase) :
    (f.push S K source).before = f.before := by
  simp [before, push, RetainedCtx.weaken]

@[simp] theorem reset_before (f : SplitFrame U R O Old New) :
    f.reset.before = f.after := rfl

theorem batchPending_frame_neutral (f : SplitFrame U R O Old New) (ps : Pending sig) :
    f.batchPending ps = f := rfl

end SplitFrame

namespace Segment

def ofReset (f : SplitFrame U R O Old New) :
    Segment U R O f.after (Old.append New) .empty :=
  ⟨f.reset, f.reset_before⟩

def push (s : Segment U R O Base Old New) (S : ↥U.stable)
    (K : DepSupport O) (source : ResolvedRef R S.1.erase) :
    Segment U R O Base Old (New.snoc S.1) :=
  ⟨s.frame.push S K source, by rw [SplitFrame.push_before, s.before_eq]⟩

def storeAtom (s : Segment U R O Base Old New)
    (hq : StableTy.atom q ∈ U.stable) (K : DepSupport O)
    (pending : PendingAssignment R (.cons (.atom q) ps)) :
    Segment U R O Base Old (New.snoc (.atom q)) :=
  s.push ⟨.atom q, hq⟩ K (pending.ref .here)

def storeShift (s : Segment U R O Base Old New)
    (hN : StableTy.neg N ∈ U.stable) (K : DepSupport O)
    (pending : PendingAssignment R (.cons (.shift N) ps)) :
    Segment U R O Base Old (New.snoc (.neg N)) :=
  s.push ⟨.neg N, hN⟩ K (pending.ref .here)

@[simp] theorem storeAtom_before (s : Segment U R O Base Old New)
    (hq : StableTy.atom q ∈ U.stable) (K : DepSupport O)
    (pending : PendingAssignment R (.cons (.atom q) ps)) :
    (s.storeAtom hq K pending).frame.before = Base :=
  (s.storeAtom hq K pending).before_eq

@[simp] theorem storeShift_before (s : Segment U R O Base Old New)
    (hN : StableTy.neg N ∈ U.stable) (K : DepSupport O)
    (pending : PendingAssignment R (.cons (.shift N) ps)) :
    (s.storeShift hN K pending).frame.before = Base :=
  (s.storeShift hN K pending).before_eq

end Segment

abbrev Results (α : Type) := List α

structure FreshSInv (Old New : StableCtx sig) (ps : Pending sig)
    (G : Goal sig.nBases) where
  proof : SInv Old New ps G
  valid : proof.freshValid = true

structure FreshSat (Old New : StableCtx sig) (P : Pos sig.nBases) where
  proof : Sat Old New P
  valid : proof.freshValid = true

abbrev SatCallback (U : SearchUniverse sig) (R : AliasResolver sig) (O : Type)
    (Base : Ctx2 U.toTypeUniverse) :=
  ∀ {Old New}, EvalAddr → Segment U.toTypeUniverse R O Base Old New →
    (P : UPos U) → Results (FreshSat Old New P.1)

structure Control (U : SearchUniverse sig) (R : AliasResolver sig) (O : Type)
    (Base : Ctx2 U.toTypeUniverse) where
  flow : PendingFlow R
  saturate : SatCallback U R O Base

namespace SearchLocalFoundationFixtures

theorem case_addresses_distinct :
    ([.caseLeft] : EvalAddr) ≠ [.caseRight] := by decide

theorem reset_uses_after_as_base (f : SplitFrame U R O Old New) :
    (Segment.ofReset f).frame.before = f.after := (Segment.ofReset f).before_eq

theorem batch_result_stays_pending (f : SplitFrame U R O Old New)
    (_B : BatchResultAssignment R selected) : f.batchPending selected = f := by
  simpa using f.batchPending_frame_neutral selected

theorem closure_arr_sum_shift (Γ : StableCtx sig) (ps : Pending sig)
    (rs : List (Pos sig.nBases)) {A B P : Pos sig.nBases} {N : Neg sig.nBases}
    (h : Neg.arr (.sum A B) (.shift P) ∈
      (SearchUniverse.fromInputs Γ ps (.neg N) rs).neg) :
    A ∈ (SearchUniverse.fromInputs Γ ps (.neg N) rs).pos ∧
      B ∈ (SearchUniverse.fromInputs Γ ps (.neg N) rs).pos ∧
      P ∈ (SearchUniverse.fromInputs Γ ps (.neg N) rs).pos := by
  let c := SearchUniverse.fromInputs_structurallyClosed Γ ps (.neg N) rs
  exact ⟨c.sum_left (c.arr_dom h), c.sum_right (c.arr_dom h),
    c.neg_shift (c.arr_cod h)⟩

end SearchLocalFoundationFixtures

end Gimbal.Equality.Scherer
