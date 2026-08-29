/- Structural saturated evaluation below the single recursive boundary callback. -/

import Gimbal.Equality.Scherer.SearchLocalFoundation

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

mutual
def posLocalWeight : Pos sig.nBases → Nat
  | .atom _ | .zero => 1
  | .sum A B => 1 + posLocalWeight A + posLocalWeight B
  | .shift N => 1 + negLocalWeight N

def negLocalWeight : Neg sig.nBases → Nat
  | .one => 1
  | .prod A B => 1 + negLocalWeight A + negLocalWeight B
  | .arr A N => 1 + posLocalWeight A + negLocalWeight N
  | .shift P => 1 + posLocalWeight P
end

def goalLocalWeight : Goal sig.nBases → Nat
  | .neg N => negLocalWeight N
  | .pos P => posLocalWeight P

def pendingLocalWeight : ResolvedPending U O → Nat
  | [] => 0
  | c :: rest => posLocalWeight c.ty.1 + pendingLocalWeight rest

def invWeight (pending : ResolvedPending U O) (G : Goal sig.nBases) : Nat :=
  pendingLocalWeight pending + goalLocalWeight G

theorem posLocalWeight_pos (P : Pos sig.nBases) : 0 < posLocalWeight P := by
  cases P <;> simp [posLocalWeight]

def Goal.InUniverse (U : SearchUniverse sig) : Goal sig.nBases → Prop
  | .neg N => N ∈ U.neg
  | .pos P => P ∈ U.pos

namespace FreshSInv

def abort : FreshSInv Old New (.cons .zero ps) G := ⟨.abort, rfl⟩
def unit : FreshSInv Old New .empty (.neg .one) := ⟨.unit, rfl⟩

def caseSum (l : FreshSInv Old New (.cons A ps) G)
    (r : FreshSInv Old New (.cons B ps) G) :
    FreshSInv Old New (.cons (.sum A B) ps) G :=
  ⟨.caseSum l.proof r.proof, by simp [SInv.freshValid, l.valid, r.valid]⟩

def storeAtom (t : FreshSInv Old (New.snoc (.atom q)) ps G) :
    FreshSInv Old New (.cons (.atom q) ps) G :=
  ⟨.storeAtom t.proof, t.valid⟩

def storeShift (t : FreshSInv Old (New.snoc (.neg N)) ps G) :
    FreshSInv Old New (.cons (.shift N) ps) G :=
  ⟨.storeShift t.proof, t.valid⟩

def pair (l : FreshSInv Old New .empty (.neg A))
    (r : FreshSInv Old New .empty (.neg B)) :
    FreshSInv Old New .empty (.neg (.prod A B)) :=
  ⟨.pair l.proof r.proof, by simp [SInv.freshValid, l.valid, r.valid]⟩

def lam (t : FreshSInv Old New (.cons A .empty) (.neg B)) :
    FreshSInv Old New .empty (.neg (.arr A B)) :=
  ⟨.lam t.proof, t.valid⟩

def satShift (s : FreshSat Old New P) :
    FreshSInv Old New .empty (.neg (.shift P)) := ⟨.satShift s.proof, s.valid⟩

def satPos (s : FreshSat Old New P) :
    FreshSInv Old New .empty (.pos P) := ⟨.satPos s.proof, s.valid⟩

end FreshSInv

namespace FreshSPos

def inl (p : FreshSPos G A) : FreshSPos G (.sum A B) :=
  ⟨.inl p.neutral, p.valid⟩

def inr (p : FreshSPos G B) : FreshSPos G (.sum A B) :=
  ⟨.inr p.neutral, p.valid⟩

def shift (t : FreshSInv G .empty .empty (.neg N)) : FreshSPos G (.shift N) :=
  ⟨.shift t.proof, t.valid⟩

end FreshSPos

namespace FreshSat

def done (p : FreshSPos (Old.append New) P) : FreshSat Old New P :=
  ⟨.done p.neutral, p.valid⟩

def batch (selected : SelectedBatch Old New ps)
    (body : FreshSInv (Old.append New) .empty ps (.pos P)) : FreshSat Old New P :=
  ⟨.batch selected.toNonemptyBatchObs body.proof, by
    simp [Sat.freshValid, SelectedBatch.all_entries_use_newMask selected,
      SelectedBatch.all_entries_freshValid selected, body.valid]⟩

end FreshSat

/-! Local weight gates. -/

theorem invWeight_sumLeft_lt (rest : ResolvedPending U O) (G : Goal sig.nBases)
    (hSum : Pos.sum A B ∈ U.pos) (K : DepSupport O) (hA : A ∈ U.pos) :
    invWeight (⟨⟨A, hA⟩, K⟩ :: rest) G <
      invWeight (⟨⟨.sum A B, hSum⟩, K⟩ :: rest) G := by
  simp [invWeight, pendingLocalWeight, posLocalWeight]
  omega

theorem invWeight_sumRight_lt (rest : ResolvedPending U O) (G : Goal sig.nBases)
    (hSum : Pos.sum A B ∈ U.pos) (K : DepSupport O) (hB : B ∈ U.pos) :
    invWeight (⟨⟨B, hB⟩, K⟩ :: rest) G <
      invWeight (⟨⟨.sum A B, hSum⟩, K⟩ :: rest) G := by
  simp [invWeight, pendingLocalWeight, posLocalWeight]

theorem invWeight_tail_lt (c : PendingCell U O) (rest : ResolvedPending U O)
    (G : Goal sig.nBases) : invWeight rest G < invWeight (c :: rest) G := by
  have h := posLocalWeight_pos c.ty.1
  simp only [invWeight, pendingLocalWeight]
  omega

theorem invWeight_prodLeft_lt {U : SearchUniverse sig} {O : Type}
    (A B : Neg sig.nBases) :
    invWeight ([] : ResolvedPending U O) (.neg A) <
      invWeight (U := U) (O := O) [] (.neg (.prod A B)) := by
  simp [invWeight, pendingLocalWeight, goalLocalWeight, negLocalWeight]
  omega

theorem invWeight_prodRight_lt {U : SearchUniverse sig} {O : Type}
    (A B : Neg sig.nBases) :
    invWeight ([] : ResolvedPending U O) (.neg B) <
      invWeight (U := U) (O := O) [] (.neg (.prod A B)) := by
  simp [invWeight, pendingLocalWeight, goalLocalWeight, negLocalWeight]

theorem invWeight_lam_lt {U : SearchUniverse sig} {O : Type} (A : Pos sig.nBases)
    (B : Neg sig.nBases)
    (hA : A ∈ U.pos) :
    invWeight (ResolvedPending.lambdaPending (O := O) ⟨A, hA⟩) (.neg B) <
      invWeight (U := U) (O := O) [] (.neg (.arr A B)) := by
  simp [invWeight, pendingLocalWeight, goalLocalWeight,
    negLocalWeight, ResolvedPending.lambdaPending]

/-! The structural evaluator.  `Control.saturate` is its only nonlocal edge. -/

def runSInv {U : SearchUniverse sig} {R : AliasResolver sig} {O : Type}
    {Base : Ctx2 U.toTypeUniverse} (closed : U.StructurallyClosed)
    (ctl : Control U R O Base) (addr : EvalAddr) :
    ∀ {Old New} (_seg : Segment U.toTypeUniverse R O Base Old New)
      (resolved : ResolvedPending U O), PendingInput U R O resolved →
      (G : Goal sig.nBases) → G.InUniverse U →
      Results (FreshSInv Old New resolved.erase G)
  | _, _, seg, ⟨⟨.sum A B, hSum⟩, K⟩ :: rest, input, G, hG =>
      (input.splitChoices ctl.flow addr (closed.sum_left hSum)
        (closed.sum_right hSum)).flatMap (fun inputs =>
          (runSInv closed ctl (.caseLeft :: addr) seg
            (⟨⟨A, closed.sum_left hSum⟩, K⟩ :: rest) inputs.1 G hG).flatMap
            (fun l =>
              (runSInv closed ctl (.caseRight :: addr) seg
                (⟨⟨B, closed.sum_right hSum⟩, K⟩ :: rest) inputs.2 G hG).map
                (FreshSInv.caseSum l)))
  | _, _, _, ⟨⟨.zero, _⟩, _⟩ :: _, _, _, _ => [FreshSInv.abort]
  | _, _, seg, ⟨⟨.atom q, hq⟩, K⟩ :: rest, input, G, hG =>
      (runSInv closed ctl (.storeTail :: addr)
        (seg.storeAtom (closed.stable_atom hq) K input.sources)
        rest input.tail G hG).map FreshSInv.storeAtom
  | _, _, seg, ⟨⟨.shift N, hN⟩, K⟩ :: rest, input, G, hG =>
      (runSInv closed ctl (.storeTail :: addr)
        (seg.storeShift (closed.stable_neg (closed.pos_shift hN)) K input.sources)
        rest input.tail G hG).map FreshSInv.storeShift
  | _, _, _, [], _, .neg .one, _ => [FreshSInv.unit]
  | _, _, seg, [], input, .neg (.prod A B), hProd =>
      (runSInv closed ctl (.pairLeft :: addr) seg [] input (.neg A)
        (closed.prod_left hProd)).flatMap (fun l =>
          (runSInv closed ctl (.pairRight :: addr) seg [] input (.neg B)
            (closed.prod_right hProd)).map (FreshSInv.pair l))
  | _, _, seg, [], _, .neg (.arr A B), hArr =>
      (PendingInput.lambdaChoices (O := O) ctl.flow (.lamBody :: addr)
        ⟨A, closed.arr_dom hArr⟩).flatMap (fun input =>
          (runSInv closed ctl (.lamBody :: addr) seg
            (ResolvedPending.lambdaPending ⟨A, closed.arr_dom hArr⟩)
            input (.neg B) (closed.arr_cod hArr)).map FreshSInv.lam)
  | _, _, seg, [], _, .neg (.shift P), hShift =>
      (ctl.saturate (.satShift :: addr) seg ⟨P, closed.neg_shift hShift⟩).map
        FreshSInv.satShift
  | _, _, seg, [], _, .pos P, hP =>
      (ctl.saturate (.satPos :: addr) seg ⟨P, hP⟩).map FreshSInv.satPos
termination_by Old New _ resolved _ G _ => invWeight resolved G
decreasing_by
  all_goals simp [invWeight, pendingLocalWeight, goalLocalWeight,
    posLocalWeight, negLocalWeight, ResolvedPending.lambdaPending] <;> omega

/-- Positive construction inside one already-entered segment. -/
def runSPos {U : SearchUniverse sig} {R : AliasResolver sig} {O : Type}
    {Base : Ctx2 U.toTypeUniverse} (closed : U.StructurallyClosed)
    (ctl : Control U R O Base) (addr : EvalAddr) {Γ : StableCtx sig}
    (seg : Segment U.toTypeUniverse R O Base Γ .empty) :
    ∀ (P : Pos sig.nBases), P ∈ U.pos → Results (FreshSPos Γ P)
  | .atom q, hq => by
      simpa using seg.frame.selectedAtoms q (closed.stable_atom hq)
  | .zero, _ => []
  | .sum A B, hSum =>
      (runSPos closed ctl (.posInl :: addr) seg A (closed.sum_left hSum)).map
        FreshSPos.inl ++
      (runSPos closed ctl (.posInr :: addr) seg B (closed.sum_right hSum)).map
        FreshSPos.inr
  | .shift N, hShift =>
      (runSInv closed ctl (.posShift :: addr) seg []
        ⟨PendingAssignment.empty R⟩ (.neg N) (closed.pos_shift hShift)).map
        FreshSPos.shift
termination_by P _ => posLocalWeight P
decreasing_by
  all_goals simp [posLocalWeight] <;> omega

/-- The positive provider exposed to elimination spines.  Its context is the
post-reset `Old ++ New`; no API here can accidentally use the pre-reset frame. -/
def runSPosReset {U : SearchUniverse sig} {R : AliasResolver sig} {O : Type}
    (closed : U.StructurallyClosed)
    {Old New : StableCtx sig} (frame : SplitFrame U.toTypeUniverse R O Old New)
    (ctl : Control U R O frame.after)
    (addr : EvalAddr) (P : UPos U) :
    Results (FreshSPos (Old.append New) P.1) :=
  let reset := Segment.ofReset frame
  runSPos closed ctl (.elimArg :: addr) reset P.1 P.2

/-- Callback in the exact shape expected by `NegSpine.fulfill`. Every
available argument goes through the reset frame. -/
def resetPositiveProvider {U : SearchUniverse sig} {R : AliasResolver sig}
    {O : Type} (closed : U.StructurallyClosed)
    {Old New : StableCtx sig} (frame : SplitFrame U.toTypeUniverse R O Old New)
    (ctl : Control U R O frame.after) (addr : EvalAddr) :
    (A : Pos sig.nBases) → Results (FreshSPos (Old.append New) A) :=
  fun A => if hA : A ∈ U.pos then
    runSPosReset closed frame ctl addr ⟨A, hA⟩
  else []

@[simp] theorem resetPositiveProvider_of_mem {U : SearchUniverse sig}
    {R : AliasResolver sig} {O : Type} (closed : U.StructurallyClosed)
    {Old New : StableCtx sig} (frame : SplitFrame U.toTypeUniverse R O Old New)
    (ctl : Control U R O frame.after) (addr : EvalAddr)
    (hA : A ∈ U.pos) :
    resetPositiveProvider closed frame ctl addr A =
      runSPosReset closed frame ctl addr ⟨A, hA⟩ := by
  simp [resetPositiveProvider, hA]

@[simp] theorem runSPosReset_base {U : SearchUniverse sig}
    {R : AliasResolver sig} {O : Type} (frame : SplitFrame U.toTypeUniverse R O Old New) :
    (Segment.ofReset frame).frame.before = frame.after :=
  (Segment.ofReset frame).before_eq

theorem runSInv_outputs_fresh {U : SearchUniverse sig} {R : AliasResolver sig}
    {O : Type} {Base : Ctx2 U.toTypeUniverse} (closed : U.StructurallyClosed)
    (ctl : Control U R O Base) (addr : EvalAddr)
    (seg : Segment U.toTypeUniverse R O Base Old New)
    (resolved : ResolvedPending U O) (input : PendingInput U R O resolved)
    (G : Goal sig.nBases) (hG : G.InUniverse U)
    (t : FreshSInv Old New resolved.erase G)
    (_ht : t ∈ runSInv closed ctl addr seg resolved input G hG) :
    t.proof.freshValid = true := t.valid

theorem runSPos_outputs_fresh {U : SearchUniverse sig} {R : AliasResolver sig}
    {O : Type} {Base : Ctx2 U.toTypeUniverse} (closed : U.StructurallyClosed)
    (ctl : Control U R O Base) (addr : EvalAddr)
    (seg : Segment U.toTypeUniverse R O Base Γ .empty)
    (P : Pos sig.nBases) (hP : P ∈ U.pos) (p : FreshSPos Γ P)
    (_hp : p ∈ runSPos closed ctl addr seg P hP) :
    p.neutral.freshValid = true := p.valid

namespace LocalSaturatedEvalFixtures

theorem pending_zero_aborts {U : SearchUniverse sig} {R : AliasResolver sig}
    {O : Type} {Base : Ctx2 U.toTypeUniverse} (closed : U.StructurallyClosed)
    (ctl : Control U R O Base) (addr : EvalAddr)
    (seg : Segment U.toTypeUniverse R O Base Old New)
    (hz : Pos.zero ∈ U.pos) (K : DepSupport O) (rest : ResolvedPending U O)
    (input : PendingInput U R O (⟨⟨.zero, hz⟩, K⟩ :: rest))
    (G : Goal sig.nBases) (hG : G.InUniverse U) :
    runSInv closed ctl addr seg (⟨⟨.zero, hz⟩, K⟩ :: rest) input G hG =
      [FreshSInv.abort] := by simp [runSInv]

theorem empty_unit {U : SearchUniverse sig} {R : AliasResolver sig}
    {O : Type} {Base : Ctx2 U.toTypeUniverse} (closed : U.StructurallyClosed)
    (ctl : Control U R O Base) (addr : EvalAddr)
    (seg : Segment U.toTypeUniverse R O Base Old New)
    (input : PendingInput U R O []) (hOne : Neg.one ∈ U.neg) :
    runSInv closed ctl addr seg [] input (.neg .one) hOne =
      [FreshSInv.unit] := by simp [runSInv]

theorem empty_pair {U : SearchUniverse sig} {R : AliasResolver sig}
    {O : Type} {Base : Ctx2 U.toTypeUniverse} (closed : U.StructurallyClosed)
    (ctl : Control U R O Base) (addr : EvalAddr)
    (seg : Segment U.toTypeUniverse R O Base Old New)
    (input : PendingInput U R O []) (hProd : Neg.prod A B ∈ U.neg) :
    runSInv closed ctl addr seg [] input (.neg (.prod A B)) hProd =
      (runSInv closed ctl (.pairLeft :: addr) seg [] input (.neg A)
        (closed.prod_left hProd)).flatMap (fun l =>
          (runSInv closed ctl (.pairRight :: addr) seg [] input (.neg B)
            (closed.prod_right hProd)).map (FreshSInv.pair l)) := by simp [runSInv]

theorem empty_lam {U : SearchUniverse sig} {R : AliasResolver sig}
    {O : Type} {Base : Ctx2 U.toTypeUniverse} (closed : U.StructurallyClosed)
    (ctl : Control U R O Base) (addr : EvalAddr)
    (seg : Segment U.toTypeUniverse R O Base Old New)
    (input : PendingInput U R O []) (hArr : Neg.arr A B ∈ U.neg) :
    runSInv closed ctl addr seg [] input (.neg (.arr A B)) hArr =
      (PendingInput.lambdaChoices (O := O) ctl.flow (.lamBody :: addr)
        ⟨A, closed.arr_dom hArr⟩).flatMap (fun bodyInput =>
          (runSInv closed ctl (.lamBody :: addr) seg
            (ResolvedPending.lambdaPending ⟨A, closed.arr_dom hArr⟩)
            bodyInput (.neg B) (closed.arr_cod hArr)).map FreshSInv.lam) := by
  simp [runSInv]

theorem pending_sum_addresses :
    ([EvalEdge.caseLeft] : EvalAddr) ≠ [.caseRight] := by decide

theorem pending_sum_preserves_tail_and_separates_sites
    {U : SearchUniverse sig} {R : AliasResolver sig} {O : Type}
    (addr : EvalAddr)
    (hSum : Pos.sum A B ∈ U.pos) (hA : A ∈ U.pos) (hB : B ∈ U.pos)
    (K : DepSupport O) (rest : ResolvedPending U O)
    (input : PendingInput U R O (⟨⟨.sum A B, hSum⟩, K⟩ :: rest))
    (choice : SplitChoice R (input.sources.ref .here)) :
    (input.splitInputs hA hB choice).1.sources.dropHead =
        input.sources.dropHead ∧
      (input.splitInputs hA hB choice).2.sources.dropHead =
        input.sources.dropHead ∧
      (.caseLeft :: addr : EvalAddr) ≠ .caseRight :: addr := by
  exact ⟨rfl, rfl, by simp⟩

theorem missing_lambda_source_prunes
    {U : SearchUniverse sig} {R : AliasResolver sig} {O : Type}
    {Base : Ctx2 U.toTypeUniverse} (closed : U.StructurallyClosed)
    (ctl : Control U R O Base) (addr : EvalAddr)
    (seg : Segment U.toTypeUniverse R O Base Old New)
    (input : PendingInput U R O []) (hArr : Neg.arr A B ∈ U.neg)
    (hmissing : ctl.flow.lambdaSources (.lamBody :: addr)
      ⟨A, closed.arr_dom hArr⟩ = []) :
    runSInv closed ctl addr seg [] input (.neg (.arr A B)) hArr = [] := by
  simp [runSInv, PendingInput.lambdaChoices, hmissing]

theorem two_lambda_sources_give_two_results
    {U : SearchUniverse sig} {R : AliasResolver sig} {O : Type}
    {Base : Ctx2 U.toTypeUniverse} (closed : U.StructurallyClosed)
    (ctl : Control U R O Base) (addr : EvalAddr)
    (seg : Segment U.toTypeUniverse R O Base Old New)
    (input : PendingInput U R O []) (hArr : Neg.arr .zero B ∈ U.neg)
    (left right : ResolvedRef R Pos.zero.erase)
    (hsources : ctl.flow.lambdaSources (.lamBody :: addr)
      ⟨.zero, closed.arr_dom hArr⟩ = [left, right]) :
    runSInv closed ctl addr seg [] input (.neg (.arr .zero B)) hArr =
      [FreshSInv.lam FreshSInv.abort, FreshSInv.lam FreshSInv.abort] := by
  simp [runSInv, PendingInput.lambdaChoices, hsources,
    PendingInput.lambdaInput, ResolvedPending.lambdaPending]

theorem missing_split_choice_prunes
    {U : SearchUniverse sig} {R : AliasResolver sig} {O : Type}
    {Base : Ctx2 U.toTypeUniverse} (closed : U.StructurallyClosed)
    (ctl : Control U R O Base) (addr : EvalAddr)
    (seg : Segment U.toTypeUniverse R O Base Old New)
    (hSum : Pos.sum A B ∈ U.pos) (K : DepSupport O)
    (rest : ResolvedPending U O)
    (input : PendingInput U R O (⟨⟨.sum A B, hSum⟩, K⟩ :: rest))
    (G : Goal sig.nBases) (hG : G.InUniverse U)
    (hmissing : ctl.flow.splitChoices addr
      ⟨A, closed.sum_left hSum⟩ ⟨B, closed.sum_right hSum⟩
      (input.sources.ref .here) = []) :
    runSInv closed ctl addr seg (⟨⟨.sum A B, hSum⟩, K⟩ :: rest)
      input G hG = [] := by
  simp [runSInv, PendingInput.splitChoices, hmissing]

theorem one_shared_split_gives_both_siblings
    {U : SearchUniverse sig} {R : AliasResolver sig} {O : Type}
    {Base : Ctx2 U.toTypeUniverse} (closed : U.StructurallyClosed)
    (ctl : Control U R O Base) (addr : EvalAddr)
    (seg : Segment U.toTypeUniverse R O Base Old New)
    (hSum : Pos.sum .zero .zero ∈ U.pos) (K : DepSupport O)
    (rest : ResolvedPending U O)
    (input : PendingInput U R O (⟨⟨.sum .zero .zero, hSum⟩, K⟩ :: rest))
    (G : Goal sig.nBases) (hG : G.InUniverse U)
    (choice : SplitChoice R (input.sources.ref .here))
    (hchoice : ctl.flow.splitChoices addr
      ⟨.zero, closed.sum_left hSum⟩ ⟨.zero, closed.sum_right hSum⟩
      (input.sources.ref .here) = [choice]) :
    runSInv closed ctl addr seg (⟨⟨.sum .zero .zero, hSum⟩, K⟩ :: rest)
      input G hG = [FreshSInv.caseSum FreshSInv.abort FreshSInv.abort] := by
  simp [runSInv, PendingInput.splitChoices, PendingInput.splitInputs, hchoice]

theorem shifted_positive {U : SearchUniverse sig} {R : AliasResolver sig}
    {O : Type} {Base : Ctx2 U.toTypeUniverse} (closed : U.StructurallyClosed)
    (ctl : Control U R O Base) (addr : EvalAddr)
    (seg : Segment U.toTypeUniverse R O Base Γ .empty)
    (hShift : Pos.shift N ∈ U.pos) :
    runSPos closed ctl addr seg (.shift N) hShift =
      (runSInv closed ctl (.posShift :: addr) seg []
        ⟨PendingAssignment.empty R⟩ (.neg N)
        (closed.pos_shift hShift)).map FreshSPos.shift := by simp [runSPos]

theorem elimination_arguments_reset {U : SearchUniverse sig}
    {R : AliasResolver sig} {O : Type}
    (frame : SplitFrame U.toTypeUniverse R O Old New) :
    (Segment.ofReset frame).frame.before = frame.after :=
  runSPosReset_base frame

theorem application_spine_uses_reset_provider
    {U : SearchUniverse sig} {R : AliasResolver sig} {O : Type}
    (closed : U.StructurallyClosed)
    (frame : SplitFrame U.toTypeUniverse R O Old New)
    (ctl : Control U R O frame.after) (addr : EvalAddr)
    (hA : A ∈ U.pos) (head : FreshSNeg (Old.append New) (.arr A N))
    (spine : NegSpine N P) :
    NegSpine.fulfill (resetPositiveProvider closed frame ctl addr) head (.app spine) =
      (runSPosReset closed frame ctl addr ⟨A, hA⟩).flatMap (fun arg =>
        NegSpine.fulfill (resetPositiveProvider closed frame ctl addr)
          (head.app arg) spine) := by
  simp [resetPositiveProvider, hA]

theorem sat_done {Old New : StableCtx sig} (p : FreshSPos (Old.append New) P) :
    (FreshSat.done p).proof = Sat.done p.neutral := rfl

theorem batch_callback_frame_neutral
    (frame : SplitFrame U R O Old New) (selected : Pending sig) :
    frame.batchPending selected = frame :=
  frame.batchPending_frame_neutral selected

theorem one_batch_callback_stays_frame_neutral
    {U : SearchUniverse sig} {R : AliasResolver sig} {O : Type}
    {Base : Ctx2 U.toTypeUniverse} (ctl : Control U R O Base)
    (addr : EvalAddr) (seg : Segment U.toTypeUniverse R O Base Old New)
    (hP : P ∈ U.pos) (selected : SelectedBatch Old New ps)
    (body : FreshSInv (Old.append New) .empty ps (.pos P))
    (_returned : FreshSat.batch selected body ∈
      ctl.saturate addr seg ⟨P, hP⟩) :
    seg.frame.batchPending ps = seg.frame :=
  seg.frame.batchPending_frame_neutral ps

theorem sat_batch {Old New : StableCtx sig} (selected : SelectedBatch Old New ps)
    (body : FreshSInv (Old.append New) .empty ps (.pos P)) :
    (FreshSat.batch selected body).proof =
      Sat.batch selected.toNonemptyBatchObs body.proof := rfl

end LocalSaturatedEvalFixtures

end Gimbal.Equality.Scherer
