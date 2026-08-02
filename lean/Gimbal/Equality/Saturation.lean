/-
  Pair-directed saturation for Milestone 7.

  Builds one shared schedule from reachability, reconstructs witness neutrals
  from first-discovery parent pointers, and applies that ordered schedule to a
  focused continuation via nested `letPos`. Pair comparison feeds both terms
  through the same schedule.
-/

import Gimbal.Equality.Focus
import Gimbal.Equality.Reachability

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- Convert a snoc context into a reachability context (all hypotheses "new"). -/
def Ctx.toReachCtx : Ctx sig → ReachCtx sig.nBases
  | .empty => ⟨#[], 0⟩
  | .snoc Γ A =>
    let r := Γ.toReachCtx
    ⟨r.hyps.push A, r.newFrom⟩

/-- `ofHyps` recovers the snoc context used to build a reachability context. -/
theorem Ctx.ofHyps_toReachCtx (Γ : Ctx sig) :
    Ctx.ofHyps Γ.toReachCtx.hyps = Γ := by
  induction Γ with
  | empty => rfl
  | snoc Γ A ih =>
    simp [Ctx.toReachCtx, Ctx.ofHyps_push, ih]

/-- Reachability context with an explicit old/new split. -/
def Ctx.toReachCtxSplit (Γold Γnew : Ctx sig) : ReachCtx sig.nBases :=
  let old := Γold.toReachCtx
  let neu := Γnew.toReachCtx
  ⟨old.hyps ++ neu.hyps, old.hyps.size⟩

/--
Build the shared saturation schedule for a context/goal from the finite
reachability closure.
-/
def scheduleFor (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases) :
    Schedule sig.nBases :=
  buildSchedule (runReachability Γ goal)

/-- Schedule size helper for fixtures. -/
def scheduleSize (s : Schedule sig.nBases) : Nat :=
  s.size

/-! ### Witness reconstruction -/

/-- Find a hypothesis with exact type `A` (oldest wins). -/
def findHypVar (hyps : Array (Object sig.nBases)) (A : Object sig.nBases) :
    Option (Var (Ctx.ofHyps hyps) A) :=
  Id.run do
    for i in [:hyps.size] do
      match Ctx.varOldest hyps i with
      | some ⟨B, x⟩ =>
        if h : B = A then
          return some (h ▸ x)
        else
          pure ()
      | none => pure ()
    return none

private inductive ReconstructCmd (sig : Signature) where
  | neuOf (hyps : Array (Object sig.nBases)) (A : Object sig.nBases)
  | witness (hyps : Array (Object sig.nBases)) (w : Witness)
  | invOf (hyps : Array (Object sig.nBases)) (A : Object sig.nBases)

private inductive ReconstructVal (sig : Signature) where
  | neu (hyps : Array (Object sig.nBases)) (A : Object sig.nBases)
      (n : NegNeu (Ctx.ofHyps hyps) A) : ReconstructVal sig
  | wit (hyps : Array (Object sig.nBases))
      (p : (A : Object sig.nBases) × NegNeu (Ctx.ofHyps hyps) A) : ReconstructVal sig
  | inv (hyps : Array (Object sig.nBases)) (A : Object sig.nBases)
      (t : InvTm (Ctx.ofHyps hyps) A) : ReconstructVal sig

/-- Fueled witness reconstruction (single recursive worker). -/
def reconstructGo (fuel : Nat) (σ : ReachState sig.nBases) :
    ReconstructCmd sig → Option (ReconstructVal sig)
  | cmd =>
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match cmd with
      | .neuOf hyps A =>
        match findHypVar hyps A with
        | some x => some (.neu hyps A (.var x))
        | none =>
          match σ.findTypeIdx A with
          | none => none
          | some i =>
            match (σ.getCell i).witness with
            | none => none
            | some w =>
              match reconstructGo fuel σ (.witness hyps w) with
              | some (.wit hyps' ⟨B, n⟩) =>
                if hH : hyps' = hyps then
                  if h : B = A then
                    some (.neu hyps A (h ▸ NegNeu.castHyps hH n))
                  else none
                else none
              | _ => none
      | .witness hyps w =>
        match w with
        | .ctxVar hypIdx =>
          match Ctx.varOldest hyps hypIdx with
          | some ⟨A, x⟩ => some (.wit hyps ⟨A, .var x⟩)
          | none => none
        | .fst pIdx =>
          match σ.typeAt pIdx with
          | some (.prod L R) =>
            match reconstructGo fuel σ (.neuOf hyps (.prod L R)) with
            | some (.neu hyps' _A n) =>
              if hH : hyps' = hyps then
                if hA : _A = .prod L R then
                  some (.wit hyps ⟨L, .fst (NegNeu.cast hA (NegNeu.castHyps hH n))⟩)
                else none
              else none
            | _ => none
          | _ => none
        | .snd pIdx =>
          match σ.typeAt pIdx with
          | some (.prod L R) =>
            match reconstructGo fuel σ (.neuOf hyps (.prod L R)) with
            | some (.neu hyps' _A n) =>
              if hH : hyps' = hyps then
                if hA : _A = .prod L R then
                  some (.wit hyps ⟨R, .snd (NegNeu.cast hA (NegNeu.castHyps hH n))⟩)
                else none
              else none
            | _ => none
          | _ => none
        | .app fnHypIdx argIdx =>
          match hyps[fnHypIdx]?, σ.typeAt argIdx with
          | some (.exp Arg Ret), some Arg' =>
            if Arg' = Arg then
              match Ctx.varOldest hyps fnHypIdx,
                    reconstructGo fuel σ (.invOf hyps Arg) with
              | some ⟨fnTy, x⟩, some (.inv hyps' A' argTm) =>
                if hH : hyps' = hyps then
                  if hA : A' = Arg then
                    if hFn : fnTy = .exp Arg Ret then
                      some (.wit hyps ⟨Ret,
                        .app (NegNeu.cast hFn (.var x))
                          (InvTm.castTy hA (InvTm.castHyps hH argTm))⟩)
                    else none
                  else none
                else none
              | _, _ => none
            else
              none
          | _, _ => none
      | .invOf hyps A =>
        match reconstructGo fuel σ (.neuOf hyps A) with
        | some (.neu hyps' A' n) =>
          if hH : hyps' = hyps then
            if hA : A' = A then
              some (.inv hyps A (.foc (.pos (.done (.neu
                (NegNeu.cast hA (NegNeu.castHyps hH n)))))))
            else none
          else none
        | _ =>
          match A with
          | .unit => some (.inv hyps .unit .unit)
          | _ => none

/-- Reconstruct a negative neutral for a target type. -/
def neuOfType (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (A : Object sig.nBases) :
    Option (NegNeu (Ctx.ofHyps hyps) A) :=
  match reconstructGo fuel σ (.neuOf hyps A) with
  | some (.neu hyps' A' n) =>
    if hH : hyps' = hyps then
      if hA : A' = A then
        some (NegNeu.cast hA (NegNeu.castHyps hH n))
      else none
    else none
  | _ => none

/-- Reconstruct the neutral described by a witness parent pointer. -/
def reconstructWitness (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (w : Witness) :
    Option ((A : Object sig.nBases) × NegNeu (Ctx.ofHyps hyps) A) :=
  match reconstructGo fuel σ (.witness hyps w) with
  | some (.wit hyps' ⟨A, n⟩) =>
    if hH : hyps' = hyps then
      some ⟨A, NegNeu.castHyps hH n⟩
    else none
  | _ => none

/-! ### Schedule application -/

/-- Outcome of applying a saturation schedule. -/
inductive SaturateResult {sig : Signature} (Γ : Ctx sig) (A : Object sig.nBases) where
  | ok : InvTm Γ A → SaturateResult Γ A
  | exhausted
  | invariantFailure

def SaturateResult.toOption {sig : Signature} {Γ : Ctx sig} {A : Object sig.nBases} :
    SaturateResult Γ A → Option (InvTm Γ A)
  | .ok t => some t
  | .exhausted | .invariantFailure => none

/--
Apply schedule entries oldest-first as nested `letPos`, reconstructing each
witness in the growing hypothesis array (original Γ plus prior observations).
-/
def applyScheduleEntries (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases))
    (entries : List (Object sig.nBases × Witness))
    {A : Object sig.nBases}
    (cont : InvTm (Ctx.ofHyps hyps) A) : SaturateResult (Ctx.ofHyps hyps) A :=
  match fuel with
  | 0 => .exhausted
  | fuel + 1 =>
    match entries with
    | [] => .ok cont
    | (P, w) :: rest =>
      match reconstructWitness fuel σ hyps w with
      | none => .invariantFailure
      | some ⟨P', n⟩ =>
        if hP : P' = P then
          let nP : NegNeu (Ctx.ofHyps hyps) P := hP ▸ n
          let hyps' := hyps.push P
          have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ P :=
            Ctx.ofHyps_push hyps P
          let contW : InvTm (Ctx.ofHyps hyps ▻ P) A := cont.weaken
          let cont' : InvTm (Ctx.ofHyps hyps') A :=
            InvTm.castCtx hctx.symm contW
          match applyScheduleEntries fuel σ hyps' rest cont' with
          | .ok body' =>
            let body : InvTm (Ctx.ofHyps hyps ▻ P) A :=
              InvTm.castCtx hctx body'
            .ok (.foc (.letPos nP body))
          | .exhausted => .exhausted
          | .invariantFailure => .invariantFailure
        else
          .invariantFailure

/--
If `0` is deducible, collapse through `abort`; otherwise apply the consistency
schedule to the continuation.
-/
def applySchedule (fuel : Nat) (Γ : ReachCtx sig.nBases)
    (goal : Object sig.nBases) {A : Object sig.nBases}
    (cont : InvTm (Ctx.ofHyps Γ.hyps) A) :
    SaturateResult (Ctx.ofHyps Γ.hyps) A :=
  let σ := runReachability Γ goal
  if σ.inconsistent then
    match neuOfType fuel σ Γ.hyps (.never : Object sig.nBases) with
    | some n => .ok (.abort n)
    | none => .invariantFailure
  else
    let sched := buildSchedule σ
    applyScheduleEntries fuel σ Γ.hyps sched.entries.toList cont

/-- Saturate a continuation under a reachability context / goal. -/
def saturateApply (fuel : Nat) (Γ : ReachCtx sig.nBases)
    (goal : Object sig.nBases) {A : Object sig.nBases}
    (cont : InvTm (Ctx.ofHyps Γ.hyps) A) :
    SaturateResult (Ctx.ofHyps Γ.hyps) A :=
  applySchedule fuel Γ goal cont

/--
Enter the saturation phase: attach the reachability schedule to an invertible
continuation (syntax-level packaging; executable application is `saturateApply`).
-/
def saturate (Γ : ReachCtx sig.nBases) {Δ : Ctx sig} {A : Object sig.nBases}
    (goal : Object sig.nBases) (cont : InvTm Δ A) : SatTm Δ A :=
  .mk (scheduleFor Γ goal) cont

/-- Saturate under a focused context treated entirely as `Γnew`. -/
def saturateCtx {Γ : Ctx sig} {A : Object sig.nBases}
    (goal : Object sig.nBases) (cont : InvTm Γ A) : SatTm Γ A :=
  saturate Γ.toReachCtx goal cont

/-- Apply the shared schedule to a term already living in `Ctx.ofHyps`. -/
def saturateInv (fuel : Nat := 2048) (Γ : ReachCtx sig.nBases)
    (goal : Object sig.nBases) {A : Object sig.nBases}
    (t : InvTm (Ctx.ofHyps Γ.hyps) A) :
    SaturateResult (Ctx.ofHyps Γ.hyps) A :=
  saturateApply fuel Γ goal t

/-- Saturate under an arbitrary snoc context (via `toReachCtx`). -/
def saturateUnder (fuel : Nat := 2048) (Γ : Ctx sig)
    (goal : Object sig.nBases) {A : Object sig.nBases}
    (t : InvTm Γ A) : SaturateResult Γ A :=
  let r := Γ.toReachCtx
  have hctx : Ctx.ofHyps r.hyps = Γ := Ctx.ofHyps_toReachCtx Γ
  match saturateApply fuel r goal (InvTm.castCtx hctx.symm t) with
  | .ok t' => .ok (InvTm.castCtx hctx t')
  | .exhausted => .exhausted
  | .invariantFailure => .invariantFailure

end Equality
end Gimbal
