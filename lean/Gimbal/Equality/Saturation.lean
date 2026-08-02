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
        | .appTy fnTypeIdx argIdx =>
          match σ.typeAt fnTypeIdx, σ.typeAt argIdx with
          | some (.exp Arg Ret), some Arg' =>
            if Arg' = Arg then
              match reconstructGo fuel σ (.neuOf hyps (.exp Arg Ret)),
                    reconstructGo fuel σ (.invOf hyps Arg) with
              | some (.neu hyps₁ A₁ n), some (.inv hyps₂ A₂ argTm) =>
                if h1 : hyps₁ = hyps then
                  if h2 : hyps₂ = hyps then
                    if hFn : A₁ = .exp Arg Ret then
                      if hA : A₂ = Arg then
                        some (.wit hyps ⟨Ret,
                          .app (NegNeu.cast hFn (NegNeu.castHyps h1 n))
                            (InvTm.castTy hA (InvTm.castHyps h2 argTm))⟩)
                      else none
                    else none
                  else none
                else none
              | _, _ => none
            else
              none
          | _, _ => none
        | .unit =>
          -- `unit` witnesses only mark η-availability for apps; never scheduled.
          none
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
          | .prod L R =>
            match reconstructGo fuel σ (.invOf hyps L),
                  reconstructGo fuel σ (.invOf hyps R) with
            | some (.inv hyps₁ A₁ t), some (.inv hyps₂ A₂ u) =>
              if h1 : hyps₁ = hyps then
                if h2 : hyps₂ = hyps then
                  if hL : A₁ = L then
                    if hR : A₂ = R then
                      some (.inv hyps (.prod L R)
                        (.pair
                          (InvTm.castTy hL (InvTm.castHyps h1 t))
                          (InvTm.castTy hR (InvTm.castHyps h2 u))))
                    else none
                  else none
                else none
              else none
            | _, _ => none
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

/-! ### Term-demanded positive types -/

/-- Push `A` if positive and not already present. -/
def pushDemand (acc : Array (Object sig.nBases)) (A : Object sig.nBases) :
    Array (Object sig.nBases) :=
  if objectPolarity A == .pos && !acc.contains A then acc.push A else acc

mutual
def demandsNegNeu {Γ : Ctx sig} {A : Object sig.nBases} :
    NegNeu Γ A → Array (Object sig.nBases) → Array (Object sig.nBases)
  | .var _, acc => pushDemand acc A
  | .app n t, acc => demandsInvTm t (demandsNegNeu n acc)
  | .fst n, acc => pushDemand (demandsNegNeu n acc) A
  | .snd n, acc => pushDemand (demandsNegNeu n acc) A

def demandsPosNeu {Γ : Ctx sig} {A : Object sig.nBases} :
    PosNeu Γ A → Array (Object sig.nBases) → Array (Object sig.nBases)
  | .neu n, acc => demandsNegNeu n (pushDemand acc A)
  | .inl p, acc => demandsPosNeu p (pushDemand acc A)
  | .inr p, acc => demandsPosNeu p (pushDemand acc A)

def demandsInvTm {Γ : Ctx sig} {A : Object sig.nBases} :
    InvTm Γ A → Array (Object sig.nBases) → Array (Object sig.nBases)
  | .unit, acc => acc
  | .pair t u, acc => demandsInvTm u (demandsInvTm t acc)
  | .lam t, acc => demandsInvTm t acc
  | .case n t u, acc =>
      demandsInvTm u (demandsInvTm t (demandsNegNeu n acc))
  | .abort n, acc => demandsNegNeu n acc
  | .foc f, acc => demandsFocTm f acc

def demandsFocTm {Γ : Ctx sig} {A : Object sig.nBases} :
    FocTm Γ A → Array (Object sig.nBases) → Array (Object sig.nBases)
  | .pos (.done p), acc => demandsPosNeu p acc
  | .neg (.done n), acc => demandsNegNeu n acc
  | .letPos n t, acc => demandsInvTm t (demandsNegNeu n acc)
  | .sat (.mk _ t), acc => demandsInvTm t acc
end

/-- Positive types demanded by a focused term (exact observations). -/
def collectDemands {Γ : Ctx sig} {A : Object sig.nBases}
    (t : InvTm Γ A) : Array (Object sig.nBases) :=
  demandsInvTm t #[]

/--
Union consistency witnesses with term-demanded positive types.
Demands are realized via the reachability first-discovery witness when the type
is simply deducible and not yet retrievable. Ordered by subformula-table index.
-/
def mergeSchedule (σ : ReachState sig.nBases) (consistency : Schedule sig.nBases)
    (demandTys : Array (Object sig.nBases)) : Schedule sig.nBases :=
  Id.run do
    let mut entries := consistency.entries
    for A in demandTys do
      if objectPolarity A == .pos && !entries.any (fun e => e.1 == A) then
        match σ.findTypeIdx A with
        | some i =>
          let c := σ.getCell i
          if c.simplyDeducible && !c.retrievable then
            match c.witness with
            | some w => entries := entries.push (A, w)
            | none => pure ()
          else
            pure ()
        | none => pure ()
    -- Deterministic order: subformula-table index, then first-seen.
    let mut ordered : Array (Object sig.nBases × Witness) := #[]
    for i in [:σ.types.size] do
      match σ.typeAt i with
      | some A =>
        match entries.findIdx? (fun e => e.1 == A) with
        | some j =>
          match entries[j]? with
          | some e => ordered := ordered.push e
          | none => pure ()
        | none => pure ()
      | none => pure ()
    -- Any leftover (type outside table) keep at end in prior order.
    for e in entries do
      if !ordered.any (fun o => o.1 == e.1) then
        ordered := ordered.push e
    pure ⟨ordered⟩

/-- Shared pair-directed schedule from reachability + both terms' demands. -/
def pairSchedule (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases)
    {Δ : Ctx sig} {A : Object sig.nBases}
    (t u : InvTm Δ A) : Schedule sig.nBases × ReachState sig.nBases :=
  let σ := runReachability Γ goal
  let dem := collectDemands t ++ collectDemands u
  let sched := mergeSchedule σ (buildSchedule σ) dem
  (sched, σ)

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
Apply schedule entries oldest-first. Positive types are inverted:
`never` collapses to `abort`; coproducts case-split; atoms bind via `letPos`.
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
          match hPeq : P with
          | .never =>
              .ok (.abort (A := A) (hPeq ▸ nP))
          | .coprod L R =>
              let nSum : NegNeu (Ctx.ofHyps hyps) (.coprod L R) := hPeq ▸ nP
              let hypsL := hyps.push L
              let hypsR := hyps.push R
              have hL : Ctx.ofHyps hypsL = Ctx.ofHyps hyps ▻ L :=
                Ctx.ofHyps_push hyps L
              have hR : Ctx.ofHyps hypsR = Ctx.ofHyps hyps ▻ R :=
                Ctx.ofHyps_push hyps R
              let contL : InvTm (Ctx.ofHyps hypsL) A :=
                InvTm.castCtx hL.symm cont.weaken
              let contR : InvTm (Ctx.ofHyps hypsR) A :=
                InvTm.castCtx hR.symm cont.weaken
              match applyScheduleEntries fuel σ hypsL rest contL,
                    applyScheduleEntries fuel σ hypsR rest contR with
              | .ok bodyL', .ok bodyR' =>
                  .ok (.case nSum
                    (InvTm.castCtx hL bodyL')
                    (InvTm.castCtx hR bodyR'))
              | .exhausted, _ | _, .exhausted => .exhausted
              | .invariantFailure, _ | _, .invariantFailure => .invariantFailure
          | _ =>
              let hyps' := hyps.push P
              have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ P :=
                Ctx.ofHyps_push hyps P
              let cont' : InvTm (Ctx.ofHyps hyps') A :=
                InvTm.castCtx hctx.symm cont.weaken
              match applyScheduleEntries fuel σ hyps' rest cont' with
              | .ok body' =>
                  .ok (.foc (.letPos nP (InvTm.castCtx hctx body')))
              | .exhausted => .exhausted
              | .invariantFailure => .invariantFailure
        else
          .invariantFailure

/--
Saturation invariant on `Γold`: every positive type simply deducible from the
old fragment alone must already be retrievable.
-/
def checkOldInvariant (Γold : ReachCtx sig.nBases) (goal : Object sig.nBases) :
    Bool :=
  let σ := runReachability Γold goal
  Id.run do
    for i in [:σ.types.size] do
      match σ.typeAt i, σ.getCell i with
      | some A, c =>
        if objectPolarity A == .pos && c.simplyDeducible && !c.retrievable then
          return false
      | _, _ => pure ()
    return true

/--
If `0` is deducible, collapse through `abort`; otherwise apply the given
schedule to the continuation.
-/
def applyFixedSchedule (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (sched : Schedule sig.nBases)
    {A : Object sig.nBases}
    (cont : InvTm (Ctx.ofHyps hyps) A) :
    SaturateResult (Ctx.ofHyps hyps) A :=
  if σ.inconsistent then
    match neuOfType fuel σ hyps (.never : Object sig.nBases) with
    | some n => .ok (.abort n)
    | none => .invariantFailure
  else
    applyScheduleEntries fuel σ hyps sched.entries.toList cont

/--
If `0` is deducible, collapse through `abort`; otherwise apply the consistency
schedule to the continuation.
-/
def applySchedule (fuel : Nat) (Γ : ReachCtx sig.nBases)
    (goal : Object sig.nBases) {A : Object sig.nBases}
    (cont : InvTm (Ctx.ofHyps Γ.hyps) A) :
    SaturateResult (Ctx.ofHyps Γ.hyps) A :=
  let σ := runReachability Γ goal
  applyFixedSchedule fuel σ Γ.hyps (buildSchedule σ) cont

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
