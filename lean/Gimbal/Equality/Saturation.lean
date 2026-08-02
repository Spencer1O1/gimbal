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
        | .unit | .inl _ | .inr _ | .eta =>
          -- Introduction witnesses justify invertible args only; never neutrals.
          none
      | .invOf hyps A =>
        match reconstructGo fuel σ (.neuOf hyps A) with
        | some (.neu hyps' A' n) =>
          if hH : hyps' = hyps then
            if hA : A' = A then
              let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
              match objectPolarity A with
              | .pos => some (.inv hyps A (.foc (.pos (.done (.neu n')))))
              | .neg => some (.inv hyps A (.foc (.neg (.done n'))))
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
          | .coprod L R =>
            let preferRight :=
              match σ.findTypeIdx (.coprod L R) with
              | some i =>
                match (σ.getCell i).witness with
                | some (.inr _) => true
                | _ => false
              | none => false
            let inlVal : Option (ReconstructVal sig) :=
              match reconstructGo fuel σ (.invOf hyps L) with
              | some (.inv hyps' A' (.foc (.pos (.done p)))) =>
                if hH : hyps' = hyps then
                  if hA : A' = L then
                    some (.inv hyps (.coprod L R)
                      (.foc (.pos (.done (.inl (hA ▸ (hH ▸ p)))))))
                  else none
                else none
              | _ => none
            let inrVal : Option (ReconstructVal sig) :=
              match reconstructGo fuel σ (.invOf hyps R) with
              | some (.inv hyps' A' (.foc (.pos (.done p)))) =>
                if hH : hyps' = hyps then
                  if hA : A' = R then
                    some (.inv hyps (.coprod L R)
                      (.foc (.pos (.done (.inr (hA ▸ (hH ▸ p)))))))
                  else none
                else none
              | _ => none
            if preferRight then
              match inrVal with
              | some v => some v
              | none => inlVal
            else
              match inlVal with
              | some v => some v
              | none => inrVal
          | .exp Arg Ret =>
            -- Identity expansion: `λ x. t` when `t : Ret` under `hyps ▻ Arg`.
            let hyps' := hyps.push Arg
            have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ Arg :=
              Ctx.ofHyps_push hyps Arg
            match reconstructGo fuel σ (.invOf hyps' Ret) with
            | some (.inv hyps'' B t) =>
              if hH : hyps'' = hyps' then
                if hB : B = Ret then
                  let body : InvTm (Ctx.ofHyps hyps ▻ Arg) Ret :=
                    InvTm.castCtx hctx
                      (InvTm.castTy hB (InvTm.castHyps hH t))
                  some (.inv hyps (.exp Arg Ret) (.lam body))
                else none
              else none
            | _ => none
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

/-! ### Exact demand neutrals -/

/-- One scheduled observation: consistency witness or exact term neutral. -/
inductive PairEntry (sig : Signature) (hyps : Array (Object sig.nBases)) where
  | consistency (P : Object sig.nBases) (w : Witness)
  | exact (P : Object sig.nBases) (n : NegNeu (Ctx.ofHyps hyps) P)

def PairEntry.ty {sig : Signature} {hyps : Array (Object sig.nBases)} :
    PairEntry sig hyps → Object sig.nBases
  | .consistency P _ => P
  | .exact P _ => P

private inductive ExactCmd (sig : Signature) (Γ : Ctx sig) where
  | neu {A : Object sig.nBases} : NegNeu Γ A → ExactCmd sig Γ
  | pos {A : Object sig.nBases} : PosNeu Γ A → ExactCmd sig Γ
  | inv {A : Object sig.nBases} : InvTm Γ A → ExactCmd sig Γ
  | foc {A : Object sig.nBases} : FocTm Γ A → ExactCmd sig Γ

/-- Exact identity: same result type and raw neutral spine. -/
def exactIdEq {Γ : Ctx sig}
    (e₁ e₂ : (P : Object sig.nBases) × NegNeu Γ P) : Bool :=
  e₁.1 == e₂.1 && NegNeu.toRaw e₁.2 == NegNeu.toRaw e₂.2

/-- Collect exact positive-typed negative neutrals at the current context.
Deduplicates by neutral identity, not by result type alone. -/
def exactGo (fuel : Nat) {Γ : Ctx sig} :
    ExactCmd sig Γ → Array ((P : Object sig.nBases) × NegNeu Γ P) →
    Array ((P : Object sig.nBases) × NegNeu Γ P)
  | cmd, acc =>
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      match cmd with
      | .neu (A := A) n =>
        let acc :=
          if objectPolarity A == .pos then
            let e : (P : Object sig.nBases) × NegNeu Γ P := ⟨A, n⟩
            if acc.any (exactIdEq e) then acc else acc.push e
          else acc
        match n with
        | .var _ => acc
        | .app n t => exactGo fuel (.inv t) (exactGo fuel (.neu n) acc)
        | .fst n => exactGo fuel (.neu n) acc
        | .snd n => exactGo fuel (.neu n) acc
      | .pos (.neu n) => exactGo fuel (.neu n) acc
      | .pos (.inl p) => exactGo fuel (.pos p) acc
      | .pos (.inr p) => exactGo fuel (.pos p) acc
      | .inv .unit => acc
      | .inv (.pair t u) => exactGo fuel (.inv u) (exactGo fuel (.inv t) acc)
      | .inv (.lam _) => acc
      | .inv (.case n _ _) => exactGo fuel (.neu n) acc
      | .inv (.abort n) => exactGo fuel (.neu n) acc
      | .inv (.foc f) => exactGo fuel (.foc f) acc
      | .foc (.pos (.done p)) => exactGo fuel (.pos p) acc
      | .foc (.neg (.done n)) => exactGo fuel (.neu n) acc
      | .foc (.letPos n _) => exactGo fuel (.neu n) acc
      | .foc (.sat (.mk _ t)) => exactGo fuel (.inv t) acc

def collectExact {Γ : Ctx sig} {A : Object sig.nBases}
    (t : InvTm Γ A) : Array ((P : Object sig.nBases) × NegNeu Γ P) :=
  exactGo 4096 (.inv t) #[]

/-! ### Exact newness (current-phase observations must use Γnew) -/

/-- Hypothesis array index for a de Bruijn-from-end raw index. -/
def rawIdxToHypIdx (hypsSize rawIdx : Nat) : Option Nat :=
  if rawIdx < hypsSize then some (hypsSize - 1 - rawIdx) else none

/-- Variable mentions at least one hypothesis in the new fragment. -/
def varMentionsNew (hypsSize newFrom : Nat) (rawIdx : Nat) : Bool :=
  match rawIdxToHypIdx hypsSize rawIdx with
  | some i => decide (newFrom ≤ i)
  | none => false

mutual
/-- Whether a negative neutral depends on at least one new hypothesis. -/
def NegNeu.mentionsNew (hypsSize newFrom : Nat) {Γ : Ctx sig}
    {A : Object sig.nBases} : NegNeu Γ A → Bool
  | .var x => varMentionsNew hypsSize newFrom x.toRawIdx
  | .app n t =>
      NegNeu.mentionsNew hypsSize newFrom n ||
        InvTm.mentionsNew hypsSize newFrom t
  | .fst n => NegNeu.mentionsNew hypsSize newFrom n
  | .snd n => NegNeu.mentionsNew hypsSize newFrom n

def InvTm.mentionsNew (hypsSize newFrom : Nat) {Γ : Ctx sig}
    {A : Object sig.nBases} : InvTm Γ A → Bool
  | .unit => false
  | .pair t u =>
      InvTm.mentionsNew hypsSize newFrom t || InvTm.mentionsNew hypsSize newFrom u
  | .lam t => InvTm.mentionsNew (hypsSize + 1) newFrom t
  | .case n t u =>
      NegNeu.mentionsNew hypsSize newFrom n ||
        InvTm.mentionsNew (hypsSize + 1) newFrom t ||
        InvTm.mentionsNew (hypsSize + 1) newFrom u
  | .abort n => NegNeu.mentionsNew hypsSize newFrom n
  | .foc f => FocTm.mentionsNew hypsSize newFrom f

def FocTm.mentionsNew (hypsSize newFrom : Nat) {Γ : Ctx sig}
    {A : Object sig.nBases} : FocTm Γ A → Bool
  | .pos (.done p) => PosNeu.mentionsNew hypsSize newFrom p
  | .neg (.done n) => NegNeu.mentionsNew hypsSize newFrom n
  | .letPos n t =>
      NegNeu.mentionsNew hypsSize newFrom n ||
        InvTm.mentionsNew (hypsSize + 1) newFrom t
  | .sat (.mk _ t) => InvTm.mentionsNew hypsSize newFrom t

def PosNeu.mentionsNew (hypsSize newFrom : Nat) {Γ : Ctx sig}
    {A : Object sig.nBases} : PosNeu Γ A → Bool
  | .neu n => NegNeu.mentionsNew hypsSize newFrom n
  | .inl p => PosNeu.mentionsNew hypsSize newFrom p
  | .inr p => PosNeu.mentionsNew hypsSize newFrom p
end

/-- Every selected exact observation in this phase must mention `Γnew`. -/
def exactsAllUseNew (hypsSize newFrom : Nat) {Γ : Ctx sig}
    (exact : Array ((P : Object sig.nBases) × NegNeu Γ P)) : Bool :=
  exact.all fun e => NegNeu.mentionsNew hypsSize newFrom e.2

/--
Exact neutrals that still need observation.
A type may already be retrievable from a hypothesis while a distinct exact
neutral (e.g. `f ()` vs hyp `x : X`) still requires strong positive cut.
Bare hypothesis variables are skipped — they are already bound.
-/
def selectExactObs (_σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases))
    (exact : Array ((P : Object sig.nBases) × NegNeu (Ctx.ofHyps hyps) P)) :
    Array ((P : Object sig.nBases) × NegNeu (Ctx.ofHyps hyps) P) :=
  Id.run do
    let mut out :
        Array ((P : Object sig.nBases) × NegNeu (Ctx.ofHyps hyps) P) := #[]
    for e in exact do
      if objectPolarity e.1 == .pos && !out.any (exactIdEq e) then
        let bareHyp :=
          match e.2 with
          | .var _ => true
          | _ => false
        if !bareHyp then
          out := out.push e
    pure out

/-- Commutative idempotent union of exact neutrals by identity. -/
def unionExact {Γ : Ctx sig}
    (a b : Array ((P : Object sig.nBases) × NegNeu Γ P)) :
    Array ((P : Object sig.nBases) × NegNeu Γ P) :=
  Id.run do
    let mut out : Array ((P : Object sig.nBases) × NegNeu Γ P) := #[]
    for e in a do
      if !out.any (exactIdEq e) then out := out.push e
    for e in b do
      if !out.any (exactIdEq e) then out := out.push e
    pure out

/-- Stable identity for a schedule entry (left/right-insensitive). -/
def PairEntry.idEq {sig : Signature} {hyps : Array (Object sig.nBases)} :
    PairEntry sig hyps → PairEntry sig hyps → Bool
  | .exact P n, .exact Q m => P == Q && NegNeu.toRaw n == NegNeu.toRaw m
  | .consistency P w, .consistency Q v => P == Q && w == v
  | _, _ => false

/--
Deterministic total key for schedule ordering (tie-break after dependencies).
Format: `typeIdx|0|raw` for exact, `typeIdx|1` for consistency.
-/
def PairEntry.sortKey {sig : Signature} {hyps : Array (Object sig.nBases)}
    (σ : ReachState sig.nBases) : PairEntry sig hyps → String
  | .exact P n =>
      let ti := (σ.findTypeIdx P).getD σ.types.size
      s!"{ti}|0|{repr (NegNeu.toRaw n)}"
  | .consistency P _ =>
      let ti := (σ.findTypeIdx P).getD σ.types.size
      s!"{ti}|1"

/-- Later entry depends on earlier: later's exact spine properly contains earlier's. -/
def PairEntry.dependsOn {sig : Signature} {hyps : Array (Object sig.nBases)} :
    PairEntry sig hyps → PairEntry sig hyps → Bool
  | .exact _ later, .exact _ earlier =>
      RawNeu.dependsOn (NegNeu.toRaw later) (NegNeu.toRaw earlier)
  | _, _ => false

/--
Topological order of observations: dependencies first, then `sortKey` tie-break.
Guarantees left/right symmetry once the entry multiset is fixed.
-/
def canonicalizePairObsOrder {sig : Signature} {hyps : Array (Object sig.nBases)}
    (σ : ReachState sig.nBases) (entries : Array (PairEntry sig hyps)) :
    Array (PairEntry sig hyps) :=
  Id.run do
    let n := entries.size
    if n == 0 then return #[]
    let mut indeg : Array Nat := Array.replicate n 0
    for j in [:n] do
      for i in [:n] do
        if i != j then
          match entries[i]?, entries[j]? with
          | some ei, some ej =>
            -- edge i → j when j depends on i (i must precede j)
            if PairEntry.dependsOn ej ei then
              indeg := indeg.set! j (indeg[j]! + 1)
          | _, _ => pure ()
    let mut remaining : Array Bool := Array.replicate n true
    let mut out : Array (PairEntry sig hyps) := #[]
    for _ in [:n] do
      let mut best : Option Nat := none
      for i in [:n] do
        if remaining[i]! && indeg[i]! == 0 then
          match entries[i]? with
          | none => pure ()
          | some e =>
            match best with
            | none => best := some i
            | some b =>
              match entries[b]? with
              | some eb =>
                if PairEntry.sortKey σ e < PairEntry.sortKey σ eb then
                  best := some i
              | none => best := some i
      match best with
      | none =>
        -- Cycle fallback: emit remaining by sortKey (should not arise for spines).
        let mut rest : Array (Nat × PairEntry sig hyps) := #[]
        for i in [:n] do
          if remaining[i]! then
            match entries[i]? with
            | some e => rest := rest.push (i, e)
            | none => pure ()
        let rest' := rest.qsort fun a b =>
          PairEntry.sortKey σ a.2 < PairEntry.sortKey σ b.2
        for p in rest' do out := out.push p.2
        return out
      | some i =>
        match entries[i]? with
        | none => return out
        | some e =>
          out := out.push e
          remaining := remaining.set! i false
          for j in [:n] do
            if remaining[j]! then
              match entries[j]? with
              | some ej =>
                if PairEntry.dependsOn ej e then
                  indeg := indeg.set! j (indeg[j]! - 1)
              | none => pure ()
    pure out

/--
Union consistency witnesses with exact term-demanded neutrals, then
canonicalize order (dependency DAG + stable key).
-/
def mergePairObs (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases))
    (consistency : Schedule sig.nBases)
    (exactSrc : Array ((P : Object sig.nBases) × NegNeu (Ctx.ofHyps hyps) P)) :
    Array (PairEntry sig hyps) :=
  Id.run do
    let mut bag : Array (PairEntry sig hyps) := #[]
    for e in exactSrc do
      bag := bag.push (.exact e.1 e.2)
    let hasExactTy (A : Object sig.nBases) : Bool :=
      exactSrc.any (fun e => e.1 == A)
    for e in consistency.entries do
      if !hasExactTy e.1 && !bag.any fun
          | .consistency Q _ => Q == e.1
          | .exact .. => false
      then
        bag := bag.push (.consistency e.1 e.2)
    pure (canonicalizePairObsOrder σ bag)

/-- Outcome of building the shared pair observation list. -/
inductive PairObsResult (sig : Signature) (hyps : Array (Object sig.nBases)) where
  | ok : Array (PairEntry sig hyps) → ReachState sig.nBases → PairObsResult sig hyps
  | invariantFailure

/-- Schedule entry lists compare equal under `PairEntry.idEq`. -/
def pairObsEntriesEq {sig : Signature} {hyps : Array (Object sig.nBases)}
    (a b : Array (PairEntry sig hyps)) : Bool :=
  a.size == b.size &&
    Id.run do
      for i in [:a.size] do
        match a[i]?, b[i]? with
        | some ea, some eb =>
          if !PairEntry.idEq ea eb then return false
        | _, _ => return false
      pure true

/--
Build the shared pair-directed observation list: consistency ∪ exact demands
from both terms (union is left/right-symmetric). Old-only exact neutrals
selected for observation are an invariant failure. Order is dependency-respecting
and deterministic.
-/
def pairObs (Γ : ReachCtx sig.nBases) (goal : Object sig.nBases)
    {A : Object sig.nBases}
    (t u : InvTm (Ctx.ofHyps Γ.hyps) A) : PairObsResult sig Γ.hyps :=
  let σ := runReachability Γ goal
  let exactSel :=
    selectExactObs σ Γ.hyps (unionExact (collectExact t) (collectExact u))
  if !exactsAllUseNew Γ.hyps.size Γ.newFrom exactSel then
    .invariantFailure
  else
    .ok (mergePairObs σ Γ.hyps (buildSchedule σ) exactSel) σ

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
    for e in entries do
      if !ordered.any (fun o => o.1 == e.1) then
        ordered := ordered.push e
    pure ⟨ordered⟩

/-- Shared pair-directed schedule from reachability + both terms' demand types. -/
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

/-- Weaken a negative neutral across a list of newest binders. -/
def NegNeu.weakenMany {Γ : Ctx sig} {A : Object sig.nBases} :
    (extras : List (Object sig.nBases)) → NegNeu Γ A →
    NegNeu (extras.foldl Ctx.snoc Γ) A
  | [], n => n
  | _B :: Bs, n => NegNeu.weakenMany Bs (NegNeu.weaken n)

/-! ### Strong positive cut (neutral abstraction) -/

mutual
/-- Shift a raw spine under one newest binder (all de Bruijn indices +1). -/
def RawNeu.shift : RawNeu → RawNeu
  | .var i => .var (i + 1)
  | .app n a => .app (RawNeu.shift n) (RawFocused.shift a)
  | .fst n => .fst (RawNeu.shift n)
  | .snd n => .snd (RawNeu.shift n)

def RawPos.shift : RawPos → RawPos
  | .neu n => .neu (RawNeu.shift n)
  | .inl p => .inl (RawPos.shift p)
  | .inr p => .inr (RawPos.shift p)

def RawFocused.shift : RawFocused → RawFocused
  | .unit => .unit
  | .pair t u => .pair (RawFocused.shift t) (RawFocused.shift u)
  | .lam t => .lam (RawFocused.shift t)
  | .case s t u =>
      .case (RawNeu.shift s) (RawFocused.shift t) (RawFocused.shift u)
  | .abort n => .abort (RawNeu.shift n)
  | .pos p => .pos (RawPos.shift p)
  | .neg n => .neg (RawNeu.shift n)
  | .letPos n t => .letPos (RawNeu.shift n) (RawFocused.shift t)
  | .sat k t => .sat k (RawFocused.shift t)
end

mutual
/--
Replace occurrences of the observed neutral (raw spine `targetRaw`)
by the abstraction variable `x` (initially `.here` under `Γ ▻ P`).
-/
def NegNeu.abstractAtom {Γ : Ctx sig} {P A : Object sig.nBases}
    (x : Var Γ P) (targetRaw : RawNeu) : NegNeu Γ A → NegNeu Γ A
  | .var y =>
      if NegNeu.toRaw (.var y) == targetRaw then
        match decEq A P with
        | isTrue h => h ▸ .var x
        | isFalse _ => .var y
      else
        .var y
  | .app f a =>
      if NegNeu.toRaw (.app f a) == targetRaw then
        match decEq A P with
        | isTrue h => h ▸ .var x
        | isFalse _ =>
            .app (NegNeu.abstractAtom x targetRaw f) (InvTm.abstractAtom x targetRaw a)
      else
        .app (NegNeu.abstractAtom x targetRaw f) (InvTm.abstractAtom x targetRaw a)
  | .fst m =>
      if NegNeu.toRaw (.fst m) == targetRaw then
        match decEq A P with
        | isTrue h => h ▸ .var x
        | isFalse _ => .fst (NegNeu.abstractAtom x targetRaw m)
      else
        .fst (NegNeu.abstractAtom x targetRaw m)
  | .snd m =>
      if NegNeu.toRaw (.snd m) == targetRaw then
        match decEq A P with
        | isTrue h => h ▸ .var x
        | isFalse _ => .snd (NegNeu.abstractAtom x targetRaw m)
      else
        .snd (NegNeu.abstractAtom x targetRaw m)

def PosNeu.abstractAtom {Γ : Ctx sig} {P A : Object sig.nBases}
    (x : Var Γ P) (targetRaw : RawNeu) : PosNeu Γ A → PosNeu Γ A
  | .neu n => .neu (NegNeu.abstractAtom x targetRaw n)
  | .inl p => .inl (PosNeu.abstractAtom x targetRaw p)
  | .inr p => .inr (PosNeu.abstractAtom x targetRaw p)

def InvTm.abstractAtom {Γ : Ctx sig} {P A : Object sig.nBases}
    (x : Var Γ P) (targetRaw : RawNeu) : InvTm Γ A → InvTm Γ A
  | .unit => .unit
  | .pair t u =>
      .pair (InvTm.abstractAtom x targetRaw t) (InvTm.abstractAtom x targetRaw u)
  | .lam t => .lam (InvTm.abstractAtom (.there x) (RawNeu.shift targetRaw) t)
  | .case n t u =>
      .case (NegNeu.abstractAtom x targetRaw n)
        (InvTm.abstractAtom (.there x) (RawNeu.shift targetRaw) t)
        (InvTm.abstractAtom (.there x) (RawNeu.shift targetRaw) u)
  | .abort n => .abort (NegNeu.abstractAtom x targetRaw n)
  | .foc f => .foc (FocTm.abstractAtom x targetRaw f)

def FocTm.abstractAtom {Γ : Ctx sig} {P A : Object sig.nBases}
    (x : Var Γ P) (targetRaw : RawNeu) : FocTm Γ A → FocTm Γ A
  | .pos (.done p) => .pos (.done (PosNeu.abstractAtom x targetRaw p))
  | .neg (.done n) => .neg (.done (NegNeu.abstractAtom x targetRaw n))
  | .letPos n t =>
      .letPos (NegNeu.abstractAtom x targetRaw n)
        (InvTm.abstractAtom (.there x) (RawNeu.shift targetRaw) t)
  | .sat (.mk s t) => .sat (.mk s (InvTm.abstractAtom x targetRaw t))

/-- Sum-branch walk and injection synthesis (same mutual as abstractAtom). -/
def NegNeu.abstractSum {Γ : Ctx sig} {B A : Object sig.nBases}
    (x : Var Γ B) (targetRaw : RawNeu) : NegNeu Γ A → NegNeu Γ A
  | .var y => .var y
  | .app f a =>
      .app (NegNeu.abstractSum x targetRaw f) (InvTm.abstractSumWalk x targetRaw a)
  | .fst m => .fst (NegNeu.abstractSum x targetRaw m)
  | .snd m => .snd (NegNeu.abstractSum x targetRaw m)

def PosNeu.abstractSumWalk {Γ : Ctx sig} {B A : Object sig.nBases}
    (x : Var Γ B) (targetRaw : RawNeu) : PosNeu Γ A → PosNeu Γ A
  | .neu n => .neu (NegNeu.abstractSum x targetRaw n)
  | .inl p => .inl (PosNeu.abstractSumWalk x targetRaw p)
  | .inr p => .inr (PosNeu.abstractSumWalk x targetRaw p)

def InvTm.abstractSumWalk {Γ : Ctx sig} {B A : Object sig.nBases}
    (x : Var Γ B) (targetRaw : RawNeu) : InvTm Γ A → InvTm Γ A
  | .unit => .unit
  | .pair t u =>
      .pair (InvTm.abstractSumWalk x targetRaw t) (InvTm.abstractSumWalk x targetRaw u)
  | .lam t => .lam (InvTm.abstractSumWalk (.there x) (RawNeu.shift targetRaw) t)
  | .case n t u =>
      .case (NegNeu.abstractSum x targetRaw n)
        (InvTm.abstractSumWalk (.there x) (RawNeu.shift targetRaw) t)
        (InvTm.abstractSumWalk (.there x) (RawNeu.shift targetRaw) u)
  | .abort n => .abort (NegNeu.abstractSum x targetRaw n)
  | .foc f => .foc (FocTm.abstractSumWalk x targetRaw f)

def FocTm.abstractSumWalk {Γ : Ctx sig} {B A : Object sig.nBases}
    (x : Var Γ B) (targetRaw : RawNeu) : FocTm Γ A → FocTm Γ A
  | .pos (.done p) => .pos (.done (PosNeu.abstractSumWalk x targetRaw p))
  | .neg (.done n) => .neg (.done (NegNeu.abstractSum x targetRaw n))
  | .letPos n t =>
      .letPos (NegNeu.abstractSum x targetRaw n)
        (InvTm.abstractSumWalk (.there x) (RawNeu.shift targetRaw) t)
  | .sat (.mk s t) => .sat (.mk s (InvTm.abstractSumWalk x targetRaw t))

def PosNeu.abstractSumInl {Γ : Ctx sig} {L R A : Object sig.nBases}
    (x : Var Γ L) (targetRaw : RawNeu) : PosNeu Γ A → PosNeu Γ A
  | .neu n =>
      if NegNeu.toRaw n == targetRaw then
        match decEq A (.coprod L R) with
        | isTrue h => h ▸ .inl (.neu (.var x))
        | isFalse _ => .neu (NegNeu.abstractSum x targetRaw n)
      else
        .neu (NegNeu.abstractSum x targetRaw n)
  | .inl p => .inl (PosNeu.abstractSumInl (R := R) x targetRaw p)
  | .inr p => .inr (PosNeu.abstractSumInl (R := R) x targetRaw p)

def PosNeu.abstractSumInr {Γ : Ctx sig} {L R A : Object sig.nBases}
    (x : Var Γ R) (targetRaw : RawNeu) : PosNeu Γ A → PosNeu Γ A
  | .neu n =>
      if NegNeu.toRaw n == targetRaw then
        match decEq A (.coprod L R) with
        | isTrue h => h ▸ .inr (.neu (.var x))
        | isFalse _ => .neu (NegNeu.abstractSum x targetRaw n)
      else
        .neu (NegNeu.abstractSum x targetRaw n)
  | .inl p => .inl (PosNeu.abstractSumInr (L := L) x targetRaw p)
  | .inr p => .inr (PosNeu.abstractSumInr (L := L) x targetRaw p)

def InvTm.abstractSumInl {Γ : Ctx sig} {L R A : Object sig.nBases}
    (x : Var Γ L) (targetRaw : RawNeu) : InvTm Γ A → InvTm Γ A
  | .unit => .unit
  | .pair t u =>
      .pair (InvTm.abstractSumInl (R := R) x targetRaw t) (InvTm.abstractSumInl (R := R) x targetRaw u)
  | .lam t => .lam (InvTm.abstractSumInl (R := R) (.there x) (RawNeu.shift targetRaw) t)
  | .case n t u =>
      .case (NegNeu.abstractSum x targetRaw n)
        (InvTm.abstractSumInl (R := R) (.there x) (RawNeu.shift targetRaw) t)
        (InvTm.abstractSumInl (R := R) (.there x) (RawNeu.shift targetRaw) u)
  | .abort n => .abort (NegNeu.abstractSum x targetRaw n)
  | .foc f => .foc (FocTm.abstractSumInl (R := R) x targetRaw f)

def InvTm.abstractSumInr {Γ : Ctx sig} {L R A : Object sig.nBases}
    (x : Var Γ R) (targetRaw : RawNeu) : InvTm Γ A → InvTm Γ A
  | .unit => .unit
  | .pair t u =>
      .pair (InvTm.abstractSumInr (L := L) x targetRaw t) (InvTm.abstractSumInr (L := L) x targetRaw u)
  | .lam t => .lam (InvTm.abstractSumInr (L := L) (.there x) (RawNeu.shift targetRaw) t)
  | .case n t u =>
      .case (NegNeu.abstractSum x targetRaw n)
        (InvTm.abstractSumInr (L := L) (.there x) (RawNeu.shift targetRaw) t)
        (InvTm.abstractSumInr (L := L) (.there x) (RawNeu.shift targetRaw) u)
  | .abort n => .abort (NegNeu.abstractSum x targetRaw n)
  | .foc f => .foc (FocTm.abstractSumInr (L := L) x targetRaw f)

def FocTm.abstractSumInl {Γ : Ctx sig} {L R A : Object sig.nBases}
    (x : Var Γ L) (targetRaw : RawNeu) : FocTm Γ A → FocTm Γ A
  | .pos (.done p) => .pos (.done (PosNeu.abstractSumInl (R := R) x targetRaw p))
  | .neg (.done n) => .neg (.done (NegNeu.abstractSum x targetRaw n))
  | .letPos n t =>
      .letPos (NegNeu.abstractSum x targetRaw n)
        (InvTm.abstractSumInl (R := R) (.there x) (RawNeu.shift targetRaw) t)
  | .sat (.mk s t) => .sat (.mk s (InvTm.abstractSumInl (R := R) x targetRaw t))

def FocTm.abstractSumInr {Γ : Ctx sig} {L R A : Object sig.nBases}
    (x : Var Γ R) (targetRaw : RawNeu) : FocTm Γ A → FocTm Γ A
  | .pos (.done p) => .pos (.done (PosNeu.abstractSumInr (L := L) x targetRaw p))
  | .neg (.done n) => .neg (.done (NegNeu.abstractSum x targetRaw n))
  | .letPos n t =>
      .letPos (NegNeu.abstractSum x targetRaw n)
        (InvTm.abstractSumInr (L := L) (.there x) (RawNeu.shift targetRaw) t)
  | .sat (.mk s t) => .sat (.mk s (InvTm.abstractSumInr (L := L) x targetRaw t))
end

/--
Map a remaining schedule entry under a new binder, abstracting the observed
neutral. Consistency witnesses are reconstructed at the old context, weakened,
abstracted, and stored as exact entries when possible.
-/
def mapRestAbstractAtom (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (P : Object sig.nBases)
    (hctx : Ctx.ofHyps (hyps.push P) = Ctx.ofHyps hyps ▻ P)
    (targetRaw : RawNeu) :
    PairEntry sig hyps → PairEntry sig (hyps.push P)
  | .exact Q n =>
      let nA := NegNeu.abstractAtom (P := P) .here targetRaw (NegNeu.weaken (B := P) n)
      .exact Q (NegNeu.castCtx hctx.symm nA)
  | .consistency Q w =>
      match reconstructWitness fuel σ hyps w with
      | some ⟨Q', n⟩ =>
        if h : Q' = Q then
          let nA := NegNeu.abstractAtom (P := P) .here targetRaw (NegNeu.weaken (B := P) (h ▸ n))
          .exact Q (NegNeu.castCtx hctx.symm nA)
        else
          .consistency (hyps := hyps.push P) Q w
      | none => .consistency (hyps := hyps.push P) Q w

def mapRestAbstractSumInl (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (L _R : Object sig.nBases)
    (hL : Ctx.ofHyps (hyps.push L) = Ctx.ofHyps hyps ▻ L)
    (targetRaw : RawNeu) :
    PairEntry sig hyps → PairEntry sig (hyps.push L)
  | .exact Q n =>
      let nA := NegNeu.abstractSum (B := L) .here targetRaw (NegNeu.weaken (B := L) n)
      .exact Q (NegNeu.castCtx hL.symm nA)
  | .consistency Q w =>
      match reconstructWitness fuel σ hyps w with
      | some ⟨Q', n⟩ =>
        if h : Q' = Q then
          let nA := NegNeu.abstractSum (B := L) .here targetRaw (NegNeu.weaken (B := L) (h ▸ n))
          .exact Q (NegNeu.castCtx hL.symm nA)
        else
          .consistency (hyps := hyps.push L) Q w
      | none => .consistency (hyps := hyps.push L) Q w

def mapRestAbstractSumInr (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases)) (_L R : Object sig.nBases)
    (hR : Ctx.ofHyps (hyps.push R) = Ctx.ofHyps hyps ▻ R)
    (targetRaw : RawNeu) :
    PairEntry sig hyps → PairEntry sig (hyps.push R)
  | .exact Q n =>
      let nA := NegNeu.abstractSum (B := R) .here targetRaw (NegNeu.weaken (B := R) n)
      .exact Q (NegNeu.castCtx hR.symm nA)
  | .consistency Q w =>
      match reconstructWitness fuel σ hyps w with
      | some ⟨Q', n⟩ =>
        if h : Q' = Q then
          let nA := NegNeu.abstractSum (B := R) .here targetRaw (NegNeu.weaken (B := R) (h ▸ n))
          .exact Q (NegNeu.castCtx hR.symm nA)
        else
          .consistency (hyps := hyps.push R) Q w
      | none => .consistency (hyps := hyps.push R) Q w

mutual
/--
Apply one positive observation `nP`, then continue with `rest` under the
extended context. Uses strong positive cut (neutral abstraction).
-/
def applyObsNeu (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases))
    (P : Object sig.nBases)
    (nP : NegNeu (Ctx.ofHyps hyps) P)
    (rest : List (PairEntry sig hyps))
    {A : Object sig.nBases}
    (cont : InvTm (Ctx.ofHyps hyps) A) : SaturateResult (Ctx.ofHyps hyps) A :=
  match fuel with
  | 0 => .exhausted
  | fuel + 1 =>
    if hNever : P = (.never : Object sig.nBases) then
      .ok (.abort (A := A) (NegNeu.cast hNever nP))
    else
      let P₀ : Object sig.nBases := P
      let n₀ : NegNeu (Ctx.ofHyps hyps) P₀ := nP
      match hP : P₀ with
      | .coprod L R =>
          let nSum : NegNeu (Ctx.ofHyps hyps) (.coprod L R) := hP ▸ n₀
          let hypsL := hyps.push L
          let hypsR := hyps.push R
          have hL : Ctx.ofHyps hypsL = Ctx.ofHyps hyps ▻ L :=
            Ctx.ofHyps_push hyps L
          have hR : Ctx.ofHyps hypsR = Ctx.ofHyps hyps ▻ R :=
            Ctx.ofHyps_push hyps R
          let targetL := NegNeu.toRaw (NegNeu.weaken (B := L) nSum)
          let targetR := NegNeu.toRaw (NegNeu.weaken (B := R) nSum)
          let restL := rest.map (mapRestAbstractSumInl fuel σ hyps L R hL targetL)
          let restR := rest.map (mapRestAbstractSumInr fuel σ hyps L R hR targetR)
          let contL : InvTm (Ctx.ofHyps hypsL) A :=
            InvTm.castCtx hL.symm
              (InvTm.abstractSumInl (L := L) (R := R) .here targetL
                (InvTm.weaken (B := L) cont))
          let contR : InvTm (Ctx.ofHyps hypsR) A :=
            InvTm.castCtx hR.symm
              (InvTm.abstractSumInr (L := L) (R := R) .here targetR
                (InvTm.weaken (B := R) cont))
          match applyPairObsGo fuel σ hypsL restL contL,
                applyPairObsGo fuel σ hypsR restR contR with
          | .ok bodyL', .ok bodyR' =>
              .ok (.case nSum
                (InvTm.castCtx hL bodyL')
                (InvTm.castCtx hR bodyR'))
          | .exhausted, _ | _, .exhausted => .exhausted
          | .invariantFailure, _ | _, .invariantFailure => .invariantFailure
      | _ =>
          let hyps' := hyps.push P₀
          have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ P₀ :=
            Ctx.ofHyps_push hyps P₀
          let targetRaw := NegNeu.toRaw (NegNeu.weaken (B := P₀) n₀)
          let rest' := rest.map (mapRestAbstractAtom fuel σ hyps P₀ hctx targetRaw)
          let cont' : InvTm (Ctx.ofHyps hyps') A :=
            InvTm.castCtx hctx.symm
              (InvTm.abstractAtom (P := P₀) .here targetRaw
                (InvTm.weaken (B := P₀) cont))
          match applyPairObsGo fuel σ hyps' rest' cont' with
          | .ok body' =>
              .ok (.foc (.letPos n₀ (InvTm.castCtx hctx body')))
          | .exhausted => .exhausted
          | .invariantFailure => .invariantFailure

/-- Apply pair-directed observations (exact ∪ consistency). -/
def applyPairObsGo (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases))
    (entries : List (PairEntry sig hyps))
    {A : Object sig.nBases}
    (cont : InvTm (Ctx.ofHyps hyps) A) : SaturateResult (Ctx.ofHyps hyps) A :=
  match fuel with
  | 0 => .exhausted
  | fuel + 1 =>
    match entries with
    | [] => .ok cont
    | e :: rest =>
      match e with
      | .consistency P w =>
          match reconstructWitness fuel σ hyps w with
          | none => .invariantFailure
          | some ⟨P', n⟩ =>
            if hP : P' = P then
              applyObsNeu fuel σ hyps P (hP ▸ n) rest cont
            else
              .invariantFailure
      | .exact P n =>
          applyObsNeu fuel σ hyps P n rest cont
end

/-- Top-level pair-obs application (handles inconsistency). -/
def applyPairObs (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases))
    (entries : Array (PairEntry sig hyps))
    {A : Object sig.nBases}
    (cont : InvTm (Ctx.ofHyps hyps) A) :
    SaturateResult (Ctx.ofHyps hyps) A :=
  if σ.inconsistent then
    match neuOfType fuel σ hyps (.never : Object sig.nBases) with
    | some n => .ok (.abort n)
    | none => .invariantFailure
  else
    applyPairObsGo fuel σ hyps entries.toList cont

/--
Apply schedule entries oldest-first. Positive types are inverted:
`never` collapses to `abort`; coproducts case-split; atoms bind via `letPos`.
-/
def applyScheduleEntries (fuel : Nat) (σ : ReachState sig.nBases)
    (hyps : Array (Object sig.nBases))
    (entries : List (Object sig.nBases × Witness))
    {A : Object sig.nBases}
    (cont : InvTm (Ctx.ofHyps hyps) A) : SaturateResult (Ctx.ofHyps hyps) A :=
  let pairEntries : List (PairEntry sig hyps) :=
    entries.map fun e => .consistency e.1 e.2
  applyPairObsGo fuel σ hyps pairEntries cont

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
        -- Intro-only positives (`inl`/`inr`) are constructible terms, not
        -- pending neutral observations that an earlier phase must have cut.
        if objectPolarity A == .pos && c.simplyDeducible && !c.retrievable then
          match c.witness with
          | some w =>
            if w.isNeutral then return false else pure ()
          | none => return false
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
