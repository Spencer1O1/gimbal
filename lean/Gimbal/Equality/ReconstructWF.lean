/-
  Well-founded witness reconstruction on a proof-only rank certificate.

  Domain: certified / completed reachability states only — not arbitrary
  `ReachState`, witnesses, or commands. Ambient rank is the derivation rank of
  the obligation being discharged.

  Lex measure: `(ambientRank, ReconPhase.toNat, objSize)`.
  `invOf → neuOf` requires a **strictly smaller** neutral derivation rank
  (never phase alone). Missing that decrease is a stop condition.
-/

import Gimbal.Equality.ReachCertified
import Gimbal.Equality.ReconstructCore

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-! ## Command phase / size for the lex measure -/

def ReconstructCmd.phase : ReconstructCmd sig → ReconPhase
  | .neuOf _ _ => .neuOf
  | .witness _ _ => .witness
  | .invOf _ _ => .invOf

def ReconstructCmd.objSize : ReconstructCmd sig → Nat
  | .neuOf _ A | .invOf _ A => reconObjectSize A
  | .witness _ _ => 0

/-! ## Rank helpers on certificates -/

/-- Rank of the slot selected by `neutralWitness`, if any. -/
def ReachRankCert.rankOfNeutralSlot {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) : Option Nat :=
  match (σ.getCell i).neutralWitness with
  | none => none
  | some _ =>
      if (σ.getCell i).newNeutral then cert.rank i true
      else cert.rank i false

theorem ReachRankCert.rankOfNeutralSlot_eq_preferred {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) :
    cert.rankOfNeutralSlot i = cert.rankOfPreferred i := by
  simp only [ReachRankCert.rankOfNeutralSlot, ReachRankCert.rankOfPreferred]
  cases (σ.getCell i).neutralWitness <;> rfl

/-- Try one provenance slot for a neutral under a rank predicate. -/
def ReachRankCert.tryNeutralSlot {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (ok : Nat → Bool) :
    Option (Witness × Nat) :=
  match (σ.getCell i).slotWitness b with
  | some w =>
      if Witness.isNeutral w then
        match cert.rank i b with
        | some r => if ok r then some (w, r) else none
        | none => none
      else none
  | none => none

/--
Neutral witness at `i` whose derivation rank is **strictly below** `ambient`.
Prefers uses-new when both qualify. For `invOf → neuOf` / parent `neuOf`.
-/
def ReachRankCert.selectNeutralLt {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i ambient : Nat) : Option (Witness × Nat) :=
  match cert.tryNeutralSlot i true (fun r => decide (r < ambient)) with
  | some x => some x
  | none => cert.tryNeutralSlot i false (fun r => decide (r < ambient))

/--
Neutral witness at `i` with rank `≤ ambient` (equal-rank OK for
`neuOf → witness` phase drop).
-/
def ReachRankCert.selectNeutralLe {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i ambient : Nat) : Option (Witness × Nat) :=
  match cert.tryNeutralSlot i true (fun r => decide (r ≤ ambient)) with
  | some x => some x
  | none => cert.tryNeutralSlot i false (fun r => decide (r ≤ ambient))

theorem ReachRankCert.tryNeutralSlot_ok {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (ok : Nat → Bool)
    {w : Witness} {r : Nat}
    (h : cert.tryNeutralSlot i b ok = some (w, r)) : ok r = true := by
  dsimp [ReachRankCert.tryNeutralSlot] at h
  cases hw : (σ.getCell i).slotWitness b with
  | none => simp [hw] at h
  | some w' =>
      simp only [hw] at h
      split at h
      · split at h
        · split at h
          · cases h; assumption
          · cases h
        · cases h
      · cases h

theorem ReachRankCert.selectNeutralLt_rank_lt {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i ambient : Nat) {w : Witness} {r : Nat}
    (h : cert.selectNeutralLt i ambient = some (w, r)) : r < ambient := by
  dsimp [ReachRankCert.selectNeutralLt] at h
  cases h1 : cert.tryNeutralSlot i true (fun r => decide (r < ambient)) with
  | some x =>
      simp only [h1] at h
      have hx : x = (w, r) := Option.some.inj h
      subst hx
      have := cert.tryNeutralSlot_ok i true (fun r => decide (r < ambient)) h1
      exact of_decide_eq_true this
  | none =>
      simp only [h1] at h
      have := cert.tryNeutralSlot_ok i false (fun r => decide (r < ambient)) h
      exact of_decide_eq_true this

theorem ReachRankCert.selectNeutralLe_rank_le {n : Nat} {σ : ReachState n}
    (cert : ReachRankCert σ) (i ambient : Nat) {w : Witness} {r : Nat}
    (h : cert.selectNeutralLe i ambient = some (w, r)) : r ≤ ambient := by
  dsimp [ReachRankCert.selectNeutralLe] at h
  cases h1 : cert.tryNeutralSlot i true (fun r => decide (r ≤ ambient)) with
  | some x =>
      simp only [h1] at h
      have hx : x = (w, r) := Option.some.inj h
      subst hx
      have := cert.tryNeutralSlot_ok i true (fun r => decide (r ≤ ambient)) h1
      exact of_decide_eq_true this
  | none =>
      simp only [h1] at h
      have := cert.tryNeutralSlot_ok i false (fun r => decide (r ≤ ambient)) h
      exact of_decide_eq_true this

/-! ## Stop condition: `invOf → neuOf` without rank decrease -/

/--
Witness/rule diagnostic when `invOf` would call `neuOf` without a strictly
smaller derivation rank. Totality on certified completed states must prove this
is unreachable.
-/
structure InvOfNeuOfRankViolation where
  ambientRank : Nat
  cellIdx : Nat
  neutralRank : Nat
  w : Witness
  deriving Repr

def InvOfNeuOfRankViolation.ok (v : InvOfNeuOfRankViolation) : Prop :=
  v.neutralRank < v.ambientRank

theorem invOf_neuOf_requires_rank_lt (v : InvOfNeuOfRankViolation) :
    v.ok ↔ v.neutralRank < v.ambientRank :=
  Iff.rfl

/-! ## Explicit measure decrease lemmas -/

theorem measure_neuOf_to_witness (r : Nat) {n : Nat} (A : Object n) :
    ReconMeasure.lt
      (reconMeasure r .witness (.unit : Object n))
      (reconMeasure r .neuOf A) := by
  dsimp [ReconMeasure.lt, reconMeasure, ReconPhase.toNat, reconObjectSize]
  refine Or.inr ⟨rfl, Or.inl (by omega)⟩

theorem measure_witness_to_parent_neuOf
    (childRank parentRank : Nat) (h : parentRank < childRank)
    {n : Nat} (A : Object n) :
    ReconMeasure.lt
      (reconMeasure parentRank .neuOf A)
      (reconMeasure childRank .witness (.unit : Object n)) := by
  dsimp [ReconMeasure.lt, reconMeasure, ReconPhase.toNat]
  exact Or.inl h

theorem measure_witness_to_invOf (r : Nat) {n : Nat} (A : Object n) :
    ReconMeasure.lt
      (reconMeasure r .invOf A)
      (reconMeasure r .witness (.unit : Object n)) := by
  dsimp [ReconMeasure.lt, reconMeasure, ReconPhase.toNat, reconObjectSize]
  refine Or.inr ⟨rfl, Or.inl (by omega)⟩

theorem measure_invOf_to_neuOf_rank
    (rAmb rNeu : Nat) (h : rNeu < rAmb) {n : Nat} (A : Object n) :
    ReconMeasure.lt
      (reconMeasure rNeu .witness (.unit : Object n))
      (reconMeasure rAmb .invOf A) := by
  dsimp [ReconMeasure.lt, reconMeasure, ReconPhase.toNat]
  exact Or.inl h

theorem measure_invOf_size_lt (r : Nat) {n : Nat} {A B : Object n}
    (h : reconObjectSize A < reconObjectSize B) :
    ReconMeasure.lt (reconMeasure r .invOf A) (reconMeasure r .invOf B) := by
  dsimp [ReconMeasure.lt, reconMeasure, ReconPhase.toNat]
  exact Or.inr ⟨rfl, Or.inr ⟨rfl, h⟩⟩

/-! ## Well-founded reconstruction worker

Single recursive function on `(ambientRank, phase, objSize)`.
-/

def reconstructGoWF {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) :
    Nat → ReconstructCmd sig → Option (ReconstructVal sig)
  | ambientRank, .neuOf hyps A =>
      match findHypVar hyps A with
      | some x => some (.neu hyps A (.var x))
      | none =>
        match σ.findTypeIdx A with
        | none => none
        | some i =>
          match hsel : cert.selectNeutralLe i ambientRank with
          | none => none
          | some (w, rNeu) =>
            match reconstructGoWF cert rNeu (.witness hyps w) with
            | some (.wit hyps' ⟨B, n⟩) =>
              if hH : hyps' = hyps then
                if hA : B = A then
                  some (.neu hyps A (hA ▸ NegNeu.castHyps hH n))
                else none
              else none
            | _ => none
  | ambientRank, .witness hyps w =>
      match w with
      | .ctxVar hypIdx =>
        match Ctx.varOldest hyps hypIdx with
        | some ⟨A, x⟩ => some (.wit hyps ⟨A, .var x⟩)
        | none => none
      | .fstHyp hypIdx =>
        match hyps[hypIdx]? with
        | some (.prod L _R) =>
          match Ctx.varOldest hyps hypIdx with
          | some ⟨P, x⟩ =>
            if hP : P = .prod L _R then
              some (.wit hyps ⟨L, .fst (NegNeu.cast hP (.var x))⟩)
            else none
          | none => none
        | _ => none
      | .sndHyp hypIdx =>
        match hyps[hypIdx]? with
        | some (.prod _L R) =>
          match Ctx.varOldest hyps hypIdx with
          | some ⟨P, x⟩ =>
            if hP : P = .prod _L R then
              some (.wit hyps ⟨R, .snd (NegNeu.cast hP (.var x))⟩)
            else none
          | none => none
        | _ => none
      | .fstType pIdx =>
        match σ.typeAt pIdx with
        | some (.prod L R) =>
          match hsel : cert.selectNeutralLt pIdx ambientRank with
          | none => none
          | some (_w, rP) =>
            match reconstructGoWF cert rP (.neuOf hyps (.prod L R)) with
            | some (.neu hyps' _A n) =>
              if hH : hyps' = hyps then
                if hA : _A = .prod L R then
                  some (.wit hyps ⟨L,
                    .fst (NegNeu.cast hA (NegNeu.castHyps hH n))⟩)
                else none
              else none
            | _ => none
        | _ => none
      | .sndType pIdx =>
        match σ.typeAt pIdx with
        | some (.prod L R) =>
          match hsel : cert.selectNeutralLt pIdx ambientRank with
          | none => none
          | some (_w, rP) =>
            match reconstructGoWF cert rP (.neuOf hyps (.prod L R)) with
            | some (.neu hyps' _A n) =>
              if hH : hyps' = hyps then
                if hA : _A = .prod L R then
                  some (.wit hyps ⟨R,
                    .snd (NegNeu.cast hA (NegNeu.castHyps hH n))⟩)
                else none
              else none
            | _ => none
        | _ => none
      | .app fnHypIdx argIdx =>
        match hyps[fnHypIdx]?, σ.typeAt argIdx with
        | some (.exp Arg Ret), some Arg' =>
          if Arg' = Arg then
            match Ctx.varOldest hyps fnHypIdx,
                  reconstructGoWF cert ambientRank (.invOf hyps Arg) with
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
          else none
        | _, _ => none
      | .appTy fnTypeIdx argIdx =>
        match σ.typeAt fnTypeIdx, σ.typeAt argIdx with
        | some (.exp Arg Ret), some Arg' =>
          if Arg' = Arg then
            match hsel : cert.selectNeutralLt fnTypeIdx ambientRank with
            | none => none
            | some (_w, rFn) =>
              match reconstructGoWF cert rFn (.neuOf hyps (.exp Arg Ret)),
                    reconstructGoWF cert ambientRank (.invOf hyps Arg) with
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
          else none
        | _, _ => none
      | .unit | .inl _ | .inr _ | .eta => none
  | ambientRank, .invOf hyps A =>
      match findHypVar hyps A with
      | some x =>
        match objectPolarity A with
        | .pos => some (.inv hyps A (.foc (.pos (.done (.neu (.var x))))))
        | .neg => some (.inv hyps A (.foc (.neg (.done (.var x)))))
      | none =>
        let tryNeu : Option (ReconstructVal sig) :=
          match σ.findTypeIdx A with
          | none => none
          | some i =>
            match hsel : cert.selectNeutralLt i ambientRank with
            | none => none
            | some (w, rNeu) =>
              match reconstructGoWF cert rNeu (.witness hyps w) with
              | some (.wit hyps' ⟨B, n⟩) =>
                if hH : hyps' = hyps then
                  if hA : B = A then
                    let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
                    match objectPolarity A with
                    | .pos =>
                      some (.inv hyps A (.foc (.pos (.done (.neu n')))))
                    | .neg =>
                      some (.inv hyps A (.foc (.neg (.done n'))))
                  else none
                else none
              | _ => none
        match tryNeu with
        | some v => some v
        | none =>
          match A with
          | .unit => some (.inv hyps .unit .unit)
          | .prod L R =>
            match reconstructGoWF cert ambientRank (.invOf hyps L),
                  reconstructGoWF cert ambientRank (.invOf hyps R) with
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
            -- Positive payloads: `foc pos done`; negative: shift via `PosNeu.val`.
            let inlVal : Option (ReconstructVal sig) :=
              match reconstructGoWF cert ambientRank (.invOf hyps L) with
              | some (.inv hyps' A' t) =>
                if hH : hyps' = hyps then
                  if hA : A' = L then
                    let t' : InvTm (Ctx.ofHyps hyps) L :=
                      InvTm.castTy hA (InvTm.castHyps hH t)
                    if objectPolarity L == .neg then
                      some (.inv hyps (.coprod L R)
                        (.foc (.pos (.done (.inl (.val t'))))))
                    else
                      match t' with
                      | .foc (.pos (.done p)) =>
                          some (.inv hyps (.coprod L R)
                            (.foc (.pos (.done (.inl p)))))
                      | _ => none
                  else none
                else none
              | _ => none
            let inrVal : Option (ReconstructVal sig) :=
              match reconstructGoWF cert ambientRank (.invOf hyps R) with
              | some (.inv hyps' A' t) =>
                if hH : hyps' = hyps then
                  if hA : A' = R then
                    let t' : InvTm (Ctx.ofHyps hyps) R :=
                      InvTm.castTy hA (InvTm.castHyps hH t)
                    if objectPolarity R == .neg then
                      some (.inv hyps (.coprod L R)
                        (.foc (.pos (.done (.inr (.val t'))))))
                    else
                      match t' with
                      | .foc (.pos (.done p)) =>
                          some (.inv hyps (.coprod L R)
                            (.foc (.pos (.done (.inr p)))))
                      | _ => none
                  else none
                else none
              | _ => none
            if preferRight then
              match inrVal with | some v => some v | none => inlVal
            else
              match inlVal with | some v => some v | none => inrVal
          | .exp Arg Ret =>
            let hyps' := hyps.push Arg
            have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ Arg :=
              Ctx.ofHyps_push hyps Arg
            match reconstructGoWF cert ambientRank (.invOf hyps' Ret) with
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
termination_by ambientRank cmd =>
  (ambientRank, (ReconstructCmd.phase (sig := sig) cmd).toNat,
    ReconstructCmd.objSize (sig := sig) cmd)
decreasing_by
  all_goals
    simp_wf
    first
    | exact Prod.Lex.left _ _
        (ReachRankCert.selectNeutralLt_rank_lt _ _ _ hsel)
    | (
        cases Nat.lt_or_eq_of_le
            (ReachRankCert.selectNeutralLe_rank_le _ _ _ hsel) with
        | inl h => exact Prod.Lex.left _ _ h
        | inr h =>
          subst h
          exact Prod.Lex.right _
            (Prod.Lex.left _ _ (by decide : (1 : Nat) < 2))
      )
    | exact Prod.Lex.left _ _ ‹_›
    | exact Prod.Lex.right _
        (Prod.Lex.left _ _ (by decide : (1 : Nat) < 2))
    | exact Prod.Lex.right _
        (Prod.Lex.left _ _ (by decide : (0 : Nat) < 1))
    | exact Prod.Lex.right _
        (Prod.Lex.right _ (reconObjectSize_prod_left_lt _ _))
    | exact Prod.Lex.right _
        (Prod.Lex.right _ (reconObjectSize_prod_right_lt _ _))
    | exact Prod.Lex.right _
        (Prod.Lex.right _ (reconObjectSize_exp_ret_lt _ _))
    | exact Prod.Lex.right _ (Prod.Lex.right _ (by
        dsimp [ReconstructCmd.objSize, reconObjectSize]; omega))

/-! ## Phase legality of well-founded reconstruction -/

/-- Casts are invisible to phase legality. -/
theorem wellNeg_castCtx {Γ Δ : Ctx sig} {A : Object sig.nBases} (h : Γ = Δ)
    {n : NegNeu Γ A} (hn : WellNeg n) : WellNeg (NegNeu.castCtx h n) := by
  cases h; exact hn

theorem wellNeg_cast {Γ : Ctx sig} {A B : Object sig.nBases} (h : A = B)
    {n : NegNeu Γ A} (hn : WellNeg n) : WellNeg (NegNeu.cast h n) := by
  cases h; exact hn

theorem wellInv_castCtx {Γ Δ : Ctx sig} {A : Object sig.nBases} (h : Γ = Δ)
    {t : InvTm Γ A} (ht : WellInv t) : WellInv (InvTm.castCtx h t) := by
  cases h; exact ht

theorem wellInv_castTy {Γ : Ctx sig} {A B : Object sig.nBases} (h : A = B)
    {t : InvTm Γ A} (ht : WellInv t) : WellInv (InvTm.castTy h t) := by
  cases h; exact ht

theorem wellNeg_castHyps {hyps hyps' : Array (Object sig.nBases)}
    {A : Object sig.nBases} (h : hyps = hyps')
    {n : NegNeu (Ctx.ofHyps hyps) A} (hn : WellNeg n) :
    WellNeg (NegNeu.castHyps h n) :=
  wellNeg_castCtx _ hn

theorem wellInv_castHyps {hyps hyps' : Array (Object sig.nBases)}
    {A : Object sig.nBases} (h : hyps = hyps')
    {t : InvTm (Ctx.ofHyps hyps) A} (ht : WellInv t) :
    WellInv (InvTm.castHyps h t) :=
  wellInv_castCtx _ ht

/-- A legal positive focus exposes a legal value at a positive type. -/
theorem wellPos_of_wellInv {Γ : Ctx sig} {A : Object sig.nBases} {p : PosNeu Γ A}
    (h : WellInv (.foc (.pos (.done p)))) : WellPos p := by
  cases h with | foc hf => cases hf with | pos _ hp => exact hp

/-- Phase legality of a reconstruction result. -/
def ReconstructVal.Well : ReconstructVal sig → Prop
  | .neu _ _ n => WellNeg n
  | .wit _ ⟨_, n⟩ => WellNeg n
  | .inv _ _ t => WellInv t

private def goLt (p q : Nat × ReconstructCmd sig) : Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
    (p.1, (ReconstructCmd.phase (sig := sig) p.2).toNat,
      ReconstructCmd.objSize (sig := sig) p.2)
    (q.1, (ReconstructCmd.phase (sig := sig) q.2).toNat,
      ReconstructCmd.objSize (sig := sig) q.2)

private theorem goLt_wf : WellFounded (goLt (sig := sig)) :=
  InvImage.wf
    (fun p : Nat × ReconstructCmd sig =>
      (p.1, (ReconstructCmd.phase (sig := sig) p.2).toNat,
        ReconstructCmd.objSize (sig := sig) p.2))
    (Prod.lex (inferInstance : WellFoundedRelation Nat)
      (Prod.lex (inferInstance : WellFoundedRelation Nat)
        (inferInstance : WellFoundedRelation Nat))).wf

private theorem well_invOf_hypFocus {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} (x : Var (Ctx.ofHyps hyps) A) {v : ReconstructVal sig}
    (h : (match objectPolarity A with
      | .pos => some (.inv hyps A (.foc (.pos (.done (.neu (.var x))))))
      | .neg => some (.inv hyps A (.foc (.neg (.done (.var x)))))) = some v) :
    ReconstructVal.Well v := by
  cases hpol : objectPolarity A <;> simp [hpol] at h <;> cases h
  · exact .foc (.pos hpol (.neu hpol .var))
  · exact .foc (.neg hpol .var)

private theorem well_invOf_neuFocus {hyps : Array (Object sig.nBases)}
    {A : Object sig.nBases} {n : NegNeu (Ctx.ofHyps hyps) A} (hn : WellNeg n)
    {v : ReconstructVal sig}
    (h : (match objectPolarity A with
      | .pos => some (.inv hyps A (.foc (.pos (.done (.neu n)))))
      | .neg => some (.inv hyps A (.foc (.neg (.done n))))) = some v) :
    ReconstructVal.Well v := by
  cases hpol : objectPolarity A <;> simp [hpol] at h <;> cases h
  · exact .foc (.pos hpol (.neu hpol hn))
  · exact .foc (.neg hpol hn)

private theorem well_coprod_inl {hyps : Array (Object sig.nBases)}
    {L R : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps) L}
    (ht : WellInv t) {v : ReconstructVal sig}
    (h : (if objectPolarity L == .neg then
            some (.inv hyps (.coprod L R)
              (.foc (.pos (.done (.inl (.val t))))))
          else
            match t with
            | .foc (.pos (.done p)) =>
                some (.inv hyps (.coprod L R) (.foc (.pos (.done (.inl p)))))
            | _ => none) = some v) :
    ReconstructVal.Well v := by
  split at h
  · cases h
    refine .foc (.pos rfl (.inl (.val ?_ ht)))
    simpa [beq_iff_eq] using ‹(objectPolarity L == Polarity.neg) = true›
  · cases t with
    | foc f =>
      cases f with
      | pos intro =>
        cases intro with
        | done p =>
          cases h
          exact .foc (.pos rfl (.inl (wellPos_of_wellInv ht)))
      | neg _ => cases h
      | letPos _ _ => cases h
      | sat _ => cases h
    | unit => cases h
    | pair _ _ => cases h
    | lam _ => cases h
    | case _ _ _ => cases h
    | abort _ => cases h

private theorem well_coprod_inr {hyps : Array (Object sig.nBases)}
    {L R : Object sig.nBases} {t : InvTm (Ctx.ofHyps hyps) R}
    (ht : WellInv t) {v : ReconstructVal sig}
    (h : (if objectPolarity R == .neg then
            some (.inv hyps (.coprod L R)
              (.foc (.pos (.done (.inr (.val t))))))
          else
            match t with
            | .foc (.pos (.done p)) =>
                some (.inv hyps (.coprod L R) (.foc (.pos (.done (.inr p)))))
            | _ => none) = some v) :
    ReconstructVal.Well v := by
  split at h
  · cases h
    refine .foc (.pos rfl (.inr (.val ?_ ht)))
    simpa [beq_iff_eq] using ‹(objectPolarity R == Polarity.neg) = true›
  · cases t with
    | foc f =>
      cases f with
      | pos intro =>
        cases intro with
        | done p =>
          cases h
          exact .foc (.pos rfl (.inr (wellPos_of_wellInv ht)))
      | neg _ => cases h
      | letPos _ _ => cases h
      | sat _ => cases h
    | unit => cases h
    | pair _ _ => cases h
    | lam _ => cases h
    | case _ _ _ => cases h
    | abort _ => cases h

private def reconstructTryNeuWF {σ : ReachState sig.nBases} (cert : ReachRankCert σ)
    (a : Nat) (hyps : Array (Object sig.nBases)) (A : Object sig.nBases) :
    Option (ReconstructVal sig) :=
  match σ.findTypeIdx A with
  | none => none
  | some i =>
    match hsel : cert.selectNeutralLt i a with
    | none => none
    | some (w, rNeu) =>
      match reconstructGoWF cert rNeu (.witness hyps w) with
      | some (.wit hyps' ⟨B, n⟩) =>
        if hH : hyps' = hyps then
          if hA : B = A then
            let n' := NegNeu.cast hA (NegNeu.castHyps hH n)
            match objectPolarity A with
            | .pos => some (.inv hyps A (.foc (.pos (.done (.neu n')))))
            | .neg => some (.inv hyps A (.foc (.neg (.done n'))))
          else none
        else none
      | _ => none

private def reconstructInlValWF {σ : ReachState sig.nBases} (cert : ReachRankCert σ)
    (a : Nat) (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases) :
    Option (ReconstructVal sig) :=
  match reconstructGoWF cert a (.invOf hyps L) with
  | some (.inv hyps' A' t) =>
    if hH : hyps' = hyps then
      if hA : A' = L then
        let t' : InvTm (Ctx.ofHyps hyps) L := InvTm.castTy hA (InvTm.castHyps hH t)
        if objectPolarity L == .neg then
          some (.inv hyps (L.coprod R) (.foc (.pos (.done (.inl (.val t'))))))
        else match t' with
          | .foc (.pos (.done p)) =>
            some (.inv hyps (L.coprod R) (.foc (.pos (.done (.inl p)))))
          | _ => none
      else none
    else none
  | _ => none

private def reconstructInrValWF {σ : ReachState sig.nBases} (cert : ReachRankCert σ)
    (a : Nat) (hyps : Array (Object sig.nBases)) (L R : Object sig.nBases) :
    Option (ReconstructVal sig) :=
  match reconstructGoWF cert a (.invOf hyps R) with
  | some (.inv hyps' A' t) =>
    if hH : hyps' = hyps then
      if hA : A' = R then
        let t' : InvTm (Ctx.ofHyps hyps) R := InvTm.castTy hA (InvTm.castHyps hH t)
        if objectPolarity R == .neg then
          some (.inv hyps (L.coprod R) (.foc (.pos (.done (.inr (.val t'))))))
        else match t' with
          | .foc (.pos (.done p)) =>
            some (.inv hyps (L.coprod R) (.foc (.pos (.done (.inr p)))))
          | _ => none
      else none
    else none
  | _ => none

/-- Successful well-founded reconstruction yields a phase-legal value. -/
theorem well_reconstructGoWF {σ : ReachState sig.nBases} (cert : ReachRankCert σ) :
    ∀ (ambientRank : Nat) (cmd : ReconstructCmd sig) {v : ReconstructVal sig},
      reconstructGoWF cert ambientRank cmd = some v → ReconstructVal.Well v := by
  intro ambientRank cmd
  refine WellFounded.fix (goLt_wf (sig := sig))
    (C := fun p => ∀ {v},
      reconstructGoWF cert p.1 p.2 = some v → ReconstructVal.Well v) ?_
    ⟨ambientRank, cmd⟩
  intro ⟨ambientRank, cmd⟩ ih v h
  cases cmd with
  | neuOf hyps A =>
    rw [reconstructGoWF.eq_1] at h
    split at h
    · cases h; exact .var
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i _ _ _ i _ w rNeu hsel
          have hlt : goLt ⟨rNeu, .witness hyps w⟩ ⟨ambientRank, .neuOf hyps A⟩ := by
            cases Nat.lt_or_eq_of_le
                (ReachRankCert.selectNeutralLe_rank_le cert i ambientRank hsel) with
            | inl hlt => exact Prod.Lex.left _ _ hlt
            | inr heq =>
              subst heq
              exact Prod.Lex.right _ (Prod.Lex.left _ _ (by decide : (1 : Nat) < 2))
          split at h
          · rename_i hyps' B n hw
            have hwWell := ih ⟨rNeu, .witness hyps w⟩ hlt hw
            split at h
            · split at h
              · cases h; exact wellNeg_cast _ (wellNeg_castHyps _ hwWell)
              · cases h
            · cases h
          · cases h
  | witness hyps w =>
    cases w with
    | ctxVar hypIdx =>
      rw [reconstructGoWF.eq_2] at h; split at h <;> (try cases h); exact .var
    | fstHyp hypIdx =>
      rw [reconstructGoWF.eq_3] at h
      split at h <;> try cases h
      split at h <;> try cases h
      split at h <;> try cases h
      exact .fst (wellNeg_cast _ .var)
    | sndHyp hypIdx =>
      rw [reconstructGoWF.eq_4] at h
      split at h <;> try cases h
      split at h <;> try cases h
      split at h <;> try cases h
      exact .snd (wellNeg_cast _ .var)
    | fstType pIdx =>
      rw [reconstructGoWF.eq_5] at h
      split at h
      · rename_i _ L R _
        split at h
        · cases h
        · rename_i _ w rP hsel
          have hlt : goLt ⟨rP, .neuOf hyps (.prod L R)⟩
              ⟨ambientRank, .witness hyps (.fstType pIdx)⟩ :=
            Prod.Lex.left _ _
              (ReachRankCert.selectNeutralLt_rank_lt cert pIdx ambientRank hsel)
          split at h
          · rename_i hyps' _A n hn
            have hnWell := ih ⟨rP, .neuOf hyps (.prod L R)⟩ hlt hn
            split at h
            · split at h
              · cases h; exact .fst (wellNeg_cast _ (wellNeg_castHyps _ hnWell))
              · cases h
            · cases h
          · cases h
      · cases h
    | sndType pIdx =>
      rw [reconstructGoWF.eq_6] at h
      split at h
      · rename_i _ L R _
        split at h
        · cases h
        · rename_i _ w rP hsel
          have hlt : goLt ⟨rP, .neuOf hyps (.prod L R)⟩
              ⟨ambientRank, .witness hyps (.sndType pIdx)⟩ :=
            Prod.Lex.left _ _
              (ReachRankCert.selectNeutralLt_rank_lt cert pIdx ambientRank hsel)
          split at h
          · rename_i hyps' _A n hn
            have hnWell := ih ⟨rP, .neuOf hyps (.prod L R)⟩ hlt hn
            split at h
            · split at h
              · cases h; exact .snd (wellNeg_cast _ (wellNeg_castHyps _ hnWell))
              · cases h
            · cases h
          · cases h
      · cases h
    | app fnHypIdx argIdx =>
      rw [reconstructGoWF.eq_7] at h
      split at h
      · rename_i _ _ Arg Ret Arg' _ _
        split at h
        · have hlt : goLt ⟨ambientRank, .invOf hyps Arg⟩
              ⟨ambientRank, .witness hyps (.app fnHypIdx argIdx)⟩ :=
            Prod.Lex.right _ (Prod.Lex.left _ _ (by decide : (0 : Nat) < 1))
          split at h
          · rename_i fnTy x hyps' A' argTm hv hi
            have hiWell := ih ⟨ambientRank, .invOf hyps Arg⟩ hlt hi
            split at h
            · split at h
              · split at h
                · cases h
                  exact .app (wellNeg_cast _ .var)
                    (wellInv_castTy _ (wellInv_castHyps _ hiWell))
                · cases h
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    | appTy fnTypeIdx argIdx =>
      rw [reconstructGoWF.eq_8] at h
      split at h
      · rename_i _ _ Arg Ret Arg' _ _
        split at h
        · have hltI : goLt ⟨ambientRank, .invOf hyps Arg⟩
              ⟨ambientRank, .witness hyps (.appTy fnTypeIdx argIdx)⟩ :=
            Prod.Lex.right _ (Prod.Lex.left _ _ (by decide : (0 : Nat) < 1))
          split at h
          · cases h
          · rename_i _ w rFn hsel
            have hltN : goLt ⟨rFn, .neuOf hyps (.exp Arg Ret)⟩
                ⟨ambientRank, .witness hyps (.appTy fnTypeIdx argIdx)⟩ :=
              Prod.Lex.left _ _
                (ReachRankCert.selectNeutralLt_rank_lt cert fnTypeIdx ambientRank hsel)
            split at h
            · rename_i hyps₁ A₁ n hyps₂ A₂ argTm hn hi
              have hnWell := ih ⟨rFn, .neuOf hyps (.exp Arg Ret)⟩ hltN hn
              have hiWell := ih ⟨ambientRank, .invOf hyps Arg⟩ hltI hi
              split at h
              · split at h
                · split at h
                  · split at h
                    · cases h
                      exact .app (wellNeg_cast _ (wellNeg_castHyps _ hnWell))
                        (wellInv_castTy _ (wellInv_castHyps _ hiWell))
                    · cases h
                  · cases h
                · cases h
              · cases h
            · cases h
        · cases h
      · cases h
    | unit => rw [reconstructGoWF.eq_9] at h; cases h
    | inl _ => rw [reconstructGoWF.eq_10] at h; cases h
    | inr _ => rw [reconstructGoWF.eq_11] at h; cases h
    | eta => rw [reconstructGoWF.eq_12] at h; cases h
  | invOf hyps A =>
    have tryW {v : ReconstructVal sig}
        (htry : reconstructTryNeuWF cert ambientRank hyps A = some v) :
        ReconstructVal.Well v := by
      dsimp [reconstructTryNeuWF] at htry
      split at htry
      · cases htry
      · split at htry
        · cases htry
        · rename_i i _ w rNeu hsel
          have hlt : goLt ⟨rNeu, .witness hyps w⟩ ⟨ambientRank, .invOf hyps A⟩ :=
            Prod.Lex.left _ _
              (ReachRankCert.selectNeutralLt_rank_lt cert i ambientRank hsel)
          split at htry
          · rename_i hyps' B n hw
            have hwWell := ih ⟨rNeu, .witness hyps w⟩ hlt hw
            split at htry
            · split at htry
              · exact well_invOf_neuFocus
                  (wellNeg_cast _ (wellNeg_castHyps _ hwWell)) htry
              · cases htry
            · cases htry
          · cases htry
    cases A with
    | unit =>
      rw [reconstructGoWF.eq_13] at h
      split at h
      · rename_i x _; exact well_invOf_hypFocus x h
      · change (match reconstructTryNeuWF cert ambientRank hyps
            (Object.unit : Object sig.nBases) with
          | some u => some u
          | none => some (.inv hyps (Object.unit : Object sig.nBases) .unit)) = some v at h
        cases htry : reconstructTryNeuWF cert ambientRank hyps
            (Object.unit : Object sig.nBases) with
        | some _ => simp [htry] at h; cases h; exact tryW htry
        | none => simp [htry] at h; cases h; exact .unit
    | prod L R =>
      rw [reconstructGoWF.eq_14] at h
      split at h
      · rename_i x _; exact well_invOf_hypFocus x h
      · change (match reconstructTryNeuWF cert ambientRank hyps (L.prod R) with
          | some u => some u
          | none =>
            match reconstructGoWF cert ambientRank (.invOf hyps L),
                  reconstructGoWF cert ambientRank (.invOf hyps R) with
            | some (.inv hyps₁ A₁ t), some (.inv hyps₂ A₂ u) =>
              if h1 : hyps₁ = hyps then
                if h2 : hyps₂ = hyps then
                  if hL : A₁ = L then
                    if hR : A₂ = R then
                      some (.inv hyps (L.prod R)
                        (.pair (InvTm.castTy hL (InvTm.castHyps h1 t))
                          (InvTm.castTy hR (InvTm.castHyps h2 u))))
                    else none
                  else none
                else none
              else none
            | _, _ => none) = some v at h
        cases htry : reconstructTryNeuWF cert ambientRank hyps (L.prod R) with
        | some _ => simp [htry] at h; cases h; exact tryW htry
        | none =>
          simp [htry] at h
          have hltL : goLt ⟨ambientRank, .invOf hyps L⟩
              ⟨ambientRank, .invOf hyps (L.prod R)⟩ :=
            Prod.Lex.right _ (Prod.Lex.right _ (reconObjectSize_prod_left_lt L R))
          have hltR : goLt ⟨ambientRank, .invOf hyps R⟩
              ⟨ambientRank, .invOf hyps (L.prod R)⟩ :=
            Prod.Lex.right _ (Prod.Lex.right _ (reconObjectSize_prod_right_lt L R))
          split at h
          · rename_i hyps₁ A₁ t hyps₂ A₂ u hL0 hR0
            have wL := ih ⟨ambientRank, .invOf hyps L⟩ hltL hL0
            have wR := ih ⟨ambientRank, .invOf hyps R⟩ hltR hR0
            split at h
            · split at h
              · split at h
                · split at h
                  · cases h
                    exact .pair (wellInv_castTy _ (wellInv_castHyps _ wL))
                      (wellInv_castTy _ (wellInv_castHyps _ wR))
                  · cases h
                · cases h
              · cases h
            · cases h
          · cases h
    | coprod L R =>
      rw [reconstructGoWF.eq_15] at h
      split at h
      · rename_i x _; exact well_invOf_hypFocus x h
      · have inlW {v} (hinl : reconstructInlValWF cert ambientRank hyps L R = some v) :
            ReconstructVal.Well v := by
          dsimp [reconstructInlValWF] at hinl
          have hlt : goLt ⟨ambientRank, .invOf hyps L⟩
              ⟨ambientRank, .invOf hyps (L.coprod R)⟩ :=
            Prod.Lex.right _ (Prod.Lex.right _ (reconObjectSize_coprod_left_lt L R))
          split at hinl
          · rename_i hyps' A' t hL
            have wL := ih ⟨ambientRank, .invOf hyps L⟩ hlt hL
            split at hinl
            · split at hinl
              · exact well_coprod_inl (wellInv_castTy _ (wellInv_castHyps _ wL)) hinl
              · cases hinl
            · cases hinl
          · cases hinl
        have inrW {v} (hinr : reconstructInrValWF cert ambientRank hyps L R = some v) :
            ReconstructVal.Well v := by
          dsimp [reconstructInrValWF] at hinr
          have hlt : goLt ⟨ambientRank, .invOf hyps R⟩
              ⟨ambientRank, .invOf hyps (L.coprod R)⟩ :=
            Prod.Lex.right _ (Prod.Lex.right _ (reconObjectSize_coprod_right_lt L R))
          split at hinr
          · rename_i hyps' A' t hR
            have wR := ih ⟨ambientRank, .invOf hyps R⟩ hlt hR
            split at hinr
            · split at hinr
              · exact well_coprod_inr (wellInv_castTy _ (wellInv_castHyps _ wR)) hinr
              · cases hinr
            · cases hinr
          · cases hinr
        change (match reconstructTryNeuWF cert ambientRank hyps (L.coprod R) with
          | some u => some u
          | none =>
            if (match σ.findTypeIdx (L.coprod R) with
                | some i =>
                  match (σ.getCell i).witness with
                  | some (.inr _) => true
                  | _ => false
                | none => false) then
              match reconstructInrValWF cert ambientRank hyps L R with
              | some u => some u
              | none => reconstructInlValWF cert ambientRank hyps L R
            else
              match reconstructInlValWF cert ambientRank hyps L R with
              | some u => some u
              | none => reconstructInrValWF cert ambientRank hyps L R) = some v at h
        cases htry : reconstructTryNeuWF cert ambientRank hyps (L.coprod R) with
        | some _ => simp [htry] at h; cases h; exact tryW htry
        | none =>
          simp [htry] at h
          split_ifs at h
          · cases hinr : reconstructInrValWF cert ambientRank hyps L R with
            | some _ => simp [hinr] at h; cases h; exact inrW hinr
            | none => simp [hinr] at h; exact inlW h
          · cases hinl : reconstructInlValWF cert ambientRank hyps L R with
            | some _ => simp [hinl] at h; cases h; exact inlW hinl
            | none => simp [hinl] at h; exact inrW h
    | exp Arg Ret =>
      rw [reconstructGoWF.eq_16] at h
      split at h
      · rename_i x _; exact well_invOf_hypFocus x h
      · change (match reconstructTryNeuWF cert ambientRank hyps (Arg.exp Ret) with
          | some u => some u
          | none =>
            let hyps' := hyps.push Arg
            have hctx : Ctx.ofHyps hyps' = Ctx.ofHyps hyps ▻ Arg :=
              Ctx.ofHyps_push hyps Arg
            match reconstructGoWF cert ambientRank (.invOf hyps' Ret) with
            | some (.inv hyps'' B t) =>
              if hH : hyps'' = hyps' then
                if hB : B = Ret then
                  some (.inv hyps (Arg.exp Ret)
                    (.lam (InvTm.castCtx hctx
                      (InvTm.castTy hB (InvTm.castHyps hH t)))))
                else none
              else none
            | _ => none) = some v at h
        cases htry : reconstructTryNeuWF cert ambientRank hyps (Arg.exp Ret) with
        | some _ => simp [htry] at h; cases h; exact tryW htry
        | none =>
          simp [htry] at h
          have hlt : goLt ⟨ambientRank, .invOf (hyps.push Arg) Ret⟩
              ⟨ambientRank, .invOf hyps (Arg.exp Ret)⟩ :=
            Prod.Lex.right _ (Prod.Lex.right _ (reconObjectSize_exp_ret_lt Arg Ret))
          split at h
          · rename_i hyps'' B t hi
            have wi := ih ⟨ambientRank, .invOf (hyps.push Arg) Ret⟩ hlt hi
            split at h
            · split at h
              · cases h
                exact .lam (wellInv_castCtx _
                  (wellInv_castTy _ (wellInv_castHyps _ wi)))
              · cases h
            · cases h
          · cases h
    | base q =>
      rw [reconstructGoWF.eq_17 cert ambientRank hyps (.base q)
        (by intro h; cases h) (by intro _ _ h; cases h)
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)] at h
      split at h
      · rename_i x _; exact well_invOf_hypFocus x h
      · change (match reconstructTryNeuWF cert ambientRank hyps (.base q) with
          | some u => some u | none => none) = some v at h
        cases htry : reconstructTryNeuWF cert ambientRank hyps (.base q) with
        | some _ => simp [htry] at h; cases h; exact tryW htry
        | none => simp [htry] at h
    | never =>
      rw [reconstructGoWF.eq_17 cert ambientRank hyps .never
        (by intro h; cases h) (by intro _ _ h; cases h)
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)] at h
      split at h
      · rename_i x _; exact well_invOf_hypFocus x h
      · change (match reconstructTryNeuWF cert ambientRank hyps
          (Object.never : Object sig.nBases) with
          | some u => some u | none => none) = some v at h
        cases htry : reconstructTryNeuWF cert ambientRank hyps
            (Object.never : Object sig.nBases) with
        | some _ => simp [htry] at h; cases h; exact tryW htry
        | none => simp [htry] at h

/-! ## Domain entry points (certified ranks only) -/

/-- Reconstruct a stored neutral witness at its certified slot rank. -/
def reconstructWitnessWF {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew)
    (hyps : Array (Object sig.nBases)) (w : Witness) :
    Option ((A : Object sig.nBases) × NegNeu (Ctx.ofHyps hyps) A) :=
  match cert.rank i b with
  | none => none
  | some r =>
    match reconstructGoWF cert r (.witness hyps w) with
    | some (.wit hyps' ⟨A, n⟩) =>
      if hH : hyps' = hyps then some ⟨A, NegNeu.castHyps hH n⟩ else none
    | _ => none

/--
Reconstruct `w` using the ranked slot of cell `i` that stores it.
Callers that only know the cell (preferred `witness`) use this entry point.
-/
def reconstructWitnessWF_ofCell {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (i : Nat)
    (hyps : Array (Object sig.nBases)) (w : Witness) :
    Option ((A : Object sig.nBases) × NegNeu (Ctx.ofHyps hyps) A) :=
  let c := σ.getCell i
  if c.newWitness == some w then
    reconstructWitnessWF cert i true hyps w
  else if c.oldWitness == some w then
    reconstructWitnessWF cert i false hyps w
  else
    none

/-- Requested neutral (hyp or ranked neutral cell). -/
def neuOfTypeWF {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (hyps : Array (Object sig.nBases))
    (A : Object sig.nBases) : Option (NegNeu (Ctx.ofHyps hyps) A) :=
  let rAmb : Nat :=
    match σ.findTypeIdx A with
    | none => 0
    | some i => (cert.rankOfNeutralSlot i).getD 0
  match reconstructGoWF cert rAmb (.neuOf hyps A) with
  | some (.neu hyps' A' n) =>
    if hH : hyps' = hyps then
      if hA : A' = A then some (NegNeu.cast hA (NegNeu.castHyps hH n))
      else none
    else none
  | _ => none

/-- Reconstructible invertible value at an application ambient rank. -/
def invOfTypeWF {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) (A : Object sig.nBases) :
    Option (InvTm (Ctx.ofHyps hyps) A) :=
  match reconstructGoWF cert ambientRank (.invOf hyps A) with
  | some (.inv hyps' A' t) =>
    if hH : hyps' = hyps then
      if hA : A' = A then some (InvTm.castTy hA (InvTm.castHyps hH t))
      else none
    else none
  | _ => none

/-- Reconstructed neutrals from `neuOfTypeWF` respect phase discipline. -/
theorem wellNeg_neuOfTypeWF {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (hyps : Array (Object sig.nBases))
    (A : Object sig.nBases) {n : NegNeu (Ctx.ofHyps hyps) A}
    (h : neuOfTypeWF cert hyps A = some n) : WellNeg n := by
  dsimp [neuOfTypeWF] at h
  split at h
  · rename_i hyps' A' m hw
    have hwWell := well_reconstructGoWF cert _ (.neuOf hyps A) hw
    split at h
    · split at h
      · cases h
        exact wellNeg_cast _ (wellNeg_castHyps _ hwWell)
      · cases h
    · cases h
  · cases h

/-- Reconstructed neutrals from `reconstructWitnessWF` respect phase discipline. -/
theorem wellNeg_reconstructWitnessWF {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew)
    (hyps : Array (Object sig.nBases)) (w : Witness)
    {A : Object sig.nBases} {n : NegNeu (Ctx.ofHyps hyps) A}
    (h : reconstructWitnessWF cert i b hyps w = some ⟨A, n⟩) : WellNeg n := by
  dsimp [reconstructWitnessWF] at h
  split at h
  · cases h
  · rename_i r _
    split at h
    · rename_i hyps' A' m hw
      have hwWell := well_reconstructGoWF cert r (.witness hyps w) hw
      split at h
      · cases h
        exact wellNeg_castHyps _ hwWell
      · cases h
    · cases h

/-- Cell-entry reconstruction respects phase discipline. -/
theorem wellNeg_reconstructWitnessWF_ofCell {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (i : Nat)
    (hyps : Array (Object sig.nBases)) (w : Witness)
    {A : Object sig.nBases} {n : NegNeu (Ctx.ofHyps hyps) A}
    (h : reconstructWitnessWF_ofCell cert i hyps w = some ⟨A, n⟩) : WellNeg n := by
  dsimp [reconstructWitnessWF_ofCell] at h
  split at h
  · exact wellNeg_reconstructWitnessWF cert i true hyps w h
  · split at h
    · exact wellNeg_reconstructWitnessWF cert i false hyps w h
    · cases h

/-! ## Domain predicates -/

/-- Stored neutral witness at a ranked provenance slot. -/
def StoredNeutralDomain {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (i : Nat) (b : SlotNew) (w : Witness) : Prop :=
  (σ.getCell i).slotWitness b = some w ∧
    Witness.isNeutral w = true ∧
    (cert.rank i b).isSome = true

/-- Cell (or hyp) supporting a requested neutral reconstruction. -/
def RequestedNeutralDomain {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (hyps : Array (Object sig.nBases))
    (A : Object sig.nBases) : Prop :=
  (findHypVar hyps A).isSome = true ∨
    ∃ i, σ.findTypeIdx A = some i ∧ (cert.rankOfNeutralSlot i).isSome = true

/--
Faithful domain for `invOfTypeWF` / `invOf` success (no polarity shortcut).

* hypothesis of type `A` — reconstructs as a variable (any polarity);
* `A = .unit` — reconstructs unconditionally;
* certified witness for `A` at rank `< ambient` — neutral via `selectNeutralLt`,
  or intro via structural `invOf` on lower-ranked `RuleDeps` parents
  (product η → components; coprod intro → payload; function η → return).
-/
def InvertibleArgDomain {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) (A : Object sig.nBases) : Prop :=
  (findHypVar hyps A).isSome = true ∨
    A = (.unit : Object sig.nBases) ∨
      ∃ (i : Nat) (b : SlotNew) (r : Nat),
        σ.findTypeIdx A = some i ∧
          cert.rank i b = some r ∧
            r < ambientRank

theorem InvertibleArgDomain.of_hyp (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) (A : Object sig.nBases)
    (h : (findHypVar hyps A).isSome = true) :
    InvertibleArgDomain cert ambientRank hyps A :=
  Or.inl h

theorem InvertibleArgDomain.of_unit (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) :
    InvertibleArgDomain (σ := σ) cert ambientRank hyps .unit :=
  Or.inr (Or.inl rfl)

theorem InvertibleArgDomain.of_ranked_lt (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) (A : Object sig.nBases)
    {i : Nat} {b : SlotNew} {r : Nat}
    (hfind : σ.findTypeIdx A = some i)
    (hr : cert.rank i b = some r) (hlt : r < ambientRank) :
    InvertibleArgDomain cert ambientRank hyps A :=
  Or.inr (Or.inr ⟨i, b, r, hfind, hr, hlt⟩)

/-- Argument accepted by `hypAppRule`: deps `[aIdx]` ranked below the fresh app rank. -/
theorem InvertibleArgDomain.of_hypApp_arg {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (hyps : Array (Object sig.nBases))
    (Arg : Object sig.nBases) (aIdx : Nat)
    (hfind : σ.findTypeIdx Arg = some aIdx)
    (hpar : RankedParents cert (RuleDeps.hypApp aIdx)) :
    InvertibleArgDomain cert hpar.freshRank hyps Arg := by
  obtain ⟨b, r, hr⟩ := hpar aIdx (by simp [RuleDeps.hypApp])
  exact InvertibleArgDomain.of_ranked_lt cert hpar.freshRank hyps Arg hfind hr
    (RankedParents.lt_freshRank hpar aIdx (by simp [RuleDeps.hypApp]) b r hr)

/-- Argument accepted by `expAppRule`: `aIdx` is a `typeApp` parent below fresh rank. -/
theorem InvertibleArgDomain.of_expApp_arg {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (hyps : Array (Object sig.nBases))
    (Arg : Object sig.nBases) (fnIdx aIdx : Nat)
    (hfind : σ.findTypeIdx Arg = some aIdx)
    (hpar : RankedParents cert (RuleDeps.typeApp fnIdx aIdx)) :
    InvertibleArgDomain cert hpar.freshRank hyps Arg := by
  have hmem : aIdx ∈ RuleDeps.typeApp fnIdx aIdx := by
    simp [RuleDeps.typeApp]
  obtain ⟨b, r, hr⟩ := hpar aIdx hmem
  exact InvertibleArgDomain.of_ranked_lt cert hpar.freshRank hyps Arg hfind hr
    (RankedParents.lt_freshRank hpar aIdx hmem b r hr)

/-- No ranked slot when the cell is not simply deducible (`rank_iff`). -/
theorem ReachRankCert.rank_eq_none_of_not_simplyDeducible {n : Nat}
    {σ : ReachState n} (cert : ReachRankCert σ) (i : Nat)
    (h : (σ.getCell i).simplyDeducible = false) (b : SlotNew) :
    cert.rank i b = none := by
  have hslot : (σ.getCell i).slotWitness b = none := by
    have h' :
        ((σ.getCell i).retrievable = false ∧ (σ.getCell i).oldWitness = none) ∧
          (σ.getCell i).newWitness = none := by
      simpa [ReachCell.simplyDeducible, Bool.or_eq_false_iff,
        Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] using h
    cases b <;> simp [ReachCell.slotWitness, h'.1.2, h'.2]
  have hrs : (cert.rank i b).isSome = false := by
    simpa [hslot] using (cert.rank_iff i b).symm
  cases hr : cert.rank i b with
  | none => rfl
  | some _ => simp [hr] at hrs

/-- Outside the domain: no hyp, not unit, and no simply-deducible cell for `A`. -/
theorem InvertibleArgDomain.not_of_unsupported {σ : ReachState sig.nBases}
    (cert : ReachRankCert σ) (ambientRank : Nat)
    (hyps : Array (Object sig.nBases)) (A : Object sig.nBases)
    (hhyp : (findHypVar hyps A).isSome = false)
    (hunit : A ≠ (.unit : Object sig.nBases))
    (hnone : ∀ i, σ.findTypeIdx A = some i →
      (σ.getCell i).simplyDeducible = false) :
    ¬ InvertibleArgDomain cert ambientRank hyps A := by
  intro h
  rcases h with h | h | ⟨i, b, r, hfind, hr, _⟩
  · simp [hhyp] at h
  · exact hunit h
  · have := cert.rank_eq_none_of_not_simplyDeducible i (hnone i hfind) b
    simp [this] at hr

end Equality
end Gimbal
