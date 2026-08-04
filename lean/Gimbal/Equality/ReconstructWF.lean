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
import Gimbal.Equality.Saturation

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
            let inlVal : Option (ReconstructVal sig) :=
              match reconstructGoWF cert ambientRank (.invOf hyps L) with
              | some (.inv hyps' A' (.foc (.pos (.done p)))) =>
                if hH : hyps' = hyps then
                  if hA : A' = L then
                    some (.inv hyps (.coprod L R)
                      (.foc (.pos (.done (.inl (hA ▸ (hH ▸ p)))))))
                  else none
                else none
              | _ => none
            let inrVal : Option (ReconstructVal sig) :=
              match reconstructGoWF cert ambientRank (.invOf hyps R) with
              | some (.inv hyps' A' (.foc (.pos (.done p)))) =>
                if hH : hyps' = hyps then
                  if hA : A' = R then
                    some (.inv hyps (.coprod L R)
                      (.foc (.pos (.done (.inr (hA ▸ (hH ▸ p)))))))
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
