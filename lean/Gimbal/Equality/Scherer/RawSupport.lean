import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Fin
import Gimbal.Equality.Scherer.Freshness

namespace Gimbal.Equality.Scherer
variable {sig : Signature}

abbrev StableLevel (Γ : StableCtx sig) := Fin Γ.length
abbrev RawSupport (Γ : StableCtx sig) := Finset (StableLevel Γ)

def StableVar.level {Γ : StableCtx sig} {S : StableTy sig.nBases} :
    StableVar Γ S → StableLevel Γ
  | .here => Fin.last _
  | .there x => Fin.castSucc x.level

def StableCtx.typeAtLevel : (Γ : StableCtx sig) → StableLevel Γ → StableTy sig.nBases
  | .empty, i => Fin.elim0 i
  | .snoc Γ S, i =>
      if h : (i : Nat) = Γ.length then S
      else typeAtLevel Γ ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) h⟩

private theorem level_eqRec {Γ : StableCtx sig} {S S' : StableTy sig.nBases}
    (e : S = S') (x : StableVar Γ S) :
    StableVar.level (e ▸ x) = StableVar.level x := by
  cases e; rfl

def StableVar.atLevel :
    (Γ : StableCtx sig) → (i : StableLevel Γ) → StableVar Γ (Γ.typeAtLevel i)
  | .empty, i => Fin.elim0 i
  | .snoc Γ S, i =>
      if h : (i : Nat) = Γ.length then
        have e : S = (Γ.snoc S).typeAtLevel i := by
          simp only [StableCtx.typeAtLevel, h, ↓reduceDIte]
        (e ▸ (StableVar.here (Γ := Γ) (S := S)) :
          StableVar (Γ.snoc S) ((Γ.snoc S).typeAtLevel i))
      else
        have e : Γ.typeAtLevel ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) h⟩ =
            (Γ.snoc S).typeAtLevel i := by
          simp only [StableCtx.typeAtLevel, h, ↓reduceDIte]
        (e ▸ (StableVar.there
            (atLevel Γ ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) h⟩)) :
          StableVar (Γ.snoc S) ((Γ.snoc S).typeAtLevel i))

@[simp] theorem StableVar.level_atLevel :
    ∀ (Γ : StableCtx sig) (i : StableLevel Γ), (StableVar.atLevel Γ i).level = i
  | .empty, i => Fin.elim0 i
  | .snoc Γ S, i => by
      by_cases h : (i : Nat) = Γ.length
      · dsimp only [StableVar.atLevel]
        rw [dif_pos h, level_eqRec]
        simp only [StableVar.level]
        exact Fin.ext (by simp [h, Fin.val_last])
      · dsimp only [StableVar.atLevel]
        rw [dif_neg h, level_eqRec]
        simp only [StableVar.level, level_atLevel]
        exact Fin.ext rfl

theorem StableCtx.typeAtLevel_level {Γ : StableCtx sig} {S : StableTy sig.nBases} :
    ∀ (x : StableVar Γ S), Γ.typeAtLevel x.level = S
  | .here => by
      simp only [StableVar.level, StableCtx.typeAtLevel, Fin.val_last, ↓reduceDIte]
  | .there (Γ := Γ0) (S' := S0) x => by
      have hne : (x.level : Nat) ≠ Γ0.length := Nat.ne_of_lt x.level.isLt
      simp only [StableVar.level, StableCtx.typeAtLevel, Fin.val_castSucc, hne,
        ↓reduceDIte, typeAtLevel_level x]

theorem StableVar.eq_of_level_eq {Γ : StableCtx sig} {S : StableTy sig.nBases} :
    ∀ (x y : StableVar Γ S), x.level = y.level → x = y
  | .here, .here, _ => rfl
  | .here, .there (Γ := Γ0) y, h => by
      change Fin.last Γ0.length = Fin.castSucc y.level at h
      have : (Fin.last Γ0.length : Nat) = (Fin.castSucc y.level : Nat) :=
        congrArg Fin.val h
      simp [Fin.val_last, Fin.val_castSucc] at this
      exact absurd this (Ne.symm (Nat.ne_of_lt y.level.isLt))
  | .there (Γ := Γ0) x, .here, h => by
      change Fin.castSucc x.level = Fin.last Γ0.length at h
      have : (Fin.castSucc x.level : Nat) = (Fin.last Γ0.length : Nat) :=
        congrArg Fin.val h
      simp [Fin.val_last, Fin.val_castSucc] at this
      exact absurd this (Nat.ne_of_lt x.level.isLt)
  | .there x, .there y, h => by
      have : x.level = y.level := Fin.castSucc_inj.mp h
      exact congrArg StableVar.there (eq_of_level_eq x y this)

theorem StableVar.atLevel_level {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (x : StableVar Γ S) :
    (StableCtx.typeAtLevel_level x) ▸ StableVar.atLevel Γ x.level = x := by
  refine StableVar.eq_of_level_eq _ _ ?_
  rw [level_eqRec, StableVar.level_atLevel]

def wkLevel {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (i : StableLevel Γ) : StableLevel (Γ.snoc S) :=
  ⟨i.1, Nat.lt_succ_of_lt i.2⟩

def wkSupport {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (K : RawSupport Γ) : RawSupport (Γ.snoc S) :=
  K.map ⟨wkLevel (S := S), by
    intro a b h
    exact Fin.ext (Fin.mk.inj h)⟩

def popSupport {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (K : RawSupport (Γ.snoc S)) : RawSupport Γ :=
  (Finset.univ : Finset (StableLevel Γ)).filter
    fun i => wkLevel (S := S) i ∈ K

theorem mem_wkSupport {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (K : RawSupport Γ) (i : StableLevel Γ) :
    i ∈ K ↔ wkLevel (S := S) i ∈ wkSupport (S := S) K := by
  constructor
  · intro hi
    exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
  · intro hi
    obtain ⟨j, hj, heq⟩ := Finset.mem_map.mp hi
    exact (Fin.ext (Fin.mk.inj heq)) ▸ hj

theorem last_not_mem_wkSupport {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (K : RawSupport Γ) :
    (Fin.last Γ.length : StableLevel (Γ.snoc S)) ∉ wkSupport (S := S) K := by
  intro h
  obtain ⟨i, _, heq⟩ := Finset.mem_map.mp h
  have hval : i.val = Γ.length := by
    have := congrArg Fin.val heq
    simp only [Fin.val_last] at this
    exact this
  exact (Nat.ne_of_lt i.isLt) hval

theorem pop_wkSupport {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (K : RawSupport Γ) :
    popSupport (S := S) (wkSupport (S := S) K) = K := by
  ext i
  simp only [popSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (mem_wkSupport (S := S) K i).symm

/-! ### Hits / masks over raw support -/

namespace RawSupport

def hits {Γ : StableCtx sig} (A K : RawSupport Γ) : Bool :=
  decide ((A ∩ K).Nonempty)

theorem hits_comm {Γ : StableCtx sig} (A K : RawSupport Γ) :
    hits A K = hits K A := by
  simp only [hits, Finset.inter_comm]

theorem hits_empty {Γ : StableCtx sig} (K : RawSupport Γ) :
    hits (∅ : RawSupport Γ) K = false := by
  simp only [hits, Finset.empty_inter, Finset.not_nonempty_empty, decide_false]

theorem hits_union {Γ : StableCtx sig} (A B K : RawSupport Γ) :
    hits (A ∪ B) K = (hits A K || hits B K) := by
  simp only [hits]
  have h : ((A ∪ B) ∩ K).Nonempty ↔ (A ∩ K).Nonempty ∨ (B ∩ K).Nonempty := by
    constructor
    · intro ⟨x, hx⟩
      simp only [Finset.mem_inter, Finset.mem_union] at hx
      rcases hx with ⟨hAB | hAB, hK⟩
      · exact Or.inl ⟨x, Finset.mem_inter.mpr ⟨hAB, hK⟩⟩
      · exact Or.inr ⟨x, Finset.mem_inter.mpr ⟨hAB, hK⟩⟩
    · intro h
      rcases h with ⟨x, hx⟩ | ⟨x, hx⟩
      · refine ⟨x, ?_⟩
        simp only [Finset.mem_inter, Finset.mem_union] at hx ⊢
        exact ⟨Or.inl hx.1, hx.2⟩
      · refine ⟨x, ?_⟩
        simp only [Finset.mem_inter, Finset.mem_union] at hx ⊢
        exact ⟨Or.inr hx.1, hx.2⟩
  rw [Bool.decide_congr h, Bool.decide_or]

def maskOf {Γ : StableCtx sig} (K : RawSupport Γ) : VarMask Γ :=
  fun _ x => decide (x.level ∈ K)

theorem maskOf_wkSupport {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (K : RawSupport Γ) :
    maskOf (wkSupport (S := S) K) = VarMask.extend (maskOf K) := by
  funext T x
  cases x with
  | here =>
    simp only [maskOf, VarMask.extend, StableVar.level]
    exact decide_eq_false (last_not_mem_wkSupport (S := S) K)
  | there y =>
    simp only [maskOf, VarMask.extend, StableVar.level]
    change decide (wkLevel (S := S) y.level ∈ wkSupport (S := S) K) =
      decide (y.level ∈ K)
    exact Bool.decide_congr (Iff.symm (mem_wkSupport (S := S) K y.level))

theorem hits_singleton {Γ : StableCtx sig} (i : StableLevel Γ) (K : RawSupport Γ) :
    hits ({i} : RawSupport Γ) K = decide (i ∈ K) := by
  simp only [hits]
  refine Bool.decide_congr ?_
  constructor
  · intro ⟨j, hj⟩
    simp only [Finset.mem_inter, Finset.mem_singleton] at hj
    exact hj.1 ▸ hj.2
  · intro hi
    exact ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self i, hi⟩⟩

end RawSupport

theorem hits_popSupport {Γ : StableCtx sig} {S : StableTy sig.nBases}
    (A : RawSupport Γ) (K : RawSupport (Γ.snoc S)) :
    RawSupport.hits A (popSupport (S := S) K) =
      RawSupport.hits (wkSupport (S := S) A) K := by
  simp only [RawSupport.hits]
  refine Bool.decide_congr ⟨?_, ?_⟩
  · intro ⟨i, hi⟩
    simp only [Finset.mem_inter, popSupport, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi
    refine ⟨wkLevel (S := S) i, ?_⟩
    simp only [Finset.mem_inter]
    exact ⟨(mem_wkSupport (S := S) A i).mp hi.1, hi.2⟩
  · intro ⟨j, hj⟩
    simp only [Finset.mem_inter] at hj
    obtain ⟨i, hiA, heq⟩ := Finset.mem_map.mp hj.1
    refine ⟨i, Finset.mem_inter.mpr ⟨hiA, ?_⟩⟩
    simp only [popSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    have heq' : wkLevel (S := S) i = j := heq
    exact heq' ▸ hj.2

/-! ### New-suffix levels -/

def newLevels (Old : StableCtx sig) :
    (New : StableCtx sig) → RawSupport (Old.append New)
  | .empty => ∅
  | .snoc Δ S =>
      insert (Fin.last (Old.append Δ).length)
        (wkSupport (S := S) (newLevels Old Δ))

@[simp] theorem newLevels_empty (Old : StableCtx sig) :
    newLevels Old (.empty : StableCtx sig) = ∅ := rfl

@[simp] theorem newLevels_snoc (Old : StableCtx sig) (Δ : StableCtx sig)
    (S : StableTy sig.nBases) :
    newLevels Old (Δ.snoc S) =
      insert (Fin.last (Old.append Δ).length)
        (wkSupport (S := S) (newLevels Old Δ)) := rfl

theorem maskOf_newLevels (Old : StableCtx sig) :
    ∀ (New : StableCtx sig),
      RawSupport.maskOf (newLevels Old New) = newMask Old New
  | .empty => by
      funext T x
      simp only [newLevels_empty, RawSupport.maskOf, newMask, isFromNew]
      exact decide_eq_false (Finset.notMem_empty _)
  | .snoc Δ S => by
      funext T x
      cases x with
      | here =>
        simp only [newLevels_snoc, RawSupport.maskOf, newMask, isFromNew,
          StableVar.level]
        exact decide_eq_true (Finset.mem_insert_self _ _)
      | there y =>
        have ih := congrFun (congrFun (maskOf_newLevels Old Δ) T) y
        simp only [newLevels_snoc, RawSupport.maskOf, newMask, isFromNew,
          StableVar.level] at ih ⊢
        have hne : wkLevel (S := S) y.level ≠
            Fin.last (Old.append Δ).length := by
          intro h
          have hval : (y.level : Nat) = (Old.append Δ).length := by
            have := congrArg Fin.val h
            simpa [wkLevel, Fin.val_last] using this
          exact (Nat.ne_of_lt y.level.isLt) hval
        refine Eq.trans ?_ ih
        change decide (wkLevel (S := S) y.level ∈
            insert (Fin.last (Old.append Δ).length)
              (wkSupport (S := S) (newLevels Old Δ))) =
          decide (y.level ∈ newLevels Old Δ)
        refine Bool.decide_congr ?_
        constructor
        · intro h
          have hmem := (Finset.mem_insert (a := wkLevel (S := S) y.level)
            (b := Fin.last (Old.append Δ).length)
            (s := wkSupport (S := S) (newLevels Old Δ))).mp h
          exact (mem_wkSupport (S := S) (newLevels Old Δ) y.level).mpr
            (hmem.resolve_left hne)
        · intro h
          exact (Finset.mem_insert (a := wkLevel (S := S) y.level)
            (b := Fin.last (Old.append Δ).length)
            (s := wkSupport (S := S) (newLevels Old Δ))).mpr
            (Or.inr ((mem_wkSupport (S := S) (newLevels Old Δ) y.level).mp h))

/-! ### Exact free raw support -/

mutual
def SNegNeu.rawSupport {Γ : StableCtx sig} {N : Neg sig.nBases} :
    SNegNeu Γ N → RawSupport Γ
  | .var x => ({x.level} : RawSupport Γ)
  | .fst n => SNegNeu.rawSupport n
  | .snd n => SNegNeu.rawSupport n
  | .app n p => SNegNeu.rawSupport n ∪ SPosNeu.rawSupport p

def SPosNeu.rawSupport {Γ : StableCtx sig} {P : Pos sig.nBases} :
    SPosNeu Γ P → RawSupport Γ
  | .atom x => ({x.level} : RawSupport Γ)
  | .inl p => SPosNeu.rawSupport p
  | .inr p => SPosNeu.rawSupport p
  | .shift t => SInv.rawSupport (Old := Γ) (New := .empty) t

def NonemptyBatchObs.rawSupport {Γ : StableCtx sig} {ps : Pending sig} :
    NonemptyBatchObs Γ ps → RawSupport Γ
  | .one n => SNegNeu.rawSupport n
  | .cons n rest => SNegNeu.rawSupport n ∪ NonemptyBatchObs.rawSupport rest

def Sat.rawSupport {Old New : StableCtx sig} {P : Pos sig.nBases} :
    Sat Old New P → RawSupport (Old.append New)
  | .done v => SPosNeu.rawSupport v
  | .batch obs body =>
      NonemptyBatchObs.rawSupport obs ∪
        (cast (by rfl)
          (SInv.rawSupport (Old := Old.append New) (New := .empty) body) :
            RawSupport (Old.append New))

def SInv.rawSupport {Old New : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} : SInv Old New ps G → RawSupport (Old.append New)
  | .unit => ∅
  | .abort => ∅
  | .pair t u => SInv.rawSupport t ∪ SInv.rawSupport u
  | .lam t => SInv.rawSupport t
  | .caseSum l r => SInv.rawSupport l ∪ SInv.rawSupport r
  | .storeAtom (q := q) t =>
      popSupport (S := .atom q)
        (cast (by rfl) (SInv.rawSupport t) :
          RawSupport ((Old.append New).snoc (.atom q)))
  | .storeShift (N := N) t =>
      popSupport (S := .neg N)
        (cast (by rfl) (SInv.rawSupport t) :
          RawSupport ((Old.append New).snoc (.neg N)))
  | .satShift s => Sat.rawSupport s
  | .satPos s => Sat.rawSupport s
end

/-! ### `uses` ↔ support intersection -/

/-- Align `hits` across `append_snoc` / `popSupport`. -/
theorem hits_popSupport_append_snoc {Old New : StableCtx sig}
    {S : StableTy sig.nBases}
    (A : RawSupport (Old.append (New.snoc S)))
    (K : RawSupport (Old.append New)) :
    RawSupport.hits A (cast (by rfl) (wkSupport (S := S) K)) =
      RawSupport.hits (popSupport (S := S) (cast (by rfl) A)) K := by
  have h :=
    hits_popSupport (S := S) K
      (cast (by rfl) A : RawSupport ((Old.append New).snoc S))
  -- h: hits K (pop (cast A)) = hits (wk K) (cast A)
  calc
    RawSupport.hits A (cast (by rfl) (wkSupport (S := S) K))
        = RawSupport.hits (cast (by rfl) (wkSupport (S := S) K)) A :=
          RawSupport.hits_comm _ _
    _ = RawSupport.hits (wkSupport (S := S) K)
          (cast (by rfl) A : RawSupport ((Old.append New).snoc S)) := rfl
    _ = RawSupport.hits K
          (popSupport (S := S)
            (cast (by rfl) A : RawSupport ((Old.append New).snoc S))) :=
          h.symm
    _ = RawSupport.hits
          (popSupport (S := S)
            (cast (by rfl) A : RawSupport ((Old.append New).snoc S)))
          K :=
          RawSupport.hits_comm _ _

mutual
theorem SNegNeu.uses_rawSupport {Γ : StableCtx sig} {N : Neg sig.nBases}
    (K : RawSupport Γ) :
    ∀ (n : SNegNeu Γ N),
      SNegNeu.uses (RawSupport.maskOf K) n =
        RawSupport.hits (SNegNeu.rawSupport n) K
  | .var x => by
      simp only [SNegNeu.uses, SNegNeu.rawSupport, RawSupport.maskOf]
      exact (RawSupport.hits_singleton x.level K).symm
  | .fst n => SNegNeu.uses_rawSupport K n
  | .snd n => SNegNeu.uses_rawSupport K n
  | .app n p => by
      simp only [SNegNeu.uses, SNegNeu.rawSupport, SNegNeu.uses_rawSupport K n,
        SPosNeu.uses_rawSupport K p, RawSupport.hits_union]

theorem SPosNeu.uses_rawSupport {Γ : StableCtx sig} {P : Pos sig.nBases}
    (K : RawSupport Γ) :
    ∀ (p : SPosNeu Γ P),
      SPosNeu.uses (RawSupport.maskOf K) p =
        RawSupport.hits (SPosNeu.rawSupport p) K
  | .atom x => by
      simp only [SPosNeu.uses, SPosNeu.rawSupport, RawSupport.maskOf]
      exact (RawSupport.hits_singleton x.level K).symm
  | .inl p => SPosNeu.uses_rawSupport K p
  | .inr p => SPosNeu.uses_rawSupport K p
  | .shift t => by
      simpa [SPosNeu.uses, SPosNeu.rawSupport] using
        SInv.uses_rawSupport (Old := Γ) (New := .empty) K t

theorem NonemptyBatchObs.anyUses_rawSupport {Γ : StableCtx sig}
    {ps : Pending sig} (K : RawSupport Γ) :
    ∀ (obs : NonemptyBatchObs Γ ps),
      NonemptyBatchObs.anyUses (RawSupport.maskOf K) obs =
        RawSupport.hits (NonemptyBatchObs.rawSupport obs) K
  | .one n => SNegNeu.uses_rawSupport K n
  | .cons n rest => by
      simp only [NonemptyBatchObs.anyUses, NonemptyBatchObs.rawSupport,
        SNegNeu.uses_rawSupport K n, NonemptyBatchObs.anyUses_rawSupport K rest,
        RawSupport.hits_union]

theorem Sat.uses_rawSupport {Old New : StableCtx sig} {P : Pos sig.nBases}
    (K : RawSupport (Old.append New)) :
    ∀ (s : Sat Old New P),
      Sat.uses (RawSupport.maskOf K) s =
        RawSupport.hits (Sat.rawSupport s) K
  | .done v => by
      simpa [Sat.uses, Sat.rawSupport] using SPosNeu.uses_rawSupport K v
  | .batch obs body => by
      -- Avoid instances-transparency mismatch on `append_empty`.
      change
        (NonemptyBatchObs.anyUses (RawSupport.maskOf K) obs ||
          SInv.uses (Old := Old.append New) (New := .empty)
            (RawSupport.maskOf
              (cast (by rfl) K :
                RawSupport ((Old.append New).append StableCtx.empty)))
            body) =
        RawSupport.hits
          (NonemptyBatchObs.rawSupport obs ∪
            (cast (by rfl)
              (SInv.rawSupport (Old := Old.append New) (New := .empty) body) :
                RawSupport (Old.append New)))
          K
      rw [NonemptyBatchObs.anyUses_rawSupport K obs,
        SInv.uses_rawSupport (Old := Old.append New) (New := .empty)
          (cast (by rfl) K) body]
      have hbody :
          RawSupport.hits
              (SInv.rawSupport (Old := Old.append New) (New := .empty) body)
              (cast (by rfl) K) =
            RawSupport.hits
              (cast (by rfl)
                (SInv.rawSupport (Old := Old.append New) (New := .empty) body) :
                  RawSupport (Old.append New))
              K := rfl
      rw [hbody, RawSupport.hits_union]

theorem SInv.uses_rawSupport {Old New : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} (K : RawSupport (Old.append New)) :
    ∀ (t : SInv Old New ps G),
      SInv.uses (RawSupport.maskOf K) t =
        RawSupport.hits (SInv.rawSupport t) K
  | .unit => by simp only [SInv.uses, SInv.rawSupport, RawSupport.hits_empty]
  | .abort => by simp only [SInv.uses, SInv.rawSupport, RawSupport.hits_empty]
  | .pair t u => by
      simp only [SInv.uses, SInv.rawSupport, SInv.uses_rawSupport K t,
        SInv.uses_rawSupport K u, RawSupport.hits_union]
  | .lam t => SInv.uses_rawSupport K t
  | .caseSum l r => by
      simp only [SInv.uses, SInv.rawSupport, SInv.uses_rawSupport K l,
        SInv.uses_rawSupport K r, RawSupport.hits_union]
  | .storeAtom (q := q) t => by
      simp only [SInv.uses, SInv.rawSupport]
      rw [← RawSupport.maskOf_wkSupport (S := .atom q) K]
      refine Eq.trans
        (SInv.uses_rawSupport (Old := Old) (New := New.snoc (.atom q))
          (cast (by rfl) (wkSupport (S := .atom q) K)) t)
        (hits_popSupport_append_snoc (S := .atom q) (SInv.rawSupport t) K)
  | .storeShift (N := N) t => by
      simp only [SInv.uses, SInv.rawSupport]
      rw [← RawSupport.maskOf_wkSupport (S := .neg N) K]
      refine Eq.trans
        (SInv.uses_rawSupport (Old := Old) (New := New.snoc (.neg N))
          (cast (by rfl) (wkSupport (S := .neg N) K)) t)
        (hits_popSupport_append_snoc (S := .neg N) (SInv.rawSupport t) K)
  | .satShift s => by
      simpa [SInv.uses, SInv.rawSupport] using Sat.uses_rawSupport K s
  | .satPos s => by
      simpa [SInv.uses, SInv.rawSupport] using Sat.uses_rawSupport K s
end

/-! ### Per-entry batch characterization -/

def NonemptyBatchObs.allHits {Γ : StableCtx sig} {ps : Pending sig}
    (K : RawSupport Γ) : NonemptyBatchObs Γ ps → Bool
  | .one n => RawSupport.hits (SNegNeu.rawSupport n) K
  | .cons n rest =>
      RawSupport.hits (SNegNeu.rawSupport n) K &&
        NonemptyBatchObs.allHits K rest

theorem NonemptyBatchObs.allUses_rawSupport_iff {Γ : StableCtx sig}
    {ps : Pending sig} (K : RawSupport Γ) :
    ∀ (obs : NonemptyBatchObs Γ ps),
      NonemptyBatchObs.allUses (RawSupport.maskOf K) obs =
        NonemptyBatchObs.allHits K obs
  | .one n => SNegNeu.uses_rawSupport K n
  | .cons n rest => by
      simp only [NonemptyBatchObs.allUses, NonemptyBatchObs.allHits,
        SNegNeu.uses_rawSupport K n,
        NonemptyBatchObs.allUses_rawSupport_iff K rest]

/-! ### Regressions -/

namespace RawSupportFixtures

open Fixtures

/-- Store-local newest level is removed by `popSupport`. -/
theorem store_local_level_popped :
    popSupport (S := .neg (.shift (.zero : Pos 0)))
      ({Fin.last 0} : RawSupport (sig := sig0)
        (StableCtx.snoc .empty (.neg (.shift .zero)))) = (∅ : RawSupport _) := by
  ext i
  exact Fin.elim0 i

/-- A pre-existing level survives store push/pop. -/
theorem preexisting_level_survives_store_pop :
    let Γ : StableCtx sig0 := .snoc .empty (.neg (.shift (.zero : Pos 0)))
    let S : StableTy 0 := .neg (.shift (.zero : Pos 0))
    let K : RawSupport Γ := {⟨0, by decide⟩}
    popSupport (S := S) (wkSupport (S := S) K) = K :=
  pop_wkSupport _

/-- `SPosNeu.shift` preserves the child's raw support. -/
theorem shift_preserves_outer_rawSupport :
    let t : SInv (sig := sig0) .empty .empty .empty (.neg .one) := .unit
    (SPosNeu.shift t).rawSupport = t.rawSupport :=
  rfl

theorem newLevels_empty_regression (Old : StableCtx sig0) :
    newLevels Old (.empty : StableCtx sig0) = ∅ :=
  newLevels_empty Old

/--
Two-entry batch: Old=`[↓0]`, New=`[↓0]`.
Head uses outer-old (`.there .here`); tail uses New (`.here`).
Union hits New, but not every entry does.
-/
def two_obs :
    NonemptyBatchObs (sig := sig0)
      (StableCtx.append
        (StableCtx.snoc .empty (.neg (.shift (.zero : Pos 0))))
        (StableCtx.snoc .empty (.neg (.shift (.zero : Pos 0)))))
      (.cons (.zero : Pos 0) (.cons (.zero : Pos 0) .empty)) :=
  .cons (.var (.there .here)) (.one (.var .here))

theorem two_obs_allUses_false_union_hits :
    let Old : StableCtx sig0 :=
      .snoc .empty (.neg (.shift (.zero : Pos 0)))
    let New : StableCtx sig0 :=
      .snoc .empty (.neg (.shift (.zero : Pos 0)))
    let K := newLevels Old New
    NonemptyBatchObs.allUses (RawSupport.maskOf K) two_obs = false ∧
      RawSupport.hits (NonemptyBatchObs.rawSupport two_obs) K = true := by
  native_decide

end RawSupportFixtures

end Gimbal.Equality.Scherer
