/-
  Renaming/contraction facts for saturated Scherer syntax.

  Generated `sizeOf` counts de Bruijn variable constructors and therefore is
  not invariant under many-to-one contraction.  `nodeSize` below counts each
  variable occurrence with constant weight and is the invariant needed by the
  normal-query splice argument.
-/

import Gimbal.Equality.Scherer.SaturatedResolved
import Gimbal.Equality.Scherer.Renaming

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Mask- and environment-respecting renamings -/

def MaskPreserves {Γ Δ : StableCtx sig} (ρ : StableRename Γ Δ)
    (mΓ : VarMask Γ) (mΔ : VarMask Δ) : Prop :=
  ∀ (S : StableTy sig.nBases) (x : StableVar Γ S), mΔ S (ρ x) = mΓ S x

namespace MaskPreserves

theorem ext {Γ Δ : StableCtx sig} {S : StableTy sig.nBases}
    {ρ : StableRename Γ Δ} {mΓ : VarMask Γ} {mΔ : VarMask Δ}
    (h : MaskPreserves ρ mΓ mΔ) :
    MaskPreserves (@StableRename.ext sig Γ Δ S ρ)
      (@VarMask.extend sig Γ S mΓ) (@VarMask.extend sig Δ S mΔ) := by
  intro T x
  cases x with
  | here => rfl
  | there y => exact h _ y

end MaskPreserves

namespace StableRename

/-- Renaming the old factor cannot change membership in the new factor. -/
theorem newMask_keepLeft {Old Old' : StableCtx sig} (ρ : StableRename Old Old') :
    ∀ (New : StableCtx sig),
      MaskPreserves (keepLeft ρ New) (newMask Old New) (newMask Old' New)
  | .empty => by intro S x; rfl
  | .snoc New T => by
      intro S x
      cases x with
      | here => rfl
      | there y => exact newMask_keepLeft ρ New _ y

end StableRename

namespace ResolvedEnv

def Preserves {O : Type} {Γ Δ : StableCtx sig} (ρ : StableRename Γ Δ)
    (envΓ : ResolvedEnv Γ O) (envΔ : ResolvedEnv Δ O) : Prop :=
  ∀ (S : StableTy sig.nBases) (x : StableVar Γ S), envΔ S (ρ x) = envΓ S x

theorem Preserves.ext {O : Type} {Γ Δ : StableCtx sig}
    {S : StableTy sig.nBases} {ρ : StableRename Γ Δ}
    {envΓ : ResolvedEnv Γ O} {envΔ : ResolvedEnv Δ O}
    (h : Preserves ρ envΓ envΔ) (K : DepSupport O) :
    Preserves (@StableRename.ext sig Γ Δ S ρ)
      (@ResolvedEnv.extend sig O Γ S envΓ K)
      (@ResolvedEnv.extend sig O Δ S envΔ K) := by
  intro T x
  cases x with
  | here => rfl
  | there y => exact h _ y

end ResolvedEnv

/-! ### Uses naturality -/

mutual

theorem SNegNeu.uses_rename {Γ Δ : StableCtx sig} {N : Neg sig.nBases}
    (ρ : StableRename Γ Δ) (mΓ : VarMask Γ) (mΔ : VarMask Δ)
    (hm : MaskPreserves ρ mΓ mΔ) (n : SNegNeu Γ N) :
    (n.rename ρ).uses mΔ = n.uses mΓ :=
  match n with
  | .var x => hm _ x
  | .fst n => SNegNeu.uses_rename ρ mΓ mΔ hm n
  | .snd n => SNegNeu.uses_rename ρ mΓ mΔ hm n
  | .app n p => by
      simp only [SNegNeu.rename, SNegNeu.uses]
      rw [SNegNeu.uses_rename ρ mΓ mΔ hm n,
        SPosNeu.uses_rename ρ mΓ mΔ hm p]
termination_by sizeOf n
decreasing_by
  all_goals (simp_wf; omega)

theorem SPosNeu.uses_rename {Γ Δ : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Γ Δ) (mΓ : VarMask Γ) (mΔ : VarMask Δ)
    (hm : MaskPreserves ρ mΓ mΔ) (p : SPosNeu Γ P) :
    (p.rename ρ).uses mΔ = p.uses mΓ :=
  match p with
  | .atom x => hm _ x
  | .inl p => SPosNeu.uses_rename ρ mΓ mΔ hm p
  | .inr p => SPosNeu.uses_rename ρ mΓ mΔ hm p
  | .shift t => by
      simpa [SPosNeu.rename, SPosNeu.uses] using
        SInv.uses_rename (Old := Γ) (Old' := Δ) (New := .empty)
          ρ mΓ mΔ hm t
termination_by sizeOf p
decreasing_by
  all_goals (simp_wf; omega)

theorem NonemptyBatchObs.anyUses_rename {Γ Δ : StableCtx sig}
    {ps : Pending sig} (ρ : StableRename Γ Δ)
    (mΓ : VarMask Γ) (mΔ : VarMask Δ) (hm : MaskPreserves ρ mΓ mΔ)
    (obs : NonemptyBatchObs Γ ps) :
    (obs.rename ρ).anyUses mΔ = obs.anyUses mΓ :=
  match obs with
  | .one n => SNegNeu.uses_rename ρ mΓ mΔ hm n
  | .cons n rest => by
      simp only [NonemptyBatchObs.rename, NonemptyBatchObs.anyUses]
      rw [SNegNeu.uses_rename ρ mΓ mΔ hm n,
        NonemptyBatchObs.anyUses_rename ρ mΓ mΔ hm rest]
termination_by sizeOf obs
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec]
    omega)

theorem NonemptyBatchObs.allUses_rename {Γ Δ : StableCtx sig}
    {ps : Pending sig} (ρ : StableRename Γ Δ)
    (mΓ : VarMask Γ) (mΔ : VarMask Δ) (hm : MaskPreserves ρ mΓ mΔ)
    (obs : NonemptyBatchObs Γ ps) :
    (obs.rename ρ).allUses mΔ = obs.allUses mΓ :=
  match obs with
  | .one n => SNegNeu.uses_rename ρ mΓ mΔ hm n
  | .cons n rest => by
      simp only [NonemptyBatchObs.rename, NonemptyBatchObs.allUses]
      rw [SNegNeu.uses_rename ρ mΓ mΔ hm n,
        NonemptyBatchObs.allUses_rename ρ mΓ mΔ hm rest]
termination_by sizeOf obs
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec]
    omega)

theorem Sat.uses_rename {Old Old' New : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Old Old')
    (m : VarMask (Old.append New)) (m' : VarMask (Old'.append New))
    (hm : MaskPreserves (StableRename.keepLeft ρ New) m m')
    (s : Sat Old New P) : (s.rename ρ).uses m' = s.uses m :=
  match s with
  | .inconsistent z =>
      SNegNeu.uses_rename (StableRename.keepLeft ρ New) m m' hm z
  | .done v => SPosNeu.uses_rename (StableRename.keepLeft ρ New) m m' hm v
  | .batch obs body => by
      simp only [Sat.rename, Sat.uses]
      rw [NonemptyBatchObs.anyUses_rename (StableRename.keepLeft ρ New) m m' hm obs]
      rw [SInv.uses_rename
        (Old := Old.append New) (Old' := Old'.append New) (New := .empty)
        (StableRename.keepLeft ρ New) m m' hm body]
termination_by sizeOf s
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec, Sat.inconsistent.sizeOf_spec,
      Sat.done.sizeOf_spec, Sat.batch.sizeOf_spec]
    omega)

theorem SInv.uses_rename {Old Old' New : StableCtx sig}
    {ps : Pending sig} {G : Goal sig.nBases} (ρ : StableRename Old Old')
    (m : VarMask (Old.append New)) (m' : VarMask (Old'.append New))
    (hm : MaskPreserves (StableRename.keepLeft ρ New) m m')
    (t : SInv Old New ps G) : (t.rename ρ).uses m' = t.uses m :=
  match t with
  | .unit => rfl
  | .abort => rfl
  | .pair l r => by
      simp only [SInv.rename, SInv.uses]
      rw [SInv.uses_rename ρ m m' hm l, SInv.uses_rename ρ m m' hm r]
  | .lam t => SInv.uses_rename ρ m m' hm t
  | .caseSum l r => by
      simp only [SInv.rename, SInv.uses]
      rw [SInv.uses_rename ρ m m' hm l, SInv.uses_rename ρ m m' hm r]
  | .storeAtom (q := q) t => by
      simpa [SInv.rename, SInv.uses] using
        SInv.uses_rename (Old := Old) (Old' := Old')
          (New := New.snoc (.atom q)) ρ
          (VarMask.extend m) (VarMask.extend m') (MaskPreserves.ext hm) t
  | .storeShift (N := N) t => by
      simpa [SInv.rename, SInv.uses] using
        SInv.uses_rename (Old := Old) (Old' := Old')
          (New := New.snoc (.neg N)) ρ
          (VarMask.extend m) (VarMask.extend m') (MaskPreserves.ext hm) t
  | .satShift s => Sat.uses_rename ρ m m' hm s
  | .satPos s => Sat.uses_rename ρ m m' hm s
termination_by sizeOf t
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec, Sat.inconsistent.sizeOf_spec,
      Sat.done.sizeOf_spec, Sat.batch.sizeOf_spec]
    omega)

end

/-! ### Two-bit output provenance -/

structure UseSig where
  usesOuter : Bool
  usesCurrent : Bool
  deriving DecidableEq, Repr

def SNegNeu.useSig {Γ : StableCtx sig} {N : Neg sig.nBases}
    (outer current : VarMask Γ) (n : SNegNeu Γ N) : UseSig :=
  ⟨n.uses outer, n.uses current⟩

theorem SNegNeu.useSig_rename {Γ Δ : StableCtx sig} {N : Neg sig.nBases}
    (ρ : StableRename Γ Δ) (outer current : VarMask Γ)
    (outer' current' : VarMask Δ)
    (ho : MaskPreserves ρ outer outer') (hc : MaskPreserves ρ current current')
    (n : SNegNeu Γ N) :
    (n.rename ρ).useSig outer' current' = n.useSig outer current := by
  unfold SNegNeu.useSig
  rw [SNegNeu.uses_rename ρ outer outer' ho n,
    SNegNeu.uses_rename ρ current current' hc n]

/-! ### Raw-support image under possibly non-injective renaming -/

def StableRename.mapLevel {Γ Δ : StableCtx sig} (ρ : StableRename Γ Δ)
    (i : StableLevel Γ) : StableLevel Δ :=
  (ρ (StableVar.atLevel Γ i)).level

def StableRename.mapRaw {Γ Δ : StableCtx sig} (ρ : StableRename Γ Δ)
    (K : RawSupport Γ) : RawSupport Δ :=
  K.image ρ.mapLevel

def StableRename.preimageRaw {Γ Δ : StableCtx sig} (ρ : StableRename Γ Δ)
    (K : RawSupport Δ) : RawSupport Γ :=
  (Finset.univ : RawSupport Γ).filter fun i => ρ.mapLevel i ∈ K

private theorem StableRename.level_rename_eqRec {Γ Δ : StableCtx sig}
    (ρ : StableRename Γ Δ) {S S' : StableTy sig.nBases}
    (e : S = S') (x : StableVar Γ S) :
    (ρ (e ▸ x)).level = (ρ x).level := by
  cases e
  rfl

theorem StableRename.mapLevel_level {Γ Δ : StableCtx sig}
    (ρ : StableRename Γ Δ) {S : StableTy sig.nBases} (x : StableVar Γ S) :
    ρ.mapLevel x.level = (ρ x).level := by
  let e : Γ.typeAtLevel x.level = S := StableCtx.typeAtLevel_level x
  let y := StableVar.atLevel Γ x.level
  have hcast := StableRename.level_rename_eqRec ρ e y
  have hxy : e ▸ y = x := StableVar.atLevel_level x
  have hr := congrArg (fun z : StableVar Γ S => (ρ z).level) hxy
  exact hcast.symm.trans hr

theorem StableRename.maskOf_preimageRaw {Γ Δ : StableCtx sig}
    (ρ : StableRename Γ Δ) (K : RawSupport Δ) :
    MaskPreserves ρ (RawSupport.maskOf (ρ.preimageRaw K))
      (RawSupport.maskOf K) := by
  intro S x
  simp only [RawSupport.maskOf, StableRename.preimageRaw, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [StableRename.mapLevel_level]

theorem RawSupport.hits_mapRaw {Γ Δ : StableCtx sig}
    (ρ : StableRename Γ Δ) (A : RawSupport Γ) (K : RawSupport Δ) :
    RawSupport.hits (ρ.mapRaw A) K =
      RawSupport.hits A (ρ.preimageRaw K) := by
  simp only [RawSupport.hits]
  apply Bool.decide_congr
  constructor
  · rintro ⟨i, hi⟩
    simp only [Finset.mem_inter] at hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi.1
    exact ⟨j, Finset.mem_inter.mpr ⟨hj, by
      simp [StableRename.preimageRaw, hi.2]⟩⟩
  · rintro ⟨j, hj⟩
    simp only [Finset.mem_inter, StableRename.preimageRaw,
      Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨ρ.mapLevel j, Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨j, hj.1, rfl⟩, hj.2⟩⟩

theorem RawSupport.eq_mapRaw_of_hits {Γ Δ : StableCtx sig}
    (ρ : StableRename Γ Δ) (A : RawSupport Γ) (B : RawSupport Δ)
    (h : ∀ K : RawSupport Δ,
      RawSupport.hits B K = RawSupport.hits A (ρ.preimageRaw K)) :
    B = ρ.mapRaw A := by
  ext i
  have hi := h ({i} : RawSupport Δ)
  rw [← RawSupport.hits_mapRaw ρ A {i}] at hi
  simpa [RawSupport.hits, Finset.Nonempty] using hi

theorem SNegNeu.rawSupport_rename {Γ Δ : StableCtx sig} {N : Neg sig.nBases}
    (ρ : StableRename Γ Δ) (n : SNegNeu Γ N) :
    (n.rename ρ).rawSupport = ρ.mapRaw n.rawSupport := by
  apply RawSupport.eq_mapRaw_of_hits ρ
  intro K
  rw [← SNegNeu.uses_rawSupport K (n.rename ρ),
    SNegNeu.uses_rename ρ (RawSupport.maskOf (ρ.preimageRaw K))
      (RawSupport.maskOf K) (StableRename.maskOf_preimageRaw ρ K) n,
    SNegNeu.uses_rawSupport (ρ.preimageRaw K) n]

theorem SPosNeu.rawSupport_rename {Γ Δ : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Γ Δ) (p : SPosNeu Γ P) :
    (p.rename ρ).rawSupport = ρ.mapRaw p.rawSupport := by
  apply RawSupport.eq_mapRaw_of_hits ρ
  intro K
  rw [← SPosNeu.uses_rawSupport K (p.rename ρ),
    SPosNeu.uses_rename ρ (RawSupport.maskOf (ρ.preimageRaw K))
      (RawSupport.maskOf K) (StableRename.maskOf_preimageRaw ρ K) p,
    SPosNeu.uses_rawSupport (ρ.preimageRaw K) p]

theorem NonemptyBatchObs.rawSupport_rename {Γ Δ : StableCtx sig}
    {ps : Pending sig} (ρ : StableRename Γ Δ) (obs : NonemptyBatchObs Γ ps) :
    (obs.rename ρ).rawSupport = ρ.mapRaw obs.rawSupport := by
  apply RawSupport.eq_mapRaw_of_hits ρ
  intro K
  rw [← NonemptyBatchObs.anyUses_rawSupport K (obs.rename ρ),
    NonemptyBatchObs.anyUses_rename ρ (RawSupport.maskOf (ρ.preimageRaw K))
      (RawSupport.maskOf K) (StableRename.maskOf_preimageRaw ρ K) obs,
    NonemptyBatchObs.anyUses_rawSupport (ρ.preimageRaw K) obs]

theorem Sat.rawSupport_rename {Old Old' New : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Old Old') (s : Sat Old New P) :
    (s.rename ρ).rawSupport =
      StableRename.mapRaw (StableRename.keepLeft ρ New) s.rawSupport := by
  apply RawSupport.eq_mapRaw_of_hits (StableRename.keepLeft ρ New)
  intro K
  rw [← Sat.uses_rawSupport K (s.rename ρ),
    Sat.uses_rename ρ
      (RawSupport.maskOf
        (StableRename.preimageRaw (StableRename.keepLeft ρ New) K))
      (RawSupport.maskOf K)
      (StableRename.maskOf_preimageRaw (StableRename.keepLeft ρ New) K) s,
    Sat.uses_rawSupport
      (StableRename.preimageRaw (StableRename.keepLeft ρ New) K) s]

theorem SInv.rawSupport_rename {Old Old' New : StableCtx sig}
    {ps : Pending sig} {G : Goal sig.nBases} (ρ : StableRename Old Old')
    (t : SInv Old New ps G) :
    (t.rename ρ).rawSupport =
      StableRename.mapRaw (StableRename.keepLeft ρ New) t.rawSupport := by
  apply RawSupport.eq_mapRaw_of_hits (StableRename.keepLeft ρ New)
  intro K
  rw [← SInv.uses_rawSupport K (t.rename ρ),
    SInv.uses_rename ρ
      (RawSupport.maskOf
        (StableRename.preimageRaw (StableRename.keepLeft ρ New) K))
      (RawSupport.maskOf K)
      (StableRename.maskOf_preimageRaw (StableRename.keepLeft ρ New) K) t,
    SInv.uses_rawSupport
      (StableRename.preimageRaw (StableRename.keepLeft ρ New) K) t]

/-! ### Recursive freshness naturality -/

mutual

theorem SNegNeu.freshValid_rename {Γ Δ : StableCtx sig} {N : Neg sig.nBases}
    (ρ : StableRename Γ Δ) (n : SNegNeu Γ N) :
    (n.rename ρ).freshValid = n.freshValid :=
  match n with
  | .var _ => rfl
  | .fst n => SNegNeu.freshValid_rename ρ n
  | .snd n => SNegNeu.freshValid_rename ρ n
  | .app n p => by
      simp only [SNegNeu.rename, SNegNeu.freshValid]
      rw [SNegNeu.freshValid_rename ρ n, SPosNeu.freshValid_rename ρ p]
termination_by sizeOf n
decreasing_by all_goals (simp_wf; omega)

theorem SPosNeu.freshValid_rename {Γ Δ : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Γ Δ) (p : SPosNeu Γ P) :
    (p.rename ρ).freshValid = p.freshValid :=
  match p with
  | .atom _ => rfl
  | .inl p => SPosNeu.freshValid_rename ρ p
  | .inr p => SPosNeu.freshValid_rename ρ p
  | .shift t => by
      simpa [SPosNeu.rename, SPosNeu.freshValid] using
        SInv.freshValid_rename (Old := Γ) (Old' := Δ) (New := .empty) ρ t
termination_by sizeOf p
decreasing_by all_goals (simp_wf; omega)

theorem NonemptyBatchObs.allFreshValid_rename {Γ Δ : StableCtx sig}
    {ps : Pending sig} (ρ : StableRename Γ Δ) (obs : NonemptyBatchObs Γ ps) :
    (obs.rename ρ).allFreshValid = obs.allFreshValid :=
  match obs with
  | .one n => SNegNeu.freshValid_rename ρ n
  | .cons n rest => by
      simp only [NonemptyBatchObs.rename, NonemptyBatchObs.allFreshValid]
      rw [SNegNeu.freshValid_rename ρ n,
        NonemptyBatchObs.allFreshValid_rename ρ rest]
termination_by sizeOf obs
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec]
    omega)

theorem Sat.freshValid_rename {Old Old' New : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Old Old') (s : Sat Old New P) :
    (s.rename ρ).freshValid = s.freshValid :=
  match s with
  | .inconsistent z => SNegNeu.freshValid_rename (StableRename.keepLeft ρ New) z
  | .done v => SPosNeu.freshValid_rename (StableRename.keepLeft ρ New) v
  | .batch obs body => by
      simp only [Sat.rename, Sat.freshValid]
      rw [NonemptyBatchObs.allUses_rename
        (StableRename.keepLeft ρ New) (newMask Old New) (newMask Old' New)
        (StableRename.newMask_keepLeft ρ New) obs,
        NonemptyBatchObs.allFreshValid_rename (StableRename.keepLeft ρ New) obs]
      rw [SInv.freshValid_rename
        (Old := Old.append New) (Old' := Old'.append New) (New := .empty)
        (StableRename.keepLeft ρ New) body]
termination_by sizeOf s
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec, Sat.inconsistent.sizeOf_spec,
      Sat.done.sizeOf_spec, Sat.batch.sizeOf_spec]
    omega)

theorem SInv.freshValid_rename {Old Old' New : StableCtx sig}
    {ps : Pending sig} {G : Goal sig.nBases} (ρ : StableRename Old Old')
    (t : SInv Old New ps G) : (t.rename ρ).freshValid = t.freshValid :=
  match t with
  | .unit => rfl
  | .abort => rfl
  | .pair l r => by
      simp only [SInv.rename, SInv.freshValid]
      rw [SInv.freshValid_rename ρ l, SInv.freshValid_rename ρ r]
  | .lam t => SInv.freshValid_rename ρ t
  | .caseSum l r => by
      simp only [SInv.rename, SInv.freshValid]
      rw [SInv.freshValid_rename ρ l, SInv.freshValid_rename ρ r]
  | .storeAtom t => SInv.freshValid_rename ρ t
  | .storeShift t => SInv.freshValid_rename ρ t
  | .satShift s => Sat.freshValid_rename ρ s
  | .satPos s => Sat.freshValid_rename ρ s
termination_by sizeOf t
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec, Sat.inconsistent.sizeOf_spec,
      Sat.done.sizeOf_spec, Sat.batch.sizeOf_spec]
    omega)

end

/-! ### Resolved support naturality -/

mutual

theorem SNegNeu.resolvedSupport_rename {O : Type} [DecidableEq O]
    {Γ Δ : StableCtx sig} {env : ResolvedEnv Γ O} {env' : ResolvedEnv Δ O}
    {N : Neg sig.nBases} (ρ : StableRename Γ Δ)
    (he : ResolvedEnv.Preserves ρ env env') (n : SNegNeu Γ N) :
    (n.rename ρ).resolvedSupport env' = n.resolvedSupport env :=
  match n with
  | .var x => he _ x
  | .fst n => SNegNeu.resolvedSupport_rename ρ he n
  | .snd n => SNegNeu.resolvedSupport_rename ρ he n
  | .app n p => by
      simp only [SNegNeu.rename, SNegNeu.resolvedSupport]
      rw [SNegNeu.resolvedSupport_rename ρ he n,
        SPosNeu.resolvedSupport_rename ρ he p]
termination_by sizeOf n
decreasing_by all_goals (simp_wf; omega)

theorem SPosNeu.resolvedSupport_rename {O : Type} [DecidableEq O]
    {Γ Δ : StableCtx sig} {env : ResolvedEnv Γ O} {env' : ResolvedEnv Δ O}
    {P : Pos sig.nBases} (ρ : StableRename Γ Δ)
    (he : ResolvedEnv.Preserves ρ env env') (p : SPosNeu Γ P) :
    (p.rename ρ).resolvedSupport env' = p.resolvedSupport env :=
  match p with
  | .atom x => he _ x
  | .inl p => SPosNeu.resolvedSupport_rename ρ he p
  | .inr p => SPosNeu.resolvedSupport_rename ρ he p
  | .shift t => by
      simpa [SPosNeu.rename, SPosNeu.resolvedSupport] using
        SInv.resolvedSupport_rename (Old := Γ) (Old' := Δ) (New := .empty)
          ρ he (.empty : PendingDeps O (.empty : Pending sig)) t
termination_by sizeOf p
decreasing_by all_goals (simp_wf; omega)

theorem NonemptyBatchObs.resolvedPending_rename {O : Type} [DecidableEq O]
    {Γ Δ : StableCtx sig} {env : ResolvedEnv Γ O} {env' : ResolvedEnv Δ O}
    {ps : Pending sig} (ρ : StableRename Γ Δ)
    (he : ResolvedEnv.Preserves ρ env env') (obs : NonemptyBatchObs Γ ps) :
    (obs.rename ρ).resolvedPending env' = obs.resolvedPending env :=
  match obs with
  | .one n => by
      simp only [NonemptyBatchObs.rename, NonemptyBatchObs.resolvedPending]
      rw [SNegNeu.resolvedSupport_rename ρ he n]
  | .cons n rest => by
      simp only [NonemptyBatchObs.rename, NonemptyBatchObs.resolvedPending]
      rw [SNegNeu.resolvedSupport_rename ρ he n,
        NonemptyBatchObs.resolvedPending_rename ρ he rest]
termination_by sizeOf obs
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec]
    omega)

theorem NonemptyBatchObs.resolvedSupport_rename {O : Type} [DecidableEq O]
    {Γ Δ : StableCtx sig} {env : ResolvedEnv Γ O} {env' : ResolvedEnv Δ O}
    {ps : Pending sig} (ρ : StableRename Γ Δ)
    (he : ResolvedEnv.Preserves ρ env env') (obs : NonemptyBatchObs Γ ps) :
    (obs.rename ρ).resolvedSupport env' = obs.resolvedSupport env :=
  match obs with
  | .one n => SNegNeu.resolvedSupport_rename ρ he n
  | .cons n rest => by
      simp only [NonemptyBatchObs.rename, NonemptyBatchObs.resolvedSupport]
      rw [SNegNeu.resolvedSupport_rename ρ he n,
        NonemptyBatchObs.resolvedSupport_rename ρ he rest]
termination_by sizeOf obs
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec]
    omega)

theorem Sat.resolvedSupport_rename {O : Type} [DecidableEq O]
    {Old Old' New : StableCtx sig}
    {env : ResolvedEnv (Old.append New) O}
    {env' : ResolvedEnv (Old'.append New) O} {P : Pos sig.nBases}
    (ρ : StableRename Old Old')
    (he : ResolvedEnv.Preserves (StableRename.keepLeft ρ New) env env')
    (s : Sat Old New P) :
    (s.rename ρ).resolvedSupport env' = s.resolvedSupport env :=
  match s with
  | .inconsistent z =>
      SNegNeu.resolvedSupport_rename (StableRename.keepLeft ρ New) he z
  | .done v => SPosNeu.resolvedSupport_rename (StableRename.keepLeft ρ New) he v
  | .batch obs body => by
      simp only [Sat.rename, Sat.resolvedSupport]
      rw [NonemptyBatchObs.resolvedSupport_rename
        (StableRename.keepLeft ρ New) he obs,
        NonemptyBatchObs.resolvedPending_rename
          (StableRename.keepLeft ρ New) he obs]
      rw [SInv.resolvedSupport_rename
        (Old := Old.append New) (Old' := Old'.append New) (New := .empty)
        (StableRename.keepLeft ρ New) he (obs.resolvedPending env) body]
termination_by sizeOf s
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec, Sat.inconsistent.sizeOf_spec,
      Sat.done.sizeOf_spec, Sat.batch.sizeOf_spec]
    omega)

theorem SInv.resolvedSupport_rename {O : Type} [DecidableEq O]
    {Old Old' New : StableCtx sig}
    {env : ResolvedEnv (Old.append New) O}
    {env' : ResolvedEnv (Old'.append New) O}
    {ps : Pending sig} {G : Goal sig.nBases} (ρ : StableRename Old Old')
    (he : ResolvedEnv.Preserves (StableRename.keepLeft ρ New) env env')
    (ann : PendingDeps O ps) (t : SInv Old New ps G) :
    (t.rename ρ).resolvedSupport env' ann = t.resolvedSupport env ann :=
  match ann, t with
  | .empty, .unit => rfl
  | .empty, .pair l r => by
      simp only [SInv.rename, SInv.resolvedSupport]
      rw [SInv.resolvedSupport_rename ρ he .empty l,
        SInv.resolvedSupport_rename ρ he .empty r]
  | .empty, .lam t => SInv.resolvedSupport_rename ρ he (.cons ∅ .empty) t
  | .empty, .satShift s => Sat.resolvedSupport_rename ρ he s
  | .empty, .satPos s => Sat.resolvedSupport_rename ρ he s
  | .cons K rest, .caseSum l r => by
      simp only [SInv.rename, SInv.resolvedSupport]
      rw [SInv.resolvedSupport_rename ρ he (.cons K rest) l,
        SInv.resolvedSupport_rename ρ he (.cons K rest) r]
  | .cons _ _, .abort => rfl
  | .cons K rest, .storeAtom (q := q) t =>
      SInv.resolvedSupport_rename (Old := Old) (Old' := Old')
        (New := New.snoc (.atom q)) ρ
        (ResolvedEnv.Preserves.ext (S := .atom q) he K) rest t
  | .cons K rest, .storeShift (N := N) t =>
      SInv.resolvedSupport_rename (Old := Old) (Old' := Old')
        (New := New.snoc (.neg N)) ρ
        (ResolvedEnv.Preserves.ext (S := .neg N) he K) rest t
termination_by sizeOf t
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec, Sat.inconsistent.sizeOf_spec,
      Sat.done.sizeOf_spec, Sat.batch.sizeOf_spec]
    omega)

end

theorem SNegResolved.rename {O : Type} [DecidableEq O]
    {Γ Δ : StableCtx sig} {env : ResolvedEnv Γ O} {env' : ResolvedEnv Δ O}
    {N : Neg sig.nBases} {n : SNegNeu Γ N} {K : DepSupport O}
    (ρ : StableRename Γ Δ) (he : ResolvedEnv.Preserves ρ env env')
    (h : SNegResolved env n K) : SNegResolved env' (n.rename ρ) K := by
  rw [SNegResolved, SNegNeu.resolvedSupport_rename ρ he n, h]

/-! ### Constructor-node size -/

mutual

def SNegNeu.nodeSize {Γ : StableCtx sig} {N : Neg sig.nBases} :
    SNegNeu Γ N → Nat
  | .var _ => 1
  | .fst n => n.nodeSize + 1
  | .snd n => n.nodeSize + 1
  | .app n p => n.nodeSize + p.nodeSize + 1

def SPosNeu.nodeSize {Γ : StableCtx sig} {P : Pos sig.nBases} :
    SPosNeu Γ P → Nat
  | .atom _ => 1
  | .inl p => p.nodeSize + 1
  | .inr p => p.nodeSize + 1
  | .shift t => t.nodeSize + 1

def NonemptyBatchObs.nodeSize {Γ : StableCtx sig} {ps : Pending sig} :
    NonemptyBatchObs Γ ps → Nat
  | .one n => n.nodeSize + 1
  | .cons n rest => n.nodeSize + rest.nodeSize + 1

def Sat.nodeSize {Old New : StableCtx sig} {P : Pos sig.nBases} :
    Sat Old New P → Nat
  | .inconsistent z => z.nodeSize + 1
  | .done v => v.nodeSize + 1
  | .batch obs body => obs.nodeSize + body.nodeSize + 1

def SInv.nodeSize {Old New : StableCtx sig} {ps : Pending sig}
    {G : Goal sig.nBases} : SInv Old New ps G → Nat
  | .caseSum l r => l.nodeSize + r.nodeSize + 1
  | .abort => 1
  | .storeAtom t => t.nodeSize + 1
  | .storeShift t => t.nodeSize + 1
  | .unit => 1
  | .pair l r => l.nodeSize + r.nodeSize + 1
  | .lam t => t.nodeSize + 1
  | .satShift s => s.nodeSize + 1
  | .satPos s => s.nodeSize + 1

end

mutual

theorem SNegNeu.nodeSize_rename {Γ Δ : StableCtx sig} {N : Neg sig.nBases}
    (ρ : StableRename Γ Δ) (n : SNegNeu Γ N) :
    (n.rename ρ).nodeSize = n.nodeSize :=
  match n with
  | .var _ => rfl
  | .fst n => by simp [SNegNeu.rename, SNegNeu.nodeSize,
      SNegNeu.nodeSize_rename ρ n]
  | .snd n => by simp [SNegNeu.rename, SNegNeu.nodeSize,
      SNegNeu.nodeSize_rename ρ n]
  | .app n p => by simp [SNegNeu.rename, SNegNeu.nodeSize,
      SNegNeu.nodeSize_rename ρ n, SPosNeu.nodeSize_rename ρ p]
termination_by sizeOf n
decreasing_by all_goals (simp_wf; omega)

theorem SPosNeu.nodeSize_rename {Γ Δ : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Γ Δ) (p : SPosNeu Γ P) :
    (p.rename ρ).nodeSize = p.nodeSize :=
  match p with
  | .atom _ => rfl
  | .inl p => by simp [SPosNeu.rename, SPosNeu.nodeSize,
      SPosNeu.nodeSize_rename ρ p]
  | .inr p => by simp [SPosNeu.rename, SPosNeu.nodeSize,
      SPosNeu.nodeSize_rename ρ p]
  | .shift t => by simp [SPosNeu.rename, SPosNeu.nodeSize,
      SInv.nodeSize_rename (Old := Γ) (Old' := Δ) (New := .empty) ρ t]
termination_by sizeOf p
decreasing_by all_goals (simp_wf; omega)

theorem NonemptyBatchObs.nodeSize_rename {Γ Δ : StableCtx sig}
    {ps : Pending sig} (ρ : StableRename Γ Δ) (obs : NonemptyBatchObs Γ ps) :
    (obs.rename ρ).nodeSize = obs.nodeSize :=
  match obs with
  | .one n => by simp [NonemptyBatchObs.rename, NonemptyBatchObs.nodeSize,
      SNegNeu.nodeSize_rename ρ n]
  | .cons n rest => by simp [NonemptyBatchObs.rename, NonemptyBatchObs.nodeSize,
      SNegNeu.nodeSize_rename ρ n, NonemptyBatchObs.nodeSize_rename ρ rest]
termination_by sizeOf obs
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec]
    omega)

theorem Sat.nodeSize_rename {Old Old' New : StableCtx sig} {P : Pos sig.nBases}
    (ρ : StableRename Old Old') (s : Sat Old New P) :
    (s.rename ρ).nodeSize = s.nodeSize :=
  match s with
  | .inconsistent z => by simp [Sat.rename, Sat.nodeSize,
      SNegNeu.nodeSize_rename (StableRename.keepLeft ρ New) z]
  | .done v => by simp [Sat.rename, Sat.nodeSize,
      SPosNeu.nodeSize_rename (StableRename.keepLeft ρ New) v]
  | .batch obs body => by simp [Sat.rename, Sat.nodeSize,
      NonemptyBatchObs.nodeSize_rename (StableRename.keepLeft ρ New) obs,
      SInv.nodeSize_rename (Old := Old.append New) (Old' := Old'.append New)
        (New := .empty) (StableRename.keepLeft ρ New) body]
termination_by sizeOf s
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec, Sat.inconsistent.sizeOf_spec,
      Sat.done.sizeOf_spec, Sat.batch.sizeOf_spec]
    omega)

theorem SInv.nodeSize_rename {Old Old' New : StableCtx sig}
    {ps : Pending sig} {G : Goal sig.nBases} (ρ : StableRename Old Old')
    (t : SInv Old New ps G) : (t.rename ρ).nodeSize = t.nodeSize :=
  match t with
  | .caseSum l r => by simp [SInv.rename, SInv.nodeSize,
      SInv.nodeSize_rename ρ l, SInv.nodeSize_rename ρ r]
  | .abort => rfl
  | .storeAtom t => by simp [SInv.rename, SInv.nodeSize, SInv.nodeSize_rename ρ t]
  | .storeShift t => by simp [SInv.rename, SInv.nodeSize, SInv.nodeSize_rename ρ t]
  | .unit => rfl
  | .pair l r => by simp [SInv.rename, SInv.nodeSize,
      SInv.nodeSize_rename ρ l, SInv.nodeSize_rename ρ r]
  | .lam t => by simp [SInv.rename, SInv.nodeSize, SInv.nodeSize_rename ρ t]
  | .satShift s => by simp [SInv.rename, SInv.nodeSize, Sat.nodeSize_rename ρ s]
  | .satPos s => by simp [SInv.rename, SInv.nodeSize, Sat.nodeSize_rename ρ s]
termination_by sizeOf t
decreasing_by
  all_goals (
    simp_wf
    try simp only [NonemptyBatchObs.one.sizeOf_spec,
      NonemptyBatchObs.cons.sizeOf_spec, Sat.inconsistent.sizeOf_spec,
      Sat.done.sizeOf_spec, Sat.batch.sizeOf_spec]
    omega)

end


/-! ### Contraction regressions -/

namespace SaturatedRenameFixtures

def sig0 : Signature := ⟨0, #[]⟩
abbrev O1 := Fin 1
def o : O1 := ⟨0, by decide⟩
def S : StableTy 0 := .neg (.shift .zero)
def Γ1 : StableCtx sig0 := .snoc .empty S
def Γ2 : StableCtx sig0 := .snoc Γ1 S

/-- Both equal outer occurrences contract to the sole target occurrence. -/
def contractTwo : StableRename Γ2 Γ1
  | _, .here => .here
  | _, .there .here => .here
  | _, .there (.there x) => nomatch x

def env1 : ResolvedEnv Γ1 O1 := fun _ _ => {o}
def env2 : ResolvedEnv Γ2 O1 := fun _ _ => {o}

theorem contractTwo_env : ResolvedEnv.Preserves contractTwo env2 env1 := by
  intro T x
  cases x with
  | here => rfl
  | there y =>
      cases y with
      | here => rfl
      | there z => nomatch z

def bothTrue1 : VarMask Γ1 := fun _ _ => true
def bothTrue2 : VarMask Γ2 := fun _ _ => true

theorem contractTwo_mask : MaskPreserves contractTwo bothTrue2 bothTrue1 := by
  intro T x
  cases x with
  | here => rfl
  | there y =>
      cases y with
      | here => rfl
      | there z => nomatch z

def twoOuterObs : NonemptyBatchObs (sig := sig0) Γ2
    (.cons .zero (.cons .zero .empty)) :=
  .cons (.var .here) (.one (.var (.there .here)))

theorem many_to_one_preserves_support_and_useSig :
    (twoOuterObs.rename contractTwo).resolvedSupport env1 =
        twoOuterObs.resolvedSupport env2 ∧
      (SNegNeu.rename contractTwo (SNegNeu.var (.here : StableVar Γ2 S))).useSig
          bothTrue1 bothTrue1 =
        (SNegNeu.var (.here : StableVar Γ2 S)).useSig bothTrue2 bothTrue2 ∧
      (twoOuterObs.rename contractTwo).rawSupport =
        StableRename.mapRaw contractTwo twoOuterObs.rawSupport ∧
      (twoOuterObs.rename contractTwo).nodeSize = twoOuterObs.nodeSize := by
  exact ⟨NonemptyBatchObs.resolvedSupport_rename contractTwo contractTwo_env _,
    SNegNeu.useSig_rename contractTwo bothTrue2 bothTrue2 bothTrue1 bothTrue1
      contractTwo_mask contractTwo_mask _,
    NonemptyBatchObs.rawSupport_rename contractTwo _,
    NonemptyBatchObs.nodeSize_rename contractTwo _⟩

/-- Extending contraction keeps the newest store-local binder distinct. -/
theorem newest_store_local_stays_distinct :
    StableRename.ext contractTwo
        (.here : StableVar (Γ2.snoc S) S) ≠
      StableRename.ext contractTwo
        (.there (.here : StableVar Γ2 S)) := by
  intro h
  cases h

def splitMask2 : VarMask Γ2
  | _, .here => true
  | _, .there _ => false

/-- A contraction cannot respect a mask that distinguishes its two sources. -/
theorem mismatched_current_mask_cannot_contract :
    ¬ ∃ m : VarMask Γ1, MaskPreserves contractTwo splitMask2 m := by
  rintro ⟨m, hm⟩
  have hnew := hm S (.here : StableVar Γ2 S)
  have hold := hm S (.there (.here : StableVar Γ1 S))
  change m S .here = true at hnew
  change m S .here = false at hold
  rw [hnew] at hold
  cases hold

end SaturatedRenameFixtures

end Gimbal.Equality.Scherer
