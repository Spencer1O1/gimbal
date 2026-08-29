/-
  Proof-relevant capped stable registries.

  `RetainedCtx` selects at most two actual ambient variables of each stable
  type. It never contracts the intrinsic context. Old/new combination follows
  Scherer's old-priority quotient: old representatives displace new ones.
-/

import Gimbal.Equality.Scherer.SearchBoundary
import Gimbal.Equality.Scherer.PairOrigin
import Gimbal.Equality.Scherer.SaturatedRenameFacts
import Mathlib.Data.Finset.Max

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Ordered stable variables -/

/-- Stable variables are ordered by their unique ambient de Bruijn level. -/
instance {G : StableCtx sig} {S : StableTy sig.nBases} :
    LinearOrder (StableVar G S) :=
  LinearOrder.lift' StableVar.level (fun _ _ => StableVar.eq_of_level_eq _ _)

/-! ### Old-priority plural algebra -/

namespace Plur

variable {α β : Type} [DecidableEq α] [DecidableEq β]

/-- Map a capped set along an embedding without changing its cardinality. -/
def mapEmbedding (f : α ↪ β) (p : Plur α) : Plur β :=
  ⟨p.1.map f, by simpa using p.2⟩

@[simp] theorem card_mapEmbedding (f : α ↪ β) (p : Plur α) :
    (mapEmbedding f p).1.card = p.1.card := by
  simp [mapEmbedding]

theorem mem_mapEmbedding {f : α ↪ β} {p : Plur α} {x : α} :
    f x ∈ (mapEmbedding f p).1 ↔ x ∈ p.1 := by
  simp [mapEmbedding]

/-- Keep only the least (oldest) representative, when one exists. -/
def takeOldest [LinearOrder α] (p : Plur α) : Plur α :=
  if h : p.1.Nonempty then singleton (p.1.min' h) else empty

theorem takeOldest_subset [LinearOrder α] (p : Plur α) :
    (takeOldest p).1 ⊆ p.1 := by
  simp only [takeOldest]
  split
  · intro x hx
    simp only [coe_singleton, Finset.mem_singleton] at hx
    subst x
    exact Finset.min'_mem _ _
  · simp

theorem card_takeOldest [LinearOrder α] (p : Plur α) :
    (takeOldest p).1.card = if p.1.Nonempty then 1 else 0 := by
  unfold takeOldest
  split <;> simp_all

theorem mem_takeOldest_iff [LinearOrder α] {p : Plur α} {x : α} :
    x ∈ (takeOldest p).1 ↔ ∃ h : p.1.Nonempty, x = p.1.min' h := by
  unfold takeOldest
  split
  · rename_i h
    simp only [coe_singleton, Finset.mem_singleton]
    exact ⟨fun hx => ⟨h, hx⟩, fun ⟨_, hx⟩ => hx⟩
  · rename_i h
    simp only [coe_empty, Finset.notMem_empty, false_iff]
    exact fun ⟨hne, _⟩ => h hne

/-- Candidates not already represented by the old registry. -/
def without (delta gamma : Plur α) : Plur α :=
  ⟨delta.1 \ gamma.1,
    le_trans (Finset.card_le_card Finset.sdiff_subset) delta.2⟩

/--
The effective new registry `delta / gamma`. Old has strict priority; with one
old representative only the oldest genuinely-new representative survives.
-/
def quotient [LinearOrder α] (delta gamma : Plur α) : Plur α :=
  if gamma.1.card = 0 then delta
  else if gamma.1.card = 1 then takeOldest (without delta gamma)
  else empty

theorem quotient_eq_of_card_zero [LinearOrder α] {delta gamma : Plur α}
    (h : gamma.1.card = 0) : quotient delta gamma = delta := by
  simp [quotient, h]

theorem quotient_eq_of_card_one [LinearOrder α] {delta gamma : Plur α}
    (h : gamma.1.card = 1) :
    quotient delta gamma = takeOldest (without delta gamma) := by
  simp [quotient, h]

theorem quotient_eq_of_card_two [LinearOrder α] {delta gamma : Plur α}
    (h : gamma.1.card = 2) : quotient delta gamma = empty := by
  simp [quotient, h]

theorem quotient_subset_delta [LinearOrder α] (delta gamma : Plur α) :
    (quotient delta gamma).1 ⊆ delta.1 := by
  unfold quotient
  split
  · exact fun _ h => h
  · split
    · exact fun x hx =>
        (Finset.mem_sdiff.mp (takeOldest_subset (without delta gamma) hx)).1
    · simp

theorem quotient_disjoint [LinearOrder α] (delta gamma : Plur α) :
    Disjoint (quotient delta gamma).1 gamma.1 := by
  rw [Finset.disjoint_left]
  intro x hxq hxg
  unfold quotient at hxq
  split at hxq
  · rename_i hzero
    have : gamma.1 = ∅ := Finset.card_eq_zero.mp hzero
    simpa [this] using hxg
  · split at hxq
    · have hd := takeOldest_subset (without delta gamma) hxq
      exact (Finset.mem_sdiff.mp hd).2 hxg
    · simp at hxq

theorem card_quotient [LinearOrder α] (delta gamma : Plur α) :
    (quotient delta gamma).1.card =
      min (2 - gamma.1.card) (delta.1 \ gamma.1).card := by
  unfold quotient
  split
  · rename_i hzero
    have he : gamma.1 = ∅ := Finset.card_eq_zero.mp hzero
    simp [he, Nat.min_eq_right delta.2]
  · rename_i hnzero
    split
    · rename_i hone
      rw [card_takeOldest]
      by_cases hne : (delta.1 \ gamma.1).Nonempty
      · have hne' : (without delta gamma).1.Nonempty := hne
        rw [if_pos hne']
        have hc : 0 < (delta.1 \ gamma.1).card := Finset.card_pos.mpr hne
        omega
      · have he : delta.1 \ gamma.1 = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact hne ⟨x, hx⟩
        have he' : (without delta gamma).1 = ∅ := he
        have hne' : ¬ (without delta gamma).1.Nonempty := by
          intro h'
          exact hne h'
        rw [if_neg hne']
        rw [he]
        simp [hone]
    · rename_i hnone
      have htwo : gamma.1.card = 2 := by omega
      simp [htwo]

/-- Old-priority capped union. -/
def addAfter [LinearOrder α] (gamma delta : Plur α) : Plur α :=
  let q := quotient delta gamma
  ⟨gamma.1 ∪ q.1, by
    rw [Finset.card_union_of_disjoint (quotient_disjoint delta gamma).symm,
      card_quotient]
    omega⟩

@[simp] theorem coe_addAfter [LinearOrder α] (gamma delta : Plur α) :
    (addAfter gamma delta).1 = gamma.1 ∪ (quotient delta gamma).1 := rfl

theorem mem_addAfter_iff [LinearOrder α] {gamma delta : Plur α} {x : α} :
    x ∈ (addAfter gamma delta).1 ↔
      x ∈ gamma.1 ∨ x ∈ (quotient delta gamma).1 := by
  simp [addAfter]

theorem card_addAfter [LinearOrder α] (gamma delta : Plur α) :
    (addAfter gamma delta).1.card =
      gamma.1.card + (quotient delta gamma).1.card := by
  rw [coe_addAfter, Finset.card_union_of_disjoint
    (quotient_disjoint delta gamma).symm]

theorem mem_addAfter_old [LinearOrder α] {gamma delta : Plur α} {x : α}
    (h : x ∈ gamma.1) : x ∈ (addAfter gamma delta).1 := by
  simp [addAfter, h]

theorem mem_quotient_addAfter [LinearOrder α] {gamma delta : Plur α} {x : α}
    (h : x ∈ (quotient delta gamma).1) : x ∈ (addAfter gamma delta).1 := by
  simp [addAfter, h]

theorem card_le_addAfter [LinearOrder α] (gamma delta : Plur α) :
    gamma.1.card ≤ (addAfter gamma delta).1.card :=
  Finset.card_le_card (by intro x hx; exact mem_addAfter_old hx)

end Plur

/-! ### Ambient-indexed retained registries -/

/-- At most two actual ambient variables for each supplied stable type. -/
structure RetainedCtx (U : TypeUniverse sig) (G : StableCtx sig) where
  slots : (S : ↥U.stable) → Plur (StableVar G S.1)

namespace RetainedCtx

variable {U : TypeUniverse sig} {G D : StableCtx sig}

@[ext] theorem ext {C D : RetainedCtx U G}
    (h : ∀ S, C.slots S = D.slots S) : C = D := by
  cases C with
  | mk c =>
    cases D with
    | mk d =>
      congr
      funext S
      exact h S

def empty : RetainedCtx U G where
  slots := fun _ => Plur.empty

def rename (rho : StableRename G D)
    (hinj : ∀ S, Function.Injective (@rho S))
    (C : RetainedCtx U G) : RetainedCtx U D where
  slots S := Plur.mapEmbedding ⟨@rho S.1, hinj S.1⟩ (C.slots S)

def weaken (C : RetainedCtx U G) (T : StableTy sig.nBases) :
    RetainedCtx U (G.snoc T) :=
  rename StableRename.weaken (fun _ x y h => by
    have hl := congrArg StableVar.level h
    exact StableVar.eq_of_level_eq x y (Fin.castSucc_inj.mp hl)) C

def insert (C : RetainedCtx U G) (S : ↥U.stable)
    (x : StableVar G S.1) : RetainedCtx U G where
  slots := Function.update C.slots S (Plur.insert x (C.slots S))

theorem insert_of_mem (C : RetainedCtx U G) (S : ↥U.stable)
    {x : StableVar G S.1} (hx : x ∈ (C.slots S).1) :
    C.insert S x = C := by
  apply RetainedCtx.ext
  intro T
  by_cases h : T = S
  · subst T
    simp [insert, Plur.insert_of_mem hx]
  · simp [insert, h]

/-- Grow the ambient context, then retain its newest binder if there is room. -/
def push (C : RetainedCtx U G) (S : ↥U.stable) :
    RetainedCtx U (G.snoc S.1) :=
  (C.weaken S.1).insert S .here

def quotient (delta gamma : RetainedCtx U G) : RetainedCtx U G where
  slots S := Plur.quotient (delta.slots S) (gamma.slots S)

def addAfter (gamma delta : RetainedCtx U G) : RetainedCtx U G where
  slots S := Plur.addAfter (gamma.slots S) (delta.slots S)

/-- Forget actual variables and retain only capped type multiplicities. -/
def toCtx2 (C : RetainedCtx U G) : Ctx2 U :=
  fun S => Count2.ofNatCap (C.slots S).1.card

theorem Count2.toNat_ofNatCap_of_le_two {n : Nat} (h : n ≤ 2) :
    (Count2.ofNatCap n).toNat = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  cases n with
  | zero => contradiction
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      have : n = 0 := by omega
      subst n
      rfl

@[simp] theorem toCtx2_count (C : RetainedCtx U G) (S : ↥U.stable) :
    (C.toCtx2 S).toNat = (C.slots S).1.card :=
  Count2.toNat_ofNatCap_of_le_two (C.slots S).2

@[simp] theorem toCtx2_rename (rho : StableRename G D)
    (hinj : ∀ S, Function.Injective (@rho S)) (C : RetainedCtx U G) :
    (C.rename rho hinj).toCtx2 = C.toCtx2 := by
  funext S
  apply Count2.toNat_injective
  simp [toCtx2_count, rename]

theorem Plur.card_le_insert {α : Type} [DecidableEq α]
    (x : α) (p : Plur α) : p.1.card ≤ (Plur.insert x p).1.card := by
  exact Finset.card_le_card fun _ h => Plur.mem_insert_of_mem h

theorem toCtx2_insert_mono (C : RetainedCtx U G) (S : ↥U.stable)
    (x : StableVar G S.1) : C.toCtx2.LE (C.insert S x).toCtx2 := by
  intro T
  by_cases h : T = S
  · subst T
    simpa [toCtx2_count, insert] using Plur.card_le_insert x (C.slots S)
  · simp [toCtx2_count, insert, h]

private theorem newest_not_mem_weaken (C : RetainedCtx U G) (S : ↥U.stable) :
    (.here : StableVar (G.snoc S.1) S.1) ∉ ((C.weaken S.1).slots S).1 := by
  intro h
  obtain ⟨x, _, hx⟩ := Finset.mem_map.mp h
  have hl := congrArg StableVar.level hx
  have hv := congrArg Fin.val hl
  simp only [Fin.val_castSucc, Fin.val_last] at hv
  exact (Nat.ne_of_lt x.level.isLt) hv

theorem Plur.ofNatCap_insert_of_not_mem {α : Type} [DecidableEq α]
    {x : α} {p : Plur α} (hx : x ∉ p.1) :
    Count2.ofNatCap (Plur.insert x p).1.card =
      (Count2.ofNatCap p.1.card).bump := by
  unfold Plur.insert
  simp only [hx, ↓reduceDIte]
  split
  · rename_i hroom
    rw [Finset.card_cons hx]
    rcases Nat.eq_zero_or_pos p.1.card with h | h
    · simp [h, Count2.ofNatCap, Count2.bump]
    · have heq : p.1.card = 1 := by omega
      simp [heq, Count2.ofNatCap, Count2.bump]
  · rename_i hfull
    have hcard : p.1.card = 2 := by omega
    simp [hcard, Count2.ofNatCap, Count2.bump]

@[simp] theorem toCtx2_push (C : RetainedCtx U G) (S : ↥U.stable) :
    (C.push S).toCtx2 = Ctx2.insert C.toCtx2 S := by
  funext T
  by_cases h : T = S
  · subst T
    simp only [push, toCtx2, insert, Function.update_self, Ctx2.insert_same]
    rw [Plur.ofNatCap_insert_of_not_mem (newest_not_mem_weaken C S)]
    congr 1
    apply Count2.toNat_injective
    simp [weaken, rename, Plur.mapEmbedding]
  · simp [push, toCtx2, insert, Ctx2.insert_other _ h,
      h, weaken, rename, Plur.mapEmbedding]

theorem old_le_addAfter (gamma delta : RetainedCtx U G) :
    gamma.toCtx2.LE (gamma.addAfter delta).toCtx2 := by
  intro S
  simpa [toCtx2_count, addAfter] using
    Plur.card_le_addAfter (gamma.slots S) (delta.slots S)

theorem addAfter_eq_iff_quotient_empty (gamma delta : RetainedCtx U G) :
    gamma.addAfter delta = gamma ↔
      ∀ S, (delta.quotient gamma).slots S = Plur.empty := by
  constructor
  · intro heq S
    have hs := congrArg (fun C : RetainedCtx U G => (C.slots S).1) heq
    apply Subtype.ext
    change (Plur.quotient (delta.slots S) (gamma.slots S)).1 = ∅
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxg : x ∈ (gamma.slots S).1 := by
      rw [← hs]
      exact Finset.mem_union_right _ hx
    exact (Finset.disjoint_left.mp
      (Plur.quotient_disjoint (delta.slots S) (gamma.slots S))) hx hxg
  · intro h
    apply RetainedCtx.ext
    intro S
    apply Subtype.ext
    have hs := congrArg Subtype.val (h S)
    change (gamma.slots S).1 ∪
        (Plur.quotient (delta.slots S) (gamma.slots S)).1 =
      (gamma.slots S).1
    change (Plur.quotient (delta.slots S) (gamma.slots S)).1 = ∅ at hs
    rw [hs]
    simp

theorem strictGrow_addAfter_iff (gamma delta : RetainedCtx U G) :
    gamma.toCtx2.StrictGrow (gamma.addAfter delta).toCtx2 ↔
      ∃ S, ((delta.quotient gamma).slots S).1.Nonempty := by
  let mono := old_le_addAfter gamma delta
  rw [Ctx2.strictGrow_iff_exists_lt mono]
  constructor
  · rintro ⟨S, hlt⟩
    refine ⟨S, ?_⟩
    by_contra h
    have he : (delta.quotient gamma).slots S = Plur.empty := by
      apply Subtype.ext
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ⟨x, hx⟩
    have hs : (gamma.addAfter delta).slots S = gamma.slots S := by
      apply Subtype.ext
      have he' := congrArg Subtype.val he
      change (gamma.slots S).1 ∪
          (Plur.quotient (delta.slots S) (gamma.slots S)).1 =
        (gamma.slots S).1
      change (Plur.quotient (delta.slots S) (gamma.slots S)).1 = ∅ at he'
      rw [he']
      simp
    rw [toCtx2_count, toCtx2_count, hs] at hlt
    exact Nat.lt_irrefl _ hlt
  · rintro ⟨S, hne⟩
    refine ⟨S, ?_⟩
    have hd := Plur.quotient_disjoint (delta.slots S) (gamma.slots S)
    change (Plur.quotient (delta.slots S) (gamma.slots S)).1.Nonempty at hne
    rw [toCtx2_count, toCtx2_count]
    simp only [addAfter, Plur.coe_addAfter]
    rw [Finset.card_union_of_disjoint hd.symm]
    have hp := Finset.card_pos.mpr hne
    omega

end RetainedCtx

/-! ### Exact-label contraction impossibility -/

namespace OriginAssignment

def Preserves {R : AliasResolver sig} {G D : StableCtx sig}
    (rho : StableRename G D) (E : OriginAssignment R G)
    (E' : OriginAssignment R D) : Prop :=
  ∀ (S : StableTy sig.nBases) (x : StableVar G S), E'.ref (rho x) = E.ref x

end OriginAssignment

namespace RetainedCtxFixtures

abbrev sig0 : Signature := ⟨0, #[]⟩
abbrev S : StableTy sig0.nBases := .neg (.shift .zero)
abbrev G1 : StableCtx sig0 := .snoc .empty S
abbrev G2 : StableCtx sig0 := .snoc G1 S
abbrev G3 : StableCtx sig0 := .snoc G2 S

def U : TypeUniverse sig0 where
  positive := {.zero}
  stable := {S}

theorem Smem : S ∈ U.stable := by simp [U]
def slot : ↥U.stable := ⟨S, Smem⟩

def C0 : RetainedCtx U (.empty : StableCtx sig0) := RetainedCtx.empty
def C1 : RetainedCtx U G1 := C0.push slot
def C2 : RetainedCtx U G2 := C1.push slot
def C3 : RetainedCtx U G3 := C2.push slot

theorem duplicate_same_variable : C1.insert slot .here = C1 := by
  apply RetainedCtx.insert_of_mem
  change (.here : StableVar G1 S) ∈
    (Plur.insert .here ((C0.weaken S).slots slot)).1
  apply Plur.mem_insert_self_of_room
  change (∅ : Finset (StableVar G1 S)).card < 2
  simp

theorem second_distinct_grows : C1.toCtx2.StrictGrow C2.toCtx2 := by
  constructor
  · intro T
    have hT : T = slot := by
      apply Subtype.ext
      exact Finset.mem_singleton.mp (by simpa [U] using T.2)
    subst T
    native_decide
  · intro h
    have hs := congrFun h slot
    have hne : C1.toCtx2 slot ≠ C2.toCtx2 slot := by native_decide
    exact hne hs
theorem third_distinct_capped : C3.toCtx2 = C2.toCtx2 := by native_decide

def oldFull : Plur (Fin 4) := Plur.insert 1 (Plur.singleton 0)
def oldOne : Plur (Fin 4) := Plur.singleton 0
def newTwo : Plur (Fin 4) := Plur.insert 3 (Plur.singleton 2)

theorem old_full_rejects_new : Plur.quotient newTwo oldFull = Plur.empty := by
  native_decide

theorem old_one_retains_oldest_new :
    Plur.quotient newTwo oldOne = Plur.singleton 2 := by native_decide

theorem old_empty_retains_first_two :
    Plur.addAfter Plur.empty newTwo = newTwo := by native_decide

abbrev O3 := Fin 3
def o0 : O3 := ⟨0, by decide⟩
def o1 : O3 := ⟨1, by decide⟩
def o2 : O3 := ⟨2, by decide⟩
def K0 : DepSupport O3 := {o0}
def K1 : DepSupport O3 := {o1}
def K2 : DepSupport O3 := {o2}

def env0 : ResolvedEnv (.empty : StableCtx sig0) O3 := ResolvedEnv.empty O3
def env2 : ResolvedEnv G2 O3 :=
  ResolvedEnv.extend (ResolvedEnv.extend env0 K0) K1
def env3 : ResolvedEnv G3 O3 := ResolvedEnv.extend env2 K2

def R : AliasResolver sig0 := AliasResolver.identity sig0
def r0 : ResolvedRef R S.erase := ResolvedRef.of R (stableOrigin sig0 S.erase 10 0)
def r1 : ResolvedRef R S.erase := ResolvedRef.of R (stableOrigin sig0 S.erase 11 0)
def r2 : ResolvedRef R S.erase := ResolvedRef.of R (stableOrigin sig0 S.erase 12 0)
def E0 : OriginAssignment R (.empty : StableCtx sig0) := OriginAssignment.empty R
def E2 : OriginAssignment R G2 := (E0.snoc r0).snoc r1
def E3 : OriginAssignment R G3 := E2.snoc r2

theorem three_labels_pairwise_distinct :
    K0 ≠ K1 ∧ K0 ≠ K2 ∧ K1 ≠ K2 ∧
      r0 ≠ r1 ∧ r0 ≠ r2 ∧ r1 ≠ r2 := by native_decide

private theorem env2_ne_K2 : ∀ x : StableVar G2 S, env2 S x ≠ K2
  | .here => three_labels_pairwise_distinct.2.2.1
  | .there .here => three_labels_pairwise_distinct.2.1

/-- No exact environment/origin-preserving contraction can discard the third label. -/
theorem no_exact_label_preserving_three_to_two :
    ¬ ∃ rho : StableRename G3 G2,
      ResolvedEnv.Preserves rho env3 env2 ∧
        OriginAssignment.Preserves rho E3 E2 := by
  rintro ⟨rho, henv, _⟩
  have h := henv S (.here : StableVar G3 S)
  apply env2_ne_K2 (rho (.here : StableVar G3 S))
  simpa [env3] using h

end RetainedCtxFixtures

end Gimbal.Equality.Scherer
