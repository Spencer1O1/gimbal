/-
  Finite negative-elimination obligations for the Scherer selector.

  A `NegSpine N P` records only the eliminations needed to expose a shifted
  positive endpoint `P` from a negative head `N`. Arrow arguments are supplied
  by a proof-relevant callback; order and duplicates are preserved.
-/

import Gimbal.Equality.Scherer.TypeSelectionSpec

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Finite negative spines -/

/-- An elimination path from `N` to the shifted endpoint `P`. -/
inductive NegSpine : Neg sig.nBases → Pos sig.nBases → Type where
  | shift {P} : NegSpine (.shift P) P
  | fst {A B P} : NegSpine A P → NegSpine (.prod A B) P
  | snd {A B P} : NegSpine B P → NegSpine (.prod A B) P
  | app {A N P} : NegSpine N P → NegSpine (.arr A N) P

/-- A spine with its positive endpoint packed existentially. -/
structure PackedNegSpine (N : Neg sig.nBases) where
  result : Pos sig.nBases
  spine : NegSpine N result

namespace NegSpine

def pack {N : Neg sig.nBases} {P : Pos sig.nBases}
    (sp : NegSpine N P) : PackedNegSpine N :=
  ⟨P, sp⟩

end NegSpine

namespace PackedNegSpine

def fst {A B : Neg sig.nBases} (sp : PackedNegSpine A) :
    PackedNegSpine (.prod A B) :=
  ⟨sp.result, .fst sp.spine⟩

def snd {A B : Neg sig.nBases} (sp : PackedNegSpine B) :
    PackedNegSpine (.prod A B) :=
  ⟨sp.result, .snd sp.spine⟩

def app {A : Pos sig.nBases} {N : Neg sig.nBases}
    (sp : PackedNegSpine N) : PackedNegSpine (.arr A N) :=
  ⟨sp.result, .app sp.spine⟩

end PackedNegSpine

/-- All shifted endpoints of `N`, in structural left-to-right order. -/
def enumerateNegSpines : (N : Neg sig.nBases) → List (PackedNegSpine N)
  | .one => []
  | .prod A B =>
      (enumerateNegSpines A).map PackedNegSpine.fst ++
        (enumerateNegSpines B).map PackedNegSpine.snd
  | .arr _ N => (enumerateNegSpines N).map PackedNegSpine.app
  | .shift _ => [NegSpine.shift.pack]

@[simp] theorem enumerateNegSpines_one :
    enumerateNegSpines (sig := sig) .one = [] := rfl

@[simp] theorem enumerateNegSpines_prod (A B : Neg sig.nBases) :
    enumerateNegSpines (.prod A B) =
      (enumerateNegSpines A).map PackedNegSpine.fst ++
        (enumerateNegSpines B).map PackedNegSpine.snd := rfl

@[simp] theorem enumerateNegSpines_arr (A : Pos sig.nBases) (N : Neg sig.nBases) :
    enumerateNegSpines (.arr A N) =
      (enumerateNegSpines N).map PackedNegSpine.app := rfl

@[simp] theorem enumerateNegSpines_shift (P : Pos sig.nBases) :
    enumerateNegSpines (.shift P) = [NegSpine.shift.pack] := rfl

/-- The structural enumeration contains every spine, including duplicates. -/
theorem NegSpine.pack_mem_enumerate {N : Neg sig.nBases} {P : Pos sig.nBases}
    (sp : NegSpine N P) : sp.pack ∈ enumerateNegSpines N := by
  induction sp with
  | shift => simp
  | fst sp ih =>
      simp only [enumerateNegSpines_prod, List.mem_append, List.mem_map]
      exact Or.inl ⟨sp.pack, ih, rfl⟩
  | snd sp ih =>
      simp only [enumerateNegSpines_prod, List.mem_append, List.mem_map]
      exact Or.inr ⟨sp.pack, ih, rfl⟩
  | app sp ih =>
      simp only [enumerateNegSpines_arr, List.mem_map]
      exact ⟨sp.pack, ih, rfl⟩

/-! ### Recursively fresh saturated neutrals -/

/-- A saturated negative neutral whose nested batches are all fresh-valid. -/
structure FreshSNeg (G : StableCtx sig) (N : Neg sig.nBases) where
  neutral : SNegNeu G N
  valid : neutral.freshValid = true

/-- A saturated positive neutral whose nested batches are all fresh-valid. -/
structure FreshSPos (G : StableCtx sig) (P : Pos sig.nBases) where
  neutral : SPosNeu G P
  valid : neutral.freshValid = true

namespace FreshSNeg

def fst {G : StableCtx sig} {A B : Neg sig.nBases}
    (n : FreshSNeg G (.prod A B)) : FreshSNeg G A :=
  ⟨.fst n.neutral, n.valid⟩

def snd {G : StableCtx sig} {A B : Neg sig.nBases}
    (n : FreshSNeg G (.prod A B)) : FreshSNeg G B :=
  ⟨.snd n.neutral, n.valid⟩

def app {G : StableCtx sig} {A : Pos sig.nBases} {N : Neg sig.nBases}
    (n : FreshSNeg G (.arr A N)) (p : FreshSPos G A) : FreshSNeg G N :=
  ⟨.app n.neutral p.neutral, by simp [SNegNeu.freshValid, n.valid, p.valid]⟩

@[simp] theorem neutral_fst {G : StableCtx sig} {A B : Neg sig.nBases}
    (n : FreshSNeg G (.prod A B)) : n.fst.neutral = .fst n.neutral := rfl

@[simp] theorem neutral_snd {G : StableCtx sig} {A B : Neg sig.nBases}
    (n : FreshSNeg G (.prod A B)) : n.snd.neutral = .snd n.neutral := rfl

@[simp] theorem neutral_app {G : StableCtx sig} {A : Pos sig.nBases}
    {N : Neg sig.nBases} (n : FreshSNeg G (.arr A N)) (p : FreshSPos G A) :
    (n.app p).neutral = .app n.neutral p.neutral := rfl

@[simp] theorem uses_fst {G : StableCtx sig} {A B : Neg sig.nBases}
    (m : VarMask G) (n : FreshSNeg G (.prod A B)) :
    n.fst.neutral.uses m = n.neutral.uses m := rfl

@[simp] theorem uses_snd {G : StableCtx sig} {A B : Neg sig.nBases}
    (m : VarMask G) (n : FreshSNeg G (.prod A B)) :
    n.snd.neutral.uses m = n.neutral.uses m := rfl

@[simp] theorem uses_app {G : StableCtx sig} {A : Pos sig.nBases}
    {N : Neg sig.nBases} (m : VarMask G)
    (n : FreshSNeg G (.arr A N)) (p : FreshSPos G A) :
    (n.app p).neutral.uses m =
      (n.neutral.uses m || p.neutral.uses m) := rfl

@[simp] theorem resolvedSupport_fst {O : Type} [DecidableEq O]
    {G : StableCtx sig} {A B : Neg sig.nBases} (env : ResolvedEnv G O)
    (n : FreshSNeg G (.prod A B)) :
    n.fst.neutral.resolvedSupport env = n.neutral.resolvedSupport env := rfl

@[simp] theorem resolvedSupport_snd {O : Type} [DecidableEq O]
    {G : StableCtx sig} {A B : Neg sig.nBases} (env : ResolvedEnv G O)
    (n : FreshSNeg G (.prod A B)) :
    n.snd.neutral.resolvedSupport env = n.neutral.resolvedSupport env := rfl

@[simp] theorem resolvedSupport_app {O : Type} [DecidableEq O]
    {G : StableCtx sig} {A : Pos sig.nBases} {N : Neg sig.nBases}
    (env : ResolvedEnv G O) (n : FreshSNeg G (.arr A N))
    (p : FreshSPos G A) :
    (n.app p).neutral.resolvedSupport env =
      n.neutral.resolvedSupport env ∪ p.neutral.resolvedSupport env := rfl

end FreshSNeg

/-! ### Fulfilling a spine with proof-relevant positive provider -/

namespace NegSpine

/-- Fulfill one spine; callback order and multiplicity are preserved. -/
def fulfill {G : StableCtx sig}
    (provide : (A : Pos sig.nBases) → List (FreshSPos G A)) :
    {N : Neg sig.nBases} → {P : Pos sig.nBases} →
      FreshSNeg G N → NegSpine N P → List (FreshSNeg G (.shift P))
  | _, _, head, .shift => [head]
  | _, _, head, .fst sp => fulfill provide head.fst sp
  | _, _, head, .snd sp => fulfill provide head.snd sp
  | _, _, head, .app sp =>
      (provide _).flatMap fun arg => fulfill provide (head.app arg) sp

@[simp] theorem fulfill_shift {G : StableCtx sig}
    (provide : (A : Pos sig.nBases) → List (FreshSPos G A))
    {P : Pos sig.nBases} (head : FreshSNeg G (.shift P)) :
    fulfill provide head .shift = [head] := rfl

@[simp] theorem fulfill_fst {G : StableCtx sig}
    (provide : (A : Pos sig.nBases) → List (FreshSPos G A))
    {A B : Neg sig.nBases} {P : Pos sig.nBases}
    (head : FreshSNeg G (.prod A B)) (sp : NegSpine A P) :
    fulfill provide head (.fst sp) = fulfill provide head.fst sp := rfl

@[simp] theorem fulfill_snd {G : StableCtx sig}
    (provide : (A : Pos sig.nBases) → List (FreshSPos G A))
    {A B : Neg sig.nBases} {P : Pos sig.nBases}
    (head : FreshSNeg G (.prod A B)) (sp : NegSpine B P) :
    fulfill provide head (.snd sp) = fulfill provide head.snd sp := rfl

@[simp] theorem fulfill_app {G : StableCtx sig}
    (provide : (A : Pos sig.nBases) → List (FreshSPos G A))
    {A : Pos sig.nBases} {N : Neg sig.nBases} {P : Pos sig.nBases}
    (head : FreshSNeg G (.arr A N)) (sp : NegSpine N P) :
    fulfill provide head (.app sp) =
      (provide A).flatMap fun arg => fulfill provide (head.app arg) sp := rfl

end NegSpine

/-! ### Boundary into selectable observations -/

namespace FreshSNeg

/-- Keep a fresh shifted neutral exactly when it genuinely uses `New`. -/
def toScopedObs? {Old New : StableCtx sig} {P : Pos sig.nBases}
    (n : FreshSNeg (Old.append New) (.shift P)) : Option (ScopedObs Old New P) :=
  if h : n.neutral.uses (newMask Old New) = true then
    some ⟨n.neutral, n.valid, h⟩
  else
    none

@[simp] theorem toScopedObs?_isSome {Old New : StableCtx sig}
    {P : Pos sig.nBases} (n : FreshSNeg (Old.append New) (.shift P)) :
    n.toScopedObs?.isSome = true ↔
      n.neutral.uses (newMask Old New) = true := by
  simp [toScopedObs?]

theorem toScopedObs?_some_neutral {Old New : StableCtx sig}
    {P : Pos sig.nBases} (n : FreshSNeg (Old.append New) (.shift P))
    {o : ScopedObs Old New P} (h : n.toScopedObs? = some o) :
    o.neutral = n.neutral := by
  simp only [toScopedObs?] at h
  split at h
  · cases h
    rfl
  · simp at h

end FreshSNeg

/-! ### Gate fixtures -/

namespace ElimObligationFixtures

abbrev sig0 : Signature := ⟨0, #[]⟩
abbrev sig1 : Signature := ⟨1, #[]⟩
abbrev q : Fin sig1.nBases := ⟨0, Nat.zero_lt_one⟩
abbrev X : Pos sig1.nBases := .atom q

theorem shift_endpoint :
    enumerateNegSpines (.shift X) = [NegSpine.shift.pack] := rfl

theorem both_product_projections :
    enumerateNegSpines (.prod (.shift X) (.shift X)) =
      [NegSpine.pack (.fst .shift), NegSpine.pack (.snd .shift)] := rfl

abbrev AppCtx : StableCtx sig1 :=
  (StableCtx.empty.snoc (.neg (.arr X (.shift X)))).snoc (.atom q)

def appHead : FreshSNeg AppCtx (.arr X (.shift X)) :=
  ⟨.var (.there .here), rfl⟩

def appArgNew : FreshSPos AppCtx X :=
  ⟨.atom .here, rfl⟩

def provideOnly {G : StableCtx sig} {P0 : Pos sig.nBases}
    (p0 : FreshSPos G P0) : (P : Pos sig.nBases) → List (FreshSPos G P) :=
  fun P => if h : P = P0 then [h.symm ▸ p0] else []

@[simp] theorem provideOnly_self {G : StableCtx sig} {P : Pos sig.nBases}
    (p : FreshSPos G P) : provideOnly p P = [p] := by
  simp [provideOnly]

theorem arrow_request_and_app :
    NegSpine.fulfill (provideOnly appArgNew) appHead (.app .shift) =
      [appHead.app appArgNew] := by
  simp

theorem missing_argument_empty :
    NegSpine.fulfill (fun _ => []) appHead (.app .shift) = [] := rfl

abbrev NestedCtx : StableCtx sig1 :=
  (StableCtx.empty.snoc
    (.neg (.arr X (.prod (.shift X) .one)))).snoc (.atom q)

def nestedHead : FreshSNeg NestedCtx (.arr X (.prod (.shift X) .one)) :=
  ⟨.var (.there .here), rfl⟩

def nestedArg : FreshSPos NestedCtx X :=
  ⟨.atom .here, rfl⟩

theorem nested_projection_app_spine :
    NegSpine.fulfill (provideOnly nestedArg) nestedHead (.app (.fst .shift)) =
      [(nestedHead.app nestedArg).fst] := by
  simp

abbrev TwoArgCtx : StableCtx sig1 :=
  ((StableCtx.empty.snoc (.neg (.arr X (.shift X)))).snoc (.atom q)).snoc (.atom q)

def twoArgHead : FreshSNeg TwoArgCtx (.arr X (.shift X)) :=
  ⟨.var (.there (.there .here)), rfl⟩

def olderArg : FreshSPos TwoArgCtx X := ⟨.atom (.there .here), rfl⟩
def newerArg : FreshSPos TwoArgCtx X := ⟨.atom .here, rfl⟩

def twoArgs : (P : Pos sig1.nBases) → List (FreshSPos TwoArgCtx P) :=
  fun P => if h : P = X then [h.symm ▸ olderArg, h.symm ▸ newerArg] else []

theorem two_argument_witnesses_yield_two_apps :
    NegSpine.fulfill twoArgs twoArgHead (.app .shift) =
      [twoArgHead.app olderArg, twoArgHead.app newerArg] := by
  simp [twoArgs]

abbrev BadOld : StableCtx sig0 := TypeSelectionSpecFixtures.BadOld
abbrev BadNew : StableCtx sig0 := TypeSelectionSpecFixtures.BadNew

def badNestedPositive :
    SPosNeu (BadOld.append BadNew) (.shift (.shift (.shift .one))) :=
  .shift
    (.satShift
      (.batch (.one (.var (.there .here))) .abort))

theorem badNestedPositive_freshValid_false :
    badNestedPositive.freshValid = false := by native_decide

theorem invalid_nested_positive_cannot_enter_fresh_result :
    ¬ ∃ p : FreshSPos (BadOld.append BadNew) (.shift (.shift (.shift .one))),
      p.neutral = badNestedPositive := by
  rintro ⟨p, hp⟩
  have hv := p.valid
  rw [hp, badNestedPositive_freshValid_false] at hv
  cases hv

theorem zero_endpoint_ordinary_spine :
    enumerateNegSpines (sig := sig0) (.shift .zero) =
      [NegSpine.shift.pack] := rfl

def generatorSig : Signature :=
  ⟨1, #[⟨Object.base ⟨0, by decide⟩, Object.base ⟨0, by decide⟩⟩]⟩

abbrev generatorQ : Fin generatorSig.nGens := ⟨0, by decide⟩

theorem opaque_generator_shaped_arrow_same_machinery :
    enumerateNegSpines
      (asNeg (.exp (generatorSig.gen generatorQ).source
        (generatorSig.gen generatorQ).target)) =
      [NegSpine.pack (.app .shift)] := rfl

end ElimObligationFixtures

end Gimbal.Equality.Scherer
