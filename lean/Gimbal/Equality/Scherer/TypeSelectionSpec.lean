/-
  Type-only selection specification for the Scherer core.

  This module is deliberately below executable selection.  A selected entry
  retains its actual saturated neutral, recursively checked freshness,
  resolved support, and a caller-chosen typed origin.  Only the coverage and
  strong-retrieval questions forget support: Scherer's SELECT-SPECIF is by
  positive result type.

  Zero is kept outside ordinary batches.  `RoundSpec` gives local
  inconsistency strict priority, while the nonzero branch is governed by
  `TypeSelectSpec`.
-/

import Gimbal.Equality.Scherer.Freshness
import Gimbal.Equality.Scherer.SaturatedResolved

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### Type-only strong retrieval -/

/-- Strong retrieval with the resolved-support label deliberately erased. -/
def TypeStrong (Γ : StableCtx sig) (P : Pos sig.nBases) : Prop :=
  Nonempty (StrongPos Γ P)

/-- Intrinsic strong retrieval at one exact resolved support. -/
def SupportedStrong {O : Type} {Γ : StableCtx sig} (env : ResolvedEnv Γ O)
    (P : Pos sig.nBases) (K : DepSupport O) : Prop :=
  Nonempty { sp : StrongPos Γ P // StrongPos.depSupport env sp = K }

namespace TypeStrong

theorem of_supported {O : Type} {env : ResolvedEnv Γ O}
    {P : Pos sig.nBases} {K : DepSupport O}
    (h : SupportedStrong env P K) : TypeStrong Γ P := by
  rcases h with ⟨⟨sp, _⟩⟩
  exact ⟨sp⟩

theorem of_strongAt {U : SearchUniverse sig} {O : Type} {B : Nat}
    {st : ResolvedState U O B} {Γ : StableCtx sig}
    {env : ResolvedEnv Γ O} (realizes : CtxRealizes st Γ env)
    {P : Pos sig.nBases} {K : DepSupport O}
    (h : StrongAt st P K) : TypeStrong Γ P := by
  rcases StrongAt.reify realizes h with ⟨⟨sp, _⟩⟩
  exact ⟨sp⟩

end TypeStrong

/-! ### Proof-relevant available observations -/

/--
An actual observation at one old/new split.  `freshValid` recursively checks
every nested batch, not only the root use of `New`.
-/
structure ScopedObs (Old New : StableCtx sig) (P : Pos sig.nBases) where
  neutral : SNegNeu (Old.append New) (.shift P)
  freshValid : neutral.freshValid = true
  usesNew : neutral.uses (newMask Old New) = true

namespace ScopedObs

theorem recursivelyFresh (o : ScopedObs Old New P) :
    o.neutral.freshValid = true :=
  o.freshValid

theorem genuinelyNew (o : ScopedObs Old New P) :
    o.neutral.uses (newMask Old New) = true :=
  o.usesNew

end ScopedObs

/--
A selectable entry.  `Origin` is abstract but indexed by the positive result,
so later source-site and alias-normalized origin implementations can be used
without changing the selection specification.
-/
structure TypedObs (Old New : StableCtx sig) (O : Type) [DecidableEq O]
    (Origin : Pos sig.nBases → Type)
    (env : ResolvedEnv (Old.append New) O) where
  result : Pos sig.nBases
  obs : ScopedObs Old New result
  support : DepSupport O
  support_eq : obs.neutral.resolvedSupport env = support
  origin : Origin result

/-- Availability remains a generic, proof-relevant predicate on actual entries. -/
abbrev ObsAvailability (Old New : StableCtx sig) (O : Type) [DecidableEq O]
    (Origin : Pos sig.nBases → Type)
    (env : ResolvedEnv (Old.append New) O) : Type :=
  TypedObs Old New O Origin env → Prop

namespace TypedObs

variable {O : Type} [DecidableEq O]
  {Origin : Pos sig.nBases → Type}
  {Old New : StableCtx sig} {env : ResolvedEnv (Old.append New) O}

theorem actualSupport (e : TypedObs Old New O Origin env) :
    e.obs.neutral.resolvedSupport env = e.support :=
  e.support_eq

theorem recursivelyFresh (e : TypedObs Old New O Origin env) :
    e.obs.neutral.freshValid = true :=
  e.obs.freshValid

theorem genuinelyNew (e : TypedObs Old New O Origin env) :
    e.obs.neutral.uses (newMask Old New) = true :=
  e.obs.usesNew

end TypedObs

/-! ### Nonzero SELECT-SPECIF -/

/--
Type-only nonzero selection.  The selected entries are still full
`TypedObs` values; only `cover` forgets exact support and origin.
-/
structure TypeSelectSpec {O : Type} [DecidableEq O]
    {Origin : Pos sig.nBases → Type}
    {Old New : StableCtx sig} {env : ResolvedEnv (Old.append New) O}
    (available : ObsAvailability Old New O Origin env)
    (selected : List (TypedObs Old New O Origin env)) : Prop where
  sound : ∀ e, e ∈ selected → available e
  nonzero : ∀ e, e ∈ selected → e.result ≠ .zero
  cover : ∀ e, available e → e.result ≠ .zero →
    TypeStrong (Old.append New) e.result ∨
      ∃ chosen ∈ selected, chosen.result = e.result

namespace TypeSelectSpec

variable {O : Type} [DecidableEq O]
  {Origin : Pos sig.nBases → Type}
  {Old New : StableCtx sig} {env : ResolvedEnv (Old.append New) O}
  {available : ObsAvailability Old New O Origin env}
  {selected : List (TypedObs Old New O Origin env)}

theorem selected_available (h : TypeSelectSpec available selected)
    {e : TypedObs Old New O Origin env} (he : e ∈ selected) : available e :=
  h.sound e he

theorem selected_result_nonzero (h : TypeSelectSpec available selected)
    {e : TypedObs Old New O Origin env} (he : e ∈ selected) :
    e.result ≠ .zero :=
  h.nonzero e he

theorem selected_of_not_strong (h : TypeSelectSpec available selected)
    (e : TypedObs Old New O Origin env) (ha : available e)
    (hnz : e.result ≠ .zero) (hns : ¬ TypeStrong (Old.append New) e.result) :
    ∃ chosen ∈ selected, chosen.result = e.result := by
  exact (h.cover e ha hnz).resolve_left hns

/-- Enlarging the concrete selected list preserves the type-only specification. -/
theorem mono (h : TypeSelectSpec available selected)
    {larger : List (TypedObs Old New O Origin env)}
    (sound : ∀ e, e ∈ larger → available e)
    (nonzero : ∀ e, e ∈ larger → e.result ≠ .zero)
    (subset : ∀ e, e ∈ selected → e ∈ larger) :
    TypeSelectSpec available larger where
  sound := sound
  nonzero := nonzero
  cover := by
    intro e ha hnz
    rcases h.cover e ha hnz with hs | ⟨chosen, hc, hr⟩
    · exact Or.inl hs
    · exact Or.inr ⟨chosen, subset chosen hc, hr⟩

end TypeSelectSpec

/-! ### Strict-priority round outcomes -/

/-- A locally available zero observation. -/
def LocalZero {O : Type} [DecidableEq O]
    {Origin : Pos sig.nBases → Type}
    {Old New : StableCtx sig} {env : ResolvedEnv (Old.append New) O}
    (available : ObsAvailability Old New O Origin env) : Prop :=
  ∃ e, available e ∧ e.result = .zero

inductive RoundMode where
  | inconsistent
  | done
  | batch
  deriving DecidableEq

/-- Zero is a terminal outcome; ordinary selected entries are necessarily nonzero. -/
inductive RoundDecision {O : Type} [DecidableEq O]
    {Origin : Pos sig.nBases → Type}
    {Old New : StableCtx sig} (env : ResolvedEnv (Old.append New) O) where
  | inconsistent (zero : TypedObs Old New O Origin env)
      (result_eq : zero.result = .zero)
  | selected (entries : List (TypedObs Old New O Origin env))

namespace RoundDecision

variable {O : Type} [DecidableEq O]
  {Origin : Pos sig.nBases → Type}
  {Old New : StableCtx sig} {env : ResolvedEnv (Old.append New) O}

def mode : RoundDecision (Origin := Origin) env → RoundMode
  | .inconsistent _ _ => .inconsistent
  | .selected [] => .done
  | .selected (_ :: _) => .batch

def entries : RoundDecision (Origin := Origin) env →
    List (TypedObs Old New O Origin env)
  | .inconsistent _ _ => []
  | .selected xs => xs

@[simp] theorem mode_inconsistent
    (z : TypedObs Old New O Origin env) (hz : z.result = .zero) :
    mode (.inconsistent z hz) = .inconsistent := rfl

@[simp] theorem mode_selected_nil :
    mode (.selected ([] : List (TypedObs Old New O Origin env))) = .done := rfl

@[simp] theorem mode_selected_cons
    (e : TypedObs Old New O Origin env)
    (rest : List (TypedObs Old New O Origin env)) :
    mode (.selected (e :: rest)) = .batch := rfl

/-- Distinct zero witnesses still choose the same terminal mode. -/
theorem two_zero_witnesses_same_mode
    (z₁ z₂ : TypedObs Old New O Origin env)
    (h₁ : z₁.result = .zero) (h₂ : z₂.result = .zero) :
    mode (.inconsistent z₁ h₁) = mode (.inconsistent z₂ h₂) := rfl

theorem inconsistent_ne_selected
    (z : TypedObs Old New O Origin env) (hz : z.result = .zero)
    (entries : List (TypedObs Old New O Origin env)) :
    (RoundDecision.inconsistent z hz : RoundDecision (Origin := Origin) env) ≠
      .selected entries := by
  intro h
  cases h

end RoundDecision

/--
One round is either strict-priority local inconsistency or a nonzero selection.
The equivalence on `mode` rules out both `done` and `batch` whenever zero is
available.
-/
structure RoundSpec {O : Type} [DecidableEq O]
    {Origin : Pos sig.nBases → Type}
    {Old New : StableCtx sig} {env : ResolvedEnv (Old.append New) O}
    (available : ObsAvailability Old New O Origin env)
    (decision : RoundDecision (Origin := Origin) env) : Prop where
  inconsistent_iff :
    decision.mode = .inconsistent ↔ LocalZero available
  inconsistent_sound : ∀ e hzero,
    decision = .inconsistent e hzero → available e
  selected_spec : ∀ entries,
    decision = .selected entries → TypeSelectSpec available entries

namespace RoundSpec

variable {O : Type} [DecidableEq O]
  {Origin : Pos sig.nBases → Type}
  {Old New : StableCtx sig} {env : ResolvedEnv (Old.append New) O}
  {available : ObsAvailability Old New O Origin env}
  {decision : RoundDecision (Origin := Origin) env}

theorem localZero_iff_inconsistent (h : RoundSpec available decision) :
    LocalZero available ↔ decision.mode = .inconsistent :=
  h.inconsistent_iff.symm

theorem noLocalZero_of_done (h : RoundSpec available decision)
    (hm : decision.mode = .done) : ¬ LocalZero available := by
  intro hz
  have hi := h.localZero_iff_inconsistent.mp hz
  rw [hi] at hm
  cases hm

theorem noLocalZero_of_batch (h : RoundSpec available decision)
    (hm : decision.mode = .batch) : ¬ LocalZero available := by
  intro hz
  have hi := h.localZero_iff_inconsistent.mp hz
  rw [hi] at hm
  cases hm

theorem available_of_inconsistent (h : RoundSpec available decision)
    {e : TypedObs Old New O Origin env} {hzero : e.result = .zero}
    (hd : decision = .inconsistent e hzero) : available e :=
  h.inconsistent_sound e hzero hd

theorem spec_of_selected (h : RoundSpec available decision)
    {entries : List (TypedObs Old New O Origin env)}
    (hd : decision = .selected entries) : TypeSelectSpec available entries :=
  h.selected_spec entries hd

end RoundSpec

/-! ### Boundary fixtures -/

namespace TypeSelectionSpecFixtures

abbrev sig0 : Signature := ⟨0, #[]⟩
abbrev sig1 : Signature := ⟨1, #[]⟩
abbrev q : Fin sig1.nBases := ⟨0, Nat.zero_lt_one⟩
abbrev X : Pos sig1.nBases := .atom q
abbrev Origin1 (_ : Pos sig1.nBases) : Type := Nat
abbrev Origin0 (_ : Pos sig0.nBases) : Type := Nat
abbrev O2 : Type := Fin 2
def o0 : O2 := ⟨0, by decide⟩
def o1 : O2 := ⟨1, by decide⟩
abbrev K0 : DepSupport O2 := {o0}
abbrev K1 : DepSupport O2 := {o1}

theorem K0_ne_K1 : K0 ≠ K1 := by decide

/-! Same positive result, distinct actual supports. -/

abbrev TwoObsNew : StableCtx sig1 :=
  (StableCtx.empty.snoc (.neg (.shift X))).snoc (.neg (.shift X))

def twoObsEnv : ResolvedEnv TwoObsNew O2 :=
  ResolvedEnv.extend
    (ResolvedEnv.extend (ResolvedEnv.empty O2) K0) K1

def olderXNeutral : SNegNeu TwoObsNew (.shift X) :=
  .var (.there .here)

def newestXNeutral : SNegNeu TwoObsNew (.shift X) :=
  .var .here

def olderXScoped : ScopedObs (sig := sig1) .empty TwoObsNew X where
  neutral := olderXNeutral
  freshValid := rfl
  usesNew := by native_decide

def newestXScoped : ScopedObs (sig := sig1) .empty TwoObsNew X where
  neutral := newestXNeutral
  freshValid := rfl
  usesNew := by native_decide

def olderXEntry : TypedObs (sig := sig1) .empty TwoObsNew O2 Origin1 twoObsEnv where
  result := X
  obs := olderXScoped
  support := K0
  support_eq := rfl
  origin := 10

def newestXEntry : TypedObs (sig := sig1) .empty TwoObsNew O2 Origin1 twoObsEnv where
  result := X
  obs := newestXScoped
  support := K1
  support_eq := rfl
  origin := 11

theorem same_P_different_support :
    olderXEntry.result = newestXEntry.result ∧
      olderXEntry.support ≠ newestXEntry.support ∧
      olderXEntry ≠ newestXEntry := by
  refine ⟨rfl, K0_ne_K1, ?_⟩
  intro h
  have hs := congrArg
    (fun e : TypedObs (sig := sig1) .empty TwoObsNew O2 Origin1 twoObsEnv =>
      e.support) h
  exact K0_ne_K1 hs

def twoObsAvailable :
    ObsAvailability (sig := sig1) .empty TwoObsNew O2 Origin1 twoObsEnv :=
  fun e => e = olderXEntry ∨ e = newestXEntry

/-- One selected `X` covers both actual `(X,K)` observations. -/
theorem one_P_covers_two_supports :
    TypeSelectSpec twoObsAvailable [olderXEntry] := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    simp only [List.mem_singleton] at he
    exact Or.inl he
  · intro e he
    simp only [List.mem_singleton] at he
    subst e
    decide
  · intro e ha _
    right
    rcases ha with rfl | rfl
    · exact ⟨olderXEntry, by simp, rfl⟩
    · exact ⟨olderXEntry, by simp, rfl⟩

/-! Strong at one support blocks a baseline demand at another support. -/

abbrev StrongOld : StableCtx sig1 :=
  StableCtx.snoc .empty (.atom q)
abbrev StrongNew : StableCtx sig1 :=
  StableCtx.snoc .empty (.neg (.shift X))
def strongEnv : ResolvedEnv (StrongOld.append StrongNew) O2 :=
  ResolvedEnv.extend
    (ResolvedEnv.extend (ResolvedEnv.empty O2) K0) K1

def strongX : StrongPos (StrongOld.append StrongNew) X :=
  .atomVar (.there .here)

theorem strongX_at_K0 : SupportedStrong strongEnv X K0 := by
  exact ⟨⟨strongX, rfl⟩⟩

def strongCandidateScoped : ScopedObs StrongOld StrongNew X where
  neutral := .var .here
  freshValid := rfl
  usesNew := rfl

def strongCandidate :
    TypedObs StrongOld StrongNew O2 Origin1 strongEnv where
  result := X
  obs := strongCandidateScoped
  support := K1
  support_eq := rfl
  origin := 20

def strongCandidateAvailable :
    ObsAvailability StrongOld StrongNew O2 Origin1 strongEnv :=
  fun e => e = strongCandidate

/-- Exact support differs, but type-strong retrieval makes an empty baseline valid. -/
theorem strong_K0_blocks_baseline_demand_at_K1 :
    strongCandidate.support = K1 ∧
      TypeSelectSpec strongCandidateAvailable [] := by
  refine ⟨rfl, ?_⟩
  refine ⟨by simp, by simp, ?_⟩
  intro e ha _
  subst e
  exact Or.inl (TypeStrong.of_supported strongX_at_K0)

/-! `h : X → X+X`: the result type is already strong through `inl x`. -/

abbrev XX : Pos sig1.nBases := .sum X X
abbrev HNew : StableCtx sig1 :=
  (StableCtx.snoc .empty (.atom q)).snoc (.neg (.arr X (.shift XX)))
def hEnv : ResolvedEnv HNew O2 :=
  ResolvedEnv.extend (ResolvedEnv.extend (ResolvedEnv.empty O2) K0) K1
def hxNeutral : SNegNeu HNew (.shift XX) :=
  .app (.var .here) (.atom (.there .here))
def hxStrong : StrongPos HNew XX :=
  .inl (.atomVar (.there .here))

def hxScoped : ScopedObs (sig := sig1) .empty HNew XX where
  neutral := hxNeutral
  freshValid := rfl
  usesNew := by native_decide

def hxEntry : TypedObs (sig := sig1) .empty HNew O2 Origin1 hEnv where
  result := XX
  obs := hxScoped
  support := K1 ∪ K0
  support_eq := rfl
  origin := 30

def hxAvailable : ObsAvailability (sig := sig1) .empty HNew O2 Origin1 hEnv :=
  fun e => e = hxEntry

theorem hx_typeStrong_allows_empty_baseline :
    TypeStrong HNew XX ∧ TypeSelectSpec hxAvailable [] := by
  have hs : TypeStrong HNew XX := ⟨hxStrong⟩
  refine ⟨hs, ⟨by simp, by simp, ?_⟩⟩
  intro e ha _
  subst e
  exact Or.inl hs

/-! Recursive freshness cannot be replaced by a root-only `usesNew` test. -/

abbrev BadOld : StableCtx sig0 :=
  StableCtx.snoc .empty (.neg (.shift .zero))
abbrev BadNew : StableCtx sig0 :=
  StableCtx.snoc .empty
    (.neg (.arr (.shift (.shift (.shift .one))) (.shift .zero)))

def badNestedNeutral : SNegNeu (BadOld.append BadNew) (.shift .zero) :=
  match FreshnessFixtures.usesNew_but_nested_oldOnly_invalid_obs with
  | .one n => n

theorem badNestedNeutral_usesNew :
    badNestedNeutral.uses (newMask BadOld BadNew) = true := by
  native_decide

theorem badNestedNeutral_freshValid_false :
    badNestedNeutral.freshValid = false := by
  native_decide

theorem nested_invalid_cannot_form_scopedObs :
    ¬ ∃ o : ScopedObs BadOld BadNew (.zero : Pos 0),
      o.neutral = badNestedNeutral := by
  rintro ⟨o, ho⟩
  have hf := o.freshValid
  rw [ho, badNestedNeutral_freshValid_false] at hf
  cases hf

/-! Zero priority and proof irrelevance of the chosen contradiction witness. -/

abbrev ZeroNew : StableCtx sig0 :=
  (StableCtx.snoc .empty (.neg (.shift .zero))).snoc (.neg (.shift .zero))
def zeroEnv : ResolvedEnv ZeroNew O2 :=
  ResolvedEnv.extend (ResolvedEnv.extend (ResolvedEnv.empty O2) K0) K1

def olderZeroScoped : ScopedObs (sig := sig0) .empty ZeroNew .zero where
  neutral := .var (.there .here)
  freshValid := rfl
  usesNew := by native_decide

def newestZeroScoped : ScopedObs (sig := sig0) .empty ZeroNew .zero where
  neutral := .var .here
  freshValid := rfl
  usesNew := by native_decide

def olderZero : TypedObs (sig := sig0) .empty ZeroNew O2 Origin0 zeroEnv where
  result := .zero
  obs := olderZeroScoped
  support := K0
  support_eq := rfl
  origin := 40

def newestZero : TypedObs (sig := sig0) .empty ZeroNew O2 Origin0 zeroEnv where
  result := .zero
  obs := newestZeroScoped
  support := K1
  support_eq := rfl
  origin := 41

def zeroAvailable : ObsAvailability (sig := sig0) .empty ZeroNew O2 Origin0 zeroEnv :=
  fun e => e = olderZero ∨ e = newestZero

def zeroDecision : RoundDecision (sig := sig0) (O := O2)
    (Origin := Origin0) (Old := .empty) (New := ZeroNew) zeroEnv :=
  .inconsistent olderZero rfl

theorem zeroRoundSpec : RoundSpec zeroAvailable zeroDecision := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro _
      exact ⟨olderZero, Or.inl rfl, rfl⟩
    · intro _
      simp [zeroDecision, RoundDecision.mode]
  · intro e hzero hd
    simp [zeroDecision] at hd
    subst e
    exact Or.inl rfl
  · intro entries hd
    simp [zeroDecision] at hd

theorem zero_priority :
    LocalZero zeroAvailable ∧
      RoundDecision.mode zeroDecision = RoundMode.inconsistent :=
  ⟨zeroRoundSpec.inconsistent_iff.mp rfl, rfl⟩

theorem distinct_zero_witnesses_same_inconsistent_mode :
    olderZero ≠ newestZero ∧
      (RoundDecision.inconsistent olderZero rfl).mode =
        (RoundDecision.inconsistent newestZero rfl).mode := by
  constructor
  · intro h
    have hs := congrArg
      (fun e : TypedObs (sig := sig0) .empty ZeroNew O2 Origin0 zeroEnv =>
        e.support) h
    exact K0_ne_K1 hs
  · exact RoundDecision.two_zero_witnesses_same_mode _ _ rfl rfl

end TypeSelectionSpecFixtures

end Gimbal.Equality.Scherer
