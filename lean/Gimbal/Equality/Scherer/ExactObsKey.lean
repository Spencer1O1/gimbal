/-
  Exact keys for selected saturated observations.  The numeric code is a
  proved-injective structural pairing code; it is not a hash or site token.
-/

import Mathlib.Tactic.DeriveEncodable
import Gimbal.Equality.Scherer.PairStructuralCode

namespace Gimbal.Equality.Scherer

variable {sig : Signature}

/-! ### A small structural tree and its injective numeric code -/

inductive StructuralNatTree where
  | atom : Nat → StructuralNatTree
  | nil : StructuralNatTree
  | cons : StructuralNatTree → StructuralNatTree → StructuralNatTree
  | tagged : Nat → StructuralNatTree → StructuralNatTree

deriving instance DecidableEq for StructuralNatTree
deriving instance Repr for StructuralNatTree
deriving instance Encodable for StructuralNatTree

namespace StructuralNatTree

@[simp] def ofList : List StructuralNatTree → StructuralNatTree
  | [] => .nil
  | x :: xs => .cons x (ofList xs)

@[simp] def node (tag : Nat) (children : List StructuralNatTree) : StructuralNatTree :=
  .tagged tag (ofList children)

theorem ofList_injective : Function.Injective ofList := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys <;> simp at h ⊢
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp at h
          exact congrArg₂ List.cons h.1 (ih h.2)

def natCode : StructuralNatTree → Nat := Encodable.encode

theorem natCode_injective : Function.Injective natCode :=
  Encodable.encode_injective

end StructuralNatTree

def objectTree {n : Nat} : Object n → StructuralNatTree
  | .base q => .node 0 [.atom q.val]
  | .unit => .node 1 []
  | .never => .node 2 []
  | .prod A B => .node 3 [objectTree A, objectTree B]
  | .coprod A B => .node 4 [objectTree A, objectTree B]
  | .exp A B => .node 5 [objectTree A, objectTree B]

theorem objectTree_injective {n : Nat} : Function.Injective (@objectTree n) := by
  intro A
  induction A with
  | base q =>
      intro B h
      cases B <;> simp [objectTree] at h ⊢
      exact Fin.ext h
  | unit => intro B h; cases B <;> simp [objectTree] at h ⊢
  | never => intro B h; cases B <;> simp [objectTree] at h ⊢
  | prod A B ihA ihB =>
      intro C h
      cases C <;> simp [objectTree] at h ⊢
      rcases h with ⟨hA, hB⟩
      exact ⟨ihA hA, ihB hB⟩
  | coprod A B ihA ihB =>
      intro C h
      cases C <;> simp [objectTree] at h ⊢
      rcases h with ⟨hA, hB⟩
      exact ⟨ihA hA, ihB hB⟩
  | exp A B ihA ihB =>
      intro C h
      cases C <;> simp [objectTree] at h ⊢
      rcases h with ⟨hA, hB⟩
      exact ⟨ihA hA, ihB hB⟩

mutual

def posTree {n : Nat} : Pos n → StructuralNatTree
  | .atom q => .node 10 [.atom q.val]
  | .zero => .node 11 []
  | .sum A B => .node 12 [posTree A, posTree B]
  | .shift N => .node 13 [negTree N]

def negTree {n : Nat} : Neg n → StructuralNatTree
  | .one => .node 14 []
  | .prod A B => .node 15 [negTree A, negTree B]
  | .arr A B => .node 16 [posTree A, negTree B]
  | .shift P => .node 17 [posTree P]

end

def originKindTree : OriginKind sig → StructuralNatTree
  | .generator q => .node 20 [.atom q.val]
  | .root slot => .node 21 [.atom slot]
  | .stable slot => .node 22 [.atom slot]
  | .store slot source => .node 23 [.atom slot, .atom source]
  | .observation site entry => .node 24 [.atom site, .atom entry]
  | .split parent right => .node 25 [.atom parent, .atom right.toNat]

theorem originKindTree_injective :
    Function.Injective (@originKindTree sig) := by
  intro a b h
  cases a <;> cases b <;> simp [originKindTree] at h ⊢
  · exact Fin.ext h
  · cases h
    rfl
  · cases h
    rfl
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  · rcases h with ⟨rfl, h⟩
    cases ‹Bool› <;> cases ‹Bool› <;> simp_all
def originTree (o : Origin sig) : StructuralNatTree :=
  .node 30 [objectTree o.ty, .atom o.id, .atom o.introRank,
    originKindTree o.kind]

theorem originTree_injective : Function.Injective (@originTree sig) := by
  intro x y h
  cases x with
  | mk xty xid xrank xkind =>
      cases y with
      | mk yty yid yrank ykind =>
          simp [originTree] at h
          rcases h with ⟨hty, rfl, rfl, hkind⟩
          cases objectTree_injective hty
          cases originKindTree_injective hkind
          rfl

theorem originTree_list_injective :
    Function.Injective (List.map (@originTree sig)) := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys <;> simp at h ⊢
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp at h
          exact congrArg₂ List.cons (originTree_injective h.1) (ih h.2)

def ctxTree : Ctx sig → StructuralNatTree
  | .empty => .node 40 []
  | .snoc Γ A => .node 41 [ctxTree Γ, objectTree A]

def pendingTree : Pending sig → StructuralNatTree
  | .empty => .node 42 []
  | .cons P ps => .node 43 [posTree P, pendingTree ps]

def goalTree : Goal sig.nBases → StructuralNatTree
  | .pos P => .node 44 [posTree P]
  | .neg N => .node 45 [negTree N]

def varIndex : Var Γ A → Nat
  | .here => 0
  | .there x => varIndex x + 1

def CanonRef.toStructuralNatTree {R : AliasResolver sig} {Δ : Ctx sig} {A} :
    CanonRef R Δ A → StructuralNatTree
  | .bound x => .node 50 [objectTree A, .atom (varIndex x)]
  | .free x => .node 51 [objectTree A, originTree x.origin.raw]

/-! ### Structural serialization of selected codes -/

mutual

def SNegCode.toStructuralNatTree {R : AliasResolver sig} {Δ : Ctx sig} {N} :
    SNegCode R Δ N → StructuralNatTree
  | .var x => .node 60 [ctxTree Δ, negTree N,
      x.toStructuralNatTree]
  | .fst n => .node 61 [ctxTree Δ, negTree N,
      n.toStructuralNatTree]
  | .snd n => .node 62 [ctxTree Δ, negTree N,
      n.toStructuralNatTree]
  | .app n p => .node 63 [ctxTree Δ, negTree N,
      n.toStructuralNatTree, p.toStructuralNatTree]

def SPosCode.toStructuralNatTree {R : AliasResolver sig} {Δ : Ctx sig} {P} :
    SPosCode R Δ P → StructuralNatTree
  | .atom x => .node 64 [ctxTree Δ, posTree P,
      x.toStructuralNatTree]
  | .inl p => .node 65 [ctxTree Δ, posTree P,
      p.toStructuralNatTree]
  | .inr p => .node 66 [ctxTree Δ, posTree P,
      p.toStructuralNatTree]
  | .shift t => .node 67 [ctxTree Δ, posTree P,
      t.toStructuralNatTree]

def BranchCode.toStructuralNatTree {R : AliasResolver sig} {Δ : Ctx sig}
    {ps : Pending sig} {G} : BranchCode R Δ ps G → StructuralNatTree
  | .dead => .node 68 [ctxTree Δ, pendingTree ps, goalTree G]
  | .caseSum l r => .node 69 [ctxTree Δ, pendingTree ps, goalTree G,
      l.toStructuralNatTree, r.toStructuralNatTree]
  | .abort => .node 70 [ctxTree Δ, pendingTree ps, goalTree G]
  | .storeAtom t => .node 71 [ctxTree Δ, pendingTree ps, goalTree G,
      t.toStructuralNatTree]
  | .storeShift t => .node 72 [ctxTree Δ, pendingTree ps, goalTree G,
      t.toStructuralNatTree]
  | .unit => .node 73 [ctxTree Δ, goalTree G]
  | .pair l r => .node 74 [ctxTree Δ, goalTree G,
      l.toStructuralNatTree, r.toStructuralNatTree]
  | .lam t => .node 75 [ctxTree Δ, goalTree G,
      t.toStructuralNatTree]
  | .satShift s => .node 76 [ctxTree Δ, goalTree G,
      s.toStructuralNatTree]
  | .satPos s => .node 77 [ctxTree Δ, goalTree G,
      s.toStructuralNatTree]

def SatCode.toStructuralNatTree {R : AliasResolver sig} {Δ : Ctx sig} {P} :
    SatCode R Δ P → StructuralNatTree
  | .inconsistent => .node 78 [ctxTree Δ, posTree P]
  | .done p => .node 79 [ctxTree Δ, posTree P,
      p.toStructuralNatTree]
  | .batch obs body => .node 80 [ctxTree Δ, posTree P,
      obs.toStructuralNatTree, body.toStructuralNatTree]

def BatchCode.toStructuralNatTree {R : AliasResolver sig} {Δ : Ctx sig}
    {selected : Pending sig} : BatchCode R Δ selected → StructuralNatTree
  | .one n => .node 81 [ctxTree Δ, pendingTree selected,
      n.toStructuralNatTree]
  | .cons n rest => .node 82 [ctxTree Δ, pendingTree selected,
      n.toStructuralNatTree, rest.toStructuralNatTree]

end

/-! ### Resolver-owned exact keys -/

/-- A structural observation tree, its exact free dependencies, and a typed
selected-code witness.  The witness is proof-only; equality is tree + deps. -/
structure ExactObsKey (R : AliasResolver sig) (A : Object sig.nBases) where
  tree : StructuralNatTree
  deps : List (Origin sig)
  realizes : ∃ (Q : Pos sig.nBases) (code : SNegCode R .empty (.shift Q)),
    Q.erase = A ∧ tree = code.toStructuralNatTree ∧ deps = code.freeDeps

namespace ExactObsKey

@[ext] theorem ext {R : AliasResolver sig} {A : Object sig.nBases}
    {x y : ExactObsKey R A} (htree : x.tree = y.tree)
    (hdeps : x.deps = y.deps) : x = y := by
  cases x
  cases y
  cases htree
  cases hdeps
  rfl

def ofStructural (code : SNegCode R .empty (.shift Q)) :
    ExactObsKey R Q.erase where
  tree := code.toStructuralNatTree
  deps := code.freeDeps
  realizes := ⟨Q, code, rfl, rfl, rfl⟩

def keyTree {A : Object sig.nBases} (key : ExactObsKey R A) :
    StructuralNatTree :=
  .node 90 [objectTree A, key.tree, .node 91 (key.deps.map originTree)]

def code {A : Object sig.nBases} (key : ExactObsKey R A) : Nat :=
  key.keyTree.natCode

theorem keyTree_injective {R : AliasResolver sig} {A : Object sig.nBases} :
    Function.Injective (@keyTree sig R A) := by
  intro x y h
  simp [keyTree] at h
  apply ExactObsKey.ext h.1
  exact originTree_list_injective (StructuralNatTree.ofList_injective h.2)

theorem code_injective {R : AliasResolver sig} {A : Object sig.nBases} :
    Function.Injective (@code sig R A) := by
  intro x y h
  exact keyTree_injective (StructuralNatTree.natCode_injective h)

theorem ofStructural_eq_iff (left right : SNegCode R .empty (.shift Q)) :
    ofStructural left = ofStructural right ↔
      left.toStructuralNatTree = right.toStructuralNatTree ∧
        left.freeDeps = right.freeDeps := by
  constructor
  · intro h
    exact ⟨congrArg tree h, congrArg deps h⟩
  · rintro ⟨htree, hdeps⟩
    exact ExactObsKey.ext htree hdeps

theorem deps_terminal (key : ExactObsKey R A) (o : Origin sig)
    (ho : o ∈ key.deps) : R.target o = none := by
  obtain ⟨Q, c, _, _, hdeps⟩ := key.realizes
  rw [hdeps] at ho
  exact c.freeDeps_terminal o ho

theorem ofStructural_scoped (code : SNegCode R .empty (.shift Q))
    (hcode : code.Scoped pre) :
    ∀ o ∈ (ofStructural code).deps, pre.Contains o := by
  intro o ho
  exact hcode o ho

def ofNeutral (supply : BatchResultSupply R) (E : OriginAssignment R Γ)
    (n : SNegNeu Γ (.shift Q)) : ExactObsKey R Q.erase :=
  ofStructural (n.toStructuralCode supply (CodeOriginAssignment.ofOrigin E))

theorem ofNeutral_eq_iff (leftSupply rightSupply : BatchResultSupply R)
    (leftE : OriginAssignment R Γleft) (rightE : OriginAssignment R Γright)
    (left : SNegNeu Γleft (.shift Q)) (right : SNegNeu Γright (.shift Q)) :
    ofNeutral leftSupply leftE left = ofNeutral rightSupply rightE right ↔
      let lc := left.toStructuralCode leftSupply
        (CodeOriginAssignment.ofOrigin leftE)
      let rc := right.toStructuralCode rightSupply
        (CodeOriginAssignment.ofOrigin rightE)
      lc.toStructuralNatTree = rc.toStructuralNatTree ∧ lc.freeDeps = rc.freeDeps :=
  ofStructural_eq_iff _ _

theorem ofNeutral_scoped (supply : BatchResultSupply R)
    (E : OriginAssignment R Γ) (n : SNegNeu Γ (.shift Q))
    (hE : (CodeOriginAssignment.ofOrigin E).Scoped pre) :
    ∀ o ∈ (ofNeutral supply E n).deps, pre.Contains o :=
  ofStructural_scoped _ (n.toStructuralCode_scoped supply
    (CodeOriginAssignment.ofOrigin E) hE)

end ExactObsKey

/-- The exact observation family consumed by typed traces. -/
def exactObsKeys (R : AliasResolver sig) : TypedKeyFamily sig where
  Key := ExactObsKey R
  code := ExactObsKey.code
  code_injective := by
    intro A x y h
    exact ExactObsKey.code_injective h
  deps := ExactObsKey.deps

theorem exactObsKeys_deps_terminal (key : ExactObsKey R A)
    (o : Origin sig) (ho : o ∈ (exactObsKeys R).deps key) :
    R.target o = none := by
  exact key.deps_terminal o ho

/-! ### Ordered literal batch keys -/

inductive OrderedBatchKeys (R : AliasResolver sig) : Pending sig → Type where
  | one {Q} : ExactObsKey R Q.erase → OrderedBatchKeys R (.cons Q .empty)
  | cons {Q ps} : ExactObsKey R Q.erase → OrderedBatchKeys R ps →
      OrderedBatchKeys R (.cons Q ps)

namespace OrderedBatchKeys

def length : OrderedBatchKeys R selected → Nat
  | .one _ => 1
  | .cons _ rest => rest.length + 1

def tree : OrderedBatchKeys R selected → StructuralNatTree
  | .one key => .node 100 [key.keyTree]
  | .cons key rest => .node 101 [key.keyTree, rest.tree]

def code (keys : OrderedBatchKeys R selected) : Nat := keys.tree.natCode

end OrderedBatchKeys

def NonemptyBatchObs.toExactKeys (supply : BatchResultSupply R)
    (E : OriginAssignment R Γ) :
    NonemptyBatchObs Γ selected → OrderedBatchKeys R selected
  | .one n => .one (ExactObsKey.ofNeutral supply E n)
  | .cons n rest => .cons (ExactObsKey.ofNeutral supply E n)
      (rest.toExactKeys supply E)

theorem NonemptyBatchObs.toExactKeys_same (supply : BatchResultSupply R)
    (E : OriginAssignment R Γ) (obs : NonemptyBatchObs Γ selected) :
    obs.toExactKeys supply E = obs.toExactKeys supply E := rfl

/-! ### Observation-result quotient bridge -/

theorem TypedTrace.WellFormed.sameExactKey_resultEquivalent
    {R : AliasResolver sig} {T : TypedTrace (exactObsKeys R)}
    (hT : T.WellFormed) {A : Object sig.nBases} (leftSite leftSupport : Nat)
    (leftPre : OriginScope) (key : ExactObsKey R A) (left : TypedOrigin sig A)
    (rightSite rightSupport : Nat) (rightPre : OriginScope)
    (right : TypedOrigin sig A)
    (hleft : TraceStep.observe leftSite leftSupport leftPre key left ∈ T.steps)
    (hright : TraceStep.observe rightSite rightSupport rightPre key right ∈ T.steps) :
    T.resolver.Equivalent left.raw right.raw := by
  obtain ⟨x, y, hx, hy, heq⟩ := hT.sameObservation_resultEquivalent hleft hright
    (key := (A, ExactObsKey.code key)) rfl rfl
  simp [TraceStep.result?] at hx hy
  subst x
  subst y
  exact heq

theorem TypedTrace.WellFormed.exactKey_eq_of_resultEquivalent
    {R : AliasResolver sig} {T : TypedTrace (exactObsKeys R)}
    (hT : T.WellFormed) {A : Object sig.nBases} (leftSite leftSupport : Nat)
    (leftPre : OriginScope) (leftKey : ExactObsKey R A)
    (left : TypedOrigin sig A) (rightSite rightSupport : Nat)
    (rightPre : OriginScope) (rightKey : ExactObsKey R A)
    (right : TypedOrigin sig A)
    (hleft : TraceStep.observe leftSite leftSupport leftPre leftKey left ∈ T.steps)
    (hright : TraceStep.observe rightSite rightSupport rightPre rightKey right ∈ T.steps)
    (hresult : T.resolver.Equivalent left.raw right.raw) : leftKey = rightKey := by
  have hsig := hT.observationKey_eq_of_resultEquivalent hleft hright
    (ks := (A, ExactObsKey.code leftKey)) (kt := (A, ExactObsKey.code rightKey))
    rfl rfl ⟨left.raw, right.raw, rfl, rfl, hresult⟩
  have hcode : ExactObsKey.code leftKey = ExactObsKey.code rightKey :=
    (Prod.mk.inj hsig).2
  exact ExactObsKey.code_injective hcode

/-! ### Adversarial fixtures -/

namespace ExactObsKeyFixtures

open PairTraceFixtures
open PairStructuralCodeFixtures

def aliasStoreKey : ExactObsKey chainResolver P.erase :=
  ExactObsKey.ofNeutral (supply chainResolver) storeAssignment aliasNeu

def aliasRootKey : ExactObsKey chainResolver P.erase :=
  ExactObsKey.ofNeutral (supply chainResolver) rootAssignment aliasNeu

/-- Alias chains are normalized before exact-key construction. -/
theorem alias_chain_same_key : aliasStoreKey = aliasRootKey := by
  apply ExactObsKey.ext
  · exact congrArg SNegCode.toStructuralNatTree alias_chain_normalizes_equal
  · exact congrArg SNegCode.freeDeps alias_chain_normalizes_equal

def newestKey : ExactObsKey idR P.erase :=
  ExactObsKey.ofNeutral (supply idR) obsAssignment newestObs

def olderKey : ExactObsKey idR P.erase :=
  ExactObsKey.ofNeutral (supply idR) obsAssignment olderObs

/-- Result type alone does not identify a neutral source. -/
theorem newest_older_key_distinct : newestKey ≠ olderKey := by
  intro h
  have hdeps := congrArg ExactObsKey.deps h
  change [refB.origin.raw] = [refA.origin.raw] at hdeps
  have hraw := List.cons.inj hdeps |>.1
  apply refA_ne_refB
  apply ResolvedRef.ext
  apply TypedOrigin.ext
  exact hraw.symm

def prodRef : ResolvedRef idR SameProd.erase := ResolvedRef.of idR prodOrigin

def fstClosedCode : SNegCode idR .empty ShiftP := .fst (.var (.free prodRef))
def sndClosedCode : SNegCode idR .empty ShiftP := .snd (.var (.free prodRef))

theorem fst_normalizes_closed :
    (SNegNeu.fst prodNeu).toStructuralCode (supply idR)
      (CodeOriginAssignment.ofOrigin prodAssignment) = fstClosedCode := rfl

theorem snd_normalizes_closed :
    (SNegNeu.snd prodNeu).toStructuralCode (supply idR)
      (CodeOriginAssignment.ofOrigin prodAssignment) = sndClosedCode := rfl

def fstKey : ExactObsKey idR ShiftP.erase :=
  ExactObsKey.ofStructural fstClosedCode

def sndKey : ExactObsKey idR ShiftP.erase :=
  ExactObsKey.ofStructural sndClosedCode

theorem fst_snd_key_distinct : fstKey ≠ sndKey := by
  intro h
  have htree := congrArg ExactObsKey.tree h
  simp [fstKey, sndKey, fstClosedCode, sndClosedCode, ExactObsKey.ofStructural,
    SNegCode.toStructuralNatTree] at htree

def fnRef : ResolvedRef idR FnN.erase := ResolvedRef.of idR fnOrigin

def appXClosedCode : SNegCode idR .empty ShiftP :=
  .app (.var (.free fnRef)) (.atom (.free refA))

def appYClosedCode : SNegCode idR .empty ShiftP :=
  .app (.var (.free fnRef)) (.atom (.free refB))

theorem appX_normalizes_closed :
    appX.toStructuralCode (supply idR)
      (CodeOriginAssignment.ofOrigin appAssignment) = appXClosedCode := rfl

theorem appY_normalizes_closed :
    appY.toStructuralCode (supply idR)
      (CodeOriginAssignment.ofOrigin appAssignment) = appYClosedCode := rfl

def appXKey : ExactObsKey idR ShiftP.erase := ExactObsKey.ofStructural appXClosedCode
def appYKey : ExactObsKey idR ShiftP.erase := ExactObsKey.ofStructural appYClosedCode

theorem app_argument_key_distinct : appXKey ≠ appYKey := by
  intro h
  have hdeps := congrArg ExactObsKey.deps h
  change [fnRef.origin.raw, refA.origin.raw] =
    [fnRef.origin.raw, refB.origin.raw] at hdeps
  have hraw := (List.cons.inj (List.cons.inj hdeps).2).1
  apply refA_ne_refB
  apply ResolvedRef.ext
  apply TypedOrigin.ext
  exact hraw

abbrev SimpleCtx : StableCtx TwoGenSig :=
  (StableCtx.empty : StableCtx TwoGenSig).snoc (.neg ShiftP)

def simpleAssignment : OriginAssignment duplicateResolver SimpleCtx :=
  (OriginAssignment.empty duplicateResolver).snoc (S := .neg ShiftP)
    (ResolvedRef.of duplicateResolver (asShiftOrigin atom0))

def simpleNeu : SNegNeu SimpleCtx ShiftP := .var .here

def commonKey : ExactObsKey duplicateResolver P.erase :=
  ExactObsKey.ofNeutral (supply duplicateResolver) simpleAssignment simpleNeu

/-- Support and observation sites are absent from exact-key identity; equal
keys force their result sites into one resolver class in a well-formed trace. -/
theorem same_key_different_support_sites_alias_result :
    commonKey = commonKey ∧ (3 : Nat) ≠ 4 ∧ (7 : Nat) ≠ 9 ∧
      duplicateResolver.Equivalent obsA.raw obsADuplicate.raw := by
  refine ⟨rfl, by decide, by decide, ?_⟩
  exact duplicate_identical_keys_share_representative

/-- Distinct exact keys of one result type remain distinct sources under the
identity resolver. -/
theorem different_keys_same_type_do_not_alias :
    newestKey ≠ olderKey ∧
      idR.resolve obsA.raw ≠ idR.resolve obsB.raw := by
  refine ⟨newest_older_key_distinct, ?_⟩
  rw [AliasResolver.resolve_eq_self_of_target_eq_none,
    AliasResolver.resolve_eq_self_of_target_eq_none]
  · decide
  · rfl
  · rfl

def keysAB := batchAB.toExactKeys (supply idR) obsAssignment
def keysBA := batchBA.toExactKeys (supply idR) obsAssignment
def batchAA : NonemptyBatchObs ObsCtx (.cons P (.cons P .empty)) :=
  .cons newestObs (.one newestObs)
def keysAA := batchAA.toExactKeys (supply idR) obsAssignment
def keysA := batchA.toExactKeys (supply idR) obsAssignment

/-- Ordered package codes retain literal batch order. -/
theorem batch_order_code_distinct : keysAB.code ≠ keysBA.code := by
  intro h
  have htree := StructuralNatTree.natCode_injective h
  simp [keysAB, keysBA, batchAB, batchBA, NonemptyBatchObs.toExactKeys,
    OrderedBatchKeys.tree] at htree
  exact newest_older_key_distinct (ExactObsKey.keyTree_injective htree.1)

/-- Ordered package codes retain multiplicity, not merely membership. -/
theorem duplicate_singleton_code_distinct : keysAA.code ≠ keysA.code := by
  intro h
  have htree := StructuralNatTree.natCode_injective h
  simp [keysAA, keysA, batchAA, batchA, NonemptyBatchObs.toExactKeys,
    OrderedBatchKeys.tree] at htree

end ExactObsKeyFixtures

end Gimbal.Equality.Scherer
