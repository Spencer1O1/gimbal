/-
  Counting-only bridge from old abstract forests to normalized queries.

  The finite normal-query foundation intentionally does not import the legacy
  forest stack. This oracle module keeps the existing abstract-derivation
  bound available to proof-only clients.
-/

import Gimbal.Equality.Scherer.SearchNormalQuery
import Gimbal.Equality.Scherer.SearchForestCore

namespace Gimbal.Equality.Scherer

/-! ### Branch-simple counting by normalized queries -/

namespace AbstractDeriv

variable {K Q : Type} {sys : AlternativeSystem K}

/-- Maximum root-to-leaf node count of an abstract derivation. -/
def depth {k : K} : AbstractDeriv sys k → Nat
  | .choose _a children =>
      1 + Finset.univ.sup fun i => depth (children i)

@[simp] theorem depth_choose {k : K} (a : sys.Alt k)
    (children : ∀ i : Fin (sys.deps a).length,
      AbstractDeriv sys ((sys.deps a).get ⟨i.val, i.isLt⟩)) :
    depth (.choose a children) =
      1 + Finset.univ.sup fun i => depth (children i) := rfl

/-- Path-local simplicity after projecting exact keys to normalized queries. -/
inductive AvoidingBy (norm : K → Q) :
    ∀ {k : K}, List Q → AbstractDeriv sys k → Prop
  | mk {k : K} {a : sys.Alt k}
      {children : ∀ i : Fin (sys.deps a).length,
        AbstractDeriv sys ((sys.deps a).get ⟨i.val, i.isLt⟩)}
      {forbidden : List Q}
      (hroot : norm k ∉ forbidden)
      (hchildren : ∀ i, AvoidingBy norm (norm k :: forbidden) (children i)) :
      AvoidingBy norm forbidden (.choose a children)

/-- No normalized query repeats on a root-to-leaf branch. -/
def BranchSimpleBy (norm : K → Q) {k : K} (d : AbstractDeriv sys k) : Prop :=
  AvoidingBy norm [] d

theorem depth_add_forbidden_le_enum [DecidableEq Q]
    (enum : CanonicalEnum Q) (norm : K → Q)
    {k : K} {d : AbstractDeriv sys k} {forbidden : List Q}
    (h : AvoidingBy norm forbidden d) (hforbidden : forbidden.Nodup) :
    d.depth + forbidden.length ≤ enum.elems.length := by
  induction h with
  | @mk k a children forbidden hroot hchildren ih =>
      have hcons : (norm k :: forbidden).Nodup :=
        List.nodup_cons.mpr ⟨hroot, hforbidden⟩
      have hcount : forbidden.length + 1 ≤ enum.elems.length := by
        simpa [List.length_cons, Nat.add_comm] using enum.nodup_length_le hcons
      have hsup :
          Finset.univ.sup (fun i => depth (children i)) +
              (forbidden.length + 1) ≤ enum.elems.length := by
        have hle : Finset.univ.sup (fun i => depth (children i)) ≤
            enum.elems.length - (forbidden.length + 1) := by
          refine Finset.sup_le ?_
          intro i _hi
          have hi := ih i hcons
          simp only [List.length_cons] at hi
          omega
        omega
      simpa [depth_choose, List.length_cons, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hsup

/-- Generic finite-carrier counting theorem for normalized branch simplicity. -/
theorem depth_le_enum_length [DecidableEq Q]
    (enum : CanonicalEnum Q) (norm : K → Q)
    {k : K} {d : AbstractDeriv sys k}
    (h : BranchSimpleBy norm d) : d.depth ≤ enum.elems.length := by
  have hle := depth_add_forbidden_le_enum enum norm h (by simp)
  simpa using hle

/--
Specialized normalized-query depth bound. This applies only after proving
`BranchSimpleBy` for the full projection (including `UseSig`) while any future
selection-work component is fixed or weakening-compatible. In particular, a
later selector still owes `workWeakening`: admissibility with fewer remaining
optional tokens must persist after enlarging that token set. No selected-trace
bound is inferred here.
-/
theorem depth_le_normalQueryBound {U : SearchUniverse sig} {O : Type}
    [DecidableEq O] (carriers : QueryCarrierEnum U O)
    (norm : K → NormalQuery U O) {k : K} {d : AbstractDeriv sys k}
    (h : BranchSimpleBy norm d) :
    d.depth ≤ normalQueryBound carriers := by
  rw [← normalQueryEnum_length carriers]
  exact depth_le_enum_length (normalQueryEnum carriers) norm h

end AbstractDeriv

end Gimbal.Equality.Scherer
