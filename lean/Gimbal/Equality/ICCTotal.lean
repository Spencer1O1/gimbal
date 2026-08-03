/-
  Totality of ordered-phase encoding on the valid fragment (Milestone 8F/E).

  `EncodeTotal` asks that every `ValidEncodeFragment` term is `EncodableICC`
  under `OriginEnv.ofHyps`. This file accumulates measure/adequacy lemmas.
-/

import Gimbal.Equality.ICCEncode
import Gimbal.Equality.ICCFragment

namespace Gimbal
namespace Equality

variable {sig : Signature}

/-- Focused pos/neg residues encode under `.focus`. -/
theorem encodeICCGo_foc_pos {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (p : PosNeu Γ A)
    (hforce : forcedRule ws A = .focus) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.foc (.pos (.done p))) =
      some (.foc (.pos p)) := by
  simp [encodeICCGo, hforce, encodeFocGo]

theorem encodeICCGo_foc_neg {Γ : Ctx sig} {A : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (n : NegNeu Γ A)
    (hforce : forcedRule ws A = .focus) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.foc (.neg (.done n))) =
      some (.foc (.neg n)) := by
  simp [encodeICCGo, hforce, encodeFocGo]

theorem forcedRule_cons_base_moveStable (e : PosEntry sig) (ws : List (PosEntry sig))
    {b : Fin sig.nBases} (hty : e.ty = .base b) (goal : Object sig.nBases) :
    forcedRule (e :: ws) goal = .moveStable e := by
  simp [forcedRule, hty]

/--
Right-product encodes as a pair of component codes when peel succeeds.
-/
theorem encodeICCGo_pair_rightProd {Γ : Ctx sig} {L R : Object sig.nBases}
    (fuel : Nat) (ws : List (PosEntry sig)) (ε : OriginEnv Γ)
    (domNest obsSlot : Nat) (t : InvTm Γ L) (u : InvTm Γ R)
    (hforce : forcedRule ws (.prod L R) = .rightProd L R) :
    encodeICCGo (fuel + 1) ws ε domNest obsSlot (.pair t u) =
      match encodeICCGo fuel ws ε domNest obsSlot t,
            encodeICCGo fuel ws ε domNest obsSlot u with
      | some c₁, some c₂ => some (.pair c₁ c₂)
      | _, _ => none := by
  simp [encodeICCGo, hforce, peelPair]
  rfl

theorem encodable_unit_nilWorklist {Γ : Ctx sig} (ε : OriginEnv Γ)
    (hws : OriginEnv.posWorklist ε = []) :
    EncodableICC ε (.unit (Γ := Γ)) := by
  simp only [EncodableICC, encodeICC_unit_of_nilWorklist ε hws, Option.isSome_some]

theorem encodable_abort_leftNever {Γ : Ctx sig} {A : Object sig.nBases}
    (ε : OriginEnv Γ) (e : PosEntry sig) (ws : List (PosEntry sig))
    (n : NegNeu Γ .never)
    (hws : OriginEnv.posWorklist ε = e :: ws) (hty : e.ty = .never) :
    EncodableICC ε (.abort (A := A) n) := by
  simp only [EncodableICC, encodeICC_abort_leftNever ε e ws n hws hty,
    Option.isSome_some]

/--
Base cases toward `EncodeTotal`: unit under empty worklist, abort under
forced `leftNever`. Pair/lam/case/letPos follow forced-rule recursion once
measure adequacy is in place.
-/
theorem encodeTotal_base_unit_abort :
    (∀ {Γ : Ctx sig} (ε : OriginEnv Γ),
      OriginEnv.posWorklist ε = [] →
        EncodableICC ε (.unit (Γ := Γ))) ∧
    (∀ {Γ : Ctx sig} {A : Object sig.nBases} (ε : OriginEnv Γ)
      (e : PosEntry sig) (ws : List (PosEntry sig)) (n : NegNeu Γ .never),
      OriginEnv.posWorklist ε = e :: ws → e.ty = .never →
        EncodableICC ε (.abort (A := A) n)) :=
  ⟨fun ε h => encodable_unit_nilWorklist ε h,
    fun ε e ws n hws hty => encodable_abort_leftNever ε e ws n hws hty⟩

end Equality
end Gimbal
