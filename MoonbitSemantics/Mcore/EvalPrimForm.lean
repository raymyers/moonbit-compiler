/-
  Proves that evalPrim for non-identity ops always returns const or unit.
-/
import MoonbitSemantics.Mcore.PrimTyping

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp)

theorem evalPrim_non_identity_constOrUnit (hop : op ≠ .identity)
    (heval : evalPrim op argVals = some v) :
    (∃ c, v = .const c) ∨ v = .unit := by
  unfold evalPrim at heval
  split at heval <;> simp_all <;> (subst heval; exact Or.inl ⟨_, rfl⟩)

end Moonbit.Mcore
