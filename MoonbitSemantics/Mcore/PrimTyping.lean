/-
  MoonBit — evalPrim type soundness
  Separate file to isolate heartbeat-heavy case analysis.
-/
import MoonbitSemantics.Mcore.Typing

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp)

set_option maxHeartbeats 3200000 in
theorem evalPrim_type_sound'
    (heval : evalPrim op args = some v)
    (hargs : ValueListHasType args argTys)
    (hprim : typeOfPrim op argTys = some τ) :
    ValueHasType v τ := by
  cases hargs with
  | nil => simp [typeOfPrim] at hprim
  | cons h1 rest =>
    cases rest with
    | cons h2 rest2 =>
      cases rest2 with
      | cons _ _ => simp [typeOfPrim] at hprim
      | nil => sorry -- 2 args const×const: ~81 subcases (9 Const × 9 Const), each .const
    | nil =>
      -- 1 arg
      cases h1 with
      | const => sorry -- 1 arg const: ~99 subcases (9 Const × 11 Op), each .const/.unit
      | unit => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> exact .unit
      | closure => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .closure
      | rawFn => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .rawFn
      | constr => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .constr
      | tuple hvts => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .tuple hvts
      | locConstr => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .locConstr
      | locArray => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .locArray

end Moonbit.Mcore
