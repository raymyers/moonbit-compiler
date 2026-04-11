/-
  MoonBit — evalPrim type soundness
-/
import MoonbitSemantics.Mcore.Typing

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp)

-- Per-Const lemma for 1-arg const case
private theorem ep1_bool (h : evalPrim op [.const (.bool b)] = some v)
    (hp : typeOfPrim op [.bool] = some τ) : ValueHasType v τ := by
  cases op <;> simp_all [evalPrim, typeOfPrim, typeOfConst, arithResultType] <;> subst_vars <;> first | exact .const | exact .unit
private theorem ep1_int (h : evalPrim op [.const (.int n)] = some v)
    (hp : typeOfPrim op [.int] = some τ) : ValueHasType v τ := by
  cases op <;> simp_all [evalPrim, typeOfPrim, typeOfConst, arithResultType] <;> subst_vars <;> first | exact .const | exact .unit
private theorem ep1_int64 (h : evalPrim op [.const (.int64 n)] = some v)
    (hp : typeOfPrim op [.int64] = some τ) : ValueHasType v τ := by
  cases op <;> simp_all [evalPrim, typeOfPrim, typeOfConst, arithResultType] <;> subst_vars <;> first | exact .const | exact .unit
private theorem ep1_float (h : evalPrim op [.const (.float n)] = some v)
    (hp : typeOfPrim op [.float] = some τ) : ValueHasType v τ := by
  cases op <;> simp_all [evalPrim, typeOfPrim, typeOfConst, arithResultType] <;> subst_vars <;> first | exact .const | exact .unit
private theorem ep1_double (h : evalPrim op [.const (.double n)] = some v)
    (hp : typeOfPrim op [.double] = some τ) : ValueHasType v τ := by
  cases op <;> simp_all [evalPrim, typeOfPrim, typeOfConst, arithResultType] <;> subst_vars <;> first | exact .const | exact .unit
private theorem ep1_string (h : evalPrim op [.const (.string s)] = some v)
    (hp : typeOfPrim op [.string] = some τ) : ValueHasType v τ := by
  cases op <;> simp_all [evalPrim, typeOfPrim, typeOfConst, arithResultType] <;> subst_vars <;> first | exact .const | exact .unit
private theorem ep1_char (h : evalPrim op [.const (.char c)] = some v)
    (hp : typeOfPrim op [.char] = some τ) : ValueHasType v τ := by
  cases op <;> simp_all [evalPrim, typeOfPrim, typeOfConst, arithResultType] <;> subst_vars <;> first | exact .const | exact .unit
private theorem ep1_byte (h : evalPrim op [.const (.byte b)] = some v)
    (hp : typeOfPrim op [.byte] = some τ) : ValueHasType v τ := by
  cases op <;> simp_all [evalPrim, typeOfPrim, typeOfConst, arithResultType] <;> subst_vars <;> first | exact .const | exact .unit
private theorem ep1_unit' (h : evalPrim op [.const .unit] = some v)
    (hp : typeOfPrim op [.unit] = some τ) : ValueHasType v τ := by
  cases op <;> simp_all [evalPrim, typeOfPrim, typeOfConst, arithResultType] <;> subst_vars <;> first | exact .const | exact .unit

-- Per-Const×Const for 2-arg case: only int×int produces results for arith/cmp
set_option maxHeartbeats 12800000 in
private theorem ep2_const_const
    (h : evalPrim op [.const c1, .const c2] = some v)
    (hp : typeOfPrim op [typeOfConst c1, typeOfConst c2] = some τ) :
    ValueHasType v τ := by
  cases c1 <;> cases c2 <;> cases op <;>
    simp_all [evalPrim, typeOfPrim, typeOfConst, arithResultType] <;> subst_vars <;>
    first | exact .const | exact .unit |
      (rename_i x; cases x <;> simp_all <;> subst_vars <;> exact .const)

set_option maxHeartbeats 1600000 in
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
      | nil =>
        cases h1 <;> cases h2 <;>
          first | exact ep2_const_const heval hprim |
            (cases op <;> simp [evalPrim] at heval)
    | nil =>
      cases h1 with
      | const =>
        rename_i c
        cases c with
        | bool b => exact ep1_bool heval hprim
        | int n => exact ep1_int heval hprim
        | int64 n => exact ep1_int64 heval hprim
        | float n => exact ep1_float heval hprim
        | double n => exact ep1_double heval hprim
        | string s => exact ep1_string heval hprim
        | char c => exact ep1_char heval hprim
        | byte b => exact ep1_byte heval hprim
        | unit => exact ep1_unit' heval hprim
      | unit => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> exact .unit
      | closure => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .closure
      | closureRec => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .closureRec
      | closureRecMutual => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .closureRecMutual
      | rawFn => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .rawFn
      | constr hvl => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .constr hvl
      | tuple hvts => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .tuple hvts
      | locConstr hσ => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .locConstr hσ
      | locArray => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .locArray
      | errorValueResultOk hvt => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .errorValueResultOk hvt
      | errorValueResultErr hvt => cases op <;> simp [evalPrim] at heval <;> simp [typeOfPrim] at hprim <;> subst_vars <;> first | exact .unit | exact .errorValueResultErr hvt

end Moonbit.Mcore
