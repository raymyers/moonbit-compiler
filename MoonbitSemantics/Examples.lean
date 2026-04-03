/-
  MoonBit Compiler — Concrete Evaluation Examples
  End-to-end examples showing Mcore programs evaluate correctly,
  the corresponding Clam programs evaluate correctly, and the
  results match via the simulation relation.

  These examples could be extended with programs extracted from
  the compiler test suite (`src/` test cases).
-/
import MoonbitSemantics.Mcore.Simulation

namespace Moonbit.Examples

open Moonbit.Clam (Const Prim ArithOp CmpOp)
open Moonbit.Simulation (ValueSim ValueListSim)

/-! ## Shared empty contexts -/

def menv : Mcore.Env := Mcore.Env.empty
def cenv : Clam.Env := Clam.Env.empty
def ms : Mcore.Store := Mcore.Store.empty
def cs : Clam.Store := Clam.Store.empty
def mjt : Mcore.JoinTable := Mcore.JoinTable.empty
def cjt : Clam.JoinTable := Clam.JoinTable.empty
def mlt : Mcore.LoopTable := Mcore.LoopTable.empty
def mft : Mcore.FnTable := fun _ => none
def cft : Clam.FnTable := fun _ => none

/-!
## Example 1: `2 + 3 = 5`

MoonBit: `2 + 3`
Mcore:   `prim(add, [const(2), const(3)])`
Clam:    `Lprim(add, [Lconst(2), Lconst(3)])`
-/

theorem ex1_mcore :
    Mcore.Eval mft menv ms mjt mlt 0
      (.prim (.arith .add) [.const (.int 2), .const (.int 3)])
      (.val (.const (.int 5))) ms 0 := by
  apply Mcore.Eval.prim
  · exact Mcore.EvalArgs.cons Mcore.Eval.const
      (Mcore.EvalArgs.cons Mcore.Eval.const Mcore.EvalArgs.nil)
  · rfl

theorem ex1_clam :
    Clam.Eval cft cenv cs cjt 0
      (.prim (.arith .add) [.const (.int 2), .const (.int 3)])
      (.const (.int 5)) cs 0 := by
  apply Clam.Eval.prim
  · exact Clam.EvalArgs.cons Clam.Eval.const
      (Clam.EvalArgs.cons Clam.Eval.const Clam.EvalArgs.nil)
  · rfl

theorem ex1_sim : ValueSim (.const (.int 5)) (.const (.int 5)) :=
  ValueSim.const

/-!
## Example 2: `let x = 10 in x + 1 = 11`

MoonBit: `let x = 10; x + 1`
-/

def xId : Nat := 42

theorem ex2_mcore :
    Mcore.Eval mft menv ms mjt mlt 0
      (.let xId (.const (.int 10))
        (.prim (.arith .add) [.var xId none, .const (.int 1)]))
      (.val (.const (.int 11))) ms 0 := by
  apply Mcore.Eval.let (by simp [menv, Mcore.Env.empty]) Mcore.Eval.const
  apply Mcore.Eval.prim
  · apply Mcore.EvalArgs.cons
    · exact Mcore.Eval.var (v := .const (.int 10)) (by simp [Mcore.Env.extend])
    · exact Mcore.EvalArgs.cons Mcore.Eval.const Mcore.EvalArgs.nil
  · rfl

theorem ex2_clam :
    Clam.Eval cft cenv cs cjt 0
      (.let xId (.const (.int 10))
        (.prim (.arith .add) [.var xId, .const (.int 1)]))
      (.const (.int 11)) cs 0 := by
  apply Clam.Eval.let Clam.Eval.const
  apply Clam.Eval.prim
  · apply Clam.EvalArgs.cons
    · exact Clam.Eval.var (v := .const (.int 10)) (by simp [Clam.Env.extend])
    · exact Clam.EvalArgs.cons Clam.Eval.const Clam.EvalArgs.nil
  · rfl

theorem ex2_sim : ValueSim (.const (.int 11)) (.const (.int 11)) :=
  ValueSim.const

/-!
## Example 3: `if true then 1 else 2 = 1`
-/

theorem ex3_mcore :
    Mcore.Eval mft menv ms mjt mlt 0
      (.if (.const (.bool true)) (.const (.int 1)) (some (.const (.int 2))))
      (.val (.const (.int 1))) ms 0 :=
  Mcore.Eval.ifTrue Mcore.Eval.const Mcore.Eval.const

theorem ex3_clam :
    Clam.Eval cft cenv cs cjt 0
      (.if (.const (.bool true)) (.const (.int 1)) (.const (.int 2)))
      (.const (.int 1)) cs 0 :=
  Clam.Eval.ifTrue Clam.Eval.const Clam.Eval.const

theorem ex3_sim : ValueSim (.const (.int 1)) (.const (.int 1)) :=
  ValueSim.const

/-!
## Example 4: Short-circuit `false && panic() = false`

The panic is never evaluated.
-/

theorem ex4_mcore :
    Mcore.Eval mft menv ms mjt mlt 0
      (.and (.const (.bool false)) (.prim .panic []))
      (.val (.const (.bool false))) ms 0 :=
  Mcore.Eval.andFalse Mcore.Eval.const

theorem ex4_sim : ValueSim (.const (.bool false)) (.const (.bool false)) :=
  ValueSim.const

/-!
## Example 5: Constructor + pattern match

```moonbit
enum Fruit { Apple; Banana(Int) }
match Banana(42) { Apple => 0, Banana(n) => n }
```

Expected: `42`
-/

def bananaTag : Nat := 1
def nId : Nat := 99

theorem ex5_mcore :
    Mcore.Eval mft menv ms mjt mlt 0
      (.switchConstr
        (.constr bananaTag [.const (.int 42)])
        [(bananaTag, some nId, .field (.var nId none) (.index 0) 0)]
        (some (.const (.int 0))))
      (.val (.const (.int 42))) ms 0 := by
  apply Mcore.Eval.switchConstr
    (binder := some nId) (branch := .field (.var nId none) (.index 0) 0)
  · exact Mcore.Eval.constr
      (Mcore.EvalArgs.cons Mcore.Eval.const Mcore.EvalArgs.nil)
  · simp [Mcore.findConstrCase, bananaTag]
  · intro x hx; simp [menv, Mcore.Env.empty]
  · simp [bananaTag, nId]
    apply Mcore.Eval.fieldConstr
    · exact Mcore.Eval.var (v := .constr 1 [.const (.int 42)])
        (by simp [Mcore.Env.extend, nId])
    · rfl

/-!
## Example 6: Abort propagation — `loop { let x = break 99; x + 1 }`

The `break` propagates through the `let` (body is never reached),
and the loop catches it and returns 99.
-/

def lbl : Nat := 7

theorem ex6_mcore :
    Mcore.Eval mft menv ms mjt mlt 0
      (.loop []
        (.let xId
          (.break (some (.const (.int 99))) lbl)
          (.prim (.arith .add) [.var xId none, .const (.int 1)]))
        [] lbl)
      (.val (.const (.int 99))) ms 0 := by
  apply Mcore.Eval.loopBreak
  · exact Mcore.EvalArgs.nil
  · apply Mcore.Eval.letAbort
    · exact Mcore.Eval.breakSome Mcore.Eval.const
    · trivial

/-!
## Example 7: Tuple field access — `(10, 20).1 = 20`
-/

theorem ex7_mcore :
    Mcore.Eval mft menv ms mjt mlt 0
      (.field (.tuple [.const (.int 10), .const (.int 20)]) (.index 1) 1)
      (.val (.const (.int 20))) ms 0 := by
  apply Mcore.Eval.fieldTuple
  · exact Mcore.Eval.tuple
      (Mcore.EvalArgs.cons Mcore.Eval.const
        (Mcore.EvalArgs.cons Mcore.Eval.const Mcore.EvalArgs.nil))
  · rfl

/-!
## Example 8: Error handling — `try { raise(42) }` wraps as `Err(42)`

Mcore: `handle_error(return(42, ErrorResult(true, _)), ToResult)`
Result: `constr(1, [42])` i.e. `Err(42)`
-/

theorem ex8_mcore :
    Mcore.Eval mft menv ms mjt mlt 0
      (.handleError
        (.return (.const (.int 42)) (.errorResult true .int))
        .toResult)
      (.val (.constr 1 [.const (.int 42)])) ms 0 :=
  Mcore.Eval.handleErrorToResultErr (Mcore.Eval.returnError Mcore.Eval.const)

theorem ex8_sim :
    ValueSim (.constr 1 [.const (.int 42)]) (.closureVal [.const (.int 42)] 1) :=
  ValueSim.constr (ValueListSim.cons ValueSim.const ValueListSim.nil)

/-!
## Example 9: Nested computation — `let a = 2 + 3 in let b = a * a in b - 1 = 24`

MoonBit: `let a = 2 + 3; let b = a * a; b - 1`
-/

def aId : Nat := 10
def bId : Nat := 11

theorem ex9_mcore :
    Mcore.Eval mft menv ms mjt mlt 0
      (.let aId (.prim (.arith .add) [.const (.int 2), .const (.int 3)])
        (.let bId (.prim (.arith .mul) [.var aId none, .var aId none])
          (.prim (.arith .sub) [.var bId none, .const (.int 1)])))
      (.val (.const (.int 24))) ms 0 := by
  apply Mcore.Eval.let (by simp [menv, Mcore.Env.empty])
  · apply Mcore.Eval.prim
    · exact Mcore.EvalArgs.cons Mcore.Eval.const
        (Mcore.EvalArgs.cons Mcore.Eval.const Mcore.EvalArgs.nil)
    · rfl
  · apply Mcore.Eval.let (by simp [Mcore.Env.extend, menv, Mcore.Env.empty, aId, bId])
    · apply Mcore.Eval.prim
      · apply Mcore.EvalArgs.cons
        · exact Mcore.Eval.var (v := .const (.int 5)) (by simp [Mcore.Env.extend])
        · apply Mcore.EvalArgs.cons
          · exact Mcore.Eval.var (v := .const (.int 5)) (by simp [Mcore.Env.extend])
          · exact Mcore.EvalArgs.nil
      · rfl
    · apply Mcore.Eval.prim
      · apply Mcore.EvalArgs.cons
        · exact Mcore.Eval.var (v := .const (.int 25)) (by simp [Mcore.Env.extend])
        · exact Mcore.EvalArgs.cons Mcore.Eval.const Mcore.EvalArgs.nil
      · rfl

theorem ex9_clam :
    Clam.Eval cft cenv cs cjt 0
      (.let aId (.prim (.arith .add) [.const (.int 2), .const (.int 3)])
        (.let bId (.prim (.arith .mul) [.var aId, .var aId])
          (.prim (.arith .sub) [.var bId, .const (.int 1)])))
      (.const (.int 24)) cs 0 := by
  apply Clam.Eval.let
  · apply Clam.Eval.prim
    · exact Clam.EvalArgs.cons Clam.Eval.const
        (Clam.EvalArgs.cons Clam.Eval.const Clam.EvalArgs.nil)
    · rfl
  · apply Clam.Eval.let
    · apply Clam.Eval.prim
      · apply Clam.EvalArgs.cons
        · exact Clam.Eval.var (v := .const (.int 5)) (by simp [Clam.Env.extend])
        · apply Clam.EvalArgs.cons
          · exact Clam.Eval.var (v := .const (.int 5)) (by simp [Clam.Env.extend])
          · exact Clam.EvalArgs.nil
      · rfl
    · apply Clam.Eval.prim
      · apply Clam.EvalArgs.cons
        · exact Clam.Eval.var (v := .const (.int 25)) (by simp [Clam.Env.extend])
        · exact Clam.EvalArgs.cons Clam.Eval.const Clam.EvalArgs.nil
      · rfl

theorem ex9_sim : ValueSim (.const (.int 24)) (.const (.int 24)) :=
  ValueSim.const

end Moonbit.Examples
