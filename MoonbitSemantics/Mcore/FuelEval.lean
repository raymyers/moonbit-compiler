/-
  MoonBit Compiler — Mcore Fuel-Bounded Evaluator

  A partial functional interpreter for Mcore expressions, bounded by a
  natural-number fuel parameter. Used to state and prove **progress** for
  well-typed programs: well-typed programs never yield `.stuck`, only `.ok`
  (successful evaluation) or `.outOfFuel` (legitimate divergence).

  This file is structured in two phases:
  - **Phase 1 (this file)**: data types + function signatures + case skeleton.
    Every case returns `.stuck "TODO: <case>"`, so the file typechecks and
    subsequent phases can fill in logic incrementally without restructuring.
  - **Phase 2+** (future): fill in each case with real evaluation logic,
    then prove soundness (`evalFuel.ok → Eval`) and progress
    (`HasType → evalFuel n ≠ .stuck _`).
-/
import MoonbitSemantics.Mcore.Semantics
import MoonbitSemantics.Mcore.CanonicalForms

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp)

/-! ## Result types

`EvalFuelResult` is the return type of `evalFuel`: successful evaluation,
out-of-fuel, or stuck (with a debug reason string).

`EvalFuelArgsResult` is the return type of `evalFuelArgs` (list-of-args
evaluation): all args evaluated to values, an abort propagated from one
of the args, out-of-fuel, or stuck. -/

inductive EvalFuelResult where
  | ok (o : Outcome) (s' : Store) (nl' : Loc) : EvalFuelResult
  | outOfFuel : EvalFuelResult
  | stuck (reason : String) : EvalFuelResult
  deriving Inhabited

inductive EvalFuelArgsResult where
  | okVals (vs : List Value) (s' : Store) (nl' : Loc) : EvalFuelArgsResult
  | abortArgs (o : Outcome) (s' : Store) (nl' : Loc) : EvalFuelArgsResult
  | outOfFuelArgs : EvalFuelArgsResult
  | stuckArgs (reason : String) : EvalFuelArgsResult
  deriving Inhabited

/-! ## Fuel-bounded evaluator — skeleton

Each case currently returns `.stuck "TODO: <case>"`. Phase 2 fills in logic.
Termination: by `n` (fuel), which decreases at every recursive call.
-/

mutual

/-- Fuel-bounded evaluation of a single expression. -/
def evalFuel : Nat → FnTable → Env → Store → JoinTable → LoopTable → Loc →
    Expr → EvalFuelResult
  | 0, _, _, _, _, _, _, _ => .outOfFuel
  | _n+1, _ft, _env, _s, _jt, _lt, _nl, e =>
    match e with
    -- Leaves
    | .const _ => .stuck "TODO: const"
    | .unit => .stuck "TODO: unit"
    | .var _ _ => .stuck "TODO: var"
    -- Bindings
    | .let _ _ _ => .stuck "TODO: let"
    | .letfn _ _ _ _ _ => .stuck "TODO: letfn"
    | .letrec _ _ => .stuck "TODO: letrec"
    -- Functions
    | .function _ _ _ => .stuck "TODO: function"
    | .apply _ _ _ => .stuck "TODO: apply"
    -- Primitives
    | .prim _ _ => .stuck "TODO: prim"
    -- Data construction
    | .constr _ _ => .stuck "TODO: constr"
    | .tuple _ => .stuck "TODO: tuple"
    | .record _ => .stuck "TODO: record"
    | .recordUpdate _ _ _ => .stuck "TODO: recordUpdate"
    | .array _ => .stuck "TODO: array"
    -- Data access
    | .field _ _ _ => .stuck "TODO: field"
    | .mutate _ _ _ _ => .stuck "TODO: mutate"
    -- Assignment
    | .assign _ _ => .stuck "TODO: assign"
    -- Sequencing
    | .seq _ _ => .stuck "TODO: seq"
    -- Control flow
    | .if _ _ _ => .stuck "TODO: if"
    | .switchConstr _ _ _ => .stuck "TODO: switchConstr"
    | .switchConstant _ _ _ => .stuck "TODO: switchConstant"
    | .loop _ _ _ _ => .stuck "TODO: loop"
    | .break _ _ => .stuck "TODO: break"
    | .continue _ _ => .stuck "TODO: continue"
    -- Logical
    | .and _ _ => .stuck "TODO: and"
    | .or _ _ => .stuck "TODO: or"
    -- Error handling
    | .handleError _ _ => .stuck "TODO: handleError"
    | .return _ _ => .stuck "TODO: return"
    -- Objects
    | .object _ => .stuck "TODO: object"

/-- Fuel-bounded evaluation of a list of argument expressions. -/
def evalFuelArgs : Nat → FnTable → Env → Store → JoinTable → LoopTable → Loc →
    List Expr → EvalFuelArgsResult
  | 0, _, _, _, _, _, _, _ => .outOfFuelArgs
  | _n+1, _ft, _env, s, _jt, _lt, nl, [] => .okVals [] s nl
  | _n+1, _ft, _env, _s, _jt, _lt, _nl, _e :: _es =>
    .stuckArgs "TODO: evalFuelArgs cons"

end

end Moonbit.Mcore
