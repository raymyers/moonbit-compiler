/-
  MoonBit Compiler — CLAM IR Operational Semantics
  Big-step evaluation relation for CLAM expressions,
  integrated with CSLib's LTS and reduction system infrastructure.
-/
import MoonbitSemantics.Clam.Values
import Cslib.Foundations.Semantics.LTS.Basic

open Cslib

namespace Moonbit.Clam

/-! ## Auxiliary definitions -/

/-- Evaluate a constant to a value. -/
def evalConst (c : Const) : Value := .const c

/-- Apply a primitive operation to a list of values. -/
def evalPrim : Prim → List Value → Option Value
  | .arith .add, [.const (.int a), .const (.int b)] => some (.const (.int (a + b)))
  | .arith .sub, [.const (.int a), .const (.int b)] => some (.const (.int (a - b)))
  | .arith .mul, [.const (.int a), .const (.int b)] => some (.const (.int (a * b)))
  | .cmp .eq, [.const (.int a), .const (.int b)] => some (.const (.bool (a == b)))
  | .cmp .ne, [.const (.int a), .const (.int b)] => some (.const (.bool (a != b)))
  | .cmp .lt, [.const (.int a), .const (.int b)] => some (.const (.bool (a < b)))
  | .cmp .le, [.const (.int a), .const (.int b)] => some (.const (.bool (a ≤ b)))
  | .cmp .gt, [.const (.int a), .const (.int b)] => some (.const (.bool (a > b)))
  | .cmp .ge, [.const (.int a), .const (.int b)] => some (.const (.bool (a ≥ b)))
  | .not, [.const (.bool b)] => some (.const (.bool (!b)))
  | .neg, [.const (.int n)] => some (.const (.int (-n)))
  | .ignore, [_] => some .unit
  | .identity, [v] => some v
  | _, _ => none

/-- Read a field from a heap object. -/
def readField (s : Store) (l : Loc) (idx : Nat) : Option Value :=
  match s l with
  | some (.aggregate _ fields) => fields[idx]?
  | none => none

/-- Write a field in a heap object. -/
def writeField (s : Store) (l : Loc) (idx : Nat) (v : Value) : Option Store :=
  match s l with
  | some (.aggregate kind fields) =>
    if h : idx < fields.size then
      some (Store.alloc s l (.aggregate kind (fields.set idx v)))
    else none
  | none => none

/-- Find a case by constructor tag. -/
def findCase (cases : List (ConstrTag × Lambda)) (tag : ConstrTag) : Option Lambda :=
  match cases.find? (fun (t, _) => t == tag) with
  | some (_, branch) => some branch
  | none => none

/-- Find a case by integer key. -/
def findIntCase (cases : List (Int × Lambda)) (n : Int) : Option Lambda :=
  match cases.find? (fun (i, _) => i == n) with
  | some (_, branch) => some branch
  | none => none

/-! ## Big-step evaluation

The judgment `Eval fnTable env s jt nl expr val s' nl'` means:
in environment `env`, store `s`, join table `jt`, with `nl` as the next fresh
location, expression `expr` evaluates to value `val`, producing store `s'` and
consuming locations up to `nl'`.

We use a separate `EvalArgs` judgment for evaluating argument lists left-to-right.
-/

mutual

/-- Evaluation of a list of expressions (left to right), threading state. -/
inductive EvalArgs (fnTable : FnTable) :
    Env → Store → JoinTable → Loc →
    List Lambda → List Value → Store → Loc → Prop where
  | nil :
    EvalArgs fnTable env s jt nl [] [] s nl
  | cons :
    Eval fnTable env s jt nl e v s₁ nl₁ →
    EvalArgs fnTable env s₁ jt nl₁ es vs s₂ nl₂ →
    EvalArgs fnTable env s jt nl (e :: es) (v :: vs) s₂ nl₂

/-- Big-step evaluation relation. -/
inductive Eval (fnTable : FnTable) :
    Env → Store → JoinTable → Loc →
    Lambda → Value → Store → Loc → Prop where

  /-- Constants evaluate to themselves. -/
  | const :
    Eval fnTable env s jt nl (.const c) (evalConst c) s nl

  /-- Variables look up in the environment. -/
  | var :
    env x = some v →
    Eval fnTable env s jt nl (.var x) v s nl

  /-- Let binding: evaluate the RHS, extend env, evaluate the body. -/
  | «let» :
    Eval fnTable env s jt nl e v₁ s₁ nl₁ →
    Eval fnTable (Env.extend env x v₁) s₁ jt nl₁ body v₂ s₂ nl₂ →
    Eval fnTable env s jt nl (.let x e body) v₂ s₂ nl₂

  /-- Allocation: evaluate fields, create heap object. -/
  | allocate :
    EvalArgs fnTable env s jt nl fieldExprs fieldVals s' nl' →
    Eval fnTable env s jt nl (.allocate kind fieldExprs)
      (.loc nl') (Store.alloc s' nl' (.aggregate kind fieldVals.toArray)) (nl' + 1)

  /-- Closure creation: capture current values of variables. -/
  | closure :
    List.Forall₂ (fun x v => env x = some v) captureVars captureVals →
    Eval fnTable env s jt nl (.closure captureVars addr) (.closureVal captureVals addr) s nl

  /-- Field read: evaluate object, read from heap. -/
  | getField :
    Eval fnTable env s jt nl obj (.loc l) s₁ nl₁ →
    readField s₁ l idx = some v →
    Eval fnTable env s jt nl (.getField obj idx kind) v s₁ nl₁

  /-- Field write: evaluate object and new value, update heap. -/
  | setField :
    Eval fnTable env s jt nl obj (.loc l) s₁ nl₁ →
    Eval fnTable env s₁ jt nl₁ field v s₂ nl₂ →
    writeField s₂ l idx v = some s₃ →
    Eval fnTable env s jt nl (.setField obj field idx kind) .unit s₃ nl₂

  /-- Static function call: look up function, bind params, evaluate body. -/
  | applyStatic :
    EvalArgs fnTable env s jt nl argExprs argVals s₁ nl₁ →
    fnTable addr = some (params, body) →
    params.length = argVals.length →
    Eval fnTable (Env.extendMany Env.empty (params.zip argVals)) s₁ JoinTable.empty nl₁
      body vr sr nlr →
    Eval fnTable env s jt nl (.apply (.staticFn addr) argExprs) vr sr nlr

  /-- Dynamic (closure) call: evaluate closure var, extract captures + addr, call. -/
  | applyDynamic :
    env f = some (.closureVal captures addr) →
    EvalArgs fnTable env s jt nl argExprs argVals s₁ nl₁ →
    fnTable addr = some (params, body) →
    params.length = captures.length + argVals.length →
    Eval fnTable (Env.extendMany Env.empty (params.zip (captures ++ argVals))) s₁
      JoinTable.empty nl₁ body vr sr nlr →
    Eval fnTable env s jt nl (.apply (.dynamic f) argExprs) vr sr nlr

  /-- Primitive operation: evaluate args, apply primitive. -/
  | prim :
    EvalArgs fnTable env s jt nl argExprs argVals s₁ nl₁ →
    evalPrim op argVals = some v →
    Eval fnTable env s jt nl (.prim op argExprs) v s₁ nl₁

  /-- If-then-else (true branch). -/
  | ifTrue :
    Eval fnTable env s jt nl pred (.const (.bool true)) s₁ nl₁ →
    Eval fnTable env s₁ jt nl₁ ifso vr sr nlr →
    Eval fnTable env s jt nl (.if pred ifso ifnot) vr sr nlr

  /-- If-then-else (false branch). -/
  | ifFalse :
    Eval fnTable env s jt nl pred (.const (.bool false)) s₁ nl₁ →
    Eval fnTable env s₁ jt nl₁ ifnot vr sr nlr →
    Eval fnTable env s jt nl (.if pred ifso ifnot) vr sr nlr

  /-- Sequence: evaluate all expressions in order, return the last. -/
  | seq :
    EvalArgs fnTable env s jt nl exprs vs s₁ nl₁ →
    Eval fnTable env s₁ jt nl₁ last vr sr nlr →
    Eval fnTable env s jt nl (.seq exprs last) vr sr nlr

  /-- Constructor switch: match on tag. -/
  | switch :
    env obj = some (.loc l) →
    s l = some (.aggregate (.enum tag) _) →
    findCase cases tag = some branch →
    Eval fnTable env s jt nl branch vr sr nlr →
    Eval fnTable env s jt nl (.switch obj cases default) vr sr nlr

  /-- Constructor switch: default branch. -/
  | switchDefault :
    env obj = some (.loc l) →
    s l = some (.aggregate (.enum tag) _) →
    findCase cases tag = none →
    Eval fnTable env s jt nl default vr sr nlr →
    Eval fnTable env s jt nl (.switch obj cases default) vr sr nlr

  /-- Integer switch: match. -/
  | switchInt :
    env obj = some (.const (.int n)) →
    findIntCase cases n = some branch →
    Eval fnTable env s jt nl branch vr sr nlr →
    Eval fnTable env s jt nl (.switchInt obj cases default) vr sr nlr

  /-- Integer switch: default. -/
  | switchIntDefault :
    env obj = some (.const (.int n)) →
    findIntCase cases n = none →
    Eval fnTable env s jt nl default vr sr nlr →
    Eval fnTable env s jt nl (.switchInt obj cases default) vr sr nlr

  /-- Join point definition: register join in the table, evaluate body. -/
  | joinlet :
    Eval fnTable env s (JoinTable.extend jt name ⟨jparams, je⟩) nl body vr sr nlr →
    Eval fnTable env s jt nl (.joinlet name jparams je body kind) vr sr nlr

  /-- Join point application: look up the join, bind params, evaluate. -/
  | joinapply :
    EvalArgs fnTable env s jt nl argExprs argVals s₁ nl₁ →
    jt name = some ⟨jparams, jbody⟩ →
    jparams.length = argVals.length →
    Eval fnTable (Env.extendMany env (jparams.zip argVals)) s₁ jt nl₁ jbody vr sr nlr →
    Eval fnTable env s jt nl (.joinapply name argExprs) vr sr nlr

  /-- Assignment: evaluate RHS (semantically returns unit). -/
  | assign :
    Eval fnTable env s jt nl e v s₁ nl₁ →
    Eval fnTable env s jt nl (.assign x e) .unit s₁ nl₁

  /-- Catch: if body succeeds, return its value. -/
  | catchOk :
    Eval fnTable env s jt nl body v s₁ nl₁ →
    Eval fnTable env s jt nl (.catch body handler) v s₁ nl₁

end -- mutual

/-! ## CSLib Integration: Labelled Transition System

We model the CLAM semantics as a CSLib `LTS` where:
- **State** = `Config` (expression + env + store + joins + fnTable + nextLoc)
- **Label** = `Unit` (unlabelled — pure reduction semantics)

This gives us access to CSLib's multistep transitions (`MTr`), reachability,
termination, confluence, bisimulation, etc.
-/

/-- The CLAM transition relation on configurations.
    A configuration steps when its expression evaluates to a value. -/
inductive ClamTr : Config → Unit → Config → Prop where
  | step (heval : Eval c₁.fnTable c₁.env c₁.store c₁.joins c₁.nextLoc c₁.expr v s' nl') :
    ClamTr c₁ ()
      { expr := .const .unit  -- terminal configuration
        env := c₁.env
        store := s'
        joins := c₁.joins
        fnTable := c₁.fnTable
        nextLoc := nl' }

/-- The CLAM Labelled Transition System. -/
def clamLTS : LTS Config Unit where
  Tr := ClamTr

/-! ## Reduction system (unlabelled)

We also define the step relation as a binary relation on `Config` for use with
CSLib's `@[reduction_sys]` to get `⭢` / `↠` notation and access to confluence,
termination, and normal forms.
-/

/-- The unlabelled step relation. -/
@[reduction_sys "clam "]
def ClamStep (c₁ c₂ : Config) : Prop := ClamTr c₁ () c₂

/-! ## Basic properties -/

/-- Variables with a binding are not stuck — they evaluate immediately. -/
theorem var_evals (env : Env) (s : Store) (jt : JoinTable) (ft : FnTable) (nl : Loc)
    (x : Var) (v : Value) (h : env x = some v) :
    Eval ft env s jt nl (.var x) v s nl :=
  Eval.var h

/-- Integer addition is correct. -/
theorem add_correct (env : Env) (s : Store) (jt : JoinTable) (ft : FnTable) (nl : Loc)
    (a b : Int) :
    Eval ft env s jt nl
      (.prim (.arith .add) [.const (.int a), .const (.int b)])
      (.const (.int (a + b))) s nl := by
  apply Eval.prim
  · exact EvalArgs.cons Eval.const (EvalArgs.cons Eval.const EvalArgs.nil)
  · simp [evalPrim, evalConst]

end Moonbit.Clam
