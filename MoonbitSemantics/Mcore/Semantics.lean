/-
  MoonBit Compiler — Mcore Operational Semantics
  Big-step evaluation relation for Mcore expressions,
  integrated with CSLib's LTS and reduction system infrastructure.
-/
import MoonbitSemantics.Mcore.Values
import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Data.Relation

open Cslib

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp)

/-! ## Auxiliary definitions -/

/-- Apply a primitive operation to Mcore values. -/
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

/-- Look up a constructor case by tag. -/
def findConstrCase (cases : List (ConstrTag × Option Var × Expr)) (tag : ConstrTag)
    : Option (Option Var × Expr) :=
  match cases.find? (fun (t, _, _) => t == tag) with
  | some (_, binder, branch) => some (binder, branch)
  | none => none

/-! ## Big-step evaluation

`Eval fnTable env s jt lt nl expr outcome s' nl'`

Evaluates `expr` in the given context, producing an `Outcome`, an updated
store `s'`, and the next fresh location `nl'`.
-/

mutual

/-- Evaluate a list of expressions left-to-right (all must produce values). -/
inductive EvalArgs (fnTable : FnTable) :
    Env → Store → JoinTable → LoopTable → Loc →
    List Expr → List Value → Store → Loc → Prop where
  | nil :
    EvalArgs fnTable env s jt lt nl [] [] s nl
  | cons :
    Eval fnTable env s jt lt nl e (.val v) s₁ nl₁ →
    EvalArgs fnTable env s₁ jt lt nl₁ es vs s₂ nl₂ →
    EvalArgs fnTable env s jt lt nl (e :: es) (v :: vs) s₂ nl₂

/-- Big-step evaluation relation for Mcore. -/
inductive Eval (fnTable : FnTable) :
    Env → Store → JoinTable → LoopTable → Loc →
    Expr → Outcome → Store → Loc → Prop where


  | const :
    Eval fnTable env s jt lt nl (.const c) (.val (.const c)) s nl

  | unit :
    Eval fnTable env s jt lt nl .unit (.val .unit) s nl


  | var :
    env x = some v →
    Eval fnTable env s jt lt nl (.var x none) (.val v) s nl


  | «let» :
    Eval fnTable env s jt lt nl rhs (.val v₁) s₁ nl₁ →
    Eval fnTable (Env.extend env name v₁) s₁ jt lt nl₁ body outcome s₂ nl₂ →
    Eval fnTable env s jt lt nl (.let name rhs body) outcome s₂ nl₂


  /-- Function expression: create closure with captured bindings. -/
  | «function» :
    Eval fnTable env s jt lt nl (.function params fnBody false)
      (.val (.closure (Env.capture env freeVars) params fnBody)) s nl

  /-- Raw function (no closure capture). -/
  | rawFunction :
    Eval fnTable env s jt lt nl (.function params fnBody true)
      (.val (.rawFn params fnBody)) s nl


  /-- Non-recursive local function. -/
  | letfnNonrec :
    Eval fnTable (Env.extend env name (.closure (Env.capture env freeVars) params fnBody))
      s jt lt nl body outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.letfn name params fnBody body .nonRecursive) outcome s₁ nl₁

  /-- Tail join point: register in join table. -/
  | letfnTailJoin :
    Eval fnTable env s (JoinTable.extend jt name ⟨params, fnBody⟩) lt nl
      body outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.letfn name params fnBody body .tailJoin) outcome s₁ nl₁

  /-- Non-tail join point: register in join table. -/
  | letfnNontailJoin :
    Eval fnTable env s (JoinTable.extend jt name ⟨params, fnBody⟩) lt nl
      body outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.letfn name params fnBody body .nontailJoin) outcome s₁ nl₁

  /-- Recursive local function: the closure's captured env includes itself. -/
  | letfnRec :
    Eval fnTable
      (Env.extend env name (Value.closure ((name, Value.unit) :: Env.capture env freeVars) params fnBody))
      s jt lt nl body outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.letfn name params fnBody body .recursive) outcome s₁ nl₁

  /-- Mutually recursive bindings: all closures share the recursive env. -/
  | letrec :
    Eval fnTable
      (Env.extendMany env (bindings.map fun (v, ps, b) => (v, Value.closure (Env.capture env freeVars) ps b)))
      s jt lt nl body outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.letrec bindings body) outcome s₁ nl₁

  /-- Call a closure value. -/
  | applyClosure :
    env func = some (.closure captured params fnBody) →
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    params.length = argVals.length →
    Eval fnTable (Env.bindParams (Env.ofCapture captured) params argVals)
      s₁ JoinTable.empty LoopTable.empty nl₁ fnBody outcome sr nlr →
    Eval fnTable env s jt lt nl (.apply func argExprs (.normal funcTy)) outcome sr nlr

  /-- Call a raw function value. -/
  | applyRawFn :
    env func = some (.rawFn params fnBody) →
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    params.length = argVals.length →
    Eval fnTable (Env.bindParams Env.empty params argVals)
      s₁ JoinTable.empty LoopTable.empty nl₁ fnBody outcome sr nlr →
    Eval fnTable env s jt lt nl (.apply func argExprs (.normal funcTy)) outcome sr nlr

  /-- Join point application. -/
  | applyJoin :
    jt func = some ⟨params, jbody⟩ →
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    params.length = argVals.length →
    Eval fnTable (Env.bindParams env params argVals)
      s₁ jt lt nl₁ jbody outcome sr nlr →
    Eval fnTable env s jt lt nl (.apply func argExprs .join) outcome sr nlr


  | prim :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Moonbit.Mcore.evalPrim op argVals = some v →
    Eval fnTable env s jt lt nl (.prim op argExprs) (.val v) s₁ nl₁


  | constr :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable env s jt lt nl (.constr tag argExprs) (.val (.constr tag argVals)) s₁ nl₁

  | tuple :
    EvalArgs fnTable env s jt lt nl exprs vals s₁ nl₁ →
    Eval fnTable env s jt lt nl (.tuple exprs) (.val (.tuple vals)) s₁ nl₁

  /-- Record: allocate on the heap. -/
  | record :
    EvalArgs fnTable env s jt lt nl (fieldExprs.map fun (_, _, _, e) => e) fieldVals s₁ nl₁ →
    Eval fnTable env s jt lt nl (.record fieldExprs)
      (.val (.loc nl₁))
      (Store.alloc s₁ nl₁ (.record fieldVals.toArray
        ((fieldExprs.map fun (_, _, m, _) => m).toArray)))
      (nl₁ + 1)

  /-- Record update: copy a record, overwriting specified fields. -/
  | recordUpdate :
    Eval fnTable env s jt lt nl rec_ (.val (.loc l)) s₁ nl₁ →
    s₁ l = some (.record oldFields mutFlags) →
    EvalArgs fnTable env s₁ jt lt nl₁ (updFields.map fun (_, _, _, e) => e) newVals s₂ nl₂ →
    updatedFields = (updFields.zip newVals).foldl
      (fun acc ((_, pos, _, _), v) => acc.setIfInBounds pos v) oldFields →
    Eval fnTable env s jt lt nl (.recordUpdate rec_ updFields fieldsNum)
      (.val (.loc nl₂))
      (Store.alloc s₂ nl₂ (.record updatedFields mutFlags))
      (nl₂ + 1)

  /-- Array construction: allocate on the heap. -/
  | array :
    EvalArgs fnTable env s jt lt nl exprs vals s₁ nl₁ →
    Eval fnTable env s jt lt nl (.array exprs)
      (.val (.loc nl₁))
      (Store.alloc s₁ nl₁ (.array vals.toArray))
      (nl₁ + 1)


  /-- Field from a tuple. -/
  | fieldTuple :
    Eval fnTable env s jt lt nl rec_ (.val (.tuple vals)) s₁ nl₁ →
    vals[pos]? = some v →
    Eval fnTable env s jt lt nl (.field rec_ acc pos) (.val v) s₁ nl₁

  /-- Field from a constructor. -/
  | fieldConstr :
    Eval fnTable env s jt lt nl rec_ (.val (.constr _ vals)) s₁ nl₁ →
    vals[pos]? = some v →
    Eval fnTable env s jt lt nl (.field rec_ acc pos) (.val v) s₁ nl₁

  /-- Field from a heap record. -/
  | fieldRecord :
    Eval fnTable env s jt lt nl rec_ (.val (.loc l)) s₁ nl₁ →
    s₁ l = some (.record fields _) →
    fields[pos]? = some v →
    Eval fnTable env s jt lt nl (.field rec_ acc pos) (.val v) s₁ nl₁

  /-- Mutable field write. -/
  | mutate :
    Eval fnTable env s jt lt nl rec_ (.val (.loc l)) s₁ nl₁ →
    Eval fnTable env s₁ jt lt nl₁ fld (.val v) s₂ nl₂ →
    s₂ l = some (.record fields mutFlags) →
    Eval fnTable env s jt lt nl (.mutate rec_ label fld pos)
      (.val .unit)
      (Store.alloc s₂ l (.record (fields.setIfInBounds pos v) mutFlags))
      nl₂

  /-- Variable assignment. -/
  | assign :
    Eval fnTable env s jt lt nl e (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.assign x e) (.val .unit) s₁ nl₁


  | seq :
    EvalArgs fnTable env s jt lt nl exprs _ s₁ nl₁ →
    Eval fnTable env s₁ jt lt nl₁ last outcome sr nlr →
    Eval fnTable env s jt lt nl (.seq exprs last) outcome sr nlr


  | ifTrue :
    Eval fnTable env s jt lt nl condE (.val (.const (.bool true))) s₁ nl₁ →
    Eval fnTable env s₁ jt lt nl₁ ifso outcome sr nlr →
    Eval fnTable env s jt lt nl (.if condE ifso ifnot) outcome sr nlr

  | ifFalse :
    Eval fnTable env s jt lt nl condE (.val (.const (.bool false))) s₁ nl₁ →
    Eval fnTable env s₁ jt lt nl₁ ifnot outcome sr nlr →
    Eval fnTable env s jt lt nl (.if condE ifso (some ifnot)) outcome sr nlr

  | ifFalseNoElse :
    Eval fnTable env s jt lt nl condE (.val (.const (.bool false))) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.if condE ifso none) (.val .unit) s₁ nl₁


  /-- Constructor switch: matching case. -/
  | switchConstr :
    Eval fnTable env s jt lt nl obj (.val (.constr tag args)) s₁ nl₁ →
    findConstrCase cases tag = some (binder, branch) →
    Eval fnTable
      (match binder with
        | some x => Env.extend env x (.constr tag args)
        | none => env)
      s₁ jt lt nl₁ branch outcome sr nlr →
    Eval fnTable env s jt lt nl (.switchConstr obj cases default) outcome sr nlr

  /-- Constructor switch: default. -/
  | switchConstrDefault :
    Eval fnTable env s jt lt nl obj (.val (.constr tag _)) s₁ nl₁ →
    findConstrCase cases tag = none →
    Eval fnTable env s₁ jt lt nl₁ dflt outcome sr nlr →
    Eval fnTable env s jt lt nl (.switchConstr obj cases (some dflt)) outcome sr nlr

  /-- Constant switch: default (simplified). -/
  | switchConstant :
    Eval fnTable env s jt lt nl obj (.val _) s₁ nl₁ →
    Eval fnTable env s₁ jt lt nl₁ dflt outcome sr nlr →
    Eval fnTable env s jt lt nl (.switchConstant obj _ dflt) outcome sr nlr


  /-- Loop: body returns a value (loop terminates). -/
  | loopVal :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable (Env.bindParams env params argVals) s₁ jt
      (LoopTable.extend lt label ⟨params, body⟩) nl₁ body (.val v) sr nlr →
    Eval fnTable env s jt lt nl (.loop params body argExprs label) (.val v) sr nlr

  /-- Loop: body does `break` with matching label — exit loop with value. -/
  | loopBreak :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable (Env.bindParams env params argVals) s₁ jt
      (LoopTable.extend lt label ⟨params, body⟩) nl₁ body (.break (some v) label) sr nlr →
    Eval fnTable env s jt lt nl (.loop params body argExprs label) (.val v) sr nlr

  /-- Loop: body does `break none` with matching label — exit with unit. -/
  | loopBreakNone :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable (Env.bindParams env params argVals) s₁ jt
      (LoopTable.extend lt label ⟨params, body⟩) nl₁ body (.break none label) sr nlr →
    Eval fnTable env s jt lt nl (.loop params body argExprs label) (.val .unit) sr nlr

  /-- Loop: body does `continue` with matching label — re-enter with new args. -/
  | loopContinue :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable (Env.bindParams env params argVals) s₁ jt
      (LoopTable.extend lt label ⟨params, body⟩) nl₁ body (.continue newVals label) s₂ nl₂ →
    -- Re-enter the loop with new values (big-step: tail-recurse into same loop rule)
    Eval fnTable (Env.bindParams env params newVals) s₂ jt
      (LoopTable.extend lt label ⟨params, body⟩) nl₂ body (.val v) sr nlr →
    Eval fnTable env s jt lt nl (.loop params body argExprs label) (.val v) sr nlr

  /-- Break: signal loop exit. -/
  | breakSome :
    Eval fnTable env s jt lt nl arg (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.break (some arg) label) (.break (some v) label) s₁ nl₁

  | breakNone :
    Eval fnTable env s jt lt nl (.break none label) (.break none label) s nl

  /-- Continue: evaluate args and signal restart. -/
  | «continue» :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable env s jt lt nl (.continue argExprs label) (.continue argVals label) s₁ nl₁


  | andTrue :
    Eval fnTable env s jt lt nl lhs (.val (.const (.bool true))) s₁ nl₁ →
    Eval fnTable env s₁ jt lt nl₁ rhs outcome sr nlr →
    Eval fnTable env s jt lt nl (.and lhs rhs) outcome sr nlr

  | andFalse :
    Eval fnTable env s jt lt nl lhs (.val (.const (.bool false))) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.and lhs rhs) (.val (.const (.bool false))) s₁ nl₁

  | orTrue :
    Eval fnTable env s jt lt nl lhs (.val (.const (.bool true))) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.or lhs rhs) (.val (.const (.bool true))) s₁ nl₁

  | orFalse :
    Eval fnTable env s jt lt nl lhs (.val (.const (.bool false))) s₁ nl₁ →
    Eval fnTable env s₁ jt lt nl₁ rhs outcome sr nlr →
    Eval fnTable env s jt lt nl (.or lhs rhs) outcome sr nlr


  /-- handle_error To_result: Ok case. -/
  | handleErrorOk :
    Eval fnTable env s jt lt nl obj (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.handleError obj .toResult)
      (.val (.constr 0 [v])) s₁ nl₁

  /-- handle_error To_result: Err case. -/
  | handleErrorErr :
    Eval fnTable env s jt lt nl obj (.error v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.handleError obj .toResult)
      (.val (.constr 1 [v])) s₁ nl₁

  /-- handle_error Joinapply: Ok passthrough. -/
  | handleErrorJoinOk :
    Eval fnTable env s jt lt nl obj (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.handleError obj (.joinapply _)) (.val v) s₁ nl₁

  /-- return Single_value: pass through. -/
  | returnSingle :
    Eval fnTable env s jt lt nl e (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.return e .singleValue) (.val v) s₁ nl₁

  /-- return Error_result (is_error = true): signal error. -/
  | returnError :
    Eval fnTable env s jt lt nl e (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.return e (.errorResult true retTy)) (.error v) s₁ nl₁

  /-- return Error_result (is_error = false): normal return. -/
  | returnOk :
    Eval fnTable env s jt lt nl e (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.return e (.errorResult false retTy)) (.val v) s₁ nl₁

  /-- handle_error Joinapply: on error, jump to join point. -/
  | handleErrorJoinErr :
    Eval fnTable env s jt lt nl obj (.error v) s₁ nl₁ →
    jt target = some ⟨jparams, jbody⟩ →
    Eval fnTable (Env.bindParams env jparams [v]) s₁ jt lt nl₁ jbody outcome sr nlr →
    Eval fnTable env s jt lt nl (.handleError obj (.joinapply target)) outcome sr nlr

  /-- handle_error Return_err: on error, propagate. -/
  | handleErrorReturnErrOk :
    Eval fnTable env s jt lt nl obj (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.handleError obj (.returnErr _)) (.val v) s₁ nl₁

  /-- handle_error Return_err: on error, re-raise. -/
  | handleErrorReturnErrErr :
    Eval fnTable env s jt lt nl obj (.error v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.handleError obj (.returnErr _)) (.error v) s₁ nl₁

end -- mutual

/-! ## CSLib Integration -/

/-- The Mcore transition relation. -/
inductive McoreTr : Config → Unit → Config → Prop where
  | step (heval : Eval c₁.fnTable c₁.env c₁.store c₁.joins c₁.loops c₁.nextLoc
      c₁.expr (.val v) s' nl') :
    McoreTr c₁ ()
      { expr := .unit
        env := c₁.env
        store := s'
        joins := c₁.joins
        loops := c₁.loops
        fnTable := c₁.fnTable
        nextLoc := nl' }

/-- The Mcore Labelled Transition System. -/
def mcoreLTS : LTS Config Unit where
  Tr := McoreTr

/-- The unlabelled step relation. -/
@[reduction_sys "mcore "]
def McoreStep (c₁ c₂ : Config) : Prop := McoreTr c₁ () c₂

/-! ## Basic properties -/

/-- Unit evaluates to the unit value. -/
theorem unit_evals (env : Env) (s : Store) (jt : JoinTable) (lt : LoopTable)
    (ft : FnTable) (nl : Loc) :
    Eval ft env s jt lt nl .unit (.val .unit) s nl :=
  Eval.unit

/-- Constants evaluate to themselves. -/
theorem const_evals (c : Moonbit.Clam.Const) (env : Env) (s : Store) (jt : JoinTable)
    (lt : LoopTable) (ft : FnTable) (nl : Loc) :
    Eval ft env s jt lt nl (.const c) (.val (.const c)) s nl :=
  Eval.const

/-- Variable lookup is total when binding exists. -/
theorem var_evals (env : Env) (s : Store) (jt : JoinTable) (lt : LoopTable)
    (ft : FnTable) (nl : Loc) (x : Var) (v : Value) (h : env x = some v) :
    Eval ft env s jt lt nl (.var x none) (.val v) s nl :=
  Eval.var h

/-- Integer addition evaluates correctly. -/
theorem add_correct (env : Env) (s : Store) (jt : JoinTable) (lt : LoopTable)
    (ft : FnTable) (nl : Loc) (a b : Int) :
    Eval ft env s jt lt nl
      (.prim (.arith .add) [.const (.int a), .const (.int b)])
      (.val (.const (.int (a + b)))) s nl := by
  apply Eval.prim
  · exact EvalArgs.cons Eval.const (EvalArgs.cons Eval.const EvalArgs.nil)
  · simp [Moonbit.Mcore.evalPrim]

/-- Let-binding composes evaluation: if rhs evals and body evals, let evals. -/
theorem let_compose (ft : FnTable) (env : Env) (s : Store) (jt : JoinTable) (lt : LoopTable)
    (nl : Loc) (x : Var) (a b : Int) (body : Expr) (outcome : Outcome) (s₂ : Store) (nl₂ : Loc)
    (hbody : Eval ft (Env.extend env x (.const (.int (a + b)))) s jt lt nl body outcome s₂ nl₂) :
    Eval ft env s jt lt nl
      (.let x (.prim (.arith .add) [.const (.int a), .const (.int b)]) body) outcome s₂ nl₂ := by
  exact Eval.let (add_correct env s jt lt ft nl a b) hbody

/-- Short-circuit AND: false && _ = false (without evaluating RHS). -/
theorem and_short_circuit (ft : FnTable) (env : Env) (s : Store) (jt : JoinTable) (lt : LoopTable)
    (nl : Loc) (rhs : Expr) :
    Eval ft env s jt lt nl
      (.and (.const (.bool false)) rhs)
      (.val (.const (.bool false))) s nl :=
  Eval.andFalse Eval.const

/-- Short-circuit OR: true || _ = true (without evaluating RHS). -/
theorem or_short_circuit (ft : FnTable) (env : Env) (s : Store) (jt : JoinTable) (lt : LoopTable)
    (nl : Loc) (rhs : Expr) :
    Eval ft env s jt lt nl
      (.or (.const (.bool true)) rhs)
      (.val (.const (.bool true))) s nl :=
  Eval.orTrue Eval.const

/-- If-true evaluates only the true branch. -/
theorem if_true_branch (ft : FnTable) (env : Env) (s : Store) (jt : JoinTable) (lt : LoopTable)
    (nl : Loc) (ifso ifnot : Expr) (outcome : Outcome) (sr : Store) (nlr : Loc)
    (hbranch : Eval ft env s jt lt nl ifso outcome sr nlr) :
    Eval ft env s jt lt nl
      (.if (.const (.bool true)) ifso (some ifnot)) outcome sr nlr :=
  Eval.ifTrue Eval.const hbranch

end Moonbit.Mcore
