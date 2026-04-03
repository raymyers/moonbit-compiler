/-
  MoonBit Compiler — Mcore Operational Semantics (Complete)
  Big-step evaluation with full abort propagation for non-local control flow.
-/
import MoonbitSemantics.Mcore.Values
import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Data.Relation

open Cslib

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp)

/-! ## Primitives -/

def evalPrim : Prim → List Value → Option Value
  | .arith .add, [.const (.int a), .const (.int b)] => some (.const (.int (a + b)))
  | .arith .sub, [.const (.int a), .const (.int b)] => some (.const (.int (a - b)))
  | .arith .mul, [.const (.int a), .const (.int b)] => some (.const (.int (a * b)))
  | .arith .div, [.const (.int a), .const (.int b)] => some (.const (.int (a / b)))
  | .arith .mod, [.const (.int a), .const (.int b)] => some (.const (.int (a % b)))
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
  | .panic, _ => none
  | .unreachable, _ => none
  | _, _ => none

/-! ## Case lookup -/

def findConstrCase (cases : List (ConstrTag × Option Var × Expr)) (tag : ConstrTag)
    : Option (Option Var × Expr) :=
  match cases.find? (fun (t, _, _) => t == tag) with
  | some (_, binder, branch) => some (binder, branch)
  | none => none

def findConstantCase (cases : List (Const × Expr)) (c : Const) : Option Expr :=
  match cases.find? (fun (k, _) => Const.beq k c) with
  | some (_, branch) => some branch
  | none => none

/-- If `findConstrCase cases tag` returns `some (binder, branch)`, then the triple
    `(tag, binder, branch)` is a member of `cases`. -/
lemma findConstrCase_mem (cases : List (ConstrTag × Option Var × Expr)) (tag : ConstrTag)
    (binder : Option Var) (branch : Expr)
    (h : findConstrCase cases tag = some (binder, branch)) :
    (tag, binder, branch) ∈ cases := by
  simp only [findConstrCase] at h
  generalize hf : cases.find? (fun (t, _, _) => t == tag) = r at h
  cases r with
  | none => simp at h
  | some entry =>
    obtain ⟨t, b, e⟩ := entry
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    have hmem := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    simp only [beq_iff_eq] at hpred
    rw [← hpred]
    exact hmem

/-- If `findConstantCase cases c` returns `some branch`, then there exists a key `c'`
    such that `(c', branch) ∈ cases` and `Const.beq c' c = true`. -/
lemma findConstantCase_mem (cases : List (Const × Expr)) (c : Const) (branch : Expr)
    (h : findConstantCase cases c = some branch) :
    ∃ c', (c', branch) ∈ cases ∧ Const.beq c' c = true := by
  simp only [findConstantCase] at h
  generalize hf : cases.find? (fun (k, _) => Const.beq k c) = r at h
  cases r with
  | none => simp at h
  | some entry =>
    obtain ⟨k, e⟩ := entry
    simp only [Option.some.injEq] at h
    rw [← h]
    have hmem := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    simp only at hpred
    exact ⟨k, hmem, hpred⟩

/-- If `findConstantCase cases c` returns `some branch`, then there exists an index `i`
    (with a bound proof `hi : i < cases.length`) such that `(cases[i]).2 = branch`. -/
lemma findConstantCase_index (cases : List (Const × Expr)) (c : Const) (branch : Expr)
    (h : findConstantCase cases c = some branch) :
    ∃ i, ∃ hi : i < cases.length, (cases[i]'hi).2 = branch := by
  simp only [findConstantCase] at h
  generalize hf : cases.find? (fun (k, _) => Const.beq k c) = r at h
  cases r with
  | none => simp at h
  | some entry =>
    obtain ⟨k, e⟩ := entry
    simp only [Option.some.injEq] at h
    rw [← h]
    have hmem := List.mem_of_find?_eq_some hf
    rw [List.mem_iff_get] at hmem
    obtain ⟨idx, hidx⟩ := hmem
    refine ⟨idx.val, idx.isLt, ?_⟩
    have : cases[idx.val]'idx.isLt = (k, e) := by
      rw [← List.get_eq_getElem]
      exact hidx
    rw [this]

/-! ## Big-step evaluation

Every compound expression form has:
1. **Normal rules** — sub-expressions produce values, evaluation proceeds.
2. **Abort rules** — a sub-expression produces a non-value outcome
   (break/continue/return/error), which propagates upward immediately.

This ensures that non-local control flow is correctly modeled.
-/

mutual

/-- Evaluate a list of expressions left-to-right. All must produce values.
    If any produces an abort, use `EvalArgsAbort` instead. -/
inductive EvalArgs (fnTable : FnTable) :
    Env → Store → JoinTable → LoopTable → Loc →
    List Expr → List Value → Store → Loc → Prop where
  | nil :
    EvalArgs fnTable env s jt lt nl [] [] s nl
  | cons :
    Eval fnTable env s jt lt nl e (.val v) s₁ nl₁ →
    EvalArgs fnTable env s₁ jt lt nl₁ es vs s₂ nl₂ →
    EvalArgs fnTable env s jt lt nl (e :: es) (v :: vs) s₂ nl₂

/-- Evaluate a list of expressions, but one aborts. Returns the abort outcome.
    Earlier expressions succeeded (produced values), the current one aborted. -/
inductive EvalArgsAbort (fnTable : FnTable) :
    Env → Store → JoinTable → LoopTable → Loc →
    List Expr → Outcome → Store → Loc → Prop where
  | here :
    Eval fnTable env s jt lt nl e outcome s₁ nl₁ →
    outcome.isAbort →
    EvalArgsAbort fnTable env s jt lt nl (e :: es) outcome s₁ nl₁
  | later :
    Eval fnTable env s jt lt nl e (.val _) s₁ nl₁ →
    EvalArgsAbort fnTable env s₁ jt lt nl₁ es outcome s₂ nl₂ →
    EvalArgsAbort fnTable env s jt lt nl (e :: es) outcome s₂ nl₂

/-- Big-step evaluation relation for Mcore. -/
inductive Eval (fnTable : FnTable) :
    Env → Store → JoinTable → LoopTable → Loc →
    Expr → Outcome → Store → Loc → Prop where

  -- ══════════════════════════════════════════════════════════════════
  -- Constants and variables
  -- ══════════════════════════════════════════════════════════════════

  | const :
    Eval fnTable env s jt lt nl (.const c) (.val (.const c)) s nl

  | unit :
    Eval fnTable env s jt lt nl .unit (.val .unit) s nl

  | var :
    env x = some v →
    Eval fnTable env s jt lt nl (.var x none) (.val v) s nl

  /-- Variable with primitive specialization: look up and apply prim. -/
  | varPrim :
    env x = some v →
    Eval fnTable env s jt lt nl (.var x (some p)) (.val v) s nl

  -- ══════════════════════════════════════════════════════════════════
  -- Let binding
  -- ══════════════════════════════════════════════════════════════════

  | «let» :
    env name = none →
    Eval fnTable env s jt lt nl rhs (.val v₁) s₁ nl₁ →
    Eval fnTable (Env.extend env name v₁) s₁ jt lt nl₁ body outcome s₂ nl₂ →
    Eval fnTable env s jt lt nl (.let name rhs body) outcome s₂ nl₂

  /-- Let: RHS aborts → propagate. -/
  | letAbort :
    Eval fnTable env s jt lt nl rhs outcome s₁ nl₁ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.let name rhs body) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Functions
  -- ══════════════════════════════════════════════════════════════════

  | «function» :
    Eval fnTable env s jt lt nl (.function params fnBody false)
      (.val (.closure env params fnBody)) s nl

  | rawFunction :
    Eval fnTable env s jt lt nl (.function params fnBody true)
      (.val (.rawFn params fnBody)) s nl

  -- ══════════════════════════════════════════════════════════════════
  -- Local function bindings (4 LetfnKind cases)
  -- ══════════════════════════════════════════════════════════════════

  | letfnNonrec :
    env name = none →
    Eval fnTable (Env.extend env name (.closure env params fnBody))
      s jt lt nl body outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.letfn name params fnBody body .nonRecursive) outcome s₁ nl₁

  | letfnRec :
    env name = none →
    recEnv = Env.extend env name (.closure recEnv params fnBody) →
    Eval fnTable recEnv s jt lt nl body outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.letfn name params fnBody body .recursive) outcome s₁ nl₁

  | letfnTailJoin :
    jt name = none →
    Eval fnTable env s (JoinTable.extend jt name ⟨params, fnBody⟩) lt nl
      body outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.letfn name params fnBody body .tailJoin) outcome s₁ nl₁

  | letfnNontailJoin :
    jt name = none →
    Eval fnTable env s (JoinTable.extend jt name ⟨params, fnBody⟩) lt nl
      body outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.letfn name params fnBody body .nontailJoin) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Mutual recursion
  -- ══════════════════════════════════════════════════════════════════

  /-- Mutually recursive bindings. Each closure captures the full recursive env. -/
  | letrec :
    recEnv = Env.extendMany env
      (bindings.map fun (v, ps, b) => (v, Value.closure recEnv ps b)) →
    Eval fnTable recEnv s jt lt nl body outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.letrec bindings body) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Function application
  -- ══════════════════════════════════════════════════════════════════

  | applyClosure :
    env func = some (.closure captured params fnBody) →
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    params.length = argVals.length →
    Eval fnTable (Env.bindParams captured params argVals)
      s₁ JoinTable.empty LoopTable.empty nl₁ fnBody outcome sr nlr →
    Eval fnTable env s jt lt nl (.apply func argExprs (.normal funcTy)) outcome sr nlr

  | applyRawFn :
    env func = some (.rawFn params fnBody) →
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    params.length = argVals.length →
    Eval fnTable (Env.bindParams Env.empty params argVals)
      s₁ JoinTable.empty LoopTable.empty nl₁ fnBody outcome sr nlr →
    Eval fnTable env s jt lt nl (.apply func argExprs (.normal funcTy)) outcome sr nlr

  /-- Call a top-level function (not in env as closure). -/
  | applyTopFn :
    fnTable func = some (params, fnBody) →
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    params.length = argVals.length →
    Eval fnTable (Env.bindParams Env.empty params argVals)
      s₁ JoinTable.empty LoopTable.empty nl₁ fnBody outcome sr nlr →
    Eval fnTable env s jt lt nl (.apply func argExprs (.normal funcTy)) outcome sr nlr

  | applyJoin :
    jt func = some ⟨params, jbody⟩ →
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    params.length = argVals.length →
    Eval fnTable (Env.bindParams env params argVals)
      s₁ jt lt nl₁ jbody outcome sr nlr →
    Eval fnTable env s jt lt nl (.apply func argExprs .join) outcome sr nlr

  /-- Apply: args abort → propagate. -/
  | applyAbort :
    EvalArgsAbort fnTable env s jt lt nl argExprs outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.apply func argExprs kind) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Primitives
  -- ══════════════════════════════════════════════════════════════════

  | prim :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Moonbit.Mcore.evalPrim op argVals = some v →
    Eval fnTable env s jt lt nl (.prim op argExprs) (.val v) s₁ nl₁

  | primAbort :
    EvalArgsAbort fnTable env s jt lt nl argExprs outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.prim op argExprs) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Data construction
  -- ══════════════════════════════════════════════════════════════════

  | constr :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable env s jt lt nl (.constr tag argExprs) (.val (.constr tag argVals)) s₁ nl₁

  | constrAbort :
    EvalArgsAbort fnTable env s jt lt nl argExprs outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.constr tag argExprs) outcome s₁ nl₁

  | tuple :
    EvalArgs fnTable env s jt lt nl exprs vals s₁ nl₁ →
    Eval fnTable env s jt lt nl (.tuple exprs) (.val (.tuple vals)) s₁ nl₁

  | tupleAbort :
    EvalArgsAbort fnTable env s jt lt nl exprs outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.tuple exprs) outcome s₁ nl₁

  | record :
    EvalArgs fnTable env s jt lt nl (fieldExprs.map fun (_, _, _, e) => e) fieldVals s₁ nl₁ →
    Eval fnTable env s jt lt nl (.record fieldExprs)
      (.val (.loc nl₁))
      (Store.alloc s₁ nl₁ (.record fieldVals.toArray
        ((fieldExprs.map fun (_, _, m, _) => m).toArray)))
      (nl₁ + 1)

  | recordAbort :
    EvalArgsAbort fnTable env s jt lt nl (fieldExprs.map fun (_, _, _, e) => e) outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.record fieldExprs) outcome s₁ nl₁

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

  | recordUpdateAbortRec :
    Eval fnTable env s jt lt nl rec_ outcome s₁ nl₁ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.recordUpdate rec_ updFields fieldsNum) outcome s₁ nl₁

  | recordUpdateAbortFields :
    Eval fnTable env s jt lt nl rec_ (.val (.loc l)) s₁ nl₁ →
    s₁ l = some (.record _ _) →
    EvalArgsAbort fnTable env s₁ jt lt nl₁ (updFields.map fun (_, _, _, e) => e) outcome s₂ nl₂ →
    Eval fnTable env s jt lt nl (.recordUpdate rec_ updFields fieldsNum) outcome s₂ nl₂

  | array :
    EvalArgs fnTable env s jt lt nl exprs vals s₁ nl₁ →
    Eval fnTable env s jt lt nl (.array exprs)
      (.val (.loc nl₁))
      (Store.alloc s₁ nl₁ (.array vals.toArray))
      (nl₁ + 1)

  | arrayAbort :
    EvalArgsAbort fnTable env s jt lt nl exprs outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.array exprs) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Data access
  -- ══════════════════════════════════════════════════════════════════

  | fieldTuple :
    Eval fnTable env s jt lt nl rec_ (.val (.tuple vals)) s₁ nl₁ →
    vals[pos]? = some v →
    Eval fnTable env s jt lt nl (.field rec_ acc pos) (.val v) s₁ nl₁

  | fieldConstr :
    Eval fnTable env s jt lt nl rec_ (.val (.constr _ vals)) s₁ nl₁ →
    vals[pos]? = some v →
    Eval fnTable env s jt lt nl (.field rec_ acc pos) (.val v) s₁ nl₁

  | fieldRecord :
    Eval fnTable env s jt lt nl rec_ (.val (.loc l)) s₁ nl₁ →
    s₁ l = some (.record fields _) →
    fields[pos]? = some v →
    Eval fnTable env s jt lt nl (.field rec_ acc pos) (.val v) s₁ nl₁

  | fieldAbort :
    Eval fnTable env s jt lt nl rec_ outcome s₁ nl₁ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.field rec_ acc pos) outcome s₁ nl₁

  | mutate :
    Eval fnTable env s jt lt nl rec_ (.val (.loc l)) s₁ nl₁ →
    Eval fnTable env s₁ jt lt nl₁ fld (.val v) s₂ nl₂ →
    s₂ l = some (.record fields mutFlags) →
    Eval fnTable env s jt lt nl (.mutate rec_ label fld pos)
      (.val .unit)
      (Store.alloc s₂ l (.record (fields.setIfInBounds pos v) mutFlags))
      nl₂

  | mutateAbortRec :
    Eval fnTable env s jt lt nl rec_ outcome s₁ nl₁ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.mutate rec_ label fld pos) outcome s₁ nl₁

  | mutateAbortFld :
    Eval fnTable env s jt lt nl rec_ (.val (.loc _)) s₁ nl₁ →
    Eval fnTable env s₁ jt lt nl₁ fld outcome s₂ nl₂ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.mutate rec_ label fld pos) outcome s₂ nl₂

  -- ══════════════════════════════════════════════════════════════════
  -- Assignment
  -- ══════════════════════════════════════════════════════════════════

  | assign :
    Eval fnTable env s jt lt nl e (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.assign x e) (.val .unit) s₁ nl₁

  | assignAbort :
    Eval fnTable env s jt lt nl e outcome s₁ nl₁ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.assign x e) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Sequencing
  -- ══════════════════════════════════════════════════════════════════

  | seq :
    EvalArgs fnTable env s jt lt nl exprs _ s₁ nl₁ →
    Eval fnTable env s₁ jt lt nl₁ last outcome sr nlr →
    Eval fnTable env s jt lt nl (.seq exprs last) outcome sr nlr

  | seqAbort :
    EvalArgsAbort fnTable env s jt lt nl exprs outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.seq exprs last) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Conditionals
  -- ══════════════════════════════════════════════════════════════════

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

  | ifAbort :
    Eval fnTable env s jt lt nl condE outcome s₁ nl₁ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.if condE ifso ifnot) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Pattern matching
  -- ══════════════════════════════════════════════════════════════════

  | switchConstr :
    Eval fnTable env s jt lt nl obj (.val (.constr tag args)) s₁ nl₁ →
    findConstrCase cases tag = some (binder, branch) →
    (∀ x, binder = some x → env x = none) →
    Eval fnTable
      (match binder with
        | some x => Env.extend env x (.constr tag args)
        | none => env)
      s₁ jt lt nl₁ branch outcome sr nlr →
    Eval fnTable env s jt lt nl (.switchConstr obj cases dflt) outcome sr nlr

  | switchConstrDefault :
    Eval fnTable env s jt lt nl obj (.val (.constr tag _)) s₁ nl₁ →
    findConstrCase cases tag = none →
    Eval fnTable env s₁ jt lt nl₁ d outcome sr nlr →
    Eval fnTable env s jt lt nl (.switchConstr obj cases (some d)) outcome sr nlr

  | switchConstrAbort :
    Eval fnTable env s jt lt nl obj outcome s₁ nl₁ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.switchConstr obj cases dflt) outcome s₁ nl₁

  | switchConstantMatch :
    Eval fnTable env s jt lt nl obj (.val (.const c)) s₁ nl₁ →
    findConstantCase cases c = some branch →
    Eval fnTable env s₁ jt lt nl₁ branch outcome sr nlr →
    Eval fnTable env s jt lt nl (.switchConstant obj cases dflt) outcome sr nlr

  | switchConstantDefault :
    Eval fnTable env s jt lt nl obj (.val (.const c)) s₁ nl₁ →
    findConstantCase cases c = none →
    Eval fnTable env s₁ jt lt nl₁ dflt outcome sr nlr →
    Eval fnTable env s jt lt nl (.switchConstant obj cases dflt) outcome sr nlr

  | switchConstantAbort :
    Eval fnTable env s jt lt nl obj outcome s₁ nl₁ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.switchConstant obj cases dflt) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Loops
  -- ══════════════════════════════════════════════════════════════════

  /-- Loop body returns a value → loop terminates. -/
  | loopVal :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable (Env.bindParams env params argVals) s₁ jt
      (LoopTable.extend lt label ⟨params, body⟩) nl₁ body (.val v) sr nlr →
    Eval fnTable env s jt lt nl (.loop params body argExprs label) (.val v) sr nlr

  /-- Loop body breaks with value → loop terminates with that value. -/
  | loopBreak :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable (Env.bindParams env params argVals) s₁ jt
      (LoopTable.extend lt label ⟨params, body⟩) nl₁ body (.break (some v) label) sr nlr →
    Eval fnTable env s jt lt nl (.loop params body argExprs label) (.val v) sr nlr

  /-- Loop body breaks with none → loop terminates with unit. -/
  | loopBreakNone :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable (Env.bindParams env params argVals) s₁ jt
      (LoopTable.extend lt label ⟨params, body⟩) nl₁ body (.break none label) sr nlr →
    Eval fnTable env s jt lt nl (.loop params body argExprs label) (.val .unit) sr nlr

  /-- Loop body continues → re-enter loop via LoopReentry (catches breaks properly). -/
  | loopContinue :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable (Env.bindParams env params argVals) s₁ jt
      (LoopTable.extend lt label ⟨params, body⟩) nl₁ body (.continue newVals label) s₂ nl₂ →
    params.length = newVals.length →
    LoopReentry fnTable env s₂ jt lt nl₂ params body newVals label loopOutcome sr nlr →
    Eval fnTable env s jt lt nl (.loop params body argExprs label) loopOutcome sr nlr

  /-- Loop body returns/errors → propagate past loop. -/
  | loopReturn :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable (Env.bindParams env params argVals) s₁ jt
      (LoopTable.extend lt label ⟨params, body⟩) nl₁ body (.return v) sr nlr →
    Eval fnTable env s jt lt nl (.loop params body argExprs label) (.return v) sr nlr

  | loopError :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable (Env.bindParams env params argVals) s₁ jt
      (LoopTable.extend lt label ⟨params, body⟩) nl₁ body (.error v) sr nlr →
    Eval fnTable env s jt lt nl (.loop params body argExprs label) (.error v) sr nlr

  /-- Loop: args abort → propagate. -/
  | loopAbort :
    EvalArgsAbort fnTable env s jt lt nl argExprs outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.loop params body argExprs label) outcome s₁ nl₁

  /-- Break: evaluate arg and signal. -/
  | breakSome :
    Eval fnTable env s jt lt nl arg (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.break (some arg) label) (.break (some v) label) s₁ nl₁

  | breakNone :
    Eval fnTable env s jt lt nl (.break none label) (.break none label) s nl

  | breakAbort :
    Eval fnTable env s jt lt nl arg outcome s₁ nl₁ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.break (some arg) label) outcome s₁ nl₁

  /-- Continue: evaluate args and signal. -/
  | «continue» :
    EvalArgs fnTable env s jt lt nl argExprs argVals s₁ nl₁ →
    Eval fnTable env s jt lt nl (.continue argExprs label) (.continue argVals label) s₁ nl₁

  | continueAbort :
    EvalArgsAbort fnTable env s jt lt nl argExprs outcome s₁ nl₁ →
    Eval fnTable env s jt lt nl (.continue argExprs label) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Short-circuit logical operators
  -- ══════════════════════════════════════════════════════════════════

  | andTrue :
    Eval fnTable env s jt lt nl lhs (.val (.const (.bool true))) s₁ nl₁ →
    Eval fnTable env s₁ jt lt nl₁ rhs outcome sr nlr →
    Eval fnTable env s jt lt nl (.and lhs rhs) outcome sr nlr

  | andFalse :
    Eval fnTable env s jt lt nl lhs (.val (.const (.bool false))) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.and lhs rhs) (.val (.const (.bool false))) s₁ nl₁

  | andAbort :
    Eval fnTable env s jt lt nl lhs outcome s₁ nl₁ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.and lhs rhs) outcome s₁ nl₁

  | orTrue :
    Eval fnTable env s jt lt nl lhs (.val (.const (.bool true))) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.or lhs rhs) (.val (.const (.bool true))) s₁ nl₁

  | orFalse :
    Eval fnTable env s jt lt nl lhs (.val (.const (.bool false))) s₁ nl₁ →
    Eval fnTable env s₁ jt lt nl₁ rhs outcome sr nlr →
    Eval fnTable env s jt lt nl (.or lhs rhs) outcome sr nlr

  | orAbort :
    Eval fnTable env s jt lt nl lhs outcome s₁ nl₁ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.or lhs rhs) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Error handling
  -- ══════════════════════════════════════════════════════════════════

  | handleErrorToResultOk :
    Eval fnTable env s jt lt nl obj (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.handleError obj .toResult)
      (.val (.constr 0 [v])) s₁ nl₁

  | handleErrorToResultErr :
    Eval fnTable env s jt lt nl obj (.error v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.handleError obj .toResult)
      (.val (.constr 1 [v])) s₁ nl₁

  | handleErrorJoinOk :
    Eval fnTable env s jt lt nl obj (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.handleError obj (.joinapply _)) (.val v) s₁ nl₁

  | handleErrorJoinErr :
    Eval fnTable env s jt lt nl obj (.error v) s₁ nl₁ →
    jt target = some ⟨jparams, jbody⟩ →
    Eval fnTable (Env.bindParams env jparams [v]) s₁ jt lt nl₁ jbody outcome sr nlr →
    Eval fnTable env s jt lt nl (.handleError obj (.joinapply target)) outcome sr nlr

  | handleErrorReturnErrOk :
    Eval fnTable env s jt lt nl obj (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.handleError obj (.returnErr _)) (.val v) s₁ nl₁

  | handleErrorReturnErrErr :
    Eval fnTable env s jt lt nl obj (.error v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.handleError obj (.returnErr _)) (.error v) s₁ nl₁

  /-- handleError: break/continue/return propagate through (not caught). -/
  | handleErrorPropagate :
    Eval fnTable env s jt lt nl obj outcome s₁ nl₁ →
    (∀ v, outcome ≠ .val v) →
    (∀ v, outcome ≠ .error v) →
    Eval fnTable env s jt lt nl (.handleError obj kind) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Return
  -- ══════════════════════════════════════════════════════════════════

  | returnSingle :
    Eval fnTable env s jt lt nl e (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.return e .singleValue) (.val v) s₁ nl₁

  | returnError :
    Eval fnTable env s jt lt nl e (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.return e (.errorResult true retTy)) (.error v) s₁ nl₁

  | returnOk :
    Eval fnTable env s jt lt nl e (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.return e (.errorResult false retTy)) (.val v) s₁ nl₁

  | returnAbort :
    Eval fnTable env s jt lt nl e outcome s₁ nl₁ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.return e kind) outcome s₁ nl₁

  -- ══════════════════════════════════════════════════════════════════
  -- Objects (trait dispatch)
  -- ══════════════════════════════════════════════════════════════════

  /-- Object expression: evaluate self and wrap as a value.
      In the full compiler this creates a vtable + self pair;
      we model it as evaluating the self expression. -/
  | object :
    Eval fnTable env s jt lt nl self (.val v) s₁ nl₁ →
    Eval fnTable env s jt lt nl (.object self) (.val v) s₁ nl₁

  | objectAbort :
    Eval fnTable env s jt lt nl self outcome s₁ nl₁ →
    outcome.isAbort →
    Eval fnTable env s jt lt nl (.object self) outcome s₁ nl₁

/-- Loop re-entry: evaluates body with new args, catching breaks/continues properly. -/
inductive LoopReentry (fnTable : FnTable) :
    Env → Store → JoinTable → LoopTable → Loc →
    List Param → Expr → List Value → LoopLabel →
    Outcome → Store → Loc → Prop where
  | val :
    Eval fnTable (Env.bindParams env params newVals) s jt
      (LoopTable.extend lt label ⟨params, body⟩) nl body (.val v) sr nlr →
    LoopReentry fnTable env s jt lt nl params body newVals label (.val v) sr nlr
  | breakSome :
    Eval fnTable (Env.bindParams env params newVals) s jt
      (LoopTable.extend lt label ⟨params, body⟩) nl body (.break (some v) label) sr nlr →
    LoopReentry fnTable env s jt lt nl params body newVals label (.val v) sr nlr
  | breakNone :
    Eval fnTable (Env.bindParams env params newVals) s jt
      (LoopTable.extend lt label ⟨params, body⟩) nl body (.break none label) sr nlr →
    LoopReentry fnTable env s jt lt nl params body newVals label (.val .unit) sr nlr
  | «continue» :
    Eval fnTable (Env.bindParams env params newVals) s jt
      (LoopTable.extend lt label ⟨params, body⟩) nl body (.continue nextVals label) s₂ nl₂ →
    nextVals.length = params.length →
    LoopReentry fnTable env s₂ jt lt nl₂ params body nextVals label loopOutcome sr nlr →
    LoopReentry fnTable env s jt lt nl params body newVals label loopOutcome sr nlr
  | «return» :
    Eval fnTable (Env.bindParams env params newVals) s jt
      (LoopTable.extend lt label ⟨params, body⟩) nl body (.return v) sr nlr →
    LoopReentry fnTable env s jt lt nl params body newVals label (.return v) sr nlr
  | error :
    Eval fnTable (Env.bindParams env params newVals) s jt
      (LoopTable.extend lt label ⟨params, body⟩) nl body (.error v) sr nlr →
    LoopReentry fnTable env s jt lt nl params body newVals label (.error v) sr nlr

end -- mutual

/-! ## CSLib Integration -/

inductive McoreTr : Config → Unit → Config → Prop where
  | step (heval : Eval c₁.fnTable c₁.env c₁.store c₁.joins c₁.loops c₁.nextLoc
      c₁.expr (.val v) s' nl') :
    McoreTr c₁ ()
      { expr := .unit, env := c₁.env, store := s', joins := c₁.joins,
        loops := c₁.loops, fnTable := c₁.fnTable, nextLoc := nl' }

def mcoreLTS : LTS Config Unit where
  Tr := McoreTr

@[reduction_sys "mcore "]
def McoreStep (c₁ c₂ : Config) : Prop := McoreTr c₁ () c₂

/-! ## Properties -/

theorem unit_evals (env : Env) (s : Store) (jt : JoinTable) (lt : LoopTable)
    (ft : FnTable) (nl : Loc) :
    Eval ft env s jt lt nl .unit (.val .unit) s nl :=
  Eval.unit

theorem const_evals (c : Const) (env : Env) (s : Store) (jt : JoinTable)
    (lt : LoopTable) (ft : FnTable) (nl : Loc) :
    Eval ft env s jt lt nl (.const c) (.val (.const c)) s nl :=
  Eval.const

theorem var_evals (env : Env) (s : Store) (jt : JoinTable) (lt : LoopTable)
    (ft : FnTable) (nl : Loc) (x : Var) (v : Value) (h : env x = some v) :
    Eval ft env s jt lt nl (.var x none) (.val v) s nl :=
  Eval.var h

theorem add_correct (env : Env) (s : Store) (jt : JoinTable) (lt : LoopTable)
    (ft : FnTable) (nl : Loc) (a b : Int) :
    Eval ft env s jt lt nl
      (.prim (.arith .add) [.const (.int a), .const (.int b)])
      (.val (.const (.int (a + b)))) s nl := by
  apply Eval.prim
  · exact EvalArgs.cons Eval.const (EvalArgs.cons Eval.const EvalArgs.nil)
  · simp [Moonbit.Mcore.evalPrim]

theorem and_short_circuit (ft : FnTable) (env : Env) (s : Store) (jt : JoinTable)
    (lt : LoopTable) (nl : Loc) (rhs : Expr) :
    Eval ft env s jt lt nl (.and (.const (.bool false)) rhs)
      (.val (.const (.bool false))) s nl :=
  Eval.andFalse Eval.const

theorem or_short_circuit (ft : FnTable) (env : Env) (s : Store) (jt : JoinTable)
    (lt : LoopTable) (nl : Loc) (rhs : Expr) :
    Eval ft env s jt lt nl (.or (.const (.bool true)) rhs)
      (.val (.const (.bool true))) s nl :=
  Eval.orTrue Eval.const

theorem if_true_branch (ft : FnTable) (env : Env) (s : Store) (jt : JoinTable)
    (lt : LoopTable) (nl : Loc) (ifso ifnot : Expr) (outcome : Outcome) (sr : Store) (nlr : Loc)
    (hbranch : Eval ft env s jt lt nl ifso outcome sr nlr) :
    Eval ft env s jt lt nl (.if (.const (.bool true)) ifso (some ifnot)) outcome sr nlr :=
  Eval.ifTrue Eval.const hbranch

/-- Break propagates through let-binding RHS. -/
theorem break_propagates_let (ft : FnTable) (env : Env) (s : Store) (jt : JoinTable)
    (lt : LoopTable) (nl : Loc) (x : Var) (body : Expr) (v : Value) (label : LoopLabel) :
    Eval ft env s jt lt nl
      (.let x (.break (some (.const (.int 42))) label) body)
      (.break (some (.const (.int 42))) label) s nl := by
  apply Eval.letAbort
  · exact Eval.breakSome Eval.const
  · trivial

end Moonbit.Mcore
