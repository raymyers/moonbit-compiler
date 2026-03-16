/-
  MoonBit Compiler — Mcore Runtime Values and State
  Defines semantic domains: values, store, environments, configurations.
-/
import MoonbitSemantics.Mcore.Syntax

namespace Moonbit.Mcore

/-! ## Heap locations -/

abbrev Loc := Nat

/-! ## Runtime values

Closures capture a list of (var, value) bindings rather than an entire `Env`
function, breaking the mutual recursion between Value and Env.
-/

/-- A runtime value produced by evaluating an Mcore expression. -/
inductive Value where
  | const (c : Moonbit.Clam.Const)
  | unit
  | closure (captured : List (Var × Value)) (params : List Param) (body : Expr)
  | rawFn (params : List Param) (body : Expr)
  | constr (tag : ConstrTag) (args : List Value)
  | tuple (vals : List Value)
  | loc (l : Loc)

instance : Inhabited Value := ⟨Value.unit⟩

/-! ## Heap objects -/

/-- A heap-allocated object. -/
inductive HeapObj where
  | record (fields : Array Value) (mutFlags : Array Bool)
  | array (elems : Array Value)

/-! ## Store (heap) -/

abbrev Store := Loc → Option HeapObj

def Store.empty : Store := fun _ => none

def Store.alloc (s : Store) (l : Loc) (obj : HeapObj) : Store :=
  fun l' => if l' = l then some obj else s l'

/-! ## Environments -/

abbrev Env := Var → Option Value

def Env.empty : Env := fun _ => none

def Env.extend (env : Env) (x : Var) (v : Value) : Env :=
  fun y => if y = x then some v else env y

def Env.extendMany (env : Env) (bindings : List (Var × Value)) : Env :=
  bindings.foldl (fun acc (x, v) => acc.extend x v) env

def Env.bindParams (env : Env) (params : List Param) (args : List Value) : Env :=
  Env.extendMany env (params.map (·.binder) |>.zip args)

/-- Snapshot an environment to a list of bindings (for closure creation).
    In the semantics we pass the relevant captured variables explicitly. -/
def Env.capture (env : Env) (vars : List Var) : List (Var × Value) :=
  vars.filterMap fun v => (env v).map (v, ·)

/-- Restore a captured environment. -/
def Env.ofCapture (captured : List (Var × Value)) : Env :=
  Env.extendMany Env.empty captured

/-! ## Function table -/

abbrev FnTable := Var → Option (List Param × Expr)

/-! ## Join point table -/

structure JoinEntry where
  params : List Param
  body : Expr

abbrev JoinTable := Var → Option JoinEntry

def JoinTable.empty : JoinTable := fun _ => none

def JoinTable.extend (jt : JoinTable) (j : Var) (e : JoinEntry) : JoinTable :=
  fun j' => if j' = j then some e else jt j'

/-! ## Loop context -/

structure LoopCtx where
  params : List Param
  body : Expr

abbrev LoopTable := LoopLabel → Option LoopCtx

def LoopTable.empty : LoopTable := fun _ => none

def LoopTable.extend (lt : LoopTable) (l : LoopLabel) (ctx : LoopCtx) : LoopTable :=
  fun l' => if l' = l then some ctx else lt l'

/-! ## Evaluation outcome -/

/-- Mcore has non-local control flow. Outcomes model this. -/
inductive Outcome where
  | val (v : Value)
  | «break» (v : Option Value) (label : LoopLabel)
  | «continue» (args : List Value) (label : LoopLabel)
  | «return» (v : Value)
  | error (v : Value)

def Outcome.isVal : Outcome → Prop
  | .val _ => True
  | _ => False

/-- An outcome is an abort (non-value: break/continue/return/error). -/
def Outcome.isAbort : Outcome → Prop
  | .val _ => False
  | _ => True

def Value.isClosure : Value → Prop
  | .closure .. => True
  | _ => False

/-- Constant equality (decidable, for switch matching). -/
def Const.beq : Moonbit.Clam.Const → Moonbit.Clam.Const → Bool
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .int64 a, .int64 b => a == b
  | .string a, .string b => a == b
  | .char a, .char b => a == b
  | .byte a, .byte b => a == b
  | .unit, .unit => true
  | _, _ => false

/-! ## Configuration -/

structure Config where
  expr : Expr
  env : Env
  store : Store
  joins : JoinTable
  loops : LoopTable
  fnTable : FnTable
  nextLoc : Loc

end Moonbit.Mcore
