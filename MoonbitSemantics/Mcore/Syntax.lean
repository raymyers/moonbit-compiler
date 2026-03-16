/-
  MoonBit Compiler — Mcore Expression IR
  Formalization of the expression type from `src/mcore.ml` (29 constructors).
-/
import MoonbitSemantics.Mcore.Types

namespace Moonbit.Mcore

/-! ## Auxiliary types -/

/-- How a local function binding is classified. -/
inductive LetfnKind where
  | nonRecursive
  | recursive
  | tailJoin
  | nontailJoin
  deriving DecidableEq

/-- Kind of function application. -/
inductive ApplyKind where
  | normal (funcTy : Mtype)
  | join

/-- Kind of return statement. -/
inductive ReturnKind where
  | errorResult (isError : Bool) (returnTy : Mtype)
  | singleValue

/-- Kind of error handling. -/
inductive HandleKind where
  | toResult
  | joinapply (target : Var)
  | returnErr (okTy : Mtype)

/-- Field accessor (by label or by position). -/
inductive Accessor where
  | label (l : FieldLabel)
  | index (i : Nat)

/-- A function parameter. -/
structure Param where
  binder : Var
  ty : Mtype

/-! ## Expression type — 29 constructors

Fn and FieldDef fields are inlined into constructors to avoid mutual recursion
with structures (which Lean 4 doesn't support).
-/

/-- Mcore expressions. -/
inductive Expr where
  -- Literals
  | const (c : Moonbit.Clam.Const)
  | unit
  -- Variables
  | var (id : Var) (prim : Option Moonbit.Clam.Prim)
  -- Primitives
  | prim (op : Moonbit.Clam.Prim) (args : List Expr)
  -- Bindings
  | «let» (name : Var) (rhs : Expr) (body : Expr)
  | letfn (name : Var) (params : List Param) (fnBody : Expr) (body : Expr) (kind : LetfnKind)
  | letrec (bindings : List (Var × List Param × Expr)) (body : Expr)
  -- Functions
  | «function» (params : List Param) (fnBody : Expr) (isRaw : Bool)
  | apply (func : Var) (args : List Expr) (kind : ApplyKind)
  -- Objects
  | object (self : Expr)
  -- Data construction
  | constr (tag : ConstrTag) (args : List Expr)
  | tuple (exprs : List Expr)
  -- Record: list of (label, position, isMut, expression)
  | record (fields : List (FieldLabel × Nat × Bool × Expr))
  | recordUpdate (rec_ : Expr) (fields : List (FieldLabel × Nat × Bool × Expr)) (fieldsNum : Nat)
  | array (exprs : List Expr)
  -- Data access
  | field (rec_ : Expr) (accessor : Accessor) (pos : Nat)
  | mutate (rec_ : Expr) (label : FieldLabel) (fld : Expr) (pos : Nat)
  -- Assignment
  | assign (v : Var) (e : Expr)
  -- Sequencing
  | seq (exprs : List Expr) (last : Expr)
  -- Control flow
  | «if» (cond : Expr) (ifso : Expr) (ifnot : Option Expr)
  | switchConstr (obj : Expr)
      (cases : List (ConstrTag × Option Var × Expr)) (default : Option Expr)
  | switchConstant (obj : Expr) (cases : List (Moonbit.Clam.Const × Expr)) (default : Expr)
  | loop (params : List Param) (body : Expr) (args : List Expr) (label : LoopLabel)
  | «break» (arg : Option Expr) (label : LoopLabel)
  | «continue» (args : List Expr) (label : LoopLabel)
  -- Error handling
  | handleError (obj : Expr) (kind : HandleKind)
  | «return» (e : Expr) (kind : ReturnKind)
  -- Logical (short-circuit)
  | and (lhs : Expr) (rhs : Expr)
  | or (lhs : Expr) (rhs : Expr)

instance : Inhabited Expr := ⟨Expr.unit⟩

/-! ## Derived definitions -/

/-- A function: parameters + body (non-recursive wrapper). -/
structure Fn where
  params : List Param
  body : Expr

/-! ## Top-level items -/

structure TopFunDecl where
  binder : Var
  func : Fn

inductive TopItem where
  | expr (e : Expr)
  | «let» (binder : Var) (e : Expr) (isPub : Bool)
  | fn (decl : TopFunDecl)
  | stub (binder : Var) (name : String) (paramsTy : List Mtype) (returnTy : Option Mtype)

structure Program where
  topItems : List TopItem

end Moonbit.Mcore
