/-
  MoonBit Compiler — CLAM IR Syntax
  Formalization of the Closure-Lambda-Apply Machine intermediate representation.
-/
import Cslib.Foundations.Data.Relation

namespace Moonbit.Clam

/-! ## Identifiers -/

/-- Variable identifiers. -/
abbrev Var := Nat

/-- Function addresses (top-level function names). -/
abbrev Address := Nat

/-- Join point identifiers. -/
abbrev JoinId := Nat

/-- Loop labels. -/
abbrev Label := Nat

/-- Type definition identifiers. -/
abbrev Tid := Nat

/-- Constructor tags. -/
abbrev ConstrTag := Nat

/-! ## Types

The CLAM type system is a low-level, GC-aware type system with only 10 type formers.
-/

/-- Integer sub-kinds sharing the I32 representation. -/
inductive IntKind where
  | int | char | bool | unit | byte | int16 | uint16 | tag | optionChar
  deriving DecidableEq, Repr

/-- CLAM types — low-level, monomorphic, GC-representation-oriented. -/
inductive Ltype where
  | i32 (kind : IntKind)
  | i64
  | f32
  | f64
  | ref (tid : Tid)
  | refLazyInit (tid : Tid)
  | refNullable (tid : Tid)
  | refExtern
  | refString
  | refBytes
  | refFunc
  | refAny
  deriving DecidableEq, Repr

/-! ## Constants -/

/-- Constant literals. -/
inductive Const where
  | bool (v : Bool)
  | int (v : Int)
  | int64 (v : Int)
  | float (v : Float)
  | double (v : Float)
  | string (v : String)
  | char (v : Char)
  | byte (v : UInt8)
  | unit
  deriving Repr

/-! ## Primitive operations

We group primitives by category rather than enumerating all ~40 OCaml constructors.
This is the subset needed for semantic rules.
-/

/-- Arithmetic operators. -/
inductive ArithOp where
  | add | sub | mul | div | mod
  deriving DecidableEq, Repr

/-- Comparison operators. -/
inductive CmpOp where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- Bitwise operators. -/
inductive BitwiseOp where
  | and | or | xor | shl | shr
  deriving DecidableEq, Repr

/-- Primitive operations. -/
inductive Prim where
  | arith (op : ArithOp)
  | cmp (op : CmpOp)
  | bitwise (op : BitwiseOp)
  | not
  | neg
  | stringLength
  | stringEqual
  | ignore
  | identity
  | panic
  | unreachable
  deriving Repr

/-! ## Allocation kinds -/

/-- What kind of aggregate is being allocated. -/
inductive AllocKind where
  | tuple
  | struct
  | enum (tag : ConstrTag)
  deriving Repr

/-- What kind of field access is being performed. -/
inductive GetFieldKind where
  | tuple | struct | enum
  deriving Repr

/-- What kind of field mutation. -/
inductive SetFieldKind where
  | struct | enum
  deriving Repr

/-- Join point kind. -/
inductive JoinKind where
  | tail | nontail
  deriving Repr

/-! ## Call targets -/

/-- The target of a function application. -/
inductive Target where
  | dynamic (v : Var)
  | staticFn (addr : Address)
  deriving Repr

/-! ## Expressions (Lambda)

The core CLAM expression type. We encode a representative subset that captures
the essential semantic behavior. Compiler-internal annotations (tids, loc, type_)
are omitted — they don't affect the dynamic semantics.
-/

/-- Closure representation — captures + function address. -/
structure Closure where
  captures : List Var
  addr : Address
  deriving Repr, DecidableEq

/-- CLAM expressions. -/
inductive Lambda where
  -- Constants and variables
  | const (c : Const)
  | var (v : Var)
  -- Binding
  | «let» (name : Var) (e : Lambda) (body : Lambda)
  | letrec (names : List Var) (closures : List Closure) (body : Lambda)
  -- Allocation
  | allocate (kind : AllocKind) (fields : List Lambda)
  | closure (captures : List Var) (addr : Address)
  | getField (obj : Lambda) (index : Nat) (kind : GetFieldKind)
  | setField (obj : Lambda) (field : Lambda) (index : Nat) (kind : SetFieldKind)
  -- Function application
  | apply (target : Target) (args : List Lambda)
  -- Primitives
  | prim (op : Prim) (args : List Lambda)
  -- Control flow
  | «if» (pred : Lambda) (ifso : Lambda) (ifnot : Lambda)
  | seq (exprs : List Lambda) (last : Lambda)
  | loop (params : List Var) (body : Lambda) (args : List Lambda) (label : Label)
  | «break» (arg : Option Lambda) (label : Label)
  | «continue» (args : List Lambda) (label : Label)
  | «return» (e : Lambda)
  -- Join points
  | joinlet (name : JoinId) (params : List Var) (e : Lambda) (body : Lambda) (kind : JoinKind)
  | joinapply (name : JoinId) (args : List Lambda)
  -- Pattern matching
  | switch (obj : Var) (cases : List (ConstrTag × Lambda)) (default : Lambda)
  | switchInt (obj : Var) (cases : List (Int × Lambda)) (default : Lambda)
  -- Error handling
  | catch (body : Lambda) (handler : Lambda)
  -- Assignment
  | assign (v : Var) (e : Lambda)

instance : Inhabited Lambda where
  default := .const .unit

/-! ## Top-level definitions -/

/-- A top-level function. -/
structure TopFn where
  addr : Address
  params : List Var
  body : Lambda

/-- A complete CLAM program. -/
structure Prog where
  fns : List TopFn
  init : Lambda
  globals : List (Var × Option Const)

end Moonbit.Clam
