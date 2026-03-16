/-
  MoonBit Compiler — CLAM IR Values and Runtime State
  Defines the semantic domains: values, store, environments, configurations.
-/
import MoonbitSemantics.Clam.Syntax

namespace Moonbit.Clam

/-! ## Runtime values -/

/-- Heap location. -/
abbrev Loc := Nat

/-- A runtime value produced by evaluating a CLAM expression. -/
inductive Value where
  | const (c : Const)
  | loc (l : Loc)
  | closureVal (captures : List Value) (addr : Address)
  | unit
  deriving Repr

/-! ## Store

The store maps heap locations to heap objects. Heap objects are aggregates
(tuples, structs, enums) and arrays.
-/

/-- A heap object — an aggregate with a kind tag and its field values. -/
inductive HeapObj where
  | aggregate (kind : AllocKind) (fields : Array Value)
  deriving Repr

/-- The heap store: a partial map from locations to heap objects. -/
abbrev Store := Loc → Option HeapObj

/-- Empty store. -/
def Store.empty : Store := fun _ => none

/-- Allocate a new object at a given fresh location. -/
def Store.alloc (s : Store) (l : Loc) (obj : HeapObj) : Store :=
  fun l' => if l' = l then some obj else s l'

/-- Update a field of an existing heap object. -/
def Store.update (s : Store) (l : Loc) (f : HeapObj → HeapObj) : Store :=
  fun l' => if l' = l then (s l).map f else s l'

/-! ## Environments

Variable environments map variables to values.
-/

/-- Environment: partial map from variables to values. -/
abbrev Env := Var → Option Value

/-- Empty environment. -/
def Env.empty : Env := fun _ => none

/-- Extend environment with a binding. -/
def Env.extend (env : Env) (x : Var) (v : Value) : Env :=
  fun y => if y = x then some v else env y

/-- Extend environment with multiple bindings. -/
def Env.extendMany (env : Env) (bindings : List (Var × Value)) : Env :=
  bindings.foldl (fun acc (x, v) => acc.extend x v) env

/-! ## Function table

Maps function addresses to their definitions.
-/

/-- Function table: maps addresses to (params, body). -/
abbrev FnTable := Address → Option (List Var × Lambda)

/-- Build a function table from a list of top-level functions. -/
def FnTable.ofTopFns (fns : List TopFn) : FnTable :=
  fun addr => fns.find? (fun f => f.addr == addr) |>.map (fun f => (f.params, f.body))

/-! ## Join point table -/

/-- Join point entry: parameters and body. -/
structure JoinEntry where
  params : List Var
  body : Lambda

/-- Join table: maps join IDs to their entries. -/
abbrev JoinTable := JoinId → Option JoinEntry

def JoinTable.empty : JoinTable := fun _ => none

def JoinTable.extend (jt : JoinTable) (j : JoinId) (e : JoinEntry) : JoinTable :=
  fun j' => if j' = j then some e else jt j'

/-! ## Evaluation context (continuation frames)

For the small-step semantics we track:
- `env`: current variable bindings
- `store`: the heap
- `joins`: active join points
- `fnTable`: top-level function defs
-/

/-- The machine configuration. -/
structure Config where
  expr : Lambda
  env : Env
  store : Store
  joins : JoinTable
  fnTable : FnTable
  nextLoc : Loc  -- next fresh heap location

end Moonbit.Clam
