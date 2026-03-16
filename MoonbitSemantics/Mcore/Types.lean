/-
  MoonBit Compiler — Mcore Monomorphic Type System
  Formalization of `Mtype.t` from `src/mtype.ml`.
-/
import MoonbitSemantics.Clam.Syntax  -- reuse Const, Prim

namespace Moonbit.Mcore

/-! ## Identifiers -/

/-- Type definition identifier. -/
abbrev TypeId := Nat

/-- Variable / binder identifier. -/
abbrev Var := Nat

/-- Constructor tag. -/
abbrev ConstrTag := Nat

/-- Loop label. -/
abbrev LoopLabel := Nat

/-- Field label (for records). -/
abbrev FieldLabel := Nat

/-! ## Monomorphic types

All 24 constructors from `Mtype.t`. After monomorphization, no type variables remain.
-/

/-- Monomorphic types. -/
inductive Mtype where
  -- Scalar types
  | int
  | char
  | bool
  | unit
  | byte
  | int16
  | uint16
  | int64
  | uint
  | uint64
  | float
  | double
  -- Reference types
  | string
  | bytes
  -- Parameterized types
  | optimizedOption (elem : Mtype)
  | func (params : List Mtype) (ret : Mtype)
  | rawFunc (params : List Mtype) (ret : Mtype)
  | tuple (tys : List Mtype)
  | fixedarray (elem : Mtype)
  -- Named types
  | constr (id : TypeId)
  | trait (id : TypeId)
  | any (id : TypeId)
  -- Special
  | maybeUninit (t : Mtype)
  | errorValueResult (ok : Mtype) (err : Mtype) (id : TypeId)

instance : Inhabited Mtype := ⟨.unit⟩

/-! ## Type metadata -/

/-- Constructor info within a variant type. -/
structure ConstrInfo where
  tag : ConstrTag
  argTypes : List Mtype
  arity : Nat

/-- Field info within a record type. -/
structure FieldInfo where
  label : FieldLabel
  ty : Mtype
  isMut : Bool
  pos : Nat

/-- Method info within a trait. -/
structure MethodInfo where
  name : String
  ty : Mtype

/-- Type definition info. -/
inductive TypeInfo where
  | placeholder
  | externref
  | variant (constrs : List ConstrInfo)
  | record (fields : List FieldInfo)
  | trait (methods : List MethodInfo)

/-- Type definitions: map from TypeId to TypeInfo. -/
abbrev TypeDefs := TypeId → Option TypeInfo

end Moonbit.Mcore
