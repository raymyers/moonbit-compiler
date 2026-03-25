/-
  MoonBit Compiler — Mcore Typing Judgment
  Defines the typing relation for Mcore expressions and values,
  enabling type preservation and progress proofs.
-/
import MoonbitSemantics.Mcore.Values
import MoonbitSemantics.Mcore.Semantics

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp BitwiseOp)

/-! ## Typing environments

A typing environment maps variables to their declared types.
-/

/-- Typing environment: maps variables to Mtype. -/
abbrev TyEnv := Var → Option Mtype

def TyEnv.empty : TyEnv := fun _ => none

def TyEnv.extend (Γ : TyEnv) (x : Var) (τ : Mtype) : TyEnv :=
  fun y => if y = x then some τ else Γ y

def TyEnv.extendMany (Γ : TyEnv) (bindings : List (Var × Mtype)) : TyEnv :=
  bindings.foldl (fun acc (x, τ) => acc.extend x τ) Γ

def TyEnv.bindParams (Γ : TyEnv) (params : List Param) : TyEnv :=
  TyEnv.extendMany Γ (params.map fun p => (p.binder, p.ty))

/-! ## Constant typing -/

/-- The type of a constant literal. -/
def typeOfConst : Const → Mtype
  | .bool _ => .bool
  | .int _ => .int
  | .int64 _ => .int64
  | .float _ => .float
  | .double _ => .double
  | .string _ => .string
  | .char _ => .char
  | .byte _ => .byte
  | .unit => .unit

/-! ## Primitive operation typing -/

/-- Result type of an arithmetic operation. -/
def arithResultType : Mtype → Option Mtype
  | .int => some .int
  | .int64 => some .int64
  | .float => some .float
  | .double => some .double
  | _ => none

/-- Type of a primitive operation given argument types. -/
def typeOfPrim : Prim → List Mtype → Option Mtype
  | .arith _, [t, _] => arithResultType t  -- both args same type (enforced by HasTypeArgs)
  | .cmp _, [_, _] => some .bool
  | .not, [.bool] => some .bool
  | .neg, [.int] => some .int
  | .neg, [.int64] => some .int64
  | .neg, [.float] => some .float
  | .neg, [.double] => some .double
  | .ignore, [_] => some .unit
  | .identity, [t] => some t
  | .stringLength, [.string] => some .int
  | .stringEqual, [.string, .string] => some .bool
  | _, _ => none

/-! ## Join point typing environment -/

/-- Join point type entry: parameter types and result type. -/
structure JoinTyEntry where
  paramTys : List Mtype
  resultTy : Mtype

/-- Join point typing environment. -/
abbrev JoinTyEnv := Var → Option JoinTyEntry

def JoinTyEnv.empty : JoinTyEnv := fun _ => none

def JoinTyEnv.extend (Δ : JoinTyEnv) (j : Var) (e : JoinTyEntry) : JoinTyEnv :=
  fun j' => if j' = j then some e else Δ j'

/-! ## Loop typing environment -/

/-- Loop type entry: parameter types and result type. -/
structure LoopTyEntry where
  paramTys : List Mtype
  resultTy : Mtype

/-- Loop typing environment. -/
abbrev LoopTyEnv := LoopLabel → Option LoopTyEntry

def LoopTyEnv.empty : LoopTyEnv := fun _ => none

def LoopTyEnv.extend (Λ : LoopTyEnv) (l : LoopLabel) (e : LoopTyEntry) : LoopTyEnv :=
  fun l' => if l' = l then some e else Λ l'

/-! ## Function table typing -/

/-- Function type table: maps function vars to their parameter and return types. -/
abbrev FnTyTable := Var → Option (List Mtype × Mtype)

/-! ## Typing judgment

`HasType Γ Δ Λ F E e τ` means: in typing environment Γ, join env Δ,
loop env Λ, function table F, expected error type E, expression e has type τ.

The error type parameter E tracks the type of error values produced by `returnErr`
within an error-handling scope. Handlers (`handleError`) set E for their body,
and `returnErr` constrains the error value to match E.
-/

mutual

/-- Typing for argument lists. -/
inductive HasTypeArgs :
    TyEnv → JoinTyEnv → LoopTyEnv → FnTyTable → Option Mtype →
    List Expr → List Mtype → Prop where
  | nil :
    HasTypeArgs Γ Δ Λ F E [] []
  | cons :
    HasType Γ Δ Λ F E e τ →
    HasTypeArgs Γ Δ Λ F E es τs →
    HasTypeArgs Γ Δ Λ F E (e :: es) (τ :: τs)

/-- Typing judgment for Mcore expressions. -/
inductive HasType :
    TyEnv → JoinTyEnv → LoopTyEnv → FnTyTable → Option Mtype →
    Expr → Mtype → Prop where

  -- ═══════════ Literals ═══════════

  | const :
    HasType Γ Δ Λ F E (.const c) (typeOfConst c)

  | unit :
    HasType Γ Δ Λ F E .unit .unit

  -- ═══════════ Variables ═══════════

  | var :
    Γ x = some τ →
    HasType Γ Δ Λ F E (.var x none) τ

  | varPrim :
    Γ x = some τ →
    HasType Γ Δ Λ F E (.var x (some p)) τ

  -- ═══════════ Let binding ═══════════

  | «let» :
    Γ name = none →
    F name = none →
    HasType Γ Δ Λ F E rhs τ₁ →
    HasType (TyEnv.extend Γ name τ₁) Δ Λ F E body τ₂ →
    HasType Γ Δ Λ F E (.let name rhs body) τ₂

  -- ═══════════ Functions ═══════════

  | «function» :
    (∀ p, p ∈ params → F p.binder = none) →
    HasType (TyEnv.bindParams Γ params) JoinTyEnv.empty LoopTyEnv.empty F none fnBody retTy →
    HasType Γ Δ Λ F E (.function params fnBody false)
      (.func (params.map (·.ty)) retTy)

  | rawFunction :
    (∀ p, p ∈ params → F p.binder = none) →
    HasType (TyEnv.bindParams TyEnv.empty params) JoinTyEnv.empty LoopTyEnv.empty F none fnBody retTy →
    HasType Γ Δ Λ F E (.function params fnBody true)
      (.rawFunc (params.map (·.ty)) retTy)

  -- ═══════════ Local function bindings ═══════════

  | letfnNonrec :
    Γ name = none →
    F name = none →
    (∀ p, p ∈ params → F p.binder = none) →
    HasType (TyEnv.bindParams Γ params) JoinTyEnv.empty LoopTyEnv.empty F none fnBody retTy →
    HasType (TyEnv.extend Γ name (.func (params.map (·.ty)) retTy)) Δ Λ F E body τ →
    HasType Γ Δ Λ F E (.letfn name params fnBody body .nonRecursive) τ

  | letfnRec :
    Γ name = none →
    F name = none →
    (∀ p, p ∈ params → F p.binder = none) →
    HasType (TyEnv.bindParams (TyEnv.extend Γ name (.func (params.map (·.ty)) retTy)) params)
      JoinTyEnv.empty LoopTyEnv.empty F none fnBody retTy →
    HasType (TyEnv.extend Γ name (.func (params.map (·.ty)) retTy)) Δ Λ F E body τ →
    HasType Γ Δ Λ F E (.letfn name params fnBody body .recursive) τ

  | letfnTailJoin :
    Δ name = none →
    (∀ p, p ∈ params → F p.binder = none) →
    HasType (TyEnv.bindParams Γ params) Δ Λ F E fnBody τ →
    HasType Γ (JoinTyEnv.extend Δ name ⟨params.map (·.ty), τ⟩) Λ F E body τ →
    HasType Γ Δ Λ F E (.letfn name params fnBody body .tailJoin) τ

  | letfnNontailJoin :
    Δ name = none →
    (∀ p, p ∈ params → F p.binder = none) →
    HasType (TyEnv.bindParams Γ params) Δ Λ F E fnBody joinTy →
    HasType Γ (JoinTyEnv.extend Δ name ⟨params.map (·.ty), joinTy⟩) Λ F E body τ →
    HasType Γ Δ Λ F E (.letfn name params fnBody body .nontailJoin) τ

  -- ═══════════ Mutual recursion ═══════════

  | letrec :
    recΓ = TyEnv.extendMany Γ
      ((bindings.map (·.1)).zip (bindings.map fun (_, ps, _) => Mtype.func (ps.map (·.ty)) retTy)) →
    (∀ j (hj : j < bindings.length), Γ (bindings[j]'hj).1 = none) →
    (∀ j (hj : j < bindings.length), F (bindings[j]'hj).1 = none) →
    (∀ j (hj : j < bindings.length) p, p ∈ (bindings[j]'hj).2.1 → F p.binder = none) →
    (∀ i (h : i < bindings.length),
      HasType (TyEnv.bindParams recΓ (bindings[i].2.1))
        JoinTyEnv.empty LoopTyEnv.empty F none (bindings[i].2.2) retTy) →
    HasType recΓ Δ Λ F E body τ →
    HasType Γ Δ Λ F E (.letrec bindings body) τ

  -- ═══════════ Application ═══════════

  | applyClosure :
    Γ func = some (.func paramTys retTy) →
    HasTypeArgs Γ Δ Λ F E argExprs paramTys →
    HasType Γ Δ Λ F E (.apply func argExprs (.normal (.func paramTys retTy))) retTy

  | applyRawFn :
    Γ func = some (.rawFunc paramTys retTy) →
    HasTypeArgs Γ Δ Λ F E argExprs paramTys →
    HasType Γ Δ Λ F E (.apply func argExprs (.normal (.rawFunc paramTys retTy))) retTy

  | applyTopFn :
    F func = some (paramTys, retTy) →
    HasTypeArgs Γ Δ Λ F E argExprs paramTys →
    HasType Γ Δ Λ F E (.apply func argExprs (.normal (.func paramTys retTy))) retTy

  | applyJoin :
    Δ func = some ⟨paramTys, retTy⟩ →
    HasTypeArgs Γ Δ Λ F E argExprs paramTys →
    HasType Γ Δ Λ F E (.apply func argExprs .join) retTy

  -- ═══════════ Primitives ═══════════

  | prim :
    HasTypeArgs Γ Δ Λ F E argExprs argTys →
    typeOfPrim op argTys = some τ →
    HasType Γ Δ Λ F E (.prim op argExprs) τ

  -- ═══════════ Data construction ═══════════

  | constr :
    HasTypeArgs Γ Δ Λ F E argExprs argTys →
    HasType Γ Δ Λ F E (.constr tag argExprs) (.constr tid argTys)

  | tuple :
    HasTypeArgs Γ Δ Λ F E exprs τs →
    HasType Γ Δ Λ F E (.tuple exprs) (.tuple τs)

  | record :
    HasTypeArgs Γ Δ Λ F E (fieldExprs.map fun (_, _, _, e) => e) fieldTys →
    HasType Γ Δ Λ F E (.record fieldExprs) (.constr tid fieldTys)

  | recordUpdate :
    HasType Γ Δ Λ F E rec_ (.constr tid ats) →
    HasTypeArgs Γ Δ Λ F E (updFields.map fun (_, _, _, e) => e) _ →
    HasType Γ Δ Λ F E (.recordUpdate rec_ updFields fieldsNum) (.constr tid ats)

  | array :
    HasTypeArgs Γ Δ Λ F E exprs (List.replicate exprs.length elemTy) →
    HasType Γ Δ Λ F E (.array exprs) (.fixedarray elemTy)

  -- ═══════════ Field access ═══════════

  | fieldTuple :
    HasType Γ Δ Λ F E rec_ (.tuple τs) →
    τs[pos]? = some τ →
    HasType Γ Δ Λ F E (.field rec_ acc pos) τ

  /-- Field access from a constr or record (both have type .constr tid argTypes).
      argTypes constrains fieldTy via positional lookup. -/
  | fieldHeap :
    HasType Γ Δ Λ F E rec_ (.constr tid argTypes) →
    argTypes[pos]? = some fieldTy →
    HasType Γ Δ Λ F E (.field rec_ acc pos) fieldTy

  -- ═══════════ Mutation ═══════════

  | mutate :
    HasType Γ Δ Λ F E rec_ (.constr tid ats) →
    HasType Γ Δ Λ F E fld fieldTy →
    HasType Γ Δ Λ F E (.mutate rec_ label fld pos) .unit

  | assign :
    Γ x = some τ →
    HasType Γ Δ Λ F E e τ →
    HasType Γ Δ Λ F E (.assign x e) .unit

  -- ═══════════ Sequencing ═══════════

  | seq :
    HasTypeArgs Γ Δ Λ F E exprs _ →
    HasType Γ Δ Λ F E last τ →
    HasType Γ Δ Λ F E (.seq exprs last) τ

  -- ═══════════ Conditionals ═══════════

  | ifSome :
    HasType Γ Δ Λ F E condE .bool →
    HasType Γ Δ Λ F E ifso τ →
    HasType Γ Δ Λ F E ifnot τ →
    HasType Γ Δ Λ F E (.if condE ifso (some ifnot)) τ

  | ifNone :
    HasType Γ Δ Λ F E condE .bool →
    HasType Γ Δ Λ F E ifso .unit →
    HasType Γ Δ Λ F E (.if condE ifso none) .unit

  -- ═══════════ Pattern matching ═══════════

  /-- Switch on constructors: all branches (and default) must have type τ. -/
  | switchConstr :
    HasType Γ Δ Λ F E obj (.constr tid ats) →
    (∀ tag binder branch, findConstrCase cases tag = some (binder, branch) →
      HasType (match binder with
        | some x => TyEnv.extend Γ x (.constr tid ats)
        | none => Γ) Δ Λ F E branch τ) →
    (∀ d, dflt = some d → HasType Γ Δ Λ F E d τ) →
    HasType Γ Δ Λ F E (.switchConstr obj cases dflt) τ

  | switchConstant :
    HasType Γ Δ Λ F E obj objTy →
    (∀ i (h : i < cases.length),
      HasType Γ Δ Λ F E (cases[i]).2 τ) →
    HasType Γ Δ Λ F E dflt τ →
    HasType Γ Δ Λ F E (.switchConstant obj cases dflt) τ

  -- ═══════════ Loops ═══════════

  | loop :
    Λ label = none →
    (∀ p, p ∈ params → Γ p.binder = none) →
    (∀ p, p ∈ params → F p.binder = none) →
    HasTypeArgs Γ Δ Λ F E argExprs (params.map (·.ty)) →
    HasType (TyEnv.bindParams Γ params) Δ
      (LoopTyEnv.extend Λ label ⟨params.map (·.ty), τ⟩) F E body τ →
    HasType Γ Δ Λ F E (.loop params body argExprs label) τ

  | «break» :
    Λ label = some ⟨_, τ⟩ →
    HasType Γ Δ Λ F E arg τ →
    HasType Γ Δ Λ F E (.break (some arg) label) τ'

  | breakNone :
    Λ label = some ⟨_, .unit⟩ →
    HasType Γ Δ Λ F E (.break none label) τ'

  | «continue» :
    Λ label = some ⟨paramTys, _⟩ →
    HasTypeArgs Γ Δ Λ F E argExprs paramTys →
    HasType Γ Δ Λ F E (.continue argExprs label) τ'

  -- ═══════════ Logical operators ═══════════

  | and :
    HasType Γ Δ Λ F E lhs .bool →
    HasType Γ Δ Λ F E rhs .bool →
    HasType Γ Δ Λ F E (.and lhs rhs) .bool

  | or :
    HasType Γ Δ Λ F E lhs .bool →
    HasType Γ Δ Λ F E rhs .bool →
    HasType Γ Δ Λ F E (.or lhs rhs) .bool

  -- ═══════════ Error handling ═══════════

  /-- handleError toResult: obj is typed with error type errTy. -/
  | handleErrorToResult :
    HasType Γ Δ Λ F (some errTy) obj τ →
    HasType Γ Δ Λ F E (.handleError obj .toResult) (.errorValueResult τ errTy resultTid)

  /-- handleError joinapply: error type of obj must match join parameter type,
      and join return type must match the overall expression type. -/
  | handleErrorJoinapply :
    HasType Γ Δ Λ F (some errTy) obj τ →
    Δ target = some ⟨[errTy], τ⟩ →
    HasType Γ Δ Λ F E (.handleError obj (.joinapply target)) τ

  | handleErrorReturnErr :
    HasType Γ Δ Λ F (some errTy) obj τ →
    HasType Γ Δ Λ F (some errTy) (.handleError obj (.returnErr okTy)) τ

  -- ═══════════ Return ═══════════

  | returnSingle :
    HasType Γ Δ Λ F E e τ →
    HasType Γ Δ Λ F E (.return e .singleValue) τ

  /-- return Ok: sub-expression value is returned, so its type must match. -/
  | returnOk :
    HasType Γ Δ Λ F E e τ →
    HasType Γ Δ Λ F E (.return e (.errorResult false τ)) τ

  /-- return Error: raises an error; E constrains the error type. -/
  | returnErr :
    E = some errTy →
    HasType Γ Δ Λ F E e errTy →
    HasType Γ Δ Λ F E (.return e (.errorResult true retTy)) retTy

  -- ═══════════ Objects ═══════════

  | object :
    HasType Γ Δ Λ F E self τ →
    HasType Γ Δ Λ F E (.object self) τ

end -- mutual

/-! ## Value typing, outcome typing, environment typing

These are mutually dependent:
- `ValueHasType.closure` references `OutcomeHasType` and `Eval`
- `OutcomeHasType.val` references `ValueHasType`
- `EnvWellTyped` references `ValueHasType`
-/

mutual

/-- A runtime value has a given type.
    Closures carry an opaque `Prop` witness that the body is well-typed.
    This avoids strict positivity issues. -/
inductive ValueHasType : Value → Mtype → Prop where
  | const :
    ValueHasType (.const c) (typeOfConst c)
  | unit :
    ValueHasType .unit .unit
  | closure :
    ValueHasType (.closure captured params body) (.func (params.map (·.ty)) retTy)
  | rawFn :
    ValueHasType (.rawFn params body) (.rawFunc (params.map (·.ty)) retTy)
  | constr :
    ValueListHasType args argTypes →
    ValueHasType (.constr tag args) (.constr tid argTypes)
  | tuple :
    ValueListHasType vals τs →
    ValueHasType (.tuple vals) (.tuple τs)
  | locConstr :
    {σ : Loc → Option (List Mtype)} →
    σ l = some ats →
    ValueHasType (.loc l) (.constr tid ats)
  | locArray :
    ValueHasType (.loc l) (.fixedarray elemTy)
  | errorValueResultOk :
    ValueHasType v okTy →
    ValueHasType (.constr 0 [v]) (.errorValueResult okTy errTy tid)
  | errorValueResultErr :
    ValueHasType v errTy →
    ValueHasType (.constr 1 [v]) (.errorValueResult okTy errTy tid)

/-- Pointwise value typing on lists. -/
inductive ValueListHasType : List Value → List Mtype → Prop where
  | nil :
    ValueListHasType [] []
  | cons :
    ValueHasType v τ →
    ValueListHasType vs τs →
    ValueListHasType (v :: vs) (τ :: τs)

end

/-- An environment is well-typed wrt a typing environment. -/
def EnvWellTyped (env : Env) (Γ : TyEnv) : Prop :=
  ∀ x τ, Γ x = some τ → ∃ v, env x = some v ∧ ValueHasType v τ

/-- Top-level functions and env closures don't overlap for the same variable. -/
def FnEnvDisjoint (env : Env) (F : FnTyTable) : Prop :=
  (∀ func cap ps bd, env func = some (.closure cap ps bd) → F func = none) ∧
  (∀ func ps bd, env func = some (.rawFn ps bd) → F func = none)

/-- A single value satisfies the closure invariant.
    For closures, provides body typing + ClosureInvariant for captured env. -/
inductive ValClosureOk : Value → Mtype → FnTyTable → Prop where
  | not_closure :
    (∀ cap ps bd, v ≠ .closure cap ps bd) →
    (∀ vals, v ≠ .tuple vals) →
    (∀ ps bd, v ≠ .rawFn ps bd) →
    (∀ tag args, v ≠ .constr tag args) →
    ValClosureOk v τ F
  | tuple :
    (hvals : ∀ i (hv : i < vals.length) (hτ : i < τs.length),
      ValClosureOk (vals[i]'hv) (τs[i]'hτ) F) →
    ValClosureOk (.tuple vals) (.tuple τs) F
  | constr :
    (hvals : ∀ i (hv : i < args.length) (hτ : i < argTypes.length),
      ValClosureOk (args[i]'hv) (argTypes[i]'hτ) F) →
    ValClosureOk (.constr tag args) (.constr tid argTypes) F
  | errorValueResultOk :
    ValClosureOk v okTy F →
    ValClosureOk (.constr 0 [v]) (.errorValueResult okTy errTy tid) F
  | errorValueResultErr :
    ValClosureOk v errTy F →
    ValClosureOk (.constr 1 [v]) (.errorValueResult okTy errTy tid) F
  | closure :
    (hptys : paramTys = params.map (·.ty)) →
    (hcapWT : EnvWellTyped captured Γcap) →
    (hcapInv : ∀ x v' τ', captured x = some v' → Γcap x = some τ' → ValClosureOk v' τ' F) →
    (hcapDisj : FnEnvDisjoint captured F) →
    (hparams : ∀ p, p ∈ params → F p.binder = none) →
    (hbody : HasType (TyEnv.bindParams Γcap params)
        JoinTyEnv.empty LoopTyEnv.empty F none body retTy) →
    ValClosureOk (.closure captured params body) (.func paramTys retTy) F
  | rawFn :
    (hptys : paramTys = params.map (·.ty)) →
    (hparams : ∀ p, p ∈ params → F p.binder = none) →
    (hbody : HasType (TyEnv.bindParams TyEnv.empty params)
        JoinTyEnv.empty LoopTyEnv.empty F none body retTy) →
    ValClosureOk (.rawFn params body) (.rawFunc paramTys retTy) F
  | recClosure :
    (hptys : paramTys = params.map (·.ty)) →
    (hrecEnv : recEnv = Env.extend baseEnv name (.closure recEnv params body)) →
    (hbaseWT : EnvWellTyped baseEnv Γbase) →
    (hbaseInv : ∀ x v' τ', baseEnv x = some v' → Γbase x = some τ' → ValClosureOk v' τ' F) →
    (hbaseDisj : FnEnvDisjoint baseEnv F) →
    (hFname : F name = none) →
    (hparams : ∀ p, p ∈ params → F p.binder = none) →
    (hbody : HasType (TyEnv.bindParams (TyEnv.extend Γbase name (.func paramTys retTy)) params)
        JoinTyEnv.empty LoopTyEnv.empty F none body retTy) →
    ValClosureOk (.closure recEnv params body) (.func paramTys retTy) F
  | recMutualClosure
    {bindings : List (Var × List Param × Expr)} :
    (hptys : paramTys_i = params_i.map (·.ty)) →
    (hrecEnv : recEnv = Env.extendMany baseEnv
      (bindings.map fun (v, ps, b) => (v, Value.closure recEnv ps b))) →
    (hrecΓ : recΓ = TyEnv.extendMany Γbase
      ((bindings.map fun b => b.1).zip
        (bindings.map fun (_, ps, _) => Mtype.func (ps.map (·.ty)) retTy))) →
    (hidx : i < bindings.length) →
    (hbinding : (bindings[i]'hidx) = (name_i, params_i, body_i)) →
    (hbaseWT : EnvWellTyped baseEnv Γbase) →
    (hbaseInv : ∀ x v' τ', baseEnv x = some v' → Γbase x = some τ' → ValClosureOk v' τ' F) →
    (hbaseDisj : FnEnvDisjoint baseEnv F) →
    (hFnames : ∀ j (hj : j < bindings.length), F (bindings[j]'hj).1 = none) →
    (hparams : ∀ j (hj : j < bindings.length) p, p ∈ (bindings[j]'hj).2.1 → F p.binder = none) →
    (hbodies : ∀ j (hj : j < bindings.length),
      HasType (TyEnv.bindParams recΓ ((bindings[j]'(by omega)).2.1))
        JoinTyEnv.empty LoopTyEnv.empty F none ((bindings[j]'(by omega)).2.2) retTy) →
    ValClosureOk (.closure recEnv params_i body_i) (.func paramTys_i retTy) F

/-- Outcome typing. Break outcomes carry value typing from the Λ lookup. -/
inductive OutcomeHasType : Outcome → Mtype → LoopTyEnv → FnTyTable → Prop where
  | val : ValueHasType v τ → OutcomeHasType (.val v) τ Λ F
  | breakSome : Λ label = some ⟨paramTys, τ_break⟩ →
      ValueHasType v τ_break → ValClosureOk v τ_break F →
      OutcomeHasType (Outcome.break (some v) label) τ Λ F
  | breakNone : Λ label = some ⟨paramTys, .unit⟩ →
      OutcomeHasType (Outcome.break none label) τ Λ F
  | «continue» : Λ label = some ⟨paramTys, τ_loop⟩ →
      ValueListHasType args paramTys →
      (∀ i (hv : i < args.length) (hτ : i < paramTys.length),
        ValClosureOk (args[i]'hv) (paramTys[i]'hτ) F) →
      OutcomeHasType (.continue args label) τ Λ F
  | «return» : OutcomeHasType (.return _) τ Λ F
  | error : ValueHasType v errTy → OutcomeHasType (.error v) τ Λ F

/-- A closure is "semantically well-typed": calling with well-typed args
    produces well-typed outcomes. -/
def ClosureSemanticTyping
    (captured : Env) (params : List Param) (body : Expr)
    (retTy : Mtype) (F : FnTyTable) : Prop :=
  ∀ (ft : FnTable) (args : List Value) (s : Store) (jt : JoinTable)
    (lt : LoopTable) (nl : Loc) (outcome : Outcome) (s' : Store) (nl' : Loc),
    ValueListHasType args (params.map (·.ty)) →
    Eval ft (Env.bindParams captured params args) s jt lt nl body outcome s' nl' →
    OutcomeHasType outcome retTy LoopTyEnv.empty F

/-- Same for raw functions. -/
def RawFnSemanticTyping
    (params : List Param) (body : Expr) (retTy : Mtype) (F : FnTyTable) : Prop :=
  ∀ (ft : FnTable) (args : List Value) (s : Store) (jt : JoinTable)
    (lt : LoopTable) (nl : Loc) (outcome : Outcome) (s' : Store) (nl' : Loc),
    ValueListHasType args (params.map (·.ty)) →
    Eval ft (Env.bindParams Env.empty params args) s jt lt nl body outcome s' nl' →
    OutcomeHasType outcome retTy LoopTyEnv.empty F

end Moonbit.Mcore
