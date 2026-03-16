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

`HasType Γ Δ Λ F e τ` means: in typing environment Γ, join env Δ,
loop env Λ, function table F, expression e has type τ.

We also define `HasTypeOutcome` for outcomes.
-/

mutual

/-- Typing for argument lists. -/
inductive HasTypeArgs :
    TyEnv → JoinTyEnv → LoopTyEnv → FnTyTable →
    List Expr → List Mtype → Prop where
  | nil :
    HasTypeArgs Γ Δ Λ F [] []
  | cons :
    HasType Γ Δ Λ F e τ →
    HasTypeArgs Γ Δ Λ F es τs →
    HasTypeArgs Γ Δ Λ F (e :: es) (τ :: τs)

/-- Typing judgment for Mcore expressions. -/
inductive HasType :
    TyEnv → JoinTyEnv → LoopTyEnv → FnTyTable →
    Expr → Mtype → Prop where

  -- ═══════════ Literals ═══════════

  | const :
    HasType Γ Δ Λ F (.const c) (typeOfConst c)

  | unit :
    HasType Γ Δ Λ F .unit .unit

  -- ═══════════ Variables ═══════════

  | var :
    Γ x = some τ →
    HasType Γ Δ Λ F (.var x none) τ

  | varPrim :
    Γ x = some τ →
    HasType Γ Δ Λ F (.var x (some p)) τ

  -- ═══════════ Let binding ═══════════

  | «let» :
    HasType Γ Δ Λ F rhs τ₁ →
    HasType (TyEnv.extend Γ name τ₁) Δ Λ F body τ₂ →
    HasType Γ Δ Λ F (.let name rhs body) τ₂

  -- ═══════════ Functions ═══════════

  | «function» :
    HasType (TyEnv.bindParams Γ params) JoinTyEnv.empty LoopTyEnv.empty F fnBody retTy →
    HasType Γ Δ Λ F (.function params fnBody false)
      (.func (params.map (·.ty)) retTy)

  | rawFunction :
    HasType (TyEnv.bindParams Γ params) JoinTyEnv.empty LoopTyEnv.empty F fnBody retTy →
    HasType Γ Δ Λ F (.function params fnBody true)
      (.rawFunc (params.map (·.ty)) retTy)

  -- ═══════════ Local function bindings ═══════════

  | letfnNonrec :
    HasType (TyEnv.bindParams Γ params) JoinTyEnv.empty LoopTyEnv.empty F fnBody retTy →
    HasType (TyEnv.extend Γ name (.func (params.map (·.ty)) retTy)) Δ Λ F body τ →
    HasType Γ Δ Λ F (.letfn name params fnBody body .nonRecursive) τ

  | letfnRec :
    HasType (TyEnv.bindParams (TyEnv.extend Γ name (.func (params.map (·.ty)) retTy)) params)
      JoinTyEnv.empty LoopTyEnv.empty F fnBody retTy →
    HasType (TyEnv.extend Γ name (.func (params.map (·.ty)) retTy)) Δ Λ F body τ →
    HasType Γ Δ Λ F (.letfn name params fnBody body .recursive) τ

  | letfnTailJoin :
    HasType (TyEnv.bindParams Γ params) Δ Λ F fnBody τ →
    HasType Γ (JoinTyEnv.extend Δ name ⟨params.map (·.ty), τ⟩) Λ F body τ →
    HasType Γ Δ Λ F (.letfn name params fnBody body .tailJoin) τ

  | letfnNontailJoin :
    HasType (TyEnv.bindParams Γ params) Δ Λ F fnBody joinTy →
    HasType Γ (JoinTyEnv.extend Δ name ⟨params.map (·.ty), joinTy⟩) Λ F body τ →
    HasType Γ Δ Λ F (.letfn name params fnBody body .nontailJoin) τ

  -- ═══════════ Mutual recursion ═══════════

  | letrec :
    recΓ = TyEnv.extendMany Γ
      ((bindings.map (·.1)).zip (bindings.map fun (_, ps, _) => Mtype.func (ps.map (·.ty)) retTy)) →
    (∀ i (h : i < bindings.length),
      HasType (TyEnv.bindParams recΓ (bindings[i].2.1))
        JoinTyEnv.empty LoopTyEnv.empty F (bindings[i].2.2) retTy) →
    HasType recΓ Δ Λ F body τ →
    HasType Γ Δ Λ F (.letrec bindings body) τ

  -- ═══════════ Application ═══════════

  | applyClosure :
    Γ func = some (.func paramTys retTy) →
    HasTypeArgs Γ Δ Λ F argExprs paramTys →
    HasType Γ Δ Λ F (.apply func argExprs (.normal (.func paramTys retTy))) retTy

  | applyRawFn :
    Γ func = some (.rawFunc paramTys retTy) →
    HasTypeArgs Γ Δ Λ F argExprs paramTys →
    HasType Γ Δ Λ F (.apply func argExprs (.normal (.rawFunc paramTys retTy))) retTy

  | applyTopFn :
    F func = some (paramTys, retTy) →
    HasTypeArgs Γ Δ Λ F argExprs paramTys →
    HasType Γ Δ Λ F (.apply func argExprs (.normal (.func paramTys retTy))) retTy

  | applyJoin :
    Δ func = some ⟨paramTys, retTy⟩ →
    HasTypeArgs Γ Δ Λ F argExprs paramTys →
    HasType Γ Δ Λ F (.apply func argExprs .join) retTy

  -- ═══════════ Primitives ═══════════

  | prim :
    HasTypeArgs Γ Δ Λ F argExprs argTys →
    typeOfPrim op argTys = some τ →
    HasType Γ Δ Λ F (.prim op argExprs) τ

  -- ═══════════ Data construction ═══════════

  | constr :
    HasTypeArgs Γ Δ Λ F argExprs argTys →
    HasType Γ Δ Λ F (.constr tag argExprs) (.constr tid)

  | tuple :
    HasTypeArgs Γ Δ Λ F exprs τs →
    HasType Γ Δ Λ F (.tuple exprs) (.tuple τs)

  | record :
    HasTypeArgs Γ Δ Λ F (fieldExprs.map fun (_, _, _, e) => e) fieldTys →
    HasType Γ Δ Λ F (.record fieldExprs) (.constr tid)

  | recordUpdate :
    HasType Γ Δ Λ F rec_ (.constr tid) →
    HasTypeArgs Γ Δ Λ F (updFields.map fun (_, _, _, e) => e) _ →
    HasType Γ Δ Λ F (.recordUpdate rec_ updFields fieldsNum) (.constr tid)

  | array :
    HasTypeArgs Γ Δ Λ F exprs (List.replicate exprs.length elemTy) →
    HasType Γ Δ Λ F (.array exprs) (.fixedarray elemTy)

  -- ═══════════ Field access ═══════════

  | fieldTuple :
    HasType Γ Δ Λ F rec_ (.tuple τs) →
    τs[pos]? = some τ →
    HasType Γ Δ Λ F (.field rec_ acc pos) τ

  | fieldConstr :
    HasType Γ Δ Λ F rec_ (.constr tid) →
    HasType Γ Δ Λ F (.field rec_ acc pos) fieldTy

  | fieldRecord :
    HasType Γ Δ Λ F rec_ (.constr tid) →
    HasType Γ Δ Λ F (.field rec_ acc pos) fieldTy

  -- ═══════════ Mutation ═══════════

  | mutate :
    HasType Γ Δ Λ F rec_ (.constr tid) →
    HasType Γ Δ Λ F fld fieldTy →
    HasType Γ Δ Λ F (.mutate rec_ label fld pos) .unit

  | assign :
    Γ x = some τ →
    HasType Γ Δ Λ F e τ →
    HasType Γ Δ Λ F (.assign x e) .unit

  -- ═══════════ Sequencing ═══════════

  | seq :
    HasTypeArgs Γ Δ Λ F exprs _ →
    HasType Γ Δ Λ F last τ →
    HasType Γ Δ Λ F (.seq exprs last) τ

  -- ═══════════ Conditionals ═══════════

  | ifSome :
    HasType Γ Δ Λ F condE .bool →
    HasType Γ Δ Λ F ifso τ →
    HasType Γ Δ Λ F ifnot τ →
    HasType Γ Δ Λ F (.if condE ifso (some ifnot)) τ

  | ifNone :
    HasType Γ Δ Λ F condE .bool →
    HasType Γ Δ Λ F ifso .unit →
    HasType Γ Δ Λ F (.if condE ifso none) .unit

  -- ═══════════ Pattern matching ═══════════

  /-- Switch with match: we type each branch assuming the binder (if present) has the scrutinee type. -/
  | switchConstrCase :
    HasType Γ Δ Λ F obj (.constr tid) →
    findConstrCase cases tag = some (binder, branch) →
    HasType (match binder with
      | some x => TyEnv.extend Γ x (.constr tid)
      | none => Γ) Δ Λ F branch τ →
    HasType Γ Δ Λ F (.switchConstr obj cases dflt) τ

  | switchConstrDefault :
    HasType Γ Δ Λ F obj (.constr tid) →
    HasType Γ Δ Λ F d τ →
    HasType Γ Δ Λ F (.switchConstr obj cases (some d)) τ

  | switchConstant :
    HasType Γ Δ Λ F obj objTy →
    (∀ i (h : i < cases.length),
      let (_, branch) := cases[i]
      HasType Γ Δ Λ F branch τ) →
    HasType Γ Δ Λ F dflt τ →
    HasType Γ Δ Λ F (.switchConstant obj cases dflt) τ

  -- ═══════════ Loops ═══════════

  | loop :
    HasTypeArgs Γ Δ Λ F argExprs (params.map (·.ty)) →
    HasType (TyEnv.bindParams Γ params) Δ
      (LoopTyEnv.extend Λ label ⟨params.map (·.ty), τ⟩) F body τ →
    HasType Γ Δ Λ F (.loop params body argExprs label) τ

  | «break» :
    Λ label = some ⟨_, τ⟩ →
    HasType Γ Δ Λ F arg τ →
    HasType Γ Δ Λ F (.break (some arg) label) τ'

  | breakNone :
    Λ label = some ⟨_, .unit⟩ →
    HasType Γ Δ Λ F (.break none label) τ'

  | «continue» :
    Λ label = some ⟨paramTys, _⟩ →
    HasTypeArgs Γ Δ Λ F argExprs paramTys →
    HasType Γ Δ Λ F (.continue argExprs label) τ'

  -- ═══════════ Logical operators ═══════════

  | and :
    HasType Γ Δ Λ F lhs .bool →
    HasType Γ Δ Λ F rhs .bool →
    HasType Γ Δ Λ F (.and lhs rhs) .bool

  | or :
    HasType Γ Δ Λ F lhs .bool →
    HasType Γ Δ Λ F rhs .bool →
    HasType Γ Δ Λ F (.or lhs rhs) .bool

  -- ═══════════ Error handling ═══════════

  | handleErrorToResult :
    HasType Γ Δ Λ F obj τ →
    HasType Γ Δ Λ F (.handleError obj .toResult) (.constr resultTid)

  | handleErrorJoinapply :
    HasType Γ Δ Λ F obj τ →
    Δ target = some ⟨[errTy], _⟩ →
    HasType Γ Δ Λ F (.handleError obj (.joinapply target)) τ

  | handleErrorReturnErr :
    HasType Γ Δ Λ F obj τ →
    HasType Γ Δ Λ F (.handleError obj (.returnErr okTy)) τ

  -- ═══════════ Return ═══════════

  | returnSingle :
    HasType Γ Δ Λ F e τ →
    HasType Γ Δ Λ F (.return e .singleValue) τ

  | returnErrorResult :
    HasType Γ Δ Λ F e τ →
    HasType Γ Δ Λ F (.return e (.errorResult isErr retTy)) retTy

  -- ═══════════ Objects ═══════════

  | object :
    HasType Γ Δ Λ F self selfTy →
    HasType Γ Δ Λ F (.object self) (.trait tid)

end -- mutual

/-! ## Value typing

Defines when a runtime value has a given type.
-/

mutual

/-- A runtime value has a given type. -/
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
    ValueHasType (.constr tag args) (.constr tid)
  | tuple :
    ValueListHasType vals τs →
    ValueHasType (.tuple vals) (.tuple τs)
  | locConstr :
    ValueHasType (.loc l) (.constr tid)
  | locArray :
    ValueHasType (.loc l) (.fixedarray elemTy)

/-- Pointwise value typing on lists. -/
inductive ValueListHasType : List Value → List Mtype → Prop where
  | nil :
    ValueListHasType [] []
  | cons :
    ValueHasType v τ →
    ValueListHasType vs τs →
    ValueListHasType (v :: vs) (τ :: τs)

end

/-! ## Environment typing

An environment is well-typed if every binding agrees with the typing environment.
-/

/-- An environment is consistent with a typing environment. -/
def EnvWellTyped (env : Env) (Γ : TyEnv) : Prop :=
  ∀ x τ, Γ x = some τ → ∃ v, env x = some v ∧ ValueHasType v τ

/-! ## Type soundness statement (preservation + progress)

These are the main theorems we want to prove. They are stated here
as goals; proofs require induction on the `Eval` / `HasType` derivations.
-/

/-- Outcome typing: an outcome has a type consistent with the expected type. -/
inductive OutcomeHasType : Outcome → Mtype → Prop where
  | val : ValueHasType v τ → OutcomeHasType (.val v) τ
  | «break» : OutcomeHasType (.break _ _) τ
  | «continue» : OutcomeHasType (.continue _ _) τ
  | «return» : OutcomeHasType (.return _) τ
  | error : OutcomeHasType (.error _) τ

end Moonbit.Mcore
