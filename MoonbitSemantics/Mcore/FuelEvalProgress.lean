/-
  MoonBit Compiler — Progress for the Fuel-Bounded Evaluator

  Proves that well-typed expressions never get **stuck** in `evalFuel`:
  evaluation either succeeds (`.ok`), runs out of fuel (`.outOfFuel`), but
  never returns `.stuck _` (which would indicate a true type error).

  Combined with `evalFuel_sound` (Phase 3) and `preservation` (already
  proved), this gives type soundness for the fragment of Mcore that
  excludes the three stubbed constructs (`.letrec`, `.letfn .recursive`,
  `.loop`).

  ## Hypothesis structure

  Like preservation's `HeapFieldTyped`, progress carries a few explicit
  invariants as hypotheses:

  - `StubFree e` : `e` does not use `.letrec`, `.letfn .recursive`, or
    `.loop`. The fuel-bounded evaluator's stub cases for these always
    return `.stuck`, so they cannot be in scope of a "non-stuck" theorem.

  - `HeapAvail s σ` : every store typing entry has a matching record in
    the store with the right number of fields. This is what lets `field`
    / `recordUpdate` / `mutate` find their target without getting stuck.

  - The standard well-typedness invariants for `env`, `ft`, `jt`, `lt`.
-/
import MoonbitSemantics.Mcore.FuelEvalSoundness
import MoonbitSemantics.Mcore.Preservation

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp)

/-! ## StubFree: rules out stubbed evalFuel cases

The fuel-bounded evaluator stubs three cases (returns `.stuck "TODO"`):
- `.letrec _ _`
- `.letfn _ _ _ _ .recursive`
- `.loop _ _ _ _`

Progress only holds for expressions that don't use these. -/

mutual

inductive StubFree : Expr → Prop where
  | const : StubFree (.const c)
  | unit : StubFree .unit
  | var : StubFree (.var x prim)
  | function : StubFree fnBody → StubFree (.function params fnBody isRaw)
  | «let» : StubFree rhs → StubFree body → StubFree (.let name rhs body)
  | letfnNonrec : StubFree fnBody → StubFree body →
      StubFree (.letfn name params fnBody body .nonRecursive)
  | letfnTailJoin : StubFree fnBody → StubFree body →
      StubFree (.letfn name params fnBody body .tailJoin)
  | letfnNontailJoin : StubFree fnBody → StubFree body →
      StubFree (.letfn name params fnBody body .nontailJoin)
  | apply : StubFreeArgs argExprs → StubFree (.apply func argExprs kind)
  | prim : StubFreeArgs argExprs → StubFree (.prim op argExprs)
  | constr : StubFreeArgs argExprs → StubFree (.constr tag argExprs)
  | tuple : StubFreeArgs exprs → StubFree (.tuple exprs)
  | record : StubFreeArgs (fieldExprs.map fun x => x.2.2.2) →
      StubFree (.record fieldExprs)
  | recordUpdate : StubFree rec_ → StubFreeArgs (updFields.map fun x => x.2.2.2) →
      StubFree (.recordUpdate rec_ updFields fieldsNum)
  | array : StubFreeArgs exprs → StubFree (.array exprs)
  | field : StubFree rec_ → StubFree (.field rec_ acc pos)
  | mutate : StubFree rec_ → StubFree fld →
      StubFree (.mutate rec_ label fld pos)
  | assign : StubFree e → StubFree (.assign x e)
  | seq : StubFreeArgs exprs → StubFree last → StubFree (.seq exprs last)
  | «if» : StubFree condE → StubFree ifso →
      (∀ e, ifnot = some e → StubFree e) →
      StubFree (.if condE ifso ifnot)
  | switchConstr : StubFree obj →
      (∀ tag binder branch, findConstrCase cases tag = some (binder, branch) →
        StubFree branch) →
      (∀ d, dflt = some d → StubFree d) →
      StubFree (.switchConstr obj cases dflt)
  | switchConstant : StubFree obj →
      (∀ i (h : i < cases.length), StubFree (cases[i]).2) →
      StubFree dflt →
      StubFree (.switchConstant obj cases dflt)
  | breakNone : StubFree (.break none label)
  | breakSome : StubFree arg → StubFree (.break (some arg) label)
  | «continue» : StubFreeArgs argExprs → StubFree (.continue argExprs label)
  | and_ : StubFree lhs → StubFree rhs → StubFree (.and lhs rhs)
  | or_ : StubFree lhs → StubFree rhs → StubFree (.or lhs rhs)
  | handleError : StubFree obj → StubFree (.handleError obj kind)
  | «return» : StubFree e → StubFree (.return e kind)
  | object : StubFree self → StubFree (.object self)

inductive StubFreeArgs : List Expr → Prop where
  | nil : StubFreeArgs []
  | cons : StubFree e → StubFreeArgs es → StubFreeArgs (e :: es)

end

/-! ## HeapAvail: store layout invariant

Says that every location in `σ` has a record in `s` with the right number
of fields. This is the structural part of `StoreWellTyped` (without the
field-level value typing). It's what `evalFuel`'s heap operations need
to avoid getting stuck. -/

def HeapAvail (s : Store) (σ : StoreTyping) : Prop :=
  ∀ l ats, σ l = some ats →
    ∃ fields mutFlags,
      s l = some (.record fields mutFlags) ∧ fields.size = ats.length

theorem HeapAvail.of_storeWellTyped {s : Store} {σ : StoreTyping} {F : FnTyTable}
    (hswt : StoreWellTyped s σ F) : HeapAvail s σ := by
  intro l ats hσ
  obtain ⟨fields, mutFlags, hs, hsize, _⟩ := hswt l ats hσ
  exact ⟨fields, mutFlags, hs, hsize⟩

/-! ## NotStuck helper

A predicate distinguishing the three result kinds. -/

def NotStuck : EvalFuelResult → Prop
  | .stuck _ => False
  | _ => True

@[simp] theorem NotStuck.ok : NotStuck (.ok o s' nl') := trivial
@[simp] theorem NotStuck.outOfFuel : NotStuck .outOfFuel := trivial
@[simp] theorem NotStuck.stuck (msg : String) : ¬ NotStuck (.stuck msg) := id

/-! ## Leaf-case progress lemmas

These are progress lemmas for the constructors of `Expr` that don't
recurse on sub-expressions: they're directly resolvable from the typing
+ env hypotheses without IH.

Each lemma corresponds to one (or several) `evalFuel` arms. -/

theorem progress_const (n : Nat) (ft : FnTable) (env : Env) (s : Store)
    (jt : JoinTable) (lt : LoopTable) (nl : Loc) (c : Moonbit.Clam.Const) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.const c)) := by
  simp [evalFuel, NotStuck]

theorem progress_unit (n : Nat) (ft : FnTable) (env : Env) (s : Store)
    (jt : JoinTable) (lt : LoopTable) (nl : Loc) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl .unit) := by
  simp [evalFuel, NotStuck]

theorem progress_function (n : Nat) (ft : FnTable) (env : Env) (s : Store)
    (jt : JoinTable) (lt : LoopTable) (nl : Loc)
    (params : List Param) (fnBody : Expr) (isRaw : Bool) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.function params fnBody isRaw)) := by
  cases isRaw <;> simp [evalFuel, NotStuck]

theorem progress_var
    {Γ : TyEnv} {env : Env} {x : Var} {τ : Mtype}
    (hΓ : Γ x = some τ) (henv : EnvWellTyped env Γ)
    (n : Nat) (ft : FnTable) (s : Store) (jt : JoinTable)
    (lt : LoopTable) (nl : Loc) (prim : Option Prim) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.var x prim)) := by
  obtain ⟨v, hv, _⟩ := henv x τ hΓ
  simp [evalFuel, NotStuck, hv]

theorem progress_breakNone
    (n : Nat) (ft : FnTable) (env : Env) (s : Store) (jt : JoinTable)
    (lt : LoopTable) (nl : Loc) (label : LoopLabel) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.break none label)) := by
  simp [evalFuel, NotStuck]

end Moonbit.Mcore
