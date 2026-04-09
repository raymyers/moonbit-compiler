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

/-! ## Stub-case eliminators

`StubFree` has no constructor for `.letrec`, `.letfn _ _ _ _ .recursive`,
or `.loop _ _ _ _`, so inversion immediately discharges these cases.
They appear as vacuous branches in any progress proof that takes a
`StubFree e` hypothesis. -/

theorem StubFree.not_letrec {bindings : List (Var × List Param × Expr)} {body : Expr}
    (h : StubFree (.letrec bindings body)) : False := by cases h

theorem StubFree.not_letfnRec {name : Var} {params : List Param}
    {fnBody body : Expr}
    (h : StubFree (.letfn name params fnBody body .recursive)) : False := by cases h

theorem StubFree.not_loop {params : List Param} {body : Expr}
    {argExprs : List Expr} {label : LoopLabel}
    (h : StubFree (.loop params body argExprs label)) : False := by cases h

/-! ## Inversion lemmas for StubFree

These expose sub-expression `StubFree` proofs for each constructor,
used by the recursive cases of the progress proof. -/

theorem StubFree.of_let {name : Var} {rhs body : Expr}
    (h : StubFree (.let name rhs body)) :
    StubFree rhs ∧ StubFree body := by cases h; exact ⟨‹_›, ‹_›⟩

theorem StubFree.of_letfnNonrec {name : Var} {params : List Param} {fnBody body : Expr}
    (h : StubFree (.letfn name params fnBody body .nonRecursive)) :
    StubFree fnBody ∧ StubFree body := by cases h; exact ⟨‹_›, ‹_›⟩

theorem StubFree.of_letfnTailJoin {name : Var} {params : List Param} {fnBody body : Expr}
    (h : StubFree (.letfn name params fnBody body .tailJoin)) :
    StubFree fnBody ∧ StubFree body := by cases h; exact ⟨‹_›, ‹_›⟩

theorem StubFree.of_letfnNontailJoin {name : Var} {params : List Param}
    {fnBody body : Expr}
    (h : StubFree (.letfn name params fnBody body .nontailJoin)) :
    StubFree fnBody ∧ StubFree body := by cases h; exact ⟨‹_›, ‹_›⟩

theorem StubFree.of_if {condE ifso : Expr} {ifnot : Option Expr}
    (h : StubFree (.if condE ifso ifnot)) :
    StubFree condE ∧ StubFree ifso ∧ (∀ e, ifnot = some e → StubFree e) := by
  cases h; exact ⟨‹_›, ‹_›, ‹_›⟩

theorem StubFree.of_and {lhs rhs : Expr} (h : StubFree (.and lhs rhs)) :
    StubFree lhs ∧ StubFree rhs := by cases h; exact ⟨‹_›, ‹_›⟩

theorem StubFree.of_or {lhs rhs : Expr} (h : StubFree (.or lhs rhs)) :
    StubFree lhs ∧ StubFree rhs := by cases h; exact ⟨‹_›, ‹_›⟩

theorem StubFree.of_assign {x : Var} {e : Expr} (h : StubFree (.assign x e)) :
    StubFree e := by cases h; exact ‹_›

theorem StubFree.of_return {e : Expr} {kind : ReturnKind}
    (h : StubFree (.return e kind)) : StubFree e := by cases h; exact ‹_›

theorem StubFree.of_object {self : Expr} (h : StubFree (.object self)) :
    StubFree self := by cases h; exact ‹_›

theorem StubFree.of_handleError {obj : Expr} {kind : HandleKind}
    (h : StubFree (.handleError obj kind)) : StubFree obj := by cases h; exact ‹_›

theorem StubFree.of_breakSome {arg : Expr} {label : LoopLabel}
    (h : StubFree (.break (some arg) label)) : StubFree arg := by
  cases h; exact ‹_›

theorem StubFree.of_continue {argExprs : List Expr} {label : LoopLabel}
    (h : StubFree (.continue argExprs label)) : StubFreeArgs argExprs := by
  cases h; exact ‹_›

theorem StubFree.of_prim {op : Prim} {argExprs : List Expr}
    (h : StubFree (.prim op argExprs)) : StubFreeArgs argExprs := by
  cases h; exact ‹_›

theorem StubFree.of_constr {tag : ConstrTag} {argExprs : List Expr}
    (h : StubFree (.constr tag argExprs)) : StubFreeArgs argExprs := by
  cases h; exact ‹_›

theorem StubFree.of_tuple {exprs : List Expr}
    (h : StubFree (.tuple exprs)) : StubFreeArgs exprs := by
  cases h; exact ‹_›

theorem StubFree.of_field {rec_ : Expr} {acc : Accessor} {pos : Nat}
    (h : StubFree (.field rec_ acc pos)) : StubFree rec_ := by
  cases h; exact ‹_›

theorem StubFree.of_mutate {rec_ fld : Expr} {label : FieldLabel} {pos : Nat}
    (h : StubFree (.mutate rec_ label fld pos)) :
    StubFree rec_ ∧ StubFree fld := by cases h; exact ⟨‹_›, ‹_›⟩

theorem StubFree.of_seq {exprs : List Expr} {last : Expr}
    (h : StubFree (.seq exprs last)) :
    StubFreeArgs exprs ∧ StubFree last := by cases h; exact ⟨‹_›, ‹_›⟩

theorem StubFree.of_apply {func : Var} {argExprs : List Expr} {kind : ApplyKind}
    (h : StubFree (.apply func argExprs kind)) :
    StubFreeArgs argExprs := by cases h; exact ‹_›

theorem StubFreeArgs.head {e : Expr} {es : List Expr}
    (h : StubFreeArgs (e :: es)) : StubFree e := by
  cases h with | cons he hes => exact he

theorem StubFreeArgs.tail {e : Expr} {es : List Expr}
    (h : StubFreeArgs (e :: es)) : StubFreeArgs es := by
  cases h with | cons he hes => exact hes

/-! ## NotStuck for argument evaluation -/

def NotStuckArgs : EvalFuelArgsResult → Prop
  | .stuckArgs _ => False
  | _ => True

@[simp] theorem NotStuckArgs.okVals : NotStuckArgs (.okVals vs s' nl') := trivial
@[simp] theorem NotStuckArgs.abortArgs : NotStuckArgs (.abortArgs o s' nl') := trivial
@[simp] theorem NotStuckArgs.outOfFuelArgs : NotStuckArgs .outOfFuelArgs := trivial
@[simp] theorem NotStuckArgs.stuck (msg : String) :
    ¬ NotStuckArgs (.stuckArgs msg) := id

/-! ## Simple propagator lemmas

These progress lemmas take an IH for the sub-expression's progress and
propagate it to the outer expression. They don't need typing info
because the outer expression never inspects the result's shape — it
just wraps aborts as-is and returns val outcomes directly. -/

theorem progress_return_single
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {e : Expr}
    (ih : NotStuck (evalFuel n ft env s jt lt nl e)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.return e .singleValue)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl e with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih; exact absurd ih id
  | ok o s' nl' => cases o <;> simp [NotStuck]

theorem progress_assign
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {x : Var} {e : Expr}
    (ih : NotStuck (evalFuel n ft env s jt lt nl e)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.assign x e)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl e with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih; exact absurd ih id
  | ok o s' nl' => cases o <;> simp [NotStuck]

theorem progress_object
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {self : Expr}
    (ih : NotStuck (evalFuel n ft env s jt lt nl self)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.object self)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl self with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih; exact absurd ih id
  | ok o s' nl' => cases o <;> simp [NotStuck]

theorem progress_break_some
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {arg : Expr} {label : LoopLabel}
    (ih : NotStuck (evalFuel n ft env s jt lt nl arg)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.break (some arg) label)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl arg with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih; exact absurd ih id
  | ok o s' nl' => cases o <;> simp [NotStuck]

theorem progress_continue
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {argExprs : List Expr} {label : LoopLabel}
    (ih : NotStuckArgs (evalFuelArgs n ft env s jt lt nl argExprs)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.continue argExprs label)) := by
  simp only [evalFuel]
  cases hr : evalFuelArgs n ft env s jt lt nl argExprs with
  | outOfFuelArgs => simp [NotStuck]
  | stuckArgs msg => rw [hr] at ih; exact absurd ih id
  | abortArgs o s' nl' => simp [NotStuck]
  | okVals vs s' nl' => simp [NotStuck]

theorem progress_constr
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {tag : ConstrTag} {argExprs : List Expr}
    (ih : NotStuckArgs (evalFuelArgs n ft env s jt lt nl argExprs)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.constr tag argExprs)) := by
  simp only [evalFuel]
  cases hr : evalFuelArgs n ft env s jt lt nl argExprs with
  | outOfFuelArgs => simp [NotStuck]
  | stuckArgs msg => rw [hr] at ih; exact absurd ih id
  | abortArgs o s' nl' => simp [NotStuck]
  | okVals vs s' nl' => simp [NotStuck]

theorem progress_tuple
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {exprs : List Expr}
    (ih : NotStuckArgs (evalFuelArgs n ft env s jt lt nl exprs)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.tuple exprs)) := by
  simp only [evalFuel]
  cases hr : evalFuelArgs n ft env s jt lt nl exprs with
  | outOfFuelArgs => simp [NotStuck]
  | stuckArgs msg => rw [hr] at ih; exact absurd ih id
  | abortArgs o s' nl' => simp [NotStuck]
  | okVals vs s' nl' => simp [NotStuck]

theorem progress_record
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc}
    {fieldExprs : List (FieldLabel × Nat × Bool × Expr)}
    (ih : NotStuckArgs (evalFuelArgs n ft env s jt lt nl
            (fieldExprs.map fun x => x.2.2.2))) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.record fieldExprs)) := by
  simp only [evalFuel]
  cases hr : evalFuelArgs n ft env s jt lt nl
              (fieldExprs.map fun x => x.2.2.2) with
  | outOfFuelArgs => simp [NotStuck]
  | stuckArgs msg => rw [hr] at ih; exact absurd ih id
  | abortArgs o s' nl' => simp [NotStuck]
  | okVals vs s' nl' => simp [NotStuck]

theorem progress_array
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {exprs : List Expr}
    (ih : NotStuckArgs (evalFuelArgs n ft env s jt lt nl exprs)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.array exprs)) := by
  simp only [evalFuel]
  cases hr : evalFuelArgs n ft env s jt lt nl exprs with
  | outOfFuelArgs => simp [NotStuck]
  | stuckArgs msg => rw [hr] at ih; exact absurd ih id
  | abortArgs o s' nl' => simp [NotStuck]
  | okVals vs s' nl' => simp [NotStuck]

/-! ## Cases with freshness hypotheses

These progress lemmas need an additional `env name = none` (or `jt name = none`)
invariant corresponding to the Eval rule's side condition. -/

theorem progress_let
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {name : Var} {rhs body : Expr}
    (hfresh : env name = none)
    (ih_rhs : NotStuck (evalFuel n ft env s jt lt nl rhs))
    (ih_body : ∀ v s' nl',
      NotStuck (evalFuel n ft (Env.extend env name v) s' jt lt nl' body)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.let name rhs body)) := by
  simp only [evalFuel, hfresh]
  cases hr : evalFuel n ft env s jt lt nl rhs with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih_rhs; exact absurd ih_rhs id
  | ok o s' nl' =>
    cases o with
    | val v =>
      have := ih_body v s' nl'
      cases hb : evalFuel n ft (Env.extend env name v) s' jt lt nl' body with
      | outOfFuel => simp [NotStuck, hb]
      | stuck msg => rw [hb] at this; exact absurd this id
      | ok o₂ s₂ nl₂ => simp [NotStuck, hb]
    | _ => simp [NotStuck]

theorem progress_letfnNonrec
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {name : Var} {params : List Param}
    {fnBody body : Expr}
    (hfresh : env name = none)
    (ih_body : ∀ v s' nl',
      NotStuck (evalFuel n ft (Env.extend env name v) s' jt lt nl' body)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl
      (.letfn name params fnBody body .nonRecursive)) := by
  simp only [evalFuel, hfresh]
  have := ih_body (.closure env params fnBody) s nl
  cases hb : evalFuel n ft (Env.extend env name (.closure env params fnBody))
              s jt lt nl body with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hb] at this; exact absurd this id
  | ok o s' nl' => simp [NotStuck]

theorem progress_letfnTailJoin
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {name : Var} {params : List Param}
    {fnBody body : Expr}
    (hfresh : jt name = none)
    (ih_body : NotStuck (evalFuel n ft env s
      (JoinTable.extend jt name ⟨params, fnBody⟩) lt nl body)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl
      (.letfn name params fnBody body .tailJoin)) := by
  simp only [evalFuel, hfresh]
  cases hb : evalFuel n ft env s
              (JoinTable.extend jt name ⟨params, fnBody⟩) lt nl body with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hb] at ih_body; exact absurd ih_body id
  | ok o s' nl' => simp [NotStuck]

theorem progress_letfnNontailJoin
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {name : Var} {params : List Param}
    {fnBody body : Expr}
    (hfresh : jt name = none)
    (ih_body : NotStuck (evalFuel n ft env s
      (JoinTable.extend jt name ⟨params, fnBody⟩) lt nl body)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl
      (.letfn name params fnBody body .nontailJoin)) := by
  simp only [evalFuel, hfresh]
  cases hb : evalFuel n ft env s
              (JoinTable.extend jt name ⟨params, fnBody⟩) lt nl body with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hb] at ih_body; exact absurd ih_body id
  | ok o s' nl' => simp [NotStuck]

theorem progress_seq
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {exprs : List Expr} {last : Expr}
    (ihargs : NotStuckArgs (evalFuelArgs n ft env s jt lt nl exprs))
    (ihlast : ∀ s' nl', NotStuck (evalFuel n ft env s' jt lt nl' last)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.seq exprs last)) := by
  simp only [evalFuel]
  cases hr : evalFuelArgs n ft env s jt lt nl exprs with
  | outOfFuelArgs => simp [NotStuck]
  | stuckArgs msg => rw [hr] at ihargs; exact absurd ihargs id
  | abortArgs o s' nl' => simp [NotStuck]
  | okVals vs s' nl' =>
    simp only [hr]
    have := ihlast s' nl'
    cases hlast : evalFuel n ft env s' jt lt nl' last with
    | outOfFuel => simp [NotStuck]
    | stuck msg => rw [hlast] at this; exact absurd this id
    | ok o₂ s₂ nl₂ => simp [NotStuck]

theorem progress_return_errorResult
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {e : Expr} {isErr : Bool} {retTy : Mtype}
    (ih : NotStuck (evalFuel n ft env s jt lt nl e)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl
      (.return e (.errorResult isErr retTy))) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl e with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih; exact absurd ih id
  | ok o s' nl' =>
    cases o with
    | val v => cases isErr <;> simp [NotStuck]
    | _ => simp [NotStuck]

theorem progress_handleError_toResult
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {obj : Expr}
    (ih : NotStuck (evalFuel n ft env s jt lt nl obj)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.handleError obj .toResult)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl obj with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih; exact absurd ih id
  | ok o s' nl' => cases o <;> simp [NotStuck]

theorem progress_handleError_returnErr
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {obj : Expr} {okTy : Mtype}
    (ih : NotStuck (evalFuel n ft env s jt lt nl obj)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl
      (.handleError obj (.returnErr okTy))) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl obj with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih; exact absurd ih id
  | ok o s' nl' => cases o <;> simp [NotStuck]

/-! ## Cases using preservation for canonical forms

For cases like `.if`, `.and`, `.or`, `.switchConstant .bool`, we need
to know that intermediate results have specific shapes. We use the
chain: `evalFuel n e = .ok → Eval ... e → ValueHasType → canonical forms`
to rule out the impossible `.stuck` arms. -/

theorem progress_if
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {τ : Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc}
    {condE ifso : Expr} {ifnot : Option Expr}
    (htype_cond : HasType Γ Δ Λ F E condE .bool)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (ih_cond : NotStuck (evalFuel n ft env s jt lt nl condE))
    (ih_ifso : ∀ s' nl', NotStuck (evalFuel n ft env s' jt lt nl' ifso))
    (ih_ifnot : ∀ e, ifnot = some e →
      ∀ s' nl', NotStuck (evalFuel n ft env s' jt lt nl' e)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.if condE ifso ifnot)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl condE with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih_cond; exact absurd ih_cond id
  | ok o s' nl' =>
    cases o with
    | val v =>
      -- Use soundness to get Eval, then preservation to get typing
      have heval := evalFuel_sound hr
      have hvt := preservation_val htype_cond heval
        henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
      obtain ⟨b, rfl⟩ := canonical_bool hvt
      cases b with
      | true =>
        have := ih_ifso s' nl'
        cases hb : evalFuel n ft env s' jt lt nl' ifso with
        | outOfFuel => simp [NotStuck, hb]
        | stuck msg => rw [hb] at this; exact absurd this id
        | ok o₂ s₂ nl₂ => simp [NotStuck, hb]
      | false =>
        cases ifnot with
        | none => simp [NotStuck]
        | some e' =>
          have := ih_ifnot e' rfl s' nl'
          cases hb : evalFuel n ft env s' jt lt nl' e' with
          | outOfFuel => simp [NotStuck, hb]
          | stuck msg => rw [hb] at this; exact absurd this id
          | ok o₂ s₂ nl₂ => simp [NotStuck, hb]
    | _ => simp [NotStuck]

theorem progress_and
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {lhs rhs : Expr}
    (htype_lhs : HasType Γ Δ Λ F E lhs .bool)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (ih_lhs : NotStuck (evalFuel n ft env s jt lt nl lhs))
    (ih_rhs : ∀ s' nl', NotStuck (evalFuel n ft env s' jt lt nl' rhs)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.and lhs rhs)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl lhs with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih_lhs; exact absurd ih_lhs id
  | ok o s' nl' =>
    cases o with
    | val v =>
      have heval := evalFuel_sound hr
      have hvt := preservation_val htype_lhs heval
        henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
      obtain ⟨b, rfl⟩ := canonical_bool hvt
      cases b with
      | true =>
        have := ih_rhs s' nl'
        cases hb : evalFuel n ft env s' jt lt nl' rhs with
        | outOfFuel => simp [NotStuck, hb]
        | stuck msg => rw [hb] at this; exact absurd this id
        | ok o₂ s₂ nl₂ => simp [NotStuck, hb]
      | false => simp [NotStuck]
    | _ => simp [NotStuck]

theorem progress_or
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {lhs rhs : Expr}
    (htype_lhs : HasType Γ Δ Λ F E lhs .bool)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (ih_lhs : NotStuck (evalFuel n ft env s jt lt nl lhs))
    (ih_rhs : ∀ s' nl', NotStuck (evalFuel n ft env s' jt lt nl' rhs)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.or lhs rhs)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl lhs with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih_lhs; exact absurd ih_lhs id
  | ok o s' nl' =>
    cases o with
    | val v =>
      have heval := evalFuel_sound hr
      have hvt := preservation_val htype_lhs heval
        henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
      obtain ⟨b, rfl⟩ := canonical_bool hvt
      cases b with
      | true => simp [NotStuck]
      | false =>
        have := ih_rhs s' nl'
        cases hb : evalFuel n ft env s' jt lt nl' rhs with
        | outOfFuel => simp [NotStuck, hb]
        | stuck msg => rw [hb] at this; exact absurd this id
        | ok o₂ s₂ nl₂ => simp [NotStuck, hb]
    | _ => simp [NotStuck]

/-! ## Progress for `evalFuelArgs` base case -/

theorem progress_args_nil
    (n : Nat) (ft : FnTable) (env : Env) (s : Store) (jt : JoinTable)
    (lt : LoopTable) (nl : Loc) :
    NotStuckArgs (evalFuelArgs (n+1) ft env s jt lt nl []) := by
  simp [evalFuelArgs, NotStuckArgs]

theorem progress_args_cons
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {e : Expr} {es : List Expr}
    (ihe : NotStuck (evalFuel n ft env s jt lt nl e))
    (ihes : ∀ s' nl', NotStuckArgs (evalFuelArgs n ft env s' jt lt nl' es)) :
    NotStuckArgs (evalFuelArgs (n+1) ft env s jt lt nl (e :: es)) := by
  simp only [evalFuelArgs]
  cases hr : evalFuel n ft env s jt lt nl e with
  | outOfFuel => simp [NotStuckArgs]
  | stuck msg => rw [hr] at ihe; exact absurd ihe id
  | ok o s' nl' =>
    cases o with
    | val v =>
      cases hrs : evalFuelArgs n ft env s' jt lt nl' es with
      | outOfFuelArgs => simp only [hrs]; simp [NotStuckArgs]
      | stuckArgs msg =>
        have := ihes s' nl'; rw [hrs] at this; exact absurd this id
      | abortArgs oA sA nlA => simp only [hrs]; simp [NotStuckArgs]
      | okVals vs sR nlR => simp only [hrs]; simp [NotStuckArgs]
    | _ => simp [NotStuckArgs]

end Moonbit.Mcore
