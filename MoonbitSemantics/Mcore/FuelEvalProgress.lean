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

/-- **HeapLocPresent**: every location with a `.constr tid ats` type has
    a record in the store with the right number of fields.

    This is the "backward" direction of heap typing (type → store) that
    `HeapFieldTyped` doesn't cover. It's the progress analog of
    `HeapFieldTyped`: callers of progress must supply it as an explicit
    invariant, paralleling how `preservation` takes `HeapFieldTyped`.

    Becomes derivable once `ValueHasType.locConstr` is parameterized by
    a store typing σ linked to the runtime store (same refactor as for
    `HeapFieldTyped`). -/
def HeapLocPresent (s : Store) : Prop :=
  ∀ (l : Loc) (tid : Nat) (ats : List Mtype),
    ValueHasType (.loc l) (.constr tid ats) →
    ∃ fields mutFlags, s l = some (.record fields mutFlags) ∧
      fields.size = ats.length

/-! ## NotStuck helper

A predicate distinguishing the three result kinds. -/

def NotStuck : EvalFuelResult → Prop
  | .stuck _ => False
  | _ => True

@[simp] theorem NotStuck.ok : NotStuck (.ok o s' nl') := trivial
@[simp] theorem NotStuck.outOfFuel : NotStuck .outOfFuel := trivial
@[simp] theorem NotStuck.stuck (msg : String) : ¬ NotStuck (.stuck msg) := id

/-! ## ProgressCtx: bundled hypothesis set

Most progress lemmas for non-leaf cases share the same hypothesis bundle
inherited from preservation. `ProgressCtx` packages these into a single
structure so they can be threaded through recursive calls compactly.

Note that this context is **store-independent** — it doesn't carry
`StoreWellTyped` or `HeapAvail`. Progress for heap-touching operations
(`.field` on `.constr`/`.loc`, `.recordUpdate`, `.mutate`) additionally
needs a store-typing invariant linked to the runtime store, which the
current formalization handles as an existential in `ValueHasType.locConstr`
and a `HeapFieldTyped` conditional hypothesis (see memory/preservation). -/

structure ProgressCtx (Γ : TyEnv) (Δ : JoinTyEnv) (Λ : LoopTyEnv) (F : FnTyTable)
    (ft : FnTable) (env : Env) (jt : JoinTable) (lt : LoopTable) where
  envWT : EnvWellTyped env Γ
  ftWT : FnTableWellTyped ft F
  clInv : ClosureInvariant env Γ F
  fnDisj : FnEnvDisjoint env F
  ftC : FnTableComplete ft F
  jwt : JoinWellTyped jt Δ Γ Λ F
  jdc : JoinDeltaConsistent jt Δ
  llc : LoopLabelConsistent lt Λ
  hft : HeapFieldTyped F

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
    {E : Option Mtype}
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

/-- A type whose values are always `.const c` for some `c`. These are the
    scalar types that are represented as `Value.const`. -/
def IsConstType : Mtype → Prop
  | .bool => True
  | .int => True
  | .int64 => True
  | .string => True
  | .char => True
  | .byte => True
  | .float => True
  | .double => True
  | _ => False

/-- If `v` has a const type, it's a `.const c` value. -/
theorem canonical_const {v : Value} {τ : Mtype}
    (hct : IsConstType τ) (h : ValueHasType v τ) :
    ∃ c, v = .const c := by
  match τ, hct, h with
  | .bool, _, h => obtain ⟨b, rfl⟩ := canonical_bool h; exact ⟨_, rfl⟩
  | .int, _, h => obtain ⟨n, rfl⟩ := canonical_int h; exact ⟨_, rfl⟩
  | .int64, _, h => obtain ⟨n, rfl⟩ := canonical_int64 h; exact ⟨_, rfl⟩
  | .string, _, h => obtain ⟨s, rfl⟩ := canonical_string h; exact ⟨_, rfl⟩
  | .char, _, h => obtain ⟨c, rfl⟩ := canonical_char h; exact ⟨_, rfl⟩
  | .byte, _, h => obtain ⟨b, rfl⟩ := canonical_byte h; exact ⟨_, rfl⟩
  | .float, _, h => obtain ⟨f, rfl⟩ := canonical_float h; exact ⟨_, rfl⟩
  | .double, _, h => obtain ⟨d, rfl⟩ := canonical_double h; exact ⟨_, rfl⟩

/-- Progress for `.switchConstr obj cases (some d)` — i.e. with a default
    branch — when `obj` has a `.constr tid ats` type AND the runtime value
    is a `.constr tag args`. The `.loc` subcase is not supported by
    evalFuel's switchConstr implementation; the no-default case is a
    latent soundness gap (switchConstr with a missing default and no
    matching tag is runtime-stuck but accepted by the typing). -/
theorem progress_switchConstr_withDefault
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {tid : Nat} {ats : List Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {obj : Expr} {d : Expr}
    {cases_ : List (ConstrTag × Option Var × Expr)}
    (htype_obj : HasType Γ Δ Λ F E obj (.constr tid ats))
    (hnot_loc : ∀ o s' nl',
      evalFuel n ft env s jt lt nl obj = .ok o s' nl' →
      ∀ l, o ≠ .val (.loc l))
    (hbinder_fresh : ∀ tag branch x,
      findConstrCase cases_ tag = some (some x, branch) → env x = none)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (ih_obj : NotStuck (evalFuel n ft env s jt lt nl obj))
    (ih_branch : ∀ tag binder branch tag' args s' nl',
      findConstrCase cases_ tag = some (binder, branch) →
      NotStuck (evalFuel n ft
        (match binder with
          | some x => Env.extend env x (.constr tag' args)
          | none => env)
        s' jt lt nl' branch))
    (ih_dflt : ∀ s' nl', NotStuck (evalFuel n ft env s' jt lt nl' d)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl
      (.switchConstr obj cases_ (some d))) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl obj with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih_obj; exact absurd ih_obj id
  | ok o s' nl' =>
    cases o with
    | val v =>
      have heval := evalFuel_sound hr
      have hvt := preservation_val htype_obj heval
        henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
      rcases canonical_constr hvt with
        ⟨tag, args, rfl, hargs⟩ | ⟨l, rfl⟩
      · -- .constr case
        cases hfc : findConstrCase cases_ tag with
        | none =>
          have := ih_dflt s' nl'
          cases hb : evalFuel n ft env s' jt lt nl' d with
          | outOfFuel => simp [NotStuck, hfc, hb]
          | stuck msg => rw [hb] at this; exact absurd this id
          | ok o₂ s₂ nl₂ => simp [NotStuck, hfc, hb]
        | some entry =>
          obtain ⟨binder, branch⟩ := entry
          cases binder with
          | some x =>
            have hxfresh : env x = none :=
              hbinder_fresh tag branch x hfc
            have := ih_branch tag (some x) branch tag args s' nl' hfc
            simp only at this
            cases hb : evalFuel n ft (Env.extend env x (.constr tag args))
                        s' jt lt nl' branch with
            | outOfFuel => simp [NotStuck, hfc, hxfresh, hb]
            | stuck msg => rw [hb] at this; exact absurd this id
            | ok o₂ s₂ nl₂ => simp [NotStuck, hfc, hxfresh, hb]
          | none =>
            have := ih_branch tag none branch tag args s' nl' hfc
            simp only at this
            cases hb : evalFuel n ft env s' jt lt nl' branch with
            | outOfFuel => simp [NotStuck, hfc, hb]
            | stuck msg => rw [hb] at this; exact absurd this id
            | ok o₂ s₂ nl₂ => simp [NotStuck, hfc, hb]
      · exact absurd rfl (hnot_loc _ _ _ hr l)
    | _ => simp [NotStuck]

theorem progress_field_heap_constrValue
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {τ fieldTy : Mtype} {tid : Nat} {ats : List Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {rec_ : Expr} {acc : Accessor} {pos : Nat}
    (htype_rec : HasType Γ Δ Λ F E rec_ (.constr tid ats))
    (hpos : ats[pos]? = some fieldTy)
    (hnot_loc : ∀ o s' nl',
      evalFuel n ft env s jt lt nl rec_ = .ok o s' nl' →
      ∀ l, o ≠ .val (.loc l))
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (ih : NotStuck (evalFuel n ft env s jt lt nl rec_)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.field rec_ acc pos)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl rec_ with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih; exact absurd ih id
  | ok o s' nl' =>
    cases o with
    | val v =>
      have heval := evalFuel_sound hr
      have hvt := preservation_val htype_rec heval
        henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
      rcases canonical_constr hvt with
        ⟨tag, args, rfl, hargs⟩ | ⟨l, rfl⟩
      · -- .constr case — handle bounds
        have hlen_args : pos < args.length := by
          have hlen_ats : pos < ats.length := by
            by_contra hlt; push_neg at hlt
            simp [List.getElem?_eq_none_iff.mpr (by omega)] at hpos
          rw [hargs.length_eq]; exact hlen_ats
        have hgetv : args[pos]? = some (args[pos]'hlen_args) := by
          simp [List.getElem?_eq_getElem hlen_args]
        simp [hgetv, NotStuck]
      · -- .loc case — ruled out by hnot_loc
        exact absurd rfl (hnot_loc _ _ _ hr l)
    | _ => simp [NotStuck]

theorem progress_switchConstant
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {objTy : Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {obj : Expr}
    {cases_ : List (Moonbit.Clam.Const × Expr)} {dflt : Expr}
    (htype_obj : HasType Γ Δ Λ F E obj objTy)
    (hct : IsConstType objTy)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (ih_obj : NotStuck (evalFuel n ft env s jt lt nl obj))
    (ih_branches : ∀ i (hi : i < cases_.length) s' nl',
      NotStuck (evalFuel n ft env s' jt lt nl' (cases_[i]'hi).2))
    (ih_dflt : ∀ s' nl', NotStuck (evalFuel n ft env s' jt lt nl' dflt)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl
      (.switchConstant obj cases_ dflt)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl obj with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih_obj; exact absurd ih_obj id
  | ok o s' nl' =>
    cases o with
    | val v =>
      have heval := evalFuel_sound hr
      have hvt := preservation_val htype_obj heval
        henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
      obtain ⟨c, rfl⟩ := canonical_const hct hvt
      cases hfc : findConstantCase cases_ c with
      | none =>
        have := ih_dflt s' nl'
        cases hb : evalFuel n ft env s' jt lt nl' dflt with
        | outOfFuel => simp [NotStuck, hfc, hb]
        | stuck msg => rw [hb] at this; exact absurd this id
        | ok o₂ s₂ nl₂ => simp [NotStuck, hfc, hb]
      | some branch =>
        obtain ⟨i, hi, heq⟩ := findConstantCase_index cases_ c branch hfc
        have := ih_branches i hi s' nl'
        rw [heq] at this
        cases hb : evalFuel n ft env s' jt lt nl' branch with
        | outOfFuel => simp [NotStuck, hfc, hb]
        | stuck msg => rw [hb] at this; exact absurd this id
        | ok o₂ s₂ nl₂ => simp [NotStuck, hfc, hb]
    | _ => simp [NotStuck]

theorem progress_handleError_joinapply
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {τ errTy : Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {obj : Expr} {target : Var}
    (htype_obj : HasType Γ Δ Λ F (some errTy) obj τ)
    (hΔ : Δ target = some ⟨[errTy], τ⟩)
    (hjparams_env_fresh : ∀ jparams jbody, jt target = some ⟨jparams, jbody⟩ →
      ∀ p, p ∈ jparams → env p.binder = none)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (ih_obj : NotStuck (evalFuel n ft env s jt lt nl obj))
    (ih_body : ∀ jparams jbody s' nl' v,
      jt target = some ⟨jparams, jbody⟩ →
      jparams.length = 1 →
      NotStuck (evalFuel n ft (Env.bindParams env jparams [v]) s' jt lt nl' jbody)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl
      (.handleError obj (.joinapply target))) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl obj with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih_obj; exact absurd ih_obj id
  | ok o s' nl' =>
    cases o with
    | val v => simp [NotStuck]
    | error v =>
      -- Get jt target from JoinDeltaConsistent
      obtain ⟨jparams, jbody, hjt_target⟩ := hjdc target ⟨[errTy], τ⟩ hΔ
      simp only [hjt_target]
      -- jparams fresh
      have hfresh_env := hjparams_env_fresh jparams jbody hjt_target
      have hfresh_not_any : ¬ ((jparams.any fun p => (env p.binder).isSome) = true) := by
        simp only [List.any_eq_true, not_exists]
        intro p ⟨hp, hsome⟩
        rw [hfresh_env p hp] at hsome
        exact absurd hsome (by simp)
      simp only [if_neg hfresh_not_any]
      -- jparams.length = 1
      obtain ⟨hjp_map, _, _⟩ := hjwt.extract hjt_target hΔ
      have hjparams_len : jparams.length = 1 := by
        have : jparams.map (·.ty) = [errTy] := hjp_map
        have := congrArg List.length this
        simp at this; exact this
      have := ih_body jparams jbody s' nl' v hjt_target hjparams_len
      cases hb : evalFuel n ft (Env.bindParams env jparams [v]) s' jt lt nl' jbody with
      | outOfFuel => simp [NotStuck, hb]
      | stuck msg => rw [hb] at this; exact absurd this id
      | ok o₂ s₂ nl₂ => simp [NotStuck, hb]
    | _ => simp [NotStuck]

theorem progress_apply_closure
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {paramTys : List Mtype} {retTy : Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {func : Var} {argExprs : List Expr}
    {captured : Env} {params : List Param} {fnBody : Expr}
    (hΓ : Γ func = some (.func paramTys retTy))
    (htype_args : HasTypeArgs Γ Δ Λ F E argExprs paramTys)
    (hEnvFunc : env func = some (.closure captured params fnBody))
    (hparams_map : params.map (·.ty) = paramTys)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (ih_args : NotStuckArgs (evalFuelArgs n ft env s jt lt nl argExprs))
    (ih_body : ∀ s' nl' vs,
      params.length = vs.length →
      NotStuck (evalFuel n ft (Env.bindParams captured params vs)
        s' JoinTable.empty LoopTable.empty nl' fnBody)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl
      (.apply func argExprs (.normal (.func paramTys retTy)))) := by
  simp only [evalFuel, hEnvFunc]
  cases hr : evalFuelArgs n ft env s jt lt nl argExprs with
  | outOfFuelArgs => simp [NotStuck]
  | stuckArgs msg => rw [hr] at ih_args; exact absurd ih_args id
  | abortArgs o s' nl' => simp [NotStuck]
  | okVals argVals s' nl' =>
    simp only [hr]
    have hevalArgs := evalFuelArgs_sound_ok hr
    have hapres := preservationArgs htype_args hevalArgs
      henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
    have hvals_len : argVals.length = paramTys.length := hapres.hasTypes.length_eq
    have hparams_len : params.length = paramTys.length := by
      rw [← hparams_map]; simp
    have hlen : params.length = argVals.length := by omega
    simp only [hlen, if_true]
    have := ih_body s' nl' argVals hlen
    cases hb : evalFuel n ft (Env.bindParams captured params argVals) s'
                JoinTable.empty LoopTable.empty nl' fnBody with
    | outOfFuel => simp [NotStuck, hb]
    | stuck msg => rw [hb] at this; exact absurd this id
    | ok o₂ s₂ nl₂ => simp [NotStuck, hb]

theorem progress_apply_rawFn
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {paramTys : List Mtype} {retTy : Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {func : Var} {argExprs : List Expr}
    {params : List Param} {fnBody : Expr}
    (hΓ : Γ func = some (.rawFunc paramTys retTy))
    (htype_args : HasTypeArgs Γ Δ Λ F E argExprs paramTys)
    (hEnvFunc : env func = some (.rawFn params fnBody))
    (hparams_map : params.map (·.ty) = paramTys)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (ih_args : NotStuckArgs (evalFuelArgs n ft env s jt lt nl argExprs))
    (ih_body : ∀ s' nl' vs,
      params.length = vs.length →
      NotStuck (evalFuel n ft (Env.bindParams Env.empty params vs)
        s' JoinTable.empty LoopTable.empty nl' fnBody)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl
      (.apply func argExprs (.normal (.rawFunc paramTys retTy)))) := by
  simp only [evalFuel, hEnvFunc]
  cases hr : evalFuelArgs n ft env s jt lt nl argExprs with
  | outOfFuelArgs => simp [NotStuck]
  | stuckArgs msg => rw [hr] at ih_args; exact absurd ih_args id
  | abortArgs o s' nl' => simp [NotStuck]
  | okVals argVals s' nl' =>
    simp only [hr]
    have hevalArgs := evalFuelArgs_sound_ok hr
    have hapres := preservationArgs htype_args hevalArgs
      henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
    have hvals_len : argVals.length = paramTys.length := hapres.hasTypes.length_eq
    have hparams_len : params.length = paramTys.length := by
      rw [← hparams_map]; simp
    have hlen : params.length = argVals.length := by omega
    simp only [hlen, if_true]
    have := ih_body s' nl' argVals hlen
    cases hb : evalFuel n ft (Env.bindParams Env.empty params argVals) s'
                JoinTable.empty LoopTable.empty nl' fnBody with
    | outOfFuel => simp [NotStuck, hb]
    | stuck msg => rw [hb] at this; exact absurd this id
    | ok o₂ s₂ nl₂ => simp [NotStuck, hb]

theorem progress_apply_join
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {paramTys : List Mtype} {retTy : Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {func : Var} {argExprs : List Expr}
    (hΔ : Δ func = some ⟨paramTys, retTy⟩)
    (htype_args : HasTypeArgs Γ Δ Λ F E argExprs paramTys)
    (hjparams_env_fresh : ∀ jparams jbody, jt func = some ⟨jparams, jbody⟩ →
      ∀ p, p ∈ jparams → env p.binder = none)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (ih_args : NotStuckArgs (evalFuelArgs n ft env s jt lt nl argExprs))
    (ih_body : ∀ jparams jbody s' nl' vs,
      jt func = some ⟨jparams, jbody⟩ →
      jparams.length = vs.length →
      NotStuck (evalFuel n ft (Env.bindParams env jparams vs) s' jt lt nl' jbody)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.apply func argExprs .join)) := by
  simp only [evalFuel]
  -- Get jt func from JoinDeltaConsistent
  obtain ⟨jparams, jbody, hjt_func⟩ := hjdc func ⟨paramTys, retTy⟩ hΔ
  simp only [hjt_func]
  -- From JoinWellTyped.extract, get params.map (·.ty) = paramTys
  obtain ⟨hjp_map, _, _⟩ := hjwt.extract hjt_func hΔ
  -- Get env freshness for jparams
  have hfresh_env : ∀ p, p ∈ jparams → env p.binder = none :=
    hjparams_env_fresh jparams jbody hjt_func
  have hfresh_not_any : ¬ ((jparams.any fun p => (env p.binder).isSome) = true) := by
    simp only [List.any_eq_true, not_exists]
    intro p ⟨hp, hsome⟩
    have := hfresh_env p hp
    rw [this] at hsome
    exact absurd hsome (by simp)
  simp only [if_neg hfresh_not_any]
  cases hr : evalFuelArgs n ft env s jt lt nl argExprs with
  | outOfFuelArgs => simp [NotStuck]
  | stuckArgs msg => rw [hr] at ih_args; exact absurd ih_args id
  | abortArgs o s' nl' => simp [NotStuck]
  | okVals argVals s' nl' =>
    simp only [hr]
    -- Length matching
    have hevalArgs := evalFuelArgs_sound_ok hr
    have hapres := preservationArgs htype_args hevalArgs
      henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
    have hvals_len : argVals.length = paramTys.length := hapres.hasTypes.length_eq
    have hjparams_len : jparams.length = paramTys.length := by
      rw [← hjp_map]; simp
    have hlen : jparams.length = argVals.length := by omega
    simp only [hlen, if_true]
    have := ih_body jparams jbody s' nl' argVals hjt_func hlen
    cases hb : evalFuel n ft (Env.bindParams env jparams argVals) s' jt lt nl' jbody with
    | outOfFuel => simp [NotStuck, hb]
    | stuck msg => rw [hb] at this; exact absurd this id
    | ok o₂ s₂ nl₂ => simp [NotStuck, hb]

theorem progress_apply_topFn
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {paramTys : List Mtype} {retTy : Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {func : Var} {argExprs : List Expr}
    (hF : F func = some (paramTys, retTy))
    (htype_args : HasTypeArgs Γ Δ Λ F E argExprs paramTys)
    (hEnvFunc : env func = none)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (ih_args : NotStuckArgs (evalFuelArgs n ft env s jt lt nl argExprs))
    (ih_body : ∀ params body s' nl' vs,
      ft func = some (params, body) →
      params.length = vs.length →
      NotStuck (evalFuel n ft (Env.bindParams Env.empty params vs)
        s' JoinTable.empty LoopTable.empty nl' body)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl
      (.apply func argExprs (.normal (.func paramTys retTy)))) := by
  simp only [evalFuel]
  simp only [hEnvFunc]
  -- Get ft func from FnTableWellTyped
  obtain ⟨params, body, hft_func, hparams_map, _, _⟩ := hft func paramTys retTy hF
  simp only [hft_func]
  cases hr : evalFuelArgs n ft env s jt lt nl argExprs with
  | outOfFuelArgs => simp [NotStuck]
  | stuckArgs msg => rw [hr] at ih_args; exact absurd ih_args id
  | abortArgs o s' nl' => simp [NotStuck]
  | okVals argVals s' nl' =>
    simp only [hr]
    -- Derive params.length = argVals.length from typing + preservationArgs
    have hevalArgs := evalFuelArgs_sound_ok hr
    have hapres := preservationArgs htype_args hevalArgs
      henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
    have hvals_len : argVals.length = paramTys.length := hapres.hasTypes.length_eq
    have hparams_len : params.length = paramTys.length := by
      rw [← hparams_map]; simp
    have hlen : params.length = argVals.length := by omega
    -- Apply IH on body
    have := ih_body params body s' nl' argVals hft_func hlen
    simp only [hlen, if_true]
    cases hb : evalFuel n ft (Env.bindParams Env.empty params argVals) s'
                JoinTable.empty LoopTable.empty nl' body with
    | outOfFuel => simp [NotStuck, hb]
    | stuck msg => rw [hb] at this; exact absurd this id
    | ok o₂ s₂ nl₂ => simp [NotStuck, hb]

/-- Progress for `.recordUpdate rec_ updFields _` given that `rec_`
    evaluates to a heap-allocated loc (not an inline `.constr` value).
    The `hrec_is_loc` hypothesis is a runtime constraint paralleling
    `hnot_loc` in the earlier switch lemmas — it's needed because
    `Eval.recordUpdate` only has a rule for `.loc` values while the
    typing `.constr tid ats` admits both. -/
theorem progress_recordUpdate
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {tid : Nat} {ats : List Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {rec_ : Expr}
    {updFields : List (FieldLabel × Nat × Bool × Expr)} {fieldsNum : Nat}
    (htype_rec : HasType Γ Δ Λ F E rec_ (.constr tid ats))
    (hrec_is_loc : ∀ v s' nl',
      evalFuel n ft env s jt lt nl rec_ = .ok (.val v) s' nl' →
      ∃ l, v = .loc l)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (hhlp : ∀ s' nl' o, evalFuel n ft env s jt lt nl rec_ = .ok o s' nl' →
            HeapLocPresent s')
    (ih_rec : NotStuck (evalFuel n ft env s jt lt nl rec_))
    (ih_fields : ∀ s' nl',
      NotStuckArgs (evalFuelArgs n ft env s' jt lt nl'
        (updFields.map fun x => x.2.2.2))) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl
      (.recordUpdate rec_ updFields fieldsNum)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl rec_ with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih_rec; exact absurd ih_rec id
  | ok o s' nl' =>
    cases o with
    | val v =>
      have heval := evalFuel_sound hr
      have hvt := preservation_val htype_rec heval
        henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
      obtain ⟨l, rfl⟩ := hrec_is_loc v s' nl' hr
      -- Use HeapLocPresent to find the record in the store
      have hhlp' : HeapLocPresent s' := hhlp s' nl' _ hr
      obtain ⟨fields, mutFlags, hstore, _⟩ := hhlp' l tid ats hvt
      simp only [hstore]
      have := ih_fields s' nl'
      cases hfa : evalFuelArgs n ft env s' jt lt nl'
                  (updFields.map fun x => x.2.2.2) with
      | outOfFuelArgs => simp [NotStuck, hfa]
      | stuckArgs msg => rw [hfa] at this; exact absurd this id
      | abortArgs oA sA nlA => simp [NotStuck, hfa]
      | okVals newVals s₂ nl₂ => simp [NotStuck, hfa]
    | _ => simp [NotStuck]

/-- Progress for `.mutate rec_ _ fld pos` given that `rec_` evaluates
    to a heap-allocated loc. Parallel to `progress_recordUpdate`. -/
theorem progress_mutate
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {tid : Nat} {ats : List Mtype} {fieldTy : Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {rec_ fld : Expr}
    {label : FieldLabel} {pos : Nat}
    (htype_rec : HasType Γ Δ Λ F E rec_ (.constr tid ats))
    (hpos : ats[pos]? = some fieldTy)
    (htype_fld : HasType Γ Δ Λ F E fld fieldTy)
    (hrec_is_loc : ∀ v s' nl',
      evalFuel n ft env s jt lt nl rec_ = .ok (.val v) s' nl' →
      ∃ l, v = .loc l)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (hhlp_fld_after_rec : ∀ s' nl' l,
      evalFuel n ft env s jt lt nl rec_ = .ok (.val (.loc l)) s' nl' →
      ∀ s'' nl'' v,
        evalFuel n ft env s' jt lt nl' fld = .ok (.val v) s'' nl'' →
        ∃ fields mutFlags, s'' l = some (.record fields mutFlags))
    (ih_rec : NotStuck (evalFuel n ft env s jt lt nl rec_))
    (ih_fld : ∀ s' nl', NotStuck (evalFuel n ft env s' jt lt nl' fld)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl
      (.mutate rec_ label fld pos)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl rec_ with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih_rec; exact absurd ih_rec id
  | ok o s' nl' =>
    cases o with
    | val v =>
      obtain ⟨l, rfl⟩ := hrec_is_loc v s' nl' hr
      have := ih_fld s' nl'
      cases hf : evalFuel n ft env s' jt lt nl' fld with
      | outOfFuel => simp [NotStuck, hf]
      | stuck msg => rw [hf] at this; exact absurd this id
      | ok oFld sFld nlFld =>
        cases oFld with
        | val vFld =>
          obtain ⟨fields, mutFlags, hstore⟩ :=
            hhlp_fld_after_rec s' nl' l hr sFld nlFld vFld hf
          simp [NotStuck, hf, hstore]
        | _ => simp [NotStuck, hf]
    | _ => simp [NotStuck]

/-- Progress for `.field rec_ acc pos` on a full `.constr tid ats` type,
    handling both the `.constr tag args` and `.loc l` subcases via
    `canonical_constr` + `HeapLocPresent`. -/
theorem progress_field_heap
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {tid : Nat} {ats : List Mtype} {fieldTy : Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {rec_ : Expr} {acc : Accessor} {pos : Nat}
    (htype_rec : HasType Γ Δ Λ F E rec_ (.constr tid ats))
    (hpos : ats[pos]? = some fieldTy)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (hhlp : ∀ s' nl' o, evalFuel n ft env s jt lt nl rec_ = .ok o s' nl' →
            HeapLocPresent s')
    (ih : NotStuck (evalFuel n ft env s jt lt nl rec_)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.field rec_ acc pos)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl rec_ with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih; exact absurd ih id
  | ok o s' nl' =>
    cases o with
    | val v =>
      have heval := evalFuel_sound hr
      have hvt := preservation_val htype_rec heval
        henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
      have hposLt : pos < ats.length := by
        by_contra hlt; push_neg at hlt
        simp [List.getElem?_eq_none_iff.mpr (by omega)] at hpos
      rcases canonical_constr hvt with
        ⟨tag, args, rfl, hargs⟩ | ⟨l, rfl⟩
      · -- .constr case
        have hlen_args : pos < args.length := by
          rw [hargs.length_eq]; exact hposLt
        have hgetv : args[pos]? = some (args[pos]'hlen_args) := by
          simp [List.getElem?_eq_getElem hlen_args]
        simp [hgetv, NotStuck]
      · -- .loc case — use HeapLocPresent on s'
        have hhlp' : HeapLocPresent s' := hhlp s' nl' _ hr
        obtain ⟨fields, mutFlags, hstore, hsize⟩ := hhlp' l tid ats hvt
        have hlen_fields : pos < fields.size := by rw [hsize]; exact hposLt
        have hgetv : fields[pos]? = some (fields[pos]'hlen_fields) :=
          Array.getElem?_eq_getElem hlen_fields
        simp [hstore, hgetv, NotStuck]
    | _ => simp [NotStuck]

theorem progress_field_tuple
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {τ : Mtype} {τs : List Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {rec_ : Expr} {acc : Accessor} {pos : Nat}
    (htype_rec : HasType Γ Δ Λ F E rec_ (.tuple τs))
    (hpos : τs[pos]? = some τ)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (ih : NotStuck (evalFuel n ft env s jt lt nl rec_)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.field rec_ acc pos)) := by
  simp only [evalFuel]
  cases hr : evalFuel n ft env s jt lt nl rec_ with
  | outOfFuel => simp [NotStuck]
  | stuck msg => rw [hr] at ih; exact absurd ih id
  | ok o s' nl' =>
    cases o with
    | val v =>
      have heval := evalFuel_sound hr
      have hvt := preservation_val htype_rec heval
        henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
      obtain ⟨vals, rfl, hvals⟩ := canonical_tuple hvt
      have hlen_vals : pos < vals.length := by
        have hlen_τs : pos < τs.length := by
          by_contra hlt; push_neg at hlt
          simp [List.getElem?_eq_none_iff.mpr (by omega)] at hpos
        rw [hvals.length_eq]; exact hlen_τs
      have hgetv : vals[pos]? = some (vals[pos]'hlen_vals) := by
        simp [List.getElem?_eq_getElem hlen_vals]
      simp [hgetv, NotStuck]
    | _ => simp [NotStuck]

theorem progress_prim
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {op : Prim} {argExprs : List Expr}
    {argTys : List Mtype}
    (htype_args : HasTypeArgs Γ Δ Λ F E argExprs argTys)
    (hsupport : PrimSupported op argTys)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hjdc : JoinDeltaConsistent jt Δ)
    (hllc : LoopLabelConsistent lt Λ)
    (hhft : HeapFieldTyped F)
    (ih_args : NotStuckArgs (evalFuelArgs n ft env s jt lt nl argExprs)) :
    NotStuck (evalFuel (n+1) ft env s jt lt nl (.prim op argExprs)) := by
  simp only [evalFuel]
  cases hr : evalFuelArgs n ft env s jt lt nl argExprs with
  | outOfFuelArgs => simp [NotStuck]
  | stuckArgs msg => rw [hr] at ih_args; exact absurd ih_args id
  | abortArgs o s' nl' => simp [NotStuck]
  | okVals argVals s' nl' =>
    simp only [hr]
    -- Get typing of argVals via soundness + preservationArgs
    have hevalArgs := evalFuelArgs_sound_ok hr
    have hapres := preservationArgs htype_args hevalArgs
      henv hft hcinv hdisj hftc hjwt hjdc hllc hhft
    -- Use evalPrim_total
    obtain ⟨v, hv⟩ := evalPrim_total hsupport hapres.hasTypes
    simp [hv, NotStuck]

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

/-! ## Combined progress theorem for a core propagator fragment

This demonstrates how to assemble the per-case progress lemmas into
a unified theorem using mutual induction on fuel. The scope is a
subset of stub-free expressions that only needs `EnvWellTyped` as
the runtime invariant (no preservation threading, no heap, no apply,
no conditional typing).

The full combined theorem for all stub-free expressions would extend
this pattern by threading the complete `ProgressCtx` + conditional
hypotheses through recursive calls. -/

/-- A Prim for which any well-typed invocation is supported by evalPrim.

    These are `.not`, `.ignore`, `.identity` — the primitives where
    `typeOfPrim op argTys ≠ none → PrimSupported op argTys`.

    `.arith`/`.cmp`/`.neg`/`.stringLength`/`.stringEqual` are not always
    safe because `typeOfPrim` accepts more argument types (int64, float,
    string, etc.) than `PrimSupported` currently covers — a gap in the
    `evalPrim` implementation rather than the type system. -/
def SafePrim : Prim → Prop
  | .not => True
  | .ignore => True
  | .identity => True
  | _ => False

/-- For safe prims, `typeOfPrim` implies `PrimSupported`. -/
theorem SafePrim.to_primSupported
    {op : Prim} {argTys : List Mtype} {τ : Mtype}
    (hsafe : SafePrim op) (htype : typeOfPrim op argTys = some τ) :
    PrimSupported op argTys := by
  cases op <;> simp [SafePrim] at hsafe
  · -- .not
    cases argTys with
    | nil => simp [typeOfPrim] at htype
    | cons t ts =>
      cases ts with
      | nil =>
        cases t <;> simp [typeOfPrim] at htype
        · simp [PrimSupported]
      | cons _ _ => simp [typeOfPrim] at htype
  · -- .ignore
    cases argTys with
    | nil => simp [typeOfPrim] at htype
    | cons t ts =>
      cases ts with
      | nil => simp [PrimSupported]
      | cons _ _ => simp [typeOfPrim] at htype
  · -- .identity
    cases argTys with
    | nil => simp [typeOfPrim] at htype
    | cons t ts =>
      cases ts with
      | nil => simp [PrimSupported]
      | cons _ _ => simp [typeOfPrim] at htype

mutual

/-- Scope for combined progress: leaves + pure propagators + .var +
    typing-directed cases (.if, .and, .or, .prim). -/
inductive CoreExpr : Expr → Prop where
  | const : CoreExpr (.const c)
  | unit : CoreExpr .unit
  | var : CoreExpr (.var x prim)
  | function : CoreExpr (.function params fnBody isRaw)
  | constr : CoreArgs argExprs → CoreExpr (.constr tag argExprs)
  | tuple : CoreArgs exprs → CoreExpr (.tuple exprs)
  | array : CoreArgs exprs → CoreExpr (.array exprs)
  | seq : CoreArgs exprs → CoreExpr last → CoreExpr (.seq exprs last)
  | assign : CoreExpr e → CoreExpr (.assign x e)
  | object : CoreExpr self → CoreExpr (.object self)
  | breakNone : CoreExpr (.break none label)
  | breakSome : CoreExpr arg → CoreExpr (.break (some arg) label)
  | «continue» : CoreArgs argExprs → CoreExpr (.continue argExprs label)
  | returnSingle : CoreExpr e → CoreExpr (.return e .singleValue)
  | returnErrorResult : CoreExpr e →
      CoreExpr (.return e (.errorResult isErr retTy))
  | handleErrorToResult : CoreExpr obj →
      CoreExpr (.handleError obj .toResult)
  | handleErrorReturnErr : CoreExpr obj →
      CoreExpr (.handleError obj (.returnErr okTy))
  | «if» : CoreExpr condE → CoreExpr ifso →
      (∀ e, ifnot = some e → CoreExpr e) →
      CoreExpr (.if condE ifso ifnot)
  | and_ : CoreExpr lhs → CoreExpr rhs → CoreExpr (.and lhs rhs)
  | or_ : CoreExpr lhs → CoreExpr rhs → CoreExpr (.or lhs rhs)
  | prim : SafePrim op → CoreArgs argExprs → CoreExpr (.prim op argExprs)

inductive CoreArgs : List Expr → Prop where
  | nil : CoreArgs []
  | cons : CoreExpr e → CoreArgs es → CoreArgs (e :: es)

end

/-- Combined progress proposition at fuel level n for the CoreExpr scope.
    Threads the full `ProgressCtx` bundle so typing-directed cases can
    use preservation. -/
private def CoreProgressAt (n : Nat) : Prop :=
  (∀ {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
     {E : Option Mtype} {τ : Mtype}
     {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
     {lt : LoopTable} {nl : Loc} {e : Expr},
    HasType Γ Δ Λ F E e τ →
    CoreExpr e →
    ProgressCtx Γ Δ Λ F ft env jt lt →
    NotStuck (evalFuel n ft env s jt lt nl e)) ∧
  (∀ {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
     {E : Option Mtype} {τs : List Mtype}
     {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
     {lt : LoopTable} {nl : Loc} {es : List Expr},
    HasTypeArgs Γ Δ Λ F E es τs →
    CoreArgs es →
    ProgressCtx Γ Δ Λ F ft env jt lt →
    NotStuckArgs (evalFuelArgs n ft env s jt lt nl es))

private theorem coreProgress_zero : CoreProgressAt 0 := by
  refine ⟨?_, ?_⟩ <;> intros <;> simp [evalFuel, evalFuelArgs, NotStuck, NotStuckArgs]

private theorem coreProgress_succ (n : Nat) (ih : CoreProgressAt n) :
    CoreProgressAt (n + 1) := by
  obtain ⟨ihE, ihArgs⟩ := ih
  refine ⟨?_, ?_⟩
  · intro Γ Δ Λ F E τ ft env s jt lt nl e htype hcore ctx
    cases hcore with
    | const => exact progress_const _ _ _ _ _ _ _ _
    | unit => exact progress_unit _ _ _ _ _ _ _
    | var =>
      cases htype with
      | var hΓ => exact progress_var hΓ ctx.envWT _ _ _ _ _ _ _
      | varPrim hΓ => exact progress_var hΓ ctx.envWT _ _ _ _ _ _ _
    | function => exact progress_function _ _ _ _ _ _ _ _ _ _
    | constr h =>
      cases htype with
      | constr ht => exact progress_constr (ihArgs ht h ctx)
    | tuple h =>
      cases htype with
      | tuple ht => exact progress_tuple (ihArgs ht h ctx)
    | array h =>
      cases htype with
      | array ht => exact progress_array (ihArgs ht h ctx)
    | seq hargs hlast =>
      cases htype with
      | seq htargs htlast =>
        exact progress_seq (ihArgs htargs hargs ctx)
          (fun _ _ => ihE htlast hlast ctx)
    | assign h =>
      cases htype with
      | assign _ ht => exact progress_assign (ihE ht h ctx)
    | object h =>
      cases htype with
      | object ht => exact progress_object (ihE ht h ctx)
    | breakNone => exact progress_breakNone _ _ _ _ _ _ _ _
    | breakSome h =>
      cases htype with
      | «break» _ ht => exact progress_break_some (ihE ht h ctx)
    | «continue» h =>
      cases htype with
      | «continue» _ ht => exact progress_continue (ihArgs ht h ctx)
    | returnSingle h =>
      cases htype with
      | returnSingle ht => exact progress_return_single (ihE ht h ctx)
    | returnErrorResult h =>
      cases htype with
      | returnOk ht => exact progress_return_errorResult (ihE ht h ctx)
      | returnErr _ ht => exact progress_return_errorResult (ihE ht h ctx)
    | handleErrorToResult h =>
      cases htype with
      | handleErrorToResult ht =>
        exact progress_handleError_toResult (ihE ht h ctx)
    | handleErrorReturnErr h =>
      cases htype with
      | handleErrorReturnErr ht =>
        exact progress_handleError_returnErr (ihE ht h ctx)
    | «if» hcondE hifso hifnot =>
      cases htype with
      | ifSome htcond htifso htifnot =>
        exact progress_if htcond ctx.envWT ctx.ftWT ctx.clInv ctx.fnDisj
          ctx.ftC ctx.jwt ctx.jdc ctx.llc ctx.hft
          (ihE htcond hcondE ctx)
          (fun _ _ => ihE htifso hifso ctx)
          (fun e' he' _ _ => by
            cases he'; exact ihE htifnot (hifnot _ rfl) ctx)
      | ifNone htcond htifso =>
        exact progress_if htcond ctx.envWT ctx.ftWT ctx.clInv ctx.fnDisj
          ctx.ftC ctx.jwt ctx.jdc ctx.llc ctx.hft
          (ihE htcond hcondE ctx)
          (fun _ _ => ihE htifso hifso ctx)
          (fun _ h => by cases h)
    | and_ hl hr =>
      cases htype with
      | and htl htr =>
        exact progress_and htl ctx.envWT ctx.ftWT ctx.clInv ctx.fnDisj
          ctx.ftC ctx.jwt ctx.jdc ctx.llc ctx.hft
          (ihE htl hl ctx) (fun _ _ => ihE htr hr ctx)
    | or_ hl hr =>
      cases htype with
      | or htl htr =>
        exact progress_or htl ctx.envWT ctx.ftWT ctx.clInv ctx.fnDisj
          ctx.ftC ctx.jwt ctx.jdc ctx.llc ctx.hft
          (ihE htl hl ctx) (fun _ _ => ihE htr hr ctx)
    | prim hsafe hargs =>
      cases htype with
      | prim htargs htypeOfPrim =>
        exact progress_prim htargs (hsafe.to_primSupported htypeOfPrim)
          ctx.envWT ctx.ftWT ctx.clInv ctx.fnDisj ctx.ftC ctx.jwt
          ctx.jdc ctx.llc ctx.hft (ihArgs htargs hargs ctx)
  · intro Γ Δ Λ F E τs ft env s jt lt nl es htype hargs ctx
    cases hargs with
    | nil => exact progress_args_nil _ _ _ _ _ _ _
    | cons he hes =>
      cases htype with
      | cons hte htes =>
        exact progress_args_cons (ihE hte he ctx)
          (fun _ _ => ihArgs htes hes ctx)

/-- Combined core progress theorem: for every fuel level, any well-typed
    `CoreExpr` expression does not get stuck in `evalFuel`. -/
theorem coreProgress : ∀ n, CoreProgressAt n := by
  intro n
  induction n with
  | zero => exact coreProgress_zero
  | succ k ih => exact coreProgress_succ k ih

/-- Main combined progress corollary (single-expression form). -/
theorem coreProgress_eval
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {τ : Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {e : Expr}
    (htype : HasType Γ Δ Λ F E e τ)
    (hcore : CoreExpr e)
    (ctx : ProgressCtx Γ Δ Λ F ft env jt lt) :
    NotStuck (evalFuel n ft env s jt lt nl e) :=
  (coreProgress n).1 htype hcore ctx

/-- Main combined progress corollary (argument-list form). -/
theorem coreProgress_evalArgs
    {Γ : TyEnv} {Δ : JoinTyEnv} {Λ : LoopTyEnv} {F : FnTyTable}
    {E : Option Mtype} {τs : List Mtype}
    {n : Nat} {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc} {es : List Expr}
    (htype : HasTypeArgs Γ Δ Λ F E es τs)
    (hargs : CoreArgs es)
    (ctx : ProgressCtx Γ Δ Λ F ft env jt lt) :
    NotStuckArgs (evalFuelArgs n ft env s jt lt nl es) :=
  (coreProgress n).2 htype hargs ctx

end Moonbit.Mcore
