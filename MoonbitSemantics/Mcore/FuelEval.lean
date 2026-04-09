/-
  MoonBit Compiler — Mcore Fuel-Bounded Evaluator

  A partial functional interpreter for Mcore expressions, bounded by a
  natural-number fuel parameter. Used to state and prove **progress** for
  well-typed programs: well-typed programs never yield `.stuck`, only `.ok`
  (successful evaluation) or `.outOfFuel` (legitimate divergence).

  Design:
  - `evalFuel` returns `.ok o s' nl'` on successful evaluation (where `o` may
    be any `Outcome` — value, break, continue, return, or error), `.outOfFuel`
    if the fuel budget is exhausted (indicating legitimate divergence), or
    `.stuck reason` if evaluation hits an impossible state (e.g., branch on
    non-bool, field access on non-aggregate, missing variable).
  - Each recursive call decrements fuel by 1, so termination is structural on
    the fuel argument.
  - `evalFuelArgs` handles list-of-args evaluation with abort propagation.

  Known stubs (deferred to a later sub-phase):
  - `.letrec`, `.letfn .recursive`: self-referential env construction.
  - `.loop`: requires a LoopReentry helper to handle `.continue` re-entry.

  Soundness (`evalFuel.ok → Eval`) and progress (`HasType → evalFuel n ≠
  .stuck _`) are proved in follow-up phases.
-/
import MoonbitSemantics.Mcore.Semantics
import MoonbitSemantics.Mcore.CanonicalForms

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp)

/-! ## Result types -/

inductive EvalFuelResult where
  | ok (o : Outcome) (s' : Store) (nl' : Loc) : EvalFuelResult
  | outOfFuel : EvalFuelResult
  | stuck (reason : String) : EvalFuelResult
  deriving Inhabited

inductive EvalFuelArgsResult where
  | okVals (vs : List Value) (s' : Store) (nl' : Loc) : EvalFuelArgsResult
  | abortArgs (o : Outcome) (s' : Store) (nl' : Loc) : EvalFuelArgsResult
  | outOfFuelArgs : EvalFuelArgsResult
  | stuckArgs (reason : String) : EvalFuelArgsResult
  deriving Inhabited

/-! ## Fuel-bounded evaluator

Termination: structural on the first argument (fuel). Every recursive call
decrements fuel by 1.
-/

mutual

/-- Fuel-bounded evaluation of a single expression. Mirrors the Eval inductive
    1:1 where possible; hard cases (letrec, letfnRec, loop) are stubbed. -/
def evalFuel : Nat → FnTable → Env → Store → JoinTable → LoopTable → Loc →
    Expr → EvalFuelResult
  | 0, _, _, _, _, _, _, _ => .outOfFuel
  | n+1, ft, env, s, jt, lt, nl, e =>
    match e with
    -- ════════ Leaves ════════
    | .const c => .ok (.val (.const c)) s nl
    | .unit => .ok (.val .unit) s nl
    | .var x _ =>
      match env x with
      | some v => .ok (.val v) s nl
      | none => .stuck "var: not in env"

    -- ════════ Let binding ════════
    | .let name rhs body =>
      match env name with
      | some _ => .stuck "let: name not fresh in env"
      | none =>
        match evalFuel n ft env s jt lt nl rhs with
        | .ok (.val v₁) s₁ nl₁ =>
          evalFuel n ft (Env.extend env name v₁) s₁ jt lt nl₁ body
        | .ok o s₁ nl₁ => .ok o s₁ nl₁  -- abort propagation
        | .outOfFuel => .outOfFuel
        | .stuck r => .stuck r

    -- ════════ Functions ════════
    | .function params fnBody false =>
      .ok (.val (.closure env params fnBody)) s nl
    | .function params fnBody true =>
      .ok (.val (.rawFn params fnBody)) s nl

    -- ════════ Local function bindings ════════
    | .letfn name params fnBody body kind =>
      match kind with
      | .nonRecursive =>
        match env name with
        | some _ => .stuck "letfnNonrec: name not fresh in env"
        | none =>
          evalFuel n ft (Env.extend env name (.closure env params fnBody))
            s jt lt nl body
      | .recursive =>
        -- recEnv = env.extend name (.closure recEnv params fnBody) is
        -- self-referential. Deferred to a later sub-phase.
        .stuck "TODO: letfnRec"
      | .tailJoin =>
        match jt name with
        | some _ => .stuck "letfnTailJoin: name not fresh in jt"
        | none =>
          evalFuel n ft env s (JoinTable.extend jt name ⟨params, fnBody⟩)
            lt nl body
      | .nontailJoin =>
        match jt name with
        | some _ => .stuck "letfnNontailJoin: name not fresh in jt"
        | none =>
          evalFuel n ft env s (JoinTable.extend jt name ⟨params, fnBody⟩)
            lt nl body

    -- ════════ Letrec ════════
    | .letrec _ _ =>
      -- recEnv = Env.extendMany env (bindings.map ...) is self-referential.
      -- Deferred to a later sub-phase.
      .stuck "TODO: letrec"

    -- ════════ Function application ════════
    | .apply func argExprs .join =>
      match jt func with
      | some ⟨params, jbody⟩ =>
        if params.any (fun p => (env p.binder).isSome) then
          .stuck "applyJoin: param binder not fresh in env"
        else
          match evalFuelArgs n ft env s jt lt nl argExprs with
          | .okVals argVals s₁ nl₁ =>
            if params.length = argVals.length then
              evalFuel n ft (Env.bindParams env params argVals)
                s₁ jt lt nl₁ jbody
            else
              .stuck "applyJoin: param/arg length mismatch"
          | .abortArgs o s₁ nl₁ => .ok o s₁ nl₁
          | .outOfFuelArgs => .outOfFuel
          | .stuckArgs r => .stuck r
      | none => .stuck "applyJoin: target not in jt"
    | .apply func argExprs (.normal _) =>
      match env func with
      | some (.closure captured params fnBody) =>
        match evalFuelArgs n ft env s jt lt nl argExprs with
        | .okVals argVals s₁ nl₁ =>
          if params.length = argVals.length then
            evalFuel n ft (Env.bindParams captured params argVals)
              s₁ JoinTable.empty LoopTable.empty nl₁ fnBody
          else .stuck "applyClosure: param/arg length mismatch"
        | .abortArgs o s₁ nl₁ => .ok o s₁ nl₁
        | .outOfFuelArgs => .outOfFuel
        | .stuckArgs r => .stuck r
      | some (.rawFn params fnBody) =>
        match evalFuelArgs n ft env s jt lt nl argExprs with
        | .okVals argVals s₁ nl₁ =>
          if params.length = argVals.length then
            evalFuel n ft (Env.bindParams Env.empty params argVals)
              s₁ JoinTable.empty LoopTable.empty nl₁ fnBody
          else .stuck "applyRawFn: param/arg length mismatch"
        | .abortArgs o s₁ nl₁ => .ok o s₁ nl₁
        | .outOfFuelArgs => .outOfFuel
        | .stuckArgs r => .stuck r
      | some _ => .stuck "apply: env value is not a function"
      | none =>
        -- Not in env; try the top-level function table.
        match ft func with
        | some (params, fnBody) =>
          match evalFuelArgs n ft env s jt lt nl argExprs with
          | .okVals argVals s₁ nl₁ =>
            if params.length = argVals.length then
              evalFuel n ft (Env.bindParams Env.empty params argVals)
                s₁ JoinTable.empty LoopTable.empty nl₁ fnBody
            else .stuck "applyTopFn: param/arg length mismatch"
          | .abortArgs o s₁ nl₁ => .ok o s₁ nl₁
          | .outOfFuelArgs => .outOfFuel
          | .stuckArgs r => .stuck r
        | none => .stuck "apply: function not found in env or fnTable"

    -- ════════ Primitives ════════
    | .prim op argExprs =>
      match evalFuelArgs n ft env s jt lt nl argExprs with
      | .okVals argVals s₁ nl₁ =>
        match Moonbit.Mcore.evalPrim op argVals with
        | some v => .ok (.val v) s₁ nl₁
        | none => .stuck "prim: evalPrim returned none"
      | .abortArgs o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuelArgs => .outOfFuel
      | .stuckArgs r => .stuck r

    -- ════════ Data construction ════════
    | .constr tag argExprs =>
      match evalFuelArgs n ft env s jt lt nl argExprs with
      | .okVals argVals s₁ nl₁ => .ok (.val (.constr tag argVals)) s₁ nl₁
      | .abortArgs o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuelArgs => .outOfFuel
      | .stuckArgs r => .stuck r
    | .tuple exprs =>
      match evalFuelArgs n ft env s jt lt nl exprs with
      | .okVals vals s₁ nl₁ => .ok (.val (.tuple vals)) s₁ nl₁
      | .abortArgs o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuelArgs => .outOfFuel
      | .stuckArgs r => .stuck r
    | .record fieldExprs =>
      match evalFuelArgs n ft env s jt lt nl (fieldExprs.map fun (_, _, _, e) => e) with
      | .okVals fieldVals s₁ nl₁ =>
        .ok (.val (.loc nl₁))
          (Store.alloc s₁ nl₁
            (.record fieldVals.toArray
              ((fieldExprs.map fun (_, _, m, _) => m).toArray)))
          (nl₁ + 1)
      | .abortArgs o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuelArgs => .outOfFuel
      | .stuckArgs r => .stuck r
    | .recordUpdate rec_ updFields _ =>
      match evalFuel n ft env s jt lt nl rec_ with
      | .ok (.val (.loc l)) s₁ nl₁ =>
        match s₁ l with
        | some (.record oldFields mutFlags) =>
          match evalFuelArgs n ft env s₁ jt lt nl₁ (updFields.map fun (_, _, _, e) => e) with
          | .okVals newVals s₂ nl₂ =>
            let updatedFields := (updFields.zip newVals).foldl
              (fun acc (entry : (FieldLabel × Nat × Bool × Expr) × Value) =>
                acc.setIfInBounds entry.1.2.1 entry.2) oldFields
            .ok (.val (.loc nl₂))
              (Store.alloc s₂ nl₂ (.record updatedFields mutFlags))
              (nl₂ + 1)
          | .abortArgs o s₂ nl₂ => .ok o s₂ nl₂
          | .outOfFuelArgs => .outOfFuel
          | .stuckArgs r => .stuck r
        | _ => .stuck "recordUpdate: loc does not point to a record"
      | .ok (.val _) _ _ => .stuck "recordUpdate: rec_ is not a loc"
      | .ok o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuel => .outOfFuel
      | .stuck r => .stuck r
    | .array exprs =>
      match evalFuelArgs n ft env s jt lt nl exprs with
      | .okVals vals s₁ nl₁ =>
        .ok (.val (.loc nl₁))
          (Store.alloc s₁ nl₁ (.array vals.toArray))
          (nl₁ + 1)
      | .abortArgs o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuelArgs => .outOfFuel
      | .stuckArgs r => .stuck r

    -- ════════ Data access ════════
    | .field rec_ _acc pos =>
      match evalFuel n ft env s jt lt nl rec_ with
      | .ok (.val (.tuple vals)) s₁ nl₁ =>
        match vals[pos]? with
        | some v => .ok (.val v) s₁ nl₁
        | none => .stuck "fieldTuple: pos out of bounds"
      | .ok (.val (.constr _ vals)) s₁ nl₁ =>
        match vals[pos]? with
        | some v => .ok (.val v) s₁ nl₁
        | none => .stuck "fieldConstr: pos out of bounds"
      | .ok (.val (.loc l)) s₁ nl₁ =>
        match s₁ l with
        | some (.record fields _) =>
          match fields[pos]? with
          | some v => .ok (.val v) s₁ nl₁
          | none => .stuck "fieldRecord: pos out of bounds"
        | _ => .stuck "fieldRecord: loc does not point to a record"
      | .ok (.val _) _ _ => .stuck "field: rec_ is not an aggregate"
      | .ok o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuel => .outOfFuel
      | .stuck r => .stuck r

    -- ════════ Mutation ════════
    | .mutate rec_ _label fld pos =>
      match evalFuel n ft env s jt lt nl rec_ with
      | .ok (.val (.loc l)) s₁ nl₁ =>
        match evalFuel n ft env s₁ jt lt nl₁ fld with
        | .ok (.val v) s₂ nl₂ =>
          match s₂ l with
          | some (.record fields mutFlags) =>
            .ok (.val .unit)
              (Store.alloc s₂ l (.record (fields.setIfInBounds pos v) mutFlags))
              nl₂
          | _ => .stuck "mutate: loc does not point to a record"
        | .ok o s₂ nl₂ => .ok o s₂ nl₂
        | .outOfFuel => .outOfFuel
        | .stuck r => .stuck r
      | .ok (.val _) _ _ => .stuck "mutate: rec_ is not a loc"
      | .ok o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuel => .outOfFuel
      | .stuck r => .stuck r

    -- ════════ Assignment ════════
    | .assign _x e =>
      match evalFuel n ft env s jt lt nl e with
      | .ok (.val _) s₁ nl₁ => .ok (.val .unit) s₁ nl₁
      | .ok o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuel => .outOfFuel
      | .stuck r => .stuck r

    -- ════════ Sequencing ════════
    | .seq exprs last =>
      match evalFuelArgs n ft env s jt lt nl exprs with
      | .okVals _vs s₁ nl₁ => evalFuel n ft env s₁ jt lt nl₁ last
      | .abortArgs o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuelArgs => .outOfFuel
      | .stuckArgs r => .stuck r

    -- ════════ Conditionals ════════
    | .if cond ifso ifnot =>
      match evalFuel n ft env s jt lt nl cond with
      | .ok (.val (.const (.bool true))) s₁ nl₁ =>
        evalFuel n ft env s₁ jt lt nl₁ ifso
      | .ok (.val (.const (.bool false))) s₁ nl₁ =>
        match ifnot with
        | some e => evalFuel n ft env s₁ jt lt nl₁ e
        | none => .ok (.val .unit) s₁ nl₁
      | .ok (.val _) _ _ => .stuck "if: cond is not a bool"
      | .ok o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuel => .outOfFuel
      | .stuck r => .stuck r

    -- ════════ Pattern matching ════════
    | .switchConstr obj cases dflt =>
      match evalFuel n ft env s jt lt nl obj with
      | .ok (.val (.constr tag args)) s₁ nl₁ =>
        match findConstrCase cases tag with
        | some (binder, branch) =>
          match binder with
          | some x =>
            match env x with
            | some _ => .stuck "switchConstr: binder not fresh in env"
            | none =>
              evalFuel n ft (Env.extend env x (.constr tag args))
                s₁ jt lt nl₁ branch
          | none => evalFuel n ft env s₁ jt lt nl₁ branch
        | none =>
          match dflt with
          | some d => evalFuel n ft env s₁ jt lt nl₁ d
          | none => .stuck "switchConstr: no matching case and no default"
      | .ok (.val _) _ _ => .stuck "switchConstr: obj is not a constr"
      | .ok o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuel => .outOfFuel
      | .stuck r => .stuck r
    | .switchConstant obj cases dflt =>
      match evalFuel n ft env s jt lt nl obj with
      | .ok (.val (.const c)) s₁ nl₁ =>
        match findConstantCase cases c with
        | some branch => evalFuel n ft env s₁ jt lt nl₁ branch
        | none => evalFuel n ft env s₁ jt lt nl₁ dflt
      | .ok (.val _) _ _ => .stuck "switchConstant: obj is not a constant"
      | .ok o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuel => .outOfFuel
      | .stuck r => .stuck r

    -- ════════ Loops ════════
    | .loop params body argExprs label =>
      match lt label with
      | some _ => .stuck "loop: label not fresh in lt"
      | none =>
        if params.any (fun p => (env p.binder).isSome) then
          .stuck "loop: param binder not fresh in env"
        else
          match evalFuelArgs n ft env s jt lt nl argExprs with
          | .okVals argVals s₁ nl₁ =>
            if params.length = argVals.length then
              -- Pass (n+1, n+1) so inside loopIter, body eval uses fuel n
              -- matching the outer IH level.
              loopIter (n+1) (n+1) ft env params body argVals label s₁ jt lt nl₁
            else .stuck "loop: param/arg length mismatch"
          | .abortArgs o s₁ nl₁ => .ok o s₁ nl₁
          | .outOfFuelArgs => .outOfFuel
          | .stuckArgs r => .stuck r

    -- ════════ Break / continue ════════
    | .break argOpt label =>
      match argOpt with
      | some arg =>
        match evalFuel n ft env s jt lt nl arg with
        | .ok (.val v) s₁ nl₁ => .ok (.break (some v) label) s₁ nl₁
        | .ok o s₁ nl₁ => .ok o s₁ nl₁
        | .outOfFuel => .outOfFuel
        | .stuck r => .stuck r
      | none => .ok (.break none label) s nl
    | .continue argExprs label =>
      match evalFuelArgs n ft env s jt lt nl argExprs with
      | .okVals vals s₁ nl₁ => .ok (.continue vals label) s₁ nl₁
      | .abortArgs o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuelArgs => .outOfFuel
      | .stuckArgs r => .stuck r

    -- ════════ Short-circuit logical operators ════════
    | .and lhs rhs =>
      match evalFuel n ft env s jt lt nl lhs with
      | .ok (.val (.const (.bool true))) s₁ nl₁ =>
        evalFuel n ft env s₁ jt lt nl₁ rhs
      | .ok (.val (.const (.bool false))) s₁ nl₁ =>
        .ok (.val (.const (.bool false))) s₁ nl₁
      | .ok (.val _) _ _ => .stuck "and: lhs is not a bool"
      | .ok o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuel => .outOfFuel
      | .stuck r => .stuck r
    | .or lhs rhs =>
      match evalFuel n ft env s jt lt nl lhs with
      | .ok (.val (.const (.bool true))) s₁ nl₁ =>
        .ok (.val (.const (.bool true))) s₁ nl₁
      | .ok (.val (.const (.bool false))) s₁ nl₁ =>
        evalFuel n ft env s₁ jt lt nl₁ rhs
      | .ok (.val _) _ _ => .stuck "or: lhs is not a bool"
      | .ok o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuel => .outOfFuel
      | .stuck r => .stuck r

    -- ════════ Error handling ════════
    | .handleError obj kind =>
      match evalFuel n ft env s jt lt nl obj with
      | .ok (.val v) s₁ nl₁ =>
        match kind with
        | .toResult => .ok (.val (.constr 0 [v])) s₁ nl₁
        | .joinapply _ => .ok (.val v) s₁ nl₁
        | .returnErr _ => .ok (.val v) s₁ nl₁
      | .ok (.error v) s₁ nl₁ =>
        match kind with
        | .toResult => .ok (.val (.constr 1 [v])) s₁ nl₁
        | .joinapply target =>
          match jt target with
          | some ⟨jparams, jbody⟩ =>
            if jparams.any (fun p => (env p.binder).isSome) then
              .stuck "handleErrorJoinErr: param binder not fresh in env"
            else
              evalFuel n ft (Env.bindParams env jparams [v]) s₁ jt lt nl₁ jbody
          | none => .stuck "handleErrorJoinErr: target not in jt"
        | .returnErr _ => .ok (.error v) s₁ nl₁
      | .ok o s₁ nl₁ =>
        -- break / continue / return propagate through handleError
        .ok o s₁ nl₁
      | .outOfFuel => .outOfFuel
      | .stuck r => .stuck r

    -- ════════ Return ════════
    | .return e kind =>
      match evalFuel n ft env s jt lt nl e with
      | .ok (.val v) s₁ nl₁ =>
        match kind with
        | .singleValue => .ok (.val v) s₁ nl₁
        | .errorResult true _ => .ok (.error v) s₁ nl₁
        | .errorResult false _ => .ok (.val v) s₁ nl₁
      | .ok o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuel => .outOfFuel
      | .stuck r => .stuck r

    -- ════════ Objects ════════
    | .object self =>
      match evalFuel n ft env s jt lt nl self with
      | .ok (.val v) s₁ nl₁ => .ok (.val v) s₁ nl₁
      | .ok o s₁ nl₁ => .ok o s₁ nl₁
      | .outOfFuel => .outOfFuel
      | .stuck r => .stuck r

/-- Fuel-bounded evaluation of a list of argument expressions, left-to-right
    with abort propagation. -/
def evalFuelArgs : Nat → FnTable → Env → Store → JoinTable → LoopTable → Loc →
    List Expr → EvalFuelArgsResult
  | 0, _, _, _, _, _, _, _ => .outOfFuelArgs
  | _n+1, _ft, _env, s, _jt, _lt, nl, [] => .okVals [] s nl
  | n+1, ft, env, s, jt, lt, nl, e :: es =>
    match evalFuel n ft env s jt lt nl e with
    | .ok (.val v) s₁ nl₁ =>
      match evalFuelArgs n ft env s₁ jt lt nl₁ es with
      | .okVals vs s₂ nl₂ => .okVals (v :: vs) s₂ nl₂
      | .abortArgs o s₂ nl₂ => .abortArgs o s₂ nl₂
      | .outOfFuelArgs => .outOfFuelArgs
      | .stuckArgs r => .stuckArgs r
    | .ok o s₁ nl₁ => .abortArgs o s₁ nl₁
    | .outOfFuel => .outOfFuelArgs
    | .stuck r => .stuckArgs r

/-- One iteration of a loop body with params bound to `argVals`.
    Mirrors `LoopReentry`: takes the **base** `lt` (without this loop's
    extension) and extends internally. On `.continue` with matching label,
    re-enters with new values; on mismatched break/continue labels,
    returns stuck (matching Eval's undefined behavior). Takes two fuel
    parameters: `iter_fuel` bounds iteration count; `eval_fuel` is used
    for each body evaluation (constant across iterations so that
    soundness can use a single `SoundnessAt eval_fuel` hypothesis). -/
def loopIter : Nat → Nat → FnTable → Env → List Param → Expr → List Value →
    LoopLabel → Store → JoinTable → LoopTable → Loc → EvalFuelResult
  | 0, _, _, _, _, _, _, _, _, _, _, _ => .outOfFuel
  | _+1, 0, _, _, _, _, _, _, _, _, _, _ => .outOfFuel
  | iter+1, eval+1, ft, env, params, body, argVals, label, s, jt, lt, nl =>
    match evalFuel eval ft (Env.bindParams env params argVals) s jt
              (LoopTable.extend lt label ⟨params, body⟩) nl body with
    | .ok (.val v) s' nl' => .ok (.val v) s' nl'
    | .ok (.break (some v) lbl) s' nl' =>
      if lbl = label then .ok (.val v) s' nl'
      else .stuck "loopBreak: label mismatch"
    | .ok (.break none lbl) s' nl' =>
      if lbl = label then .ok (.val .unit) s' nl'
      else .stuck "loopBreakNone: label mismatch"
    | .ok (.continue newVals lbl) s' nl' =>
      if lbl = label then
        if params.length = newVals.length then
          loopIter iter (eval+1) ft env params body newVals label s' jt lt nl'
        else .stuck "loopContinue: param/arg length mismatch"
      else .stuck "loopContinue: label mismatch"
    | .ok (.return v) s' nl' => .ok (.return v) s' nl'
    | .ok (.error v) s' nl' => .ok (.error v) s' nl'
    | .outOfFuel => .outOfFuel
    | .stuck r => .stuck r

end

end Moonbit.Mcore
