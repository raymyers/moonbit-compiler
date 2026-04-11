/-
  MoonBit Compiler — Soundness of the Fuel-Bounded Evaluator

  Proves that `evalFuel` is sound with respect to the big-step `Eval`
  relation: whenever `evalFuel` returns `.ok o s' nl'`, there exists a
  corresponding `Eval` derivation. Similarly for `evalFuelArgs`.

  Strategy: mutual induction on the fuel parameter, case analysis on the
  expression / list, relying on the IH for recursive sub-calls (which
  use decremented fuel).

  The three stubbed cases (`.letrec`, `.letfn .recursive`, `.loop`) are
  vacuously sound: they return `.stuck`, never `.ok`, so the theorem's
  premise `... = .ok ...` cannot hold for them.
-/
import MoonbitSemantics.Mcore.FuelEval

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp)

/-! ## Loop soundness helpers -/

/-- Convert a `LoopReentry` derivation into an `Eval .loop`, given the
    args evaluation and freshness conditions. Dispatches on LoopReentry's
    constructor to pick the matching `Eval.loop*` rule. -/
private theorem loopReentryToEval
    {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
    {lt : LoopTable} {nl : Loc}
    {params : List Param} {body : Expr} {argExprs : List Expr}
    {label : LoopLabel} {argVals : List Value}
    {s₁ : Store} {nl₁ : Loc}
    {o : Outcome} {sr : Store} {nlr : Loc}
    (hlt : lt label = none)
    (hparams : ∀ p, p ∈ params → env p.binder = none)
    (hargs : EvalArgs ft env s jt lt nl argExprs argVals s₁ nl₁)
    (hreentry : LoopReentry ft env s₁ jt lt nl₁ params body argVals label o sr nlr) :
    Eval ft env s jt lt nl (.loop params body argExprs label) o sr nlr := by
  cases hreentry with
  | val hbody => exact Eval.loopVal hlt hparams hargs hbody
  | breakSome hbody => exact Eval.loopBreak hlt hparams hargs hbody
  | breakNone hbody => exact Eval.loopBreakNone hlt hparams hargs hbody
  | «continue» hbody hlen hreentry' =>
    exact Eval.loopContinue hlt hparams hargs hbody hlen.symm hreentry'
  | «return» hbody => exact Eval.loopReturn hlt hparams hargs hbody
  | error hbody => exact Eval.loopError hlt hparams hargs hbody

/-! ## Combined soundness proposition for induction -/

/-- Bundle the three soundness statements at a fuel level for mutual
    induction on `n`. -/
private def SoundnessAt (n : Nat) : Prop :=
  (∀ {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
      {lt : LoopTable} {nl : Loc} {e : Expr}
      {o : Outcome} {s' : Store} {nl' : Loc},
    evalFuel n ft env s jt lt nl e = .ok o s' nl' →
    Eval ft env s jt lt nl e o s' nl') ∧
  (∀ {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
      {lt : LoopTable} {nl : Loc} {es : List Expr}
      {vs : List Value} {s' : Store} {nl' : Loc},
    evalFuelArgs n ft env s jt lt nl es = .okVals vs s' nl' →
    EvalArgs ft env s jt lt nl es vs s' nl') ∧
  (∀ {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
      {lt : LoopTable} {nl : Loc} {es : List Expr}
      {o : Outcome} {s' : Store} {nl' : Loc},
    evalFuelArgs n ft env s jt lt nl es = .abortArgs o s' nl' →
    EvalArgsAbort ft env s jt lt nl es o s' nl' ∧ o.isAbort)

private theorem soundness_zero : SoundnessAt 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> first | simp [evalFuel] at * | simp [evalFuelArgs] at *

/-! ## The induction step

Given soundness at fuel `n`, prove soundness at fuel `n+1`. This is the bulk
of the work — a case analysis on the expression (for the `evalFuel` part)
and on the list (for the args parts).

Since the proof is long, we prove it via three mutually independent lemmas,
each handling one of the three statements in `SoundnessAt`. -/

/-- Soundness of `loopIter`: when called with `eval_fuel = n+1`, body
    evaluations happen at fuel `n`, so the IH `ihE : SoundnessAt n`
    directly covers them. Each iteration matches one step in
    `LoopReentry`'s inductive structure. -/
private theorem loopIter_sound {n : Nat}
    (ihE : ∀ {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
      {lt : LoopTable} {nl : Loc} {e : Expr}
      {o : Outcome} {s' : Store} {nl' : Loc},
      evalFuel n ft env s jt lt nl e = .ok o s' nl' →
      Eval ft env s jt lt nl e o s' nl') :
    ∀ (iter : Nat) {ft : FnTable} {env : Env}
      {params : List Param} {body : Expr} {argVals : List Value}
      {label : LoopLabel} {s : Store} {jt : JoinTable} {lt : LoopTable}
      {nl : Loc} {o : Outcome} {s' : Store} {nl' : Loc},
    loopIter iter (n+1) ft env params body argVals label s jt lt nl =
        .ok o s' nl' →
    LoopReentry ft env s jt lt nl params body argVals label o s' nl' := by
  intro iter
  induction iter with
  | zero =>
    intro ft env params body argVals label s jt lt nl o s' nl' h
    simp [loopIter] at h
  | succ k ih =>
    intro ft env params body argVals label s jt lt nl o s' nl' h
    simp only [loopIter] at h
    cases hbody : evalFuel n ft (Env.bindParams env params argVals) s jt
                  (LoopTable.extend lt label ⟨params, body⟩) nl body with
    | outOfFuel => simp only [hbody] at h; simp at h
    | stuck r => simp only [hbody] at h; simp at h
    | ok oBody sBody nlBody =>
      have hbody_eval := ihE hbody
      cases oBody with
      | val v =>
        simp only [hbody] at h
        cases h
        exact LoopReentry.val hbody_eval
      | «break» vOpt lbl =>
        cases vOpt with
        | none =>
          simp only [hbody] at h
          split at h
          · rename_i hlbl; subst hlbl
            cases h; exact LoopReentry.breakNone hbody_eval
          · exact absurd h (by simp)
        | some v =>
          simp only [hbody] at h
          split at h
          · rename_i hlbl; subst hlbl
            cases h; exact LoopReentry.breakSome hbody_eval
          · exact absurd h (by simp)
      | «continue» newVals lbl =>
        simp only [hbody] at h
        split at h
        · rename_i hlbl; subst hlbl
          split at h
          · rename_i hlen
            exact LoopReentry.continue hbody_eval hlen.symm (ih h)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      | «return» v =>
        simp only [hbody] at h
        cases h
        exact LoopReentry.return hbody_eval
      | error v =>
        simp only [hbody] at h
        cases h
        exact LoopReentry.error hbody_eval

/-- Step case for the `evalFuel` soundness. -/
private theorem soundness_step_eval (n : Nat) (ih : SoundnessAt n) :
    ∀ {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
      {lt : LoopTable} {nl : Loc} {e : Expr}
      {o : Outcome} {s' : Store} {nl' : Loc},
    evalFuel (n+1) ft env s jt lt nl e = .ok o s' nl' →
    Eval ft env s jt lt nl e o s' nl' := by
  obtain ⟨ihE, ihAok, ihAabort⟩ := ih
  intro ft env s jt lt nl e o s' nl' h
  -- Main case analysis on the expression
  cases e with
  -- Leaves
  | const c =>
    simp only [evalFuel] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact Eval.const
  | unit =>
    simp only [evalFuel] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact Eval.unit
  | var x prim =>
    simp only [evalFuel] at h
    cases hx : env x with
    | none => rw [hx] at h; simp at h
    | some v =>
      rw [hx] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      cases prim with
      | none => exact Eval.var hx
      | some p => exact Eval.varPrim hx
  | «function» params fnBody isRaw =>
    cases isRaw with
    | false =>
      simp only [evalFuel] at h
      rcases h with ⟨rfl, rfl, rfl⟩; exact Eval.function
    | true =>
      simp only [evalFuel] at h
      rcases h with ⟨rfl, rfl, rfl⟩; exact Eval.rawFunction

  -- Let-binding
  | «let» name rhs body =>
    simp only [evalFuel] at h
    cases hname : env name with
    | some _ => rw [hname] at h; simp at h
    | none =>
      rw [hname] at h
      cases hrhs : evalFuel n ft env s jt lt nl rhs with
      | outOfFuel => rw [hrhs] at h; simp at h
      | stuck r => rw [hrhs] at h; simp at h
      | ok oRhs sRhs nlRhs =>
        rw [hrhs] at h
        cases oRhs with
        | val v₁ =>
          dsimp only at h
          exact Eval.let hname (ihE hrhs) (ihE h)
        | _ =>
          dsimp only at h
          rcases h with ⟨rfl, rfl, rfl⟩
          exact Eval.letAbort (ihE hrhs) (by simp [Outcome.isAbort])

  -- Local function bindings (only the non-recursive cases are implemented;
  -- .recursive is stubbed)
  | letfn name params fnBody body kind =>
    cases kind with
    | nonRecursive =>
      simp only [evalFuel] at h
      cases hname : env name with
      | some _ => rw [hname] at h; simp at h
      | none =>
        rw [hname] at h
        exact Eval.letfnNonrec hname (ihE h)
    | recursive =>
      simp only [evalFuel] at h
      cases hname : env name with
      | some _ => rw [hname] at h; simp at h
      | none =>
        rw [hname] at h
        exact Eval.letfnRec hname (ihE h)
    | tailJoin =>
      simp only [evalFuel] at h
      cases hname : jt name with
      | some _ => rw [hname] at h; simp at h
      | none =>
        rw [hname] at h
        exact Eval.letfnTailJoin hname (ihE h)
    | nontailJoin =>
      simp only [evalFuel] at h
      cases hname : jt name with
      | some _ => rw [hname] at h; simp at h
      | none =>
        rw [hname] at h
        exact Eval.letfnNontailJoin hname (ihE h)

  -- Letrec
  | letrec bindings body =>
    simp only [evalFuel] at h
    split at h
    · exact absurd h (by simp)
    · exact Eval.letrecV2 (ihE h)

  -- Function application
  | apply func argExprs kind =>
    cases kind with
    | join =>
      simp only [evalFuel] at h
      cases hjt : jt func with
      | none => simp only [hjt] at h; simp at h
      | some entry =>
        obtain ⟨params, jbody⟩ := entry
        simp only [hjt] at h
        split at h
        · exact absurd h (by simp)
        · rename_i hfresh
          cases hargs : evalFuelArgs n ft env s jt lt nl argExprs with
          | outOfFuelArgs => simp only [hargs] at h; simp at h
          | stuckArgs _ => simp only [hargs] at h; simp at h
          | abortArgs oA sA nlA =>
            simp only [hargs] at h
            cases h
            exact Eval.applyAbort (ihAabort hargs).1
          | okVals argVals s₁ nl₁ =>
            simp only [hargs] at h
            split at h
            · rename_i hlen
              have hparams : ∀ p, p ∈ params → env p.binder = none := by
                intro p hp
                by_contra hne
                apply absurd hfresh
                simp only [not_not]
                refine List.any_eq_true.mpr ⟨p, hp, ?_⟩
                exact Option.isSome_iff_ne_none.mpr hne
              exact Eval.applyJoin hjt (ihAok hargs) hlen hparams (ihE h)
            · exact absurd h (by simp)
    | normal funcTy =>
      simp only [evalFuel] at h
      cases henv : env func with
      | some v =>
        simp only [henv] at h
        cases v with
        | closure captured params fnBody =>
          cases hargs : evalFuelArgs n ft env s jt lt nl argExprs with
          | outOfFuelArgs => simp only [hargs] at h; simp at h
          | stuckArgs _ => simp only [hargs] at h; simp at h
          | abortArgs oA sA nlA =>
            simp only [hargs] at h
            cases h
            exact Eval.applyAbort (ihAabort hargs).1
          | okVals argVals s₁ nl₁ =>
            simp only [hargs] at h
            split at h
            · exact Eval.applyClosure henv (ihAok hargs) (by assumption) (ihE h)
            · exact absurd h (by simp)
        | rawFn params fnBody =>
          cases hargs : evalFuelArgs n ft env s jt lt nl argExprs with
          | outOfFuelArgs => simp only [hargs] at h; simp at h
          | stuckArgs _ => simp only [hargs] at h; simp at h
          | abortArgs oA sA nlA =>
            simp only [hargs] at h
            cases h
            exact Eval.applyAbort (ihAabort hargs).1
          | okVals argVals s₁ nl₁ =>
            simp only [hargs] at h
            split at h
            · exact Eval.applyRawFn henv (ihAok hargs) (by assumption) (ihE h)
            · exact absurd h (by simp)
        | closureRec captured recName params fnBody =>
          cases hargs : evalFuelArgs n ft env s jt lt nl argExprs with
          | outOfFuelArgs => simp only [hargs] at h; simp at h
          | stuckArgs _ => simp only [hargs] at h; simp at h
          | abortArgs oA sA nlA =>
            simp only [hargs] at h
            cases h
            exact Eval.applyAbort (ihAabort hargs).1
          | okVals argVals s₁ nl₁ =>
            simp only [hargs] at h
            split at h
            · exact Eval.applyClosureRec henv (ihAok hargs) (by assumption) (ihE h)
            · exact absurd h (by simp)
        | closureRecMutual baseEnv allBindings params fnBody =>
          cases hargs : evalFuelArgs n ft env s jt lt nl argExprs with
          | outOfFuelArgs => simp only [hargs] at h; simp at h
          | stuckArgs _ => simp only [hargs] at h; simp at h
          | abortArgs oA sA nlA =>
            simp only [hargs] at h
            cases h
            exact Eval.applyAbort (ihAabort hargs).1
          | okVals argVals s₁ nl₁ =>
            simp only [hargs] at h
            split at h
            · exact Eval.applyClosureRecMutual henv (ihAok hargs) (by assumption) (ihE h)
            · exact absurd h (by simp)
        | _ => simp at h
      | none =>
        simp only [henv] at h
        cases hft : ft func with
        | none => simp only [hft] at h; simp at h
        | some entry =>
          obtain ⟨params, fnBody⟩ := entry
          simp only [hft] at h
          cases hargs : evalFuelArgs n ft env s jt lt nl argExprs with
          | outOfFuelArgs => simp only [hargs] at h; simp at h
          | stuckArgs _ => simp only [hargs] at h; simp at h
          | abortArgs oA sA nlA =>
            simp only [hargs] at h
            cases h
            exact Eval.applyAbort (ihAabort hargs).1
          | okVals argVals s₁ nl₁ =>
            simp only [hargs] at h
            split at h
            · exact Eval.applyTopFn hft (ihAok hargs) (by assumption) (ihE h)
            · exact absurd h (by simp)

  -- Primitives
  | prim op argExprs =>
    simp only [evalFuel] at h
    cases hargs : evalFuelArgs n ft env s jt lt nl argExprs with
    | outOfFuelArgs => simp only [hargs] at h; simp at h
    | stuckArgs _ => simp only [hargs] at h; simp at h
    | abortArgs oA sA nlA =>
      simp only [hargs] at h
      cases h
      exact Eval.primAbort (ihAabort hargs).1
    | okVals argVals s₁ nl₁ =>
      simp only [hargs] at h
      cases hep : Moonbit.Mcore.evalPrim op argVals with
      | none => simp only [hep] at h; simp at h
      | some v =>
        simp only [hep] at h
        cases h
        exact Eval.prim (ihAok hargs) hep

  -- Data construction
  | constr tag argExprs =>
    simp only [evalFuel] at h
    cases hargs : evalFuelArgs n ft env s jt lt nl argExprs with
    | outOfFuelArgs => rw [hargs] at h; simp at h
    | stuckArgs _ => rw [hargs] at h; simp at h
    | abortArgs oA sA nlA =>
      rw [hargs] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact Eval.constrAbort (ihAabort hargs).1
    | okVals argVals s₁ nl₁ =>
      rw [hargs] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact Eval.constr (ihAok hargs)
  | tuple exprs =>
    simp only [evalFuel] at h
    cases hargs : evalFuelArgs n ft env s jt lt nl exprs with
    | outOfFuelArgs => rw [hargs] at h; simp at h
    | stuckArgs _ => rw [hargs] at h; simp at h
    | abortArgs oA sA nlA =>
      rw [hargs] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact Eval.tupleAbort (ihAabort hargs).1
    | okVals vals s₁ nl₁ =>
      rw [hargs] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact Eval.tuple (ihAok hargs)
  | record fieldExprs =>
    simp only [evalFuel] at h
    cases hargs : evalFuelArgs n ft env s jt lt nl
                    (fieldExprs.map fun x => x.2.2.2) with
    | outOfFuelArgs => rw [hargs] at h; simp at h
    | stuckArgs _ => rw [hargs] at h; simp at h
    | abortArgs oA sA nlA =>
      rw [hargs] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact Eval.recordAbort (ihAabort hargs).1
    | okVals fieldVals s₁ nl₁ =>
      rw [hargs] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact Eval.record (ihAok hargs)
  | recordUpdate rec_ updFields _ =>
    simp only [evalFuel] at h
    cases hrec : evalFuel n ft env s jt lt nl rec_ with
    | outOfFuel => simp only [hrec] at h; simp at h
    | stuck _ => simp only [hrec] at h; simp at h
    | ok oRec sRec nlRec =>
      simp only [hrec] at h
      cases oRec with
      | val vRec =>
        cases vRec with
        | loc l =>
          cases hstore : sRec l with
          | none => simp only [hstore] at h; simp at h
          | some hobj =>
            simp only [hstore] at h
            cases hobj with
            | array _ => simp at h
            | record oldFields mutFlags =>
              cases hargs : evalFuelArgs n ft env sRec jt lt nlRec
                              (updFields.map fun x => x.2.2.2) with
              | outOfFuelArgs => simp only [hargs] at h; simp at h
              | stuckArgs _ => simp only [hargs] at h; simp at h
              | abortArgs oA sA nlA =>
                simp only [hargs] at h
                cases h
                exact Eval.recordUpdateAbortFields
                  (ihE hrec) hstore (ihAabort hargs).1
              | okVals newVals s₂ nl₂ =>
                simp only [hargs] at h
                cases h
                exact Eval.recordUpdate (ihE hrec) hstore (ihAok hargs) rfl
        | _ => simp at h
      | _ =>
        cases h
        exact Eval.recordUpdateAbortRec (ihE hrec) (by simp [Outcome.isAbort])
  | array exprs =>
    simp only [evalFuel] at h
    cases hargs : evalFuelArgs n ft env s jt lt nl exprs with
    | outOfFuelArgs => rw [hargs] at h; simp at h
    | stuckArgs _ => rw [hargs] at h; simp at h
    | abortArgs oA sA nlA =>
      rw [hargs] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact Eval.arrayAbort (ihAabort hargs).1
    | okVals vals s₁ nl₁ =>
      rw [hargs] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact Eval.array (ihAok hargs)

  -- Data access
  | field rec_ acc pos =>
    simp only [evalFuel] at h
    cases hrec : evalFuel n ft env s jt lt nl rec_ with
    | outOfFuel => simp only [hrec] at h; simp at h
    | stuck _ => simp only [hrec] at h; simp at h
    | ok oRec sRec nlRec =>
      simp only [hrec] at h
      cases oRec with
      | val vRec =>
        cases vRec with
        | tuple vals =>
          cases hp : vals[pos]? with
          | none => simp only [hp] at h; simp at h
          | some v =>
            simp only [hp] at h
            cases h
            exact Eval.fieldTuple (ihE hrec) hp
        | constr tag args =>
          cases hp : args[pos]? with
          | none => simp only [hp] at h; simp at h
          | some v =>
            simp only [hp] at h
            cases h
            exact Eval.fieldConstr (ihE hrec) hp
        | loc l =>
          cases hstore : sRec l with
          | none => simp only [hstore] at h; simp at h
          | some hobj =>
            simp only [hstore] at h
            cases hobj with
            | array _ => simp at h
            | record fields mutFlags =>
              cases hp : fields[pos]? with
              | none => simp only [hp] at h; simp at h
              | some v =>
                simp only [hp] at h
                cases h
                exact Eval.fieldRecord (ihE hrec) hstore hp
        | _ => simp at h
      | _ =>
        cases h
        exact Eval.fieldAbort (ihE hrec) (by simp [Outcome.isAbort])

  -- Mutation
  | mutate rec_ label fld pos =>
    simp only [evalFuel] at h
    cases hrec : evalFuel n ft env s jt lt nl rec_ with
    | outOfFuel => simp only [hrec] at h; simp at h
    | stuck _ => simp only [hrec] at h; simp at h
    | ok oRec sRec nlRec =>
      simp only [hrec] at h
      cases oRec with
      | val vRec =>
        cases vRec with
        | loc l =>
          cases hfld : evalFuel n ft env sRec jt lt nlRec fld with
          | outOfFuel => simp only [hfld] at h; simp at h
          | stuck _ => simp only [hfld] at h; simp at h
          | ok oFld sFld nlFld =>
            simp only [hfld] at h
            cases oFld with
            | val vFld =>
              cases hstore : sFld l with
              | none => simp only [hstore] at h; simp at h
              | some hobj =>
                simp only [hstore] at h
                cases hobj with
                | array _ => simp at h
                | record fields mutFlags =>
                  cases h
                  exact Eval.mutate (ihE hrec) (ihE hfld) hstore
            | _ =>
              cases h
              exact Eval.mutateAbortFld (ihE hrec) (ihE hfld)
                (by simp [Outcome.isAbort])
        | _ => simp at h
      | _ =>
        cases h
        exact Eval.mutateAbortRec (ihE hrec) (by simp [Outcome.isAbort])

  -- Assignment
  | assign x e =>
    simp only [evalFuel] at h
    cases he : evalFuel n ft env s jt lt nl e with
    | outOfFuel => simp only [he] at h; simp at h
    | stuck _ => simp only [he] at h; simp at h
    | ok oE sE nlE =>
      simp only [he] at h
      cases oE with
      | val v =>
        cases h
        exact Eval.assign (ihE he)
      | _ =>
        cases h
        exact Eval.assignAbort (ihE he) (by simp [Outcome.isAbort])

  -- Sequencing
  | seq exprs last =>
    simp only [evalFuel] at h
    cases hargs : evalFuelArgs n ft env s jt lt nl exprs with
    | outOfFuelArgs => simp only [hargs] at h; simp at h
    | stuckArgs _ => simp only [hargs] at h; simp at h
    | abortArgs oA sA nlA =>
      simp only [hargs] at h
      cases h
      exact Eval.seqAbort (ihAabort hargs).1
    | okVals _ s₁ nl₁ =>
      simp only [hargs] at h
      exact Eval.seq (ihAok hargs) (ihE h)

  -- Conditionals
  | «if» cond ifso ifnot =>
    simp only [evalFuel] at h
    cases hc : evalFuel n ft env s jt lt nl cond with
    | outOfFuel => simp only [hc] at h; simp at h
    | stuck _ => simp only [hc] at h; simp at h
    | ok oC sC nlC =>
      simp only [hc] at h
      cases oC with
      | val vC =>
        cases vC with
        | const c =>
          cases c with
          | bool b =>
            cases b with
            | true => exact Eval.ifTrue (ihE hc) (ihE h)
            | false =>
              cases ifnot with
              | none =>
                cases h
                exact Eval.ifFalseNoElse (ihE hc)
              | some e' => exact Eval.ifFalse (ihE hc) (ihE h)
          | _ => simp at h
        | _ => simp at h
      | _ =>
        cases h
        exact Eval.ifAbort (ihE hc) (by simp [Outcome.isAbort])

  -- Pattern matching
  | switchConstr obj cases_ dflt =>
    simp only [evalFuel] at h
    cases ho : evalFuel n ft env s jt lt nl obj with
    | outOfFuel => simp only [ho] at h; simp at h
    | stuck _ => simp only [ho] at h; simp at h
    | ok oO sO nlO =>
      simp only [ho] at h
      cases oO with
      | val vO =>
        cases vO with
        | constr tag args =>
          cases hfc : findConstrCase cases_ tag with
          | none =>
            simp only [hfc] at h
            cases dflt with
            | none => simp at h
            | some d => exact Eval.switchConstrDefault (ihE ho) hfc (ihE h)
          | some entry =>
            simp only [hfc] at h
            obtain ⟨binder, branch⟩ := entry
            cases binder with
            | some x =>
              cases hex : env x with
              | some _ => simp only [hex] at h; simp at h
              | none =>
                simp only [hex] at h
                have hbinder_fresh : ∀ y, some x = some y → env y = none := by
                  intro y hy; cases hy; exact hex
                exact Eval.switchConstr (binder := some x) (ihE ho) hfc
                  hbinder_fresh (ihE h)
            | none =>
              have hbinder_fresh : ∀ y, (none : Option Var) = some y → env y = none :=
                fun _ h => by cases h
              exact Eval.switchConstr (binder := none) (ihE ho) hfc
                hbinder_fresh (ihE h)
        | _ => simp at h
      | _ =>
        cases h
        exact Eval.switchConstrAbort (ihE ho) (by simp [Outcome.isAbort])
  | switchConstant obj cases_ dflt =>
    simp only [evalFuel] at h
    cases ho : evalFuel n ft env s jt lt nl obj with
    | outOfFuel => simp only [ho] at h; simp at h
    | stuck _ => simp only [ho] at h; simp at h
    | ok oO sO nlO =>
      simp only [ho] at h
      cases oO with
      | val vO =>
        cases vO with
        | const c =>
          cases hfc : findConstantCase cases_ c with
          | none =>
            simp only [hfc] at h
            exact Eval.switchConstantDefault (ihE ho) hfc (ihE h)
          | some branch =>
            simp only [hfc] at h
            exact Eval.switchConstantMatch (ihE ho) hfc (ihE h)
        | _ => simp at h
      | _ =>
        cases h
        exact Eval.switchConstantAbort (ihE ho) (by simp [Outcome.isAbort])

  -- Loops
  | loop params body argExprs label =>
    simp only [evalFuel] at h
    cases hlt : lt label with
    | some _ => simp only [hlt] at h; simp at h
    | none =>
      simp only [hlt] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hfresh
        cases hargs : evalFuelArgs n ft env s jt lt nl argExprs with
        | outOfFuelArgs => simp only [hargs] at h; simp at h
        | stuckArgs _ => simp only [hargs] at h; simp at h
        | abortArgs oA sA nlA =>
          simp only [hargs] at h
          cases h
          exact Eval.loopAbort (ihAabort hargs).1
        | okVals argVals s₁ nl₁ =>
          simp only [hargs] at h
          split at h
          · rename_i hlen
            have hparams_fresh : ∀ p, p ∈ params → env p.binder = none := by
              intro p hp
              by_contra hne
              apply absurd hfresh
              simp only [ne_eq, not_not]
              refine List.any_eq_true.mpr ⟨p, hp, ?_⟩
              exact Option.isSome_iff_ne_none.mpr hne
            -- h : loopIter (n+1) (n+1) ft env params body argVals label s₁ jt lt nl₁ = .ok o s' nl'
            -- Build a LoopReentry derivation via loopIter_sound, then convert to Eval
            have hreentry := loopIter_sound ihE (n+1) h
            exact loopReentryToEval hlt hparams_fresh (ihAok hargs) hreentry
          · exact absurd h (by simp)

  -- Break / continue
  | «break» argOpt label =>
    cases argOpt with
    | none =>
      simp only [evalFuel] at h
      cases h
      exact Eval.breakNone
    | some arg =>
      simp only [evalFuel] at h
      cases harg : evalFuel n ft env s jt lt nl arg with
      | outOfFuel => simp only [harg] at h; simp at h
      | stuck _ => simp only [harg] at h; simp at h
      | ok oA sA nlA =>
        simp only [harg] at h
        cases oA with
        | val v =>
          cases h
          exact Eval.breakSome (ihE harg)
        | _ =>
          cases h
          exact Eval.breakAbort (ihE harg) (by simp [Outcome.isAbort])
  | «continue» argExprs label =>
    simp only [evalFuel] at h
    cases hargs : evalFuelArgs n ft env s jt lt nl argExprs with
    | outOfFuelArgs => simp only [hargs] at h; simp at h
    | stuckArgs _ => simp only [hargs] at h; simp at h
    | abortArgs oA sA nlA =>
      simp only [hargs] at h
      cases h
      exact Eval.continueAbort (ihAabort hargs).1
    | okVals vals s₁ nl₁ =>
      simp only [hargs] at h
      cases h
      exact Eval.continue (ihAok hargs)

  -- Short-circuit logical operators
  | and lhs rhs =>
    simp only [evalFuel] at h
    cases hl : evalFuel n ft env s jt lt nl lhs with
    | outOfFuel => simp only [hl] at h; simp at h
    | stuck _ => simp only [hl] at h; simp at h
    | ok oL sL nlL =>
      simp only [hl] at h
      cases oL with
      | val vL =>
        cases vL with
        | const c =>
          cases c with
          | bool b =>
            cases b with
            | true => exact Eval.andTrue (ihE hl) (ihE h)
            | false =>
              cases h
              exact Eval.andFalse (ihE hl)
          | _ => simp at h
        | _ => simp at h
      | _ =>
        cases h
        exact Eval.andAbort (ihE hl) (by simp [Outcome.isAbort])
  | or lhs rhs =>
    simp only [evalFuel] at h
    cases hl : evalFuel n ft env s jt lt nl lhs with
    | outOfFuel => simp only [hl] at h; simp at h
    | stuck _ => simp only [hl] at h; simp at h
    | ok oL sL nlL =>
      simp only [hl] at h
      cases oL with
      | val vL =>
        cases vL with
        | const c =>
          cases c with
          | bool b =>
            cases b with
            | true =>
              cases h
              exact Eval.orTrue (ihE hl)
            | false => exact Eval.orFalse (ihE hl) (ihE h)
          | _ => simp at h
        | _ => simp at h
      | _ =>
        cases h
        exact Eval.orAbort (ihE hl) (by simp [Outcome.isAbort])

  -- Error handling
  | handleError obj kind =>
    simp only [evalFuel] at h
    cases ho : evalFuel n ft env s jt lt nl obj with
    | outOfFuel => simp only [ho] at h; simp at h
    | stuck _ => simp only [ho] at h; simp at h
    | ok oO sO nlO =>
      simp only [ho] at h
      cases oO with
      | val v =>
        cases kind with
        | toResult =>
          cases h
          exact Eval.handleErrorToResultOk (ihE ho)
        | joinapply target =>
          cases h
          exact Eval.handleErrorJoinOk (ihE ho)
        | returnErr okTy =>
          cases h
          exact Eval.handleErrorReturnErrOk (ihE ho)
      | error v =>
        cases kind with
        | toResult =>
          cases h
          exact Eval.handleErrorToResultErr (ihE ho)
        | joinapply target =>
          cases hjt : jt target with
          | none => simp only [hjt] at h; simp at h
          | some entry =>
            obtain ⟨jparams, jbody⟩ := entry
            simp only [hjt] at h
            split at h
            · exact absurd h (by simp)
            · rename_i hfresh
              have hparams : ∀ p, p ∈ jparams → env p.binder = none := by
                intro p hp
                by_contra hne
                apply absurd hfresh
                simp only [not_not]
                refine List.any_eq_true.mpr ⟨p, hp, ?_⟩
                exact Option.isSome_iff_ne_none.mpr hne
              exact Eval.handleErrorJoinErr (ihE ho) hjt hparams (ihE h)
        | returnErr okTy =>
          cases h
          exact Eval.handleErrorReturnErrErr (ihE ho)
      | _ =>
        cases h
        exact Eval.handleErrorPropagate (ihE ho) (by intro _ h; cases h)
          (by intro _ h; cases h)

  -- Return
  | «return» e kind =>
    simp only [evalFuel] at h
    cases he : evalFuel n ft env s jt lt nl e with
    | outOfFuel => simp only [he] at h; simp at h
    | stuck _ => simp only [he] at h; simp at h
    | ok oE sE nlE =>
      simp only [he] at h
      cases oE with
      | val v =>
        cases kind with
        | singleValue =>
          cases h
          exact Eval.returnSingle (ihE he)
        | errorResult isErr retTy =>
          cases isErr with
          | true =>
            cases h
            exact Eval.returnError (ihE he)
          | false =>
            cases h
            exact Eval.returnOk (ihE he)
      | _ =>
        cases h
        exact Eval.returnAbort (ihE he) (by simp [Outcome.isAbort])

  -- Objects
  | object self =>
    simp only [evalFuel] at h
    cases hs : evalFuel n ft env s jt lt nl self with
    | outOfFuel => simp only [hs] at h; simp at h
    | stuck _ => simp only [hs] at h; simp at h
    | ok oS sS nlS =>
      simp only [hs] at h
      cases oS with
      | val v =>
        cases h
        exact Eval.object (ihE hs)
      | _ =>
        cases h
        exact Eval.objectAbort (ihE hs) (by simp [Outcome.isAbort])

/-- Step case for `evalFuelArgs` soundness: `okVals` case. -/
private theorem soundness_step_args_ok (n : Nat) (ih : SoundnessAt n) :
    ∀ {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
      {lt : LoopTable} {nl : Loc} {es : List Expr}
      {vs : List Value} {s' : Store} {nl' : Loc},
    evalFuelArgs (n+1) ft env s jt lt nl es = .okVals vs s' nl' →
    EvalArgs ft env s jt lt nl es vs s' nl' := by
  obtain ⟨ihE, ihAok, _⟩ := ih
  intro ft env s jt lt nl es vs s' nl' h
  cases es with
  | nil =>
    simp only [evalFuelArgs] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact EvalArgs.nil
  | cons e es =>
    simp only [evalFuelArgs] at h
    cases he : evalFuel n ft env s jt lt nl e with
    | outOfFuel => rw [he] at h; simp at h
    | stuck _ => rw [he] at h; simp at h
    | ok oE sE nlE =>
      rw [he] at h
      cases oE with
      | val v =>
        dsimp only at h
        cases hes : evalFuelArgs n ft env sE jt lt nlE es with
        | outOfFuelArgs => rw [hes] at h; simp at h
        | stuckArgs _ => rw [hes] at h; simp at h
        | abortArgs _ _ _ => rw [hes] at h; simp at h
        | okVals vs' sR nlR =>
          rw [hes] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          exact EvalArgs.cons (ihE he) (ihAok hes)
      | _ => simp at h

/-- Step case for `evalFuelArgs` soundness: `abortArgs` case. -/
private theorem soundness_step_args_abort (n : Nat) (ih : SoundnessAt n) :
    ∀ {ft : FnTable} {env : Env} {s : Store} {jt : JoinTable}
      {lt : LoopTable} {nl : Loc} {es : List Expr}
      {o : Outcome} {s' : Store} {nl' : Loc},
    evalFuelArgs (n+1) ft env s jt lt nl es = .abortArgs o s' nl' →
    EvalArgsAbort ft env s jt lt nl es o s' nl' ∧ o.isAbort := by
  obtain ⟨ihE, _, ihAabort⟩ := ih
  intro ft env s jt lt nl es o s' nl' h
  cases es with
  | nil => simp only [evalFuelArgs] at h; simp at h
  | cons e es =>
    simp only [evalFuelArgs] at h
    cases he : evalFuel n ft env s jt lt nl e with
    | outOfFuel => rw [he] at h; simp at h
    | stuck _ => rw [he] at h; simp at h
    | ok oE sE nlE =>
      rw [he] at h
      cases oE with
      | val v =>
        dsimp only at h
        cases hes : evalFuelArgs n ft env sE jt lt nlE es with
        | outOfFuelArgs => rw [hes] at h; simp at h
        | stuckArgs _ => rw [hes] at h; simp at h
        | okVals _ _ _ => rw [hes] at h; simp at h
        | abortArgs oA sA nlA =>
          rw [hes] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          obtain ⟨habort, hisAbort⟩ := ihAabort hes
          exact ⟨EvalArgsAbort.later (ihE he) habort, hisAbort⟩
      | _ =>
        dsimp only at h
        rcases h with ⟨rfl, rfl, rfl⟩
        refine ⟨EvalArgsAbort.here (ihE he) ?_, ?_⟩ <;>
          simp [Outcome.isAbort]

/-- Combined induction step. -/
private theorem soundness_succ (n : Nat) (ih : SoundnessAt n) : SoundnessAt (n+1) :=
  ⟨soundness_step_eval n ih, soundness_step_args_ok n ih, soundness_step_args_abort n ih⟩

/-- Soundness at every fuel level. -/
private theorem soundness_all (n : Nat) : SoundnessAt n := by
  induction n with
  | zero => exact soundness_zero
  | succ k ih => exact soundness_succ k ih

/-! ## Public interface -/

/-- **Soundness of `evalFuel`**: if the fuel-bounded evaluator returns
    `.ok`, the corresponding big-step `Eval` derivation exists. -/
theorem evalFuel_sound {n : Nat} {ft : FnTable} {env : Env} {s : Store}
    {jt : JoinTable} {lt : LoopTable} {nl : Loc} {e : Expr}
    {o : Outcome} {s' : Store} {nl' : Loc}
    (h : evalFuel n ft env s jt lt nl e = .ok o s' nl') :
    Eval ft env s jt lt nl e o s' nl' :=
  (soundness_all n).1 h

/-- **Soundness of `evalFuelArgs`** (ok case). -/
theorem evalFuelArgs_sound_ok {n : Nat} {ft : FnTable} {env : Env} {s : Store}
    {jt : JoinTable} {lt : LoopTable} {nl : Loc} {es : List Expr}
    {vs : List Value} {s' : Store} {nl' : Loc}
    (h : evalFuelArgs n ft env s jt lt nl es = .okVals vs s' nl') :
    EvalArgs ft env s jt lt nl es vs s' nl' :=
  (soundness_all n).2.1 h

/-- **Soundness of `evalFuelArgs`** (abort case). -/
theorem evalFuelArgs_sound_abort {n : Nat} {ft : FnTable} {env : Env} {s : Store}
    {jt : JoinTable} {lt : LoopTable} {nl : Loc} {es : List Expr}
    {o : Outcome} {s' : Store} {nl' : Loc}
    (h : evalFuelArgs n ft env s jt lt nl es = .abortArgs o s' nl') :
    EvalArgsAbort ft env s jt lt nl es o s' nl' ∧ o.isAbort :=
  (soundness_all n).2.2 h

end Moonbit.Mcore
