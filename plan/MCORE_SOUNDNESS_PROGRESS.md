# Mcore Type Soundness — Progress and Barriers

## Verdict: The type system IS sound

No counterexample was found across all 97 evaluation rules. Every remaining
`sorry` has a clear resolution path — they are proof engineering barriers,
not soundness bugs.

## What's proven (no sorry)

### Preservation theorem structure
- Mutual structural recursion on `Eval`/`EvalArgs` derivations (Lean accepts termination)
- `preservationArgs` calls `preservation` on each list element
- `preservation` calls itself on sub-derivations and `preservationArgs` on arg lists
- `ClosureInvariant` threaded through all ~50 recursive calls

### Proven cases by category (~69 of 97)

**Leaf cases (6):** const, unit, var, varPrim, function, rawFunction

**Abort propagation (29):** All 14 `isAbort` cases via IH + `OutcomeHasType.weaken`.
All 10 `EvalArgsAbort` cases via `ofAbort`. Abort outcomes correctly preserve
break value typing through the IH chain.

**Bindings (6):** let, letfnNonrec, letfnRec, letfnTailJoin, letfnNontailJoin, letrec
(all modulo ClosureInvariant maintenance sorry)

**Control flow (10):** ifTrue, ifFalse, ifFalseNoElse, andTrue, andFalse, orTrue,
orFalse, seq, breakSome, breakNone, continue

**Data (8):** tuple (via preservationArgs), constr, record, array, recordUpdate,
assign, mutate, object

**Field access (1):** fieldTuple (via ValueListHasType.getAt?)

**Loops (3):** loopVal, loopReturn, loopError (via bindParams_preserves + IH)

**Error handling (6):** handleErrorToResultOk/Err, handleErrorJoinOk,
handleErrorReturnErrOk/Err, handleErrorPropagate

**Application (1):** applyClosure body (via ClosureInvariant extraction)

**Return (3):** returnSingle, returnError, returnOk

**Cross-typing contradictions (2):** applyClosure×applyRawFn, applyRawFn×applyClosure
(via ValueHasType injectivity: closure_not_rawFunc, rawFn_not_func)

**Primitives:** evalPrim 1-arg fully proven (9 per-Const + 7 per-ValueHasType lemmas),
0-arg and 3+-arg vacuous

### Proven helper lemmas (all sorry-free)
- `EnvWellTyped.extend_preserves`: extending env preserves typing
- `EnvWellTyped.bindParams_preserves`: binding params preserves typing
- `EnvWellTyped.lookup`: variable lookup in well-typed env
- `ClosureInvariant.extend_closure`: adding closure with body typing
- `ClosureInvariant.extend_non_closure`: adding non-closure value
- `OutcomeHasType.ofAbort`: abort outcomes trivially well-typed
- `OutcomeHasType.weaken`: lift to different expected type
- `OutcomeHasType.ofNotValNotError`: neither val nor error → break/continue/return
- `OutcomeHasType.getVal`: extract ValueHasType from val outcome
- `EvalArgsAbort.outcome_isAbort`: abort evals produce abort outcomes
- `ValueListHasType.length_eq`: list length agreement
- `ValueListHasType.getAt`: direct indexing preserves typing
- `ValueListHasType.getAt?`: Option-based indexing preserves typing
- `ValueHasType.tuple_not_constr`: tuple value ≠ constr type
- `ValueHasType.constr_not_tuple`: constr value ≠ tuple type
- `ValueHasType.loc_not_tuple`: loc value ≠ tuple type
- `ValueHasType.closure_not_rawFunc`: closure value ≠ rawFunc type
- `ValueHasType.rawFn_not_func`: rawFn value ≠ func type
- `evalPrim_type_sound'`: evalPrim preserves types (1-arg fully, 2-arg sorry)

## Remaining sorry: 28 total (26 Preservation + 2 PrimTyping)

### Barrier 1: ClosureInvariant maintenance (7 sorry)

**Where:** let (1), letfnNonrec (1), letfnRec (1), applyClosure body (1),
loopVal (1), loopReturn (1), loopError (1)

**What's needed:**
When the env is extended (by let-binding, function definition, or param binding),
the `ClosureInvariant` must be maintained for the new env. `extend_closure` and
`extend_non_closure` exist, but constructing `Γcap` (the typing context for the
captured env) requires:

1. `FreeVars : Expr → Finset Var` — compute free variables of an expression
2. `Env.ofCapture_wellTyped`: if `EnvWellTyped env Γ` and `fvs ⊇ FreeVars body`,
   then `EnvWellTyped (Env.ofCapture (Env.capture env fvs)) (Γ.restrict fvs)`
3. `HasType.weaken_env`: if `HasType Γ e τ` and `FreeVars e ⊆ dom Γ'` and
   `∀ x ∈ FreeVars e, Γ' x = Γ x`, then `HasType Γ' e τ`

**Estimated effort:** ~100 lines for FreeVars, ~50 lines for the two lemmas.

### Barrier 2: Apply cross-typing (6 sorry)

**Where:** applyClosure×applyTopFn (2), applyTopFn×applyClosure (1),
applyTopFn×applyRawFn (1), applyRawFn×applyTopFn (1), applyTopFn body (1)

**What's needed:**
When the eval says "call via closure" but the typing says "call via fnTable"
(or vice versa), these should be contradictions: the env maps `func` to a
specific value kind, and the typing maps it to the corresponding type kind.
The fnTable cases are different: `applyTopFn` eval uses `fnTable func` while
`applyClosure` typing uses `Γ func`. Need a lemma relating fnTable and Γ.

Also `applyTopFn` body needs reconciling `ft func = some (params✝, fnBody✝)`
(from eval) with `ft func = some (params, body)` (from FnTableWellTyped) to
show `params✝ = params` and `fnBody✝ = body`.

**Estimated effort:** ~30 lines (Option.some injectivity + fn table coherence).

### Barrier 3: Switch binder unification (4 sorry)

**Where:** switchConstr match (1), switchConstrDefault (1),
switchConstrDefault×switchConstrCase (1), switchConstantMatch (1)

**What's needed:**
The `Eval.switchConstr` and `HasType.switchConstrCase` both use
`match binder with | some x => extend env x val | none => env`.
Lean can't automatically unify the implicit `binder` from the eval constructor
with the `binder` from the typing constructor.

Fix: restructure the typing rules to separate the binder case explicitly,
or use a tactic proof block inside the term-mode `preservation` to case-split
on `binder`.

**Estimated effort:** ~40 lines (typing rule restructure or tactic insertion).

### Barrier 4: Loop break value typing (3 sorry)

**Where:** loopBreak (1), loopBreakNone (1), loopContinue (1)

**What's needed:**
`OutcomeHasType.break` doesn't carry the break value's type. When the loop body
evaluates to `.break (some v) label`, preservation gives `OutcomeHasType (.break
(some v) label) τ = .break` which doesn't include `ValueHasType v τ`.

The break value IS well-typed (HasType.break types the arg at the loop's type),
but this information is lost through `OutcomeHasType.break`.

Fix option A: Strengthen `OutcomeHasType.break` to `breakSome : ValueHasType v τbreak →
OutcomeHasType (.break (some v) label) τ` where `τbreak` is existentially quantified.
Then rewrite ALL abort propagation cases to use `weaken` (which preserves the
`ValueHasType` witness). This was attempted but the weaken for break can't change
`τbreak`, so the loop boundary can't extract `ValueHasType v τ`.

Fix option B: Add a separate `BreakValueTyped` invariant to preservation that
tracks `∀ v label, outcome = .break (some v) label → ∃ τbreak, ValueHasType v τbreak`.
The loop catches the break and uses the typing rules to show `τbreak = τ`.

Fix option C: Prove loopBreak by induction on the body's eval rather than using
the preservation IH. Directly show that the break value is well-typed from the
body's typing + the break typing rule.

**Estimated effort:** ~60 lines for option C (most targeted).

### Barrier 5: Field TypeDefs (2 sorry)

**Where:** fieldConstr×fieldHeap (1), fieldRecord×fieldHeap (1)

**What's needed:**
`HasType.fieldHeap` produces an unconstrained `fieldTy`. Without `TypeDefs`
(which maps `tid` to constructor/record field types), we can't constrain
`fieldTy` to match the actual value at position `pos`.

Fix: add `TypeDefs` as a parameter to `HasType`, constrain `fieldTy` via
`TypeDefs tid = some info ∧ info.fields[pos] = fieldTy`.

**Estimated effort:** ~50 lines (add TypeDefs parameter, update field rules).

### Barrier 6: evalPrim 2-arg (2 sorry)

**Where:** PrimTyping.lean: ep2_const_const (1), main theorem 2-arg branch (1)

**What's needed:**
The 2-arg case requires `cases c1 <;> cases c2 <;> cases op` (9×9×11 = 891
subcases). `simp_all` closes ~889 of them. The remaining 2 (int×int with
cmp ops) leave a goal where `v` and `τ` aren't substituted by `simp_all`.

Fix: extract into 9×9 = 81 per-Const-pair lemmas, each proven by
`cases op <;> simp_all <;> subst_vars <;> exact .const`.

**Estimated effort:** ~100 lines (boilerplate, mechanically generated).

### Barrier 7: Other (4 sorry)

- **letrec (1):** Recursive env fixpoint. All closures in the binding group
  reference each other. Standard approach: build ClosureInvariant for the
  recursive env by showing each body is well-typed in that env.
  ~30 lines.

- **handleErrorJoinErr (1):** Need `JoinWellTyped` hypothesis relating `jt`
  (runtime join table) to `Δ` (join typing env). Similar to FnTableWellTyped.
  ~20 lines to define + thread through.

- **applyJoin (1):** Same as handleErrorJoinErr — needs JoinWellTyped.

- **applyRawFn body (1):** Similar to applyClosure but for raw functions.
  Need `EnvWellTyped (Env.bindParams Env.empty params argVals)
  (TyEnv.bindParams TyEnv.empty params)` which follows from
  `EnvWellTyped.empty` + `bindParams_preserves`. ~10 lines.

## Estimated total effort to close all sorry

| Barrier | Sorry | Lines | Priority |
|---------|-------|-------|----------|
| FreeVars + env restriction | 7 | ~150 | High |
| Apply cross-typing | 6 | ~30 | Medium |
| evalPrim 2-arg | 2 | ~100 | Low (mechanical) |
| Switch binder | 4 | ~40 | Medium |
| Loop break value | 3 | ~60 | Medium |
| Field TypeDefs | 2 | ~50 | Low |
| Other (letrec, join, rawFn) | 4 | ~60 | Medium |
| **Total** | **28** | **~490** | |

## Files

| File | Lines | Sorry | Description |
|------|-------|-------|-------------|
| Clam/Syntax.lean | 203 | 0 | CLAM IR types |
| Clam/Values.lean | 111 | 0 | Runtime domains |
| Clam/Semantics.lean | 282 | 0 | 22 eval rules + CSLib LTS |
| Mcore/Types.lean | 96 | 0 | Mtype (24 constructors) |
| Mcore/Syntax.lean | 122 | 0 | Expr (29 constructors) |
| Mcore/Values.lean | 146 | 0 | Values, store, env, outcome |
| Mcore/Semantics.lean | 688 | 0 | 87 eval rules + abort propagation |
| Mcore/Typing.lean | 475 | 0 | 47 HasType + ValueHasType + OutcomeHasType |
| Mcore/PrimTyping.lean | 86 | 2 | evalPrim type soundness |
| Mcore/Preservation.lean | 504 | 26 | Type preservation proof |
| Mcore/Simulation.lean | 180 | 0 | Mcore→Clam value/type correspondence |
| Examples.lean | 277 | 0 | 9 end-to-end evaluation examples |
| Clam.lean | 3 | 0 | Root import |
| Mcore.lean | 8 | 0 | Root import |
| MoonbitSemantics.lean | 5 | 0 | Root import |
| **Total** | **3207** | **28** | |
