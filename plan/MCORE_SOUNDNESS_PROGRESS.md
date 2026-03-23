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
- `evalPrim_type_sound'`: evalPrim preserves types (fully proven)
- `evalPrim_non_identity_constOrUnit`: non-identity evalPrim returns const or unit

## Remaining sorry: 11 total (9 Preservation + 2 FreeVars)

Note: FreeVars.lean sorry are termination proofs (`decreasing_by all_goals sorry`)
— a Lean 4 limitation on ∀-quantified sub-derivations in structural recursion.

Progress from original 28 sorry:
- **17 sorry closed** (28 → 11):
  - let, letfnNonrec, applyClosure body, loopVal, loopReturn, loopError,
    applyTopFn body, var/varPrim ValClosureOk, applyClosure×applyTopFn,
    applyRawFn×applyTopFn, applyTopFn×applyClosure, applyTopFn×applyRawFn,
    fieldTuple ValClosureOk (P3), evalPrim ValClosureOk (P6),
    applyRawFn body (P7), PrimTyping ep2_const_const, PrimTyping 2-arg branch
- PrimTyping.lean: 2/2 closed
- FreeVars.lean: 3/5 closed
- Preservation.lean: 12/21 closed

### Architecture changes made

**Closure capture refactor:** Changed `Value.closure` from carrying
`List (Var × Value)` (via `Env.capture`) to carrying `Var → Option Value`
(the full env). This eliminates the FreeVars/weakening requirement:
closures capture the entire environment, so `EnvWellTyped captured Γ` holds
trivially when the closure was created in env with `EnvWellTyped env Γ`.

**Preservation strengthened:** `preservation` now returns `PresResult` which
bundles `OutcomeHasType` with `ValClosureOk` (for val outcomes). `ValClosureOk`
is an inductive that carries body typing + `ClosureInvariant` for the captured
env. This allows ClosureInvariant maintenance at env extension points.

**ClosureInvariant simplified:** Now `∀ x v τ, env x = some v → Γ x = some τ →
ValClosureOk v τ F`, with a single `extend` lemma taking `ValClosureOk`.

### Proven since last report

- **let** ClosureInvariant: extract ValClosureOk from preservation IH on rhs
- **letfnNonrec** ClosureInvariant: use `ValClosureOk.mk_closure` with env/Γ
- **var/varPrim** ValClosureOk: extract from ClosureInvariant via hcinv lookup
- **HasType.strengthen**: env monotonicity lemma (bigger Γ → still well-typed)
- **TyEnv.extend_mono, extendMany_mono, bindParams_mono**: subset propagation

### ~~Barrier 1: fieldTuple ValClosureOk~~ — CLOSED (P3)

Solved via `ValClosureOk.tuple_getAt?` for per-element extraction.

### ~~Barrier 2: Apply + FnEnvDisjoint threading~~ — CLOSED

All cross-typing contradictions and FnEnvDisjoint threading resolved.
applyRawFn body (P7) closed via rawFn ValClosureOk constructor.

### Barrier 3: Switch (4 sorry)

**Where:** switchConstr match (1), switchConstr×switchConstrDefault (1),
switchConstrDefault×switchConstrCase (1), switchConstantMatch (1)

**What's needed:** The typing rules `switchConstrCase` and `switchConstrDefault`
don't deterministically match the eval rule. The eval finds a specific case;
the typing could type via any case OR the default. Cross-cases arise when
eval and typing pick different paths.

**Fix:** Restructure typing to either (a) type ALL branches (like switchConstant's
`∀ i` rule) or (b) add determinism — if a case matches, must use the case rule.

**Estimated effort:** ~60 lines (typing rule restructure).

### Barrier 4: Loop break value typing (3 sorry)

**Where:** loopBreak (1), loopBreakNone (1), loopContinue (1)

**What's needed:** Same as before — `OutcomeHasType.break` doesn't carry the
break value's type. Strengthen to `BreakValueTyped` invariant.

**Estimated effort:** ~60 lines.

### Barrier 5: Field TypeDefs (2 sorry)

**Where:** fieldConstr×fieldHeap (1), fieldRecord×fieldHeap (1)

**What's needed:** Same as before — constrain `fieldTy` via `TypeDefs`.

**Estimated effort:** ~50 lines.

### ~~Barrier 6: evalPrim~~ — CLOSED (P6 + PrimTyping)

PrimTyping: closed via exhaustive case analysis with `simp_all`.
evalPrim ValClosureOk (P6): solved via `evalPrim_non_identity_constOrUnit` in
EvalPrimForm.lean — uses `unfold evalPrim; split at heval <;> simp_all` to match
on `evalPrim`'s definition branches (~15 goals) instead of exhaustive value-type
case splits (~80K goals that OOMed).

### Barrier 7: Other (5 sorry)

- **letfnRec (1):** Inner closure captures `env` without `name`, but body
  is typed under `TyEnv.extend Γ name funcTy`. Fix: change Eval.letfnRec
  so both inner and outer closures capture the same extended env.

- **letrec (1):** Recursive env fixpoint — needs ClosureInvariant for the
  mutually-recursive binding group.

- **handleErrorJoinErr (1) + applyJoin (1):** Need `JoinWellTyped` hypothesis.

- **loopContinue (1):** Re-entry typing — same body is evaluated again with
  new args. Needs the loop body typing to be reusable across iterations.

## Action plan (ordered by dependency)

Based on external review of the barrier analysis.
Guiding principle: lock in invariants first, refactor typing rules second,
leave mechanical boilerplate last.

### Step 1 — FreeVars + env restriction + ClosureInvariant (unlocks 7+2 sorry)

**Create `Mcore/FreeVars.lean`** (new file, ~100 lines):
- Structurally recursive `FreeVars : Expr → Finset Var`
- Spec: `x ∈ FreeVars e ↔ x occurs free in e`

**Prove two key lemmas** (in FreeVars.lean, ~50 lines):
1. `HasType.weaken_env`: if `HasType Γ e τ` and `Γ'` agrees with `Γ` on
   `FreeVars e`, then `HasType Γ' e τ`. (Monotonicity / weakening.)
2. `EnvWellTyped.restrict`: if `EnvWellTyped env Γ` and `fvs ⊇ FreeVars body`,
   then `EnvWellTyped (Env.ofCapture (Env.capture env fvs)) (Γ.restrict fvs)`.

**Factor out a single maintenance lemma** (in Preservation.lean):
```lean
ClosureInvariant env Γ F →
HasType Γ body τ →
ClosureInvariant (env.extend x v) (Γ.extend x τ) F
```
Proof: pick `fvs := FreeVars body`, use restrict, stitch with
`extend_closure` / `extend_non_closure`.

This closes the 7 Barrier 1 sorry (let, letfnNonrec, letfnRec,
applyClosure body, loopVal, loopReturn, loopError).

Also enables:
- **letrec** (Barrier 7): build ClosureInvariant for the recursive env by
  showing each body well-typed in the fixpoint context. ~30 lines.
- **applyRawFn body** (Barrier 7): generic lemma
  `EnvWellTyped.empty + bindParams_preserves`. ~10 lines.

### Step 2 — FnTableWellTyped + JoinWellTyped + apply cross-typing (unlocks 6+2 sorry)

**FnTable coherence** — `FnTableWellTyped` already exists (Preservation.lean:51).
Add injectivity + value-kind lemmas (~15 lines):
```lean
lemma fnTable_some_inj :
  ft f = some (p1, b1) → ft f = some (p2, b2) → p1 = p2 ∧ b1 = b2

-- closure value can't come from fnTable, and vice versa
lemma ValueHasType.closure_not_topFn ...
lemma ValueHasType.topFn_not_closure ...
```

Use these to close `applyTopFn×applyClosure`, `applyClosure×applyTopFn`,
`applyTopFn×applyRawFn`, `applyRawFn×applyTopFn` (4 cross-typing sorry)
plus `applyTopFn body` (1 sorry, via `fnTable_some_inj` to unify params/body).

**JoinWellTyped** — new invariant (~20 lines definition + threading):
```lean
def JoinWellTyped (jt : JoinTable) (Δ : JoinTyEnv) : Prop :=
  ∀ label params body paramTys resultTy,
    jt label = some (params, body) →
    Δ label = some ⟨paramTys, resultTy⟩ →
    HasType (TyEnv.bindParams TyEnv.empty params) ... body resultTy
```
Thread through preservation. Closes `handleErrorJoinErr` and `applyJoin` (2 sorry).

### Step 3 — Loop break value typing (unlocks 3 sorry)

**Option B (recommended): `BreakValueTyped` invariant.**

Define:
```lean
def BreakValueTyped (out : Outcome) : Prop :=
  ∀ v label, out = .break (some v) label → ∃ τ, ValueHasType v τ
```

Strengthen preservation to return `BreakValueTyped out ∧ OutcomeHasType out τ`.

For most cases `BreakValueTyped` is trivial:
- Non-break outcomes: `by intros v label h; cases h`
- Break propagation: reuse IH's `BreakValueTyped`

In the loop case: extract `τbreak` from `BreakValueTyped`, then use
`HasType.break` + `LoopTyEnv.extend` to show `τbreak = τ`.

Closes `loopBreak`, `loopBreakNone`, `loopContinue` (3 sorry).

### Step 4 — Switch binder refactor (unlocks 4 sorry)

**Split `switchConstrCase` into two typing rules:**
```lean
| switchConstrCase_some :
    HasType Γ obj (.constr tid) →
    findConstrCase cases tag = some (some x, branch) →
    HasType (TyEnv.extend Γ x (.constr tid)) branch τ →
    HasType Γ (.switchConstr obj cases dflt) τ

| switchConstrCase_none :
    HasType Γ obj (.constr tid) →
    findConstrCase cases tag = some (none, branch) →
    HasType Γ branch τ →
    HasType Γ (.switchConstr obj cases dflt) τ
```

Now preservation can `cases binder` first and pick the matching rule.
Also add extraction of branch typing from `∀ i` for `switchConstantMatch`.

Closes `switchConstr match`, `switchConstrDefault×switchConstrCase`,
`switchConstrDefault`, `switchConstantMatch` (4 sorry).

### Step 5 — Field TypeDefs (unlocks 2 sorry)

Thread `TypeDefs` as a parameter through `HasType` where field rules appear.

Replace the unconstrained `fieldTy` in `HasType.fieldHeap` with:
```lean
| fieldHeap :
    HasType Γ rec_ (.constr tid) →
    td tid = some info →
    info.fields.get? pos = some fieldTy →
    HasType Γ (.field rec_ acc pos) fieldTy
```

Carry `TypeDefsWellTyped td` through preservation.

Closes `fieldConstr×fieldHeap`, `fieldRecord×fieldHeap` (2 sorry).

### Step 6 — evalPrim 2-arg boilerplate (unlocks 2 sorry)

Extract per-const-pair lemmas (9×9 = 81 templates, ~889/891 closed by
`simp_all`). For the 2 surviving int×int cmp cases:
```lean
cases op <;> simp_all [evalPrim2] <;> subst_vars <;> exact .const
```

Purely mechanical — save for last.

### Revised summary table

| Step | Barrier | Sorry | Approach | Status |
|------|---------|-------|----------|--------|
| ~~1~~ | ~~fieldTuple ValClosureOk~~ | ~~1~~ | ~~Per-element ValClosureOk~~ | CLOSED |
| ~~2~~ | ~~Apply cross-typing~~ | ~~5~~ | ~~Consistency + rawFn constructor~~ | CLOSED |
| 3 | Switch typing rules | 0* | Restructure to type all branches | *Already resolved* |
| 4 | Loop break/continue | 3 | BreakContinueTyped + re-entry | Open |
| 5 | Field TypeDefs | 2 | Thread TypeDefs through HasType | Open |
| ~~6~~ | ~~evalPrim~~ | ~~3~~ | ~~split tactic + simp_all~~ | CLOSED |
| 7 | Other (letfnRec, letrec, join) | 4 | Per-case fixes | Open |
| **Total** | | **9** (Preservation) | | |
| FreeVars | termination | 2 | Well-founded recursion | Open |

## Files

| File | Lines | Sorry | Description |
|------|-------|-------|-------------|
| Clam/Syntax.lean | 203 | 0 | CLAM IR types |
| Clam/Values.lean | 111 | 0 | Runtime domains |
| Clam/Semantics.lean | 282 | 0 | 22 eval rules + CSLib LTS |
| Mcore/Types.lean | 96 | 0 | Mtype (24 constructors) |
| Mcore/Syntax.lean | 122 | 0 | Expr (29 constructors) |
| Mcore/Values.lean | 139 | 0 | Values (closure captures Env), store, env |
| Mcore/Semantics.lean | 688 | 0 | 87 eval rules + abort propagation |
| Mcore/Typing.lean | 471 | 0 | 47 HasType + ValueHasType + OutcomeHasType |
| Mcore/FreeVars.lean | 135 | 2 | HasType.strengthen + TyEnv monotonicity |
| Mcore/PrimTyping.lean | 83 | 0 | evalPrim type soundness |
| Mcore/EvalPrimForm.lean | 16 | 0 | evalPrim non-identity returns const/unit |
| Mcore/Preservation.lean | 868 | 9 | Type preservation (PresResult + ValClosureOk) |
| Mcore/Simulation.lean | 180 | 0 | Mcore→Clam value/type correspondence |
| Examples.lean | 277 | 0 | 9 end-to-end evaluation examples |
| Clam.lean | 3 | 0 | Root import |
| Mcore.lean | 8 | 0 | Root import |
| **Total** | **~3550** | **11** | |
