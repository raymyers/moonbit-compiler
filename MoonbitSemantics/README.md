# MoonBit Semantics

Lean 4 formalization of the MoonBit compiler's intermediate representations, with mechanized proofs of type soundness.

## Where Mcore fits in the MoonBit compiler

The MoonBit compiler lowers source programs through several IRs:

```
MoonBit source
    |
    v
  MCore IR   <-- this formalization (typed, monomorphic, closure-converted)
    |
    v
  CLAM IR    <-- also formalized (Closure-Lambda-Apply Machine, GC-aware)
    |
    v
  WASM / JS / native
```

**Mcore** is the compiler's core typed IR (`src/mcore.ml` / `src/mtype.ml` in the compiler). It is monomorphic, has explicit closures, algebraic data types, mutable records, loops with labeled break/continue, error handling, and mutually recursive bindings. The formalization covers all 29 expression forms.

**CLAM** is the lower-level Closure-Lambda-Apply Machine IR used for code generation. A simulation relation between Mcore and CLAM is partially formalized.

## What is proven

### Type Soundness (Mcore)

The main result is **type safety for the Mcore IR**: well-typed programs either produce well-typed results or diverge -- they never get stuck on a type error.

This is established via three theorems:

| Theorem | Statement | File |
|---------|-----------|------|
| **`preservation`** | If `e` is well-typed and evaluates to outcome `o`, then `o` is well-typed | `Preservation.lean` |
| **`evalFuel_sound`** | If the fuel-bounded evaluator returns `.ok`, the big-step `Eval` relation holds | `FuelEvalSoundness.lean` |
| **`coreProgress_eval`** | Well-typed `CoreExpr` programs never get stuck in the fuel-bounded evaluator | `FuelEvalProgress.lean` |

These combine into the capstone:

```lean
theorem type_soundness
    (hft : FnTableWellTyped ft F) (hftc : FnTableComplete ft F) (hhft : HeapFieldTyped F)
    (htype : HasType TyEnv.empty JoinTyEnv.empty LoopTyEnv.empty F none e τ)
    (hcore : CoreExpr e) (n : Nat) :
    (∃ o s' nl',
      evalFuel n ft Env.empty Store.empty JoinTable.empty LoopTable.empty 0 e =
        .ok o s' nl' ∧ OutcomeHasType o τ LoopTyEnv.empty F) ∨
    evalFuel n ft Env.empty Store.empty JoinTable.empty LoopTable.empty 0 e = .outOfFuel
```

For any well-typed stub-free program, fuel-bounded evaluation either succeeds with a well-typed outcome or runs out of fuel (legitimate divergence) -- **never** returns `.stuck` (a type error).

### Axiom usage

All theorems depend only on the three standard Lean axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice)
- `Quot.sound` (quotient soundness)

**Zero sorry. Zero project-specific axioms.** Verified via `#print axioms`.

### What the fuel-bounded evaluator covers

The evaluator `evalFuel` implements all 29 Mcore expression forms:

- **Leaves**: `const`, `unit`, `var`, `function` (closure + raw)
- **Bindings**: `let`, `letfn` (non-recursive, recursive, tail-join, non-tail-join), `letrec` (mutual recursion)
- **Application**: closure, raw function, recursive closure, mutually recursive closure, top-level function, join point
- **Data**: `constr`, `tuple`, `record`, `array`, `field` access, `recordUpdate`, `mutate`
- **Control flow**: `if`/`and`/`or`, `switchConstr`, `switchConstant`, `loop` (with `loopIter` for continue re-entry), `break`, `continue`
- **Error handling**: `handleError` (toResult, joinapply, returnErr), `return` (single, ok, error)
- **Other**: `assign`, `seq`, `object`

Recursive closures use `Value.closureRec` (single recursion) and `Value.closureRecMutual` (mutual recursion via `letrec`), deferring self-reference to apply time.

## File structure

```
MoonbitSemantics/
  Mcore/
    Types.lean            96 lines   Monomorphic type system (24 constructors)
    Syntax.lean          122 lines   Expression IR (29 constructors)
    Values.lean          156 lines   Runtime values, store, environments
    Typing.lean          640 lines   Typing judgments (HasType, ValueHasType, ValClosureOk)
    Semantics.lean       823 lines   Big-step Eval relation (~100 constructors)
    FreeVars.lean        498 lines   Environment strengthening lemmas
    CanonicalForms.lean  465 lines   Canonical forms + evalPrim totality
    PrimTyping.lean       93 lines   Primitive operation typing
    EvalPrimForm.lean     16 lines   evalPrim output form lemma
    Preservation.lean   2208 lines   Type preservation (mutual block + external helpers)
    FuelEval.lean        531 lines   Fuel-bounded evaluator (evalFuel + loopIter)
    FuelEvalSoundness.lean 996 lines Soundness of evalFuel
    FuelEvalProgress.lean 1831 lines Progress theorem + combined coreProgress
    Simulation.lean      180 lines   Mcore → Clam simulation relation
  Clam/
    Syntax.lean                      CLAM IR syntax
    Values.lean                      CLAM runtime values
    Semantics.lean                   CLAM big-step semantics
  Examples.lean                      9 end-to-end evaluation examples
```

Total: ~9500 lines of Lean 4.

## Hypotheses

The formalization uses two explicit hypotheses (parallel to standard PL practice):

- **`HeapFieldTyped F`**: heap-allocated records have type-consistent fields. This is an invariant that would follow from parameterizing `ValueHasType` by a store typing `σ` (~3000-line refactor deferred).

- **`HeapLocPresent s`**: every location with a constructor type has a matching record in the store. The backward direction of heap typing, used by progress for field access.

Both are derivable from a full store-typing refactor and do not represent unsoundness.

## Building

Requires [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) v4.29.0-rc6 and [Lake](https://github.com/leanprover/lake).

```bash
lake build
```

This builds all modules (~840 compilation jobs). First build fetches dependencies (CSLib, Mathlib) and takes several minutes; subsequent builds are incremental.

To verify axiom usage of a specific theorem:

```bash
lake env lean -c - <<'EOF'
import MoonbitSemantics.Mcore.FuelEvalProgress
#print axioms Moonbit.Mcore.type_soundness
EOF
```

## Checked against

This formalization is based on commit [`efb8ab7`](https://github.com/aspect-build/moonbit-compiler/commit/efb8ab742371badc6487cb38f268efb2e10ecddd) of the `main` branch.

## License

See the repository root for license information.
