The was feedback from Perplexity given `plan/MCORE_SOUNDNESS_PROGRESS.md`.

You’re in good shape: what you have is a mostly‑mechanized *design review* of the type system and proof architecture rather than a stuck meta‑theorem. What’s left are localized engineering gaps, so I’d treat this as a refactor/cleanup project with a clear order of attack.

## 1. Overall strategy

I’d recommend:

1. Lock in the invariants that are currently “informal” but used everywhere (ClosureInvariant, fn/Join tables, break values).  
2. Refactor typing rules where Lean is obviously fighting you (switch binder, fieldTypeDefs).  
3. Leave purely mechanical proof search (evalPrim 2‑arg) for last; it’s boring but easy.

That will keep you from baking in brittle shapes that you later regret.

## 2. ClosureInvariant + FreeVars (Barrier 1, + letrec/applyRawFn from Barrier 7)

### Suggested design

- Make `FreeVars` structurally recursive on `Expr` with a minimal spec:  
  - `x ∈ FreeVars e ↔` there is an occurrence of `x` not bound in `e`.  
- Prove two key lemmas upfront and use *only* these in preservation:
  - Monotonicity: if `Γ'` and `Γ` agree on `FreeVars e`, then `HasType Γ e τ → HasType Γ' e τ`.  
  - Restriction: if `EnvWellTyped env Γ` and `fvs ⊇ FreeVars e`, then  
    `EnvWellTyped (Env.ofCapture (Env.capture env fvs)) (Γ.restrict fvs)`.

Then:

- For `let`, `letfn*`, `loop*`, and `applyClosure`:
  - Factor out a *single* lemma:  

    ```lean
    ClosureInvariant env Γ →
    HasType Γ body τ →
    ClosureInvariant (env.extend x v) (Γ.extend x τ)
    ```

    whose proof is: pick `fvs := FreeVars body`, use the restriction lemma, then stitch with `extend_closure` / `extend_non_closure`.

- For `letrec`:
  - Define the recursive environment as a `fixpoint` on bindings.  
  - Prove a “simultaneous closure invariant” lemma: assume each body is well typed in the recursive context ⇒ the env built by the fixpoint satisfies `ClosureInvariant`. This is standard recursive‑functions soundness structure.

- For `applyRawFn body`:
  - Don’t special‑case it in preservation; instead, prove a generic lemma:

    ```lean
    EnvWellTyped Env.empty TyEnv.empty →
    EnvWellTyped (Env.bindParams Env.empty params argVals)
                 (TyEnv.bindParams TyEnv.empty params)
    ```

    and call that from preservation. That’s a small wrapper around `EnvWellTyped.empty` + `bindParams_preserves`.

### Engineering advice

- Keep `FreeVars` and its lemmas *in their own section/file* (e.g. `Mcore/FreeVars.lean`) and import from Typing/Preservation. It decouples syntax work from the rest and avoids recompilation thrash when you tweak the free‑vars shape.
- Encode `HasType.weaken_env` once, then never mention `Γcap` explicitly in proofs: always go via “env restriction + weaken_env” instead of re‑constructing the capture context by hand.

## 3. Apply cross‑typing + tables (Barrier 2, + Join from Barrier 7)

### FnTable coherence

Introduce a single invariant:

```lean
structure FnTableWellTyped (ft : FnTable) (Γ : TyEnv) : Prop :=
(wf :
  ∀ func params body τ,
    ft func = some (params, body) →
    Γ func = some τ →
    HasType (Γ.bindParams params) body τ)
(kind :
  ∀ func params body,
    ft func = some (params, body) →
    ValueHasType (Value.topFn func) (MType.fn params τ) -- or your fn type
)
```

Then:

- In `applyTopFn×applyClosure` and friends, use:
  - `EnvWellTyped.lookup` to show the runtime env entry for `func` must be a particular value form.  
  - `FnTableWellTyped.kind` to show the fn table version has the corresponding type.  
  - A pair of injectivity lemmas (`closure_not_topFn`, `topFn_not_closure` or similar) to eliminate impossible combinations.

For the “same body” issue:

- Add a tiny lemma:

  ```lean
  lemma fnTable_some_inj {ft : FnTable} {f} {p1 p2 b1 b2} :
    ft f = some (p1, b1) → ft f = some (p2, b2) → p1 = p2 ∧ b1 = b2
  ```

  by `cases h₁; cases h₂; simp at *`.

- Use it to rewrite `params✝`, `fnBody✝` to `params`, `body` in `applyTopFn body` preservation.

### JoinWellTyped

Mirror `FnTableWellTyped`:

```lean
structure JoinWellTyped (jt : JoinTable) (Δ : JoinEnv) : Prop :=
(wf :
  ∀ label τ body,
    jt label = some (τ, body) →
    Δ label = some τ ∧ HasType Δ body τ)
```

Thread `JoinWellTyped` through:

- Typing: add it as a parameter to the typing judgment where joins appear.  
- Semantics: ensure evaluation carries the same `jt`.  
- Preservation: in `handleErrorJoinErr` and `applyJoin`, you use `JoinWellTyped.wf` exactly like the fn table case.

## 4. Switch binders (Barrier 3)

Lean’s unification trouble here is a symptom that the typing rule is slightly too implicit.

Two options:

1. **Refactor typing rules**:

   Split the typing rule into two:

   ```lean
   | switchConstr_some :
       HasType Γ scrut (ConstrT tid ...) →
       HasType (Γ.extend x fieldTy) body τ →
       HasType Γ (switchConstr (some x) scrut cases default) τ

   | switchConstr_none :
       HasType Γ scrut (ConstrT tid ...) →
       HasType Γ body τ →
       HasType Γ (switchConstr none scrut cases default) τ
   ```

   Now preservation can `cases binder` first and pick the matching typing rule, with `simp` taking care of the env expression.

2. **Keep rule, use tactic block locally**:

   In the `preservation` case:

   ```lean
   | switchConstr .. :=
     by
       cases binder <;> simp [Eval.switchConstr, HasType.switchConstrCase] at *
       -- now both sides use the same binder constructor
   ```

   You can hide this in a small helper lemma if you dislike inline tactics in the main theorem.

In a mechanized semantics like this, I’d seriously prefer the explicit two‑rule version: it also makes human reading of the typing rules clearer.

## 5. Loop break values (Barrier 4)

Your diagnosis is exactly right: the invariant you *actually* need is weaker than a typed break outcome, and trying to push typing through `OutcomeHasType.break` makes `weaken` too rigid.

I’d go with your **Option B**, but keep it minimal:

- Define

  ```lean
  def BreakValueTyped (out : Outcome) : Prop :=
    ∀ v label, out = .break (some v) label → ∃ τ, ValueHasType v τ
  ```

- Strengthen the preservation statement to:

  ```lean
  theorem preservation :
    Eval env e out →
    HasType Γ e τ →
    ClosureInvariant env Γ →
    BreakValueTyped out ∧ OutcomeHasType out τ
  ```

- For almost all cases, `BreakValueTyped` is trivial:
  - Non‑break outcomes: `by intros v label h; cases h`.  
  - Cases that propagate breaks: reuse the IH’s `BreakValueTyped`.

- In the loop case:
  - Use `BreakValueTyped` on the body’s result to obtain `τbreak`.  
  - Use the typing rule for `break` in the loop body plus `OutcomeHasType`/env invariants to show `τbreak = τ`, and then you can finish the loop rule.

This keeps `OutcomeHasType` simple (no existentials) and pushes the existential quantification into a separate invariant that is easy to propagate.

If you really want Option C (direct induction on eval), I’d still define the above `BreakValueTyped` because it will naturally fall out of that proof anyway and can be reused.

## 6. Field TypeDefs (Barrier 5)

You’ve already identified the correct abstraction: make `TypeDefs` a first‑class parameter of typing.

Concrete steps:

1. Thread `TypeDefs` through `HasType`, `ValueHasType`, and any `field*` rules that touch user types.  
2. Define a record:

   ```lean
   structure TypeDefsWellTyped (td : TypeDefs) : Prop :=
   (constr :
     ∀ tid fields, td tid = some (ConstructorInfo fields) →
       -- whatever global well-formedness you need)
   )
   ```

3. In `HasType.fieldHeap`, replace the unconstrained `fieldTy` with:

   ```lean
   td tid = some info →
   info.fields.get? pos = some fieldTy →
   HasType Γ (field expr pos) fieldTy
   ```

4. In preservation, carry a `TypeDefsWellTyped td` parameter and use it where needed.

This is one of those “do it once, everywhere gets cleaner” refactors; doing it now is better than layering ad‑hoc constraints in proof scripts.

## 7. evalPrim 2‑arg (Barrier 6)

You’re right that the space is 9×9×11, and 2 cases survive `simp_all`. My advice:

- Abstract *per const‑pair* as you propose, but generate the lemmas via Lean metaprogramming or a small macro if you can; otherwise:

  ```lean
  lemma ep2_int_int :
    PrimTyping2 op (.const (.int i1)) (.const (.int i2)) v τ :=
  by
    cases op <;> simp_all [evalPrim2] <;> subst_vars <;> exact .const
  ```

- Once you have a template lemma for one pair, cloning it to the other 8 pairs is purely mechanical; don’t over‑engineer.

Given how localized this is and how little it affects the rest of the meta‑theory, I’d genuinely save it for the very end.

## 8. Practical order of work

Given your estimates and dependencies, I’d do:

1. **FreeVars + env restriction + ClosureInvariant maintenance**  
2. **FnTableWellTyped + JoinWellTyped + apply cross‑typing**  
3. **Loop break invariant**  
4. **Switch binder refactor**  
5. **Field TypeDefs threading**  
6. **letrec + applyRawFn body (after ClosureInvariant tools exist)**  
7. **evalPrim 2‑arg boilerplate**

That gives you a monotonic path where each step unlocks several sorrys without forcing you to re‑shape earlier proofs.
