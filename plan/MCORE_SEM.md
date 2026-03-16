# MCore Operational Semantics — Formalization Plan

Goal: define a big-step (and eventually small-step) operational semantics for
the MoonBit compiler's **Mcore** IR in Lean 4, using CSLib, and prove a
simulation relation with the existing Clam semantics.

## 1. Mtype — Monomorphic Type System

- [ ] Define `Mtype` inductive with all 24 constructors:
      `T_int`, `T_char`, `T_bool`, `T_unit`, `T_byte`, `T_int16`, `T_uint16`,
      `T_int64`, `T_uint`, `T_uint64`, `T_float`, `T_double`, `T_string`,
      `T_bytes`, `T_optimized_option`, `T_func`, `T_raw_func`, `T_tuple`,
      `T_fixedarray`, `T_constr`, `T_trait`, `T_any`, `T_maybe_uninit`,
      `T_error_value_result`
- [ ] Define type metadata: `TypeInfo` (Variant, Record, Trait, Externref, etc.)
- [ ] Define `TypeDefs` as a map from type IDs to `TypeInfo`
- [ ] Define `ConstrInfo` (constructor metadata: tag, arity, field types)
- [ ] Define `FieldInfo` (record field metadata: name, type, mutability, position)

## 2. Mcore Syntax — Expression IR

### 2a. Auxiliary types

- [ ] `Const` — reuse from Clam (already defined)
- [ ] `Prim` — reuse from Clam (already defined)
- [ ] `Var`, `Binder` — core identifiers
- [ ] `ConstrTag` — constructor tags
- [ ] `LoopLabel` — loop labels for break/continue
- [ ] `Accessor` — field accessor (by name or position)
- [ ] `Label` — field label for records

### 2b. Control flow / application kinds

- [ ] `LetfnKind`: `Nonrec | Rec | Tail_join | Nontail_join`
- [ ] `ApplyKind`: `Normal (func_ty : Mtype) | Join`
- [ ] `ReturnKind`: `Error_result (is_error : Bool) (return_ty : Mtype) | Single_value`
- [ ] `HandleKind`: `To_result | Joinapply (target : Var) | Return_err (ok_ty : Mtype)`

### 2c. Expression type (29 constructors)

- [ ] `Cexpr_const` — constant literal
- [ ] `Cexpr_unit` — unit value
- [ ] `Cexpr_var` — variable reference (with optional `Prim` specialization)
- [ ] `Cexpr_prim` — primitive operation application
- [ ] `Cexpr_let` — let binding
- [ ] `Cexpr_letfn` — local function binding (with `LetfnKind`)
- [ ] `Cexpr_function` — function/closure value (with `is_raw` flag)
- [ ] `Cexpr_apply` — function application (with `ApplyKind`)
- [ ] `Cexpr_object` — object/trait instantiation
- [ ] `Cexpr_letrec` — mutually recursive function bindings
- [ ] `Cexpr_constr` — variant constructor application
- [ ] `Cexpr_tuple` — tuple construction
- [ ] `Cexpr_record` — record construction (with `FieldDef` list)
- [ ] `Cexpr_record_update` — functional record update
- [ ] `Cexpr_field` — field access (record/tuple)
- [ ] `Cexpr_mutate` — mutable field write
- [ ] `Cexpr_array` — fixed array construction
- [ ] `Cexpr_assign` — variable assignment
- [ ] `Cexpr_sequence` — expression sequencing
- [ ] `Cexpr_if` — conditional (with optional else)
- [ ] `Cexpr_switch_constr` — constructor pattern match (with optional binder + default)
- [ ] `Cexpr_switch_constant` — constant pattern match (required default)
- [ ] `Cexpr_loop` — loop with parameters and label
- [ ] `Cexpr_break` — break from labeled loop (optional arg)
- [ ] `Cexpr_continue` — continue labeled loop (with args)
- [ ] `Cexpr_handle_error` — error handling (with `HandleKind`)
- [ ] `Cexpr_return` — return (with `ReturnKind`)
- [ ] `Cexpr_and` — short-circuit logical AND
- [ ] `Cexpr_or` — short-circuit logical OR

### 2d. Supporting definitions

- [ ] `Fn` structure: `params : List Param`, `body : Expr`
- [ ] `Param` structure: `binder : Var`, `ty : Mtype`
- [ ] `FieldDef` structure: `label`, `pos`, `is_mut`, `expr`
- [ ] `TopItem`: `Ctop_expr | Ctop_let | Ctop_fn | Ctop_stub`
- [ ] `Program` structure: `top_items : List TopItem`

## 3. Mcore Values and Runtime State

- [ ] `Value`: constants, closures `(env × params × body)`, constructors
      `(tag × List Value)`, tuples `(List Value)`, records `(fields)`,
      locations (for mutable state), unit, raw function pointers
- [ ] `Store`: heap mapping `Loc → HeapObj`
- [ ] `HeapObj`: record objects, array objects (mutable fields)
- [ ] `Env`: `Var → Option Value` (variable environment)
- [ ] `FnTable`: top-level function lookup
- [ ] `JoinTable`: active join point bindings
- [ ] `LoopCtx`: loop label → (params, body, env) for break/continue
- [ ] `Config`: `(expr, env, store, joins, loops, fnTable, nextLoc)`

## 4. Big-Step Evaluation Rules

### 4a. Core expression rules

- [ ] `const` — constant evaluates to itself
- [ ] `unit` — evaluates to unit value
- [ ] `var` — environment lookup
- [ ] `let` — evaluate RHS, extend env, evaluate body
- [ ] `sequence` — evaluate all, return last
- [ ] `and` / `or` — short-circuit evaluation

### 4b. Functions and application

- [ ] `function` — create closure value (capture env)
- [ ] `letfn` (Nonrec) — bind function in env, evaluate body
- [ ] `letfn` (Rec) — bind recursive function (self-reference), evaluate body
- [ ] `letrec` — mutual recursion: bind all functions with back-pointers
- [ ] `apply` (Normal) — evaluate function + args, call
- [ ] `apply` (Join) — jump to join point (tail call to continuation)

### 4c. Data construction and access

- [ ] `constr` — evaluate args, create tagged value
- [ ] `tuple` — evaluate elements, create tuple value
- [ ] `record` — evaluate fields, create record value
- [ ] `record_update` — copy record, overwrite specified fields
- [ ] `array` — evaluate elements, create array
- [ ] `field` — access field by position from record/tuple
- [ ] `mutate` — write to mutable field in store
- [ ] `assign` — update mutable variable binding

### 4d. Pattern matching

- [ ] `switch_constr` — match on constructor tag, bind payload, evaluate branch
- [ ] `switch_constr` (default) — fallback when no tag matches
- [ ] `switch_constant` — match on constant value
- [ ] `switch_constant` (default) — fallback

### 4e. Control flow

- [ ] `if` (true branch) — evaluate condition, take ifso
- [ ] `if` (false branch) — evaluate condition, take ifnot
- [ ] `if` (no else, true) — evaluate condition, take ifso, return unit if false
- [ ] `loop` — initialize loop params, evaluate body (may break/continue)
- [ ] `break` — exit loop with optional value
- [ ] `continue` — restart loop body with new args

### 4f. Error handling

- [ ] `handle_error` (To_result) — wrap expression result as Ok/Err
- [ ] `handle_error` (Joinapply) — on error, jump to join point
- [ ] `handle_error` (Return_err) — propagate error up
- [ ] `return` (Single_value) — return from function
- [ ] `return` (Error_result) — return ok or error value

### 4g. Objects

- [ ] `object` — create trait object with method table and self value

### 4h. Argument list evaluation

- [ ] `EvalArgs` (nil / cons) — left-to-right list evaluation threading state

## 5. CSLib Integration

- [ ] Define `McoreTr : Config → Unit → Config → Prop` (LTS transition)
- [ ] Instantiate `mcoreLTS : LTS Config Unit`
- [ ] Define `McoreStep` with `@[reduction_sys "mcore "]`
- [ ] Prove `const_normal` — constants are normal forms
- [ ] Prove `var_deterministic` — variable lookup is deterministic
- [ ] Prove `Eval` is deterministic (given deterministic `evalPrim`)

## 6. Simulation: Mcore → Clam

This connects the two IRs, corresponding to `clam_of_core.ml` in the compiler.

### 6a. Value correspondence

- [ ] Define `ValueSim : Mcore.Value → Clam.Value → Prop`
      (e.g., Mcore closure ↔ Clam closureVal, Mcore constr ↔ Clam aggregate)
- [ ] Define `StoreSim : Mcore.Store → Clam.Store → Prop`
- [ ] Define `EnvSim : Mcore.Env → Clam.Env → Prop`

### 6b. Expression translation

- [ ] Define `translate : Mcore.Expr → Clam.Lambda` (or relate as a Prop)
- [ ] Type lowering: `lowerType : Mtype → Ltype`

### 6c. Simulation theorem

- [ ] **Forward simulation**: if `Mcore.Eval e v` and `translate e = e'`,
      then `Clam.Eval e' v'` and `ValueSim v v'`
- [ ] Prove per-constructor: one lemma per expression form
- [ ] Compose into the main simulation theorem

### 6d. Key translation correspondences to verify

- [ ] `Cexpr_function` → `Lclosure` (closure conversion)
- [ ] `Cexpr_constr` → `Lallocate (.enum tag)` (constructor → heap alloc)
- [ ] `Cexpr_record` → `Lallocate (.struct)` (record → struct alloc)
- [ ] `Cexpr_tuple` → `Lallocate (.tuple)` (tuple → tuple alloc)
- [ ] `Cexpr_field` → `Lget_field` (field access)
- [ ] `Cexpr_mutate` → `Lset_field` (field mutation)
- [ ] `Cexpr_switch_constr` → `Lswitch` (pattern match)
- [ ] `Cexpr_apply (Normal)` → `Lapply` (function call)
- [ ] `Cexpr_apply (Join)` → `Ljoinapply` (join point jump)
- [ ] `Cexpr_handle_error` → `Lcatch` or join-based lowering
- [ ] `Cexpr_object` → `Lallocate (.object)` (trait object)

## 7. Properties to Prove

- [ ] **Determinism**: `Eval` is a partial function (at most one result)
- [ ] **Type preservation**: if `e : τ` and `Eval e v`, then `v : τ`
- [ ] **Progress**: well-typed closed expressions either are values or can step
- [ ] **Simulation correctness**: Mcore evaluation simulated by Clam evaluation
- [ ] **Monotone store**: evaluation only extends the store (no deallocation)
- [ ] **Fresh locations**: allocated locations are always fresh
