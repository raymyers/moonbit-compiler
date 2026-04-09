/-
  MoonBit Compiler — Mcore Canonical Forms Lemmas

  Inversion lemmas establishing the shape of well-typed values.
  These are foundational for progress proofs and, together with
  `HeapAvail`, let us case-analyse the shape of a value given its
  `ValueHasType` evidence.
-/
import MoonbitSemantics.Mcore.Typing

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp)

/-! ## Internal: cases of `ValueHasType` by value shape

The helper `cases h` on `ValueHasType v τ` struggles with the
`const` constructor because its type index is `typeOfConst c`, which
Lean can't unify with concrete `τ` via dependent elimination. Instead
we case-split on `v` first, which lets Lean discharge impossible cases
automatically. -/

/-! ## Canonical forms for scalar types -/

theorem canonical_bool {v : Value} (h : ValueHasType v .bool) :
    ∃ b, v = .const (.bool b) := by
  cases v with
  | const c => cases c <;> first | exact ⟨_, rfl⟩ | cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_int {v : Value} (h : ValueHasType v .int) :
    ∃ n, v = .const (.int n) := by
  cases v with
  | const c => cases c <;> first | exact ⟨_, rfl⟩ | cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_int64 {v : Value} (h : ValueHasType v .int64) :
    ∃ n, v = .const (.int64 n) := by
  cases v with
  | const c => cases c <;> first | exact ⟨_, rfl⟩ | cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_float {v : Value} (h : ValueHasType v .float) :
    ∃ n, v = .const (.float n) := by
  cases v with
  | const c => cases c <;> first | exact ⟨_, rfl⟩ | cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_double {v : Value} (h : ValueHasType v .double) :
    ∃ n, v = .const (.double n) := by
  cases v with
  | const c => cases c <;> first | exact ⟨_, rfl⟩ | cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_string {v : Value} (h : ValueHasType v .string) :
    ∃ s, v = .const (.string s) := by
  cases v with
  | const c => cases c <;> first | exact ⟨_, rfl⟩ | cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_char {v : Value} (h : ValueHasType v .char) :
    ∃ c', v = .const (.char c') := by
  cases v with
  | const c => cases c <;> first | exact ⟨_, rfl⟩ | cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_byte {v : Value} (h : ValueHasType v .byte) :
    ∃ b, v = .const (.byte b) := by
  cases v with
  | const c => cases c <;> first | exact ⟨_, rfl⟩ | cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_unit {v : Value} (h : ValueHasType v .unit) :
    v = .unit ∨ v = .const .unit := by
  cases v with
  | const c =>
    cases c <;> first | (right; rfl) | cases h
  | unit => left; rfl
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

/-! ## Canonical forms for function types -/

theorem canonical_func {v : Value} {paramTys retTy}
    (h : ValueHasType v (.func paramTys retTy)) :
    ∃ captured params body,
      v = .closure captured params body ∧ paramTys = params.map (·.ty) := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ =>
    cases h with
    | closure => exact ⟨_, _, _, rfl, rfl⟩
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_rawFunc {v : Value} {paramTys retTy}
    (h : ValueHasType v (.rawFunc paramTys retTy)) :
    ∃ params body, v = .rawFn params body ∧ paramTys = params.map (·.ty) := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ =>
    cases h with
    | rawFn => exact ⟨_, _, rfl, rfl⟩
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

/-! ## Canonical forms for compound types -/

theorem canonical_tuple {v : Value} {τs}
    (h : ValueHasType v (.tuple τs)) :
    ∃ vals, v = .tuple vals ∧ ValueListHasType vals τs := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple vals =>
    cases h with
    | tuple hvls => exact ⟨vals, rfl, hvls⟩
  | loc _ => cases h

/-- A value of `.constr tid ats` type is either a `.constr` value (with typed
    args) or a `.loc` pointing to a heap-allocated record. -/
theorem canonical_constr {v : Value} {tid ats}
    (h : ValueHasType v (.constr tid ats)) :
    (∃ tag args, v = .constr tag args ∧ ValueListHasType args ats) ∨
    (∃ l, v = .loc l) := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr tag args =>
    cases h with
    | constr hvls => left; exact ⟨tag, args, rfl, hvls⟩
  | tuple _ => cases h
  | loc l => right; exact ⟨l, rfl⟩

theorem canonical_fixedarray {v : Value} {elemTy}
    (h : ValueHasType v (.fixedarray elemTy)) :
    ∃ l, v = .loc l := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc l => exact ⟨l, rfl⟩

/-- A value of `.errorValueResult okTy errTy tid` type is either an Ok wrapper
    `.constr 0 [v]` with `v` having type `okTy`, or an Err wrapper
    `.constr 1 [v]` with `v` having type `errTy`. -/
theorem canonical_errorValueResult {v : Value} {okTy errTy tid}
    (h : ValueHasType v (.errorValueResult okTy errTy tid)) :
    (∃ w, v = .constr 0 [w] ∧ ValueHasType w okTy) ∨
    (∃ w, v = .constr 1 [w] ∧ ValueHasType w errTy) := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr tag args =>
    cases h with
    | errorValueResultOk hv => left; exact ⟨_, rfl, hv⟩
    | errorValueResultErr hv => right; exact ⟨_, rfl, hv⟩
  | tuple _ => cases h
  | loc _ => cases h

/-! ## Negative canonical forms: types with no inhabitants

Several `Mtype` constructors (`.int16`, `.uint16`, `.uint`, `.uint64`,
`.bytes`, `.optimizedOption`, `.trait`, `.any`, `.maybeUninit`) have no
`ValueHasType` introduction rules in the current type system. A
`ValueHasType v τ` for such a `τ` is vacuously absurd. These lemmas give
`False` directly, which is useful in progress when ruling out impossible
cases (e.g., a `HasType` derivation can't reach them, so by inversion any
well-typed value at such a type leads to contradiction). -/

theorem canonical_int16_absurd {v : Value} (h : ValueHasType v .int16) : False := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_uint16_absurd {v : Value} (h : ValueHasType v .uint16) : False := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_uint_absurd {v : Value} (h : ValueHasType v .uint) : False := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_uint64_absurd {v : Value} (h : ValueHasType v .uint64) : False := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_bytes_absurd {v : Value} (h : ValueHasType v .bytes) : False := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_optimizedOption_absurd {v : Value} {t}
    (h : ValueHasType v (.optimizedOption t)) : False := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_trait_absurd {v : Value} {id}
    (h : ValueHasType v (.trait id)) : False := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_any_absurd {v : Value} {id}
    (h : ValueHasType v (.any id)) : False := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

theorem canonical_maybeUninit_absurd {v : Value} {t}
    (h : ValueHasType v (.maybeUninit t)) : False := by
  cases v with
  | const c => cases c <;> cases h
  | unit => cases h
  | closure _ _ _ => cases h
  | rawFn _ _ => cases h
  | constr _ _ => cases h
  | tuple _ => cases h
  | loc _ => cases h

/-! ## evalPrim totality for supported operations

`evalPrim` is a partial function: `typeOfPrim` accepts broader types (e.g.,
`.arith` on `.int64`, `.float`, `.double`) than `evalPrim` actually implements
(only `.int` is wired up for arithmetic; similar for `.cmp` and `.neg`).

These lemmas prove totality of `evalPrim` for the *supported* cases — i.e.,
exactly those `(op, argTys)` pairs that `evalPrim` handles. Progress will
compose them, and types not in the supported set will appear as a gap
(the primitive-implementation gap of `evalPrim`, not a soundness issue). -/

theorem evalPrim_arith_int_total {op} {v1 v2 : Value}
    (h1 : ValueHasType v1 .int) (h2 : ValueHasType v2 .int) :
    ∃ v, evalPrim (.arith op) [v1, v2] = some v := by
  obtain ⟨a, rfl⟩ := canonical_int h1
  obtain ⟨b, rfl⟩ := canonical_int h2
  cases op <;> exact ⟨_, rfl⟩

theorem evalPrim_cmp_int_total {op} {v1 v2 : Value}
    (h1 : ValueHasType v1 .int) (h2 : ValueHasType v2 .int) :
    ∃ v, evalPrim (.cmp op) [v1, v2] = some v := by
  obtain ⟨a, rfl⟩ := canonical_int h1
  obtain ⟨b, rfl⟩ := canonical_int h2
  cases op <;> exact ⟨_, rfl⟩

theorem evalPrim_not_total {v : Value} (h : ValueHasType v .bool) :
    ∃ v', evalPrim .not [v] = some v' := by
  obtain ⟨b, rfl⟩ := canonical_bool h
  exact ⟨_, rfl⟩

theorem evalPrim_neg_int_total {v : Value} (h : ValueHasType v .int) :
    ∃ v', evalPrim .neg [v] = some v' := by
  obtain ⟨n, rfl⟩ := canonical_int h
  exact ⟨_, rfl⟩

theorem evalPrim_ignore_total {v : Value} :
    ∃ v', evalPrim .ignore [v] = some v' :=
  ⟨.unit, rfl⟩

theorem evalPrim_identity_total {v : Value} :
    ∃ v', evalPrim .identity [v] = some v' :=
  ⟨v, rfl⟩

/-- Predicate marking which `(op, argTys)` pairs are fully supported by
    `evalPrim` (i.e., where totality holds). This is a subset of the pairs
    accepted by `typeOfPrim`. -/
def PrimSupported : Prim → List Mtype → Prop
  | .arith _, [.int, .int] => True
  | .cmp _, [.int, .int] => True
  | .not, [.bool] => True
  | .neg, [.int] => True
  | .ignore, [_] => True
  | .identity, [_] => True
  | _, _ => False

/-- Main evalPrim totality: for well-typed args of a supported prim, `evalPrim`
    returns a defined value. Progress will discharge `PrimSupported` by case
    analysis on the prim; cases where it fails reflect the primitive-
    implementation gap in `evalPrim`. -/
theorem evalPrim_total {op : Prim} {argTys : List Mtype} {argVals : List Value}
    (hsupport : PrimSupported op argTys)
    (hargs : ValueListHasType argVals argTys) :
    ∃ v, evalPrim op argVals = some v := by
  match op, argTys, hsupport with
  | .arith aop, [.int, .int], _ =>
    match argVals, hargs with
    | [v1, v2], .cons h1 (.cons h2 .nil) =>
      exact evalPrim_arith_int_total (op := aop) h1 h2
  | .cmp cop, [.int, .int], _ =>
    match argVals, hargs with
    | [v1, v2], .cons h1 (.cons h2 .nil) =>
      exact evalPrim_cmp_int_total (op := cop) h1 h2
  | .not, [.bool], _ =>
    match argVals, hargs with
    | [v], .cons h .nil => exact evalPrim_not_total h
  | .neg, [.int], _ =>
    match argVals, hargs with
    | [v], .cons h .nil => exact evalPrim_neg_int_total h
  | .ignore, [_], _ =>
    match argVals, hargs with
    | [v], .cons _ .nil => exact evalPrim_ignore_total
  | .identity, [_], _ =>
    match argVals, hargs with
    | [v], .cons _ .nil => exact evalPrim_identity_total

end Moonbit.Mcore
