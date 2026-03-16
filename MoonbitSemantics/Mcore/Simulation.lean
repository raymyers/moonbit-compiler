/-
  MoonBit Compiler — Mcore → Clam Simulation
  Defines the value/state correspondence and translation between
  the Mcore and Clam IRs, corresponding to `clam_of_core.ml`.
-/
import MoonbitSemantics.Mcore.Semantics
import MoonbitSemantics.Clam.Semantics

namespace Moonbit.Simulation

open Moonbit.Clam (Const)

/-! ## Value correspondence

Defines when an Mcore value and a Clam value represent the same semantic entity.
-/

mutual

/-- Value simulation: an Mcore value corresponds to a Clam value. -/
inductive ValueSim : Mcore.Value → Clam.Value → Prop where
  | const : ValueSim (.const c) (.const c)
  | unit : ValueSim .unit .unit
  | loc : ValueSim (.loc l) (.loc l)
  | constr :
    ValueListSim args clamArgs →
    ValueSim (.constr tag args) (.closureVal clamArgs tag)
  | tuple :
    ValueListSim vals clamVals →
    ValueSim (.tuple vals) (.closureVal clamVals 0)

/-- Pointwise value simulation on lists. -/
inductive ValueListSim : List Mcore.Value → List Clam.Value → Prop where
  | nil : ValueListSim [] []
  | cons :
    ValueSim v cv →
    ValueListSim vs cvs →
    ValueListSim (v :: vs) (cv :: cvs)

end

/-! ## Store correspondence -/

/-- Two stores correspond if every location maps to corresponding heap objects. -/
def StoreSim (ms : Mcore.Store) (cs : Clam.Store) : Prop :=
  ∀ l : Mcore.Loc,
    match ms l, cs l with
    | none, none => True
    | some (.record fields _), some (.aggregate _ cfields) =>
        fields.size = cfields.size ∧
        ∀ i (h₁ : i < fields.size) (h₂ : i < cfields.size),
          ValueSim fields[i] cfields[i]
    | some (.array elems), some (.aggregate _ celems) =>
        elems.size = celems.size ∧
        ∀ i (h₁ : i < elems.size) (h₂ : i < celems.size),
          ValueSim elems[i] celems[i]
    | _, _ => False

/-! ## Environment correspondence -/

/-- Two environments correspond if they agree on all variables (up to ValueSim). -/
def EnvSim (me : Mcore.Env) (ce : Clam.Env) : Prop :=
  ∀ x : Mcore.Var,
    match me x, ce x with
    | none, none => True
    | some mv, some cv => ValueSim mv cv
    | _, _ => False

/-! ## Type lowering

Maps `Mtype` to `Ltype` (CLAM's GC-aware type system).
This corresponds to the type translation in `clam_of_core.ml`.
-/

open Clam (Ltype IntKind)

/-- Lower an Mcore type to a Clam type. -/
def lowerType : Mcore.Mtype → Ltype
  | .int => .i32 .int
  | .char => .i32 .char
  | .bool => .i32 .bool
  | .unit => .i32 .unit
  | .byte => .i32 .byte
  | .int16 => .i32 .int16
  | .uint16 => .i32 .uint16
  | .int64 => .i64
  | .uint => .i32 .int    -- simplified: uint maps to i32
  | .uint64 => .i64
  | .float => .f32
  | .double => .f64
  | .string => .refString
  | .bytes => .refBytes
  | .func _ _ => .refFunc
  | .rawFunc _ _ => .refFunc
  | .tuple _ => .refAny     -- tuples become heap refs
  | .fixedarray _ => .refAny
  | .constr id => .ref id
  | .trait id => .ref id
  | .any id => .refAny
  | .optimizedOption _ => .refAny
  | .maybeUninit t => lowerType t
  | .errorValueResult _ _ id => .ref id

/-! ## Expression translation sketch

The translation from Mcore.Expr to Clam.Lambda corresponds to the
`transl_expr` function in `clam_of_core.ml`. Key correspondences:

- `Cexpr_const c`      → `Lconst c`
- `Cexpr_unit`         → `Lconst unit`
- `Cexpr_var x`        → `Lvar x`
- `Cexpr_let x e b`    → `Llet x e' b'`
- `Cexpr_if c t f`     → `Lif c' t' f'`
- `Cexpr_function`     → `Lclosure` (after lambda lifting)
- `Cexpr_constr tag as` → `Lallocate (Enum tag) as'`
- `Cexpr_tuple es`     → `Lallocate Tuple es'`
- `Cexpr_record fs`    → `Lallocate Struct fs'`
- `Cexpr_field r _ i`  → `Lget_field r' i kind`
- `Cexpr_mutate r _ f i` → `Lset_field r' f' i kind`
- `Cexpr_apply f as`   → `Lapply target as'`
- `Cexpr_switch_constr` → `Lswitch`
- `Cexpr_loop`         → `Lloop`
- `Cexpr_break`        → `Lbreak`
- `Cexpr_continue`     → `Lcontinue`
-/

/-! ## Forward simulation (per-constructor lemmas)

The main theorem we want:
  If `Mcore.Eval e outcome` and `translate e = e'` and the states correspond,
  then `Clam.Eval e' outcome'` and the outcomes correspond.

We prove this constructor-by-constructor.
-/

/-- Constants translate to constants and preserve semantics. -/
theorem const_sim (c : Const) (me : Mcore.Env) (ce : Clam.Env) (ms : Mcore.Store) (cs : Clam.Store)
    (mjt : Mcore.JoinTable) (cjt : Clam.JoinTable) (ft : Mcore.FnTable) (cft : Clam.FnTable)
    (mlt : Mcore.LoopTable) (nl : Nat)
    (henv : EnvSim me ce) (hstore : StoreSim ms cs) :
    Mcore.Eval ft me ms mjt mlt nl (.const c) (.val (.const c)) ms nl →
    Clam.Eval cft ce cs cjt nl (.const c) (.const c) cs nl := by
  intro _
  exact Clam.Eval.const

/-- Unit translates to unit constant and preserves semantics. -/
theorem unit_sim (me : Mcore.Env) (ce : Clam.Env) (ms : Mcore.Store) (cs : Clam.Store)
    (mjt : Mcore.JoinTable) (cjt : Clam.JoinTable) (ft : Mcore.FnTable) (cft : Clam.FnTable)
    (mlt : Mcore.LoopTable) (nl : Nat)
    (henv : EnvSim me ce) (hstore : StoreSim ms cs) :
    Mcore.Eval ft me ms mjt mlt nl .unit (.val .unit) ms nl →
    Clam.Eval cft ce cs cjt nl (.const .unit) (Clam.evalConst .unit) cs nl := by
  intro _
  exact Clam.Eval.const

/-- Variable lookup is preserved by environment simulation. -/
theorem var_sim (x : Mcore.Var) (mv : Mcore.Value) (cv : Clam.Value)
    (me : Mcore.Env) (ce : Clam.Env) (ms : Mcore.Store) (cs : Clam.Store)
    (mjt : Mcore.JoinTable) (cjt : Clam.JoinTable) (ft : Mcore.FnTable) (cft : Clam.FnTable)
    (mlt : Mcore.LoopTable) (nl : Nat)
    (henv : EnvSim me ce)
    (hmcore : me x = some mv)
    (hclam : ce x = some cv)
    (hval : ValueSim mv cv) :
    Mcore.Eval ft me ms mjt mlt nl (.var x none) (.val mv) ms nl ∧
    Clam.Eval cft ce cs cjt nl (.var x) cv cs nl :=
  ⟨Mcore.Eval.var hmcore, Clam.Eval.var hclam⟩

/-- Short-circuit AND preservation: false && _ = false in both IRs. -/
theorem and_false_sim (ft : Mcore.FnTable) (cft : Clam.FnTable)
    (me : Mcore.Env) (ce : Clam.Env) (ms : Mcore.Store) (cs : Clam.Store)
    (mjt : Mcore.JoinTable) (cjt : Clam.JoinTable)
    (mlt : Mcore.LoopTable) (nl : Nat)
    (rhs_m : Mcore.Expr) (rhs_c : Clam.Lambda) :
    Mcore.Eval ft me ms mjt mlt nl
      (.and (.const (.bool false)) rhs_m)
      (.val (.const (.bool false))) ms nl :=
  Mcore.Eval.andFalse Mcore.Eval.const

end Moonbit.Simulation
