/-
  MoonBit Compiler — Mcore Type Preservation
  Proves that well-typed expressions evaluate to well-typed outcomes
  via mutual structural recursion on the evaluation derivation.
-/
import MoonbitSemantics.Mcore.Typing
import MoonbitSemantics.Mcore.PrimTyping

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp)

/-! ## Helpers -/

@[simp] theorem Outcome.val_not_abort (v : Value) : ¬ (Outcome.val v).isAbort := by
  simp [Outcome.isAbort]

/-- Lift OutcomeHasType to a different expected type (abort outcomes are polymorphic). -/
def OutcomeHasType.weaken : OutcomeHasType o τ₁ → o.isAbort → OutcomeHasType o τ₂
  | .break, _ => .break
  | .continue, _ => .continue
  | .return, _ => .return
  | .error, _ => .error

def OutcomeHasType.ofAbort : (o : Outcome) → o.isAbort → OutcomeHasType o τ
  | .break _ _, _ => .break
  | .continue _ _, _ => .continue
  | .return _, _ => .return
  | .error _, _ => .error

def EvalArgsAbort.outcome_isAbort :
    EvalArgsAbort ft env s jt lt nl es outcome s' nl' → outcome.isAbort
  | .here _ hab => hab
  | .later _ htail => htail.outcome_isAbort

theorem EnvWellTyped.extend_preserves
    (hwt : EnvWellTyped env Γ) (hv : ValueHasType v τ) :
    EnvWellTyped (Env.extend env x v) (TyEnv.extend Γ x τ) := by
  intro y σ hy
  by_cases h : y = x
  · subst h; simp only [TyEnv.extend, ite_true] at hy
    simp only [Env.extend, ite_true]; cases hy; exact ⟨v, rfl, hv⟩
  · simp only [TyEnv.extend, h, ite_false] at hy
    simp only [Env.extend, h, ite_false]; exact hwt y σ hy

theorem EnvWellTyped.lookup
    (hwt : EnvWellTyped env Γ) (hΓ : Γ x = some τ) (henv : env x = some v) :
    ValueHasType v τ := by
  obtain ⟨v', hv', hvt⟩ := hwt x τ hΓ; rw [henv] at hv'; cases hv'; exact hvt

def FnTableWellTyped (ft : FnTable) (F : FnTyTable) : Prop :=
  ∀ f paramTys retTy,
    F f = some (paramTys, retTy) →
    ∃ params body,
      ft f = some (params, body) ∧
      params.map (·.ty) = paramTys ∧
      (∀ p, p ∈ params → F p.binder = none) ∧
      HasType (TyEnv.bindParams TyEnv.empty params)
        JoinTyEnv.empty LoopTyEnv.empty F body retTy

/-- Top-level functions and env closures don't overlap for the same variable. -/
def FnEnvDisjoint (env : Env) (F : FnTyTable) : Prop :=
  (∀ func cap ps bd, env func = some (.closure cap ps bd) → F func = none) ∧
  (∀ func ps bd, env func = some (.rawFn ps bd) → F func = none)

/-- FnEnvDisjoint is preserved when extending env, if F doesn't contain the key. -/
theorem FnEnvDisjoint.extend
    (hdisj : FnEnvDisjoint env F) (hF : F x = none) :
    FnEnvDisjoint (Env.extend env x v) F := by
  constructor
  · intro func cap ps bd henv
    by_cases h : func = x
    · subst h; exact hF
    · simp [Env.extend, h] at henv; exact hdisj.1 func cap ps bd henv
  · intro func ps bd henv
    by_cases h : func = x
    · subst h; exact hF
    · simp [Env.extend, h] at henv; exact hdisj.2 func ps bd henv

/-- FnEnvDisjoint holds for the empty env. -/
theorem FnEnvDisjoint.empty : FnEnvDisjoint Env.empty F :=
  ⟨fun _ _ _ _ h => by simp [Env.empty] at h, fun _ _ _ h => by simp [Env.empty] at h⟩

/-- Extending env with a non-closure, non-rawFn value preserves FnEnvDisjoint. -/
theorem FnEnvDisjoint.extend_non_closure
    (hdisj : FnEnvDisjoint env F)
    (hnotcl : ∀ cap ps bd, v ≠ .closure cap ps bd)
    (hnotrfn : ∀ ps bd, v ≠ .rawFn ps bd) :
    FnEnvDisjoint (Env.extend env x v) F := by
  constructor
  · intro func cap ps bd henv
    by_cases h : func = x
    · subst h; simp [Env.extend] at henv; exact absurd henv (hnotcl cap ps bd)
    · simp [Env.extend, h] at henv; exact hdisj.1 func cap ps bd henv
  · intro func ps bd henv
    by_cases h : func = x
    · subst h; simp [Env.extend] at henv; exact absurd henv (hnotrfn ps bd)
    · simp [Env.extend, h] at henv; exact hdisj.2 func ps bd henv

/-- FnEnvDisjoint for bindParams: if all param binders are absent from F. -/
theorem FnEnvDisjoint.bindParams
    (hdisj : FnEnvDisjoint env F)
    (params : List Param) (args : List Value)
    (hparams : ∀ p, p ∈ params → F p.binder = none) :
    FnEnvDisjoint (Env.bindParams env params args) F := by
  simp [Env.bindParams, Env.extendMany]
  induction params generalizing args env with
  | nil => exact hdisj
  | cons p ps ih =>
    match args with
    | [] => exact hdisj
    | a :: as =>
      simp [List.zip, List.foldl]
      apply ih (FnEnvDisjoint.extend hdisj (hparams p (by simp))) as
      intro q hq; exact hparams q (by simp [hq])

/-- Every entry in the fn table has a corresponding entry in the fn type table. -/
def FnTableComplete (ft : FnTable) (F : FnTyTable) : Prop :=
  ∀ f params body, ft f = some (params, body) → ∃ retTy, F f = some (params.map (·.ty), retTy)

/-! ## Closure invariant

The key to proving apply cases: every closure value in the env
has a body that is well-typed in the appropriate context. This
invariant is maintained by all evaluation rules and gives us
the body typing at application sites.
-/

/-- A single value satisfies the closure invariant.
    For closures, provides body typing + ClosureInvariant for captured env. -/
inductive ValClosureOk : Value → Mtype → FnTyTable → Prop where
  | not_closure :
    (∀ cap ps bd, v ≠ .closure cap ps bd) →
    (∀ vals, v ≠ .tuple vals) →
    (∀ ps bd, v ≠ .rawFn ps bd) →
    ValClosureOk v τ F
  | tuple :
    (hvals : ∀ i (hv : i < vals.length) (hτ : i < τs.length),
      ValClosureOk (vals[i]'hv) (τs[i]'hτ) F) →
    ValClosureOk (.tuple vals) (.tuple τs) F
  | closure :
    (hptys : paramTys = params.map (·.ty)) →
    (hcapWT : EnvWellTyped captured Γcap) →
    (hcapInv : ∀ x v' τ', captured x = some v' → Γcap x = some τ' → ValClosureOk v' τ' F) →
    (hcapDisj : FnEnvDisjoint captured F) →
    (hparams : ∀ p, p ∈ params → F p.binder = none) →
    (hbody : HasType (TyEnv.bindParams Γcap params)
        JoinTyEnv.empty LoopTyEnv.empty F body retTy) →
    ValClosureOk (.closure captured params body) (.func paramTys retTy) F
  | rawFn :
    (hptys : paramTys = params.map (·.ty)) →
    (hparams : ∀ p, p ∈ params → F p.binder = none) →
    (hbody : HasType (TyEnv.bindParams TyEnv.empty params)
        JoinTyEnv.empty LoopTyEnv.empty F body retTy) →
    ValClosureOk (.rawFn params body) (.rawFunc paramTys retTy) F

/-- Non-closure, non-tuple, non-rawFn values trivially satisfy ValClosureOk. -/
theorem ValClosureOk.of_not_closure'
    (h : ∀ cap ps bd, v ≠ .closure cap ps bd)
    (h2 : ∀ vals, v ≠ .tuple vals := by intro _ h; cases h)
    (h3 : ∀ ps bd, v ≠ .rawFn ps bd := by intro _ _ h; cases h) :
    ValClosureOk v τ F :=
  .not_closure h h2 h3

/-- Extract per-element ValClosureOk from a tuple's proof. -/
theorem ValClosureOk.tuple_getAt?
    {vals : List Value} {τs : List Mtype} {pos : Nat} {v : Value} {τ : Mtype}
    (hcl : ValClosureOk (.tuple vals) (.tuple τs) F)
    (hv : vals[pos]? = some v) (hτ : τs[pos]? = some τ) :
    ValClosureOk v τ F := by
  match hcl with
  | .tuple hvals =>
    have hlen_v : pos < vals.length := by
      by_contra hlt; push_neg at hlt
      simp [List.getElem?_eq_none_iff.mpr (by omega)] at hv
    have hlen_τ : pos < τs.length := by
      by_contra hlt; push_neg at hlt
      simp [List.getElem?_eq_none_iff.mpr (by omega)] at hτ
    rw [List.getElem?_eq_getElem hlen_v] at hv
    rw [List.getElem?_eq_getElem hlen_τ] at hτ
    simp at hv hτ; rw [← hv, ← hτ]
    exact hvals pos hlen_v hlen_τ
  | .not_closure _ htup _ => exact absurd rfl (htup _)

/-- Every closure in env has a well-typed body given its captured env. -/
def ClosureInvariant (env : Env) (Γ : TyEnv) (F : FnTyTable) : Prop :=
  ∀ x v τ,
    env x = some v →
    Γ x = some τ →
    ValClosureOk v τ F

/-- Extending env preserves ClosureInvariant if the new value satisfies ValClosureOk. -/
theorem ClosureInvariant.extend
    (hinv : ClosureInvariant env Γ F)
    (hval : ValClosureOk v τ F) :
    ClosureInvariant (Env.extend env x v) (TyEnv.extend Γ x τ) F := by
  intro y v' τ' henv_y hΓ_y
  by_cases h : y = x
  · subst h
    simp only [Env.extend, ite_true, Option.some.injEq] at henv_y
    simp only [TyEnv.extend, ite_true, Option.some.injEq] at hΓ_y
    subst henv_y; subst hΓ_y
    exact hval
  · simp only [Env.extend, h, ite_false] at henv_y
    simp only [TyEnv.extend, h, ite_false] at hΓ_y
    exact hinv y v' τ' henv_y hΓ_y

/-- A closure value produced by Eval.function satisfies ValClosureOk
    when we have body typing, EnvWellTyped, and ClosureInvariant for captured env. -/
theorem ValClosureOk.mk_closure
    (henv : EnvWellTyped captured Γcap)
    (hcinv : ClosureInvariant captured Γcap F)
    (hdisj : FnEnvDisjoint captured F)
    (hparams : ∀ p, p ∈ params → F p.binder = none)
    (hbody : HasType (TyEnv.bindParams Γcap params)
        JoinTyEnv.empty LoopTyEnv.empty F body retTy) :
    ValClosureOk (.closure captured params body) (.func (params.map (·.ty)) retTy) F :=
  .closure rfl henv hcinv hdisj hparams hbody

/-- ClosureInvariant is maintained through bindParams with well-typed args.
    Each arg value must satisfy ValClosureOk. -/
theorem ClosureInvariant.bindParams
    (hinv : ClosureInvariant env Γ F)
    (params : List Param) (args : List Value)
    (hargs : ValueListHasType args (params.map (·.ty)))
    (hlen : params.length = args.length)
    (hargsClos : ∀ i (hv : i < args.length) (hτ : i < params.length),
      ValClosureOk (args[i]'hv) ((params.map (·.ty))[i]'(by simp; omega)) F) :
    ClosureInvariant (Env.bindParams env params args) (TyEnv.bindParams Γ params) F := by
  simp only [Env.bindParams, TyEnv.bindParams, Env.extendMany, TyEnv.extendMany]
  induction params generalizing args env Γ with
  | nil =>
    match args, hargs with
    | [], .nil => exact hinv
  | cons p ps ih =>
    match args, hargs with
    | a :: as_, .cons hvt rest =>
      simp [List.map, List.zip_cons_cons]
      have h0v : 0 < (a :: as_).length := by simp
      have h0τ : 0 < (p :: ps).length := by simp
      apply ih (ClosureInvariant.extend hinv (hargsClos 0 h0v h0τ)) as_ rest
        (by simp at hlen; omega)
      intro i hv hτ
      have hv' : i + 1 < (a :: as_).length := by simp; omega
      have hτ' : i + 1 < (p :: ps).length := by simp; omega
      exact hargsClos (i + 1) hv' hτ'

/-! ## ValueListHasType indexing -/

/-- Length agreement for ValueListHasType. -/
def ValueListHasType.length_eq : ValueListHasType vs τs → vs.length = τs.length
  | .nil => rfl
  | .cons _ rest => by simp [List.length_cons, rest.length_eq]

/-- Indexing into a well-typed value list. -/
def ValueListHasType.getAt :
    (h : ValueListHasType vs τs) → (i : Nat) →
    (hv : vs.length > i) → (hτ : τs.length > i) →
    ValueHasType (vs[i]'hv) (τs[i]'hτ)
  | .cons hvt _, 0, _, _ => hvt
  | .cons _ rest, i + 1, hv, hτ =>
    rest.getAt i (Nat.lt_of_succ_lt_succ hv) (Nat.lt_of_succ_lt_succ hτ)

/-- getElem? version of ValueListHasType indexing. -/
theorem ValueListHasType.getAt?
    (h : ValueListHasType vs τs) (i : Nat)
    (hv : vs[i]? = some v) (hτ : τs[i]? = some τ) :
    ValueHasType v τ := by
  have hlen_v : i < vs.length := by
    by_contra hlt; push_neg at hlt
    simp [List.getElem?_eq_none_iff.mpr (by omega)] at hv
  have hlen_τ : i < τs.length := by
    by_contra hlt; push_neg at hlt
    simp [List.getElem?_eq_none_iff.mpr (by omega)] at hτ
  have hvt := h.getAt i hlen_v hlen_τ
  rw [List.getElem?_eq_getElem hlen_v] at hv
  rw [List.getElem?_eq_getElem hlen_τ] at hτ
  simp at hv hτ
  rw [← hv, ← hτ]
  exact hvt

/-- A tuple value can only have tuple type. -/
theorem ValueHasType.tuple_not_constr
    (h : ValueHasType (.tuple vs) (.constr tid)) : False := by
  cases h

/-- A constr value can only have constr type. -/
theorem ValueHasType.constr_not_tuple
    (h : ValueHasType (.constr tag args) (.tuple τs)) : False := by
  cases h

/-- A loc value can only have constr or fixedarray type. -/
theorem ValueHasType.loc_not_tuple
    (h : ValueHasType (.loc l) (.tuple τs)) : False := by
  cases h

/-- A closure value can't have rawFunc type. -/
theorem ValueHasType.closure_not_rawFunc
    (h : ValueHasType (.closure c p b) (.rawFunc pts rt)) : False := by cases h

/-- A closure value can't have func type with wrong params (for topFn). -/
theorem ValueHasType.rawFn_not_func
    (h : ValueHasType (.rawFn p b) (.func pts rt)) : False := by cases h

/-! ## Env.bindParams well-typedness -/

/-- Extending env with one param-arg binding preserves well-typedness. -/
private theorem extendOne
    (hwt : EnvWellTyped env Γ) (hvt : ValueHasType v τ) :
    EnvWellTyped (Env.extend env x v) (TyEnv.extend Γ x τ) :=
  EnvWellTyped.extend_preserves hwt hvt

/-- Binding params with well-typed args gives a well-typed env extension. -/
theorem EnvWellTyped.bindParams_preserves
    (hwt : EnvWellTyped env Γ)
    (params : List Param) (args : List Value)
    (hargs : ValueListHasType args (params.map (·.ty)))
    (hlen : params.length = args.length) :
    EnvWellTyped (Env.bindParams env params args)
      (TyEnv.bindParams Γ params) := by
  simp only [Env.bindParams, TyEnv.bindParams, Env.extendMany, TyEnv.extendMany]
  induction params generalizing args env Γ with
  | nil =>
    match args, hargs with
    | [], .nil => exact hwt
  | cons p ps ih =>
    match args, hargs with
    | a :: as_, .cons hvt rest =>
      simp [List.map, List.zip_cons_cons, List.foldl]
      exact ih (EnvWellTyped.extend_preserves hwt hvt) as_ rest (by simp at hlen; omega)

/-- The empty env is well-typed wrt the empty TyEnv. -/
theorem EnvWellTyped.empty : EnvWellTyped Env.empty TyEnv.empty := by
  intro x τ h; simp [TyEnv.empty] at h

/-! ## handleErrorPropagate helper -/

/-- An outcome that is neither val nor error must be break/continue/return. -/
def OutcomeHasType.ofNotValNotError
    (hnotval : ∀ v, outcome ≠ .val v)
    (hnoterr : ∀ v, outcome ≠ .error v) :
    OutcomeHasType outcome τ :=
  match outcome with
  | .val v => absurd rfl (hnotval v)
  | .break _ _ => .break
  | .continue _ _ => .continue
  | .return _ => .return
  | .error v => absurd rfl (hnoterr v)

/-! ## Inversion lemma: extract ValueHasType from OutcomeHasType (.val v) -/

def OutcomeHasType.getVal : OutcomeHasType (.val v) τ → ValueHasType v τ
  | .val hvt => hvt

/-- Helper: EnvWellTyped through a switchConstr binder match. -/
private theorem switchConstrEnvWT
    (binder : Option Var) (henv : EnvWellTyped env Γ)
    (hvt : ValueHasType v (.constr tid)) :
    EnvWellTyped
      (match binder with | some x => Env.extend env x v | none => env)
      (match binder with | some x => TyEnv.extend Γ x (.constr tid) | none => Γ) := by
  cases binder with
  | some x => exact EnvWellTyped.extend_preserves henv hvt
  | none => exact henv

/-- Helper: ClosureInvariant through a switchConstr binder match. -/
private theorem switchConstrCInv
    (binder : Option Var) (hcinv : ClosureInvariant env Γ F)
    (hcl : ValClosureOk v (.constr tid) F) :
    ClosureInvariant
      (match binder with | some x => Env.extend env x v | none => env)
      (match binder with | some x => TyEnv.extend Γ x (.constr tid) | none => Γ) F := by
  cases binder with
  | some x => exact ClosureInvariant.extend hcinv hcl
  | none => exact hcinv

/-- Helper: FnEnvDisjoint through a switchConstr binder match (constr value). -/
private theorem switchConstrDisj
    (binder : Option Var) (hdisj : FnEnvDisjoint env F)
    (tag : ConstrTag) (args : List Value) :
    FnEnvDisjoint
      (match binder with | some x => Env.extend env x (.constr tag args) | none => env) F := by
  cases binder with
  | some x => exact hdisj.extend_non_closure (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
  | none => exact hdisj

/-! ## Preservation via mutual structural recursion

The three functions recurse on strictly smaller sub-derivations:
- `preservation` calls itself on sub-evals from compound rules, and
  calls `preservationArgs` on argument list evals.
- `preservationArgs` calls `preservation` on each element eval.

Preservation returns both:
1. `OutcomeHasType outcome τ` — the outcome has the expected type
2. For val outcomes: `ValClosureOk v τ F` — closure body typing is available
   (needed to maintain ClosureInvariant when the value enters an env)
-/

/-- Combined preservation result: outcome typing + closure invariant for values. -/
structure PresResult (outcome : Outcome) (τ : Mtype) (F : FnTyTable) where
  hasType : OutcomeHasType outcome τ
  closureOk : ∀ v, outcome = .val v → ValClosureOk v τ F

def PresResult.ofAbort (hab : outcome.isAbort) : PresResult outcome τ F :=
  ⟨.ofAbort _ hab, fun v h => by cases outcome <;> simp [Outcome.isAbort] at hab ⊢ <;> exact absurd h (by simp)⟩

def PresResult.val' (hvt : ValueHasType v τ) (hcl : ValClosureOk v τ F) :
    PresResult (.val v) τ F :=
  ⟨.val hvt, fun v' h => by cases h; exact hcl⟩

/-- Weaken: change the expected type when the outcome is an abort. -/
def PresResult.weaken (pr : PresResult outcome τ₁ F) (hab : outcome.isAbort) :
    PresResult outcome τ₂ F :=
  ⟨pr.hasType.weaken hab, fun v h => by
    cases outcome with
    | val => exact absurd hab (by simp [Outcome.isAbort])
    | «break» => cases h
    | «continue» => cases h
    | «return» => cases h
    | error => cases h⟩

/-- Break result. -/
def PresResult.break' : PresResult (.break bv label) τ F :=
  ⟨.break, fun v h => by cases h⟩

/-- Continue result. -/
def PresResult.continue' : PresResult (.continue args label) τ F :=
  ⟨.continue, fun v h => by cases h⟩

/-- Return result. -/
def PresResult.return' : PresResult (.return v) τ F :=
  ⟨.return, fun v' h => by cases h⟩

/-- Error result. -/
def PresResult.error' : PresResult (.error v) τ F :=
  ⟨.error, fun v' h => by cases h⟩

/-- Lift from OutcomeHasType for non-val/non-error outcomes. -/
def PresResult.ofNotValNotError
    (hnotval : ∀ v, outcome ≠ .val v)
    (hnoterr : ∀ v, outcome ≠ .error v) :
    PresResult outcome τ F :=
  ⟨.ofNotValNotError hnotval hnoterr,
   fun v h => absurd h (hnotval v)⟩

-- evalPrim results satisfy ValClosureOk.
-- Identity passes through; all other ops produce const/unit.
-- The closure/tuple/rawFn case for non-identity ops requires evalPrim pattern match reduction.
private theorem evalPrim_valClosureOk
    (heval : evalPrim op argVals = some v)
    (hprim : typeOfPrim op argTys = some τ)
    (hargs : ValueListHasType argVals argTys)
    (hclos : ∀ i (hv : i < argVals.length) (hτ : i < argTys.length),
      ValClosureOk (argVals[i]'hv) (argTys[i]'hτ) F) :
    ValClosureOk v τ F := by
  match v with
  | .const _ | .unit | .constr _ _ | .loc _ =>
    exact .not_closure (fun _ _ _ h => by cases h) (fun _ h => by cases h)
      (fun _ _ h => by cases h)
  | .closure _ _ _ | .tuple _ | .rawFn _ _ =>
    -- Identity passes through; non-identity never produces closure/tuple/rawFn.
    sorry

/-- Result of preservationArgs: value list typing + per-element ValClosureOk. -/
structure ArgsPresResult (vs : List Value) (τs : List Mtype) (F : FnTyTable) where
  hasTypes : ValueListHasType vs τs
  closureOks : ∀ i (hv : i < vs.length) (hτ : i < τs.length),
    ValClosureOk (vs[i]'hv) (τs[i]'hτ) F

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 1024 in
mutual

/-- Preservation for argument list evaluation.
    Returns value typing + per-value closure invariants. -/
def preservationArgs
    (htypes : HasTypeArgs Γ Δ Λ F es τs)
    (hevals : EvalArgs ft env s jt lt nl es vs s' nl')
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F) :
    ArgsPresResult vs τs F :=
  match htypes, hevals with
  | .nil, .nil => ⟨.nil, fun i hv _ => absurd hv (by simp)⟩
  | .cons htype htypes', .cons heval hrest =>
    let pr := preservation htype heval henv hft hcinv hdisj hftc
    let hvt := pr.hasType.getVal
    let hcl := pr.closureOk _ rfl
    let rest := preservationArgs htypes' hrest henv hft hcinv hdisj hftc
    ⟨.cons hvt rest.hasTypes, fun i hv hτ =>
      match i with
      | 0 => hcl
      | i + 1 => rest.closureOks i (by simp at hv; omega) (by simp at hτ; omega)⟩

/-- **Type Preservation**: well-typed expressions evaluate to well-typed outcomes.

    Proof by structural recursion on the `Eval` derivation. -/
def preservation
    (htype : HasType Γ Δ Λ F e τ)
    (heval : Eval ft env s jt lt nl e outcome s' nl')
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F) :
    PresResult outcome τ F :=
  match heval with
  -- ════════ Leaf cases ════════
  | .const => match htype with
    | .const => .val' .const (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .unit => match htype with
    | .unit => .val' .unit (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .var hx => match htype with
    | .var hΓ =>
      let hvt := EnvWellTyped.lookup henv hΓ hx
      .val' hvt (hcinv _ _ _ hx hΓ)
  | .varPrim hx => match htype with
    | .varPrim hΓ =>
      let hvt := EnvWellTyped.lookup henv hΓ hx
      .val' hvt (hcinv _ _ _ hx hΓ)
  | .function => match htype with
    | .function hparams hbody_typed =>
      .val' .closure (ValClosureOk.mk_closure henv hcinv hdisj hparams hbody_typed)
  | .rawFunction => match htype with
    | .rawFunction hparams_fn hbody_typed_fn =>
      .val' .rawFn (.rawFn rfl hparams_fn hbody_typed_fn)

  -- ════════ All abort propagation (use IH + weaken) ════════
  | .letAbort heval_rhs hab => match htype with
    | .let _ htype_rhs _ => (preservation htype_rhs heval_rhs henv hft hcinv hdisj hftc).weaken hab
  | .assignAbort heval_e hab => match htype with
    | .assign _ htype_e => (preservation htype_e heval_e henv hft hcinv hdisj hftc).weaken hab
  | .mutateAbortRec heval_rec hab => match htype with
    | .mutate htype_rec _ => (preservation htype_rec heval_rec henv hft hcinv hdisj hftc).weaken hab
  | .mutateAbortFld heval_rec heval_fld hab => match htype with
    | .mutate _ htype_fld => (preservation htype_fld heval_fld henv hft hcinv hdisj hftc).weaken hab
  | .fieldAbort heval_rec hab => match htype with
    | .fieldTuple htype_rec _ => (preservation htype_rec heval_rec henv hft hcinv hdisj hftc).weaken hab
    | .fieldHeap htype_rec => (preservation htype_rec heval_rec henv hft hcinv hdisj hftc).weaken hab
  | .ifAbort heval_cond hab => match htype with
    | .ifSome htype_cond _ _ => (preservation htype_cond heval_cond henv hft hcinv hdisj hftc).weaken hab
    | .ifNone htype_cond _ => (preservation htype_cond heval_cond henv hft hcinv hdisj hftc).weaken hab
  | .switchConstrAbort heval_obj hab => match htype with
    | .switchConstr htype_obj _ _ => (preservation htype_obj heval_obj henv hft hcinv hdisj hftc).weaken hab
  | .switchConstantAbort heval_obj hab => match htype with
    | .switchConstant htype_obj _ _ => (preservation htype_obj heval_obj henv hft hcinv hdisj hftc).weaken hab
  | .returnAbort heval_e hab => match htype with
    | .returnSingle htype_e => (preservation htype_e heval_e henv hft hcinv hdisj hftc).weaken hab
    | .returnOk htype_e => (preservation htype_e heval_e henv hft hcinv hdisj hftc).weaken hab
    | .returnErr htype_e => (preservation htype_e heval_e henv hft hcinv hdisj hftc).weaken hab
  | .breakAbort heval_arg hab => match htype with
    | .break _ htype_arg => (preservation htype_arg heval_arg henv hft hcinv hdisj hftc).weaken hab
  | .objectAbort heval_self hab => match htype with
    | .object htype_self => (preservation htype_self heval_self henv hft hcinv hdisj hftc).weaken hab
  | .andAbort heval_lhs hab => match htype with
    | .and htype_lhs _ => (preservation htype_lhs heval_lhs henv hft hcinv hdisj hftc).weaken hab
  | .orAbort heval_lhs hab => match htype with
    | .or htype_lhs _ => (preservation htype_lhs heval_lhs henv hft hcinv hdisj hftc).weaken hab
  | .recordUpdateAbortRec heval_rec hab => match htype with
    | .recordUpdate htype_rec _ => (preservation htype_rec heval_rec henv hft hcinv hdisj hftc).weaken hab
  -- EvalArgsAbort cases: use ofAbort (no sub-expression to IH on)
  | .constrAbort h => .ofAbort h.outcome_isAbort
  | .tupleAbort h => .ofAbort h.outcome_isAbort
  | .recordAbort h => .ofAbort h.outcome_isAbort
  | .arrayAbort h => .ofAbort h.outcome_isAbort
  | .recordUpdateAbortFields _ _ h => .ofAbort h.outcome_isAbort
  | .primAbort h => .ofAbort h.outcome_isAbort
  | .applyAbort h => .ofAbort h.outcome_isAbort
  | .seqAbort h => .ofAbort h.outcome_isAbort
  | .loopAbort h => .ofAbort h.outcome_isAbort
  | .continueAbort h => .ofAbort h.outcome_isAbort

  -- ════════ Break / continue ════════
  | .breakSome _ => .break'
  | .breakNone => .break'
  | .continue _ => .continue'

  -- ════════ Simple value-producing cases ════════
  | .assign _ => match htype with
    | .assign _ _ => .val' .unit (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .mutate _ _ _ => match htype with
    | .mutate _ _ => .val' .unit (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .constr _ => match htype with
    | .constr _ => .val' .constr (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .record _ => match htype with
    | .record _ => .val' .locConstr (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .array _ => match htype with
    | .array _ => .val' .locArray (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .recordUpdate _ _ _ _ => match htype with
    | .recordUpdate _ _ => .val' .locConstr (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .andFalse _ => match htype with
    | .and _ _ => .val' .const (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .orTrue _ => match htype with
    | .or _ _ => .val' .const (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .ifFalseNoElse _ => match htype with
    | .ifNone _ _ => .val' .unit (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))

  -- ════════ Recursive cases (IH via structural recursion) ════════

  | .let heval_rhs heval_body => match htype with
    | .let hFname htype_rhs htype_body =>
      let pr := preservation htype_rhs heval_rhs henv hft hcinv hdisj hftc
      let hvt := pr.hasType.getVal
      let hcl := pr.closureOk _ rfl
      let henv' := EnvWellTyped.extend_preserves henv hvt
      let hcinv' := ClosureInvariant.extend hcinv hcl
      preservation htype_body heval_body henv' hft hcinv' (hdisj.extend hFname) hftc

  | .letfnNonrec heval_body => match htype with
    | .letfnNonrec hFname hparams htype_fn htype_body =>
      let hcl := ValClosureOk.mk_closure henv hcinv hdisj hparams htype_fn
      let henv' := EnvWellTyped.extend_preserves henv ValueHasType.closure
      let hcinv' := ClosureInvariant.extend hcinv hcl
      preservation htype_body heval_body henv' hft hcinv' (hdisj.extend hFname) hftc

  | .letfnRec heval_body => match htype with
    | .letfnRec hFname hparams htype_fn htype_body =>
      sorry -- needs: recursive closure ValClosureOk (inner closure captures env without name)

  | .letfnTailJoin heval_body => match htype with
    | .letfnTailJoin _ htype_body =>
      preservation htype_body heval_body henv hft hcinv hdisj hftc

  | .letfnNontailJoin heval_body => match htype with
    | .letfnNontailJoin _ htype_body =>
      preservation htype_body heval_body henv hft hcinv hdisj hftc

  | .letrec _ heval_body => match htype with
    | .letrec _ _ htype_body => sorry -- needs recursive env typing

  | .ifTrue heval_cond heval_so => match htype with
    | .ifSome _ htype_so _ => preservation htype_so heval_so henv hft hcinv hdisj hftc
    | .ifNone _ htype_so => preservation htype_so heval_so henv hft hcinv hdisj hftc

  | .ifFalse heval_cond heval_not => match htype with
    | .ifSome _ _ htype_not => preservation htype_not heval_not henv hft hcinv hdisj hftc

  | .andTrue heval_lhs heval_rhs => match htype with
    | .and _ htype_rhs => preservation htype_rhs heval_rhs henv hft hcinv hdisj hftc

  | .orFalse heval_lhs heval_rhs => match htype with
    | .or _ htype_rhs => preservation htype_rhs heval_rhs henv hft hcinv hdisj hftc

  | .seq heval_exprs heval_last => match htype with
    | .seq _ htype_last => preservation htype_last heval_last henv hft hcinv hdisj hftc

  | .fieldTuple heval_rec hfield => match htype with
    | .fieldTuple htype_rec hpos =>
      let pr := preservation htype_rec heval_rec henv hft hcinv hdisj hftc
      let .val (.tuple hvts) := pr.hasType
      let v_typed := hvts.getAt? _ hfield hpos
      .val' v_typed (ValClosureOk.tuple_getAt? (pr.closureOk _ rfl) hfield hpos)
    | .fieldHeap htype_rec =>
      let pr := preservation htype_rec heval_rec henv hft hcinv hdisj hftc
      let .val hvt := pr.hasType
      absurd hvt (by intro h; exact ValueHasType.tuple_not_constr h)
  | .fieldConstr heval_rec hfield => match htype with
    | .fieldHeap _ => sorry -- need TypeDefs to constrain fieldTy
    | .fieldTuple htype_rec _ =>
      let pr := preservation htype_rec heval_rec henv hft hcinv hdisj hftc
      let .val hvt := pr.hasType
      absurd hvt (by intro h; exact ValueHasType.constr_not_tuple h)
  | .fieldRecord heval_rec _ hfield => match htype with
    | .fieldHeap _ => sorry -- need TypeDefs/store typing
    | .fieldTuple htype_rec _ =>
      let pr := preservation htype_rec heval_rec henv hft hcinv hdisj hftc
      let .val hvt := pr.hasType
      absurd hvt (by intro h; exact ValueHasType.loc_not_tuple h)

  | .object heval_self => match htype with
    | .object htype_self => preservation htype_self heval_self henv hft hcinv hdisj hftc

  -- ════════ Switch ════════
  | @Eval.switchConstr _ _ _ _ _ _ _ _ _ _ _ _ binder _ _ _ _ _ heval_obj hfind heval_branch =>
    match htype with
    | .switchConstr htype_obj htype_cases _ =>
      let pr_obj := preservation htype_obj heval_obj henv hft hcinv hdisj hftc
      let hvt_obj := pr_obj.hasType.getVal
      let hcl_obj := pr_obj.closureOk _ rfl
      let htype_branch := htype_cases _ _ _ hfind
      preservation htype_branch heval_branch
        (switchConstrEnvWT binder henv hvt_obj) hft
        (switchConstrCInv binder hcinv hcl_obj)
        (switchConstrDisj binder hdisj _ _)
        hftc
  | .switchConstrDefault heval_obj hfind_none heval_dflt => match htype with
    | .switchConstr _ _ htype_dflt =>
      preservation (htype_dflt _ rfl) heval_dflt henv hft hcinv hdisj hftc
  | .switchConstantMatch heval_obj hfindcase heval_branch => match htype with
    | .switchConstant _ htype_cases _ =>
      let ⟨i, hi, hbranch_eq⟩ := findConstantCase_index _ _ _ hfindcase
      let htype_branch := htype_cases i hi
      preservation (hbranch_eq ▸ htype_branch) heval_branch henv hft hcinv hdisj hftc
  | .switchConstantDefault _ _ heval_dflt => match htype with
    | .switchConstant _ _ htype_dflt => preservation htype_dflt heval_dflt henv hft hcinv hdisj hftc

  -- ════════ Prim ════════
  | .prim heval_args hprim => match htype with
    | .prim htype_args htype_prim =>
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc
      -- evalPrim never produces closures, so ValClosureOk is trivially satisfied
      let hvt := evalPrim_type_sound' hprim apr.hasTypes htype_prim
      .val' hvt (evalPrim_valClosureOk hprim htype_prim apr.hasTypes apr.closureOks)

  -- ════════ Application ════════
  | .applyClosure hclos heval_args hlen_clo heval_body => match htype with
    | .applyClosure hΓ htype_args =>
      let cinv_func := hcinv _ _ _ hclos hΓ
      -- Extract from ValClosureOk.closure
      match cinv_func with
      | .closure hptys hcapWT hcapCinv hcapDisj hclosParams hbodyTyped =>
        let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc
        let hvts' := hptys ▸ apr.hasTypes
        let hlen_bp := by
          have := hvts'.length_eq; simp [List.length_map] at this; omega
        let henv_body := EnvWellTyped.bindParams_preserves hcapWT _ _ hvts' hlen_bp
        let hcinv_body := ClosureInvariant.bindParams hcapCinv _ _ hvts' hlen_bp
          (fun i hv hτ => by
            have := apr.closureOks i hv (by
              subst hptys; simp [List.length_map]; exact hτ)
            exact hptys ▸ this)
        preservation hbodyTyped heval_body henv_body hft hcinv_body
          (FnEnvDisjoint.bindParams hcapDisj _ _ hclosParams) hftc
      | .not_closure hnotcl _ _ => absurd rfl (hnotcl _ _ _)
    | .applyRawFn hΓ _ =>
      absurd (EnvWellTyped.lookup henv hΓ hclos) (fun h => ValueHasType.closure_not_rawFunc h)
    | .applyTopFn hF _ => absurd hF (by rw [hdisj.1 _ _ _ _ hclos]; exact fun h => nomatch h)
  | .applyRawFn hfn heval_args hlen heval_body => match htype with
    | .applyRawFn hΓ htype_args =>
      let cinv_func := hcinv _ _ _ hfn hΓ
      match cinv_func with
      | .rawFn hptys hclosParams hbodyTyped =>
        let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc
        let hvts' := hptys ▸ apr.hasTypes
        let hlen_bp := by
          have := hvts'.length_eq; simp [List.length_map] at this; omega
        let henv_body := EnvWellTyped.bindParams_preserves EnvWellTyped.empty _ _ hvts' hlen_bp
        let hcinv_empty : ClosureInvariant Env.empty TyEnv.empty F :=
          fun x v τ henv_x _ => absurd henv_x (by simp [Env.empty])
        let hcinv_body := ClosureInvariant.bindParams hcinv_empty _ _ hvts' hlen_bp
          (fun i hv hτ => by
            have := apr.closureOks i hv (by subst hptys; simp [List.length_map]; exact hτ)
            exact hptys ▸ this)
        preservation hbodyTyped heval_body henv_body hft hcinv_body
          (FnEnvDisjoint.bindParams FnEnvDisjoint.empty _ _ hclosParams) hftc
      | .not_closure _ _ hnotrfn => absurd rfl (hnotrfn _ _)
    | .applyClosure hΓ _ =>
      absurd (EnvWellTyped.lookup henv hΓ hfn) (fun h => ValueHasType.rawFn_not_func h)
    | .applyTopFn hF _ => absurd hF (by rw [hdisj.2 _ _ _ hfn]; exact fun h => nomatch h)
  | .applyTopFn hfnlookup heval_args hlen heval_body => match htype with
    | .applyTopFn hF htype_args => by
      -- From FnTableWellTyped: get params/body from ft that match F
      obtain ⟨params', body', hft_lookup, hmap_eq, hftparams, hbody_typed⟩ := hft _ _ _ hF
      -- Unify ft lookups: hfnlookup and hft_lookup both give ft func = some (_, _)
      rw [hfnlookup] at hft_lookup
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hft_lookup)
      -- Now params'/body' are unified with the eval's params/body
      -- hmap_eq : params.map (·.ty) = paramTys, hbody_typed : HasType ... body τ
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc
      -- apr.hasTypes : ValueListHasType argVals paramTys
      -- We need ValueListHasType argVals (params.map (·.ty))
      have hvts_map := hmap_eq ▸ apr.hasTypes
      have henv_body := EnvWellTyped.bindParams_preserves EnvWellTyped.empty _ _ hvts_map hlen
      have hcinv_empty : ClosureInvariant Env.empty TyEnv.empty F :=
        fun x v τ henv_x _ => absurd henv_x (by simp [Env.empty])
      have hcinv_body := ClosureInvariant.bindParams hcinv_empty _ _ hvts_map hlen
        (fun i hv hτ => by
          have := apr.closureOks i hv (by subst hmap_eq; simp [List.length_map]; exact hτ)
          exact hmap_eq ▸ this)
      exact preservation hbody_typed heval_body henv_body hft hcinv_body
        (FnEnvDisjoint.bindParams FnEnvDisjoint.empty _ _ hftparams) hftc
    | .applyClosure hΓ _ => by
      -- ft func = some (...) → F func = some (...) by FnTableComplete
      obtain ⟨retTy', hFsome⟩ := hftc _ _ _ hfnlookup
      -- Γ func = some (.func ...) → env func = some v with ValueHasType v (.func ...)
      obtain ⟨v, henv_v, hvt⟩ := henv _ _ hΓ
      -- ValueHasType v (.func ...) → v is a closure
      match v, hvt with
      | .closure cap ps bd, .closure =>
        exact absurd hFsome (by rw [hdisj.1 _ _ _ _ henv_v]; exact fun h => nomatch h)
    | .applyRawFn hΓ _ => by
      obtain ⟨retTy', hFsome⟩ := hftc _ _ _ hfnlookup
      obtain ⟨v, henv_v, hvt⟩ := henv _ _ hΓ
      match v, hvt with
      | .rawFn ps bd, .rawFn =>
        exact absurd hFsome (by rw [hdisj.2 _ _ _ henv_v]; exact fun h => nomatch h)
  | .applyJoin _ _ _ _ => sorry -- needs join env typing

  -- ════════ Tuple (needs ValueListHasType from preservationArgs) ════════
  | .tuple heval_args => match htype with
    | .tuple htype_args =>
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc
      .val' (.tuple apr.hasTypes) (.tuple apr.closureOks)

  -- ════════ Loop ════════
  | .loopVal heval_args heval_body => match htype with
    | .loop hloopParams htype_args htype_body =>
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc
      let hlen := by
        have := apr.hasTypes.length_eq; simp [List.length_map] at this; omega
      let henv' := EnvWellTyped.bindParams_preserves henv _ _ apr.hasTypes hlen
      let hcinv' := ClosureInvariant.bindParams hcinv _ _ apr.hasTypes hlen
        (fun i hv hτ => apr.closureOks i hv (by simp [List.length_map]; exact hτ))
      preservation htype_body heval_body henv' hft hcinv'
        (FnEnvDisjoint.bindParams hdisj _ _ hloopParams) hftc
  | .loopBreak heval_args heval_body => match htype with
    | .loop _ htype_args htype_body =>
      sorry -- needs: extract break arg typing through OutcomeHasType
  | .loopBreakNone heval_args heval_body => match htype with
    | .loop _ htype_args htype_body =>
      sorry -- needs: τ = .unit from Λ label constraint
  | .loopContinue _ _ _ heval_reentry => sorry -- needs re-entry typing
  | .loopReturn heval_args heval_body => match htype with
    | .loop _ htype_args htype_body => .return'
  | .loopError heval_args heval_body => match htype with
    | .loop _ htype_args htype_body => .error'

  -- ════════ Error handling ════════
  | .handleErrorToResultOk heval_obj => match htype with
    | .handleErrorToResult htype_obj =>
      .val' .constr (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .handleErrorToResultErr heval_obj => match htype with
    | .handleErrorToResult _ =>
      .val' .constr (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .handleErrorJoinOk heval_obj => match htype with
    | .handleErrorJoinapply htype_obj _ => preservation htype_obj heval_obj henv hft hcinv hdisj hftc
  | .handleErrorJoinErr heval_obj _ heval_body => sorry -- needs join env typing
  | .handleErrorReturnErrOk heval_obj => match htype with
    | .handleErrorReturnErr htype_obj => preservation htype_obj heval_obj henv hft hcinv hdisj hftc
  | .handleErrorReturnErrErr heval_obj => match htype with
    | .handleErrorReturnErr _ => .error'
  | .handleErrorPropagate _ hnotval hnoterr =>
    .ofNotValNotError hnotval hnoterr

  -- ════════ Return ════════
  | .returnSingle heval_e => match htype with
    | .returnSingle htype_e => preservation htype_e heval_e henv hft hcinv hdisj hftc
  | .returnError heval_e => match htype with
    | .returnErr _ => .error'
  | .returnOk heval_e => match htype with
    | .returnOk htype_e => preservation htype_e heval_e henv hft hcinv hdisj hftc

def preservation_val
    (htype : HasType Γ Δ Λ F e τ)
    (heval : Eval ft env s jt lt nl e (.val v) s' nl')
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F) :
    ValueHasType v τ :=
  (preservation htype heval henv hft hcinv hdisj hftc).hasType.getVal

end -- mutual

end Moonbit.Mcore
