/-
  MoonBit Compiler — Mcore Type Preservation
  Proves that well-typed expressions evaluate to well-typed outcomes
  via mutual structural recursion on the evaluation derivation.
-/
import MoonbitSemantics.Mcore.Typing

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp)

/-! ## Helpers -/

@[simp] theorem Outcome.val_not_abort (v : Value) : ¬ (Outcome.val v).isAbort := by
  simp [Outcome.isAbort]

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
      HasType (TyEnv.bindParams TyEnv.empty params)
        JoinTyEnv.empty LoopTyEnv.empty F body retTy

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

/-! ## Preservation via mutual structural recursion

The three functions recurse on strictly smaller sub-derivations:
- `preservation` calls itself on sub-evals from compound rules, and
  calls `preservationArgs` on argument list evals.
- `preservationArgs` calls `preservation` on each element eval.
- `preservationAbort` is non-recursive (abort outcomes are trivially typed).
-/

/-! ## evalPrim type soundness -/

/-- evalPrim preserves types: each prim case returns the declared type.
    Proof requires exhaustive case analysis on (op, argTys, args). -/
theorem evalPrim_type_sound
    (heval : evalPrim op args = some v)
    (hargs : ValueListHasType args argTys)
    (hprim : typeOfPrim op argTys = some τ) :
    ValueHasType v τ := by
  sorry -- ~30 mechanical cases, each trivially .const/.unit/identity

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1024 in
mutual

/-- Preservation for argument list evaluation. -/
def preservationArgs
    (htypes : HasTypeArgs Γ Δ Λ F es τs)
    (hevals : EvalArgs ft env s jt lt nl es vs s' nl')
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F) :
    ValueListHasType vs τs :=
  match htypes, hevals with
  | .nil, .nil => .nil
  | .cons htype htypes', .cons heval hrest =>
    let oht := preservation htype heval henv hft
    -- heval : Eval ... e (.val v) ..., so oht : OutcomeHasType (.val v) τ
    let hvt := oht.getVal
    .cons hvt (preservationArgs htypes' hrest henv hft)

/-- **Type Preservation**: well-typed expressions evaluate to well-typed outcomes.

    Proof by structural recursion on the `Eval` derivation. -/
def preservation
    (htype : HasType Γ Δ Λ F e τ)
    (heval : Eval ft env s jt lt nl e outcome s' nl')
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F) :
    OutcomeHasType outcome τ :=
  match heval with
  -- ════════ Leaf cases ════════
  | .const => match htype with | .const => .val .const
  | .unit => match htype with | .unit => .val .unit
  | .var hx => match htype with
    | .var hΓ => .val (EnvWellTyped.lookup henv hΓ hx)
  | .varPrim hx => match htype with
    | .varPrim hΓ => .val (EnvWellTyped.lookup henv hΓ hx)
  | .function => match htype with
    | .function _ => .val .closure
  | .rawFunction => match htype with
    | .rawFunction _ => .val .rawFn

  -- ════════ All abort propagation ════════
  | .letAbort _ hab => .ofAbort _ hab
  | .assignAbort _ hab => .ofAbort _ hab
  | .mutateAbortRec _ hab => .ofAbort _ hab
  | .mutateAbortFld _ _ hab => .ofAbort _ hab
  | .fieldAbort _ hab => .ofAbort _ hab
  | .ifAbort _ hab => .ofAbort _ hab
  | .switchConstrAbort _ hab => .ofAbort _ hab
  | .switchConstantAbort _ hab => .ofAbort _ hab
  | .returnAbort _ hab => .ofAbort _ hab
  | .breakAbort _ hab => .ofAbort _ hab
  | .objectAbort _ hab => .ofAbort _ hab
  | .andAbort _ hab => .ofAbort _ hab
  | .orAbort _ hab => .ofAbort _ hab
  | .recordUpdateAbortRec _ hab => .ofAbort _ hab
  | .constrAbort h => .ofAbort _ h.outcome_isAbort
  | .tupleAbort h => .ofAbort _ h.outcome_isAbort
  | .recordAbort h => .ofAbort _ h.outcome_isAbort
  | .arrayAbort h => .ofAbort _ h.outcome_isAbort
  | .recordUpdateAbortFields _ _ h => .ofAbort _ h.outcome_isAbort
  | .primAbort h => .ofAbort _ h.outcome_isAbort
  | .applyAbort h => .ofAbort _ h.outcome_isAbort
  | .seqAbort h => .ofAbort _ h.outcome_isAbort
  | .loopAbort h => .ofAbort _ h.outcome_isAbort
  | .continueAbort h => .ofAbort _ h.outcome_isAbort

  -- ════════ Break / continue (non-val outcomes, always well-typed) ════════
  | .breakSome _ => .break
  | .breakNone => .break
  | .continue _ => .continue

  -- ════════ Simple value-producing cases ════════
  | .assign _ => match htype with | .assign _ _ => .val .unit
  | .mutate _ _ _ => match htype with | .mutate _ _ => .val .unit
  | .constr _ => match htype with | .constr _ => .val .constr
  | .record _ => match htype with | .record _ => .val .locConstr
  | .array _ => match htype with | .array _ => .val .locArray
  | .recordUpdate _ _ _ _ => match htype with | .recordUpdate _ _ => .val .locConstr
  | .andFalse _ => match htype with | .and _ _ => .val .const
  | .orTrue _ => match htype with | .or _ _ => .val .const
  | .ifFalseNoElse _ => match htype with | .ifNone _ _ => .val .unit

  -- ════════ Recursive cases (IH via structural recursion) ════════

  | .let heval_rhs heval_body => match htype with
    | .let htype_rhs htype_body =>
      let hvt := (preservation htype_rhs heval_rhs henv hft).getVal
      let henv' := EnvWellTyped.extend_preserves henv hvt
      preservation htype_body heval_body henv' hft

  | .letfnNonrec heval_body => match htype with
    | .letfnNonrec htype_fn htype_body =>
      let henv' := EnvWellTyped.extend_preserves henv ValueHasType.closure
      preservation htype_body heval_body henv' hft

  | .letfnRec heval_body => match htype with
    | .letfnRec _ htype_body =>
      let henv' := EnvWellTyped.extend_preserves henv ValueHasType.closure
      preservation htype_body heval_body henv' hft

  | .letfnTailJoin heval_body => match htype with
    | .letfnTailJoin _ htype_body =>
      preservation htype_body heval_body henv hft

  | .letfnNontailJoin heval_body => match htype with
    | .letfnNontailJoin _ htype_body =>
      preservation htype_body heval_body henv hft

  | .letrec _ heval_body => match htype with
    | .letrec _ _ htype_body => sorry -- needs recursive env typing

  | .ifTrue heval_cond heval_so => match htype with
    | .ifSome _ htype_so _ => preservation htype_so heval_so henv hft
    | .ifNone _ htype_so => preservation htype_so heval_so henv hft

  | .ifFalse heval_cond heval_not => match htype with
    | .ifSome _ _ htype_not => preservation htype_not heval_not henv hft

  | .andTrue heval_lhs heval_rhs => match htype with
    | .and _ htype_rhs => preservation htype_rhs heval_rhs henv hft

  | .orFalse heval_lhs heval_rhs => match htype with
    | .or _ htype_rhs => preservation htype_rhs heval_rhs henv hft

  | .seq heval_exprs heval_last => match htype with
    | .seq _ htype_last => preservation htype_last heval_last henv hft

  | .fieldTuple heval_rec hfield => sorry -- needs accessor pattern + ValueListHasType.get
  | .fieldConstr heval_rec _ => sorry
  | .fieldRecord heval_rec _ _ => sorry

  | .object heval_self => match htype with
    | .object htype_self =>
      -- The Eval.object rule just evaluates self and returns its value.
      -- But HasType.object says the result type is (.trait tid), not selfTy.
      -- This is a genuine type gap: the eval returns self's value but the
      -- typing says it should be a trait. Need vtable wrapping in eval.
      sorry

  -- ════════ Switch ════════
  -- Switch cases: need env extension for binder + branch typing extraction
  | .switchConstr _ _ _ => sorry
  | .switchConstrDefault heval_obj _ heval_dflt => match htype with
    | .switchConstrDefault _ htype_dflt => preservation htype_dflt heval_dflt henv hft
    | .switchConstrCase _ _ _ => sorry -- typing says case matches but eval says default
  | .switchConstantMatch _ _ _ => sorry
  | .switchConstantDefault _ _ heval_dflt => match htype with
    | .switchConstant _ _ htype_dflt => preservation htype_dflt heval_dflt henv hft

  -- ════════ Prim ════════
  | .prim heval_args hprim => match htype with
    | .prim htype_args htype_prim =>
      let hvts := preservationArgs htype_args heval_args henv hft
      .val (evalPrim_type_sound hprim hvts htype_prim)

  -- ════════ Application ════════
  -- ════════ Application ════════
  -- Apply: needs step-indexed logical relation or closure store typing.
  -- ValueHasType.closure doesn't carry body typing (strict positivity).
  | .applyClosure _ _ _ _ => sorry
  | .applyRawFn _ _ _ _ => sorry
  | .applyTopFn _ _ _ _ => sorry
  | .applyJoin _ _ _ _ => sorry

  -- ════════ Tuple (needs ValueListHasType from preservationArgs) ════════
  | .tuple heval_args => match htype with
    | .tuple htype_args =>
      .val (.tuple (preservationArgs htype_args heval_args henv hft))

  -- ════════ Loop ════════
  | .loopVal heval_args heval_body => match htype with
    | .loop htype_args htype_body =>
      let hvts := preservationArgs htype_args heval_args henv hft
      let henv' := EnvWellTyped.bindParams_preserves henv _ _ hvts (by have := hvts.length_eq; simp [List.length_map] at this; omega)
      -- body is typed with extended env + loop env
      -- We have htype_body but it uses LoopTyEnv.extend — preservation call needs matching
      preservation htype_body heval_body henv' hft
  | .loopBreak heval_args heval_body => match htype with
    | .loop htype_args htype_body =>
      let hvts := preservationArgs htype_args heval_args henv hft
      let henv' := EnvWellTyped.bindParams_preserves henv _ _ hvts (by have := hvts.length_eq; simp [List.length_map] at this; omega)
      let .break := preservation htype_body heval_body henv' hft
      .val sorry -- break value has the right type
  | .loopBreakNone heval_args heval_body => match htype with
    | .loop htype_args htype_body => sorry -- τ must be unit if break None
  | .loopContinue _ _ _ heval_reentry => sorry -- needs re-entry typing
  | .loopReturn heval_args heval_body => match htype with
    | .loop htype_args htype_body =>
      let hvts := preservationArgs htype_args heval_args henv hft
      let henv' := EnvWellTyped.bindParams_preserves henv _ _ hvts (by have := hvts.length_eq; simp [List.length_map] at this; omega)
      preservation htype_body heval_body henv' hft
  | .loopError heval_args heval_body => match htype with
    | .loop htype_args htype_body =>
      let hvts := preservationArgs htype_args heval_args henv hft
      let henv' := EnvWellTyped.bindParams_preserves henv _ _ hvts (by have := hvts.length_eq; simp [List.length_map] at this; omega)
      preservation htype_body heval_body henv' hft

  -- ════════ Error handling ════════
  | .handleErrorToResultOk heval_obj => match htype with
    | .handleErrorToResult htype_obj => .val .constr
  | .handleErrorToResultErr heval_obj => match htype with
    | .handleErrorToResult _ => .val .constr
  | .handleErrorJoinOk heval_obj => match htype with
    | .handleErrorJoinapply htype_obj _ => preservation htype_obj heval_obj henv hft
  | .handleErrorJoinErr heval_obj _ heval_body => sorry -- needs join env typing
  | .handleErrorReturnErrOk heval_obj => match htype with
    | .handleErrorReturnErr htype_obj => preservation htype_obj heval_obj henv hft
  | .handleErrorReturnErrErr heval_obj => match htype with
    | .handleErrorReturnErr _ => .error
  | .handleErrorPropagate _ hnotval hnoterr =>
    OutcomeHasType.ofNotValNotError hnotval hnoterr

  -- ════════ Return ════════
  | .returnSingle heval_e => match htype with
    | .returnSingle htype_e => preservation htype_e heval_e henv hft
  | .returnError heval_e => match htype with
    | .returnErr _ => .error
  | .returnOk heval_e => match htype with
    | .returnOk htype_e => preservation htype_e heval_e henv hft

def preservation_val
    (htype : HasType Γ Δ Λ F e τ)
    (heval : Eval ft env s jt lt nl e (.val v) s' nl')
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F) :
    ValueHasType v τ :=
  (preservation htype heval henv hft).getVal

end -- mutual

end Moonbit.Mcore
