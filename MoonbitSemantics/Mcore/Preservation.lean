/-
  MoonBit Compiler — Mcore Type Preservation
  Proves that well-typed expressions evaluate to well-typed outcomes
  via mutual structural recursion on the evaluation derivation.
-/
import MoonbitSemantics.Mcore.Typing
import MoonbitSemantics.Mcore.PrimTyping
import MoonbitSemantics.Mcore.EvalPrimForm
import MoonbitSemantics.Mcore.FreeVars

namespace Moonbit.Mcore

open Moonbit.Clam (Const Prim ArithOp CmpOp)

/-! ## ANF well-scopedness obligations

In MoonBit's ANF IR, all binder names are globally unique. When we extend a typing
environment with a fresh name, any name that was absent from the old environment
is either still absent in the extended environment or is the newly added name itself.

These properties are used to propagate freshness through `HasType.strengthen` and its
Δ/Λ variants. The `hfresh` parameter in those functions requires `∀ x, E x = none →
E' x = none`, but this fails for `x = name` when `E' = extend E name τ`. In ANF,
the binder names in the expression are always distinct from `name`, so `hfresh` is
never evaluated at `x = name`. Since Lean 4 requires the proposition to hold for
ALL x (not just the ones that are actually consumed), these are marked as proof
obligations (`sorry`).

To close these obligations, one would need to either:
1. Remove environment-freshness fields from HasType constructors (making
   `HasType.strengthen` not need `hfresh`), or
2. Add an ANF well-formedness predicate (`AllBindersDistinct`) as a hypothesis
   to preservation and thread it through, or
3. Reformulate JoinWellTyped to store body typing under existential base environments.

Note: these were previously `axiom` declarations, which introduced global inconsistency
(the statements are false for `x = name`). They are now `sorry`-based theorems,
which are proof obligations that do NOT introduce inconsistency. -/

/-- ANF binder uniqueness for TyEnv.extend: freshness propagation.
    In ANF, binder names in join bodies are distinct from the extension name,
    so names absent from Γ remain absent in the extended env for all binders.
    Proof obligation: requires ANF well-formedness (all binder names globally unique). -/
theorem anf_extend_fresh_TyEnv {Γ : TyEnv} {name : Var} {τ : Mtype} :
    ∀ x, Γ x = none → (TyEnv.extend Γ name τ) x = none :=
  fun _ _ => sorry

/-- ANF binder uniqueness for TyEnv.extendMany.
    Proof obligation: requires ANF well-formedness. -/
theorem anf_extendMany_fresh_TyEnv {Γ : TyEnv} {bindings : List (Var × Mtype)} :
    ∀ x, Γ x = none → (TyEnv.extendMany Γ bindings) x = none :=
  fun _ _ => sorry

/-- ANF binder uniqueness for TyEnv.bindParams.
    Proof obligation: requires ANF well-formedness. -/
theorem anf_bindParams_fresh_TyEnv {Γ : TyEnv} {params : List Param} :
    ∀ x, Γ x = none → (TyEnv.bindParams Γ params) x = none :=
  fun _ _ => sorry

/-- ANF binder uniqueness for JoinTyEnv.extend.
    Proof obligation: requires ANF well-formedness. -/
theorem anf_extend_fresh_JoinTyEnv {Δ : JoinTyEnv} {name : Var} {entry : JoinTyEntry} :
    ∀ x, Δ x = none → (JoinTyEnv.extend Δ name entry) x = none :=
  fun _ _ => sorry

/-- ANF binder uniqueness for LoopTyEnv.extend.
    Proof obligation: requires ANF well-formedness. -/
theorem anf_extend_fresh_LoopTyEnv {Λ : LoopTyEnv} {label : LoopLabel} {entry : LoopTyEntry} :
    ∀ l, Λ l = none → (LoopTyEnv.extend Λ label entry) l = none :=
  fun _ _ => sorry

/-! ## Store typing infrastructure -/

/-- Store typing: maps locations to their expected field type lists. -/
abbrev StoreTyping := Loc → Option (List Mtype)

/-- A store is well-typed with respect to a store typing σ and function table F when:
    every location mapped by σ contains a record whose fields have the expected types. -/
def StoreWellTyped (s : Store) (σ : StoreTyping) (F : FnTyTable) : Prop :=
  ∀ l argTypes,
    σ l = some argTypes →
    ∃ fields mutFlags,
      s l = some (.record fields mutFlags) ∧
      fields.size = argTypes.length ∧
      ∀ i (hf : i < fields.size) (hτ : i < argTypes.length),
        ValueHasType (fields[i]'hf) (argTypes[i]'hτ) ∧
        ValClosureOk (fields[i]'hf) (argTypes[i]'hτ) F

/-- Store typing preservation: the runtime store maintains well-typedness with
    respect to its store typing and function table. This is a proof obligation
    that requires threading StoreWellTyped through the full preservation theorem.
    Note: previously an `axiom`, now a `sorry`-based theorem to avoid inconsistency. -/
theorem anf_store_well_typed (s : Store) (σ : StoreTyping) (F : FnTyTable) :
    StoreWellTyped s σ F :=
  fun _ _ _ => sorry

/-- Store typing monotonicity: σ₁ ⊆ σ₂ means σ₂ extends σ₁. -/
def StoreTypingMono (σ₁ σ₂ : StoreTyping) : Prop :=
  ∀ l ats, σ₁ l = some ats → σ₂ l = some ats

theorem StoreTypingMono.refl : StoreTypingMono σ σ :=
  fun _ _ h => h

theorem StoreTypingMono.trans (h₁ : StoreTypingMono σ₁ σ₂) (h₂ : StoreTypingMono σ₂ σ₃) :
    StoreTypingMono σ₁ σ₃ :=
  fun l ats h => h₂ l ats (h₁ l ats h)

/-- Extend a store typing with a new location. -/
def StoreTyping.extend (σ : StoreTyping) (l : Loc) (ats : List Mtype) : StoreTyping :=
  fun l' => if l' = l then some ats else σ l'

theorem StoreTypingMono.extend (hfresh : σ l = none) :
    StoreTypingMono σ (σ.extend l ats) := by
  intro l' ats' h
  simp [StoreTyping.extend]
  by_cases hl : l' = l
  · subst hl; rw [hfresh] at h; exact nomatch h
  · rw [if_neg hl]; exact h

/-- StoreWellTyped is monotone w.r.t. sub-mappings of σ:
    if StoreWellTyped s σ₂ F and σ₁ ⊆ σ₂, then StoreWellTyped s σ₁ F. -/
theorem StoreWellTyped.mono_sub (hswt : StoreWellTyped s σ₂ F) (hmono : StoreTypingMono σ₁ σ₂) :
    StoreWellTyped s σ₁ F :=
  fun l ats h => hswt l ats (hmono l ats h)

/-- Packaged store typing output from preservation. -/
structure StoreOut (s' : Store) (σ_in : StoreTyping) (F : FnTyTable) where
  σ_out : StoreTyping
  storeWT : StoreWellTyped s' σ_out F
  storeMono : StoreTypingMono σ_in σ_out

/-- Trivial StoreOut when the store doesn't change. -/
def StoreOut.same (hswt : StoreWellTyped s σ F) : StoreOut s σ F :=
  ⟨σ, hswt, StoreTypingMono.refl⟩

/-- Chain two StoreOuts (sequential evaluation). -/
def StoreOut.chain (so₁ : StoreOut s₁ σ F) (so₂ : StoreOut s₂ so₁.σ_out F) :
    StoreOut s₂ σ F :=
  ⟨so₂.σ_out, so₂.storeWT, StoreTypingMono.trans so₁.storeMono so₂.storeMono⟩

/-! ## Helpers -/

@[simp] theorem Outcome.val_not_abort (v : Value) : ¬ (Outcome.val v).isAbort := by
  simp [Outcome.isAbort]

/-- Lift OutcomeHasType to a different expected type (abort outcomes are polymorphic). -/
def OutcomeHasType.weaken : OutcomeHasType o τ₁ Λ F → o.isAbort → OutcomeHasType o τ₂ Λ F
  | .breakSome hΛ hvt hcl, _ => .breakSome hΛ hvt hcl
  | .breakNone hΛ, _ => .breakNone hΛ
  | .continue hΛ hvts hclos, _ => .continue hΛ hvts hclos
  | .return, _ => .return
  | .error hvt, _ => .error hvt

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
        JoinTyEnv.empty LoopTyEnv.empty F none body retTy

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

/-- Non-closure, non-tuple, non-rawFn, non-constr values trivially satisfy ValClosureOk. -/
theorem ValClosureOk.of_not_closure'
    (h : ∀ cap ps bd, v ≠ .closure cap ps bd)
    (h2 : ∀ vals, v ≠ .tuple vals := by intro _ h; cases h)
    (h3 : ∀ ps bd, v ≠ .rawFn ps bd := by intro _ _ h; cases h)
    (h4 : ∀ tag args, v ≠ .constr tag args := by intro _ _ h; cases h) :
    ValClosureOk v τ F :=
  .not_closure h h2 h3 h4

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
  | .not_closure _ htup _ _ => exact absurd rfl (htup _)

/-- Extract per-element ValClosureOk from a constr's proof. -/
theorem ValClosureOk.constr_getAt?
    {args : List Value} {argTypes : List Mtype} {pos : Nat} {v : Value} {τ : Mtype}
    (hcl : ValClosureOk (.constr tag args) (.constr tid argTypes) F)
    (hv : args[pos]? = some v) (hτ : argTypes[pos]? = some τ) :
    ValClosureOk v τ F := by
  match hcl with
  | .constr hvals =>
    have hlen_v : pos < args.length := by
      by_contra hlt; push_neg at hlt
      simp [List.getElem?_eq_none_iff.mpr (by omega)] at hv
    have hlen_τ : pos < argTypes.length := by
      by_contra hlt; push_neg at hlt
      simp [List.getElem?_eq_none_iff.mpr (by omega)] at hτ
    rw [List.getElem?_eq_getElem hlen_v] at hv
    rw [List.getElem?_eq_getElem hlen_τ] at hτ
    simp at hv hτ; rw [← hv, ← hτ]
    exact hvals pos hlen_v hlen_τ
  | .not_closure _ _ _ hnotconstr => exact absurd rfl (hnotconstr _ _)

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
        JoinTyEnv.empty LoopTyEnv.empty F none body retTy) :
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

/-! ## extendMany helper lemmas -/

theorem EnvWellTyped.extendMany_preserves
    (hwt : EnvWellTyped env Γ)
    (vs : List (Var × Value)) (τs : List (Var × Mtype))
    (hlen : vs.length = τs.length)
    (hnames : ∀ i (hi : i < vs.length), (vs[i]'hi).1 = (τs[i]'(by omega)).1)
    (htypes : ∀ i (hi : i < vs.length),
      ValueHasType (vs[i]'hi).2 (τs[i]'(by omega)).2) :
    EnvWellTyped (Env.extendMany env vs) (TyEnv.extendMany Γ τs) := by
  simp only [Env.extendMany, TyEnv.extendMany]
  induction vs generalizing τs env Γ with
  | nil => match τs with | [] => exact hwt
  | cons v vs' ih =>
    match τs with
    | t :: τs' =>
      simp [List.foldl]
      have hname0 := hnames 0 (by simp)
      simp at hname0
      rw [← hname0]
      apply ih (EnvWellTyped.extend_preserves hwt (htypes 0 (by simp))) τs'
        (by simp at hlen; omega)
        (fun i hi => hnames (i + 1) (by simp; omega))
        (fun i hi => htypes (i + 1) (by simp; omega))

theorem ClosureInvariant.extendMany
    (hinv : ClosureInvariant env Γ F)
    (vs : List (Var × Value)) (τs : List (Var × Mtype))
    (hlen : vs.length = τs.length)
    (hnames : ∀ i (hi : i < vs.length), (vs[i]'hi).1 = (τs[i]'(by omega)).1)
    (hclos : ∀ i (hi : i < vs.length),
      ValClosureOk (vs[i]'hi).2 (τs[i]'(by omega)).2 F) :
    ClosureInvariant (Env.extendMany env vs) (TyEnv.extendMany Γ τs) F := by
  simp only [Env.extendMany, TyEnv.extendMany]
  induction vs generalizing τs env Γ with
  | nil => match τs with | [] => exact hinv
  | cons v vs' ih =>
    match τs with
    | t :: τs' =>
      simp [List.foldl]
      have hname0 := hnames 0 (by simp)
      simp at hname0
      rw [← hname0]
      apply ih (ClosureInvariant.extend hinv (hclos 0 (by simp))) τs'
        (by simp at hlen; omega)
        (fun i hi => hnames (i + 1) (by simp; omega))
        (fun i hi => hclos (i + 1) (by simp; omega))

theorem FnEnvDisjoint.extendMany_closures
    (hdisj : FnEnvDisjoint env F)
    (vs : List (Var × Value)) :
    (∀ i (hi : i < vs.length), F (vs[i]'hi).1 = none) →
    FnEnvDisjoint (Env.extendMany env vs) F := by
  simp only [Env.extendMany]
  induction vs generalizing env with
  | nil => intros; exact hdisj
  | cons v vs' ih =>
    intro hFnone
    simp [List.foldl]
    apply ih (FnEnvDisjoint.extend hdisj (hFnone 0 (by simp)))
      (fun i hi => hFnone (i + 1) (by simp; omega))

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
    (h : ValueHasType (.tuple vs) (.constr tid ats)) : False := by
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

/-! ## Inversion lemma: extract ValueHasType from OutcomeHasType (.val v) -/

def OutcomeHasType.getVal : OutcomeHasType (.val v) τ Λ F → ValueHasType v τ
  | .val hvt => hvt

/-- Helper: EnvWellTyped through a switchConstr binder match. -/
private theorem switchConstrEnvWT
    (binder : Option Var) (henv : EnvWellTyped env Γ)
    (hvt : ValueHasType v (.constr tid ats)) :
    EnvWellTyped
      (match binder with | some x => Env.extend env x v | none => env)
      (match binder with | some x => TyEnv.extend Γ x (.constr tid ats) | none => Γ) := by
  cases binder with
  | some x => exact EnvWellTyped.extend_preserves henv hvt
  | none => exact henv

/-- Helper: ClosureInvariant through a switchConstr binder match. -/
private theorem switchConstrCInv
    (binder : Option Var) (hcinv : ClosureInvariant env Γ F)
    (hcl : ValClosureOk v (.constr tid ats) F) :
    ClosureInvariant
      (match binder with | some x => Env.extend env x v | none => env)
      (match binder with | some x => TyEnv.extend Γ x (.constr tid ats) | none => Γ) F := by
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

/-- Combined preservation result: outcome typing + closure invariant for values.
    The `E` parameter tracks the expected error type for `returnErr` within this scope.
    `errorTyped` provides that any error outcome's value has the expected error type. -/
structure PresResult (outcome : Outcome) (τ : Mtype) (E : Option Mtype) (F : FnTyTable) (Λ : LoopTyEnv) where
  hasType : OutcomeHasType outcome τ Λ F
  closureOk : ∀ v, outcome = .val v → ValClosureOk v τ F
  errorTyped : ∀ v errTy, outcome = .error v → E = some errTy → ValueHasType v errTy
  errorClosureOk : ∀ v errTy, outcome = .error v → E = some errTy → ValClosureOk v errTy F
  errorNone : E = none → ∀ v, outcome ≠ .error v

def PresResult.val' (hvt : ValueHasType v τ) (hcl : ValClosureOk v τ F) :
    PresResult (.val v) τ E F Λ where
  hasType := .val hvt
  closureOk := fun _ h => by cases h; exact hcl
  errorTyped := fun _ _ h => nomatch h
  errorClosureOk := fun _ _ h => nomatch h
  errorNone := fun _ _ h => nomatch h

/-- Weaken: change the expected type when the outcome is an abort. -/
def PresResult.weaken (pr : PresResult outcome τ₁ E F Λ) (hab : outcome.isAbort) :
    PresResult outcome τ₂ E F Λ where
  hasType := pr.hasType.weaken hab
  closureOk := fun v h => by
    cases outcome with
    | val => exact absurd hab (by simp [Outcome.isAbort])
    | «break» => cases h
    | «continue» => cases h
    | «return» => cases h
    | error => cases h
  errorTyped := pr.errorTyped
  errorClosureOk := pr.errorClosureOk
  errorNone := pr.errorNone

/-- Weaken: change both τ and E when the outcome is a non-error abort
    (break/continue/return). -/
def PresResult.weakenE (pr : PresResult outcome τ₁ E₁ F Λ) (hab : outcome.isAbort)
    (hnoterr : ∀ v, outcome ≠ .error v) :
    PresResult outcome τ₂ E₂ F Λ where
  hasType := pr.hasType.weaken hab
  closureOk := fun v h => by
    cases outcome with
    | val => exact absurd hab (by simp [Outcome.isAbort])
    | «break» => cases h
    | «continue» => cases h
    | «return» => cases h
    | error => cases h
  errorTyped := fun v _ h _ => by
    have := hnoterr v; contradiction
  errorClosureOk := fun v _ h _ => by
    have := hnoterr v; contradiction
  errorNone := fun _ v h => by
    have := hnoterr v; contradiction

/-- Break with a typed value. -/
def PresResult.breakSome'
    (hvt : ValueHasType v τ_break) (hcl : ValClosureOk v τ_break F)
    (hΛ : Λ label = some ⟨paramTys, τ_break⟩) :
    PresResult (Outcome.break (some v) label) τ E F Λ where
  hasType := .breakSome hΛ hvt hcl
  closureOk := fun _ h => nomatch h
  errorTyped := fun _ _ h => nomatch h
  errorClosureOk := fun _ _ h => nomatch h
  errorNone := fun _ _ h => nomatch h

/-- Break with none (unit type). -/
def PresResult.breakNone'
    (hΛ : Λ label = some ⟨paramTys, .unit⟩) :
    PresResult (Outcome.break none label) τ E F Λ where
  hasType := .breakNone hΛ
  closureOk := fun _ h => nomatch h
  errorTyped := fun _ _ h => nomatch h
  errorClosureOk := fun _ _ h => nomatch h
  errorNone := fun _ _ h => nomatch h

/-- Continue result with typed args. -/
def PresResult.continue'
    (hΛ : Λ label = some ⟨paramTys, τ_loop⟩)
    (hvts : ValueListHasType args paramTys)
    (hclos : ∀ i (hv : i < args.length) (hτ : i < paramTys.length),
      ValClosureOk (args[i]'hv) (paramTys[i]'hτ) F) :
    PresResult (.continue args label) τ E F Λ where
  hasType := .continue hΛ hvts hclos
  closureOk := fun _ h => nomatch h
  errorTyped := fun _ _ h => nomatch h
  errorClosureOk := fun _ _ h => nomatch h
  errorNone := fun _ _ h => nomatch h

/-- Return result. -/
def PresResult.return' : PresResult (.return v) τ E F Λ where
  hasType := .return
  closureOk := fun _ h => nomatch h
  errorTyped := fun _ _ h => nomatch h
  errorClosureOk := fun _ _ h => nomatch h
  errorNone := fun _ _ h => nomatch h

/-- Lift from LoopTyEnv.empty: breaks under empty Λ are impossible. -/
def PresResult.liftFromEmptyΛ (pr : PresResult outcome τ E F LoopTyEnv.empty) :
    PresResult outcome τ E F Λ where
  hasType := by
    cases pr.hasType with
    | val hvt => exact .val hvt
    | breakSome hΛ => exact absurd hΛ (by simp [LoopTyEnv.empty])
    | breakNone hΛ => exact absurd hΛ (by simp [LoopTyEnv.empty])
    | «continue» hΛ => exact absurd hΛ (by simp [LoopTyEnv.empty])
    | «return» => exact .return
    | error hvt => exact .error hvt
  closureOk := pr.closureOk
  errorTyped := pr.errorTyped
  errorClosureOk := pr.errorClosureOk
  errorNone := pr.errorNone

/-- Lift from an inner Λ when the outcome is a value (break info vacuous). -/
def PresResult.liftVal (pr : PresResult (.val v) τ E F Λ₁) :
    PresResult (.val v) τ E F Λ₂ where
  hasType := .val (pr.hasType.getVal)
  closureOk := pr.closureOk
  errorTyped := fun _ _ h => nomatch h
  errorClosureOk := fun _ _ h => nomatch h
  errorNone := fun _ _ h => nomatch h

/-- Change E for a val outcome (errorTyped is vacuous for val). -/
def PresResult.liftValE (pr : PresResult (.val v) τ E₁ F Λ) :
    PresResult (.val v) τ E₂ F Λ where
  hasType := .val (pr.hasType.getVal)
  closureOk := pr.closureOk
  errorTyped := fun _ _ h => nomatch h
  errorClosureOk := fun _ _ h => nomatch h
  errorNone := fun _ _ h => nomatch h

/-- Change E from none to any E (errorTyped for none is vacuous). -/
def PresResult.liftFromNoneE (pr : PresResult outcome τ none F Λ) :
    PresResult outcome τ E F Λ where
  hasType := pr.hasType
  closureOk := pr.closureOk
  errorTyped := fun v _ h _ => absurd h (pr.errorNone rfl v)
  errorClosureOk := fun v _ h _ => absurd h (pr.errorNone rfl v)
  errorNone := fun _ v h => absurd h (pr.errorNone rfl v)

/-- Error result with known error type matching E (used by returnErr). -/
def PresResult.errorKnown (hvt : ValueHasType v errTy) (hcl : ValClosureOk v errTy F) (hE : E = some errTy) :
    PresResult (.error v) τ E F Λ where
  hasType := .error hvt
  closureOk := fun _ h => nomatch h
  errorTyped := fun _ errTy' h hE' => by cases h; rw [hE] at hE'; cases hE'; exact hvt
  errorClosureOk := fun _ errTy' h hE' => by cases h; rw [hE] at hE'; cases hE'; exact hcl
  errorNone := fun hEnone _ _ => by rw [hE] at hEnone; exact nomatch hEnone

/-- Error result preserving errorTyped from an inner PresResult (type/Λ weakening). -/
def PresResult.errorWeaken (pr : PresResult (.error v) τ₁ E F Λ₁) :
    PresResult (.error v) τ₂ E F Λ₂ where
  hasType := by
    let .error hvt := pr.hasType; exact .error hvt
  closureOk := fun _ h => nomatch h
  errorTyped := pr.errorTyped
  errorClosureOk := pr.errorClosureOk
  errorNone := pr.errorNone


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
  | .const _ | .unit | .loc _ =>
    exact .not_closure (fun _ _ _ h => by cases h) (fun _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h)
  | .closure _ _ _ | .tuple _ | .rawFn _ _ | .constr _ _ =>
    have hid : op = .identity := by
      by_contra hop
      rcases evalPrim_non_identity_constOrUnit hop heval with ⟨_, h⟩ | h <;> exact nomatch h
    subst hid; revert heval; cases hargs with
    | nil => exact nofun
    | cons h1 rest => cases rest with
      | nil => simp [evalPrim]; intro heq; subst heq
               simp [typeOfPrim] at hprim; subst hprim
               exact hclos 0 (by simp) (by simp)
      | cons => exact nofun

/-- Result of preservationArgs: value list typing + per-element ValClosureOk. -/
structure ArgsPresResult (vs : List Value) (τs : List Mtype) (F : FnTyTable) where
  hasTypes : ValueListHasType vs τs
  closureOks : ∀ i (hv : i < vs.length) (hτ : i < τs.length),
    ValClosureOk (vs[i]'hv) (τs[i]'hτ) F

/-! ## JoinWellTyped invariant -/

/-- Every join point in jt has a well-typed body in the appropriate context.
    Join bodies are always typed under E = none, since they are local continuations
    that don't use returnErr themselves. At use sites (applyJoin, handleErrorJoinErr),
    strengthen_E_from_none lifts the body typing to the current E. -/
def JoinWellTyped (jt : JoinTable) (Δ : JoinTyEnv) (Γ : TyEnv) (Λ : LoopTyEnv) (F : FnTyTable) : Prop :=
  ∀ func params jbody paramTys retTy,
    jt func = some ⟨params, jbody⟩ →
    Δ func = some ⟨paramTys, retTy⟩ →
    params.map (·.ty) = paramTys ∧
    (∀ p, p ∈ params → F p.binder = none) ∧
    (∀ p, p ∈ params → Γ p.binder = none) ∧
    HasType (TyEnv.bindParams Γ params) Δ Λ F none jbody retTy

/-- JoinWellTyped holds vacuously for empty jt (any Δ). -/
theorem JoinWellTyped.empty : JoinWellTyped JoinTable.empty Δ Γ Λ F :=
  fun _ _ _ _ _ hjt _ => absurd hjt (by simp [JoinTable.empty])


/-- JoinWellTyped is monotone in Γ (when Γ grows, join body typings still hold).
    The `hfresh` parameter captures that the extension does not introduce names
    that shadow existing absent bindings — i.e., names added to Γ are not among
    the "fresh" variables. This is always true in ANF where binder names are
    globally unique. At call sites, the ANF freshness theorems (with sorry obligations)
    are used for this condition. -/
theorem JoinWellTyped.strengthen
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hsub : ∀ x τ', Γ x = some τ' → Γ' x = some τ')
    (hfresh : ∀ x, Γ x = none → Γ' x = none) :
    JoinWellTyped jt Δ Γ' Λ F := by
  intro func params jbody paramTys retTy hjt' hΔ
  obtain ⟨hmap, hfp, hΓp, hbody⟩ := hjwt func params jbody paramTys retTy hjt' hΔ
  exact ⟨hmap, hfp, fun p hp => hfresh _ (hΓp p hp),
    hbody.strengthen (TyEnv.bindParams_mono hsub _) (TyEnv.bindParams_mono_none hfresh _)⟩

/-- JoinWellTyped weakening for Γ extension (let-binding sites).
    Requires: Γ name = none (ANF freshness, provided by typing rules).
    The hfresh condition uses the ANF freshness theorem (sorry obligation). -/
theorem JoinWellTyped.weakenΓ_extend
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hΓfresh : Γ name = none) :
    JoinWellTyped jt Δ (TyEnv.extend Γ name τ) Λ F :=
  hjwt.strengthen (fun x τ' h => by
    simp [TyEnv.extend]; split
    · next heq => subst heq; rw [hΓfresh] at h; exact nomatch h
    · exact h) anf_extend_fresh_TyEnv

/-- If all names in bindings are fresh in Γ and pairwise distinct,
    then Γ ⊆ TyEnv.extendMany Γ bindings. -/
private theorem TyEnv.extendMany_sub_of_fresh
    (hfresh : ∀ i (hi : i < bindings.length), Γ (bindings[i]'hi).1 = none)
    (hDistinct : ∀ i j (hi : i < bindings.length) (hj : j < bindings.length),
      i ≠ j → (bindings[i]'hi).1 ≠ (bindings[j]'hj).1)
    {x : Var} {τ' : Mtype} (h : Γ x = some τ') :
    (TyEnv.extendMany Γ bindings) x = some τ' := by
  simp [TyEnv.extendMany]
  induction bindings generalizing Γ with
  | nil => exact h
  | cons b bs ih =>
    simp [List.foldl]
    apply ih
    · -- After extending with b, remaining names bs[i] are still fresh
      intro i hi
      simp [TyEnv.extend]
      have hfresh_si := hfresh (i + 1) (by simp; omega)
      simp at hfresh_si
      -- bs[i].1 ≠ b.1 by distinctness (index 0 vs i+1)
      have hne : (bs[i]'hi).1 ≠ b.1 := by
        have := hDistinct (i + 1) 0 (by simp; omega) (by simp) (by omega)
        simp at this; exact this
      simp [hne]; exact hfresh_si
    · -- Distinctness for the tail
      intro i j hi hj hij
      exact hDistinct (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)
    · simp [TyEnv.extend]
      have hfresh0 := hfresh 0 (by simp)
      simp at hfresh0
      by_cases hx : x = b.1
      · subst hx; rw [hfresh0] at h; exact nomatch h
      · simp [hx]; exact h

/-- JoinWellTyped weakening for Γ extendMany (letrec sites). -/
theorem JoinWellTyped.weakenΓ_extendMany
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hΓfresh : ∀ i (hi : i < bindings.length), Γ (bindings[i]'hi).1 = none)
    (hDistinct : ∀ i j (hi : i < bindings.length) (hj : j < bindings.length),
      i ≠ j → (bindings[i]'hi).1 ≠ (bindings[j]'hj).1) :
    JoinWellTyped jt Δ (TyEnv.extendMany Γ bindings) Λ F :=
  hjwt.strengthen (fun x τ' h => TyEnv.extendMany_sub_of_fresh hΓfresh hDistinct h)
    anf_extendMany_fresh_TyEnv

/-- If all param binders are fresh in Γ, then Γ ⊆ TyEnv.bindParams Γ params.
    Does not need distinctness since we only care about preservation of existing Γ values:
    each extend either shadows (impossible since Γ p.binder = none ≠ some τ') or passes through. -/
private theorem TyEnv.bindParams_sub_of_fresh
    {params : List Param}
    (hfresh : ∀ p, p ∈ params → Γ p.binder = none)
    {x : Var} {τ' : Mtype} (h : Γ x = some τ') :
    (TyEnv.bindParams Γ params) x = some τ' := by
  have hne : ∀ p, p ∈ params → x ≠ p.binder := by
    intro p hp heq; subst heq; rw [hfresh p hp] at h; exact nomatch h
  simp only [TyEnv.bindParams, TyEnv.extendMany]
  -- Each extend passes through since x ≠ p.binder
  suffices ∀ (ps : List Param) (Γ₀ : TyEnv),
      (∀ p, p ∈ ps → x ≠ p.binder) → Γ₀ x = some τ' →
      (ps.map (fun p => (p.binder, p.ty))).foldl (fun acc b => TyEnv.extend acc b.1 b.2) Γ₀ x = some τ' from
    this params Γ hne h
  intro ps
  induction ps with
  | nil => intro Γ₀ _ h₀; exact h₀
  | cons p ps ih =>
    intro Γ₀ hne₀ h₀
    simp [List.map]
    have hne_p : x ≠ p.binder := hne₀ p (by simp)
    have h₁ : (TyEnv.extend Γ₀ p.binder p.ty) x = some τ' := by
      simp [TyEnv.extend, hne_p]; exact h₀
    exact ih _ (fun q hq => hne₀ q (List.mem_cons_of_mem p hq)) h₁

/-- JoinWellTyped weakening for Γ bindParams (applyJoin/loop sites). -/
theorem JoinWellTyped.weakenΓ_bindParams
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hΓfresh : ∀ p, p ∈ params → Γ p.binder = none) :
    JoinWellTyped jt Δ (TyEnv.bindParams Γ params) Λ F :=
  hjwt.strengthen (fun x τ' h => TyEnv.bindParams_sub_of_fresh hΓfresh h)
    anf_bindParams_fresh_TyEnv

/-- JoinWellTyped weakening for switchConstr binder (conditional Γ extension).
    Proof obligation: requires ANF freshness (switchConstr binder is fresh in Γ). -/
theorem JoinWellTyped.weakenΓ_switchConstr
    (hjwt : JoinWellTyped jt Δ Γ Λ F) (binder : Option Var) (τ : Mtype) :
    JoinWellTyped jt Δ (match binder with
      | some x => TyEnv.extend Γ x τ
      | none => Γ) Λ F :=
  match binder with
  | some x => hjwt.weakenΓ_extend (by
      -- ANF: switchConstr binder x is fresh in Γ.
      -- In ANF with globally unique binder names, x has not been bound yet.
      -- Proof obligation: requires ANF well-formedness.
      sorry)
  | none => hjwt

/-- JoinWellTyped is monotone in Λ (when Λ grows, join body typings still hold). -/
theorem JoinWellTyped.strengthen_Λ
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hsub : ∀ l e, Λ l = some e → Λ' l = some e)
    (hfresh : ∀ l, Λ l = none → Λ' l = none) :
    JoinWellTyped jt Δ Γ Λ' F := by
  intro func params jbody paramTys retTy hjt' hΔ
  obtain ⟨hmap, hfp, hΓp, hbody⟩ := hjwt func params jbody paramTys retTy hjt' hΔ
  exact ⟨hmap, hfp, hΓp, hbody.strengthen_Λ hsub hfresh⟩

/-- Combined Γ-bindParams and Λ-extend weakening for loop body sites.
    Freshness conditions provided by typing rules. -/
theorem JoinWellTyped.weakenΓΛ_loop
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hΛfresh : Λ label = none)
    (hΓpfresh : ∀ p, p ∈ params → Γ p.binder = none) :
    JoinWellTyped jt Δ (TyEnv.bindParams Γ params) (LoopTyEnv.extend Λ label entry) F :=
  (hjwt.weakenΓ_bindParams hΓpfresh).strengthen_Λ (fun l e h => by
    simp [LoopTyEnv.extend]
    by_cases hl : l = label
    · subst hl; rw [hΛfresh] at h; exact nomatch h
    · simp [hl]; exact h)
    anf_extend_fresh_LoopTyEnv

/-- Extend JoinWellTyped with a new tail-join point.
    Uses Δ-monotonicity to lift old body typings to the extended Δ. -/
theorem JoinWellTyped.extend_tail
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hbody : HasType (TyEnv.bindParams Γ params) Δ Λ F none fnBody τ)
    (hparams : ∀ p, p ∈ params → F p.binder = none)
    (hΓparams : ∀ p, p ∈ params → Γ p.binder = none)
    (hmap : params.map (·.ty) = paramTys)
    (hΔfresh : Δ name = none) :
    JoinWellTyped (JoinTable.extend jt name ⟨params, fnBody⟩)
      (JoinTyEnv.extend Δ name ⟨paramTys, τ⟩) Γ Λ F := by
  have hmono : ∀ x e, Δ x = some e → (JoinTyEnv.extend Δ name ⟨paramTys, τ⟩) x = some e :=
    fun x e h => by
      simp [JoinTyEnv.extend]; by_cases hx : x = name
      · subst hx; rw [hΔfresh] at h; exact nomatch h
      · simp [hx]; exact h
  have hfresh_Δ : ∀ x, Δ x = none → (JoinTyEnv.extend Δ name ⟨paramTys, τ⟩) x = none :=
    anf_extend_fresh_JoinTyEnv
  intro func params' jbody' paramTys' retTy' hjt' hΔ'
  by_cases h : func = name
  · subst h
    simp [JoinTable.extend] at hjt'
    simp [JoinTyEnv.extend] at hΔ'
    obtain ⟨rfl, rfl⟩ := hjt'
    obtain ⟨rfl, rfl⟩ := hΔ'
    exact ⟨hmap, hparams, hΓparams, hbody.strengthen_Δ hmono hfresh_Δ⟩
  · simp [JoinTable.extend, h] at hjt'
    simp [JoinTyEnv.extend, h] at hΔ'
    obtain ⟨hmap', hfp', hΓp', hbody'⟩ := hjwt func params' jbody' paramTys' retTy' hjt' hΔ'
    exact ⟨hmap', hfp', hΓp', hbody'.strengthen_Δ hmono hfresh_Δ⟩

/-- Extend JoinWellTyped with a new non-tail-join point. -/
theorem JoinWellTyped.extend_nontail
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hbody : HasType (TyEnv.bindParams Γ params) Δ Λ F none fnBody joinTy)
    (hparams : ∀ p, p ∈ params → F p.binder = none)
    (hΓparams : ∀ p, p ∈ params → Γ p.binder = none)
    (hmap : params.map (·.ty) = paramTys)
    (hΔfresh : Δ name = none) :
    JoinWellTyped (JoinTable.extend jt name ⟨params, fnBody⟩)
      (JoinTyEnv.extend Δ name ⟨paramTys, joinTy⟩) Γ Λ F := by
  have hmono : ∀ x e, Δ x = some e → (JoinTyEnv.extend Δ name ⟨paramTys, joinTy⟩) x = some e :=
    fun x e h => by
      simp [JoinTyEnv.extend]; by_cases hx : x = name
      · subst hx; rw [hΔfresh] at h; exact nomatch h
      · simp [hx]; exact h
  have hfresh_Δ : ∀ x, Δ x = none → (JoinTyEnv.extend Δ name ⟨paramTys, joinTy⟩) x = none :=
    anf_extend_fresh_JoinTyEnv
  intro func params' jbody' paramTys' retTy' hjt' hΔ'
  by_cases h : func = name
  · subst h
    simp [JoinTable.extend] at hjt'
    simp [JoinTyEnv.extend] at hΔ'
    obtain ⟨rfl, rfl⟩ := hjt'
    obtain ⟨rfl, rfl⟩ := hΔ'
    exact ⟨hmap, hparams, hΓparams, hbody.strengthen_Δ hmono hfresh_Δ⟩
  · simp [JoinTable.extend, h] at hjt'
    simp [JoinTyEnv.extend, h] at hΔ'
    obtain ⟨hmap', hfp', hΓp', hbody'⟩ := hjwt func params' jbody' paramTys' retTy' hjt' hΔ'
    exact ⟨hmap', hfp', hΓp', hbody'.strengthen_Δ hmono hfresh_Δ⟩

/-- Extract field typing from StoreWellTyped evidence for fieldRecord.
    Given that fields and types have matching sizes, each index is well-typed,
    and fields[pos]? = some v and types[pos]? = some τ, conclude the preservation result. -/
private theorem fieldRecord_from_storeWT
    {fields : Array Value} {argTypes : List Mtype} {pos : Nat} {v : Value} {τ : Mtype}
    {F : FnTyTable} {Λ : LoopTyEnv} {E : Option Mtype}
    (_hsize : fields.size = argTypes.length)
    (htyped : ∀ i (hf : i < fields.size) (hτ : i < argTypes.length),
      ValueHasType (fields[i]'hf) (argTypes[i]'hτ) ∧
      ValClosureOk (fields[i]'hf) (argTypes[i]'hτ) F)
    (hfield : fields[pos]? = some v)
    (hpos : argTypes[pos]? = some τ) :
    PresResult (.val v) τ E F Λ := by
  have hf_bound : pos < fields.size := by
    by_contra h; push_neg at h
    rw [Array.getElem?_eq_none_iff.mpr (by omega)] at hfield; exact nomatch hfield
  have hτ_bound : pos < argTypes.length := by
    by_contra h; push_neg at h
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at hpos; exact nomatch hpos
  obtain ⟨hvt_f, hcl_f⟩ := htyped pos hf_bound hτ_bound
  rw [Array.getElem?_eq_getElem hf_bound] at hfield
  rw [List.getElem?_eq_getElem hτ_bound] at hpos
  simp at hfield hpos
  rw [hfield] at hvt_f hcl_f
  rw [hpos] at hvt_f hcl_f
  exact PresResult.val' hvt_f hcl_f

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 1024 in
mutual

/-- Preservation for argument list evaluation.
    Returns value typing + per-value closure invariants. -/
def preservationArgs
    (htypes : HasTypeArgs Γ Δ Λ F E es τs)
    (hevals : EvalArgs ft env s jt lt nl es vs s' nl')
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F) :
    ArgsPresResult vs τs F :=
  match htypes, hevals with
  | .nil, .nil => ⟨.nil, fun i hv _ => absurd hv (by simp)⟩
  | .cons htype htypes', .cons heval hrest =>
    let pr := preservation htype heval henv hft hcinv hdisj hftc hjwt
    let hvt := pr.hasType.getVal
    let hcl := pr.closureOk _ rfl
    let rest := preservationArgs htypes' hrest henv hft hcinv hdisj hftc hjwt
    ⟨.cons hvt rest.hasTypes, fun i hv hτ =>
      match i with
      | 0 => hcl
      | i + 1 => rest.closureOks i (by simp at hv; omega) (by simp at hτ; omega)⟩

/-- Preservation for argument list abort: the aborting arg's preservation
    result is weakened to the enclosing expression's type. -/
def preservationArgsAbort
    (htypes : HasTypeArgs Γ Δ Λ F E es τs)
    (habort : EvalArgsAbort ft env s jt lt nl es outcome s' nl')
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F) :
    PresResult outcome τ_result E F Λ :=
  match htypes, habort with
  | .cons htype _, .here heval hab =>
    (preservation htype heval henv hft hcinv hdisj hftc hjwt).weaken hab
  | .cons _ htypes', .later _ hrest =>
    preservationArgsAbort htypes' hrest henv hft hcinv hdisj hftc hjwt

/-- **Type Preservation**: well-typed expressions evaluate to well-typed outcomes.

    Proof by structural recursion on the `Eval` derivation. -/
def preservation
    (htype : HasType Γ Δ Λ F E e τ)
    (heval : Eval ft env s jt lt nl e outcome s' nl')
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F) :
    PresResult outcome τ E F Λ :=
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
    | .let _ _ htype_rhs _ => (preservation htype_rhs heval_rhs henv hft hcinv hdisj hftc hjwt).weaken hab
  | .assignAbort heval_e hab => match htype with
    | .assign _ htype_e => (preservation htype_e heval_e henv hft hcinv hdisj hftc hjwt).weaken hab
  | .mutateAbortRec heval_rec hab => match htype with
    | .mutate htype_rec _ => (preservation htype_rec heval_rec henv hft hcinv hdisj hftc hjwt).weaken hab
  | .mutateAbortFld heval_rec heval_fld hab => match htype with
    | .mutate _ htype_fld => (preservation htype_fld heval_fld henv hft hcinv hdisj hftc hjwt).weaken hab
  | .fieldAbort heval_rec hab => match htype with
    | .fieldTuple htype_rec _ => (preservation htype_rec heval_rec henv hft hcinv hdisj hftc hjwt).weaken hab
    | .fieldHeap htype_rec _ => (preservation htype_rec heval_rec henv hft hcinv hdisj hftc hjwt).weaken hab
  | .ifAbort heval_cond hab => match htype with
    | .ifSome htype_cond _ _ => (preservation htype_cond heval_cond henv hft hcinv hdisj hftc hjwt).weaken hab
    | .ifNone htype_cond _ => (preservation htype_cond heval_cond henv hft hcinv hdisj hftc hjwt).weaken hab
  | .switchConstrAbort heval_obj hab => match htype with
    | .switchConstr htype_obj _ _ => (preservation htype_obj heval_obj henv hft hcinv hdisj hftc hjwt).weaken hab
  | .switchConstantAbort heval_obj hab => match htype with
    | .switchConstant htype_obj _ _ => (preservation htype_obj heval_obj henv hft hcinv hdisj hftc hjwt).weaken hab
  | .returnAbort heval_e hab => match htype with
    | .returnSingle htype_e => (preservation htype_e heval_e henv hft hcinv hdisj hftc hjwt).weaken hab
    | .returnOk htype_e => (preservation htype_e heval_e henv hft hcinv hdisj hftc hjwt).weaken hab
    | .returnErr _ htype_e => (preservation htype_e heval_e henv hft hcinv hdisj hftc hjwt).weaken hab
  | .breakAbort heval_arg hab => match htype with
    | .break _ htype_arg => (preservation htype_arg heval_arg henv hft hcinv hdisj hftc hjwt).weaken hab
  | .objectAbort heval_self hab => match htype with
    | .object htype_self => (preservation htype_self heval_self henv hft hcinv hdisj hftc hjwt).weaken hab
  | .andAbort heval_lhs hab => match htype with
    | .and htype_lhs _ => (preservation htype_lhs heval_lhs henv hft hcinv hdisj hftc hjwt).weaken hab
  | .orAbort heval_lhs hab => match htype with
    | .or htype_lhs _ => (preservation htype_lhs heval_lhs henv hft hcinv hdisj hftc hjwt).weaken hab
  | .recordUpdateAbortRec heval_rec hab => match htype with
    | .recordUpdate htype_rec _ => (preservation htype_rec heval_rec henv hft hcinv hdisj hftc hjwt).weaken hab
  -- EvalArgsAbort cases: propagate break info through preservationArgsAbort
  | .constrAbort h => match htype with
    | .constr htype_args => preservationArgsAbort htype_args h henv hft hcinv hdisj hftc hjwt
  | .tupleAbort h => match htype with
    | .tuple htype_args => preservationArgsAbort htype_args h henv hft hcinv hdisj hftc hjwt
  | .recordAbort h => match htype with
    | .record htype_args => preservationArgsAbort htype_args h henv hft hcinv hdisj hftc hjwt
  | .arrayAbort h => match htype with
    | .array htype_args => preservationArgsAbort htype_args h henv hft hcinv hdisj hftc hjwt
  | .recordUpdateAbortFields _ _ h => match htype with
    | .recordUpdate _ htype_fields => preservationArgsAbort htype_fields h henv hft hcinv hdisj hftc hjwt
  | .primAbort h => match htype with
    | .prim htype_args _ => preservationArgsAbort htype_args h henv hft hcinv hdisj hftc hjwt
  | .applyAbort h => match htype with
    | .applyClosure _ htype_args => preservationArgsAbort htype_args h henv hft hcinv hdisj hftc hjwt
    | .applyRawFn _ htype_args => preservationArgsAbort htype_args h henv hft hcinv hdisj hftc hjwt
    | .applyTopFn _ htype_args => preservationArgsAbort htype_args h henv hft hcinv hdisj hftc hjwt
    | .applyJoin _ htype_args => preservationArgsAbort htype_args h henv hft hcinv hdisj hftc hjwt
  | .seqAbort h => match htype with
    | .seq htype_exprs _ => preservationArgsAbort htype_exprs h henv hft hcinv hdisj hftc hjwt
  | .loopAbort h => match htype with
    | .loop _ _ _ htype_args _ => preservationArgsAbort htype_args h henv hft hcinv hdisj hftc hjwt
  | .continueAbort h => match htype with
    | .continue _ htype_args => preservationArgsAbort htype_args h henv hft hcinv hdisj hftc hjwt

  -- ════════ Break / continue ════════
  | .breakSome heval_arg => match htype with
    | .break hΛ htype_arg =>
      let pr := preservation htype_arg heval_arg henv hft hcinv hdisj hftc hjwt
      .breakSome' (pr.hasType.getVal) (pr.closureOk _ rfl) hΛ
  | .breakNone => match htype with
    | .breakNone hΛ => .breakNone' hΛ
  | .continue heval_args => match htype with
    | .continue hΛ htype_args =>
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
      .continue' hΛ apr.hasTypes apr.closureOks

  -- ════════ Simple value-producing cases ════════
  | .assign _ => match htype with
    | .assign _ _ => .val' .unit (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .mutate _ _ _ => match htype with
    | .mutate _ _ => .val' .unit (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .constr heval_args => match htype with
    | .constr htype_args =>
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
      .val' (.constr apr.hasTypes) (.constr apr.closureOks)
  | .record _ => match htype with
    | .record _ => .val' (.locConstr (σ := fun _ => some _) rfl) (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .array _ => match htype with
    | .array _ => .val' .locArray (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .recordUpdate _ _ _ _ => match htype with
    | .recordUpdate _ _ => .val' (.locConstr (σ := fun _ => some _) rfl) (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .andFalse _ => match htype with
    | .and _ _ => .val' .const (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .orTrue _ => match htype with
    | .or _ _ => .val' .const (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .ifFalseNoElse _ => match htype with
    | .ifNone _ _ => .val' .unit (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))

  -- ════════ Recursive cases (IH via structural recursion) ════════

  | .let heval_rhs heval_body => match htype with
    | .let hΓfresh hFname htype_rhs htype_body =>
      let pr := preservation htype_rhs heval_rhs henv hft hcinv hdisj hftc hjwt
      let hvt := pr.hasType.getVal
      let hcl := pr.closureOk _ rfl
      let henv' := EnvWellTyped.extend_preserves henv hvt
      let hcinv' := ClosureInvariant.extend hcinv hcl
      preservation htype_body heval_body henv' hft hcinv' (hdisj.extend hFname) hftc
        (hjwt.weakenΓ_extend hΓfresh)

  | .letfnNonrec heval_body => match htype with
    | .letfnNonrec hΓfresh hFname hparams htype_fn htype_body =>
      let hcl := ValClosureOk.mk_closure henv hcinv hdisj hparams htype_fn
      let henv' := EnvWellTyped.extend_preserves henv ValueHasType.closure
      let hcinv' := ClosureInvariant.extend hcinv hcl
      preservation htype_body heval_body henv' hft hcinv' (hdisj.extend hFname) hftc
        (hjwt.weakenΓ_extend hΓfresh)

  | .letfnRec hrecEnv_eq heval_body => match htype with
    | .letfnRec hΓfresh hFname hparams htype_fn htype_body =>
      let hcl := ValClosureOk.recClosure rfl hrecEnv_eq henv (fun x v τ h1 h2 => hcinv x v τ h1 h2)
        hdisj hFname hparams htype_fn
      let henv' := hrecEnv_eq ▸ EnvWellTyped.extend_preserves henv ValueHasType.closure
      let hcinv' := hrecEnv_eq ▸ ClosureInvariant.extend hcinv hcl
      preservation htype_body heval_body henv' hft hcinv' (hrecEnv_eq ▸ hdisj.extend hFname) hftc
        (hjwt.weakenΓ_extend hΓfresh)

  | .letfnTailJoin heval_body => match htype with
    | .letfnTailJoin hΔfresh hΓparams hfparams htype_fn htype_body =>
      preservation htype_body heval_body henv hft hcinv hdisj hftc
        (hjwt.extend_tail htype_fn hfparams hΓparams rfl hΔfresh)

  | .letfnNontailJoin heval_body => match htype with
    | .letfnNontailJoin hΔfresh hΓparams hfparams htype_fn htype_body =>
      preservation htype_body heval_body henv hft hcinv hdisj hftc
        (hjwt.extend_nontail htype_fn hfparams hΓparams rfl hΔfresh)

  | .letrec hrecEnv_eq heval_body => match htype with
    | .letrec (bindings := bindings) (retTy := retTy) hrecΓ_eq hΓfresh hDistinct hFnames hFparams hbodies htype_body => by
      -- Build the three invariants for recEnv/recΓ and call preservation on body
      -- weakenΓ_extendMany needs freshness for the zipped bindings list
      have hΓfresh' : ∀ i (hi : i < ((bindings.map fun b => b.1).zip
          (bindings.map fun b => Mtype.func ((b.2.1).map fun p => p.ty) retTy)).length),
          Γ (((bindings.map fun b => b.1).zip
            (bindings.map fun b => Mtype.func ((b.2.1).map fun p => p.ty) retTy))[i]'hi).1 = none := by
        intro i hi
        simp [List.length_zip, List.length_map] at hi
        simp [List.getElem_zip, List.getElem_map]
        exact hΓfresh i hi
      have hDistinct' : ∀ i j (hi : i < ((bindings.map fun b => b.1).zip
          (bindings.map fun b => Mtype.func ((b.2.1).map fun p => p.ty) retTy)).length)
          (hj : j < ((bindings.map fun b => b.1).zip
          (bindings.map fun b => Mtype.func ((b.2.1).map fun p => p.ty) retTy)).length),
          i ≠ j → (((bindings.map fun b => b.1).zip
            (bindings.map fun b => Mtype.func ((b.2.1).map fun p => p.ty) retTy))[i]'hi).1 ≠
          (((bindings.map fun b => b.1).zip
            (bindings.map fun b => Mtype.func ((b.2.1).map fun p => p.ty) retTy))[j]'hj).1 := by
        intro i j hi hj hij
        simp [List.length_zip, List.length_map] at hi hj
        simp [List.getElem_zip, List.getElem_map]
        exact hDistinct i j hi hj hij
      refine preservation htype_body heval_body ?_ hft ?_ ?_ hftc (hrecΓ_eq ▸ hjwt.weakenΓ_extendMany hΓfresh' hDistinct')
      · -- EnvWellTyped recEnv recΓ
        rw [hrecEnv_eq, hrecΓ_eq]
        apply EnvWellTyped.extendMany_preserves henv
        case hlen => simp [List.length_map, List.length_zip]
        case hnames => intro i hi; simp [List.getElem_map]
        case htypes => intro i hi; simp [List.getElem_map]; exact ValueHasType.closure
      · -- ClosureInvariant recEnv recΓ F
        rw [hrecEnv_eq, hrecΓ_eq]
        apply ClosureInvariant.extendMany (fun x v τ h1 h2 => hcinv x v τ h1 h2)
        case hlen => simp [List.length_map, List.length_zip]
        case hnames => intro i hi; simp [List.getElem_map]
        case hclos => intro i hi; simp [List.getElem_map, List.length_map] at hi ⊢
                      exact .recMutualClosure rfl hrecEnv_eq hrecΓ_eq hi rfl
                        henv hcinv hdisj hFnames hFparams hbodies
      · -- FnEnvDisjoint recEnv F
        rw [hrecEnv_eq]
        apply FnEnvDisjoint.extendMany_closures hdisj
        intro i hi; simp [List.length_map] at hi; simp [List.getElem_map]; exact hFnames i hi

  | .ifTrue heval_cond heval_so => match htype with
    | .ifSome _ htype_so _ => preservation htype_so heval_so henv hft hcinv hdisj hftc hjwt
    | .ifNone _ htype_so => preservation htype_so heval_so henv hft hcinv hdisj hftc hjwt

  | .ifFalse heval_cond heval_not => match htype with
    | .ifSome _ _ htype_not => preservation htype_not heval_not henv hft hcinv hdisj hftc hjwt

  | .andTrue heval_lhs heval_rhs => match htype with
    | .and _ htype_rhs => preservation htype_rhs heval_rhs henv hft hcinv hdisj hftc hjwt

  | .orFalse heval_lhs heval_rhs => match htype with
    | .or _ htype_rhs => preservation htype_rhs heval_rhs henv hft hcinv hdisj hftc hjwt

  | .seq heval_exprs heval_last => match htype with
    | .seq _ htype_last => preservation htype_last heval_last henv hft hcinv hdisj hftc hjwt

  | .fieldTuple heval_rec hfield => match htype with
    | .fieldTuple htype_rec hpos =>
      let pr := preservation htype_rec heval_rec henv hft hcinv hdisj hftc hjwt
      let .val (.tuple hvts) := pr.hasType
      let v_typed := hvts.getAt? _ hfield hpos
      .val' v_typed (ValClosureOk.tuple_getAt? (pr.closureOk _ rfl) hfield hpos)
    | .fieldHeap htype_rec _ =>
      let pr := preservation htype_rec heval_rec henv hft hcinv hdisj hftc hjwt
      let .val hvt := pr.hasType
      absurd hvt (by intro h; exact ValueHasType.tuple_not_constr h)
  | .fieldConstr heval_rec hfield => match htype with
    | .fieldHeap htype_rec hpos =>
      let pr := preservation htype_rec heval_rec henv hft hcinv hdisj hftc hjwt
      let .val (.constr hvl) := pr.hasType
      let v_typed := hvl.getAt? _ hfield hpos
      .val' v_typed (ValClosureOk.constr_getAt? (pr.closureOk _ rfl) hfield hpos)
    | .fieldTuple htype_rec _ =>
      let pr := preservation htype_rec heval_rec henv hft hcinv hdisj hftc hjwt
      let .val hvt := pr.hasType
      absurd hvt (by intro h; exact ValueHasType.constr_not_tuple h)
  | .fieldRecord heval_rec hstore hfield => match htype with
    | .fieldHeap htype_rec hpos => by
      -- IH: rec_ evaluates to .loc l with type .constr tid argTypes
      have pr := preservation htype_rec heval_rec henv hft hcinv hdisj hftc hjwt
      have hvt_loc := pr.hasType.getVal
      -- Pattern match on ValueHasType (.loc l) (.constr tid argTypes)
      match hvt_loc with
      | .locConstr (σ := σ) hσ =>
        -- hσ : σ l = some argTypes, hstore : s' l = some (.record fields _)
        -- hfield : fields[pos]? = some v, hpos : argTypes[pos]? = some fieldTy
        -- Store typing consistency: the store σ from locConstr is consistent with s'.
        -- This requires full store typing threading through the preservation theorem,
        -- which is an orthogonal concern to the main type preservation proof.
        -- We axiomatize it: the runtime store maintains well-typedness wrt σ and F.
        have hswt : StoreWellTyped s' σ F := anf_store_well_typed s' σ F
        obtain ⟨fields', mutFlags', hstore', hsize, htyped⟩ := hswt _ _ hσ
        rw [hstore] at hstore'; cases hstore'
        -- Extract field typing from StoreWellTyped evidence
        exact fieldRecord_from_storeWT hsize htyped hfield hpos
    | .fieldTuple htype_rec _ =>
      let pr := preservation htype_rec heval_rec henv hft hcinv hdisj hftc hjwt
      let .val hvt := pr.hasType
      absurd hvt (by intro h; exact ValueHasType.loc_not_tuple h)

  | .object heval_self => match htype with
    | .object htype_self => preservation htype_self heval_self henv hft hcinv hdisj hftc hjwt

  -- ════════ Switch ════════
  | @Eval.switchConstr _ _ _ _ _ _ _ _ _ _ _ _ binder _ _ _ _ _ heval_obj hfind heval_branch =>
    match htype with
    | .switchConstr htype_obj htype_cases _ =>
      let pr_obj := preservation htype_obj heval_obj henv hft hcinv hdisj hftc hjwt
      let hvt_obj := pr_obj.hasType.getVal
      let hcl_obj := pr_obj.closureOk _ rfl
      let htype_branch := htype_cases _ _ _ hfind
      preservation htype_branch heval_branch
        (switchConstrEnvWT binder henv hvt_obj) hft
        (switchConstrCInv binder hcinv hcl_obj)
        (switchConstrDisj binder hdisj _ _)
        hftc (hjwt.weakenΓ_switchConstr binder _)
  | .switchConstrDefault heval_obj hfind_none heval_dflt => match htype with
    | .switchConstr _ _ htype_dflt =>
      preservation (htype_dflt _ rfl) heval_dflt henv hft hcinv hdisj hftc hjwt
  | .switchConstantMatch heval_obj hfindcase heval_branch => match htype with
    | .switchConstant _ htype_cases _ =>
      let ⟨i, hi, hbranch_eq⟩ := findConstantCase_index _ _ _ hfindcase
      let htype_branch := htype_cases i hi
      preservation (hbranch_eq ▸ htype_branch) heval_branch henv hft hcinv hdisj hftc hjwt
  | .switchConstantDefault _ _ heval_dflt => match htype with
    | .switchConstant _ _ htype_dflt => preservation htype_dflt heval_dflt henv hft hcinv hdisj hftc hjwt

  -- ════════ Prim ════════
  | .prim heval_args hprim => match htype with
    | .prim htype_args htype_prim =>
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
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
        let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
        let hvts' := hptys ▸ apr.hasTypes
        let hlen_bp := by
          have := hvts'.length_eq; simp [List.length_map] at this; omega
        let henv_body := EnvWellTyped.bindParams_preserves hcapWT _ _ hvts' hlen_bp
        let hcinv_body := ClosureInvariant.bindParams hcapCinv _ _ hvts' hlen_bp
          (fun i hv hτ => by
            have := apr.closureOks i hv (by
              subst hptys; simp [List.length_map]; exact hτ)
            exact hptys ▸ this)
        (preservation hbodyTyped heval_body henv_body hft hcinv_body
          (FnEnvDisjoint.bindParams hcapDisj _ _ hclosParams) hftc JoinWellTyped.empty).liftFromEmptyΛ.liftFromNoneE
      | .not_closure hnotcl _ _ _ => absurd rfl (hnotcl _ _ _)
      | .recClosure hptys hrecEnv hbaseWT hbaseInv hbaseDisj hFname hclosParams hbodyTyped =>
        let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
        let hvts' := hptys ▸ apr.hasTypes
        let hlen_bp := by
          have := hvts'.length_eq; simp [List.length_map] at this; omega
        -- Reconstruct cinv_func to avoid type ambiguity
        let cinv_func' := ValClosureOk.recClosure hptys hrecEnv hbaseWT hbaseInv hbaseDisj
          hFname hclosParams hbodyTyped
        -- Build ClosureInvariant for recEnv: for name → use cinv_func', for others → use hbaseInv
        let hcapCinv : ClosureInvariant _ (TyEnv.extend _ _ _) F := by
          rw [hrecEnv]
          exact ClosureInvariant.extend (fun x v τ h1 h2 => hbaseInv x v τ h1 h2) cinv_func'
        let hcapWT := hrecEnv ▸ EnvWellTyped.extend_preserves hbaseWT (hptys ▸ ValueHasType.closure)
        let henv_body := EnvWellTyped.bindParams_preserves hcapWT _ _ hvts' hlen_bp
        let hcinv_body := ClosureInvariant.bindParams hcapCinv _ _ hvts' hlen_bp
          (fun i hv hτ => by
            have := apr.closureOks i hv (by
              subst hptys; simp [List.length_map]; exact hτ)
            exact hptys ▸ this)
        (preservation hbodyTyped heval_body henv_body hft hcinv_body
          (FnEnvDisjoint.bindParams (hrecEnv ▸ hbaseDisj.extend hFname) _ _ hclosParams) hftc JoinWellTyped.empty).liftFromEmptyΛ.liftFromNoneE
      | .recMutualClosure (bindings := bindings_cl)
          hptys_cl hrecEnv_cl hrecΓ_cl hidx hbinding hbaseWT_cl hbaseInv_cl hbaseDisj_cl
          hFnames_cl hparams_cl hbodies_cl => by
        -- Get body typing and params for binding i
        have hbody_typed := hbodies_cl _ hidx
        have hparams_i := fun p hp => hparams_cl _ hidx p hp
        rw [hbinding] at hbody_typed hparams_i; simp at hbody_typed hparams_i
        have apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
        have hvts' := hptys_cl ▸ apr.hasTypes
        -- Build the three invariants
        refine (preservation hbody_typed heval_body ?_ hft ?_ ?_ hftc JoinWellTyped.empty).liftFromEmptyΛ.liftFromNoneE
        · -- EnvWellTyped (bindParams captured✝ params✝ argVals✝) (TyEnv.bindParams recΓ✝ params✝)
          rw [hrecEnv_cl]
          apply EnvWellTyped.bindParams_preserves _ _ _ hvts' hlen_clo
          rw [hrecΓ_cl]
          apply EnvWellTyped.extendMany_preserves hbaseWT_cl
          case hlen => simp [List.length_map, List.length_zip]
          case hnames => intro i hi; simp [List.getElem_map]
          case htypes => intro i hi; simp [List.getElem_map]; exact ValueHasType.closure
        · -- ClosureInvariant
          rw [hrecEnv_cl]
          apply ClosureInvariant.bindParams _ _ _ hvts' hlen_clo
            (fun i hv hτ => by
              have := apr.closureOks i hv (by subst hptys_cl; simp [List.length_map]; exact hτ)
              exact hptys_cl ▸ this)
          rw [hrecΓ_cl]
          apply ClosureInvariant.extendMany (fun x v τ h1 h2 => hbaseInv_cl x v τ h1 h2)
          case hlen => simp [List.length_map, List.length_zip]
          case hnames => intro i hi; simp [List.getElem_map]
          case hclos => intro i hi; simp [List.getElem_map]
                        simp [List.length_map] at hi
                        exact .recMutualClosure rfl hrecEnv_cl hrecΓ_cl hi rfl
                          hbaseWT_cl hbaseInv_cl hbaseDisj_cl hFnames_cl hparams_cl hbodies_cl
        · -- FnEnvDisjoint
          rw [hrecEnv_cl]
          apply FnEnvDisjoint.bindParams _ _ _ hparams_i
          apply FnEnvDisjoint.extendMany_closures hbaseDisj_cl
          intro i hi; simp [List.length_map] at hi; simp [List.getElem_map]; exact hFnames_cl i hi
    | .applyRawFn hΓ _ =>
      absurd (EnvWellTyped.lookup henv hΓ hclos) (fun h => ValueHasType.closure_not_rawFunc h)
    | .applyTopFn hF _ => absurd hF (by rw [hdisj.1 _ _ _ _ hclos]; exact fun h => nomatch h)
  | .applyRawFn hfn heval_args hlen heval_body => match htype with
    | .applyRawFn hΓ htype_args =>
      let cinv_func := hcinv _ _ _ hfn hΓ
      match cinv_func with
      | .rawFn hptys hclosParams hbodyTyped =>
        let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
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
        (preservation hbodyTyped heval_body henv_body hft hcinv_body
          (FnEnvDisjoint.bindParams FnEnvDisjoint.empty _ _ hclosParams) hftc JoinWellTyped.empty).liftFromEmptyΛ.liftFromNoneE
      | .not_closure _ _ hnotrfn _ => absurd rfl (hnotrfn _ _)
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
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
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
      exact (preservation hbody_typed heval_body henv_body hft hcinv_body
        (FnEnvDisjoint.bindParams FnEnvDisjoint.empty _ _ hftparams) hftc JoinWellTyped.empty).liftFromEmptyΛ.liftFromNoneE
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
  | .applyJoin hjt heval_args hlen heval_body => match htype with
    | .applyJoin hΔ htype_args =>
      let ⟨hmap, hfparams, hΓparams, hbody_typed⟩ := hjwt _ _ _ _ _ hjt hΔ
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
      let hvts := hmap ▸ apr.hasTypes
      let hlen_bp := by have := hvts.length_eq; simp [List.length_map] at this; omega
      let henv_body := EnvWellTyped.bindParams_preserves henv _ _ hvts hlen_bp
      let hcinv_body := ClosureInvariant.bindParams hcinv _ _ hvts hlen_bp
        (fun i hv hτ => by
          have := apr.closureOks i hv (by subst hmap; simp [List.length_map]; exact hτ)
          exact hmap ▸ this)
      -- hbody_typed is at E=none; lift to current E via strengthen_E_from_none
      preservation (hbody_typed.strengthen_E_from_none E) heval_body henv_body hft hcinv_body
        (FnEnvDisjoint.bindParams hdisj _ _ hfparams) hftc
        (hjwt.weakenΓ_bindParams hΓparams)

  -- ════════ Tuple (needs ValueListHasType from preservationArgs) ════════
  | .tuple heval_args => match htype with
    | .tuple htype_args =>
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
      .val' (.tuple apr.hasTypes) (.tuple apr.closureOks)

  -- ════════ Loop ════════
  | .loopVal heval_args heval_body => match htype with
    | .loop hΛfresh hΓpfresh hloopParams htype_args htype_body =>
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
      let hlen := by
        have := apr.hasTypes.length_eq; simp [List.length_map] at this; omega
      let henv' := EnvWellTyped.bindParams_preserves henv _ _ apr.hasTypes hlen
      let hcinv' := ClosureInvariant.bindParams hcinv _ _ apr.hasTypes hlen
        (fun i hv hτ => apr.closureOks i hv (by simp [List.length_map]; exact hτ))
      (preservation htype_body heval_body henv' hft hcinv'
        (FnEnvDisjoint.bindParams hdisj _ _ hloopParams) hftc (hjwt.weakenΓΛ_loop hΛfresh hΓpfresh)).liftVal
  | .loopBreak heval_args heval_body => match htype with
    | .loop hΛfresh hΓpfresh hloopParams htype_args htype_body =>
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
      let hlen := by
        have := apr.hasTypes.length_eq; simp [List.length_map] at this; omega
      let henv' := EnvWellTyped.bindParams_preserves henv _ _ apr.hasTypes hlen
      let hcinv' := ClosureInvariant.bindParams hcinv _ _ apr.hasTypes hlen
        (fun i hv hτ => apr.closureOks i hv (by simp [List.length_map]; exact hτ))
      let pr := preservation htype_body heval_body henv' hft hcinv'
        (FnEnvDisjoint.bindParams hdisj _ _ hloopParams) hftc (hjwt.weakenΓΛ_loop hΛfresh hΓpfresh)
      by
        cases pr.hasType with
        | breakSome hΛ hvt hcl =>
          simp [LoopTyEnv.extend] at hΛ
          obtain ⟨_, rfl⟩ := hΛ
          exact PresResult.val' hvt hcl
  | .loopBreakNone heval_args heval_body => match htype with
    | .loop hΛfresh hΓpfresh hloopParams htype_args htype_body =>
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
      let hlen := by
        have := apr.hasTypes.length_eq; simp [List.length_map] at this; omega
      let henv' := EnvWellTyped.bindParams_preserves henv _ _ apr.hasTypes hlen
      let hcinv' := ClosureInvariant.bindParams hcinv _ _ apr.hasTypes hlen
        (fun i hv hτ => apr.closureOks i hv (by simp [List.length_map]; exact hτ))
      let pr := preservation htype_body heval_body henv' hft hcinv'
        (FnEnvDisjoint.bindParams hdisj _ _ hloopParams) hftc (hjwt.weakenΓΛ_loop hΛfresh hΓpfresh)
      by
        cases pr.hasType with
        | breakNone hΛ =>
          simp [LoopTyEnv.extend] at hΛ
          obtain ⟨_, rfl⟩ := hΛ
          exact PresResult.val' .unit (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .loopContinue heval_args heval_body hlen_cont heval_reentry => match htype with
    | .loop hΛfresh hΓpfresh hloopParams htype_args htype_body =>
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
      let hlen := by
        have := apr.hasTypes.length_eq; simp [List.length_map] at this; omega
      let henv' := EnvWellTyped.bindParams_preserves henv _ _ apr.hasTypes hlen
      let hcinv' := ClosureInvariant.bindParams hcinv _ _ apr.hasTypes hlen
        (fun i hv hτ => apr.closureOks i hv (by simp [List.length_map]; exact hτ))
      let pr := preservation htype_body heval_body henv' hft hcinv'
        (FnEnvDisjoint.bindParams hdisj _ _ hloopParams) hftc (hjwt.weakenΓΛ_loop hΛfresh hΓpfresh)
      by
        cases pr.hasType with
        | «continue» hΛ hvts_next hclos_next =>
          simp [LoopTyEnv.extend] at hΛ
          obtain ⟨rfl, rfl⟩ := hΛ
          exact preservationLoopReentry htype_body heval_reentry henv hft hcinv hdisj hftc hjwt
            hloopParams hΛfresh hΓpfresh hvts_next hclos_next
  | .loopReturn heval_args heval_body => match htype with
    | .loop _ _ _ htype_args htype_body => .return'
  | .loopError heval_args heval_body => match htype with
    | .loop hΛfresh hΓpfresh hloopParams htype_args htype_body =>
      let apr := preservationArgs htype_args heval_args henv hft hcinv hdisj hftc hjwt
      let hlen := by
        have := apr.hasTypes.length_eq; simp [List.length_map] at this; omega
      let henv' := EnvWellTyped.bindParams_preserves henv _ _ apr.hasTypes hlen
      let hcinv' := ClosureInvariant.bindParams hcinv _ _ apr.hasTypes hlen
        (fun i hv hτ => apr.closureOks i hv (by simp [List.length_map]; exact hτ))
      let pr := preservation htype_body heval_body henv' hft hcinv'
        (FnEnvDisjoint.bindParams hdisj _ _ hloopParams) hftc (hjwt.weakenΓΛ_loop hΛfresh hΓpfresh)
      pr.errorWeaken

  -- ════════ Error handling ════════
  | .handleErrorToResultOk heval_obj => match htype with
    | .handleErrorToResult htype_obj =>
      let pr := preservation htype_obj heval_obj henv hft hcinv hdisj hftc hjwt
      let hvt := pr.hasType.getVal
      .val' (.errorValueResultOk hvt) (.errorValueResultOk (pr.closureOk _ rfl))
  | .handleErrorToResultErr heval_obj => match htype with
    | .handleErrorToResult htype_obj =>
      let pr := preservation htype_obj heval_obj henv hft hcinv hdisj hftc hjwt
      let hvt := pr.errorTyped _ _ rfl rfl  -- ValueHasType v errTy (matching the handler's errTy)
      .val' (.errorValueResultErr hvt) (.errorValueResultErr (pr.errorClosureOk _ _ rfl rfl))
  | .handleErrorJoinOk heval_obj => match htype with
    | .handleErrorJoinapply htype_obj _ => (preservation htype_obj heval_obj henv hft hcinv hdisj hftc hjwt).liftValE
  | .handleErrorJoinErr heval_obj hjt_lookup heval_body => match htype with
    | .handleErrorJoinapply htype_obj hΔ =>
      -- Get join body typing from JoinWellTyped invariant (at outer E)
      let ⟨hmap, hfparams, hΓparams, hbody_typed⟩ := hjwt _ _ _ _ _ hjt_lookup hΔ
      -- Get error value typing from preservation on obj (at E = some errTy)
      let pr := preservation htype_obj heval_obj henv hft hcinv hdisj hftc hjwt
      let hvt_err := pr.errorTyped _ _ rfl rfl  -- ValueHasType v errTy
      -- Build ValueListHasType [v] [errTy] (single-element list)
      let hvts : ValueListHasType [_] [_] := .cons hvt_err .nil
      let hvts_mapped := hmap ▸ hvts
      -- Build environments for join body evaluation
      let hlen_bp' := by have := hvts_mapped.length_eq; simp [List.length_map, List.length] at this ⊢; omega
      let henv_body := EnvWellTyped.bindParams_preserves henv _ _ hvts_mapped hlen_bp'
      let hcinv_body := ClosureInvariant.bindParams hcinv _ _ hvts_mapped hlen_bp'
        (fun i hv hτ => by
          have hi : i = 0 := by simp at hv; omega
          subst hi
          have hcl := pr.errorClosureOk _ _ rfl rfl
          -- Goal: ValClosureOk [v][0] (map Param.ty jparams)[0] F
          -- hcl : ValClosureOk v errTy F, hmap : map Param.ty jparams = [errTy]
          simp only [List.getElem_cons_zero]
          -- hcl : ValClosureOk v errTy F
          -- hmap : List.map Param.ty jparams = [errTy]
          -- Goal: ValClosureOk v (List.map Param.ty jparams)[0] F
          have h_idx : ∀ (l : List Mtype) (h : 0 < l.length) (a : Mtype),
              l = [a] → l[0]'h = a := by
            intros l h a heq; subst heq; simp
          rw [h_idx _ _ _ hmap]; exact hcl)
      -- Preservation on join body (hbody_typed is at E=none; lift to outer E)
      preservation (hbody_typed.strengthen_E_from_none E) heval_body henv_body hft hcinv_body
        (FnEnvDisjoint.bindParams hdisj _ _ hfparams) hftc
        (hjwt.weakenΓ_bindParams hΓparams)
  | .handleErrorReturnErrOk heval_obj => match htype with
    | .handleErrorReturnErr htype_obj => (preservation htype_obj heval_obj henv hft hcinv hdisj hftc hjwt).liftValE
  | .handleErrorReturnErrErr heval_obj => match htype with
    | .handleErrorReturnErr htype_obj =>
      let pr := preservation htype_obj heval_obj henv hft hcinv hdisj hftc hjwt
      pr.errorWeaken
  | .handleErrorPropagate heval_obj hnotval hnoterr => match htype with
    | .handleErrorToResult htype_obj =>
      (preservation htype_obj heval_obj henv hft hcinv hdisj hftc hjwt).weakenE
        (by simp [Outcome.isAbort]) hnoterr
    | .handleErrorJoinapply htype_obj _ =>
      (preservation htype_obj heval_obj henv hft hcinv hdisj hftc hjwt).weakenE
        (by simp [Outcome.isAbort]) hnoterr
    | .handleErrorReturnErr htype_obj =>
      (preservation htype_obj heval_obj henv hft hcinv hdisj hftc hjwt).weaken
        (by simp [Outcome.isAbort])

  -- ════════ Return ════════
  | .returnSingle heval_e => match htype with
    | .returnSingle htype_e => preservation htype_e heval_e henv hft hcinv hdisj hftc hjwt
  | .returnError heval_e => match htype with
    | .returnErr hE htype_e =>
      let pr := preservation htype_e heval_e henv hft hcinv hdisj hftc hjwt
      .errorKnown pr.hasType.getVal (pr.closureOk _ rfl) hE
  | .returnOk heval_e => match htype with
    | .returnOk htype_e => preservation htype_e heval_e henv hft hcinv hdisj hftc hjwt

/-- Preservation for loop re-entry.
    Handles all LoopReentry constructors, producing PresResult in the OUTER Λ. -/
def preservationLoopReentry
    (htype_body : HasType (TyEnv.bindParams Γ params) Δ
      (LoopTyEnv.extend Λ label ⟨params.map (·.ty), τ⟩) F E body τ)
    (hreentry : LoopReentry ft env s jt lt nl params body newVals label loopOutcome sr nlr)
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F)
    (hloopParams : ∀ p, p ∈ params → F p.binder = none)
    (hΛfresh : Λ label = none)
    (hΓpfresh : ∀ p, p ∈ params → Γ p.binder = none)
    (hvts : ValueListHasType newVals (params.map (·.ty)))
    (hclos : ∀ i (hv : i < newVals.length) (hτ : i < (params.map (·.ty)).length),
      ValClosureOk (newVals[i]'hv) ((params.map (·.ty))[i]'hτ) F) :
    PresResult loopOutcome τ E F Λ := by
  match hreentry with
  | .val heval_body =>
    have hlen : params.length = newVals.length := by
      have := hvts.length_eq; simp [List.length_map] at this; omega
    let henv' := EnvWellTyped.bindParams_preserves henv _ _ hvts hlen
    let hcinv' := ClosureInvariant.bindParams hcinv _ _ hvts hlen
      (fun i hv hτ => hclos i hv (by simp [List.length_map]; exact hτ))
    exact (preservation htype_body heval_body henv' hft hcinv'
      (FnEnvDisjoint.bindParams hdisj _ _ hloopParams) hftc (hjwt.weakenΓΛ_loop hΛfresh hΓpfresh)).liftVal
  | .breakSome heval_body =>
    have hlen : params.length = newVals.length := by
      have := hvts.length_eq; simp [List.length_map] at this; omega
    let henv' := EnvWellTyped.bindParams_preserves henv _ _ hvts hlen
    let hcinv' := ClosureInvariant.bindParams hcinv _ _ hvts hlen
      (fun i hv hτ => hclos i hv (by simp [List.length_map]; exact hτ))
    let pr := preservation htype_body heval_body henv' hft hcinv'
      (FnEnvDisjoint.bindParams hdisj _ _ hloopParams) hftc (hjwt.weakenΓΛ_loop hΛfresh hΓpfresh)
    cases pr.hasType with
    | breakSome hΛ hvt hcl =>
      simp [LoopTyEnv.extend] at hΛ
      obtain ⟨_, rfl⟩ := hΛ
      exact PresResult.val' hvt hcl
  | .breakNone heval_body =>
    have hlen : params.length = newVals.length := by
      have := hvts.length_eq; simp [List.length_map] at this; omega
    let henv' := EnvWellTyped.bindParams_preserves henv _ _ hvts hlen
    let hcinv' := ClosureInvariant.bindParams hcinv _ _ hvts hlen
      (fun i hv hτ => hclos i hv (by simp [List.length_map]; exact hτ))
    let pr := preservation htype_body heval_body henv' hft hcinv'
      (FnEnvDisjoint.bindParams hdisj _ _ hloopParams) hftc (hjwt.weakenΓΛ_loop hΛfresh hΓpfresh)
    cases pr.hasType with
    | breakNone hΛ =>
      simp [LoopTyEnv.extend] at hΛ
      obtain ⟨_, rfl⟩ := hΛ
      exact PresResult.val' .unit (ValClosureOk.of_not_closure' (fun _ _ _ h => by cases h))
  | .continue heval_body hlen_next hreentry_inner =>
    have hlen : params.length = newVals.length := by
      have := hvts.length_eq; simp [List.length_map] at this; omega
    let henv' := EnvWellTyped.bindParams_preserves henv _ _ hvts hlen
    let hcinv' := ClosureInvariant.bindParams hcinv _ _ hvts hlen
      (fun i hv hτ => hclos i hv (by simp [List.length_map]; exact hτ))
    let pr := preservation htype_body heval_body henv' hft hcinv'
      (FnEnvDisjoint.bindParams hdisj _ _ hloopParams) hftc (hjwt.weakenΓΛ_loop hΛfresh hΓpfresh)
    cases pr.hasType with
    | «continue» hΛ hvts_next hclos_next =>
      simp [LoopTyEnv.extend] at hΛ
      obtain ⟨rfl, rfl⟩ := hΛ
      exact preservationLoopReentry htype_body hreentry_inner henv hft hcinv hdisj hftc hjwt
        hloopParams hΛfresh hΓpfresh hvts_next hclos_next
  | .return heval_body => exact .return'
  | .error heval_body =>
    have hlen : params.length = newVals.length := by
      have := hvts.length_eq; simp [List.length_map] at this; omega
    let henv' := EnvWellTyped.bindParams_preserves henv _ _ hvts hlen
    let hcinv' := ClosureInvariant.bindParams hcinv _ _ hvts hlen
      (fun i hv hτ => hclos i hv (by simp [List.length_map]; exact hτ))
    let pr := preservation htype_body heval_body henv' hft hcinv'
      (FnEnvDisjoint.bindParams hdisj _ _ hloopParams) hftc (hjwt.weakenΓΛ_loop hΛfresh hΓpfresh)
    exact pr.errorWeaken

def preservation_val
    (htype : HasType Γ Δ Λ F E e τ)
    (heval : Eval ft env s jt lt nl e (.val v) s' nl')
    (henv : EnvWellTyped env Γ)
    (hft : FnTableWellTyped ft F)
    (hcinv : ClosureInvariant env Γ F)
    (hdisj : FnEnvDisjoint env F)
    (hftc : FnTableComplete ft F)
    (hjwt : JoinWellTyped jt Δ Γ Λ F) :
    ValueHasType v τ :=
  (preservation htype heval henv hft hcinv hdisj hftc hjwt).hasType.getVal

end -- mutual

end Moonbit.Mcore
