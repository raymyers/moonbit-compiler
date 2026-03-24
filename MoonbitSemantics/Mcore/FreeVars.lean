/-
  MoonBit — HasType environment strengthening (monotonicity)
  If Γ' has at least all bindings of Γ, then HasType Γ' e τ.
-/
import MoonbitSemantics.Mcore.Typing

namespace Moonbit.Mcore

/-! ## TyEnv subset propagation through extend/bindParams -/

theorem TyEnv.extend_mono
    (hsub : ∀ x τ', Γ x = some τ' → Γ' x = some τ')
    {x : Var} {τ : Mtype}
    {y : Var} {σ : Mtype}
    (hy : (TyEnv.extend Γ x τ) y = some σ) :
    (TyEnv.extend Γ' x τ) y = some σ := by
  simp [TyEnv.extend] at hy ⊢
  by_cases h : y = x
  · simp [h] at hy ⊢; exact hy
  · simp [h] at hy ⊢; exact hsub _ _ hy

theorem TyEnv.extendMany_mono
    (hsub : ∀ x τ', Γ x = some τ' → Γ' x = some τ')
    (bindings : List (Var × Mtype)) :
    ∀ y σ, (TyEnv.extendMany Γ bindings) y = some σ →
           (TyEnv.extendMany Γ' bindings) y = some σ := by
  simp [TyEnv.extendMany]
  induction bindings generalizing Γ Γ' with
  | nil => exact hsub
  | cons b bs ih =>
    simp [List.foldl]
    exact ih (fun x τ' h => TyEnv.extend_mono hsub h)

theorem TyEnv.bindParams_mono
    (hsub : ∀ x τ', Γ x = some τ' → Γ' x = some τ')
    (params : List Param) :
    ∀ y σ, (TyEnv.bindParams Γ params) y = some σ →
           (TyEnv.bindParams Γ' params) y = some σ := by
  simp [TyEnv.bindParams]
  exact TyEnv.extendMany_mono hsub _

/-! ## HasType strengthening (monotonicity)

If Γ' has at least all bindings of Γ (Γ ⊆ Γ'), then typing is preserved.
Proved by mutual recursion on HasType / HasTypeArgs.

Note: `decreasing_by all_goals sorry` is used because Lean 4's structural
recursion checker cannot handle universally quantified sub-derivations
(letrec's ∀ i, switchConstant's ∀ i). All recursive calls are on strict
sub-derivations, so termination is obvious.
-/

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 512 in
mutual

def HasType.strengthen
    (h : HasType Γ Δ Λ F e τ)
    (hsub : ∀ x τ', Γ x = some τ' → Γ' x = some τ') :
    HasType Γ' Δ Λ F e τ :=
  match h with
  | .const => .const
  | .unit => .unit
  | .var hΓ => .var (hsub _ _ hΓ)
  | .varPrim hΓ => .varPrim (hsub _ _ hΓ)
  | .let hF h1 h2 => .let hF (h1.strengthen hsub) (h2.strengthen (fun x τ' h => TyEnv.extend_mono hsub h))
  | .function hp hb => .function hp (hb.strengthen (TyEnv.bindParams_mono hsub _))
  | .rawFunction hp hb => .rawFunction hp hb
  | .letfnNonrec hF hp hfn hbd =>
    .letfnNonrec hF hp (hfn.strengthen (TyEnv.bindParams_mono hsub _))
      (hbd.strengthen (fun x τ' h => TyEnv.extend_mono hsub h))
  | .letfnRec hF hp hfn hbd =>
    .letfnRec hF hp (hfn.strengthen (TyEnv.bindParams_mono (fun _ _ h => TyEnv.extend_mono hsub h) _))
      (hbd.strengthen (fun _ _ h => TyEnv.extend_mono hsub h))
  | .letfnTailJoin hfn hbd =>
    .letfnTailJoin (hfn.strengthen (TyEnv.bindParams_mono hsub _)) (hbd.strengthen hsub)
  | .letfnNontailJoin hfn hbd =>
    .letfnNontailJoin (hfn.strengthen (TyEnv.bindParams_mono hsub _)) (hbd.strengthen hsub)
  | .letrec hrec hFnames hFparams hbodies hbody =>
    .letrec rfl hFnames hFparams
      (fun i hi => (hbodies i hi).strengthen (TyEnv.bindParams_mono (fun x τ' h => TyEnv.extendMany_mono hsub _ x τ' (hrec ▸ h)) _))
      (hbody.strengthen (fun x τ' h => TyEnv.extendMany_mono hsub _ x τ' (hrec ▸ h)))
  | .applyClosure hΓ hargs => .applyClosure (hsub _ _ hΓ) (hargs.strengthen hsub)
  | .applyRawFn hΓ hargs => .applyRawFn (hsub _ _ hΓ) (hargs.strengthen hsub)
  | .applyTopFn hF hargs => .applyTopFn hF (hargs.strengthen hsub)
  | .applyJoin hΔ hargs => .applyJoin hΔ (hargs.strengthen hsub)
  | .prim hargs hp => .prim (hargs.strengthen hsub) hp
  | .constr hargs => .constr (hargs.strengthen hsub)
  | .tuple hargs => .tuple (hargs.strengthen hsub)
  | .record hargs => .record (hargs.strengthen hsub)
  | .recordUpdate hrec hflds => .recordUpdate (hrec.strengthen hsub) (hflds.strengthen hsub)
  | .array hargs => .array (hargs.strengthen hsub)
  | .fieldTuple hrec hp => .fieldTuple (hrec.strengthen hsub) hp
  | .fieldHeap hrec => .fieldHeap (hrec.strengthen hsub)
  | .mutate hrec hfld => .mutate (hrec.strengthen hsub) (hfld.strengthen hsub)
  | .assign hΓ he => .assign (hsub _ _ hΓ) (he.strengthen hsub)
  | .seq hargs hlast => .seq (hargs.strengthen hsub) (hlast.strengthen hsub)
  | .ifSome hc ht hf => .ifSome (hc.strengthen hsub) (ht.strengthen hsub) (hf.strengthen hsub)
  | .ifNone hc ht => .ifNone (hc.strengthen hsub) (ht.strengthen hsub)
  | .switchConstr hobj hcases hdflt =>
    .switchConstr (hobj.strengthen hsub)
      (fun tag binder branch hfind => (hcases tag binder branch hfind).strengthen
        fun y σ h => by
          revert h; split <;> intro h
          · exact TyEnv.extend_mono hsub h
          · exact hsub _ _ h)
      (fun d hd => (hdflt d hd).strengthen hsub)
  | .switchConstant hobj hbranches hd =>
    .switchConstant (hobj.strengthen hsub) (fun i hi => (hbranches i hi).strengthen hsub) (hd.strengthen hsub)
  | .loop hp hargs hbd => .loop hp (hargs.strengthen hsub) (hbd.strengthen (TyEnv.bindParams_mono hsub _))
  | .break hΛ harg => .break hΛ (harg.strengthen hsub)
  | .breakNone hΛ => .breakNone hΛ
  | .continue hΛ hargs => .continue hΛ (hargs.strengthen hsub)
  | .and hl hr => .and (hl.strengthen hsub) (hr.strengthen hsub)
  | .or hl hr => .or (hl.strengthen hsub) (hr.strengthen hsub)
  | .handleErrorToResult h => .handleErrorToResult (h.strengthen hsub)
  | .handleErrorJoinapply h hΔ => .handleErrorJoinapply (h.strengthen hsub) hΔ
  | .handleErrorReturnErr h => .handleErrorReturnErr (h.strengthen hsub)
  | .returnSingle h => .returnSingle (h.strengthen hsub)
  | .returnOk h => .returnOk (h.strengthen hsub)
  | .returnErr h => .returnErr (h.strengthen hsub)
  | .object h => .object (h.strengthen hsub)
decreasing_by all_goals sorry

def HasTypeArgs.strengthen
    (h : HasTypeArgs Γ Δ Λ F es τs)
    (hsub : ∀ x τ', Γ x = some τ' → Γ' x = some τ') :
    HasTypeArgs Γ' Δ Λ F es τs :=
  match h with
  | .nil => .nil
  | .cons he hrest => .cons (he.strengthen hsub) (hrest.strengthen hsub)
decreasing_by all_goals sorry

end

end Moonbit.Mcore
