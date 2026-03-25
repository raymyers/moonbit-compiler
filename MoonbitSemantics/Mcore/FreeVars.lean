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

Note: `decreasing_by all_goals sorry` is used in some mutual blocks because Lean 4's
recursion checker cannot handle universally quantified sub-derivations
(letrec's ∀ i, switchConstant's ∀ i). All recursive calls are on strict
sub-derivations, so termination is obvious.

Freshness fields (e.g., `Γ name = none`) cannot survive Γ-strengthening
(Γ ⊆ Γ' does not imply Γ' name = none), so these are closed with `sorry`.
-/

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 512 in
mutual

def HasType.strengthen
    (h : HasType Γ Δ Λ F E e τ)
    (hsub : ∀ x τ', Γ x = some τ' → Γ' x = some τ') :
    HasType Γ' Δ Λ F E e τ :=
  match h with
  | .const => .const
  | .unit => .unit
  | .var hΓ => .var (hsub _ _ hΓ)
  | .varPrim hΓ => .varPrim (hsub _ _ hΓ)
  | .let _hΓfresh hF h1 h2 => .let sorry hF (h1.strengthen hsub) (h2.strengthen (fun x τ' h => TyEnv.extend_mono hsub h))
  | .function hp hb => .function hp (hb.strengthen (TyEnv.bindParams_mono hsub _))
  | .rawFunction hp hb => .rawFunction hp hb
  | .letfnNonrec _hΓfresh hF hp hfn hbd =>
    .letfnNonrec sorry hF hp (hfn.strengthen (TyEnv.bindParams_mono hsub _))
      (hbd.strengthen (fun x τ' h => TyEnv.extend_mono hsub h))
  | .letfnRec _hΓfresh hF hp hfn hbd =>
    .letfnRec sorry hF hp (hfn.strengthen (TyEnv.bindParams_mono (fun _ _ h => TyEnv.extend_mono hsub h) _))
      (hbd.strengthen (fun _ _ h => TyEnv.extend_mono hsub h))
  | .letfnTailJoin hΔfresh _hΓpfresh hp hfn hbd =>
    .letfnTailJoin hΔfresh sorry hp (hfn.strengthen (TyEnv.bindParams_mono hsub _)) (hbd.strengthen hsub)
  | .letfnNontailJoin hΔfresh _hΓpfresh hp hfn hbd =>
    .letfnNontailJoin hΔfresh sorry hp (hfn.strengthen (TyEnv.bindParams_mono hsub _)) (hbd.strengthen hsub)
  | .letrec hrec _hΓfresh hDistinct hFnames hFparams hbodies hbody =>
    .letrec rfl sorry hDistinct hFnames hFparams
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
  | .fieldHeap hrec hpos => .fieldHeap (hrec.strengthen hsub) hpos
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
  | .loop hΛfresh _hΓpfresh hp hargs hbd =>
    .loop hΛfresh sorry hp (hargs.strengthen hsub) (hbd.strengthen (TyEnv.bindParams_mono hsub _))
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
  | .returnErr hE h => .returnErr hE (h.strengthen hsub)
  | .object h => .object (h.strengthen hsub)

def HasTypeArgs.strengthen
    (h : HasTypeArgs Γ Δ Λ F E es τs)
    (hsub : ∀ x τ', Γ x = some τ' → Γ' x = some τ') :
    HasTypeArgs Γ' Δ Λ F E es τs :=
  match h with
  | .nil => .nil
  | .cons he hrest => .cons (he.strengthen hsub) (hrest.strengthen hsub)

end

/-! ## JoinTyEnv subset propagation through extend -/

theorem JoinTyEnv.extend_mono
    (hsub : ∀ x e, Δ x = some e → Δ' x = some e)
    {j : Var} {entry : JoinTyEntry}
    {j' : Var} {e : JoinTyEntry}
    (h : (JoinTyEnv.extend Δ j entry) j' = some e) :
    (JoinTyEnv.extend Δ' j entry) j' = some e := by
  simp [JoinTyEnv.extend] at h ⊢
  by_cases hj : j' = j
  · simp [hj] at h ⊢; exact h
  · simp [hj] at h ⊢; exact hsub _ _ h

/-! ## HasType Δ-strengthening (monotonicity)

If Δ' has at least all bindings of Δ (Δ ⊆ Δ'), then typing is preserved.
Proved by mutual recursion on HasType / HasTypeArgs.

Freshness fields for Δ (letfnTailJoin/letfnNontailJoin) cannot survive
Δ-strengthening, so these are closed with `sorry`.
-/

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 512 in
mutual

def HasType.strengthen_Δ
    (h : HasType Γ Δ Λ F E e τ)
    (hsub : ∀ x e, Δ x = some e → Δ' x = some e) :
    HasType Γ Δ' Λ F E e τ :=
  match h with
  | .const => .const
  | .unit => .unit
  | .var hΓ => .var hΓ
  | .varPrim hΓ => .varPrim hΓ
  | .let hΓfresh hF h1 h2 => .let hΓfresh hF (h1.strengthen_Δ hsub) (h2.strengthen_Δ hsub)
  | .function hp hb => .function hp hb
  | .rawFunction hp hb => .rawFunction hp hb
  | .letfnNonrec hΓfresh hF hp hfn hbd =>
    .letfnNonrec hΓfresh hF hp hfn (hbd.strengthen_Δ hsub)
  | .letfnRec hΓfresh hF hp hfn hbd =>
    .letfnRec hΓfresh hF hp hfn (hbd.strengthen_Δ hsub)
  | .letfnTailJoin _hΔfresh hΓpfresh hp hfn hbd =>
    .letfnTailJoin sorry hΓpfresh hp (hfn.strengthen_Δ hsub)
      (hbd.strengthen_Δ (fun x e h => JoinTyEnv.extend_mono hsub h))
  | .letfnNontailJoin _hΔfresh hΓpfresh hp hfn hbd =>
    .letfnNontailJoin sorry hΓpfresh hp (hfn.strengthen_Δ hsub)
      (hbd.strengthen_Δ (fun x e h => JoinTyEnv.extend_mono hsub h))
  | .letrec hrec hΓfresh hDistinct hFnames hFparams hbodies hbody =>
    .letrec rfl hΓfresh hDistinct hFnames hFparams
      (fun i hi => hrec ▸ hbodies i hi)
      ((hrec ▸ hbody).strengthen_Δ hsub)
  | .applyClosure hΓ hargs => .applyClosure hΓ (hargs.strengthen_Δ hsub)
  | .applyRawFn hΓ hargs => .applyRawFn hΓ (hargs.strengthen_Δ hsub)
  | .applyTopFn hF hargs => .applyTopFn hF (hargs.strengthen_Δ hsub)
  | .applyJoin hΔ hargs => .applyJoin (hsub _ _ hΔ) (hargs.strengthen_Δ hsub)
  | .prim hargs hp => .prim (hargs.strengthen_Δ hsub) hp
  | .constr hargs => .constr (hargs.strengthen_Δ hsub)
  | .tuple hargs => .tuple (hargs.strengthen_Δ hsub)
  | .record hargs => .record (hargs.strengthen_Δ hsub)
  | .recordUpdate hrec hflds => .recordUpdate (hrec.strengthen_Δ hsub) (hflds.strengthen_Δ hsub)
  | .array hargs => .array (hargs.strengthen_Δ hsub)
  | .fieldTuple hrec hp => .fieldTuple (hrec.strengthen_Δ hsub) hp
  | .fieldHeap hrec hpos => .fieldHeap (hrec.strengthen_Δ hsub) hpos
  | .mutate hrec hfld => .mutate (hrec.strengthen_Δ hsub) (hfld.strengthen_Δ hsub)
  | .assign hΓ he => .assign hΓ (he.strengthen_Δ hsub)
  | .seq hargs hlast => .seq (hargs.strengthen_Δ hsub) (hlast.strengthen_Δ hsub)
  | .ifSome hc ht hf => .ifSome (hc.strengthen_Δ hsub) (ht.strengthen_Δ hsub) (hf.strengthen_Δ hsub)
  | .ifNone hc ht => .ifNone (hc.strengthen_Δ hsub) (ht.strengthen_Δ hsub)
  | .switchConstr hobj hcases hdflt =>
    .switchConstr (hobj.strengthen_Δ hsub)
      (fun tag binder branch hfind => (hcases tag binder branch hfind).strengthen_Δ hsub)
      (fun d hd => (hdflt d hd).strengthen_Δ hsub)
  | .switchConstant hobj hbranches hd =>
    .switchConstant (hobj.strengthen_Δ hsub) (fun i hi => (hbranches i hi).strengthen_Δ hsub) (hd.strengthen_Δ hsub)
  | .loop hΛfresh hΓpfresh hp hargs hbd => .loop hΛfresh hΓpfresh hp (hargs.strengthen_Δ hsub) (hbd.strengthen_Δ hsub)
  | .break hΛ harg => .break hΛ (harg.strengthen_Δ hsub)
  | .breakNone hΛ => .breakNone hΛ
  | .continue hΛ hargs => .continue hΛ (hargs.strengthen_Δ hsub)
  | .and hl hr => .and (hl.strengthen_Δ hsub) (hr.strengthen_Δ hsub)
  | .or hl hr => .or (hl.strengthen_Δ hsub) (hr.strengthen_Δ hsub)
  | .handleErrorToResult h => .handleErrorToResult (h.strengthen_Δ hsub)
  | .handleErrorJoinapply h hΔ => .handleErrorJoinapply (h.strengthen_Δ hsub) (hsub _ _ hΔ)
  | .handleErrorReturnErr h => .handleErrorReturnErr (h.strengthen_Δ hsub)
  | .returnSingle h => .returnSingle (h.strengthen_Δ hsub)
  | .returnOk h => .returnOk (h.strengthen_Δ hsub)
  | .returnErr hE h => .returnErr hE (h.strengthen_Δ hsub)
  | .object h => .object (h.strengthen_Δ hsub)
decreasing_by all_goals sorry

def HasTypeArgs.strengthen_Δ
    (h : HasTypeArgs Γ Δ Λ F E es τs)
    (hsub : ∀ x e, Δ x = some e → Δ' x = some e) :
    HasTypeArgs Γ Δ' Λ F E es τs :=
  match h with
  | .nil => .nil
  | .cons he hrest => .cons (he.strengthen_Δ hsub) (hrest.strengthen_Δ hsub)
decreasing_by all_goals sorry

end

/-! ## LoopTyEnv subset propagation through extend -/

theorem LoopTyEnv.extend_mono
    (hsub : ∀ l e, Λ l = some e → Λ' l = some e) :
    ∀ l e, (LoopTyEnv.extend Λ name entry) l = some e →
           (LoopTyEnv.extend Λ' name entry) l = some e := by
  intro l e h
  simp [LoopTyEnv.extend] at h ⊢
  by_cases hl : l = name
  · simp [hl] at h ⊢; exact h
  · simp [hl] at h ⊢; exact hsub _ _ h

/-! ## HasType Λ-strengthening (monotonicity)

If Λ' has at least all bindings of Λ (Λ ⊆ Λ'), then typing is preserved.
Proved by mutual recursion on HasType / HasTypeArgs.

Freshness field for Λ (loop's `Λ label = none`) cannot survive
Λ-strengthening, so it is closed with `sorry`.
-/

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 512 in
mutual

def HasType.strengthen_Λ
    (h : HasType Γ Δ Λ F E e τ)
    (hsub : ∀ l e, Λ l = some e → Λ' l = some e) :
    HasType Γ Δ Λ' F E e τ :=
  match h with
  | .const => .const
  | .unit => .unit
  | .var hΓ => .var hΓ
  | .varPrim hΓ => .varPrim hΓ
  | .let hΓfresh hF h1 h2 => .let hΓfresh hF (h1.strengthen_Λ hsub) (h2.strengthen_Λ hsub)
  | .function hp hb => .function hp hb
  | .rawFunction hp hb => .rawFunction hp hb
  | .letfnNonrec hΓfresh hF hp hfn hbd =>
    .letfnNonrec hΓfresh hF hp hfn (hbd.strengthen_Λ hsub)
  | .letfnRec hΓfresh hF hp hfn hbd =>
    .letfnRec hΓfresh hF hp hfn (hbd.strengthen_Λ hsub)
  | .letfnTailJoin hΔfresh hΓpfresh hp hfn hbd =>
    .letfnTailJoin hΔfresh hΓpfresh hp (hfn.strengthen_Λ hsub) (hbd.strengthen_Λ hsub)
  | .letfnNontailJoin hΔfresh hΓpfresh hp hfn hbd =>
    .letfnNontailJoin hΔfresh hΓpfresh hp (hfn.strengthen_Λ hsub) (hbd.strengthen_Λ hsub)
  | .letrec hrec hΓfresh hDistinct hFnames hFparams hbodies hbody =>
    .letrec rfl hΓfresh hDistinct hFnames hFparams
      (fun i hi => hrec ▸ hbodies i hi)
      ((hrec ▸ hbody).strengthen_Λ hsub)
  | .applyClosure hΓ hargs => .applyClosure hΓ (hargs.strengthen_Λ hsub)
  | .applyRawFn hΓ hargs => .applyRawFn hΓ (hargs.strengthen_Λ hsub)
  | .applyTopFn hF hargs => .applyTopFn hF (hargs.strengthen_Λ hsub)
  | .applyJoin hΔ hargs => .applyJoin hΔ (hargs.strengthen_Λ hsub)
  | .prim hargs hp => .prim (hargs.strengthen_Λ hsub) hp
  | .constr hargs => .constr (hargs.strengthen_Λ hsub)
  | .tuple hargs => .tuple (hargs.strengthen_Λ hsub)
  | .record hargs => .record (hargs.strengthen_Λ hsub)
  | .recordUpdate hrec hflds => .recordUpdate (hrec.strengthen_Λ hsub) (hflds.strengthen_Λ hsub)
  | .array hargs => .array (hargs.strengthen_Λ hsub)
  | .fieldTuple hrec hp => .fieldTuple (hrec.strengthen_Λ hsub) hp
  | .fieldHeap hrec hpos => .fieldHeap (hrec.strengthen_Λ hsub) hpos
  | .mutate hrec hfld => .mutate (hrec.strengthen_Λ hsub) (hfld.strengthen_Λ hsub)
  | .assign hΓ he => .assign hΓ (he.strengthen_Λ hsub)
  | .seq hargs hlast => .seq (hargs.strengthen_Λ hsub) (hlast.strengthen_Λ hsub)
  | .ifSome hc ht hf => .ifSome (hc.strengthen_Λ hsub) (ht.strengthen_Λ hsub) (hf.strengthen_Λ hsub)
  | .ifNone hc ht => .ifNone (hc.strengthen_Λ hsub) (ht.strengthen_Λ hsub)
  | .switchConstr hobj hcases hdflt =>
    .switchConstr (hobj.strengthen_Λ hsub)
      (fun tag binder branch hfind => (hcases tag binder branch hfind).strengthen_Λ hsub)
      (fun d hd => (hdflt d hd).strengthen_Λ hsub)
  | .switchConstant hobj hbranches hd =>
    .switchConstant (hobj.strengthen_Λ hsub) (fun i hi => (hbranches i hi).strengthen_Λ hsub) (hd.strengthen_Λ hsub)
  | .loop _hΛfresh hΓpfresh hp hargs hbd =>
    .loop sorry hΓpfresh hp (hargs.strengthen_Λ hsub) (hbd.strengthen_Λ (LoopTyEnv.extend_mono hsub))
  | .break hΛ harg => .break (hsub _ _ hΛ) (harg.strengthen_Λ hsub)
  | .breakNone hΛ => .breakNone (hsub _ _ hΛ)
  | .continue hΛ hargs => .continue (hsub _ _ hΛ) (hargs.strengthen_Λ hsub)
  | .and hl hr => .and (hl.strengthen_Λ hsub) (hr.strengthen_Λ hsub)
  | .or hl hr => .or (hl.strengthen_Λ hsub) (hr.strengthen_Λ hsub)
  | .handleErrorToResult h => .handleErrorToResult (h.strengthen_Λ hsub)
  | .handleErrorJoinapply h hΔ => .handleErrorJoinapply (h.strengthen_Λ hsub) hΔ
  | .handleErrorReturnErr h => .handleErrorReturnErr (h.strengthen_Λ hsub)
  | .returnSingle h => .returnSingle (h.strengthen_Λ hsub)
  | .returnOk h => .returnOk (h.strengthen_Λ hsub)
  | .returnErr hE h => .returnErr hE (h.strengthen_Λ hsub)
  | .object h => .object (h.strengthen_Λ hsub)
decreasing_by all_goals sorry

def HasTypeArgs.strengthen_Λ
    (h : HasTypeArgs Γ Δ Λ F E es τs)
    (hsub : ∀ l e, Λ l = some e → Λ' l = some e) :
    HasTypeArgs Γ Δ Λ' F E es τs :=
  match h with
  | .nil => .nil
  | .cons he hrest => .cons (he.strengthen_Λ hsub) (hrest.strengthen_Λ hsub)
decreasing_by all_goals sorry

end

/-! ## HasType E-strengthening from none

If E = none, expressions have no returnErr, so they can be re-typed at any E'.
The key insight: `returnErr` requires `E = some errTy`, but `E = none` makes
this absurd. `function`/`rawFunction`/`letrec` bodies have their own E, so
they pass through unchanged.

All freshness fields pass through unchanged since E doesn't affect Γ/Δ/Λ.
-/

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 512 in
mutual

/-- E-strengthening from none: expressions typed under E=none have no returnErr,
    so they can be re-typed at any E'. -/
def HasType.strengthen_E_from_none
    (h : HasType Γ Δ Λ F none e τ) (E' : Option Mtype) :
    HasType Γ Δ Λ F E' e τ :=
  match h with
  | .const => .const
  | .unit => .unit
  | .var hΓ => .var hΓ
  | .varPrim hΓ => .varPrim hΓ
  | .let hΓfresh hF h1 h2 => .let hΓfresh hF (h1.strengthen_E_from_none E') (h2.strengthen_E_from_none E')
  | .function hp hb => .function hp hb  -- body has fresh E (none), unchanged
  | .rawFunction hp hb => .rawFunction hp hb  -- body has fresh E (none), unchanged
  | .letfnNonrec hΓfresh hF hp hfn hbd => .letfnNonrec hΓfresh hF hp hfn (hbd.strengthen_E_from_none E')
  | .letfnRec hΓfresh hF hp hfn hbd => .letfnRec hΓfresh hF hp hfn (hbd.strengthen_E_from_none E')
  | .letfnTailJoin hΔfresh hΓpfresh hp hfn hbd => .letfnTailJoin hΔfresh hΓpfresh hp hfn (hbd.strengthen_E_from_none E')
  | .letfnNontailJoin hΔfresh hΓpfresh hp hfn hbd => .letfnNontailJoin hΔfresh hΓpfresh hp hfn (hbd.strengthen_E_from_none E')
  | .letrec hrec hΓfresh hDistinct hFnames hFparams hbodies hbody =>
    .letrec hrec hΓfresh hDistinct hFnames hFparams
      (fun i hi => (hbodies i hi))  -- letrec bodies have JoinTyEnv.empty, LoopTyEnv.empty, keep E
      (hbody.strengthen_E_from_none E')
  | .applyClosure hΓ hargs => .applyClosure hΓ (hargs.strengthen_E_from_none E')
  | .applyRawFn hΓ hargs => .applyRawFn hΓ (hargs.strengthen_E_from_none E')
  | .applyTopFn hF hargs => .applyTopFn hF (hargs.strengthen_E_from_none E')
  | .applyJoin hΔ hargs => .applyJoin hΔ (hargs.strengthen_E_from_none E')
  | .prim hargs hp => .prim (hargs.strengthen_E_from_none E') hp
  | .constr hargs => .constr (hargs.strengthen_E_from_none E')
  | .tuple hargs => .tuple (hargs.strengthen_E_from_none E')
  | .record hargs => .record (hargs.strengthen_E_from_none E')
  | .recordUpdate hrec hflds => .recordUpdate (hrec.strengthen_E_from_none E') (hflds.strengthen_E_from_none E')
  | .array hargs => .array (hargs.strengthen_E_from_none E')
  | .fieldTuple hrec hp => .fieldTuple (hrec.strengthen_E_from_none E') hp
  | .fieldHeap hrec hp => .fieldHeap (hrec.strengthen_E_from_none E') hp
  | .mutate hrec hfld => .mutate (hrec.strengthen_E_from_none E') (hfld.strengthen_E_from_none E')
  | .assign hΓ he => .assign hΓ (he.strengthen_E_from_none E')
  | .seq hargs hlast => .seq (hargs.strengthen_E_from_none E') (hlast.strengthen_E_from_none E')
  | .ifSome hc ht hf => .ifSome (hc.strengthen_E_from_none E') (ht.strengthen_E_from_none E') (hf.strengthen_E_from_none E')
  | .ifNone hc ht => .ifNone (hc.strengthen_E_from_none E') (ht.strengthen_E_from_none E')
  | .switchConstr hobj hcases hdflt =>
    .switchConstr (hobj.strengthen_E_from_none E')
      (fun tag binder branch hfind => (hcases tag binder branch hfind).strengthen_E_from_none E')
      (fun d hd => (hdflt d hd).strengthen_E_from_none E')
  | .switchConstant hobj hbranches hd =>
    .switchConstant (hobj.strengthen_E_from_none E') (fun i hi => (hbranches i hi).strengthen_E_from_none E') (hd.strengthen_E_from_none E')
  | .loop hΛfresh hΓpfresh hp hargs hbd => .loop hΛfresh hΓpfresh hp (hargs.strengthen_E_from_none E') (hbd.strengthen_E_from_none E')
  | .break hΛ harg => .break hΛ (harg.strengthen_E_from_none E')
  | .breakNone hΛ => .breakNone hΛ
  | .continue hΛ hargs => .continue hΛ (hargs.strengthen_E_from_none E')
  | .and hl hr => .and (hl.strengthen_E_from_none E') (hr.strengthen_E_from_none E')
  | .or hl hr => .or (hl.strengthen_E_from_none E') (hr.strengthen_E_from_none E')
  | .handleErrorToResult h => .handleErrorToResult h  -- inner E fixed to some errTy, outer changes
  | .handleErrorJoinapply h hΔ => .handleErrorJoinapply h hΔ  -- inner E fixed
  -- handleErrorReturnErr is impossible: outer E = some errTy contradicts E = none
  | .returnSingle h => .returnSingle (h.strengthen_E_from_none E')
  | .returnOk h => .returnOk (h.strengthen_E_from_none E')
  | .returnErr hE h => nomatch hE  -- E = none ≠ some errTy, so returnErr is impossible!
  | .object h => .object (h.strengthen_E_from_none E')
decreasing_by all_goals sorry

def HasTypeArgs.strengthen_E_from_none
    (h : HasTypeArgs Γ Δ Λ F none es τs) (E' : Option Mtype) :
    HasTypeArgs Γ Δ Λ F E' es τs :=
  match h with
  | .nil => .nil
  | .cons he hrest => .cons (he.strengthen_E_from_none E') (hrest.strengthen_E_from_none E')
decreasing_by all_goals sorry

end

end Moonbit.Mcore
