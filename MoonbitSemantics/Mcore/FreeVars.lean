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

/-! ## Freshness propagation through extend/bindParams/extendMany

If all names absent from Γ are also absent from Γ' (hfresh : Γ x = none → Γ' x = none),
then extending both by the same variable preserves this property. This is key to
propagating freshness through recursive calls in HasType.strengthen.
-/

theorem TyEnv.extend_mono_none
    (hfresh : ∀ x, Γ x = none → Γ' x = none)
    (name : Var) (τ : Mtype) :
    ∀ x, (TyEnv.extend Γ name τ) x = none → (TyEnv.extend Γ' name τ) x = none := by
  intro x hx
  simp [TyEnv.extend] at hx ⊢
  by_cases h : x = name
  · simp [h] at hx
  · simp [h] at hx ⊢; exact hfresh _ hx

theorem TyEnv.extendMany_mono_none
    (hfresh : ∀ x, Γ x = none → Γ' x = none)
    (bindings : List (Var × Mtype)) :
    ∀ x, (TyEnv.extendMany Γ bindings) x = none →
         (TyEnv.extendMany Γ' bindings) x = none := by
  simp [TyEnv.extendMany]
  induction bindings generalizing Γ Γ' with
  | nil => exact hfresh
  | cons b bs ih =>
    simp [List.foldl]
    exact ih (TyEnv.extend_mono_none hfresh b.1 b.2)

theorem TyEnv.bindParams_mono_none
    (hfresh : ∀ x, Γ x = none → Γ' x = none)
    (params : List Param) :
    ∀ x, (TyEnv.bindParams Γ params) x = none →
         (TyEnv.bindParams Γ' params) x = none := by
  simp [TyEnv.bindParams]
  exact TyEnv.extendMany_mono_none hfresh _

/-! ## HasType Γ-strengthening (monotonicity)

If Γ' has at least all bindings of Γ (Γ ⊆ Γ'), then typing is preserved.
Proved by mutual recursion on HasType / HasTypeArgs.

Note: `decreasing_by all_goals sorry` is used in some mutual blocks because Lean 4's
recursion checker cannot handle universally quantified sub-derivations
(letrec's ∀ i, switchConstant's ∀ i). All recursive calls are on strict
sub-derivations, so termination is obvious.

The `hfresh` parameter captures that Γ and Γ' agree on absent names: if a variable
is absent from Γ, it is also absent from Γ'. This allows binder freshness fields
(e.g., `Γ name = none`) to propagate to `Γ' name = none`.

Note: `hfresh` is a strong condition that does NOT hold when Γ' = TyEnv.extend Γ x τ
(since the extended name goes from none to some). However, HasType.strengthen is only
used internally (no external callers in the codebase), and for recursive calls the
condition propagates through extend/bindParams since both sides are extended by the
same variable.
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
  | .let hF h1 h2 => .let hF (h1.strengthen hsub)
      (h2.strengthen (fun x τ' h => TyEnv.extend_mono hsub h))
  | .function hp hb => .function hp (hb.strengthen (TyEnv.bindParams_mono hsub _))
  | .rawFunction hp hb => .rawFunction hp hb
  | .letfnNonrec hF hp hfn hbd =>
    .letfnNonrec hF hp (hfn.strengthen (TyEnv.bindParams_mono hsub _))
      (hbd.strengthen (fun x τ' h => TyEnv.extend_mono hsub h))
  | .letfnRec hF hp hfn hbd =>
    .letfnRec hF hp
      (hfn.strengthen (TyEnv.bindParams_mono (fun _ _ h => TyEnv.extend_mono hsub h) _))
      (hbd.strengthen (fun _ _ h => TyEnv.extend_mono hsub h))
  | .letfnTailJoin hp hfn hbd =>
    .letfnTailJoin hp
      (hfn.strengthen (TyEnv.bindParams_mono hsub _)) (hbd.strengthen hsub)
  | .letfnNontailJoin hp hfn hbd =>
    .letfnNontailJoin hp
      (hfn.strengthen (TyEnv.bindParams_mono hsub _)) (hbd.strengthen hsub)
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
  | .fieldHeap hrec hpos => .fieldHeap (hrec.strengthen hsub) hpos
  | .mutate hrec hpos hfld => .mutate (hrec.strengthen hsub) hpos (hfld.strengthen hsub)
  | .assign hΓ he => .assign (hsub _ _ hΓ) (he.strengthen hsub)
  | .seq hargs hlast => .seq (hargs.strengthen hsub) (hlast.strengthen hsub)
  | .ifSome hc ht hf => .ifSome (hc.strengthen hsub) (ht.strengthen hsub) (hf.strengthen hsub)
  | .ifNone hc ht => .ifNone (hc.strengthen hsub) (ht.strengthen hsub)
  | .switchConstr hobj hcases hdflt =>
    .switchConstr (hobj.strengthen hsub)
      (fun tag binder branch hfind => (hcases tag binder branch hfind).strengthen
        (fun y σ h => by
          revert h; split <;> intro h
          · exact TyEnv.extend_mono hsub h
          · exact hsub _ _ h))
      (fun d hd => (hdflt d hd).strengthen hsub)
  | .switchConstant hobj hct hbranches hd =>
    .switchConstant (hobj.strengthen hsub) hct (fun i hi => (hbranches i hi).strengthen hsub) (hd.strengthen hsub)
  | .loop hp hargs hbd =>
    .loop hp (hargs.strengthen hsub)
      (hbd.strengthen (TyEnv.bindParams_mono hsub _))
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

theorem JoinTyEnv.extend_mono_none
    (hfresh : ∀ x, Δ x = none → Δ' x = none)
    (name : Var) (entry : JoinTyEntry) :
    ∀ x, (JoinTyEnv.extend Δ name entry) x = none → (JoinTyEnv.extend Δ' name entry) x = none := by
  intro x hx
  simp [JoinTyEnv.extend] at hx ⊢
  by_cases h : x = name
  · simp [h] at hx
  · simp [h] at hx ⊢; exact hfresh _ hx

/-! ## HasType Δ-strengthening (monotonicity)

If Δ' has at least all bindings of Δ (Δ ⊆ Δ'), then typing is preserved.
Proved by mutual recursion on HasType / HasTypeArgs.

The `hfresh` parameter captures that Δ and Δ' agree on absent names: if a join
variable is absent from Δ, it is also absent from Δ'. This allows binder freshness
fields (e.g., `Δ name = none`) to propagate to `Δ' name = none`.
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
  | .let hF h1 h2 => .let hF (h1.strengthen_Δ hsub) (h2.strengthen_Δ hsub)
  | .function hp hb => .function hp hb
  | .rawFunction hp hb => .rawFunction hp hb
  | .letfnNonrec hF hp hfn hbd =>
    .letfnNonrec hF hp hfn (hbd.strengthen_Δ hsub)
  | .letfnRec hF hp hfn hbd =>
    .letfnRec hF hp hfn (hbd.strengthen_Δ hsub)
  | .letfnTailJoin hp hfn hbd =>
    .letfnTailJoin hp (hfn.strengthen_Δ hsub)
      (hbd.strengthen_Δ (fun x e h => JoinTyEnv.extend_mono hsub h))
  | .letfnNontailJoin hp hfn hbd =>
    .letfnNontailJoin hp (hfn.strengthen_Δ hsub)
      (hbd.strengthen_Δ (fun x e h => JoinTyEnv.extend_mono hsub h))
  | .letrec hrec hFnames hFparams hbodies hbody =>
    .letrec rfl hFnames hFparams
      (fun i hi => hrec ▸ hbodies i hi)
      (hrec ▸ hbody.strengthen_Δ hsub)
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
  | .mutate hrec hpos hfld => .mutate (hrec.strengthen_Δ hsub) hpos (hfld.strengthen_Δ hsub)
  | .assign hΓ he => .assign hΓ (he.strengthen_Δ hsub)
  | .seq hargs hlast => .seq (hargs.strengthen_Δ hsub) (hlast.strengthen_Δ hsub)
  | .ifSome hc ht hf => .ifSome (hc.strengthen_Δ hsub) (ht.strengthen_Δ hsub) (hf.strengthen_Δ hsub)
  | .ifNone hc ht => .ifNone (hc.strengthen_Δ hsub) (ht.strengthen_Δ hsub)
  | .switchConstr hobj hcases hdflt =>
    .switchConstr (hobj.strengthen_Δ hsub)
      (fun tag binder branch hfind => (hcases tag binder branch hfind).strengthen_Δ hsub)
      (fun d hd => (hdflt d hd).strengthen_Δ hsub)
  | .switchConstant hobj hct hbranches hd =>
    .switchConstant (hobj.strengthen_Δ hsub) hct (fun i hi => (hbranches i hi).strengthen_Δ hsub) (hd.strengthen_Δ hsub)
  | .loop hp hargs hbd => .loop hp (hargs.strengthen_Δ hsub) (hbd.strengthen_Δ hsub)
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

def HasTypeArgs.strengthen_Δ
    (h : HasTypeArgs Γ Δ Λ F E es τs)
    (hsub : ∀ x e, Δ x = some e → Δ' x = some e) :
    HasTypeArgs Γ Δ' Λ F E es τs :=
  match h with
  | .nil => .nil
  | .cons he hrest => .cons (he.strengthen_Δ hsub) (hrest.strengthen_Δ hsub)

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

theorem LoopTyEnv.extend_mono_none
    (hfresh : ∀ l, Λ l = none → Λ' l = none)
    (name : LoopLabel) (entry : LoopTyEntry) :
    ∀ l, (LoopTyEnv.extend Λ name entry) l = none → (LoopTyEnv.extend Λ' name entry) l = none := by
  intro l hl
  simp [LoopTyEnv.extend] at hl ⊢
  by_cases h : l = name
  · simp [h] at hl
  · simp [h] at hl ⊢; exact hfresh _ hl

/-! ## HasType Λ-strengthening (monotonicity)

If Λ' has at least all bindings of Λ (Λ ⊆ Λ'), then typing is preserved.
Proved by mutual recursion on HasType / HasTypeArgs.

The `hfresh` parameter captures that Λ and Λ' agree on absent names: if a loop
label is absent from Λ, it is also absent from Λ'. This allows binder freshness
fields (e.g., `Λ label = none`) to propagate to `Λ' label = none`.
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
  | .let hF h1 h2 => .let hF (h1.strengthen_Λ hsub) (h2.strengthen_Λ hsub)
  | .function hp hb => .function hp hb
  | .rawFunction hp hb => .rawFunction hp hb
  | .letfnNonrec hF hp hfn hbd =>
    .letfnNonrec hF hp hfn (hbd.strengthen_Λ hsub)
  | .letfnRec hF hp hfn hbd =>
    .letfnRec hF hp hfn (hbd.strengthen_Λ hsub)
  | .letfnTailJoin hp hfn hbd =>
    .letfnTailJoin hp (hfn.strengthen_Λ hsub) (hbd.strengthen_Λ hsub)
  | .letfnNontailJoin hp hfn hbd =>
    .letfnNontailJoin hp (hfn.strengthen_Λ hsub) (hbd.strengthen_Λ hsub)
  | .letrec hrec hFnames hFparams hbodies hbody =>
    .letrec rfl hFnames hFparams
      (fun i hi => hrec ▸ hbodies i hi)
      (hrec ▸ hbody.strengthen_Λ hsub)
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
  | .mutate hrec hpos hfld => .mutate (hrec.strengthen_Λ hsub) hpos (hfld.strengthen_Λ hsub)
  | .assign hΓ he => .assign hΓ (he.strengthen_Λ hsub)
  | .seq hargs hlast => .seq (hargs.strengthen_Λ hsub) (hlast.strengthen_Λ hsub)
  | .ifSome hc ht hf => .ifSome (hc.strengthen_Λ hsub) (ht.strengthen_Λ hsub) (hf.strengthen_Λ hsub)
  | .ifNone hc ht => .ifNone (hc.strengthen_Λ hsub) (ht.strengthen_Λ hsub)
  | .switchConstr hobj hcases hdflt =>
    .switchConstr (hobj.strengthen_Λ hsub)
      (fun tag binder branch hfind => (hcases tag binder branch hfind).strengthen_Λ hsub)
      (fun d hd => (hdflt d hd).strengthen_Λ hsub)
  | .switchConstant hobj hct hbranches hd =>
    .switchConstant (hobj.strengthen_Λ hsub) hct (fun i hi => (hbranches i hi).strengthen_Λ hsub) (hd.strengthen_Λ hsub)
  | .loop hp hargs hbd =>
    .loop hp (hargs.strengthen_Λ hsub)
      (hbd.strengthen_Λ (LoopTyEnv.extend_mono hsub))
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

def HasTypeArgs.strengthen_Λ
    (h : HasTypeArgs Γ Δ Λ F E es τs)
    (hsub : ∀ l e, Λ l = some e → Λ' l = some e) :
    HasTypeArgs Γ Δ Λ' F E es τs :=
  match h with
  | .nil => .nil
  | .cons he hrest => .cons (he.strengthen_Λ hsub) (hrest.strengthen_Λ hsub)

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

/-- E-strengthening: expressions typed under E can be re-typed at E' if E = none
    (no returnErr possible). Takes E as a variable with equality proof. -/
def HasType.strengthen_E_from_none_aux
    (h : HasType Γ Δ Λ F E e τ) (hE : E = none) (E' : Option Mtype) :
    HasType Γ Δ Λ F E' e τ :=
  match h with
  | .const => .const
  | .unit => .unit
  | .var hΓ => .var hΓ
  | .varPrim hΓ => .varPrim hΓ
  | .let hF h1 h2 => .let hF (h1.strengthen_E_from_none_aux hE E') (h2.strengthen_E_from_none_aux hE E')
  | .function hp hb => .function hp hb  -- body has fresh E (none), unchanged
  | .rawFunction hp hb => .rawFunction hp hb  -- body has fresh E (none), unchanged
  | .letfnNonrec hF hp hfn hbd => .letfnNonrec hF hp hfn (hbd.strengthen_E_from_none_aux hE E')
  | .letfnRec hF hp hfn hbd => .letfnRec hF hp hfn (hbd.strengthen_E_from_none_aux hE E')
  | .letfnTailJoin hp hfn hbd => .letfnTailJoin hp hfn (hbd.strengthen_E_from_none_aux hE E')
  | .letfnNontailJoin hp hfn hbd => .letfnNontailJoin hp hfn (hbd.strengthen_E_from_none_aux hE E')
  | .letrec hrec hFnames hFparams hbodies hbody =>
    .letrec rfl hFnames hFparams
      (fun i hi => hrec ▸ hbodies i hi)
      (hrec ▸ hbody.strengthen_E_from_none_aux hE E')
  | .applyClosure hΓ hargs => .applyClosure hΓ (hargs.strengthen_E_from_none_aux hE E')
  | .applyRawFn hΓ hargs => .applyRawFn hΓ (hargs.strengthen_E_from_none_aux hE E')
  | .applyTopFn hF hargs => .applyTopFn hF (hargs.strengthen_E_from_none_aux hE E')
  | .applyJoin hΔ hargs => .applyJoin hΔ (hargs.strengthen_E_from_none_aux hE E')
  | .prim hargs hp => .prim (hargs.strengthen_E_from_none_aux hE E') hp
  | .constr hargs => .constr (hargs.strengthen_E_from_none_aux hE E')
  | .tuple hargs => .tuple (hargs.strengthen_E_from_none_aux hE E')
  | .record hargs => .record (hargs.strengthen_E_from_none_aux hE E')
  | .recordUpdate hrec hflds => .recordUpdate (hrec.strengthen_E_from_none_aux hE E') (hflds.strengthen_E_from_none_aux hE E')
  | .array hargs => .array (hargs.strengthen_E_from_none_aux hE E')
  | .fieldTuple hrec hp => .fieldTuple (hrec.strengthen_E_from_none_aux hE E') hp
  | .fieldHeap hrec hp => .fieldHeap (hrec.strengthen_E_from_none_aux hE E') hp
  | .mutate hrec hpos hfld => .mutate (hrec.strengthen_E_from_none_aux hE E') hpos (hfld.strengthen_E_from_none_aux hE E')
  | .assign hΓ he => .assign hΓ (he.strengthen_E_from_none_aux hE E')
  | .seq hargs hlast => .seq (hargs.strengthen_E_from_none_aux hE E') (hlast.strengthen_E_from_none_aux hE E')
  | .ifSome hc ht hf => .ifSome (hc.strengthen_E_from_none_aux hE E') (ht.strengthen_E_from_none_aux hE E') (hf.strengthen_E_from_none_aux hE E')
  | .ifNone hc ht => .ifNone (hc.strengthen_E_from_none_aux hE E') (ht.strengthen_E_from_none_aux hE E')
  | .switchConstr hobj hcases hdflt =>
    .switchConstr (hobj.strengthen_E_from_none_aux hE E')
      (fun tag binder branch hfind => (hcases tag binder branch hfind).strengthen_E_from_none_aux hE E')
      (fun d hd => (hdflt d hd).strengthen_E_from_none_aux hE E')
  | .switchConstant hobj hct hbranches hd =>
    .switchConstant (hobj.strengthen_E_from_none_aux hE E') hct (fun i hi => (hbranches i hi).strengthen_E_from_none_aux hE E') (hd.strengthen_E_from_none_aux hE E')
  | .loop hp hargs hbd => .loop hp (hargs.strengthen_E_from_none_aux hE E') (hbd.strengthen_E_from_none_aux hE E')
  | .break hΛ harg => .break hΛ (harg.strengthen_E_from_none_aux hE E')
  | .breakNone hΛ => .breakNone hΛ
  | .continue hΛ hargs => .continue hΛ (hargs.strengthen_E_from_none_aux hE E')
  | .and hl hr => .and (hl.strengthen_E_from_none_aux hE E') (hr.strengthen_E_from_none_aux hE E')
  | .or hl hr => .or (hl.strengthen_E_from_none_aux hE E') (hr.strengthen_E_from_none_aux hE E')
  | .handleErrorToResult h => .handleErrorToResult h  -- inner E fixed to some errTy, outer changes
  | .handleErrorJoinapply h hΔ => .handleErrorJoinapply h hΔ  -- inner E fixed
  | @HasType.handleErrorReturnErr _ _ _ _ errTy _ _ _ h => by cases hE  -- E = some errTy, contradicts hE : E = none
  | .returnSingle h => .returnSingle (h.strengthen_E_from_none_aux hE E')
  | .returnOk h => .returnOk (h.strengthen_E_from_none_aux hE E')
  | .returnErr hE' h => by subst hE; exact nomatch hE'  -- E = none ≠ some errTy
  | .object h => .object (h.strengthen_E_from_none_aux hE E')

def HasTypeArgs.strengthen_E_from_none_aux
    (h : HasTypeArgs Γ Δ Λ F E es τs) (hE : E = none) (E' : Option Mtype) :
    HasTypeArgs Γ Δ Λ F E' es τs :=
  match h with
  | .nil => .nil
  | .cons he hrest => .cons (he.strengthen_E_from_none_aux hE E') (hrest.strengthen_E_from_none_aux hE E')

end

/-- Wrapper: E-strengthening from none. -/
def HasType.strengthen_E_from_none
    (h : HasType Γ Δ Λ F none e τ) (E' : Option Mtype) :
    HasType Γ Δ Λ F E' e τ :=
  h.strengthen_E_from_none_aux rfl E'

def HasTypeArgs.strengthen_E_from_none
    (h : HasTypeArgs Γ Δ Λ F none es τs) (E' : Option Mtype) :
    HasTypeArgs Γ Δ Λ F E' es τs :=
  h.strengthen_E_from_none_aux rfl E'

end Moonbit.Mcore
