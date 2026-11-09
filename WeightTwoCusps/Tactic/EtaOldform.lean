module

public import WeightTwoCusps.Oldforms.Rescale
public import WeightTwoCusps.EtaQuotient.Constructor
public meta import Mathlib.Tactic.Ext
public meta import Mathlib.Tactic.NormNum
public meta import Mathlib.Tactic.Simproc.Divisors

/-!
# Identifying oldforms with eta products

`eta_oldform` proves equalities between named eta-quotient cusp forms and
their degeneracy lifts at numeral levels. It follows the named forms,
applies the Oldforms application lemmas, and compares the finite eta products.
Divisor lists and integer arithmetic are checked by the kernel. No Fourier
coefficient comparison or search through existing identities is used.
-/

public meta section

open Lean Meta Elab Tactic Simp

namespace WeightTwoCusps.Tactic

/-- Normalize an application using explicit Oldforms lemmas. This also works when
the ambient level has already reduced from `M * d` to a numeral. -/
private partial def etaOldformApplication (form point : Expr) : MetaM Expr := do
  let form := (← instantiateMVars form).consumeMData
  let args := form.getAppArgs
  if form.isAppOfArity ``etaQuotientCuspForm 5 then
    return ← mkAppM ``etaQuotientCuspForm_apply
      #[args[0]!, args[1]!, args[3]!, args[4]!, point]
  let step? ← if form.isAppOfArity ``gamma0Rescale 4 then do
      pure <| some (args[1]!, ← mkAppM ``gamma0Rescale_apply
        #[args[1]!, args[2]!, args[3]!, point])
    else if form.isAppOfArity ``gamma0RescaleToLevel 6 then do
      pure <| some (args[2]!, ← mkAppM ``gamma0RescaleToLevel_apply
        #[args[2]!, args[3]!, args[4]!, args[5]!, point])
    else if form.isAppOfArity ``gamma0Restrict 4 then do
      pure <| some (args[2]!, ← mkAppM ``gamma0Restrict_apply
        #[args[2]!, args[3]!, point])
    else pure none
  if let some (source, step) := step? then
    let some (_, _, rhs) := (← inferType step).eq?
      | throwError "eta_oldform: expected an application identity"
    return ← mkEqTrans step (← etaOldformApplication source rhs.appArg!)
  if let .fvar id := form then
    if let some value := (← id.getDecl).value? then
      return ← etaOldformApplication value point
  let .const name _ := form.getAppFn
    | throwError "eta_oldform expects named eta-quotient cusp forms and degeneracy lifts"
  let some unfolded ← unfoldDefinition? form (ignoreTransparency := true)
    | throwError "eta_oldform cannot unfold {form} to an eta quotient or degeneracy lift"
  unless unfolded != form do
    throwError "eta_oldform cannot unfold {name}"
  etaOldformApplication unfolded point

/-- Evaluate closed exponents, including those stored in ordinary named definitions.
This procedure is enabled only inside `eta_oldform`, and the kernel checks reduction. -/
dsimproc_decl etaOldformExponent (EtaQuotient.exponent _ _) := fun e => do
  if e.hasFVar || e.hasMVar then return .continue
  let value ← withTransparency .all <| reduce e
  unless value.isAppOfArity ``Int.ofNat 1 || value.isAppOfArity ``Int.negSucc 1 do
    return .continue
  let some n ← getNatValue? value.appArg! | return .continue
  let value := if value.isAppOf ``Int.ofNat then Int.ofNat n else Int.negSucc n
  return .done (toExpr value)

/-- Prove a closed eta-product identity for restrictions and positive degeneracy
lifts, including named source forms and named lifts. Both sides must reduce to
`etaQuotientCuspForm`, `gamma0Restrict`, `gamma0Rescale`, or `gamma0RescaleToLevel`.
The tactic closes the goal only after the full finite-product identity is proved. -/
elab "eta_oldform" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some (_, lhs, rhs) := target.eq?
    | throwError "eta_oldform expects an equality of eta-quotient cusp forms"
  evalTactic (← `(tactic| ext z))
  withMainContext do
    let some (_, application, _) := (← getMainTarget).eq?
      | throwError "eta_oldform expects an equality of cusp-form values"
    let point := application.appArg!
    let lhsProof ← etaOldformApplication lhs point
    let rhsProof ← etaOldformApplication rhs point
    let some (_, _, lhsProduct) := (← inferType lhsProof).eq?
      | throwError "eta_oldform: expected a normalized left-hand side"
    let some (_, _, rhsProduct) := (← inferType rhsProof).eq?
      | throwError "eta_oldform: expected a normalized right-hand side"
    let productGoal ← mkFreshExprMVar (← mkEq lhsProduct rhsProduct)
    let proof ← mkEqTrans lhsProof (← mkEqTrans productGoal (← mkEqSymm rhsProof))
    (← getMainGoal).assign proof
    replaceMainGoal [productGoal.mvarId!]
    evalTactic (← `(tactic| solve |
      norm_num [etaQuotient, Nat.divisors_ofNat, etaOldformExponent,
        Eta.coe_dilate, ← mul_assoc]))

end WeightTwoCusps.Tactic
