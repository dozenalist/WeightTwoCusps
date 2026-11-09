module

public import WeightTwoCusps.QExpansion
public import Mathlib.LinearAlgebra.Basis.Defs
public meta import Mathlib.Data.Fin.VecNotation
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.DeclarationRange
public meta import Mathlib.Tactic.Translate.Attributes

/-!
# Entry lemmas for coefficient prefixes and finite eta bases

`@[eta_simps]` on `h : first_coeffs m f = [...]` generates the simp lemmas
`h_coeff_0`, ..., `h_coeff_{m-1}`. On `b : Module.Basis (Fin n) R M`, it
generates `b_0`, ..., `b_{n-1}`, simplifying the constructor at each index.
Parameters and hypotheses of the original declaration are retained.
Vector-based constructors reuse their coercion equality once, without
simplifying their coefficient columns, certification proofs, or vector entries.
-/

public section

namespace WeightTwoCusps

/-- Reuse a checked coefficient prefix at any index inside its stored range. -/
theorem qExpansion_coeff_eq_of_first_coeffs {m : ℕ}
    {f : UpperHalfPlane → ℂ} {t : List ℂ}
    (h : first_coeffs m f = t) (n : ℕ) (hn : n < m) :
    (UpperHalfPlane.qExpansion 1 f).coeff n = (t[n]?).getD 0 := by
  have hn' : n < (first_coeffs m f).length := by simpa using hn
  rw [← h, List.getElem?_eq_getElem hn', Option.getD_some]
  exact (first_coeffs_getElem m f n hn').symm

end WeightTwoCusps

public meta section

open Lean Meta Elab

namespace WeightTwoCusps.Tactic

private partial def prefixEntries (list : Expr) (entries : Array Expr := #[]) :
    MetaM (Array Expr) := do
  let list ← withTransparency .default <| whnf list
  if list.isAppOfArity ``List.nil 1 then return entries
  if list.isAppOfArity ``List.cons 3 then
    let args := list.getAppArgs
    return ← prefixEntries args[2]! (entries.push args[1]!)
  throwError "eta_simps: expected a coefficient list with a concrete length"

private def addEntryLemma (tgt : Name) (ref : Syntax) (levels : List Name)
    (params : Array Expr) (type proof : Expr) : MetaM Unit := do
  checkNotAlreadyDeclared tgt
  let type ← instantiateMVars (← mkForallFVars params type)
  let proof ← instantiateMVars (← mkLambdaFVars params proof)
  addDecl <| .thmDecl { name := tgt, levelParams := levels, type, value := proof }
  addDeclarationRangesFromSyntax tgt (← getRef) ref
  inferDefEqAttr tgt
  addSimpTheorem simpExtension tgt true false .global 1000

/-- Rewrite the basis coercion at the root before visiting any constructor arguments.
Unfold aliases only until a coercion lemma exposes the underlying vector. -/
private partial def basisVector? (basis : Expr) (ctx : Simp.Context) :
    MetaM (Option (Expr × Expr)) := do
  checkSystem "eta_simps"
  let coe ← mkAppM ``DFunLike.coe #[basis]
  let (step, _) ← Lean.Meta.Simp.SimpM.run ctx {} {} (Simp.rewritePost false coe)
  match step with
  | .done result | .visit result | .continue (some result) =>
    if result.expr != coe then
      return some (result.expr, ← result.getProof)
  | .continue none => pure ()
  let some body ← unfoldDefinition? basis (ignoreTransparency := true) | return none
  if body == basis then return none
  basisVector? body ctx

/-- Resolve a named vector while preserving the entries of its literal. -/
private partial def basisVectorEntries (count : Expr) (n : Nat) (vector : Expr) :
    MetaM (Array Expr) := do
  checkSystem "eta_simps"
  let (entries, _, _) ← Matrix.matchVecConsPrefix count vector
  if entries.length == n then return entries.toArray
  if vector.isLambda then return #[]
  let some body ← unfoldDefinition? vector (ignoreTransparency := true) | return #[]
  if body == vector then return #[]
  basisVectorEntries count n body

private def etaSimps (src : Name) (ref : Syntax) : MetaM (Array Name) := do
  let info ← withoutExporting <| getConstInfo src
  forallTelescopeReducing info.type fun params type => do
    let value := mkAppN (mkConst src (info.levelParams.map mkLevelParam)) params
    let mut generated := #[]
    if let some (_, lhs, rhs) := type.eq? then
      unless lhs.isAppOfArity ``first_coeffs 2 do
        throwError "eta_simps: expected `first_coeffs m f = [...]`"
      let count := lhs.getAppArgs[0]!
      let some n ← getNatValue? count
        | throwError "eta_simps: the coefficient count must be a concrete natural number"
      let entries ← prefixEntries rhs
      unless entries.size == n do
        throwError "eta_simps: expected {n} coefficients, found {entries.size}"
      for i in [:n] do
        let index := toExpr i
        let bound ← mkDecideProof (← mkAppM ``LT.lt #[index, count])
        let proof ← mkAppM ``qExpansion_coeff_eq_of_first_coeffs #[value, index, bound]
        let some (_, coeff, _) := (← inferType proof).eq? | unreachable!
        let name := src.appendAfter s!"_coeff_{i}"
        addEntryLemma name ref info.levelParams params (← mkEq coeff entries[i]!) proof
        generated := generated.push name
      return generated
    unless type.isAppOf ``Module.Basis do
      throwError "eta_simps: expected a coefficient-prefix theorem or a \
        `Module.Basis (Fin n) R M` definition"
    let indexType := type.getAppArgs[0]!
    unless indexType.isAppOfArity ``Fin 1 do
      throwError "eta_simps: the basis must be indexed by `Fin n`"
    let count := indexType.getAppArgs[0]!
    let some n ← getNatValue? count
      | throwError "eta_simps: the basis size must be a concrete natural number"
    let theorems ← (← getSimpTheorems).addDeclToUnfold src
    let ctx ← Simp.mkContext {} (simpTheorems := #[theorems])
      (congrTheorems := ← getSimpCongrTheorems)
    let simprocs := #[← Simp.getSimprocs]
    let vector? ← if n == 0 then pure none else basisVector? value ctx
    let entries ← match vector? with
      | some (vector, _) => basisVectorEntries count n vector
      | none => pure #[]
    for i in [:n] do
      -- Match the frontend's numeral syntax, so these rules also work with `simp`.
      let index ← if hi : i < n then pure (toExpr (⟨i, hi⟩ : Fin n)) else unreachable!
      let lhs ← mkAppM ``DFunLike.coe #[value, index]
      let result ← match vector? with
        | some (vector, proof) => do
          let rhs := if entries.size == n then entries[i]! else (mkApp vector index).headBeta
          let proof ← mkAppM ``congrFun #[proof, index]
          let proof := mkExpectedPropHint proof (← mkEq lhs rhs)
          if entries.size == n then
            pure ({ expr := rhs, proof? := some proof } : Simp.Result)
          else
            -- Other constructors may leave linear equivalences or function applications.
            -- Simplify those after eliminating the basis and its certificate arguments.
            let (result, _) ← simp rhs ctx simprocs
            pure { result with proof? := some (← mkEqTrans proof (← result.getProof)) }
        | none => pure (← simp lhs ctx simprocs).1
      unless result.expr != lhs do
        throwError "eta_simps: could not simplify basis entry {i}"
      let name := src.appendAfter s!"_{i}"
      addEntryLemma name ref info.levelParams params
        (← mkEq lhs result.expr) (← result.getProof)
      generated := generated.push name
    return generated

/-- Generate simp lemmas for every entry of a checked coefficient prefix or a finite basis. -/
syntax (name := eta_simps) "eta_simps" : attr

initialize etaSimpsAttribute : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `eta_simps
    descr := "Generate coefficient or finite-basis entry simp lemmas"
    applicationTime := .afterCompilation
    getParam := fun src ref => MetaM.run' (etaSimps src ref) }

initialize Mathlib.Tactic.registerGeneratingAttr `eta_simps fun src ref kind => do
  etaSimpsAttribute.attr.add src ref kind
  return (etaSimpsAttribute.getParam? (← getEnv) src).get!

end WeightTwoCusps.Tactic
