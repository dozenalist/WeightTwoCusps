module

public import WeightTwoCusps.Basis.IntegerMatrix
public import Mathlib.Tactic.Echelon.Cert
public meta import Mathlib.Tactic.Echelon.Rat
public meta import Mathlib.Tactic.NormNum
public meta import Mathlib.Tactic.Ring
public import Mathlib.Data.Matrix.Reflection
public import Mathlib.Tactic.Matrix.Parsing

/-!
# Fast nonzero determinant certificates for integer matrices

`integer_det` tries triangularity before searching successive primes for a
unit upper triangular elimination product. Failed primes generate no proof
terms. Only the successful partial product is checked by the Lean kernel.
The prime search limit is configurable; exhausting it is not a singularity
certificate. No native decision procedure is trusted.
-/

public meta section

open Lean Meta Elab Tactic Qq

namespace WeightTwoCusps.Tactic

initialize registerTraceClass `Tactic.integer_det

register_option integer_det.maxPrimes : Nat := {
  defValue := 64
  descr := "maximum number of successive primes tried by integer_det" }

/-- Assemble equality of finite vectors from entry equalities without `fin_cases`. -/
def determinantVectorEq {u : Level} (α : Q(Type u)) (n : Nat)
    (proofs : Array Expr) : MetaM Expr := do
  have empty : Q(Fin 0 → $α) := q(Matrix.vecEmpty)
  let mut left : Expr := empty
  let mut right : Expr := empty
  let mut proof : Expr := q(Eq.refl $empty)
  for k in [:n] do
    let entryProof := proofs[n - k - 1]!
    let some (_, a, b) := (← inferType entryProof).eq?
      | throwError "determinant certificate: expected an entry equality"
    have a : Q($α) := a
    have b : Q($α) := b
    have entryProof : Q($a = $b) := entryProof
    have tailLeft : Q(Fin $k → $α) := left
    have tailRight : Q(Fin $k → $α) := right
    have tailProof : Q($tailLeft = $tailRight) := proof
    proof := q(congrArg₂ (Matrix.vecCons (n := $k)) $entryProof $tailProof)
    left := q(Matrix.vecCons $a $tailLeft)
    right := q(Matrix.vecCons $b $tailRight)
  return proof

/-- Check a closed certificate once, in the kernel, and share the result. -/
def checkedDeterminantLemma (prop proof : Expr) : MetaM Expr := do
  -- Local numeral aliases may occur in a rational scaling equality. Expand
  -- their let-values before creating a closed auxiliary declaration.
  let prop ← if prop.hasFVar then zetaReduce prop else pure prop
  let proof ← if proof.hasFVar then zetaReduce proof else pure proof
  let name ← withOptions (Lean.Elab.async.set · false) <| mkAuxLemma [] prop proof
  return mkConst name

private def checkedDecide (prop : Expr) : MetaM Expr := do
  let dec ← mkDecide prop
  let refl := mkExpectedPropHint q(Eq.refl true) (← mkEq dec q(true))
  checkedDeterminantLemma prop
    (mkApp3 (mkConst ``of_decide_eq_true) prop dec.appArg! refl)

/-- Candidate generation only. Row swaps are applied to the transform itself,
so the certificate requires no separate permutation or invertibility proof. -/
private def modularTransform (p : Nat) (input : Array (Array Int)) :
    MetaM (Option (Array (Array Nat))) := do
  let n := input.size
  let mut a := input.map (·.map fun z => (z % (p : Int)).toNat)
  let mut e := (Array.range n).map fun i =>
    (Array.range n).map fun j => if i == j then 1 else 0
  for k in [:n] do
    checkSystem "integer_det"
    let mut pivot := k
    while pivot < n && (a[pivot]!)[k]! == 0 do pivot := pivot + 1
    if pivot == n then return none
    let oldA := a[k]!
    let oldE := e[k]!
    a := (a.set! k a[pivot]!).set! pivot oldA
    e := (e.set! k e[pivot]!).set! pivot oldE
    let mut inv := 1
    while inv < p && (inv * (a[k]!)[k]!) % p != 1 do inv := inv + 1
    if inv == p then return none
    let ak := a[k]!.map fun z => (inv * z) % p
    let ek := e[k]!.map fun z => (inv * z) % p
    a := a.set! k ak
    e := e.set! k ek
    for i in [k + 1:n] do
      let t := (a[i]!)[k]!
      if t != 0 then
        a := a.set! i ((Array.range n).map fun j =>
          ((a[i]!)[j]! + p - (t * ak[j]!) % p) % p)
        e := e.set! i ((Array.range n).map fun j =>
          ((e[i]!)[j]! + p - (t * ek[j]!) % p) % p)
  return some e

private def isPrimeCandidate (p : Nat) : Bool := Id.run do
  if p < 2 then return false
  let mut d := 2
  while d * d ≤ p do
    if p % d == 0 then return false
    d := d + 1
  return true

/-- Prove nonzeroness for an integer matrix whose normalized entries are given.
All sizes and entries are data, with no level-specific cases. -/
def proveIntegerDeterminant (n : Nat) (A : Q(Matrix (Fin $n) (Fin $n) ℤ))
    (entries : Array (Array Expr)) : MetaM Expr := do
  let mut cache : Std.HashMap Expr Int := {}
  let mut values := #[]
  for row in entries do
    let mut result := #[]
    for entry in row do
      let value ← if let some value := cache[entry]? then pure value else do
        let value ← Mathlib.Tactic.Echelon.evalRatEntry true entry
        unless value.den == 1 do throwError "integer_det: expected integer entries"
        pure value.num
      cache := cache.insert entry value
      result := result.push value
    values := values.push result
  let lit := Mathlib.Tactic.Echelon.ListMatrixLit.ofArray q(inferInstance : Zero ℤ)
    n n (values.map (·.map toExpr))
  have B : Q(Matrix (Fin $n) (Fin $n) ℤ) := lit.matrix
  let upper := (Array.range n).all fun i =>
    (Array.range i).all fun j => (values[i]!)[j]! == 0
  let lower := (Array.range n).all fun i =>
    (Array.range n).all fun j => j ≤ i || (values[i]!)[j]! == 0
  if upper || lower then
    unless (Array.range n).all (fun i => (values[i]!)[i]! != 0) do
      throwError "integer_det: singular triangular matrix"
    let diag ← checkedDecide q(∀ i, ($B).diag i ≠ 0)
    let proof ← if upper then do
        let triangular ← checkedDecide q(($B).IsUpperTriangular)
        mkAppM ``Iff.mpr #[← mkAppM ``Matrix.IsUpperTriangular.det_ne_zero_iff
          #[triangular], diag]
      else do
        let triangular ← checkedDecide q(($B).IsLowerTriangular)
        mkAppM ``Iff.mpr #[← mkAppM ``Matrix.IsLowerTriangular.det_ne_zero_iff
          #[triangular], diag]
    trace[Tactic.integer_det] "certified a triangular {n} by {n} integer matrix"
    return mkExpectedPropHint proof q(($A).det ≠ 0)
  let count := integer_det.maxPrimes.get (← getOptions)
  let mut p := 2
  for _ in [:count] do
    checkSystem "integer_det"
    while !isPrimeCandidate p do p := p + 1
    if let some transform ← modularTransform p values then
      let e := Mathlib.Tactic.Echelon.ListMatrixLit.ofArray q(inferInstance : Zero ℕ)
        n n (transform.map (·.map toExpr))
      have pE : Q(ℕ) := toExpr p
      let hp ← mkDecideProofQ q(1 < $pE)
      let columns := (Array.range n).map fun j => values.map fun row =>
        toExpr ((row[j]! % (p : Int)).toNat)
      let cols := Mathlib.Tactic.Echelon.ListMatrixLit.ofArray q(inferInstance : Zero ℕ)
        n n columns
      let colProp := q(Mathlib.Tactic.Matrix.ListMatrix.transpose $n
        (matrixResidues $pE $(lit.lit)) = $(cols.lit))
      let colCheck ← checkedDeterminantLemma colProp
        (mkExpectedPropHint q(Eq.refl $(cols.lit)) colProp)
      let prop := q(modularUpperCheckColumns $pE $n $(e.lit) $(cols.lit) = true)
      let check ← checkedDeterminantLemma prop (mkExpectedPropHint q(Eq.refl true) prop)
      let proof ← mkAppM ``matrix_det_ne_zero_of_modularColumns
        #[pE, toExpr n, hp, lit.lit, e.lit, cols.lit, colCheck, check]
      trace[Tactic.integer_det] "certified full rank modulo {p} for a {n} by {n} matrix"
      return mkExpectedPropHint proof q(($A).det ≠ 0)
    trace[Tactic.integer_det] "rank deficient modulo {p}; trying the next prime"
    p := p + 1
  throwError "integer_det: no full-rank modular image in {count} primes; \
    increase integer_det.maxPrimes"

private partial def exposeIntegerMatrix (e : Expr) : MetaM Expr := do
  checkSystem "integer_det"
  if e.isAppOf ``Mathlib.Tactic.Matrix.ofLists then return e
  if e.isAppOf ``Matrix.of || e.isAppOf ``Matrix.vecCons then return e
  if e.isLambda then return e
  if let .fvar id := e then
    if let some value := (← id.getDecl).value? then return ← exposeIntegerMatrix value
  let some body ← unfoldDefinition? e (ignoreTransparency := true) | return e
  if body == e then return e
  exposeIntegerMatrix body

private partial def integerListEntries? (e : Expr)
    (acc : Array Expr := #[]) : MetaM (Option (Array Expr)) := do
  match_expr ← whnfD e with
  | List.nil _ => return some acc
  | List.cons _ x xs => integerListEntries? xs (acc.push x)
  | _ => return none

private def integerRows? (n : Nat) (body : Expr) :
    MetaM (Option (Array (Array Expr))) := do
  unless body.isAppOf ``Mathlib.Tactic.Matrix.ofLists do return none
  let some rows ← integerListEntries? body.appArg! | return none
  let mut result := #[]
  for i in [:n] do
    let some row ← integerListEntries? (rows[i]?.getD q(([] : List ℤ))) | return none
    result := result.push ((Array.range n).map fun j => row[j]?.getD q((0 : ℤ)))
  return some result

private def computableIntegerEntry? (entry : Expr) : MetaM (Option Simp.Result) := do
  let value ← withTransparency .all <| whnf entry
  let z? ← if value.isAppOfArity ``Int.ofNat 1 || value.isAppOfArity ``Int.negSucc 1 then do
      let arg ← withTransparency .all <| whnf value.appArg!
      pure ((← getNatValue? arg).map fun n =>
        if value.isAppOf ``Int.ofNat then Int.ofNat n else Int.negSucc n)
    else getIntValue? value
  let some z := z? | return none
  have zE : Q(ℤ) := toExpr z
  return some {
    expr := zE
    proof? := some (mkExpectedPropHint q(Eq.refl $zE) (← mkEq entry zE)) }

/-- Integer-only entry point. Coefficient extraction and rational denominator
clearing are deliberately handled by their respective frontends. -/
elab "integer_det" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let_expr Ne _ lhs rhs := target | throwError "integer_det expects A.det ≠ 0"
  unless lhs.isAppOf ``Matrix.det do throwError "integer_det expects A.det ≠ 0"
  let original := lhs.appArg!
  let matrixType ← whnf (← inferType original)
  let .forallE _ rowTy tail _ := matrixType | throwError "integer_det expects a matrix"
  let .forallE _ colTy R _ ← whnf tail | throwError "integer_det expects a matrix"
  unless ← isDefEq R q(ℤ) do throwError "integer_det expects integer entries"
  unless ← isDefEq rhs q((0 : ℤ)) do throwError "integer_det expects comparison with zero"
  let_expr Fin size := rowTy | throwError "integer_det expects Fin indices"
  unless ← isDefEq rowTy colTy do throwError "integer_det expects a square matrix"
  let some n ← getNatValue? (← whnfD size) | throwError "integer_det expects a numeral size"
  let body ← exposeIntegerMatrix original
  let lists? ← integerRows? n body
  let literal? ← if lists?.isSome then pure none
    else Mathlib.Tactic.Matrix.matchMatrixLit? body (closed := false)
  let entries ← if let some es := lists? then pure es
    else if let some (_, _, _, es) := literal? then pure es
    else (Array.range n).mapM fun i => (Array.range n).mapM fun j => do
      pure (mkApp2 body (← mkFinLitQ n i) (← mkFinLitQ n j))
  if lists?.isSome then
    let numeralOnly ← entries.allM fun row => row.allM fun entry => do
      return (← getIntValue? entry).isSome
    if numeralOnly then
      have A : Q(Matrix (Fin $n) (Fin $n) ℤ) := original
      goal.assign (← proveIntegerDeterminant n A entries)
      replaceMainGoal []
      return
  let ctx ← Simp.mkContext {} (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let procs := #[← Simp.getSimprocs]
  let mut cache : Std.HashMap Expr Simp.Result := {}
  let mut normalized := #[]
  for row in entries do
    let mut result := #[]
    for entry in row do
      let r ← if let some r := cache[entry]? then pure r
        else if let some r ← computableIntegerEntry? entry then pure r
        else Mathlib.Meta.NormNum.deriveSimp ctx procs true entry
      cache := cache.insert entry r
      result := result.push r
    normalized := normalized.push result
  let es := normalized.map (·.map (·.expr))
  let rawRows := entries.map fun row =>
    PiFin.mkLiteralQ (α := q(ℤ)) (n := n) fun j => row[j.val]!
  have raw : Q(Matrix (Fin $n) (Fin $n) ℤ) := q(Matrix.of
    $(PiFin.mkLiteralQ (α := q(Fin $n → ℤ)) (n := n) fun i => rawRows[i.val]!))
  let rows := es.map fun row => PiFin.mkLiteralQ (α := q(ℤ)) (n := n) fun j => row[j.val]!
  have B : Q(Matrix (Fin $n) (Fin $n) ℤ) := q(Matrix.of
    $(PiFin.mkLiteralQ (α := q(Fin $n → ℤ)) (n := n) fun i => rows[i.val]!))
  let rowProofs ← (show MetaM (Array Expr) from normalized.mapM fun row => do
    determinantVectorEq q(ℤ) n (← row.mapM Simp.Result.getProof))
  let heq ← determinantVectorEq q(Fin $n → ℤ) n rowProofs
  have A : Q(Matrix (Fin $n) (Fin $n) ℤ) := original
  have hnorm : Q($raw = $B) := mkExpectedPropHint heq q($raw = $B)
  have hexpand : Q($raw = $A) := if literal?.isSome then
      mkExpectedPropHint q(Eq.refl $A) q($raw = $A)
    else mkExpectedPropHint q(Matrix.etaExpand_eq $A) q($raw = $A)
  have heq : Q($A = $B) := q(($hexpand).symm.trans $hnorm)
  let proof : Q(($B).det ≠ 0) ← proveIntegerDeterminant n B es
  goal.assign q(($heq).symm ▸ $proof)
  replaceMainGoal []

end WeightTwoCusps.Tactic
