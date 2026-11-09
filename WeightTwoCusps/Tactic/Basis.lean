module

public import WeightTwoCusps.Basis.Basic
public import WeightTwoCusps.Basis.Determinant
public import WeightTwoCusps.Tactic.IntegerDeterminant
public import WeightTwoCusps.Tactic.Gamma_0
public import WeightTwoCusps.Tactic.Gamma_1
public import WeightTwoCusps.Tactic.Gamma
public import WeightTwoCusps.Tactic.EtaCoefficient
public meta import Mathlib.Tactic.NormNum
public meta import Mathlib.Tactic.Ring
public meta import Lean.Meta.Sym.Eta
public import Mathlib.Data.Matrix.Reflection
public import Mathlib.Tactic.NormRank
public import Determinant
public meta import Determinant.Tactic.Cache
public meta import Lean.Util.Path

/-!
# Certifying cusp-form bases

`cusp_basis_dimension`, `cusp_basis_period`, `cusp_basis_det`, and
`cusp_basis_independent` handle the separate constructor obligations.
`cusp_basis` remains a compatibility dispatcher. `matrix_det` tries structural
proofs, small determinants, and numerical certificates in that order.
`cusp_basis_independent using ![1, 3]` selects coefficient indices.

Characteristic-zero numerical matrices are reduced to rational entries and
then to integer matrices by checked denominator clearing. `integer_det`
certifies triangular matrices directly, otherwise searching successive primes
and checking only the successful elimination product's lower triangle and
diagonal. Positive-characteristic fields retain Mathlib's full-rank fallback.
Named and local vectors and custom columns are resolved before evaluation.
Stored `first_coeffs` proofs are reused within their actual ranges; remaining
entries use coefficient automation. Symbolic goals retain the simplification
and ring-arithmetic fallback.
-/

public meta section

open Lean Meta Elab Tactic Qq

namespace WeightTwoCusps.Tactic

initialize registerTraceClass `Tactic.cusp_basis

/-- Expose a named matrix without reducing a vector literal to `Fin.cases`.
Keeping the literal lets the vector simprocs handle arbitrary numeric indices. -/
private partial def exposeCoefficientMatrix (matrix : Expr) : MetaM Expr := do
  checkSystem "cusp_basis"
  let matrix := Sym.etaReduce matrix.consumeMData
  if let .fvar id := matrix then
    if let some value := (← id.getDecl).value? then
      return ← exposeCoefficientMatrix value
  if matrix.isAppOf ``qExpansionMatrix || matrix.isLambda then return matrix
  if (← Mathlib.Tactic.Matrix.matchMatrixLit? matrix (closed := false)).isSome then
    return matrix
  let some body ← unfoldDefinition? matrix (ignoreTransparency := true) | return matrix
  if body == matrix then return matrix
  exposeCoefficientMatrix body

/-- Unfold vector aliases while retaining the vector-notation constructor. -/
private partial def exposeCoefficientVector (n : Expr) (v : Expr) : MetaM Expr := do
  checkSystem "cusp_basis"
  let v := Sym.etaReduce v.consumeMData
  if let .fvar id := v then
    if let some value := (← id.getDecl).value? then
      return ← exposeCoefficientVector n value
  let (entries, _, _) ← Matrix.matchVecConsPrefix n v
  if let some size ← getNatValue? n then
    if entries.length == size then return v
  if v.isLambda then return v
  let some body ← unfoldDefinition? v (ignoreTransparency := true) | return v
  if body == v then return v
  exposeCoefficientVector n body

/-- Read a coefficient list, including Lean's shared `let`-encoded literals. -/
private partial def coefficientListEntries? (rhs : Expr)
    (entries : Array Expr := #[]) : MetaM (Option (Array Expr)) := do
  match_expr ← whnfR rhs with
  | List.nil _ => return some entries
  | List.cons _ entry rest => coefficientListEntries? rest (entries.push entry)
  | _ => return none

/-- Resolve forms and column indices before normalizing q-expansions. This
keeps named vectors and arbitrarily large vector indices out of the analytic
coercions handled by the coefficient simprocs. -/
private def coefficientMatrixEntries? (n : Nat) (matrix : Expr) :
    MetaM (Option (Array (Array Expr) × Array (Array (Option Simp.Result)))) := do
  unless matrix.isAppOf ``qExpansionMatrix do return none
  let args := matrix.getAppArgs
  have Γ : Q(Subgroup (GL (Fin 2) ℝ)) := args[0]!
  have k : Q(ℤ) := args[1]!
  have h : Q(ℝ) := args[args.size - 3]!
  let v ← exposeCoefficientVector (toExpr n) args[args.size - 2]!
  let c ← exposeCoefficientVector (toExpr n) args[args.size - 1]!
  let (forms, _, _) ← Matrix.matchVecConsPrefix (toExpr n) v
  let (columns, _, _) ← Matrix.matchVecConsPrefix (toExpr n) c
  let degrees ← (Array.range n).mapM fun j => do
    let jE ← mkFinLitQ n j
    whnfD (if columns.length == n then columns[j]! else mkApp c jE)
  let mut precision := 0
  for degree in degrees do
    if let some index ← getNatValue? degree then precision := max precision (index + 1)
  let periodOne ← isDefEq h q((1 : ℝ))
  let prefixCtx ← Simp.mkContext {} (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let prefixSimprocs := #[← Simp.getSimprocs]
  let mut rows := #[]
  let mut prefixResults := #[]
  let mut boundCache : Std.HashMap (Nat × Nat) Expr := {}
  for i in [:n] do
    let iE ← mkFinLitQ n i
    have f : Q(CuspForm $Γ $k) :=
      if forms.length == n then forms[i]! else (mkApp v iE).headBeta
    let mut prefix? ← do
      unless periodOne do return none
      let .const name _ := f.getAppFn | return none
      let extended := name.appendAfter "_basis_coeffs"
      let name := if (← getEnv).contains extended then extended else name.appendAfter "_first_coeffs"
      unless (← getEnv).contains name do return none
      let proof ← mkConstWithFreshMVarLevels name
      let some (_, lhs, rhs) := (← inferType proof).eq? | return none
      unless lhs.isAppOfArity ``first_coeffs 2 do return none
      let count := lhs.getAppArgs[0]!
      let some value ← getNatValue? count | return none
      let some storedEntries ← coefficientListEntries? rhs | return none
      pure (some (proof, count, value, some storedEntries))
    if periodOne && precision > (prefix?.map (fun (_, _, count, _) => count)).getD 0 then
      -- Missing columns share one coefficient computation per form, rather
      -- than rebuilding an Euler-unit table independently for every entry.
      have count : Q(ℕ) := toExpr precision
      let (result, _) ← simp q(first_coeffs $count $f) prefixCtx prefixSimprocs
      if let some entries ← coefficientListEntries? result.expr then
        let proof ← result.getProof
        prefix? := some (proof, count, precision, some entries)
    let mut row := #[]
    let mut checkedRow := #[]
    for j in [:n] do
      have degree : Q(ℕ) := degrees[j]!
      row := row.push q((UpperHalfPlane.qExpansion $h $f).coeff $degree)
      let mut checkedEntry := none
      if let some (prefixProof, count, value, storedEntries?) := prefix? then
        if let some index ← getNatValue? degree then
          if index < value then
            have count : Q(ℕ) := count
            let hbound ← if let some proof := boundCache[(value, index)]? then pure proof
              else mkDecideProofQ q($degree < $count)
            boundCache := boundCache.insert (value, index) hbound
            let proof ← mkAppM ``qExpansion_coeff_eq_of_first_coeffs
              #[prefixProof, degree, hbound]
            let proof ← if let some storedEntries := storedEntries? then do
                if index < storedEntries.size then
                  let some (_, lhs, _) := (← inferType proof).eq?
                    | throwError "cusp_basis: expected a coefficient equality"
                  pure (mkExpectedPropHint proof (← mkEq lhs storedEntries[index]!))
                else pure proof
              else pure proof
            let some (_, _, rhs) := (← inferType proof).eq?
              | throwError "cusp_basis: expected a coefficient equality"
            checkedEntry := some { expr := rhs, proof? := some proof }
      checkedRow := checkedRow.push checkedEntry
    rows := rows.push row
    prefixResults := prefixResults.push checkedRow
  return some (rows, prefixResults)

/-- Assemble equality of vector literals from checked entry equalities. -/
private def vectorLiteralEq {u : Level} (α : Q(Type u)) (n : Nat)
    (proofs : Array Expr) : MetaM Expr := do
  have empty : Q(Fin 0 → $α) := q(Matrix.vecEmpty)
  let mut left : Expr := empty
  let mut right : Expr := empty
  let mut proof : Expr := q(Eq.refl $empty)
  for k in [:n] do
    let entryProof := proofs[n - k - 1]!
    let some (_, a, b) := (← inferType entryProof).eq?
      | throwError "cusp_basis: expected an entry equality"
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

/-- Read both kernel integer constructors and standard numeral syntax. -/
private def reducedIntValue? (e : Expr) : MetaM (Option Int) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Int.ofNat 1 || e.isAppOfArity ``Int.negSucc 1 then
    let argument ← withTransparency .all <| whnf e.appArg!
    let some value ← getNatValue? argument | return none
    return some (if e.isAppOf ``Int.ofNat then Int.ofNat value else Int.negSucc value)
  getIntValue? e

/-- Reduce closed rational and integer computations before simplification.
The proposed numeral is justified by kernel-checked definitional equality. -/
private def normalizeComputableEntry? (R entry : Expr) : MetaM (Option Simp.Result) := do
  let R ← whnfD R
  if R == q(ℚ) then
    let numerator ← mkAppM ``_root_.Rat.num #[entry]
    let denominator ← mkAppM ``_root_.Rat.den #[entry]
    let numerator ← withTransparency .all <| whnf numerator
    let denominator ← withTransparency .all <| whnf denominator
    let some num ← reducedIntValue? numerator | return none
    let some den ← getNatValue? denominator | return none
    if den == 0 then return none
    let numE : Q(ℚ) ← Mathlib.Tactic.Echelon.mkIntNumeral q(ℚ) num
    let value ← if den == 1 then pure numE else do
      let denE : Q(ℚ) ← Mathlib.Tactic.Echelon.mkIntNumeral q(ℚ) (den : Int)
      pure q($numE / $denE)
    let proof := mkExpectedPropHint (← mkEqRefl value) (← mkEq entry value)
    return some { expr := value, proof? := some proof }
  if R == q(ℤ) then
    let entryValue ← withTransparency .all <| whnf entry
    let some num ← reducedIntValue? entryValue | return none
    let value ← Mathlib.Tactic.Echelon.mkIntNumeral q(ℤ) num
    let proof := mkExpectedPropHint (← mkEqRefl value) (← mkEq entry value)
    return some { expr := value, proof? := some proof }
  return none

/-- Clear denominators row by row, certify the scaling equality, then use the
integer determinant tactic. The matrix arithmetic certificate is independent
of the source of its entries. -/
private def rationalDeterminant (n : Nat) (matrix : Q(Matrix (Fin $n) (Fin $n) ℚ))
    (entries : Array (Array Expr)) : MetaM Expr := do
  let mut cache : Std.HashMap Expr Rat := {}
  let mut fractions := #[]
  for row in entries do
    let mut values := #[]
    for entry in row do
      let value ← if let some v := cache[entry]? then pure v
        else Mathlib.Tactic.Echelon.evalRatEntry true entry
      cache := cache.insert entry value
      values := values.push value
    fractions := fractions.push values
  let scales : Array Nat := fractions.map fun row =>
    row.foldl (fun (s : Nat) (r : Rat) => s.lcm r.den) 1
  let integers := fractions.mapIdx fun i row => row.map fun r =>
    r.num * ((scales[i]! / r.den : Nat) : Int)
  let data := Mathlib.Tactic.Echelon.ListMatrixLit.ofArray q(inferInstance : Zero ℤ)
    n n (integers.map (·.map toExpr))
  have B : Q(Matrix (Fin $n) (Fin $n) ℤ) := data.matrix
  have s : Q(Fin $n → ℚ) := PiFin.mkLiteralQ (α := q(ℚ)) (n := n)
    fun i => toExpr (scales[i.val]! : Rat)
  let mut arithmeticCache : Std.HashMap (Nat × Expr) Expr := {}
  let mut rowProofs := #[]
  let mut leftRows := #[]
  for i in [:n] do
    have scale : Q(ℚ) := toExpr (scales[i]! : Rat)
    let mut proofs := #[]
    let mut left := #[]
    for j in [:n] do
      have entry : Q(ℚ) := (entries[i]!)[j]!
      have z : Q(ℤ) := toExpr ((integers[i]!)[j]!)
      let prop := q($scale * $entry = ($z : ℚ))
      let key : Nat × Expr := (scales[i]!, entry)
      let proof ← if let some proof := arithmeticCache[key]? then pure proof
        else checkedDeterminantLemma prop (mkExpectedPropHint q(Eq.refl ($z : ℚ)) prop)
      arithmeticCache := arithmeticCache.insert key proof
      proofs := proofs.push proof
      left := left.push q($scale * $entry)
    rowProofs := rowProofs.push (← vectorLiteralEq q(ℚ) n proofs)
    leftRows := leftRows.push (PiFin.mkLiteralQ (α := q(ℚ)) (n := n) fun j => left[j.val]!)
  have expanded : Q(Matrix (Fin $n) (Fin $n) ℚ) := q(Matrix.of
    $(PiFin.mkLiteralQ (α := q(Fin $n → ℚ)) (n := n) fun i => leftRows[i.val]!))
  have pointwise : Q(Matrix (Fin $n) (Fin $n) ℚ) := q(fun i j ↦ $s i * $matrix i j)
  have hexpand : Q($expanded = $pointwise) :=
    mkExpectedPropHint q(Matrix.etaExpand_eq $pointwise) q($expanded = $pointwise)
  let hrows ← vectorLiteralEq q(Fin $n → ℚ) n rowProofs
  let castMap ← mkAppM ``matrix_ofLists_map #[q(fun z : ℤ ↦ (z : ℚ)),
    q(Int.cast_zero (R := ℚ)), toExpr n, toExpr n, data.lit]
  let some (_, castLeft, _) := (← inferType castMap).eq?
    | throwError "cusp_basis_det: expected a matrix cast equality"
  let hrows := mkExpectedPropHint hrows (← mkEq expanded castLeft)
  let hscaled ← mkEqTrans q(matrix_diagonal_mul_eq $s $matrix) (← mkEqSymm hexpand)
  let heq ← mkEqTrans (← mkEqTrans hscaled hrows) castMap
  let hB ← proveIntegerDeterminant n B (integers.map (·.map toExpr))
  mkAppM ``matrix_det_ne_zero_of_int_rowScale #[matrix, B, s, heq, hB]

private def characteristicZeroField? {u : Level} (α : Q(Type u)) :
    MetaM (Option (Expr × Expr)) := do
  let .some field ← trySynthInstanceQ q(Field $α) | return none
  let .some charZero ← trySynthInstanceQ q(CharZero $α) | return none
  return some (field, charZero)

/-- Integral coefficients go straight to integers, avoiding a rational matrix
and a second denominator-clearing equality. Cast equalities are proved and
shared by value, rather than assumed to hold definitionally. -/
private def integralDeterminant? {u : Level} (α : Q(Type u)) (n : Nat)
    (original raw : Q(Matrix (Fin $n) (Fin $n) $α)) (isLiteral : Bool)
    (normalized : Array (Array Simp.Result)) : MetaM (Option Expr) := do
  unless (← characteristicZeroField? α).isSome do return none
  let _ ← synthInstanceQ q(Field $α)
  let _ ← synthInstanceQ q(CharZero $α)
  let mut values := #[]
  let mut valueCache : Std.HashMap Expr Int := {}
  for row in normalized do
    let mut result := #[]
    for entry in row do
      let value? ← if let some value := valueCache[entry.expr]? then pure (some value) else do
        let value ← Mathlib.Tactic.Echelon.evalRatEntry true entry.expr
        pure (if value.den == 1 then some value.num else none)
      let some value := value? | return none
      valueCache := valueCache.insert entry.expr value
      result := result.push value
    values := values.push result
  let data := Mathlib.Tactic.Echelon.ListMatrixLit.ofArray q(inferInstance : Zero ℤ)
    n n (values.map (·.map toExpr))
  let mut castCache : Std.HashMap Expr Expr := {}
  let mut rows := #[]
  for i in [:n] do
    let mut proofs := #[]
    for j in [:n] do
      let result := (normalized[i]!)[j]!
      have entry : Q($α) := result.expr
      have z : Q(ℤ) := toExpr ((values[i]!)[j]!)
      let cast ← if let some cast := castCache[result.expr]? then pure cast else do
        let prop := q($entry = ($z : $α))
        let ⟨true, proof⟩ ← Mathlib.Meta.NormNum.deriveBool prop
          | throwError "matrix_det: could not certify an integer cast"
        pure proof
      castCache := castCache.insert result.expr cast
      proofs := proofs.push (← mkEqTrans (← result.getProof) cast)
    rows := rows.push (← vectorLiteralEq α n proofs)
  let vectorProof ← vectorLiteralEq q(Fin $n → $α) n rows
  let castMap ← mkAppM ``matrix_ofLists_map #[q(fun z : ℤ ↦ (z : $α)),
    q(Int.cast_zero (R := $α)), toExpr n, toExpr n, data.lit]
  let some (_, castLeft, _) := (← inferType castMap).eq?
    | throwError "matrix_det: expected an integer matrix cast equality"
  let hnorm := mkExpectedPropHint vectorProof (← mkEq raw castLeft)
  have hexpand : Q($raw = $original) := if isLiteral then
      mkExpectedPropHint q(Eq.refl $original) q($raw = $original)
    else mkExpectedPropHint q(Matrix.etaExpand_eq $original) q($raw = $original)
  let heq ← mkEqTrans (← mkEqTrans (← mkEqSymm hexpand) hnorm) castMap
  let hB ← proveIntegerDeterminant n data.matrix (values.map (·.map toExpr))
  return some (← mkAppM ``matrix_det_ne_zero_of_int_eq #[original, data.matrix, heq, hB])

/-- Materialize a coefficient matrix, then use general determinant automation.
Neither the dimension, the modulus, nor the pivots are hard-coded. -/
private def proveCoefficientDeterminant (goal : MVarId) (materializeOnly : Bool := false) :
    MetaM Unit := do
  let target ← instantiateMVars (← goal.getType)
  let_expr Ne _ determinant rhs := target
    | throwError "cusp_basis_det expects a determinant disequality"
  unless determinant.isAppOf ``Matrix.det do
    throwError "cusp_basis_det expects a determinant"
  let original := determinant.appArg!
  let matrixType ← instantiateMVars (← inferType original)
  let_expr Matrix rowTy colTy R := matrixType
    | throwError "cusp_basis_det expects a matrix"
  let_expr Fin nE := rowTy | throwError "cusp_basis_det expects Fin indices"
  let_expr Fin mE := colTy | throwError "cusp_basis_det expects Fin indices"
  let some n ← getNatValue? (← whnfD nE)
    | throwError "cusp_basis_det expects a numeral size"
  let some m ← getNatValue? (← whnfD mE)
    | throwError "cusp_basis_det expects a numeral size"
  unless n == m do throwError "cusp_basis_det expects a square matrix"
  let u ← getDecLevel R
  have α : Q(Type u) := R
  unless ← isDefEq rhs (← mkNumeral R 0) do
    throwError "cusp_basis_det expects comparison with zero"
  have original : Q(Matrix (Fin $n) (Fin $n) $α) := original
  let exposed ← exposeCoefficientMatrix original
  let literal? ← Mathlib.Tactic.Matrix.matchMatrixLit? exposed (closed := false)
  let isLiteral := literal?.isSome
  let bodyExpr ← if isLiteral then pure exposed else whnfD exposed
  have body : Q(Matrix (Fin $n) (Fin $n) $α) := bodyExpr
  let coefficientEntries ← coefficientMatrixEntries? n exposed
  let rawEntries ← match literal?, coefficientEntries with
    | some (_, _, _, es), _ => pure es
    | _, some (es, _) => pure es
    | none, none => (Array.range n).mapM fun rowIndex => do
      let i ← mkFinLitQ n rowIndex
      (Array.range n).mapM fun columnIndex => do
        let j ← mkFinLitQ n columnIndex
        pure q($body $i $j)
  if R == q(ℚ) && isLiteral then
    goal.assign (← rationalDeterminant n original rawEntries)
    return
  let rawRows := rawEntries.map fun row =>
    PiFin.mkLiteralQ (u := u) (α := α) (n := n) fun j => row[j.val]!
  let rawVector := PiFin.mkLiteralQ (u := u) (α := q(Fin $n → $α))
    (n := n) fun i => rawRows[i.val]!
  have raw : Q(Matrix (Fin $n) (Fin $n) $α) :=
    if isLiteral then exposed else q(Matrix.of $rawVector)
  let mut thms ← getSimpTheorems
  thms ← thms.addConst ``PowerSeries.coeff_expand
  thms ← thms.addConst ``PowerSeries.constantCoeff_expand
  let ctx ← Simp.mkContext {} (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let simprocs := #[← Simp.getSimprocs]
  trace[Tactic.cusp_basis] "normalizing a {n} by {n} matrix"
  let mut direct : Nat := 0
  let mut entryCache : Std.HashMap Expr Simp.Result := {}
  let mut normalized := #[]
  for i in [:n] do
    let mut results := #[]
    for j in [:n] do
      let entry := (rawEntries[i]!)[j]!
      let checked := coefficientEntries.bind fun (_, rows) => (rows[i]!)[j]!
      let result ← if let some result := checked then pure result
        else if let some result := entryCache[entry]? then pure result
        else if let some result ← normalizeComputableEntry? R entry then do
          direct := direct + 1
          pure result
        else Mathlib.Meta.NormNum.deriveSimp ctx simprocs true entry
      entryCache := entryCache.insert entry result
      results := results.push result
    normalized := normalized.push results
  trace[Tactic.cusp_basis] "normalized entries; {direct} used direct reduction"
  if materializeOnly then
    let data := Mathlib.Tactic.Echelon.ListMatrixLit.ofArray
      (α := α) (← synthInstanceQ q(Zero $α)) n n (normalized.map (·.map (·.expr)))
    let rows ← normalized.mapM fun row => do
      vectorLiteralEq α n (← row.mapM Simp.Result.getProof)
    let hrows ← vectorLiteralEq q(Fin $n → $α) n rows
    let hnorm := mkExpectedPropHint hrows (← mkEq raw data.matrix)
    have hexpand : Q($raw = $original) := if isLiteral then
        mkExpectedPropHint q(Eq.refl $original) q($raw = $original)
      else mkExpectedPropHint q(Matrix.etaExpand_eq $original) q($raw = $original)
    let heq ← mkEqTrans (← mkEqSymm hexpand) hnorm
    let rewritten ← goal.rewrite target heq
    discard <| goal.replaceTargetEq rewritten.eNew rewritten.eqProof
    return
  if let some proof ← integralDeterminant? α n original raw isLiteral normalized then
    goal.assign proof
    return
  -- Transport characteristic-zero matrices to rationals before elimination.
  -- Repeated small entries share both decoding and the cast equality proof.
  let mut rationalMatrix? : Option (Expr × Array (Array Expr)) := none
  if R != q(ℚ) then
    let rationalField? ← characteristicZeroField? α
    if let some (_field, _charZero) := rationalField? then
      let mut castCache : Std.HashMap Expr (Expr × Expr) := {}
      let mut rationalEntries := #[]
      let mut castResults := #[]
      for row in normalized do
        let mut rationalRow := #[]
        let mut castRow := #[]
        for result in row do
          let (value, castProof) ← if let some cached := castCache[result.expr]? then pure cached
            else do
              let value ← Mathlib.Tactic.Echelon.evalRatEntry true result.expr
              have valueE : Q(ℚ) := toExpr value
              have entry : Q($α) := result.expr
              let _ ← synthInstanceQ q(Field $α)
              let _ ← synthInstanceQ q(CharZero $α)
              let prop := q($entry = ($valueE : $α))
              let ⟨true, proof⟩ ← Mathlib.Meta.NormNum.deriveBool prop
                | throwError "cusp_basis_det could not certify a rational entry"
              pure (valueE, proof)
          castCache := castCache.insert result.expr (value, castProof)
          let some (_, _, castValue) := (← inferType castProof).eq?
            | throwError "cusp_basis_det: expected a cast equality"
          let castResult : Simp.Result := {
            expr := castValue
            proof? := some (← mkEqTrans (← result.getProof) castProof) }
          castRow := castRow.push castResult
          rationalRow := rationalRow.push value
        rationalEntries := rationalEntries.push rationalRow
        castResults := castResults.push castRow
      normalized := castResults
      let rationalRows := rationalEntries.map fun row =>
        PiFin.mkLiteralQ (α := q(ℚ)) (n := n) fun j => row[j.val]!
      let rationalVector := PiFin.mkLiteralQ (α := q(Fin $n → ℚ))
        (n := n) fun i => rationalRows[i.val]!
      rationalMatrix? := some (q(Matrix.of $rationalVector), rationalEntries)
  let normalizedRows := normalized.map fun row =>
    PiFin.mkLiteralQ (u := u) (α := α) (n := n) fun j => row[j.val]!.expr
  let normalizedVector := PiFin.mkLiteralQ (u := u) (α := q(Fin $n → $α))
    (n := n) fun i => normalizedRows[i.val]!
  have matrix : Q(Matrix (Fin $n) (Fin $n) $α) := q(Matrix.of $normalizedVector)
  let rowEqualities : MetaM (Array Expr) := normalized.mapM fun row => do
    let proofs ← row.mapM Simp.Result.getProof
    vectorLiteralEq α n proofs
  let rowProofs ← rowEqualities
  let vectorProof ← vectorLiteralEq (u := u) q(Fin $n → $α) n rowProofs
  let ofFn := q(fun rows : Fin $n → Fin $n → $α ↦ Matrix.of rows)
  let normalizedProof ← mkAppM ``congrArg #[ofFn, vectorProof]
  let normalizedProof := mkExpectedPropHint normalizedProof (← mkEq raw matrix)
  let hexp ← if isLiteral then
      pure (mkExpectedPropHint (← mkEqRefl original) (← mkEq raw original))
    else
      pure (mkExpectedPropHint q(Matrix.etaExpand_eq $original) (← mkEq raw original))
  let hmatrix ← mkEqTrans (← mkEqSymm hexp) normalizedProof
  let rewritten ← goal.rewrite target hmatrix
  let goal ← goal.replaceTargetEq rewritten.eNew rewritten.eqProof
  let some (_, _, _, matrixEntries) ←
      Mathlib.Tactic.Matrix.matchMatrixLit? matrix (closed := false)
    | throwError "cusp_basis_det could not materialize the matrix"
  let .ok rα ← Mathlib.Tactic.Echelon.inferBareissRing α
    | throwError "cusp_basis_det expects entries in a commutative domain"
  let rankExpr ← mkAppM ``Matrix.rank #[matrix]
  trace[Tactic.cusp_basis] "constructing the elimination certificate"
  if let some (rationalMatrix, rationalEntries) := rationalMatrix? then
    have rationalMatrix : Q(Matrix (Fin $n) (Fin $n) ℚ) := rationalMatrix
    let hdet ← rationalDeterminant n rationalMatrix rationalEntries
    let proof ← mkAppOptM ``matrix_det_ne_zero_of_rat #[some α, none, none,
      some (toExpr n), some rationalMatrix, some hdet]
    goal.assign (mkExpectedPropHint proof (← goal.getType))
    return
  if R == q(ℚ) then
    goal.assign (← rationalDeterminant n matrix matrixEntries)
    return
  if R == q(ℤ) then
    goal.assign (← proveIntegerDeterminant n matrix matrixEntries)
    return
  let rankResult ← Mathlib.Tactic.Echelon.normalizeRank rα rankExpr matrix matrixEntries
  let some rank ← getNatValue? rankResult.expr
    | throwError "cusp_basis_det could not compute the rank"
  unless rank == n do
    throwError "cusp_basis_det: the matrix has rank {rank}, expected {n}"
  trace[Tactic.cusp_basis] "certified rank {rank}"
  let hcard ← mkEqSymm q(Fintype.card_fin $n)
  let hrank ← mkEqTrans (← rankResult.getProof) hcard
  let proof ← mkAppM ``matrix_det_ne_zero_of_rank_eq_card #[matrix, hrank]
  unless ← isDefEq (← inferType proof) (← goal.getType) do
    throwError "cusp_basis_det expects determinant nonzeroness over a field"
  goal.assign proof

elab "matrix_det_numeric" : tactic => withMainContext do
  proveCoefficientDeterminant (← getMainGoal)
  replaceMainGoal []

/-- Replace a q-expansion determinant by a compact, checked `ofLists` table.
Coefficient normalization is independent of determinant certification. -/
elab "q_expansion_matrix" : tactic => withMainContext do
  let goal ← getMainGoal
  proveCoefficientDeterminant goal (materializeOnly := true)
  let proof ← instantiateMVars (mkMVar goal)
  replaceMainGoal (← getMVars proof).toList

/-- Locate the local Determinant producer also when Lean starts outside the project.
Windows uses the package's Sage/WSL adapter; cache lookup uses standard Python.
Witness locality is determined by the calling source file, not the producer. -/
elab "cusp_basis_det_config%" : term => do
  -- `lake build` supplies import artifacts without setting `LEAN_SRC_PATH`.
  -- Resolve the configured local dependency from the caller's Lake project instead.
  let source ← IO.FS.realPath (← getFileName)
  let mut project := source.parent.getD source
  repeat
    if (← (project / "lakefile.toml").pathExists) ||
        (← (project / "lakefile.lean").pathExists) then break
    let some parent := project.parent | throwError "cannot locate the Lake project"
    if parent == project then throwError "cannot locate the Lake project"
    project := parent
  let root ← IO.FS.realPath (project / ".." / "Determinant")
  let rootSyntax := Syntax.mkStrLit root.toString
  let lookup := Syntax.mkStrLit (root / "scripts" / "cache_lookup.py").toString
  let config ← if System.Platform.isWindows then
      let adapter := Syntax.mkStrLit (root / "scripts" / "Invoke-SageWSL.ps1").toString
      `(term|
        ({ kind := "unit-upper-product"
           executable := "powershell.exe"
           arguments := #["-NoProfile", "-ExecutionPolicy", "Bypass", "-File", $adapter]
           lookupArguments := #[$lookup]
           workingDirectory := some $rootSyntax } : Determinant.Tactic.CacheConfig))
    else
      let script := Syntax.mkStrLit (root / "scripts" / "det_certificate.py").toString
      `(term|
        ({ kind := "unit-upper-product"
           lookupArguments := #[$lookup]
           arguments := #[$script] } : Determinant.Tactic.CacheConfig))
  Term.elabTerm config none

/-- Try triangularity using symbolic simplification. Numerical triangularity
is also detected by the integer backend after coefficient normalization. -/
macro "matrix_det_triangular" : tactic =>
  `(tactic| first
    | (solve
      | refine (Matrix.IsUpperTriangular.det_ne_zero_iff ?_).mpr ?_
        · intro i j hij
          have hne : i ≠ j := by intro h; subst j; exact lt_irrefl _ hij
          simp_all [Matrix.diagonal_apply]
        · intro i; simp_all [Matrix.diag_apply])
    | (solve
      | refine (Matrix.IsLowerTriangular.det_ne_zero_iff ?_).mpr ?_
        · intro i j hij
          have hne : i ≠ j := by intro h; subst j; exact lt_irrefl _ hij
          simp_all [Matrix.diagonal_apply]
        · intro i; simp_all [Matrix.diag_apply]))

/-- Expand determinants only in dimensions at most three. This guard avoids
accidentally invoking a large determinant evaluator during a cheap fallback. -/
elab "matrix_det_small" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some (_, lhs, _) := target.eq? <|> (if target.isAppOfArity ``Ne 3 then
      some (target.getAppArgs[0]!, target.getAppArgs[1]!, target.getAppArgs[2]!) else none)
    | throwError "matrix_det_small expects a determinant comparison"
  unless lhs.isAppOf ``Matrix.det do throwError "matrix_det_small expects a determinant"
  let matrixType ← inferType lhs.appArg!
  let_expr Matrix rowTy _ _ := matrixType | throwError "matrix_det_small expects a matrix"
  let_expr Fin n := rowTy | throwError "matrix_det_small expects Fin indices"
  let some n ← getNatValue? (← whnfD n) | throwError "matrix_det_small expects a numeral size"
  unless n ≤ 3 do throwError "matrix_det_small is restricted to dimensions at most three"
  evalTactic (← `(tactic| solve
    | norm_num [qExpansionMatrix, PowerSeries.coeff_expand,
        PowerSeries.constantCoeff_expand, Matrix.det_fin_zero, Matrix.det_fin_one,
        Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix] <;> ring))

/-- Nonzero determinant automation, ordered from structural proofs to exact
integer reduction and successive modular certificates. Also supports small
symbolic determinant identities. -/
macro "matrix_det" : tactic =>
  `(tactic| first
    | assumption
    | (solve | simp only [Matrix.det_one, ne_eq, one_ne_zero, not_false_eq_true])
    | matrix_det_triangular
    | matrix_det_small
    | matrix_det_numeric)

/-- Coefficient determinant frontend, retained under its established name. -/
macro "cusp_basis_det" : tactic => `(tactic| matrix_det)

/-- Dimension arithmetic, independently of coefficient or determinant proofs. -/
elab "cusp_basis_dimension" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some (_, lhs, _) := target.eq?
    | throwError "cusp_basis_dimension expects a dimension equality"
  unless lhs.isAppOf ``Module.finrank || lhs.isAppOf ``gamma0Dimension ||
      lhs.isAppOf ``gamma1Dimension || lhs.isAppOf ``gammaDimension do
    throwError "cusp_basis_dimension expects a dimension equality"
  evalTactic (← `(tactic| first | assumption | (solve | norm_num)))

/-- Strict period membership, independently of dimension and coefficients. -/
macro "cusp_basis_period" : tactic =>
  `(tactic| first | assumption | (solve | norm_num))

/-- Independence from the first positive q-coefficients. -/
macro "cusp_basis_independent" : tactic =>
  `(tactic|
    (apply linearIndependent_of_qExpansionMatrix_det_ne_zero
      (h := 1) (by positivity) (by cusp_basis_period) _ (fun i ↦ i.val + 1)
     cusp_basis_det))

/-- Independence using explicitly selected q-indices. -/
macro "cusp_basis_independent" " using " c:term : tactic =>
  `(tactic|
    (apply linearIndependent_of_qExpansionMatrix_det_ne_zero
      (h := 1) (by positivity) (by cusp_basis_period) _ $c
     cusp_basis_det))

/-- Compatibility dispatcher. Constructors use the specialized tactics. -/
macro "cusp_basis" : tactic =>
  `(tactic| first
    | assumption
    | cusp_basis_dimension
    | cusp_basis_det
    | cusp_basis_independent)

/-- Prove independence using an explicitly selected vector of q-indices. -/
macro "cusp_basis" " using " c:term : tactic =>
  `(tactic| cusp_basis_independent using $c)

end WeightTwoCusps.Tactic
