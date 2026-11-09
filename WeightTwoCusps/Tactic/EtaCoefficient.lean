module

public import WeightTwoCusps.EtaQuotient.QExpansion.PackedCertificates
public import WeightTwoCusps.EtaQuotient.QExpansion.ModularForm
public import WeightTwoCusps.Oldforms.QExpansion
public import WeightTwoCusps.Tactic.EtaSimps
public meta import Mathlib.Util.Qq
public meta import Lean.Elab.Tactic.Simproc
public meta import Mathlib.Tactic.NormNum

/-!
# Numeral evaluation of eta-quotient q-expansion coefficients

`simp` evaluates coefficients at numeral indices and levels with closed integer
exponent functions. The proposed values and intermediate tables are all checked
by the kernel. Signed exponents are supported. The simproc applies when the
infinity sum is nonnegative and divisible by 24.
`first_coeffs m f` is evaluated in one batch using a shared intermediate table.
Powers use repeated squaring, sparse tables omit trailing zeros, and convolution
certificates use packed integer products with checked norm bounds. Arithmetic
lemmas are checked once and reused, just as with `decide +kernel`.
Degeneracy lifts, ambient-level changes, and named aliases are supported. Positive
periods are moved through lifts and normalized to period one when integral.
-/

public meta section

open Lean Meta Simp Qq
open WeightTwoCusps.EtaQuotient

namespace WeightTwoCusps.Tactic

/-- A proposed finite table together with its checked agreement proof. -/
structure EtaCoefficientTable where
  values : List Int
  proof : Expr

private def etaTableAt (t : List Int) (n : Nat) : Int := t[n]?.getD 0

private def etaOneTable (_p : Nat) : List Int := [1]

private def etaTrimTable (t : List Int) : List Int :=
  (t.reverse.dropWhile (· == 0)).reverse

private def etaConvolveTables (a b : List Int) (p : Nat) : List Int :=
  Id.run do
    let a := a.toArray
    let b := b.toArray
    let mut result := Array.replicate p 0
    for i in [:min p a.size] do
      if a[i]! != 0 then
        for j in [:min (p - i) b.size] do
          result := result.modify (i + j) (· + a[i]! * b[j]!)
    return etaTrimTable result.toList

private def etaInverseTable (a : List Int) (p : Nat) : List Int := Id.run do
  let a := a.toArray
  let mut t : Array Int := #[]
  for n in [:p] do
    let mut v := if n = 0 then 1 else 0
    for k in [:n] do
      v := v - a[n - k]?.getD 0 * t[k]!
    t := t.push v
  return etaTrimTable t.toList

private def etaEulerValue (n : Nat) : Int :=
  ((List.range (2 * Nat.sqrt n + 1)).map fun j =>
    let k := (j : Int) - (Nat.sqrt n : Int)
    if k * (3 * k - 1) / 2 = (n : Int) then
      if k % 2 = 0 then 1 else -1
    else 0).sum

private def etaEulerTable (m p : Nat) : List Int :=
  etaTrimTable ((List.range p).map fun n => if n % m = 0 then etaEulerValue (n / m) else 0)

private def etaCheck (proposition : Expr) : MetaM Expr := do
  let dec ← withTransparency .all <| mkDecide proposition
  let refl := mkExpectedPropHint q(Eq.refl true) (← mkEq dec q(true))
  let proof := mkApp3 (mkConst ``of_decide_eq_true) proposition dec.appArg! refl
  -- Check each arithmetic certificate once, as `decide +kernel` does. Later
  -- products refer to the checked lemma instead of duplicating its reduction.
  let name ← withOptions (Lean.Elab.async.set · false) <|
    mkAuxLemma [] proposition proof
  return mkConst name

private def etaClosedInt (e : Expr) : MetaM (Option Int) := withTransparency .all do
  let e ← whnf e
  match_expr e with
  | Int.ofNat n => return (← getNatValue? (← whnf n)).map Int.ofNat
  | Int.negSucc n => return (← getNatValue? (← whnf n)).map Int.negSucc
  | _ => getIntValue? e

private def etaCertifyTable (a : Expr) (p : Nat) (values : List Int) :
    MetaM EtaCoefficientTable := do
  let check ← mkAppM ``checkCoefficientPrefix #[a, toExpr (0 : Nat), toExpr p, toExpr values]
  let proof ← etaCheck (← mkEq check q(true))
  return ⟨values, mkAppN (mkConst ``coefficient_table_of_check)
    #[a, toExpr p, toExpr values, proof]⟩

private def etaTableFunction (table : EtaCoefficientTable) : MetaM Expr := do
  let type ← inferType table.proof
  unless type.isAppOfArity ``IsCoefficientTable 3 do
    throwError "eta_coeff: expected a coefficient-table certificate"
  return type.getAppArgs[0]!

private def etaConvolutionCertificate (a b : List Int) (p : Nat)
    (values : List Int) : MetaM EtaCoefficientTable := do
  if a == [1] then
    return ⟨values, ← mkAppM ``convolution_table_one_left_values #[toExpr p, toExpr b]⟩
  if b == [1] then
    return ⟨values, ← mkAppM ``convolution_table_one_right_values #[toExpr p, toExpr a]⟩
  have ta : Q(List ℤ) := toExpr a
  have tb : Q(List ℤ) := toExpr b
  have tc : Q(List ℤ) := toExpr values
  have precision : Q(ℕ) := toExpr p
  let norm (t : List Int) := t.foldl (fun s z ↦ s + z.natAbs) 0
  have base : Q(ℕ) := toExpr (norm a * norm b + norm values + 1)
  let check ← etaCheck q(tableNorm ($ta) * tableNorm ($tb) + tableNorm ($tc) < $base ∧
    ($base : ℤ) ^ $precision ∣
      evaluateTable ($base) ($ta) * evaluateTable ($base) ($tb) - evaluateTable ($base) ($tc))
  return ⟨values, mkAppN (mkConst ``convolution_table_packed)
    #[ta, tb, tc, precision, base, ← mkAppM ``And.left #[check], ← mkAppM ``And.right #[check]]⟩

private partial def etaPowerTable (a : Expr) (base : EtaCoefficientTable) (p k : Nat) :
    MetaM EtaCoefficientTable := do
  if k == 0 then
    return ⟨etaOneTable p, mkApp (mkConst ``oneCoefficient_table) (toExpr p)⟩
  if k == 1 then
    return ⟨base.values, mkAppN (mkConst ``powCoefficient_table_one)
      #[a, toExpr p, toExpr base.values, base.proof]⟩
  let half ← etaPowerTable a base p (k / 2)
  let values := etaConvolveTables half.values half.values p
  let certificate ← etaConvolutionCertificate half.values half.values p values
  let proof := mkAppN (mkConst ``powCoefficient_table_add)
    #[a, toExpr (k / 2), toExpr (k / 2), toExpr p,
      toExpr half.values, toExpr half.values, toExpr values,
      half.proof, half.proof, certificate.proof]
  let mut result : EtaCoefficientTable := ⟨values, proof⟩
  if k % 2 == 1 then
    let values := etaConvolveTables base.values result.values p
    let certificate ← etaConvolutionCertificate base.values result.values p values
    let proof := mkAppN (mkConst ``powCoefficient_table_succ)
      #[a, toExpr (2 * (k / 2)), toExpr p, toExpr base.values, toExpr result.values,
        toExpr values, base.proof, result.proof, certificate.proof]
    result := ⟨values, proof⟩
  return result

private def etaSignedPowerTable (m : Nat) (exponent : Int) (p : Nat) :
    MetaM EtaCoefficientTable := do
  let a ← mkAppM ``EtaQuotient.dilateCoefficient #[toExpr m, mkConst ``eulerCoefficient]
  if exponent = 0 then
    return ⟨etaOneTable p, mkApp (mkConst ``oneCoefficient_table) (toExpr p)⟩
  if p ≤ m then
    let hp ← etaCheck (← mkAppM ``LE.le #[toExpr p, toExpr m])
    let base := mkAppN (mkConst ``dilateCoefficient_table_one_of_le)
      #[mkConst ``eulerCoefficient, toExpr m, toExpr p, mkConst ``eulerCoefficient_zero, hp]
    return ⟨etaOneTable p, mkAppN (mkConst ``zpowCoefficient_table_one_values)
      #[a, toExpr p, base, toExpr exponent]⟩
  let base ← etaCertifyTable a p (etaEulerTable m p)
  if exponent ≥ 0 then
    etaPowerTable a base p exponent.toNat
  else
    let values := etaInverseTable base.values p
    let product ← etaConvolutionCertificate base.values values p [1]
    let constant ← mkAppM ``tableCoefficient #[toExpr base.values, toExpr (0 : Nat)]
    let h0 ← etaCheck (← mkEq constant (toExpr (1 : Int)))
    let recurrence := mkAppN (mkConst ``inverseTable_of_product)
      #[toExpr p, toExpr base.values, toExpr values, h0, product.proof]
    let inverseProof := mkAppN (mkConst ``inverseCoefficient_table)
      #[a, toExpr p, toExpr base.values, toExpr values, base.proof, recurrence]
    let ai ← mkAppM ``inverseCoefficient #[a]
    etaPowerTable ai ⟨values, inverseProof⟩ p exponent.natAbs

private def etaUnitTable (N : Nat) (r : Expr) (p : Nat) : MetaM EtaCoefficientTable := do
  let divisors := if N = 0 then [] else (List.range (N + 1)).filter fun m => N % m = 0
  let mut factors : List EtaCoefficientTable := []
  for m in divisors do
    let exponentExpr ← mkAppM ``EtaQuotient.exponent #[r, toExpr m]
    let some exponent ← etaClosedInt exponentExpr
      | throwError "eta coefficient evaluation requires closed integer exponents"
    let table ← etaSignedPowerTable m exponent p
    factors := table :: factors
  let mut result : EtaCoefficientTable :=
    ⟨etaOneTable p, mkApp (mkConst ``productCoefficient_table_nil) (toExpr p)⟩
  for table in factors do
    let values := etaConvolveTables table.values result.values p
    let certificate ← etaConvolutionCertificate table.values result.values p values
    let a ← etaTableFunction table
    let rest ← etaTableFunction result
    unless rest.isAppOf ``productCoefficient do
      throwError "eta_coeff: expected a product certificate"
    let proof := mkAppN (mkConst ``productCoefficient_table_cons)
      #[a, rest.appArg!, toExpr p, toExpr table.values, toExpr result.values,
        toExpr values, table.proof, result.proof, certificate.proof]
    result := ⟨values, proof⟩
  return result

/-- Evaluate an analytic eta-quotient coefficient using finite checked tables. -/
simproc ↓ etaQuotientCoeff_ofNat
    (PowerSeries.coeff _ (UpperHalfPlane.qExpansion 1 (etaQuotient _ _))) := fun e => do
  have e : Q(ℂ) := e
  let ~q(PowerSeries.coeff $n (UpperHalfPlane.qExpansion 1 (etaQuotient $N $r))) := e
    | return .continue
  let some level ← getNatValue? N | return .continue
  let some degree ← getNatValue? (← whnf n) | return .continue
  if r.hasFVar || r.hasMVar then return .continue
  let sumExpr ← mkAppM ``infinitySum #[N, r]
  let some sum ← etaClosedInt sumExpr | return .continue
  if sum < 0 || sum % 24 != 0 then return .continue
  let order := (sum / 24).toNat
  have v : Q(ℕ) := toExpr order
  let hv : Q(infinitySum $N $r = 24 * ($v : ℤ)) ←
    etaCheck q(infinitySum $N $r = 24 * ($v : ℤ))
  if degree < order then
    let hn : Q($n < $v) ← etaCheck q($n < $v)
    let proof := q(qExpansion_coeff_eq_zero_of_lt $hv $hn)
    return .done { expr := q((0 : ℂ)), proof? := some proof }
  let j := degree - order
  let table ← etaUnitTable level r (j + 1)
  have jExpr : Q(ℕ) := toExpr j
  have p : Q(ℕ) := toExpr (j + 1)
  have t : Q(List ℤ) := toExpr table.values
  have ht : Q(IsCoefficientTable (unitCoefficient $N $r) $p $t) := table.proof
  let hn : Q($jExpr < $p) ← etaCheck q($jExpr < $p)
  let proof := q(qExpansion_coeff_add_of_table $hv $hn $ht)
  have value : Q(ℤ) := toExpr (etaTableAt table.values j)
  return .done { expr := q(($value : ℂ)), proof? := some proof }

/-- Also evaluate after simplification has exposed a bundled constructor's function. -/
simproc etaQuotientCoeff_post
    (PowerSeries.coeff _ (UpperHalfPlane.qExpansion 1 (etaQuotient _ _))) :=
  etaQuotientCoeff_ofNat

/-- Handle coefficient zero after `simp` has rewritten it to `constantCoeff`. -/
simproc etaQuotientConstantCoeff_ofNat
    (PowerSeries.constantCoeff (UpperHalfPlane.qExpansion 1 (etaQuotient _ _))) := fun e => do
  have e : Q(ℂ) := e
  let ~q(PowerSeries.constantCoeff (UpperHalfPlane.qExpansion 1 (etaQuotient $N $r))) := e
    | return .continue
  let coeffExpr := q(PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (etaQuotient $N $r)))
  let .done result ← etaQuotientCoeff_ofNat coeffExpr | return .continue
  let some proof := result.proof? | return .continue
  let eqZero := q(PowerSeries.coeff_zero_eq_constantCoeff_apply
    (UpperHalfPlane.qExpansion 1 (etaQuotient $N $r)))
  let proof ← mkEqTrans (← mkEqSymm eqZero) proof
  return .done { result with proof? := some proof }

/-- Evaluate a whole coefficient prefix with one checked Euler-unit table. -/
simproc ↓ etaQuotientFirstCoeffs_ofNat (first_coeffs _ (etaQuotient _ _)) := fun e => do
  have e : Q(List ℂ) := e
  let ~q(first_coeffs $m (etaQuotient $N $r)) := e | return .continue
  let some count ← getNatValue? (← whnf m) | return .continue
  if count == 0 then return .continue
  let some level ← getNatValue? N | return .continue
  if r.hasFVar || r.hasMVar then return .continue
  let sumExpr ← mkAppM ``infinitySum #[N, r]
  let some sum ← etaClosedInt sumExpr | return .continue
  if sum < 0 || sum % 24 != 0 then return .continue
  let order := (sum / 24).toNat
  have v : Q(ℕ) := toExpr order
  let hv : Q(infinitySum $N $r = 24 * ($v : ℤ)) ←
    etaCheck q(infinitySum $N $r = 24 * ($v : ℤ))
  let precision := count - order
  let table ← if precision == 0 then do
      let unit ← mkAppM ``unitCoefficient #[N, r]
      etaCertifyTable unit 0 []
    else etaUnitTable level r precision
  have t : Q(List ℤ) := toExpr table.values
  have ht : Q(IsCoefficientTable (unitCoefficient $N $r) ($m - $v) $t) := table.proof
  let proof := q(first_coeffs_eq_of_table_shift (m := $m) $hv $ht)
  let values := (List.range count).map fun n ↦
    if n < order then 0 else etaTableAt table.values (n - order)
  let entries ← values.mapM fun z ↦ do
    have value : Q(ℤ) := toExpr z
    return q(($value : ℂ))
  return .done { expr := ← mkListLit q(ℂ) entries, proof? := some proof }

/-- Also evaluate prefixes after bundled constructor coercions simplify. -/
simproc etaQuotientFirstCoeffs_post (first_coeffs _ (etaQuotient _ _)) :=
  etaQuotientFirstCoeffs_ofNat

private def etaRescaleAlias? (f : Expr) : MetaM (Option Expr) := do
  let mut form := f
  for _ in List.range 16 do
    if form.isAppOf ``gamma0Rescale || form.isAppOf ``gamma0RescaleToLevel ||
        form.isAppOf ``gamma0Restrict || form.isAppOf ``etaQuotientCuspForm then
      return if form == f then none else some form
    let some unfolded ← unfoldDefinition? form (ignoreTransparency := true) | return none
    form := unfolded
  return none

private def etaRewriteStep (proof : Expr) : MetaM Step := do
  let type ← inferType proof
  unless type.isAppOfArity ``Eq 3 do return .continue
  return .visit { expr := type.appArg!, proof? := some proof }

/-- Normalize lifts and positive integral periods before cusp-form coercions unfold.
Inspect the bundled form separately so computed ambient levels also match. -/
simproc ↓ gamma0QExpansionNormalize
    (UpperHalfPlane.qExpansion _ _) := fun e => do
  have e : Q(PowerSeries ℂ) := e
  let ~q(UpperHalfPlane.qExpansion $h (⇑($f : gamma0CuspForms $M))) := e
    | return .continue
  if let some form ← etaRescaleAlias? f then
    have form : Q(gamma0CuspForms $M) := form
    return .visit {
      expr := q(UpperHalfPlane.qExpansion $h $form)
      proof? := some (← mkEqRefl e) }
  let args := f.getAppArgs
  if f.isAppOfArity ``gamma0RescaleToLevel 6 then
    return ← etaRewriteStep (← mkAppM ``gamma0RescaleToLevel_qExpansion
      #[args[2]!, args[3]!, args[4]!, args[5]!, h])
  if f.isAppOfArity ``gamma0Restrict 4 then
    return ← etaRewriteStep (← mkAppM ``gamma0Restrict_qExpansion #[args[2]!, args[3]!, h])
  if f.isAppOfArity ``gamma0Rescale 4 then
    try
      let ⟨true, hh⟩ ← Mathlib.Meta.NormNum.deriveBool q(0 < $h) | return .continue
      return ← etaRewriteStep (← mkAppM ``gamma0Rescale_qExpansion_period
        #[args[1]!, args[2]!, args[3]!, hh])
    catch _ => return .continue
  if ← isDefEq h q((1 : ℝ)) then return .continue
  try
    let ⟨n, hn⟩ ← Mathlib.Meta.NormNum.deriveNat h q(inferInstance)
    let some period ← getNatValue? n | return .continue
    if period == 0 then return .continue
    let hp : Q(0 < $n) ← etaCheck q(0 < $n)
    let heq : Q($h = ($n : ℝ)) := q(Mathlib.Meta.NormNum.IsNat.out $hn)
    let changePeriod := q(congrArg (fun t : ℝ ↦ UpperHalfPlane.qExpansion t $f) $heq)
    let proof ← mkEqTrans changePeriod q(gamma0_qExpansion_nat $f $n $hp)
    return .visit {
      expr := q((UpperHalfPlane.qExpansion 1 $f).expand $n (Nat.ne_of_gt $hp))
      proof? := some proof }
  catch _ => return .continue

/-- Evaluate a lifted prefix using one smaller source coefficient table. -/
simproc ↓ gamma0RescaleFirstCoeffs (first_coeffs _ _) := fun e => do
  have e : Q(List ℂ) := e
  let ~q(first_coeffs $m (⇑($f : gamma0CuspForms $M))) := e | return .continue
  if let some form ← etaRescaleAlias? f then
    have form : Q(gamma0CuspForms $M) := form
    return .visit { expr := q(first_coeffs $m $form), proof? := some (← mkEqRefl e) }
  let args := f.getAppArgs
  if f.isAppOfArity ``gamma0RescaleToLevel 6 then
    return ← etaRewriteStep (← mkAppM ``gamma0RescaleToLevel_first_coeffs
      #[args[2]!, args[3]!, args[4]!, args[5]!, m])
  if f.isAppOfArity ``gamma0Restrict 4 then
    return ← etaRewriteStep (← mkAppM ``gamma0Restrict_first_coeffs #[args[2]!, args[3]!, m])
  unless f.isAppOfArity ``gamma0Rescale 4 do return .continue
  let some count ← getNatValue? (← whnf m) | return .continue
  let some factor ← getNatValue? (← whnf args[2]!) | return .continue
  if count == 0 || factor == 0 then return .continue
  if factor == 1 then
    return ← etaRewriteStep (← mkAppM ``gamma0Rescale_first_coeffs_one
      #[args[1]!, args[3]!, m])
  have d : Q(ℕ) := args[2]!
  have precision : Q(ℕ) := toExpr ((count - 1) / factor + 1)
  let bound ← etaCheck q($m ≤ ($d) * $precision)
  return ← etaRewriteStep (← mkAppM ``gamma0Rescale_first_coeffs_of_bound
    #[args[1]!, d, args[3]!, m, precision, bound])

/-- Normalize zero insertion after the source prefix has been certified. -/
simproc etaRescaleCoefficients_ofNat (rescaleCoefficients _ _ _) := fun e => do
  have e : Q(List ℂ) := e
  let ~q(rescaleCoefficients $d $m $a) := e | return .continue
  let some factor ← getNatValue? (← whnf d) | return .continue
  let some count ← getNatValue? (← whnf m) | return .continue
  let some entries ← getListLit? a | return .continue
  let values := (List.range count).map fun n ↦
    if n % factor == 0 then entries[n / factor]?.getD q((0 : ℂ)) else q((0 : ℂ))
  let result ← mkListLit q(ℂ) values
  return .done { expr := result, proof? := some (← mkEqRefl result) }

/-- Prove numeral eta-quotient coefficient or coefficient-list identities
using checked finite tables. -/
macro "eta_coeff" : tactic =>
  `(tactic| (simp only [etaQuotientMF_qExpansion, etaQuotientCuspForm_qExpansion,
    etaQuotientMF_first_coeffs, etaQuotientCuspForm_first_coeffs, first_coeffs_zero,
    gamma0QExpansionNormalize, gamma0RescaleFirstCoeffs, etaRescaleCoefficients_ofNat,
    gamma0Rescaleₗ_apply, gamma0RescaleToLevelₗ_apply,
    PowerSeries.coeff_expand, PowerSeries.constantCoeff_expand,
    etaQuotientCoeff_ofNat, etaQuotientCoeff_post, etaQuotientConstantCoeff_ofNat,
    etaQuotientFirstCoeffs_ofNat, etaQuotientFirstCoeffs_post] <;>
      (first | rfl | norm_num [rescaleCoefficients, List.range_succ])))

end WeightTwoCusps.Tactic
