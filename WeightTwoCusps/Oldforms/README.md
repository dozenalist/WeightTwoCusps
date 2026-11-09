# Rescaling cusp forms

`import WeightTwoCusps.Oldforms` provides degeneracy lifts of weight-two
`Γ₀` cusp forms. The main `WeightTwoCusps` import exports this API too.

```lean
import WeightTwoCusps

open WeightTwoCusps

noncomputable section

-- The function f(2z), with no additional scalar factor.
example : gamma0CuspForms 22 :=
  gamma0Rescale cuspForm_11_2_a_a 2

-- The same function at a larger ambient level.
example : gamma0CuspForms 44 :=
  gamma0RescaleToLevel cuspForm_11_2_a_a 2 (by decide)

-- The dilation-one oldform at level 22.
example : gamma0CuspForms 22 :=
  gamma0Restrict cuspForm_11_2_a_a (by decide)
```

For `f : gamma0CuspForms M`, `gamma0Rescale f d hd` has level `M * d`.
The argument `hd : 0 < d` defaults to `by positivity`, so positive numeral
factors need no explicit proof. `gamma0RescaleToLevel f d h hd` has level
`N`, using `h : M * d ∣ N`. Neither constructor needs a positive source
level assumption.

The simp lemmas `gamma0Rescale_apply` and `gamma0RescaleToLevel_apply`
identify the value at `z` with `f (Eta.dilate d _ z)`. The constructors
reuse Mathlib's cusp-form translation and restriction proofs and remove
the factor `d` introduced by its weight-two slash action.

`gamma0Rescaleₗ d hd` and `gamma0RescaleToLevelₗ d h hd` bundle the same
operations as complex linear maps. Positive rescaling is injective.
`gamma0RescaleToLevel_one` identifies dilation one with `gamma0Restrict`;
`gamma0RescaleToLevel_trans` combines successive factors `d` and `e`
into `d * e`, including any intervening increases in ambient level.

## Q-expansion coefficients

`gamma0Rescale_qExpansion_coeff` gives the period-one coefficient rule:
coefficient `n` is the source coefficient `n / d` when `d ∣ n`, and zero
otherwise. The variants `gamma0Rescale_qExpansion_coeff_mul` and
`gamma0Rescale_qExpansion_coeff_of_not_dvd` specialize the two cases.
`gamma0Rescale_qExpansion_coeff_of_period` works at any positive strict
period of the source group.

`gamma0Rescale_qExpansion` expresses the full series using
`PowerSeries.expand`. For every positive real `h`, the separate identity
`gamma0Rescale_qExpansion_period` identifies the lift's period-`h` expansion
with the source's period-`h * d` expansion. Thus periods smaller than one
are useful too. `gamma0_qExpansion_nat` normalizes a positive integral
period back to period one.

With `import WeightTwoCusps.Tactic.EtaCoefficient` (also exported by the
main import), `eta_coeff` evaluates lifted eta forms directly:

```lean
example : (UpperHalfPlane.qExpansion 1
    (gamma0Rescale cuspForm_11_2_a_a 2)).coeff 4 = -2 := by eta_coeff

example : first_coeffs 8 (gamma0Rescale cuspForm_11_2_a_a 2) =
    [0, 0, 1, 0, -2, 0, -1, 0] := by eta_coeff

example : (UpperHalfPlane.qExpansion (1 / 2)
    (gamma0Rescale cuspForm_11_2_a_a 2)).coeff 2 = -2 := by eta_coeff
```

The tactic handles successive lifts, named definitions, restrictions,
ambient-level changes, and the linear-map constructors. Individual
coefficients support positive numerical periods whose product with the
total dilation is a positive integer. Nonpositive and unsupported periods
are left unevaluated. Finite lists use one checked source table through
degree `m / d`, followed by zero insertion and truncation. `cusp_basis`
also evaluates coefficient matrices of these lifts directly.

With `import WeightTwoCusps.Tactic.EtaOldform` (also exported by the main
import), `eta_oldform` identifies a degeneracy lift with its exact eta product:

```lean
example : gamma0Rescale cuspForm_11_2_a_a 2 =
    etaQuotientCuspForm 22 sparse![22; 1 => 2, 21 => 2] := by
  eta_oldform
```

The tactic follows named definitions and successive lifts, uses the application
lemmas above, and checks the full finite product. Numeral ambient levels and
closed signed exponent vectors are supported. See the
[level-folder guide](../Levels/HasEtaQuotientBasis/README.md) for complete
new-level instructions, naming conventions, and validation steps.

`Tests.lean` identifies the level-11 lifts at level 22 with the corresponding
eta products, checks the leading coefficient of the dilation-two lift,
and constructs their basis using `cuspFormBasis`. Run:

```sh
lake build WeightTwoCusps WeightTwoCusps.Oldforms.Tests WeightTwoCusps.Tactic.EtaOldformTests WeightTwoCusps.Tactic.RescaleCoefficientTests
```
