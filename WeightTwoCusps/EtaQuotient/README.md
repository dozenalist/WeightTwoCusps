# Eta quotients

The public constructions are `WeightTwoCusps.etaQuotientMF` and
`WeightTwoCusps.etaQuotientCuspForm`. They accept signed integer exponents at
every positive level. See [current progress and outstanding work](PROGRESS_2026-11-05.md).

```lean
import WeightTwoCusps.EtaQuotient
import WeightTwoCusps.Tactic.EtaCoefficient

open WeightTwoCusps WeightTwoCusps.EtaQuotient UpperHalfPlane

noncomputable section

def r15 : Fin 15 → ℤ := ![1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

example : ModularForm (CongruenceSubgroup.Gamma0 15) 2 := etaQuotientMF 15 r15
example : CuspForm (CongruenceSubgroup.Gamma0 15) 2 := etaQuotientCuspForm 15 r15

example : (qExpansion 1 (etaQuotient 15 r15)).coeff 3 = -1 := by eta_coeff
example : (qExpansion 1 (etaQuotientMF 15 r15 (k := 2))).coeff 3 = -1 := by simp
example : (qExpansion 1 (etaQuotient 1 ![24])).coeff 10 = -115920 := by eta_coeff
```

## Inputs and arithmetic conditions

`etaQuotient N r : ℍ → ℂ` is the product of `η(mz)^(exponent r m)` over
positive divisors `m` of `N`. The input is `r : Fin N → ℤ`: entry `i` belongs
to `η((i.val + 1)z)`. Nondivisor entries are ignored. Negative exponents are
integer powers. At level zero the raw function is one; the constructors
require positive level.

```lean
etaQuotientMF (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k := by decide +kernel) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k

etaQuotientCuspForm (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k := by decide +kernel)
    (hc : VanishingAtCusps N r := by decide +kernel) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k
```

`NewmanLigozatConditions` records positive level, `∑ rₘ = 2k`, both
weighted congruences modulo 24, even weight, a rational square `∏ m^rₘ`,
and nonnegative Ligozat cusp sums. `VanishingAtCusps` requires strictly
positive cusp sums. The character conditions give Mathlib's ordinary
trivial-character modular forms.

The weight is inferred from the expected type or supplied with `(k := k)`.
Omitted arithmetic proofs are checked by the kernel. Explicit proofs remain
accepted for symbolic inputs, including supplying just one cusp-form proof.
Both bundled forms have `etaQuotient N r` as their underlying function.

## File structure

| Path | Purpose |
| --- | --- |
| [Basic.lean](Basic.lean) | Eta quotient, exponents, weight and weighted sums |
| [Criteria.lean](Criteria.lean) | Finite Newman–Ligozat conditions and cusp arithmetic |
| [Constructor.lean](Constructor.lean) | The two public constructors and existence theorems |
| [Transformation/](Transformation/) | Eta-square laws, translations, reflection and group generation |
| [Multiplier/](Multiplier/) | Actual half-weight multiplier, Jacobi formula and character descent |
| [Cusps/](Cusps/) | Infinity analysis, affine cusp factorization, bounds and local orders |
| [Criteria/](Criteria/) | Necessary conditions, forced weight and the even-exponent equivalences |
| [QExpansion/](QExpansion/) | Analytic expansions, integer coefficient formulas and finite certificates |
| [Examples.lean](Examples.lean) | Forms at levels 1, 4, 11, 14 and 15 using the general constructors |
| [Audit.lean](Audit.lean) | Public-interface checks and axiom audit |

The old prime-level and nonnegative-exponent constructor modules were removed.
Use the two general constructors with the **actual** exponent vector. Internal
flat module paths have moved; `import WeightTwoCusps.EtaQuotient` is unchanged.

## Q-expansion API

Let `hi : (24 : ℤ) ∣ infinitySum N r` and `h0 : 0 ≤ infinitySum N r`.
These hypotheses require no modularity theorem and follow from the constructor
conditions. Set `v = infinityOrder N r = (infinitySum N r / 24).toNat`.

- `qExpansion_coeff_eq_coefficient hi h0 n` identifies every analytic
  coefficient with the integer `coefficient N r n`.
- `qExpansion_coeff_add hv n` identifies coefficient `v + n` with
  `unitCoefficient N r n`, given `hv : infinitySum N r = 24 * (v : ℤ)`.
- `qExpansion_coeff_eq_zero_of_lt`, `qExpansion_coeff_leading`, and
  `qExpansion_order_of_congruence` give initial vanishing, leading coefficient
  one and the exact order.
- `qExpansion_coeff_leading_add_one` gives `-exponent r 1`.
- `qExpansion_coeff_leading_add_two` gives `a * (a - 3) / 2 - b`, where
  `a = exponent r 1` and `b = divisorExponent N r 2`. The latter is zero
  when 2 does not divide the level.
- `unitCoefficient_zero`, `unitCoefficient_one`, and `unitCoefficient_two`
  give the corresponding integer identities for the normalized Euler unit.
- `qExpansion_coeff_integral`, `qExpansion_coeff_re`, and `qExpansion_coeff_im`
  give integrality and reality.
- `qExpansion_coeff_mul_of_exponent_add` gives a finite integer convolution
  when divisor exponents are added.
- `qExpansion_eq_mk_coefficient` and `hasSum_coefficient` identify the whole
  convergent series with the integer algorithm.

`etaQuotientMF_qExpansion_coeff` and `etaQuotientCuspForm_qExpansion_coeff`
apply the formula directly to the constructors. The corresponding
`_qExpansion_order` lemmas compute their orders; the cusp-form constructor
has positive infinity order and zero constant coefficient.

The implementation is split into:

- `Basic`: analytic Euler unit, shift, order and convergence.
- `Euler`: normalized dilated factors and the first coefficient.
- `Sequence`: Euler coefficients and convergence, convolution, power substitution,
  powers and reciprocal recursion.
- `Computable`: the complete integer formula and its analytic correctness proof.
- `LowCoefficients`, `Properties`, `ModularForm`: symbolic and bundled-form APIs.
- `Certificates`: checked intermediate tables used by the numeral tactic.
- `Tests`: ordinary-import checks and symbolic API regressions.

The remaining `Eta/` modules supply the dilation, integral level conjugation,
eta-square transformation laws and multiplier arithmetic used by this
development. Specialized paired-product constructors and their analytic proofs
have been removed. All coefficient arithmetic now lives in `QExpansion/Sequence.lean`,
with one Euler coefficient definition and a direct proof of agreement with
Mathlib's pentagonal series.

## Numeral evaluation

`import WeightTwoCusps.Tactic.EtaCoefficient` registers the coefficient
simprocs and the `eta_coeff` tactic. They are also exported by
`WeightTwoCusps.Tactic` and `WeightTwoCusps`.

Use `by simp` or `by eta_coeff` for numeral indices and levels with closed
integer exponent functions, including vector literals and closed definitions.
Both constructors are supported. Each proposed table is checked with finite
integer equalities, then connected to the analytic expansion by proved lemmas.
No additional axiom or `native_decide` is used.

Reciprocal tables are checked by a finite convolution with constant value one.
The proved `inverseTable_of_product` lemma recovers the reciprocal recurrence,
avoiding repeated random-access walks through coefficient lists.

The evaluator uses exponentiation by squaring, omits trailing zero entries,
and reuses checked arithmetic lemmas. Convolution certificates pack the input
polynomials into integers at a large base. The kernel checks their product
modulo a base power and a coefficient norm bound that rules out hidden carries;
the correctness proof is in [PackedCertificates.lean](QExpansion/PackedCertificates.lean).
Euler tables use a sequential checker, while candidate values use arrays.
Euler's pentagonal sum searches only `-sqrt(n)` through `sqrt(n)`, using the
proved inequality `k² ≤ pentagonal(k)`. The larger-index regressions include
Ramanujan's coefficient at degree 200 with the default heartbeat limit; that
case permits recursion depth 4096. These checks do not imply an unlimited
coefficient range.

`WeightTwoCusps.first_coeffs m f : List ℂ` is defined recursively in
`WeightTwoCusps/QExpansion.lean`. It lists degrees **0 through `m - 1`**,
including the constant coefficient. `first_coeffs_length` and
`first_coeffs_getElem` describe its length and entries for any function
`f : ℍ → ℂ`.

`eta_coeff` and `simp` evaluate a whole prefix with a single checked table:

```lean
import WeightTwoCusps.Tactic.EtaCoefficient

open WeightTwoCusps

example : first_coeffs 5 (etaQuotient 1 ![24]) = [0, 1, -24, 252, -1472] := by
  eta_coeff

example : first_coeffs 5 (etaQuotientMF 1 ![24] (k := 12)) =
    [0, 1, -24, 252, -1472] := by eta_coeff

example : first_coeffs 5 (etaQuotientCuspForm 1 ![24] (k := 12)) =
    [0, 1, -24, 252, -1472] := by eta_coeff
```

The batch evaluator shares the Euler-unit table across every coefficient and
computes only the precision needed after the initial zeros. It handles numeral
lengths such as 50 using the same supported exponent data as scalar evaluation.
The [prefix regression suite](../Tactic/FirstCoeffsTests.lean) checks 50 entries
for raw eta quotients and both bundled constructors, as well as signed exponents,
zero precision, and prefixes ending before the leading term. The final prefix
certificate shifts and pads the table linearly, with the leading-zero block
capped at the requested length. Lifted prefixes use a checked numeral source
precision before inserting zeros.

The [optimization log](../../benchmarks/eta-coeff/OPTIMIZATION.md) records the
50- and 100-coefficient benchmarks, retained and rejected experiments, and
reproduction commands. For a large sequence of coefficient declarations,
`set_option Elab.async false` reproduces the faster measured batch compilation;
individual proofs retain the default heartbeat limit.

The evaluator handles period one with a nonnegative infinity sum divisible
by 24. Symbolic inputs, negative infinity order and nonintegral infinity
order are left unevaluated. Negative individual exponents are supported.
See the permanent [coefficient regressions](../Tactic/EtaCoefficientTests.lean)
and [larger-index checks](../Tactic/EtaCoefficientBenchmarks.lean).

## Verification and sources

The exact checked commands and remaining work are recorded in the
[progress notes](PROGRESS_2026-11-05.md).

- David Savitt, [*An elementary proof of Newman's eta-quotient theorem*](https://math.jhu.edu/~savitt/papers/pdfs/newman.pdf).
- Gérard Ligozat, [*Courbes modulaires de genre 1*](https://www.numdam.org/article/MSMF_1975__43__5_0.pdf), §3.2.
- The attributed rational-cusp transport in `Cusps/Bounds.lean` is adapted
  from [TauCeti](https://github.com/TauCetiProject/TauCeti/blob/e8758b7b2f82b9b1c3f33b992ab8f499b510240f/TauCeti/NumberTheory/ModularForms/Cusps/Rat/Basic.lean)
  under Apache-2.0; TauCeti is not a dependency.
