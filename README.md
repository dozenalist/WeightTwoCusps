# WeightTwoCusps

Lean 4 formalization of weight-two cusp forms, dimension formulas, and explicit
eta-quotient bases, built on Mathlib. Lean and Mathlib are pinned to **v4.35.0**.

## Main definitions

All project declarations below are in the `WeightTwoCusps` namespace.

- `gamma0CuspForms N`, `gamma1CuspForms N`, and `gammaCuspForms N` are Mathlib's
  analytic weight-two cusp-form spaces for Γ₀(N), Γ₁(N), and Γ(N).
  `gamma0Dimension`, `gamma1Dimension`, and `gammaDimension` compute their
  dimensions; the matching `*_dimension_formula` theorems prove the formulas
  at every positive level. The proofs live in [Dimension/](Dimension/).
- `etaQuotient N r` is the product of `η(mz)^r(m)` over divisors of `N`.
  For `r : Fin N → ℤ`, entry `m - 1` gives the exponent at `m`.
  `etaQuotientMF` and `etaQuotientCuspForm` bundle the product using checked
  Newman–Ligozat conditions. See [EtaQuotient/](WeightTwoCusps/EtaQuotient/README.md).
- `first_coeffs m f` lists q-expansion coefficients of degrees **0 through m − 1**.
  `cuspFormBasis` and `etaQuotientBasis` construct bases from forms or exponent
  vectors using a nonzero coefficient determinant and the dimension formula.
  See [Basis/](WeightTwoCusps/Basis/README.md).
- `gamma0Rescale f d` constructs `f(dz)` at level `M * d` from a level-`M` form.
  `gamma0RescaleToLevel` and `gamma0Restrict` place forms at larger divisible
  levels. See [Oldforms/](WeightTwoCusps/Oldforms/README.md).

## Tactics and automation

- `simp` evaluates dimensions at numeral levels; `eta_coeff` certifies individual
  eta coefficients and entire `first_coeffs` lists, including signed exponents
  and oldform lifts.
- `@[eta_simps]` generates coefficient simp lemmas from checked prefixes and
  entry simp lemmas from finite bases. `sparse![N; i => r, ...]` writes sparse vectors.
- `eta_oldform` proves identities between degeneracy lifts and eta products.
- `cusp_basis_dimension`, `cusp_basis_period`, `cusp_basis_det`, and
  `cusp_basis_independent` discharge basis obligations; `cusp_basis` dispatches
  between them. `q_expansion_matrix` materializes coefficient tables.
- `integer_det` and the [Determinant](https://github.com/dozenalist/Determinant)
  dependency certify nonzero determinants. Stored certificates in
  [det_ne_zero_witnesses/](det_ne_zero_witnesses/) replay with Python, without
  SageMath. New dense certificates may require SageMath. Proofs are checked
  by Lean's kernel.

## Level data

[WeightTwoCusps/Levels/](WeightTwoCusps/Levels/) contains:

- [HasEtaQuotientBasis/TABLE.md](WeightTwoCusps/Levels/HasEtaQuotientBasis/TABLE.md):
  reference data for **levels 1–500**, including cusp counts, dimensions,
  cuspidal eta-span ranks, full-basis flags, Sturm bounds, and exponent vectors.
- `HasEtaQuotientBasis/N/`: **99 complete nonzero bases**, exported as
  `level_N_etaBasis` from `Basis.lean`. `New/` contains directly defined forms
  and `Old/` contains degeneracy lifts; the forms carry checked 100-coefficient
  prefixes. For example, levels 180 and 462 have dimensions 25 and 89.
- `WithoutEtaQuotientBasis/N/`: supporting eta sources at **27 levels** where
  the eta span is incomplete. These folders do not claim full bases.

Names such as `1m1_2p3` encode `η(z)⁻¹η(2z)³`; `_old_N_d` records the ambient
level and dilation. Placement in `New/` alone does not assert a normalized
Hecke newform. See the [level conventions](WeightTwoCusps/Levels/HasEtaQuotientBasis/README.md).

## Build and use

Install [elan](https://github.com/leanprover/elan) and Python 3, with `python3`
available on your path, then run:

```sh
lake update
lake exe cache get
lake build
```

`import WeightTwoCusps` exports the library and all complete level bases.
Use `import WeightTwoCusps.Tactic` for automation without importing every basis.

```lean
import WeightTwoCusps.Tactic

open WeightTwoCusps

example : Module.finrank ℂ (gamma0CuspForms 11) = 1 := by simp
example : first_coeffs 5 (etaQuotient 1 ![24]) = [0, 1, -24, 252, -1472] := by
  eta_coeff
```

The dimension development includes attributed Apache-2.0 material extracted
from Anthropic's `fermats-last-theorem`; see [provenance and license notices](Dimension/FLT/README.md).
