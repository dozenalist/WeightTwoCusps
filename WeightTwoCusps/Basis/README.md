# Bases from q-expansion coefficients

`import WeightTwoCusps.Basis` exports the coefficient criteria, the
`cusp_basis` tactic, and the constructors. The main `WeightTwoCusps` import
exports them too. All arithmetic certificates are checked by the Lean kernel.

```lean
import WeightTwoCusps

open WeightTwoCusps WeightTwoCusps.Tactic

noncomputable section

def r22 : Fin 22 → ℤ := sparse![22; 0 => 2, 10 => 2]
def s22 : Fin 22 → ℤ := sparse![22; 1 => 2, 21 => 2]

-- η(z)²η(11z)² and η(2z)²η(22z)², with every proof omitted.
def basis22 : Module.Basis (Fin 2) ℂ (gamma0CuspForms 22) :=
  etaQuotientBasis 22 ![r22, s22]

-- A vector of already bundled cusp forms is also accepted.
example : Module.Basis (Fin 2) ℂ (gamma0CuspForms 22) :=
  cuspFormBasis ![etaQuotientCuspForm 22 r22, etaQuotientCuspForm 22 s22]

example : LinearIndependent ℂ ![etaQuotientCuspForm 22 r22 (k := 2),
    etaQuotientCuspForm 22 s22 (k := 2)] := by
  cusp_basis

-- Other coefficient columns can be selected explicitly.
example : Module.Basis (Fin 2) ℂ (gamma0CuspForms 22) :=
  etaQuotientBasis 22 ![r22, s22] (c := ![1, 4])
```

For an exponent vector, entry `j` refers to the exponent of `η((j+1)z)`;
entries at nondivisors of the level are ignored, as in `etaQuotientCuspForm`.
The two level-22 forms above have coefficient rows `(1, -2)` and `(0, 1)`
at indices 1 and 2. Their determinant is 1 and the space has dimension 2.
The resulting basis contains exactly the supplied forms; it does not
normalize or replace them.

Vectors may also contain degeneracy lifts constructed by `gamma0Rescale`
or `gamma0RescaleToLevel`. Coefficient automation follows the lifts to their
eta-quotient sources, so oldforms can be used directly without rewriting
them as larger eta exponent vectors. For example, with the main import:

```lean
example : Module.Basis (Fin 2) ℂ (gamma0CuspForms 22) :=
  cuspFormBasis ![gamma0Restrict cuspForm_11_2_a_a (by decide),
    gamma0Rescale cuspForm_11_2_a_a 2]
```

## Mathematical interface

`qExpansionMatrix h v c i j` is coefficient `c j` of the period-`h`
q-expansion of `v i`. Rows correspond to forms; columns correspond to
the selected q-indices. The lemmas in `Basic.lean` work for every integer
weight and every subgroup with determinant one, provided `h` is a positive
strict period.

- `linearIndependent_of_qExpansionMatrix_det_ne_zero` proves independence
  from a nonzero determinant, without any dimension hypothesis.
- `linearIndependent_of_qExpansion_triangular` and
  `linearIndependent_of_qExpansion_leading` handle triangular coefficient
  tables and strictly increasing leading orders.
- `linearIndependent_of_qExpansionMatrix_eq_one` handles normalized tables.
- `basisOfQExpansionMatrix` constructs a basis when the vector length
  equals the dimension; `basisOfQExpansionMatrix_coe` identifies its entries.
- `span_eq_top_of_qExpansionMatrix_det_ne_zero` gives the spanning statement.
- `eq_iff_qExpansion_coeff_eq_of_det_ne_zero` shows that the same selected
  coefficients determine any cusp form in the space.
- `eq_of_qExpansion_coeff_eq_of_finrank_eq_one` and
  `existsUnique_normalized_of_finrank_eq_one` in `DimensionOne.lean` give
  coefficient comparison and normalized uniqueness in every one-dimensional
  cusp-form space, at arbitrary weight and positive strict period.

The basis and comparison statements require finite dimensionality explicitly,
including for empty vectors. The project supplies this instance for the
positive-level weight-two congruence spaces. An empty vector gives a basis
of a dimension-zero space.

## Constructors and tactic

`cuspFormBasis v` takes a vector of bundled cusp forms. Its optional arguments
are the coefficient indices `c`, the period `h`, positivity `hh`, strict-period
membership `hΓ`, the dimension equality `hdim`, and the determinant proof `hdet`.
Proof arguments have specialized defaults; explicit proofs are also accepted.

`etaQuotientBasis N r` takes `r : Fin n → Fin N → ℤ` at positive level and
returns a basis of `gamma0CuspForms N`. Its optional arguments are the
Newman–Ligozat proofs `h`, strict cusp proofs `hc`, coefficient indices `c`,
dimension equality `hdim`, and determinant proof `hdet`. The first two default
to `decide +kernel`; the last two use the dimension and determinant defaults below. Explicit proofs
are accepted for symbolic data. Negative and odd exponents use the existing
eta-quotient constructor and coefficient APIs.

Constructor defaults use `positivity` for the positive period,
`cusp_basis_period` for strict-period membership, `cusp_basis_dimension` for
the dimension. For the coefficient determinant, `q_expansion_matrix` reuses
checked coefficient prefixes and builds a compact `ofLists` table, then
`det_ne_zero! cusp_basis_det_config%` certifies its nonzero determinant.
The abstract `qExpansionMatrix` and its entry API remain unchanged.
`cusp_basis_independent` handles independence, with an optional `using ![...]`.
The original `cusp_basis` spelling remains a compatibility dispatcher.

`Determinant` is a pinned Git dependency fetched automatically by Lake.
Dense constructor proofs save kernel-checked modular witnesses in
`det_ne_zero_witnesses/` at this project's root. Keep the JSON files to replay
proofs without Sage; replay still needs standard `python3`. Triangular tables
need no external process and create no witness. The local dependency's scripts
are resolved from the calling source file's Lake project. Native Windows uses its `Invoke-SageWSL.ps1`
adapter with the installed `SageMath-10.10` distribution; other platforms use
`python3` with `sage.all`. `cusp_basis_det_config%` selects the
`unit-upper-product` certificate, so Lean checks the diagonal and lower triangle.
For explicit offline certification, use:

```lean
by
  q_expansion_matrix
  det_ne_zero! { cusp_basis_det_config% with policy := .cacheOnly }
```

Both constructors default to indices 1 through the vector length. These
columns need not certify every basis: supply `(c := ![...])` when another
minor is required. The tactic does not search for a minor. On an independence
goal, `cusp_basis using ![...]` selects custom columns. The bare tactic
also handles dimension equalities and coefficient-determinant goals.

Numerical dimension automation covers weight two. Eta-coefficient automation
covers closed exponent data at period one. `matrix_det` first tries symbolic
triangularity and determinant identities of size at most three. It then
materializes the coefficients and clears rational denominators row by row,
using the proved `matrix_det_ne_zero_of_int_rowScale` reduction.

The independent `integer_det` tactic is available by importing
`WeightTwoCusps.Tactic.IntegerDeterminant`. It first detects upper or lower
triangular matrices. Otherwise, it tries successive primes starting at two.
For the first successful prime it supplies an elimination transform and
checks only the product's lower triangle and diagonal. The diagonal is
normalized to one, so the soundness theorem actually works for every modulus
greater than one. Integer residues and their transpose are checked once;
the dot products use natural-number arithmetic. No determinant value,
invertibility proof for the transform, or entries above the diagonal are
required. Every arithmetic identity is checked by the kernel; `native_decide`
is not used. Finite-field inputs retain Mathlib's echelon fallback.

There is no fixed matrix-size cutoff. The search tries 64 primes by default;
use `set_option integer_det.maxPrimes 128` to extend it. Exhausting the search
reports failure and does not assert singularity. The tactics handle row swaps,
rational entries, named or locally defined vectors, and custom columns. Available
`first_coeffs` lemmas supply entries within their stored ranges; later
coefficients are evaluated normally. Symbolic goals retain the simplification
and ring-arithmetic fallback. Larger certificates may require additional
recursion depth; the default heartbeat limit is retained.

The regression suites cover empty and singular matrices, row swaps, bad primes,
rational denominator clearing, arbitrary characteristic-zero coefficient fields,
symbolic triangular matrices, finite fields, and coefficient-prefix reuse.
See `OPTIMIZATION_PROGRESS.md` for large-matrix timings and level-462 checks.

The design follows the separation between candidate generation and proof
checking in [Mathlib's echelon certificates](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Echelon/Cert.html).
For background on modular exact linear algebra, see
[FLINT's multimodular algorithms](https://flintlib.org/doc/algorithms/linear-algebra/multimodular.html).

## Files and verification

- `Basic.lean`: coefficient maps, independence, bases, spanning and comparison.
- `DimensionOne.lean`: comparison and normalized uniqueness in dimension one.
- `Determinant.lean`: full rank implies nonzero determinant over an arbitrary
  field and finite index type, and reuse of checked coefficient prefixes.
- `IntegerMatrix.lean`: integer cast and denominator-clearing reductions,
  and the partial-product modular certificate and its soundness proof.
- `Constructor.lean`: the two constructors with default proof tactics.
- `../Tactic/Basis.lean`: the `cusp_basis` tactic.
- `../Tactic/IntegerDeterminant.lean`: the independent integer matrix tactic.
- `../Tactic/IntegerDeterminantTests.lean`: integer and modular regressions.
- `Tests.lean`: concrete constructions, custom indices, empty and invalid inputs,
  and axiom audits.
- `../Tactic/BasisDeterminantTests.lean`: larger numerical matrices, row pivots,
  rational and finite-field arithmetic, local contexts, coefficient-prefix
  bounds, custom columns, rejection tests, and axiom audits.

Run `lake build WeightTwoCusps WeightTwoCusps.Basis.Tests
WeightTwoCusps.Tactic.BasisDeterminantTests`.

The checked examples include bases at levels 11, 22 and 33 (including odd
exponents), reversed rows, custom columns, vectors of bundled eta quotients,
and the empty basis. Duplicate vectors and an incorrect dimension are rejected.
The basis constructions and independence proofs have only `propext`,
`Classical.choice`, and `Quot.sound` as axioms.
