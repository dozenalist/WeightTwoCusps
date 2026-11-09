# Tactic optimization progress

## November 8: modular determinant certificates

The general integer backend is now `integer_det` in
`WeightTwoCusps/Tactic/IntegerDeterminant.lean`. Its soundness theorems are in
`WeightTwoCusps/Basis/IntegerMatrix.lean`, independently of cusp-form data.

- Triangular integer matrices are certified directly. Other matrices use
  successive primes, starting at two. Only the successful modular image is
  certified; failed primes produce no proof terms. The default search limit
  is 64 primes and can be changed with `integer_det.maxPrimes`.
- The verifier checks the lower triangle and normalized diagonal of an
  elimination product. It does not compute the entries above the diagonal,
  the determinant's value, or an inverse of the transform. Its soundness
  theorem accepts any modulus greater than one, without a primality hypothesis.
- Integer residues and their transpose are checked and shared separately,
  keeping their computation out of individual dot products. The arithmetic
  checks use natural numbers and kernel reduction, without `native_decide`.
- Integer cast nonzeroness and rational denominator clearing are proved for
  arbitrary finite index types and characteristic-zero coefficient rings.
  Integral coefficient tables go directly to integers; nonintegral rational
  entries use checked row scaling. Local rational aliases are supported.
- `cusp_basis_dimension`, `cusp_basis_period`, `cusp_basis_det`, and
  `cusp_basis_independent` handle separate goals. `matrix_det` tries structural
  proofs and small determinant identities before numerical certificates.
  `cusp_basis` remains a compatibility dispatcher. Constructor positivity
  defaults use `positivity`.

Validation completed during this work:

- The unchanged plain `level_462_etaBasis` compiled at the default heartbeat
  limit in 52.8 seconds, retaining its existing recursion-depth setting.
  No level-specific certificate or replacement constructor was supplied.
- An independent 89-by-89 dense integer benchmark (`I + J`) compiled at
  default heartbeats in 27.5 seconds, including import time. It must skip
  primes 2, 3, and 5 before using 7.
- The level-462 integer coefficient table also passed the standalone integer
  tactic at default heartbeats, skipping 2, 3, 5, and 7 before using 11.
  Its initial successful run took 86.8 seconds including data elaboration;
  this was before the final literal-input fast path.
- Integer, determinant/basis, and basis-constructor regression suites passed.
  Coverage includes empty and singular matrices, row swaps, bad primes,
  rational entries, local aliases, arbitrary characteristic-zero fields,
  symbolic triangular matrices, arbitrary positive periods supplied by
  hypotheses, finite fields, and stored coefficient-prefix boundaries.

Timings are local wall-clock observations and were affected by concurrent
validation. Logs are `.lake/IntegerDeterminantBenchmarks.log`,
`.lake/IntegerDeterminantStress.log`, `.lake/ModularPlain462DirectInt.log`,
`.lake/ModularBasisRegressions.log`, and `.lake/IntegerDeterminantTests.log`.
The earlier session notes below are historical; their unresolved level-462
determinant limitation is superseded by these results. Whole-library and
levels-1–500 validation are not claimed by this section.

## Earlier optimization session

This is a working handoff for the optimization of `eta_coeff` and
`cuspFormBasis`, with level 462 as the main stress test. The latest work
session is limited to one hour, beginning November 7, 2026 at 11:37 p.m.
America/Denver. Final validation results will be recorded below.

## Implemented

- Coefficient candidate generation uses arrays, skips zero multipliers, and
  trims trailing zeros from intermediate tables.
- Natural powers use exponentiation by squaring and reuse checked arithmetic
  lemmas. Convolution certificates traverse lists sequentially.
- Euler coefficients use a proved square-root bound on the pentagonal sum.
- `sparse!` stores only its specified entries, preserving duplicate-entry and
  out-of-bounds behavior.
- Basis automation batches missing coefficients by form, reuses stored
  prefixes, and transports characteristic-zero arithmetic to rational
  certificates. Large determinant certificate work is still being validated.
- Added sparse-vector regressions, dimension checks for levels 1–500, and
  `scripts/ValidateLevels.ps1` for builds, export checks, and axiom audits.

## Verified before the latest session

- Coefficient, prefix, and rescaling regression targets passed.
- The existing degree-100 coefficient benchmark decreased from approximately
  375 seconds to 27 seconds in local direct runs; these timings are affected
  by concurrent build load. A later Lake run completed it in 19 seconds.
- Ramanujan's coefficient at degree 200 passed with the default heartbeat
  limit and recursion depth 4096. Degree 500 still exceeded that heartbeat
  limit and is not claimed as supported by this benchmark.
- Earlier determinant regressions passed before the latest changes to large
  certificates; they must be rerun against the final implementation.

## Latest session validation

- All 89 level-462 forms have additional, kernel-checked 90-coefficient
  prefixes in `WeightTwoCusps/Levels/HasEtaQuotientBasis/462/Coefficients.lean`.
  The complete file compiled in 353.7 seconds with default `maxHeartbeats`.
  The original 50-coefficient statements are retained.
- Replaced reciprocal-table checking by `inverseTable_of_product`, which
  recovers the reciprocal recurrence from a checked finite convolution.
  The coefficient, first-prefix, and rescale regression files pass.
- The final general determinant regressions pass, including dense 12-by-12
  matrices, row swaps, rational entries, finite fields, level 42, custom
  columns, short prefixes, and rejection tests. Their axiom reports contain
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Temporary diagnostic file writes and a redundant certificate branch have
  been removed from the tactic.
- Following the user's correction, level 462 again uses the plain
  `cuspFormBasis ![...]` application. A proposed separate numerical
  determinant module and explicit determinant argument were removed. No
  replacement basis constructor or alternate level-specific certification
  is installed.
- The 89-by-89 general numerical stress test still exceeds the default
  heartbeat budget. A successful final compilation of `level_462_etaBasis`
  has **not** been established. The main objective remains outstanding.

Relevant logs are `.lake/Hour462CoefficientsFast.log`,
`.lake/HourFinalCleanRegressions.log`, `.lake/HourPlain462Check.log`, and
`.lake/Hour462CoefficientAxioms.log`. These are local build artifacts.

## Outstanding work

- Finish and validate level 462's `cuspFormBasis` under default
  `maxHeartbeats`, then audit its axioms.
- Rerun determinant and basis regressions after the final certificate changes.
- Complete the main library build and the dimension tests for levels 1–500.
- Run the complete exported-form and basis axiom audit.
- Further reduce the general determinant certificate's cost without
  changing level 462's certification method. The existing full product
  certificate checks entries above the diagonal even though upper
  triangularity and a nonzero diagonal need only the lower triangle and
  diagonal. A general partial-product certificate is a promising next step.
- Retest the exact plain level-462 constructor and audit its axioms after
  this resource limitation is resolved. Do not replace this with a
  separately supplied numerical determinant certificate.

The table has 99 positive-dimensional levels with full eta bases and 15
zero-dimensional levels. Other levels have only partial eta spans; a full
basis must not be asserted for them on the supplied data alone.

The final tactic source retains rational arithmetic certificates, coefficient
prefix reuse, and batching of missing coefficients. An experimental integer
rank path failed kernel type checking and was removed; the final determinant
regression file passes after that removal. No failed proof is part of a
successfully built artifact. The separately supplied determinant-certificate
API was also removed following the user's correction.

Suggested implementation of the remaining general optimization:

1. Compute an elimination transform `L` and row permutation as candidate data.
2. Check only product entries below the diagonal and the nonzero diagonal.
   Entries above the diagonal need not be computed to prove the product is
   upper triangular with nonzero determinant.
3. Use determinant multiplicativity and the permutation identity to deduce
   nonzeroness of the original matrix. This keeps `cusp_basis` and the
   existing plain `cuspFormBasis` application as the certification path.
4. If integer arithmetic is used, prove the matrix cast equality explicitly;
   an expected-type hint is insufficient when rational numeral expressions
   are not definitionally equal to the cast matrix.

The extended-prefix axiom audit completed successfully: all 89 extended
coefficient theorems and `inverseTable_of_product` (90 reports) use only
`propext`, `Classical.choice`, and `Quot.sound`. The final plain level-462
check was stopped before the one-hour deadline without a completed result;
it is not counted as successful. Whole-library and levels-1–500 success is
not claimed.

Session stopped November 8, 2026, before 12:38 a.m. America/Denver, within
the requested one-hour limit.

## Local Determinant package integration

The level-462 verification item above is now resolved.

- Added the existing sibling `../Determinant` as a local Lake dependency,
  using the same Lean/Mathlib v4.35.0 pins. No repository was cloned.
- Both basis constructors materialize their coefficient matrices as compact
  `ofLists` tables and certify the determinant using `det_ne_zero!`.
  The abstract `qExpansionMatrix` and the plain level-462 constructor call
  retain their existing definitions and API.
- Producer and lookup scripts are resolved from the calling file's Lake
  project. Windows uses the dependency's Sage/WSL adapter; standard Python
  handles cache lookup. The selected certificate kind is `unit-upper-product`.
- The original `WeightTwoCusps.Levels.HasEtaQuotientBasis.«462».Basis`
  module built successfully in 61 seconds with default `maxHeartbeats` and
  its existing `maxRecDepth 4096`. Its 89-by-89 witness uses modulus 11
  and is stored in the root `det_ne_zero_witnesses/` folder.
- Reconstructed the same level-462 basis in a fresh Lean process with
  `.cacheOnly` and `executable := "must-not-launch"`. The trace confirms
  a hit on that exact witness. The original basis and the replayed basis
  depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- The final Lake build of `WeightTwoCusps.Basis.Tests`,
  `WeightTwoCusps.Tactic.BasisDeterminantTests`, and the level-462 basis
  passed (4588 jobs). The regression suite now includes persisted level-42
  certification and cache-only replay; these two checks run synchronously
  so publication finishes before replay begins.

Validation logs are `.lake/DeterminantVerifiedBuild.log` and
`.lake/Level462CacheReplay.log`. The fresh level-462 build timing is in
`.lake/DeterminantValidationFinal.log`; that earlier run also exposed the
subsequently fixed asynchronous publication race in the new regression test.
Whole-library and levels-1–500 axiom audits remain separate work.

## eta_coeff arithmetic versus certificate checking

The external-calculation feasibility check is complete; see
[`benchmarks/eta-coeff/REPORT.md`](benchmarks/eta-coeff/REPORT.md) and its
machine-readable results. Production `eta_coeff` was unchanged.

All 89 level-462 coefficient prefixes were profiled with serialized theorem
checking: 774.814 s in declaration bodies, of which only 1.672 s (0.216%)
was candidate table arithmetic. `etaCheck` consumed 511.491 s (66.0%);
other Lean work consumed 261.652 s. Those serialized timings are not the
earlier 384 s parallel module-build measurement.

One fresh Sage/WSL process computed and returned the complete batch in a
median 2.644 s across three launches, exceeding the local arithmetic time.
Warm Sage arithmetic took 0.04553 s, so even a persistent producer ignoring
IPC would save only about 1.63 s (0.21%) with the existing proof pipeline.
All Sage outputs matched the Lean-checked coefficient tables. The report
includes repeated unmodified-tactic controls and reproducible profiling
scripts. Certificate checking and other Lean work are the larger targets.
