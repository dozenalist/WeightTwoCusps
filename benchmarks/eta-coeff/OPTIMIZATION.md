# eta_coeff certification optimization

Work window: November 9, 2026, 01:20–03:20 America/Denver (08:20–10:20 UTC).
Goal: certify `first_coeffs 100 f` in less than 60 seconds for a range of
eta quotients, particularly level 462. Start each experiment with concrete
50-coefficient identities. Keep production changes only after measured gains.

## Initial implementation observations

`WeightTwoCusps/Tactic/EtaCoefficient.lean` constructs Euler, reciprocal,
power, and product tables. `etaCheck` checks closed propositions by kernel
reduction of `decide`, publishing synchronous auxiliary lemmas. The product
checker originally wrapped full-list multiplication in `take`; demand-driven kernel
reduction may already avoid evaluating discarded tails.
`Certificates.lean` supplies the propagation proofs. The previous cost study
attributes 66% of serialized level-462 declaration time to `etaCheck`, versus
0.216% to candidate arithmetic. Candidate generation is outside this work's
optimization priorities.

## Final results

All 89 actual level-462 basis forms pass concrete `first_coeffs 100` checks.
The final fresh, serial compilation, including `.olean` output, takes
**55.046 seconds**. Use `set_option Elab.async false` for this batch result;
the default asynchronous batch takes 66.687 seconds. The isolated original
implementation takes 309.876 seconds for the same 89 concrete identities.
Every individual declaration is faster in the retained implementation.

The retained changes are packed integer certificates for convolutions,
sequential coefficient checking, symbolic certificates for neutral factors,
literal source precision for rescaling, and a linear final-prefix check.
Slower experiments were reverted. Three final 50-coefficient runs give
per-case median declaration times of 0.761, 0.289, 0.427, and 0.259 seconds;
the corresponding 100-coefficient medians are 1.546, 0.866, 1.058, and
0.524 seconds. See the progress entries for controlled comparisons.

The normal Lake build passes all five tactic regression modules and
`WeightTwoCusps.Levels.HasEtaQuotientBasis.«462».Coefficients` (4084 build
jobs, final cached verification 6.073 seconds). The axiom audit passes all
96 reports: seven supporting lemmas and 89 compiled coefficient identities,
using only `propext`, `Classical.choice`, and `Quot.sound`.

The broader level-462 **Basis** build was attempted but cannot complete in
this environment: its determinant certificate producer requires `python3`,
which is missing from PATH. Its coefficient modules compile successfully;
the failure is outside `eta_coeff`. No determinant or basis source was changed.

## Numbered ideas (initial investigation order)

1. **Truncate the multiplication certificate during recursion.** Avoid
   calculating the discarded upper half of each list product. Prove that
   the truncated algorithm agrees with convolution below the precision.
2. **Skip zero rows in the multiplication checker.** Euler and dilated
   tables contain many zeros. A proved zero branch should avoid scaling
   and adding a whole row, and combine naturally with truncation.
3. **Use a Boolean prefix comparator with implicit zero padding.** Replace
   propositional list equality, `take`, and `rightpad` with a structural
   Boolean checker and a correctness theorem. This can reduce the proof
   objects allocated by reduction as well as redundant traversals.
4. **Certify Euler tables once before dilation.** Prove a generic dilation
   table lemma, then check only the shorter undilated Euler prefix. Explore
   a sequential Euler checker rather than `∀ n : Fin p` and repeated indexing.
5. **Use symbolic certificates for neutral factors.** Zero exponents and
   dilation steps above the precision give the identity prefix; eliminate
   their arithmetic checks while retaining the factor-list correspondence.
6. **Share repeated checked subproofs.** Publish intermediate power/product
   proofs or cache closed arithmetic certificates in the environment so
   final declarations do not recheck repeated proof trees. Measure the
   auxiliary-declaration overhead before retaining this.
7. **Reduce final definitional-equality work.** Explicitly bridge the computed
   divisor/exponent list to the original `unitCoefficient` once, so nested
   table proofs do not repeatedly unfold large sparse exponent functions.
8. **Change the certificate algorithm if local changes plateau.** Investigate
   sparse dot products, an Euler-product/logarithmic-derivative recurrence,
   or evaluation-based polynomial multiplication certificates, with generic
   correctness lemmas. These are larger proof investments and follow the
   lower-risk experiments. In particular, pack coefficients into a large-base
   integer: check a product modulo the base raised to the precision, with a
   proved coefficient norm bound that rules out hidden carries/cancellation.
9. **Normalize lifted coefficient lists by reflexivity.** The current
   `norm_num [rescaleCoefficients, List.range_succ]` fallback builds large
   simplification proofs. A simproc can materialize a rescaled literal list
   and let the kernel check the definitional equality directly.

## Measurement protocol

- Native Lean 4.35.0, synchronous theorem elaboration, two Lean threads,
  default heartbeats, `maxRecDepth 4096`.
- Use fresh processes and time each complete declaration, including final
  kernel checking. Record process time separately from declaration time.
- Keep literal lists in benchmark statements and regenerate candidates
  independently from their kernel certification.
- Compare identical 50-coefficient examples before/after each idea, then
  verify 100 coefficients and existing signed/lift/prefix regressions.
- Inspect axiom reports; no unchecked computation or new axioms.
- Expected literal lists are generated before process timing by an independent
  Euler-product calculation. All table generation performed inside `eta_coeff`
  is included in the recorded Lean times. Fresh processes reuse the operating
  system's filesystem cache; this is not a cold-boot benchmark.

## Progress

- 08:20 UTC: Started the two-hour window. Read the tactic, certificate lemmas,
  computable coefficient definitions, existing regression tests, and prior
  cost study. Repository files are all untracked at entry; preserve the
  existing workspace and keep source snapshots for controlled comparisons.
- 08:26 UTC: The generic truncated-multiplication correctness lemmas compile.
  An initial baseline was invalidated by overlapping a dependency rebuild
  with import loading (missing `.olean` during replacement). Discarded that
  failed run; subsequent builds and measured runs are strictly sequential.
- 08:29 UTC: Valid original-tactic 50-coefficient baselines (two fresh
  processes) passed with only `propext`, `Classical.choice`, `Quot.sound`.
  Declaration seconds, run 1 / run 2: complex462 2.261 / 1.980;
  simple462 0.961 / 0.633; heavy42 1.678 / 1.508;
  dilated462 0.973 / 0.933. Process totals 17.659 / 16.267 seconds.
  The runner is `scripts/BenchmarkEtaCertification.ps1`; raw logs and JSON
  live under `.lake/eta-opt/`. Its timer is compiled as an imported module,
  because Lean cannot execute an initializer from its defining module.
- 08:31 UTC: Original 100-coefficient baselines also pass. Declaration
  seconds, run 1 / run 2: complex462 8.220 / 8.951;
  simple462 3.844 / 3.899; heavy42 6.365 / 6.355;
  dilated462 3.901 / 4.008. Process totals 33.794 / 34.991 seconds.
  This already meets the per-form 60-second target for these raw examples;
  continue optimizing and broaden validation to actual level-462 forms.
- 08:34 UTC — **Idea 1 rejected and reverted.** Three 50-coefficient runs
  passed, but the sum of per-case median declaration times rose from
  5.463 seconds (original two-run midpoints) to 8.533 seconds. Individual medians:
  complex462 3.470, simple462 0.894, heavy42 2.563, dilated462 1.606.
  Repeated prefix slicing in recursive kernel reduction increased cost;
  the original demand-driven reduction may already discard unused tails.
  Experimental sources remain only in `.lake/eta-opt/`.
  Next: skip zero rows in the original sequential multiplication instead.
- 08:36 UTC — **Idea 2 retained.** Zero-row skipping passes three fresh
  50-coefficient runs. Per-case medians: complex462 1.486, simple462 0.575,
  heavy42 1.069, dilated462 0.562 seconds. Their sum is 3.691 seconds,
  32.4% below the 5.463-second baseline. All axiom reports remain standard.
  The multiplication correctness proof now handles the zero branch explicitly.
- 08:40 UTC — **Idea 3 rejected and reverted.** A Boolean comparator with
  implicit zero padding passed all examples but did not show a reliable
  runtime gain over zero-row skipping. Per-case medians were 2.706, 0.743,
  1.508, 0.885 seconds (sum 5.842). Process times varied from 18.3 to
  30.9 seconds, so system noise is material; no improvement is claimed.
  Next: the sequential coefficient-table checker part of idea 4, initially
  retaining the existing dilation formula to isolate the checker change.
- 08:43 UTC — **Idea 4, sequential checker retained.** Three passing
  50-coefficient runs give per-case medians 1.125, 0.433, 0.832, 0.387
  seconds (sum 2.777). This improves the retained zero-row version by
  24.8%, and the original by 49.2%. The new generic soundness lemma checks
  coefficient functions against list heads/tails, rather than universal
  `Fin` enumeration with repeated list indexing. Dilation-specific reuse
  remains a separate possible experiment.
- 08:45 UTC — **Idea 5 retained.** Generic proofs replace checks of zero
  powers, the empty product, and signed factors dilated beyond the precision.
  Three passing 50-coefficient runs give medians 1.071, 0.409, 0.837, 0.349
  seconds (sum 2.666), a modest 4.0% reduction from the previous retained
  version. The nearly unchanged heavy42 case is within timing noise.
  Beginning the packed-integer multiplication experiment from idea 8;
  `mkAuxLemma` already caches arithmetic lemmas by proposition within an
  environment, so part of idea 6 is present in the original implementation.
- 08:47 UTC: The retained changes pass two 100-coefficient runs. Ranges:
  complex462 2.970–3.015, simple462 1.358–1.528, heavy42 2.740–3.009,
  dilated462 0.779–0.783 seconds. Whole fresh processes take 19.1–19.6
  seconds. Packed multiplication is now being compiled as a separate
  generic certificate module; its bound and divisibility checks remain
  closed propositions verified by the kernel.
- 08:50 UTC — **Idea 8, packed multiplication retained.** The generic
  correctness module `PackedCertificates.lean` compiles without additional
  axioms. Three passing 50-coefficient runs give medians 0.840, 0.304,
  0.441, 0.275 seconds (sum 1.860), a further 30.2% reduction and 66.0%
  below the original. The kernel checks a bound on the sum of absolute
  coefficients and divisibility of one packed product difference by
  `base ^ precision`. The theorem proves that small coefficients cannot
  be concealed by carries. No multiplication-table reduction is needed
  inside these closed arithmetic checks.
  Added a manifest and runner for all 89 actual level-462 basis forms;
  candidates are recomputed independently as Euler products, including
  their infinity orders and oldform dilation factors.
- 08:52 UTC: Packed 100-coefficient checks pass twice: complex462
  1.584–1.588, simple462 0.872–0.879, heavy42 1.087–1.413,
  dilated462 0.612–0.615 seconds. An eight-form actual level-462
  50-coefficient sample also passes, including three dilation-1 oldforms
  and the dilation-42/33 forms. Oldform list normalization is now the
  larger remaining target; proceeding with idea 9.
- 08:56 UTC — **Idea 9, general rescaling simproc rejected and reverted.**
  The actual eight-form 50-coefficient sample passes, but changes are small
  and mixed (for example oldform index 1: 1.668 → 1.721 seconds; index 27:
  1.903 → 1.633). The original macro already tries `rfl` before `norm_num`,
  so direct definitional normalization is already available. Trying a
  narrower variant: a generic dilation-1 prefix lemma that avoids the
  rescaled list and the extra source coefficient entirely.
- 08:57 UTC — **Idea 9, dilation-1 specialization retained.** The actual
  50-coefficient sample passes. Oldform indices 1, 25, 27 improve from
  1.668 / 1.536 / 1.903 seconds to 0.455 / 0.206 / 0.413 seconds.
  A generic `gamma0Rescale_first_coeffs_one` lemma directly exposes the
  source prefix. Other sample forms remain comparable. Starting the full
  89-form 100-coefficient check, including every oldform dilation.
- 09:00 UTC: All 89 actual basis forms pass at 100 coefficients, with
  standard axiom reports. Declaration total 65.094 seconds; per-form range
  0.272–1.900 seconds; complete fresh process 76.717 seconds. The whole
  batch is close to one minute, while every individual form comfortably
  meets the target. Target-size profiling suggests revisiting large-dilation
  zero insertion. A closed arithmetic expression for the count also passes
  two 50-coefficient controls, with only a small timing effect.
- 09:04 UTC: A temporary rescaling trace explains why the general list
  simproc was ineffective: its source remained `first_coeffs (100 / d + 1)`
  rather than a literal table. Added a generic sufficient-precision lemma
  so the tactic can supply the source count as an explicit numeral, with
  a kernel-checked `m ≤ d * precision` bound. It also uses the minimal
  sufficient source count. Removed the temporary trace and general simproc.
- 09:11 UTC: Combining the numeral source count with literal zero insertion
  resolves the large-dilation cost. Two 100-coefficient probes improve from
  1.722 / 1.061 seconds to 0.501 / 0.055 seconds (indices 67 / 87).
  An experimental explicit source-evaluation fallback was never taken and
  was removed. The minimal implementation uses the generic precision bound
  and a reflexive list normalizer; running 50-coefficient validation followed
  by the complete 89-form 100-coefficient workload.
- 09:14 UTC — **Idea 9, numeral bound plus literal rescaling retained.**
  The nine-form 50-coefficient validation passes: indices 67 / 87 / 88
  take 0.142 / 0.033 / 0.035 seconds, versus 0.553 / 0.322 / 0.392 with
  the bound alone. All 89 forms pass at 100 coefficients again: declaration
  total 50.726 seconds; maximum 1.630 seconds; fresh process 62.886 seconds.
  This meets one minute for the complete serialized certification work,
  excluding process startup/imports. Continuing toward a sub-minute fresh
  process as well, with a linear final-prefix certificate (idea 7).
- 09:21 UTC — **Idea 7, linear final prefix provisionally retained.**
  Three passing 50-coefficient runs give medians 0.748, 0.272, 0.425,
  0.260 seconds (sum 1.706), 8.3% below the prior packed-table medians.
  `first_coeffs_eq_of_table_shift` uses a clamped leading-zero block,
  truncation, and padding instead of one table lookup per degree.
  Added a million-order vanishing example to guard against constructing
  an unnecessarily large zero block. Checking target-size timings next.
- 09:24 UTC — **Idea 7 retained at target size.** Both four-case
  100-coefficient runs pass. The full 89-form run passes in 54.379 seconds
  including startup/imports, meeting the stricter whole-batch one-minute
  target. Generic and concrete proofs retain only the standard axioms.
  The isolated original 50-coefficient controls reproduce the initial
  baseline closely. Preparing a full original comparison; its first
  actual-form control had invalid attribute-removal syntax and is excluded.
  Removing the earlier zero-row implementation, now superseded by packed
  products and no longer used by the tactic's arithmetic checker.
- 09:41 UTC: The isolated original 89-form 100-coefficient control passes:
  297.819 seconds in declarations, 309.876 seconds for the fresh process,
  maximum 11.177 seconds. Final cleanup passes all 89 again in 55.438
  process seconds (43.792 in declarations, maximum 1.497); every one of
  the 89 cases is faster. This is a 5.59× whole-process speedup.
  Ramanujan, the signed level-4 quotient `[-8,20,0,-8]`, level 11, and a
  signed level-15 quotient also pass 100-coefficient checks in 0.27–0.92 s.
  Default asynchronous compilation including `.olean` output passes but
  takes 66.687 s. Trying the remaining Euler-reuse part of idea 4 to reduce
  repeated checks within each individual proof.
- 09:48 UTC — **Idea 4, shared Euler prefix rejected and reverted.**
  The generic dilation lemmas compile, but the first 50-coefficient process
  exceeded a minute and consumed far more memory than the retained version.
  Stopped that benchmark and restored the measured implementation. Replacing
  repeated Euler sums by repeated lookups in the shared literal table was
  unfavorable to kernel reduction. No shared-Euler code is retained.
- 09:55 UTC: The normal Lake build passes `EtaCoefficientTests`,
  `EtaCoefficientBenchmarks`, `FirstCoeffsTests`, `RescaleCoefficientTests`,
  and `EtaOldformTests`, including the new million-order vanishing case
  and the existing degree-200 Ramanujan check at its existing resource limits.
  The combined command's basis target was initially misspelled: numeric
  directory names require `«462»` in the Lake target. Retrying that build
  with the correctly escaped target; no source change was needed.
- 10:20 UTC: Finished the final review and validation for the two-hour pass.
  Serial compilation of all 89 hundred-coefficient identities, including
  `.olean` output, passes in 55.046 seconds. The normal coefficient/tactic
  build passes, as do all 96 axiom reports. A mechanical comparison confirms
  89/89 declarations are faster and all recorded Lean source hashes match.
  The broader basis build reaches the determinant helper and fails because
  `python3` is unavailable; this is recorded separately from passing checks.
  Retained implementation is frozen; numbered ideas, rejected experiments,
  benchmark scripts, and aggregate results are available for continuation.

## Reproducing the retained implementation

Run from the repository root with the installed Lean 4.35.0 toolchain:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/BenchmarkEtaCertification.ps1 -Label final -Count 50 -Repeats 3
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/BenchmarkEtaCertification.ps1 -Label final -Count 100 -Repeats 3
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/BenchmarkEtaLevel462.ps1 -Label all-final -Count 100
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/BenchmarkEtaLevel462.ps1 -Label compiled-final -Count 100 -SerialThroughput
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/SummarizeEtaCertification.ps1
```

`SerialThroughput` compiles the same 89 declarations to an `.olean` with
`Elab.async false`, without per-declaration timers or axiom-printing commands.
`AsyncThroughput` instead uses the default asynchronous theorem checking.
Only whole-process times are reported for these two compilation modes.
For batches of declarations, the measured fast mode uses:

```lean
set_option Elab.async false
set_option maxRecDepth 4096
```

The recursion depth matches the existing level-462 files. Heartbeats are not
raised. Individual 100-coefficient declarations also work with normal
asynchronous elaboration; the batch timings distinguish their scheduling modes.

The original comparison uses the source snapshots saved at the beginning of
this session under `.lake/eta-opt/`. `PrepareEtaBaseline.ps1` clones only their
namespaces and tactic name, qualifying references to the cloned certificate
lemmas. It preserves the original arithmetic and proof algorithms. The
actual-form baseline runner disables the optimized simprocs, including during
fallback simplification, to avoid mixing implementations.

Raw logs, generated concrete Lean examples, experimental source snapshots,
and individual result files are in `.lake/eta-opt/`. The permanent aggregate
is [optimization-results.json](optimization-results.json); it includes final
source hashes, passing runs, failed/stopped runs, and verification results.

## Why packed products are checked

For tables `a`, `b`, and proposed product prefix `c`, choose
`B = ‖a‖₁ * ‖b‖₁ + ‖c‖₁ + 1`. Evaluate their coefficient polynomials at `B`.
The kernel checks the norm bound and that `B^p` divides `a(B)*b(B)-c(B)`.
The generic proof bounds the sum of absolute coefficients of the difference
by a number below `B`. Its constant coefficient is divisible by `B` and has
absolute value below `B`, so it is zero. Repeated division proves all first
`p` coefficients zero. The closed check consequently needs integer evaluation
and one packed product, rather than reduction of all convolution entries.
