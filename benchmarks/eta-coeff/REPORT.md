# eta_coeff: external-calculator cost study

Measured November 9, 2026, on the existing native Windows Lean 4.35.0 / WSL
SageMath 10.10 installation. Moving coefficient arithmetic to Sage offers
little benefit for these workloads while retaining the current certificates.
The useful optimization targets are certificate checking and the other Lean
work around those checks.

## Measured Lean costs

These are serial, per-declaration wall times, excluding process startup and
imports. The table uses the second Ramanujan run and the complete level-462
run. Candidate arithmetic means Euler-table construction, truncated
convolution, and reciprocal-table construction.

| Workload | Declaration time | Candidate arithmetic | `etaCheck` | Ideal time saved by free arithmetic |
| --- | ---: | ---: | ---: | ---: |
| Ramanujan coefficient 20 | 1.318 s | 0.0217 s | 0.476 s | 1.64% |
| Ramanujan coefficient 50 | 1.979 s | 0.0053 s | 1.896 s | 0.27% |
| Ramanujan coefficient 100 | 5.991 s | 0.0133 s | 5.889 s | 0.22% |
| Ramanujan coefficient 200 | 23.737 s | 0.0504 s | 23.563 s | 0.21% |
| All 89 level-462 prefixes, 90 coefficients each | 774.814 s | 1.672 s | 511.491 s | 0.216% |

For level 462, 2,932 calls to `etaCheck` consumed 66.0% of declaration time.
Within those calls, the synchronous `mkAuxLemma` path consumed 509.500 s;
this includes kernel verification and auxiliary-declaration construction.
The remaining 261.652 s was Lean work outside the timed arithmetic and
`etaCheck` phases. That remainder includes elaboration, simplification,
proof assembly, and final declaration checking; this study does not attribute
it more finely. It cannot be removed merely by supplying numbers from Sage.

The whole serial level-462 process took 803.022 s, including imports and
startup. This deliberately serialized experiment is different from the
earlier parallel coefficient-module build, which took 384 s. It also differs
from the 61 s basis-constructor build: that constructor reuses the already
compiled coefficient-prefix proofs.

## Measured Sage costs

The external benchmark receives the actual exponent data and precisions
used by the Lean proofs. It calculates the unit-series prefixes with Sage
integer power series and compares every coefficient against the corresponding
kernel-checked Lean table. Precisions are reduced where the q-order or a
degeneracy lift permits it. All 744 unit-prefix evaluations matched, across
three fresh-process batches and five in-process rounds for each workload.

| Workload | Fresh process, median of 3 | Fresh-process range | Warm arithmetic, median of rounds 2–5 |
| --- | ---: | ---: | ---: |
| Four Ramanujan jobs together | 3.140 s | 2.733–8.148 s | 0.00141 s |
| All 89 level-462 jobs together | 2.644 s | 2.417–2.982 s | 0.04553 s |

These fresh-process times include the existing PowerShell/WSL launcher,
Python/Sage startup, input parsing, calculation, comparison, JSON output,
and process completion. The WSL distribution and filesystem caches were
not reset between launches. The first fresh Ramanujan launch was the 8.148 s
outlier. For the level-462 batch, median Sage import time alone was 1.456 s.
Its request and response were approximately 50 KB and 27 KB respectively.

The warm arithmetic figure excludes launch, import, IPC, and JSON costs.
This prototype returns final unit-series tables, rather than every intermediate
table required by the current Lean proof construction. Its modeled benefits
are consequently optimistic; it is not an integrated replacement tactic.

## Savings and costs

Holding the remaining Lean phases fixed, let `T` be declaration time, `G`
current candidate-generation time, and `S` external-producer time. The model
is `T_new = T - G + S`.

For the complete level-462 workload:

| Scenario | Modeled change from the current serial run |
| --- | ---: |
| Completely free arithmetic | Save at most 1.672 s (0.216%) |
| One fresh Sage process for the whole batch | Add about 0.972 s |
| Persistent Sage process, arithmetic only, ignoring IPC | Save about 1.626 s (0.210%) |

Starting Sage separately for individual prefixes would repeat launch/import
costs many times and is unfavorable on this installation. A persistent
service would add lifecycle, protocol, validation, and reproducibility work
to pursue a best-case saving of roughly one or two seconds here. A JSON
candidate cache would still need its certificates checked on each fresh
elaboration. Existing compiled coefficient theorems already provide reusable
checked results to downstream basis construction.

A hypothetical 50% reduction in the `etaCheck` phase would instead save about
255.7 s, or 33.0%, in the serial level-462 experiment. This is a cost-model
scenario, not a measured optimization. Achieving it would require a cheaper
certificate/checker, fewer intermediate checks, or better reuse, with an
appropriate correctness proof. Other Lean work is another substantial target.
An arithmetic-only Sage backend is not the next optimization recommended by
these measurements.

## Controls and limits

- The production `EtaCoefficient.lean` was not edited. Instrumentation is
  generated into a separate namespace and module under `.lake/eta-profile`.
  The source digest is recorded in [results.json](results.json); it hashes
  UTF-8 source text with normalized line endings.
- Candidate timing and complete `etaCheck` timing are disjoint. The
  `check.kernel_aux` timer is nested inside `check.total` and must not be
  added to it. Full theorem declarations run with `Elab.async false`, two
  Lean threads, default `maxHeartbeats`, and `maxRecDepth 4096`.
- An initial instrumented/unmodified control differed by 15–24% on the
  larger Ramanujan cases. A subsequent adjacent pair differed by +6.35%
  at coefficient 100 and -2.25% at coefficient 200. Small cases were noisier.
  These are local wall-time observations, not precise statistical speedup
  claims. The arithmetic fraction stayed below 0.4% on the 100/200 cases
  in both instrumented runs, so that variation does not affect the decision.
- The full 89-prefix profile was run once. The results cover the supplied
  level-462 data and Ramanujan indices through 200; substantially larger
  precisions or different certificate algorithms need separate measurements.
- All profiled Lean proofs passed. The Ramanujan axiom reports contain only
  `propext`, `Classical.choice`, and `Quot.sound`. Sage outputs were compared
  with the Lean tables and never used to bypass kernel verification.

## Reproducing the study

Run these commands from the project root, using the installed Python and
Sage/WSL environment. The generated artifacts and raw logs stay under
`.lake/eta-profile`.

```powershell
python3 scripts/profile_eta_coeff.py prepare
powershell -NoProfile -File scripts/ProfileEtaCoefficient.ps1 -Phase instrumentation
powershell -NoProfile -File scripts/ProfileEtaCoefficient.ps1 -Phase tau
powershell -NoProfile -File scripts/ProfileEtaCoefficient.ps1 -Phase level462
powershell -NoProfile -File scripts/ProfileEtaCoefficient.ps1 -Phase baseline
python3 scripts/profile_eta_coeff.py summarize
powershell -NoProfile -File scripts/ProfileEtaCoefficientSage.ps1 -Workload TauProfile
powershell -NoProfile -File scripts/ProfileEtaCoefficientSage.ps1 -Workload Level462Profile
python3 scripts/profile_eta_coeff.py analyze
```

For the repeated control used here, the first `TauProfile.log` and
`TauBaseline.log` were copied into a `repeats/` subdirectory with
`-run1.log` suffixes, then the `tau` and `baseline` phases were rerun
consecutively. [results.json](results.json) preserves both controls, each
profiled declaration, and all Sage launch/round timings. Process-duration
summaries and raw Lean/Sage logs are in `.lake/eta-profile`.
