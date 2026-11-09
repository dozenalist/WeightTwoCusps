## Instructions for agents adding a level

Produce the complete `N/` folder, export its basis from `WeightTwoCusps.lean`,
and finish the checks below. The [level table](TABLE.md) supplies the
cuspidal eta exponent vectors; this README specifies how to turn them into
named forms, coefficient certificates, and a complete basis. Levels 15,
28, 35, and 40 illustrate an LMFDB newform, oldform lifts, an eta basis in
the newspace, and an eta complement to an oldspace, respectively.

### 1. Determine the cusp-form basis

1. Select a row with `dim S₂ > 0` and `Full eta basis = YES`. These columns
   preserve `Dimension_S2` and `S2_spanned_by_cuspidal_eta_quotients` from
   the report. A zero-dimensional space needs no nontrivial folder. A
   `NO` row supplies only the cuspidal eta span, so its vectors cannot be
   advertised as a basis of the whole cusp-form space.
   Needed cusp forms at these incomplete levels belong in the sibling
   `Levels/WithoutEtaQuotientBasis/N/` folder, as described below.
2. Open the table's `Level N` block and copy **every** vector in its
   `Basis_cuspidal_eta_S2` list, preserving the order. This list has type
   `List (Fin N → ℤ)`; give it that expected type if copied into Lean.
   `Basis_eta_M2` describes a different space and must not be substituted.
   Check that the list length is `dim S₂` and agrees with `gamma0Dimension N`.
3. Decode each vector as `∏ η(mz)^r(m)`: index `m - 1` in `sparse![N; ...]`
   is the exponent of `η(mz)`. Unlisted entries are zero. Preserve negative
   exponents and the ambient level `N`, even if the product also occurs
   at a smaller level. The constructor checks modularity and strict
   vanishing at every cusp; do not weaken those conditions to make an
   incorrect vector compile.
4. Identify the new and old contributions using proper divisors of `N`
   and explicit sources. A lift from level `M` has the form `f(dz)` with
   `M * d ∣ N`; include dilation one when needed. Use the original source
   and the total dilation, so a lift already present at an intermediate
   level is not counted twice. For example, lifting `f(2z)` again by three
   is the same function as the original source lifted by six.
5. Classify each table vector using the naming rules below: an identified
   oldform lift, an exactly identified LMFDB newform, or a remaining eta
   basis vector. A form outside the oldspace need not lie in the canonical
   newspace: it may simply complement the oldspace. Membership in the
   newspace also does not imply that it is a Hecke eigenform.
6. Keep one basis entry for each table vector. Express a vector that is
   exactly an identified lift using the oldform constructor and certify
   its eta identity. Do not append that lift a second time. If a desired
   new/old adapted basis differs from the table basis, document the change
   of spanning set and certify the resulting full basis; do not assume
   that every newform or independent oldform lift is itself a table vector
   or a single eta quotient. The default is the table basis in table order.

For each form, record the table section, its eta expression, any source
URL used for identification, and its mathematical role in the module
documentation. The table supplies no LMFDB labels or new/old decomposition.

### 2. Create the files and use the established names

Keep the existing `New/` and `Old/` layout, creating these directories only
when they have entries. `New/` contains both identified newforms and the
remaining directly defined eta basis vectors. Its name alone makes no
claim that every declaration is a Hecke newform or lies in the newspace.
Do not introduce an `Eta/` directory or move existing declarations.

```text
N/
  Basis.lean
  New/
    N_2_a_a.lean
    N_eta_<factors>.lean
  Old/
    M_2_a_a_old_N_1.lean
    M_2_a_a_old_N_d.lean
```

Name identified oldform lifts with the oldform rule, even if the source
has an LMFDB label. For other forms, use the LMFDB rule when the exact
identification is established, and the eta exponent rule otherwise.
Rename the associated coefficient theorems and every reference whenever
a form's declaration is renamed.

#### Supporting forms at levels without a full eta basis

Use `WeightTwoCusps/Levels/WithoutEtaQuotientBasis/` for levels whose table
row has `Full eta basis = NO`. Create a level subfolder only when a cusp
form from that level is needed, for example as the original source of an
oldform at a larger level. Define the needed eta quotients there using the
same `New/` and `Old/` subfolders, naming rules, module structure, and
documentation as above. Do not create a `Basis.lean` file or claim that
these forms span the whole cusp-form space.

For example, level 23 has cusp-space dimension two but cuspidal eta rank
one. Its eta quotient `η(z)²η(23z)²` is needed for the first two table
vectors at level 46. Define the source in
`Levels/WithoutEtaQuotientBasis/23/New/23_eta_1p2_23p2.lean`, with declaration
`cuspForm_23_eta_1p2_23p2`. Its level-46 lifts belong in
`HasEtaQuotientBasis/46/Old/23_eta_1p2_23p2_old_46_1.lean` and
`HasEtaQuotientBasis/46/Old/23_eta_1p2_23p2_old_46_2.lean`, importing that
source module explicitly. Retain the original source and total dilation
when later levels reuse either lift.

Every supporting form must have the same kernel-checked 100-coefficient
prefix and generated coefficient simp theorems required in section 3. Supporting
oldforms must also have the `eq_eta` identity from section 4. Record the
source table section and its partial-span status; an exponent-based name
makes no assertion that the form is a normalized Hecke newform.

Export supporting form modules individually from `WeightTwoCusps.lean`,
using imports such as
`WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«23».New.«23_eta_1p2_23p2»`.
The coefficient-prefix fallback in section 3 applies here too. They
receive the same build and axiom checks as forms at complete levels,
but no dimension, independence, or full-basis certificate is required.
Leave zero-rank levels without a folder unless a specific additional
cuspidal eta quotient has been established and is needed.

A needed original source may not itself occur among the report's chosen
vectors at its own level. In that case certify its eta quotient with the
same constructor and document the table vector at the larger level that
requires it. If its source level has a full eta basis, keep the additional
source in that level's `New/` directory and import it from `Basis.lean`,
but do not append it to the table-ordered basis. If its level has no full
eta basis, use `WithoutEtaQuotientBasis/` as above.

#### Identified LMFDB newforms

Use the **actual complete LMFDB newform label**, replacing dots with
underscores and prefixing `cuspForm_`. For example, `15.2.a.a` gives
`cuspForm_15_2_a_a`, normally in `New/15_2_a_a.lean`. Preserve the actual
character and orbit components; do not assign `a.a` by default, use a
space label as a form label, or invent an LMFDB-style label.

An LMFDB-style declaration asserts identification with that exact
normalized Hecke newform. Verify the eta expression or compare exact
q-expansions through the weight-two Sturm bound, including degree `B`
from the table. Record the source URL and comparison range. Coefficient
one at degree one is necessary for this normalization but is not enough
to establish the identification. Existence of an LMFDB entry at the same
level also does not identify an arbitrary eta basis vector with it.

#### Eta basis vectors without an established LMFDB identification

For a directly defined cusp form with no matching LMFDB newform entry, or
whose exact identification has not been established, use
`cuspForm_N_eta_<factor>_<factor>_...`. This includes eta complements and
newspace basis vectors that are not normalized Hecke newforms. The name
records the product without claiming that no related LMFDB entry exists.

For `∏ η(mz)^r(m)`, generate the factors as follows:

1. Combine exponents at the same argument and discard zero exponents.
2. Sort the actual positive eta arguments `m` in increasing numerical order.
3. Encode a positive exponent `r` as `<argument>p<exponent>`; encode a
   negative exponent as `<argument>m<absolute-exponent>`. Replace the
   placeholders with decimal numerals; the middle letter is literally
   `p` (plus) or `m` (minus).
   Thus `5p2` means `η(5z)²`, and `10m1` means `η(10z)⁻¹`.
4. Include exponent one explicitly (`1p1`, not `1`), and join the tokens
   with underscores after `cuspForm_N_eta_`. Use ordinary decimal numerals
   without leading zeros. `N` is the ambient level of `gamma0CuspForms N`.

In particular, a sparse entry `i => r` contributes argument `i + 1` to
the name, not `i`. Do not use `_sq`, `_complement`, a table row number,
or a basis index as a replacement for the exponent encoding.

| Eta expression | Declaration name |
| --- | --- |
| `η(z)η(2z)η(15z)η(30z)` at level 30 | `cuspForm_30_eta_1p1_2p1_15p1_30p1` |
| `η(z)η(3z)η(11z)η(33z)` at level 33 | `cuspForm_33_eta_1p1_3p1_11p1_33p1` |
| `η(z)²η(35z)²` at level 35 | `cuspForm_35_eta_1p2_35p2` |
| `η(z)η(5z)η(7z)η(35z)` at level 35 | `cuspForm_35_eta_1p1_5p1_7p1_35p1` |
| `η(5z)²η(7z)²` at level 35 | `cuspForm_35_eta_5p2_7p2` |
| `η(2z)⁵η(5z)²η(20z)/(η(z)²η(4z)η(10z))` at level 40 | `cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1` |

Use the declaration name without `cuspForm_` as the filename. For example,
the level-40 eta quotient belongs in
`40/New/40_eta_1m2_2p5_4m1_5p2_10m1_20p1.lean`. When renaming a form,
rename its file within the same directory and update every module import
to match. Keep the `New/` and `Old/` directory placement unchanged.

#### Oldform lifts

Retain the oldform notation `cuspForm_<source-stem>_old_N_d`. For an LMFDB
source this is `cuspForm_M_2_a_a_old_N_d`. It records **both** the ambient
level `N` and the dilation `d`, and means exactly `f(dz)` without a scalar
factor. For example, `cuspForm_11_2_a_a_old_44_2` means the dilation-two
lift of `cuspForm_11_2_a_a` viewed at level 44. The dilation-one lift must
still end in `_old_N_1`.

If the original lower-level source has an exponent-based eta name, retain
its complete stem before `_old_N_d`, for example
`cuspForm_35_eta_1p2_35p2_old_70_2`. This notation asserts a degeneracy lift
of the named lower-level cusp form; it does not assert that the source is
a Hecke newform. Do not replace an identified lift's name by its target
eta encoding or nest `_old_` suffixes for successive lifts.

#### File structure and imports

Every Lean file starts with `module`, explicit `public import` lines, and
module documentation, followed by:

```lean
@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

-- Definitions and theorems go here.

end WeightTwoCusps
```

Import individual files using quoted numeric components, for example
`WeightTwoCusps.Levels.HasEtaQuotientBasis.«14».New.«14_2_a_a»`.
The directories themselves are not modules: do not import `...«14».New`
unless an actual `14/New.lean` aggregator has been created. Form files must
not import the root `WeightTwoCusps` module, which would create a cycle.

### 3. Define each direct eta quotient and certify its coefficients

Import `WeightTwoCusps.Tactic.Basic` for `sparse!` and
`WeightTwoCusps.Tactic.EtaCoefficient` for the constructor and `eta_coeff`.
For example, the definition in `15/New/15_2_a_a.lean` is:

```lean
abbrev cuspForm_15_2_a_a : gamma0CuspForms 15 :=
  etaQuotientCuspForm 15 sparse![15; 0 => 1, 2 => 1, 4 => 1, 14 => 1]
```

The same constructor applies to a form without an LMFDB identification:

```lean
abbrev cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1 : gamma0CuspForms 40 :=
  etaQuotientCuspForm 40 sparse![40; 0 => -2, 1 => 5, 3 => -1, 4 => 2, 9 => -1, 19 => 1]
```

To compute coefficient lists from a table vector, first compute
`v = (∑ m * r(m)) / 24` and expand

```text
q^v * ∏_{m : r(m) ≠ 0} ∏_{j ≥ 1} (1 - q^(m*j))^r(m).
```

Use exact integer arithmetic and truncate the formal power series at the
required degree. Negative exponents require the inverse-power series,
not a finite positive-power product. For a lift, take the source series
and replace `q` by `q^d`, inserting zero coefficients at other degrees.
The first nonzero degree is `v`, not necessarily one. For the stored
prefix compute degrees 0 through 99; if a Sturm comparison requires more,
compute and compare through at least `max(99, B)`. An external coefficient
calculation supplies candidate values; `eta_coeff` must certify them.

For **every** form, including oldforms, supply:

- `@[eta_simps] theorem <name>_first_coeffs`, proving
  `first_coeffs 100 <name> = [...]` by `eta_coeff`. Give all 100 actual
  coefficients, starting with degree zero; the list ends at degree 99.
  Compute the list from the eta product or
  lift, and let Lean certify it. Never insert an unchecked placeholder.
- The attribute generates all 100 `@[simp]` theorems
  `<name>_first_coeffs_coeff_0` through `<name>_first_coeffs_coeff_99`.
  Each proof extracts an entry from the checked prefix; do not write
  individual coefficient lemmas or recompute coefficients for them.
  `WeightTwoCusps.Tactic.EtaCoefficient` also imports this attribute.

Use the default `maxHeartbeats` for these proofs. A local increase of
`maxRecDepth` is permitted when needed, provided the proofs still finish
within the default heartbeat limit. Stored prefixes contain 100 coefficients;
optimize the certificate computation if a proof exceeds that limit.
Do not raise `maxHeartbeats` to retain a longer prefix. The stored prefix
does not reduce any required Sturm comparison range.

These requirements also apply to every supporting form under
`Levels/WithoutEtaQuotientBasis/`; only the full-basis construction is
omitted there.

Copy the shape of these declarations from an existing form and update
every identifier and value. A normalized newform has coefficient one at
degree one. A lift `f(dz)` has zero coefficients outside multiples of `d`;
its first nonzero term need not have degree one. If a source identification
requires a Sturm comparison, check through the level's weight-two Sturm
bound, even when it exceeds the stored 100-coefficient prefix.

### 4. Define oldforms through Oldforms and use `eta_oldform`

Import the original source form, `WeightTwoCusps.Oldforms`, and
`WeightTwoCusps.Tactic.EtaOldform`. Use `gamma0Rescale f d` when the target
is exactly `M * d`, and `gamma0RescaleToLevel f d (by decide)` for any
ambient level `N` divisible by `M * d`. In particular, the latter handles
dilation one without changing the underlying function. These constructors
represent exactly `f(dz)`, with no additional scalar factor.

Each oldform must have a `<name>_eq_eta` theorem proved by `eta_oldform`:

```lean
abbrev cuspForm_14_2_a_a_old_28_1 : gamma0CuspForms 28 :=
  gamma0RescaleToLevel cuspForm_14_2_a_a 1 (by decide)

theorem cuspForm_14_2_a_a_old_28_1_eq_eta :
    cuspForm_14_2_a_a_old_28_1 =
      etaQuotientCuspForm 28 sparse![28; 0 => 1, 1 => 1, 6 => 1, 13 => 1] := by
  eta_oldform
```

For dilation `d`, move the source exponent at index `m - 1` to index
`d * m - 1` in the target vector. Keep its integer value unchanged.
The tactic follows named definitions, restrictions, and successive lifts,
applies the Oldforms application theorems, and checks the exact finite
eta-product identity. It evaluates numeral levels, dilation factors, and
closed integer exponent vectors, including negative exponents and named
vectors. It also accepts the reversed equality. There is no need to list
divisors, unfold source names manually, or compare a finite q-prefix.
Symbolic parameters and identities requiring unrelated analytic relations
are outside its scope; a mismatched product must fail.

### 5. Construct and export the full basis

`N/Basis.lean` imports **all** its form files and
`WeightTwoCusps.Basis.Constructor`. Define `level_N_etaBasis` using
`cuspFormBasis` with a vector in the documented basis order, and tag the
definition with `@[eta_simps]`. For example:

```lean
@[eta_simps] def level_28_etaBasis : Module.Basis (Fin 2) ℂ (gamma0CuspForms 28) :=
  cuspFormBasis ![cuspForm_14_2_a_a_old_28_1, cuspForm_14_2_a_a_old_28_2]
```

The attribute generates `level_28_etaBasis_0` and `level_28_etaBasis_1` as
simp theorems, and analogously `level_N_etaBasis_i` for every other basis.
Do not write these lemmas manually. The constructor
checks both dimension and independence. It defaults to coefficient columns
1 through the number of forms. If that minor vanishes, choose and certify
an independent set of columns using `(c := ![...])`; do not change the
mathematical basis solely to hide a failed certificate. See the
[basis API](../../Basis/README.md) for custom columns and explicit proofs.

For example, level 40 keeps the table's two oldform lifts followed by its
eta complement:

```lean
@[eta_simps] def level_40_etaBasis : Module.Basis (Fin 3) ℂ (gamma0CuspForms 40) :=
  cuspFormBasis ![cuspForm_20_2_a_a_old_40_1, cuspForm_20_2_a_a_old_40_2,
    cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1]
```

Add `public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«N».Basis`
to `WeightTwoCusps.lean`, replacing `N` with the numeral. Document the
basis order, names, identifications, and sources in the level files.
For levels under `WithoutEtaQuotientBasis/`, export the individual form
files instead and omit this basis-construction step.
`TABLE.md` preserves the supplied report data: do not alter its exponent
vectors, dimensions, or report order to accommodate a naming choice.

### 6. Finish verification before reporting completion

Run the main library build and the relevant regressions:

```text
lake build WeightTwoCusps WeightTwoCusps.Tactic.EtaOldformTests WeightTwoCusps.Oldforms.Tests WeightTwoCusps.Basis.Tests WeightTwoCusps.Tactic.RescaleCoefficientTests WeightTwoCusps.Tactic.BasisDeterminantTests
```

The main import must expose every new form, including supporting forms
at incomplete levels, and every full `level_N_etaBasis`. Check the
new basis, coefficient tables, and oldform identities with `#print axioms`
in a temporary audit file: only `propext`, `Classical.choice`, and
`Quot.sound` should occur. Leave no `sorry`, `admit`, new axioms, or
`native_decide` certificates. If the tactic is extended, add regression
cases in `Tactic/EtaOldformTests.lean`, including rejection of an incorrect
identity, and rerun the checks. Report the completed level folders and the
actual validation result.

Before reporting completion, account for every vector in the selected
table block exactly once, check that each name follows its applicable
rule, and verify that no stale declaration references or module imports
remain. Filenames must match their declaration stems. Preserve LMFDB labels
and oldform names when only the remaining eta declarations are renamed.

The remaining folders through level 500 have been generated, but their full
library build and axiom audit are not yet complete. The determinant regressions
include numerical matrices through size 12 and the level-42 basis. The largest
basis occurs at level 462 and has dimension 89. Its matrix test using mapped
lists exceeds the default heartbeat budget during entry reduction, and the
corresponding matrix-literal check remains unfinished. The full level rollout
is paused at this resource limitation. Do not treat the generated folders as fully verified until the
checks above pass.

The optimization work recorded in [OPTIMIZATION_PROGRESS.md](../../../../OPTIMIZATION_PROGRESS.md)
adds checked 90-coefficient prefixes for all 89 level-462 forms and improves
reciprocal-table evaluation. Level 462 retains its plain `cuspFormBasis`
application and table order; no separate numerical determinant certificate is
used. Its compilation under the default heartbeat budget and the complete
levels-1–500 validation remain outstanding.
