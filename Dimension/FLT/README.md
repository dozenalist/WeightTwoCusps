# Sources for the principal-level dimension formula

This directory contains a reduced extraction supporting five results from
[Anthropic's `fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem)
at revision `6e837e75355538c7f80bab5b956861e86c4eacc2`:

- `ModularCurve.twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma`
- `ModularCurve.six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq`
- `ModularCurve.periodMapOf_mem_parabolicHoms`
- `ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero`
- `ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp`

The original import closure had 439 Lean modules. The current extraction has
178 modules and about 87,400 lines, including three local import bundles
and one command helper.
The original library is not a Lake dependency. External imports use Mathlib
and Lean core only; each copied file has a provenance header.

The extraction removes the Hecke, Galois-representation, and Frobenius material
which entered through unused imports. Period definitions retain only the
general finite-index subgroup construction. Repeated rational-function-field
proofs are shared, compatibility code is restricted to additive automorphisms,
and full Mathlib imports are replaced by explicit module lists.

The residue-theorem route is specialized to characteristic zero, removing the
positive-characteristic Cartier argument. The final lower bound takes
finite-dimensionality of weight-two cusp forms as an instance, supplied by the
period argument, instead of importing a separate theorem for all weights. Duplicate theorem
wrappers and their proof modules are removed wherever the retained definition
files already prove the same result. The remaining 152 public statement
wrappers are consolidated into their proof modules; `EndScopes.lean` closes
the solution-local scopes before each public statement without adding any
mathematical declarations.
These are deliberate restrictions of the copied results to the hypotheses
needed here. Other changes port the source to Lean/Mathlib 4.35.0, including
module visibility, renamed APIs, and proof elaboration adjustments.

The rational-function residue-degree theorem is a short corollary of the
curve-over-a-field result, removing a separate 1,300-line proof and eleven
now-unused evaluation/reciprocity support modules.

The first result supplies the lower bound through algebraic function fields and
Riemann–Roch. The second computes the rank of integral parabolic homomorphisms.
The last three construct an injective real period map and identify the real and
integral ranks, which give the upper bound. Here the cusp-form spaces are
Mathlib's analytic `CuspForm` spaces.

`import-closure.json` records the actual local import graph and these five roots.
The upstream files target Lean 4.33.1 and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

The retained extraction, including the algebraic lower bound and principal-level
equality, passes the full project build with Lean/Mathlib 4.35.0. The downstream
positive-level dimension formulas for `Γ(N)`, `Γ₀(N)`, and `Γ₁(N)` are now proved.
Their axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.
See [the continuation notes](../PROGRESS_2026-11-04.md) for the build and audit logs.

The downstream finite-stabilizer argument in `Dimension/GroupTheory/BassSerreHoms.lean`,
`BassSerreCochains.lean`, and `BassSerreRank.lean` reuses this extraction's
Bass--Serre tree and connected-transversal constructions. The transversal-edge
equivalence in `BassSerreRank.lean` adapts the corresponding proof from
`S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.lean`; its source
attribution and Apache notice are retained in the downstream file.

The source is distributed under the Apache 2.0 license. See `LICENSE`, `NOTICE`,
and `ATTRIBUTION_UPSTREAM.md` for the original license and third-party credits.
