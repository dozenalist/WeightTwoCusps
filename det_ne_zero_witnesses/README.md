# Determinant witnesses

`cuspFormBasis` and `etaQuotientBasis` use the pinned `Determinant` dependency's
`det_ne_zero!` tactic to generate these JSON certificates. Filenames identify
the full integer coefficient table by dimension and SHA-256 digest.

Keep the JSON files with the project to replay certificates without Sage.
Replay uses standard Python and checks the mathematical certificate again in
Lean's kernel. Triangular matrices require no stored certificate.

For explicit cache-only replay of a coefficient determinant:

```lean
by
  q_expansion_matrix
  det_ne_zero! { cusp_basis_det_config% with policy := .cacheOnly }
```
