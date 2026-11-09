# Source of the elementary index calculation

The proofs in `../Gamma_0/Index.lean`, `../Gamma_1/Index.lean`, and
`../Gamma/CongruenceIndex.lean` adapt Filip Najman's
[normalizer-lean](https://github.com/F-Najman/normalizer-lean), commit
`1f4c27ec11da475383f69e6f82e2837a0cb54fd0`:

- `NormalizerLean/Index.lean`: the prime-step coset count and the index of Γ₀(N).
- `NormalizerDelta/XNOrder.lean`: the upper-right-entry map for Γ₁(N), the totient
  identity, and the principal-level index formula.

Only elementary integer-matrix and subgroup calculations are copied. The
diagonal-entry map to `(ZMod N)ˣ` is proved directly using Bézout, avoiding
the upstream generalized congruence-subgroup and normalizer dependencies.
The extraction imports Mathlib directly and has no FLT imports.
The full and projective index formulas for all three groups have passed Lean 4.35.0.

The source is licensed under Apache 2.0; see `LICENSE`.
