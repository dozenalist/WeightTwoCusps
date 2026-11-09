# Supporting cuspidal eta quotients

These folders contain only the original eta-quotient sources needed by
full-basis levels through 500. Their source levels have `Full eta basis = NO`
in [the level table](../HasEtaQuotientBasis/TABLE.md): the available eta span
does not give a basis of the whole cusp-form space. There are no `Basis.lean`
files here.

Each form has a kernel-checked 100-coefficient prefix tagged with `@[eta_simps]`,
which generates simp lemmas for coefficients zero through 99, using the same conventions as
[the generation instructions](../HasEtaQuotientBasis/README.md). Forms without
an exact normalized-newform identification use eta-exponent names.

Additional sources absent from their own level's chosen table list are
explicitly documented with a target table vector that requires them. The
eta constructor still certifies modularity and strict vanishing at all cusps.

| Level | Needed sources |
| --- | --- |
| 23 | 1 |
| 38 | 2 |
| 51 | 1 |
| 55 | 1 |
| 63 | 2 |
| 66 | 3 |
| 69 | 1 |
| 75 | 2 |
| 76 | 2 |
| 77 | 1 |
| 92 | 1 |
| 98 | 4 |
| 99 | 1 |
| 102 | 7 |
| 105 | 4 |
| 114 | 9 |
| 136 | 2 |
| 138 | 4 |
| 154 | 9 |
| 156 | 2 |
| 175 | 4 |
| 189 | 7 |
| 195 | 8 |
| 196 | 2 |
| 198 | 11 |
| 225 | 3 |
| 243 | 9 |
