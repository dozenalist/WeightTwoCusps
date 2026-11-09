module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 108

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-2) η(18z)`; see
[the local level table](../../TABLE.md#level-108).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 19 (zero-based) at level 216; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-216).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-2) η(18z)` at level 108. -/
abbrev cuspForm_108_eta_1m2_2p1_3p6_6m2_18p1 : gamma0CuspForms 108 :=
  etaQuotientCuspForm 108 sparse![108; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 17 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_1m2_2p1_3p6_6m2_18p1_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_1m2_2p1_3p6_6m2_18p1 =
    [0, 1, 2, 4, 2, 2, 0, 3, 2, 0, 0, -2, 0, -3, -2, 0, -4, 0, 0, -3,
     -6, -16, 0, -4, 0, -5, -8, 0, -2, 4, 0, -4, 2, 0, 0, -2, 0, 3, 4, 8,
     0, -4, 0, 8, 6, 0, 0, 4, 0, 10, 8, 0, 10, 6, 0, 0, -2, 32, 0, 8,
     0, -9, 10, 0, 8, -8, 0, 9, 0, 0, 0, 0, 0, 9, 4, -20, -14, 2, 0, -3,
     -6, 0, 0, -2, 0, 0, -20, 0, 0, -12, 0, -25, 12, -16, 0, 4, 0, -3, -12, 0] := by
  eta_coeff

end WeightTwoCusps
