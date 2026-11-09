module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 60

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(5z)^3 η(6z)^(-3) η(10z)^(-3) η(12z) η(15z)^(-3) η(20z) η(30z)^6 η(60z)^(-2)`; see
[the local level table](../../TABLE.md#level-60).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 2 (zero-based) at level 300; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-300).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(5z)^3 η(6z)^(-3) η(10z)^(-3) η(12z) η(15z)^(-3) η(20z) η(30z)^6 η(60z)^(-2)` at level 60. -/
abbrev cuspForm_60_eta_1m3_2p6_3p3_4m2_5p3_6m3_10m3_12p1_15m3_20p1_30p6_60m2 : gamma0CuspForms 60 :=
  etaQuotientCuspForm 60 sparse![60; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 4 => 3, 5 => -3, 9 => -3, 11 => 1, 14 => -3, 19 => 1, 29 => 6, 59 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_60_eta_1m3_2p6_3p3_4m2_5p3_6m3_10m3_12p1_15m3_20p1_30p6_60m2_first_coeffs :
    first_coeffs 100 cuspForm_60_eta_1m3_2p6_3p3_4m2_5p3_6m3_10m3_12p1_15m3_20p1_30p6_60m2 =
    [0, 1, 3, 3, 1, -1, -3, -6, -7, -1, 3, 0, -1, 2, 0, -3, 5, 10, 3, -4,
     1, -2, -12, -2, 7, 1, -6, 1, 0, -10, -3, 12, 9, 0, 6, 6, 1, 2, 12, 6,
     -7, -10, 0, -2, -4, 1, 0, 2, -5, 13, 3, -2, -2, -6, -3, 0, 0, -12, -6, -4,
     -1, -14, 0, -10, -19, -2, 12, -6, 2, 10, 0, 4, -7, 2, -30, 3, 4, 0, 6, 8,
     5, 9, 30, 14, 0, -10, 12, 2, 28, 26, 3, -12, 0, 4, 24, 4, -9, 2, -21, 0] := by
  eta_coeff

end WeightTwoCusps
