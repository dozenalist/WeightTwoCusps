module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 60

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(5z)^(-1) η(6z)^(-2) η(10z) η(12z) η(15z)^3 η(30z)^(-1)`; see
[the local level table](../../TABLE.md#level-60).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 6 (zero-based) at level 300; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-300).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(5z)^(-1) η(6z)^(-2) η(10z) η(12z) η(15z)^3 η(30z)^(-1)` at level 60. -/
abbrev cuspForm_60_eta_1m3_2p8_3p1_4m3_5m1_6m2_10p1_12p1_15p3_30m1 : gamma0CuspForms 60 :=
  etaQuotientCuspForm 60 sparse![60; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 4 => -1, 5 => -2, 9 => 1, 11 => 1, 14 => 3, 29 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_60_eta_1m3_2p8_3p1_4m3_5m1_6m2_10p1_12p1_15p3_30m1_first_coeffs :
    first_coeffs 100 cuspForm_60_eta_1m3_2p8_3p1_4m3_5m1_6m2_10p1_12p1_15p3_30m1 =
    [0, 1, 3, 1, -3, -1, 1, 2, 1, -5, -1, 0, -1, 2, -8, -1, 1, -6, 3, -4,
     1, 2, -4, 6, 3, 1, 2, 7, 8, 6, -3, -4, 1, 0, 14, -2, -3, 2, -4, 2,
     -3, 6, -8, -10, 4, 5, 0, -6, -5, -3, 3, -6, -2, -6, 1, 0, -8, -4, -14, 12,
     3, 2, 16, -10, -7, -2, 4, 2, -14, 6, 8, -12, 1, 2, -6, 1, 4, 0, 6, 8,
     5, 1, -2, 6, 8, 6, -4, 6, 4, -6, -1, 4, 0, -4, 8, 4, 3, 2, 11, 0] := by
  eta_coeff

end WeightTwoCusps
