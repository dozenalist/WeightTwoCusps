module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 60

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(5z)^(-3) η(6z)^(-2) η(10z)^8 η(12z) η(15z) η(20z)^(-3) η(30z)^(-2) η(60z)`; see
[the local level table](../../TABLE.md#level-60).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 5 (zero-based) at level 300; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-300).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(5z)^(-3) η(6z)^(-2) η(10z)^8 η(12z) η(15z) η(20z)^(-3) η(30z)^(-2) η(60z)` at level 60. -/
abbrev cuspForm_60_eta_1m3_2p8_3p1_4m3_5m3_6m2_10p8_12p1_15p1_20m3_30m2_60p1 : gamma0CuspForms 60 :=
  etaQuotientCuspForm 60 sparse![60; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 4 => -3, 5 => -2, 9 => 8, 11 => 1, 14 => 1, 19 => -3, 29 => -2, 59 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_60_eta_1m3_2p8_3p1_4m3_5m3_6m2_10p8_12p1_15p1_20m3_30m2_60p1_first_coeffs :
    first_coeffs 100 cuspForm_60_eta_1m3_2p8_3p1_4m3_5m3_6m2_10p8_12p1_15p1_20m3_30m2_60p1 =
    [0, 1, 3, 1, -3, -1, 3, 8, 3, -11, -3, 0, -3, 2, -12, -1, -3, -18, 3, -4,
     3, 8, 0, 12, 3, 1, 6, 13, 12, 18, -3, -16, 3, 0, 18, -8, -3, 2, -12, 2,
     -3, 18, -12, -16, 0, 11, 0, -12, -3, -15, 3, -18, -6, -6, 3, 0, -12, -4, -18, 24,
     3, 14, 24, -16, -3, -2, 0, 8, -18, 12, 12, -24, 3, 2, 6, 1, 12, 0, 6, 8,
     3, 1, -18, 0, 12, 18, -12, 18, 0, -30, -3, 16, 0, -16, 0, 4, 3, 2, 27, 0] := by
  eta_coeff

end WeightTwoCusps
