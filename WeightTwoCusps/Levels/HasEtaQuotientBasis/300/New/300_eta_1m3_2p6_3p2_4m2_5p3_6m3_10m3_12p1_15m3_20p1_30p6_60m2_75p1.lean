module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(5z)^3 η(6z)^(-3) η(10z)^(-3) η(12z) η(15z)^(-3) η(20z) η(30z)^6 η(60z)^(-2) η(75z)`; see
[the local level table](../../TABLE.md#level-300).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(5z)^3 η(6z)^(-3) η(10z)^(-3) η(12z) η(15z)^(-3) η(20z) η(30z)^6 η(60z)^(-2) η(75z)` at level 300. -/
abbrev cuspForm_300_eta_1m3_2p6_3p2_4m2_5p3_6m3_10m3_12p1_15m3_20p1_30p6_60m2_75p1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 4 => 3, 5 => -3, 9 => -3, 11 => 1, 14 => -3, 19 => 1, 29 => 6, 59 => -2, 74 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m3_2p6_3p2_4m2_5p3_6m3_10m3_12p1_15m3_20p1_30p6_60m2_75p1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m3_2p6_3p2_4m2_5p3_6m3_10m3_12p1_15m3_20p1_30p6_60m2_75p1 =
    [0, 0, 0, 0, 1, 3, 3, 2, 2, 0, -3, -2, 2, 2, 0, 1, 1, -2, 0, 7,
     5, 1, 2, 2, -1, -1, 4, 2, -2, -2, 1, -1, -4, -2, 0, -2, -3, 2, 0, -3,
     -1, 4, 0, -4, -4, -3, -8, -6, 0, -7, -1, -2, 0, 0, 1, -4, -6, 2, 2, 0,
     -3, 1, -6, 0, 5, 2, -6, -4, -2, 2, 4, 8, 2, -4, 6, -3, 6, -2, -4, -8,
     -7, -2, 0, -2, -2, 2, -2, -2, -6, 0, -3, -1, 2, 2, -16, -4, -1, 0, -2, 2] := by
  eta_coeff

end WeightTwoCusps
