module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-3) η(2z)^6 η(3z) η(5z) η(6z)^(-2) η(8z)^(-1) η(10z)^(-2) η(12z) η(15z) η(20z) η(60z)^2 η(120z)^(-1)`; see
[the local level table](../../TABLE.md#level-240).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z) η(5z) η(6z)^(-2) η(8z)^(-1) η(10z)^(-2) η(12z) η(15z) η(20z) η(60z)^2 η(120z)^(-1)` at level 240. -/
abbrev cuspForm_240_eta_1m3_2p6_3p1_5p1_6m2_8m1_10m2_12p1_15p1_20p1_60p2_120m1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -3, 1 => 6, 2 => 1, 4 => 1, 5 => -2, 7 => -1, 9 => -2, 11 => 1, 14 => 1, 19 => 1, 59 => 2, 119 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m3_2p6_3p1_5p1_6m2_8m1_10m2_12p1_15p1_20p1_60p2_120m1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m3_2p6_3p1_5p1_6m2_8m1_10m2_12p1_15p1_20p1_60p2_120m1 =
    [0, 1, 3, 3, 3, 3, -1, 0, 3, 1, 3, 4, 3, 2, 2, 3, -3, -4, 1, -2,
     -3, 8, 4, -4, 3, -1, -6, -7, 0, -2, -5, 10, 3, -8, -2, 2, -9, -6, 0, -6,
     -3, 4, 10, -4, 0, 1, -14, -8, -3, -5, -9, 4, 6, 0, 5, -4, -12, -10, -2, -4,
     -3, 8, 0, -6, -3, -2, -12, -12, -6, -16, -6, 4, 3, -2, 2, 1, -12, -4, 2, 2,
     3, -1, -2, 4, 0, 4, 2, -2, 0, -2, 1, -4, 12, 18, 14, 6, 3, -2, 3, 8] := by
  eta_coeff

end WeightTwoCusps
