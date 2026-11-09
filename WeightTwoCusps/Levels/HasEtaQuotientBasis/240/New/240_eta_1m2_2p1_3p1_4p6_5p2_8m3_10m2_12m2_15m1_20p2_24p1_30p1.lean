module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-2) η(2z) η(3z) η(4z)^6 η(5z)^2 η(8z)^(-3) η(10z)^(-2) η(12z)^(-2) η(15z)^(-1) η(20z)^2 η(24z) η(30z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z) η(4z)^6 η(5z)^2 η(8z)^(-3) η(10z)^(-2) η(12z)^(-2) η(15z)^(-1) η(20z)^2 η(24z) η(30z)` at level 240. -/
abbrev cuspForm_240_eta_1m2_2p1_3p1_4p6_5p2_8m3_10m2_12m2_15m1_20p2_24p1_30p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -2, 1 => 1, 2 => 1, 3 => 6, 4 => 2, 7 => -3, 9 => -2, 11 => -2, 14 => -1, 19 => 2, 23 => 1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m2_2p1_3p1_4p6_5p2_8m3_10m2_12m2_15m1_20p2_24p1_30p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m2_2p1_3p1_4p6_5p2_8m3_10m2_12m2_15m1_20p2_24p1_30p1 =
    [0, 0, 1, 2, 4, 7, 6, 6, 3, -2, -2, -2, 1, 4, 8, 7, 6, 4, 3, 2,
     -1, 8, -2, -2, 0, -12, -8, -4, 2, 2, 3, 2, -9, -12, -4, -2, -8, 8, 4, -14,
     0, -18, -12, -10, -6, 5, -14, -2, -9, -6, 1, 12, 2, 0, -12, -20, -6, -16, -8, 2,
     -4, -2, 4, -2, -6, -12, 18, -6, -6, 6, -4, -12, 3, 8, -12, -10, -4, -8, -18, 22,
     9, 10, 18, 26, 2, 4, -2, -12, -6, 0, 0, -20, 12, 8, 10, 18, 12, -8, 9, 6] := by
  eta_coeff

end WeightTwoCusps
