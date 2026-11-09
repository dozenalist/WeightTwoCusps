module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-2) η(2z)^2 η(3z) η(5z)^5 η(6z)^(-1) η(10z)^(-3) η(11z)^5 η(15z)^(-2) η(22z)^(-3) η(30z)^2 η(33z)^(-2) η(55z)^(-2) η(66z)^2 η(110z)^2 η(165z) η(330z)^(-1)`; see
[the local level table](../../TABLE.md#level-330).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z) η(5z)^5 η(6z)^(-1) η(10z)^(-3) η(11z)^5 η(15z)^(-2) η(22z)^(-3) η(30z)^2 η(33z)^(-2) η(55z)^(-2) η(66z)^2 η(110z)^2 η(165z) η(330z)^(-1)` at level 330. -/
abbrev cuspForm_330_eta_1m2_2p2_3p1_5p5_6m1_10m3_11p5_15m2_22m3_30p2_33m2_55m2_66p2_110p2_165p1_330m1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -2, 1 => 2, 2 => 1, 4 => 5, 5 => -1, 9 => -3, 10 => 5, 14 => -2, 21 => -3, 29 => 2, 32 => -2, 54 => -2, 65 => 2, 109 => 2, 164 => 1, 329 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m2_2p2_3p1_5p5_6m1_10m3_11p5_15m2_22m3_30p2_33m2_55m2_66p2_110p2_165p1_330m1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m2_2p2_3p1_5p5_6m1_10m3_11p5_15m2_22m3_30p2_33m2_55m2_66p2_110p2_165p1_330m1 =
    [0, 1, 2, 3, 5, 7, 6, 6, 8, 7, 8, 12, 10, 4, 3, -4, -12, -4, 2, -4,
     0, 2, -12, -13, 6, 7, 11, 22, 8, -14, -8, 1, -12, 0, 7, -20, -39, -21, -14, -14,
     14, 14, -23, -16, 0, -5, 4, 46, 23, -15, -4, -6, -8, 4, 32, 0, -15, -2, -16, -29,
     5, 26, -10, -16, 23, -10, 0, 29, 22, -6, 5, 5, -46, -6, 0, -9, -24, -24, -25, -38,
     -19, -4, -8, 6, -6, -2, -23, 10, 12, -9, 2, -22, 14, -4, 14, 10, 10, 5, -12, 12] := by
  eta_coeff

end WeightTwoCusps
