module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-3) η(2z)^5 η(3z)^2 η(5z)^2 η(6z)^(-2) η(10z)^(-2) η(11z)^2 η(15z)^(-1) η(22z)^(-2) η(30z) η(33z)^(-1) η(55z)^(-3) η(66z) η(110z)^5 η(165z)^2 η(330z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z)^2 η(5z)^2 η(6z)^(-2) η(10z)^(-2) η(11z)^2 η(15z)^(-1) η(22z)^(-2) η(30z) η(33z)^(-1) η(55z)^(-3) η(66z) η(110z)^5 η(165z)^2 η(330z)^(-2)` at level 330. -/
abbrev cuspForm_330_eta_1m3_2p5_3p2_5p2_6m2_10m2_11p2_15m1_22m2_30p1_33m1_55m3_66p1_110p5_165p2_330m2 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -3, 1 => 5, 2 => 2, 4 => 2, 5 => -2, 9 => -2, 10 => 2, 14 => -1, 21 => -2, 29 => 1, 32 => -1, 54 => -3, 65 => 1, 109 => 5, 164 => 2, 329 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m3_2p5_3p2_5p2_6m2_10m2_11p2_15m1_22m2_30p1_33m1_55m3_66p1_110p5_165p2_330m2_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m3_2p5_3p2_5p2_6m2_10m2_11p2_15m1_22m2_30p1_33m1_55m3_66p1_110p5_165p2_330m2 =
    [0, 0, 0, 1, 3, 4, 5, 5, 3, 2, 2, 3, 2, 2, 1, -5, -6, -4, -2, -3,
     -1, -2, -9, -3, 2, 3, 4, 8, 1, -11, -1, 1, 0, 4, 4, -7, -17, -3, -9, -12,
     5, 1, -10, -10, 7, 0, 3, 22, 6, -1, 3, 6, -6, 5, 22, -2, -8, -3, -7, -13,
     1, 18, -1, 7, 12, -7, 2, 12, 16, -3, 1, 4, -17, -8, 3, 1, -7, -10, -12, -25,
     -9, 6, -7, 2, 2, -2, -14, 1, 3, -5, 0, -12, 2, 1, 2, 4, -6, 2, -5, 1] := by
  eta_coeff

end WeightTwoCusps
