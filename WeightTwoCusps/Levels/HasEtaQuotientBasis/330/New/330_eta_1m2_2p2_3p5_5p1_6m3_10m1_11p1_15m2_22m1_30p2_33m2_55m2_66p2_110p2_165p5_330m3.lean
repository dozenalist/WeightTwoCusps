module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^5 η(5z) η(6z)^(-3) η(10z)^(-1) η(11z) η(15z)^(-2) η(22z)^(-1) η(30z)^2 η(33z)^(-2) η(55z)^(-2) η(66z)^2 η(110z)^2 η(165z)^5 η(330z)^(-3)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^5 η(5z) η(6z)^(-3) η(10z)^(-1) η(11z) η(15z)^(-2) η(22z)^(-1) η(30z)^2 η(33z)^(-2) η(55z)^(-2) η(66z)^2 η(110z)^2 η(165z)^5 η(330z)^(-3)` at level 330. -/
abbrev cuspForm_330_eta_1m2_2p2_3p5_5p1_6m3_10m1_11p1_15m2_22m1_30p2_33m2_55m2_66p2_110p2_165p5_330m3 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -2, 1 => 2, 2 => 5, 4 => 1, 5 => -3, 9 => -1, 10 => 1, 14 => -2, 21 => -1, 29 => 2, 32 => -2, 54 => -2, 65 => 2, 109 => 2, 164 => 5, 329 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m2_2p2_3p5_5p1_6m3_10m1_11p1_15m2_22m1_30p2_33m2_55m2_66p2_110p2_165p5_330m3_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m2_2p2_3p5_5p1_6m3_10m1_11p1_15m2_22m1_30p2_33m2_55m2_66p2_110p2_165p5_330m3 =
    [0, 1, 2, 3, 1, -1, -2, -2, 0, -1, 0, -4, -6, -4, -1, 4, 4, 4, 2, -4,
     0, 2, 4, 3, -2, -1, -9, -2, 0, 2, 0, 1, 4, 0, 3, 4, 5, 3, 2, 2,
     -2, -2, -3, -8, 0, -5, 4, -2, 3, 1, -4, 10, 0, 4, 0, 0, -3, -10, 0, -5,
     -7, 2, -2, 0, -5, 6, 0, -3, 6, 2, 9, -3, 2, -6, 0, 7, 0, 8, -5, -6,
     -7, -4, 8, -2, 10, -2, -11, 2, -4, 15, 2, 10, -2, -4, 6, -6, 2, -3, -4, -4] := by
  eta_coeff

end WeightTwoCusps
