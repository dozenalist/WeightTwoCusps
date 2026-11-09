module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(2z) η(3z)^2 η(5z)^2 η(6z)^(-2) η(10z)^(-2) η(11z)^2 η(15z)^(-3) η(22z)^(-2) η(30z)^5 η(33z)^(-3) η(55z)^(-1) η(66z)^5 η(110z) η(165z)^2 η(330z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^2 η(5z)^2 η(6z)^(-2) η(10z)^(-2) η(11z)^2 η(15z)^(-3) η(22z)^(-2) η(30z)^5 η(33z)^(-3) η(55z)^(-1) η(66z)^5 η(110z) η(165z)^2 η(330z)^(-2)` at level 330. -/
abbrev cuspForm_330_eta_1m1_2p1_3p2_5p2_6m2_10m2_11p2_15m3_22m2_30p5_33m3_55m1_66p5_110p1_165p2_330m2 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -1, 1 => 1, 2 => 2, 4 => 2, 5 => -2, 9 => -2, 10 => 2, 14 => -3, 21 => -2, 29 => 5, 32 => -3, 54 => -1, 65 => 5, 109 => 1, 164 => 2, 329 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m1_2p1_3p2_5p2_6m2_10m2_11p2_15m3_22m2_30p5_33m3_55m1_66p5_110p1_165p2_330m2_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m1_2p1_3p2_5p2_6m2_10m2_11p2_15m3_22m2_30p5_33m3_55m1_66p5_110p1_165p2_330m2 =
    [0, 1, 1, 1, 0, 0, -1, -1, 0, 1, 0, -1, -2, -2, -1, 2, 3, 2, 1, -1,
     -1, 0, 3, 1, 0, -2, -4, -4, -1, 1, 0, -1, 1, -1, 2, 3, 2, 1, 1, 2,
     -1, 1, 0, -4, -3, -2, 1, 0, 2, 0, -2, 2, 2, 3, 2, 1, -2, -5, 1, -3,
     -2, 0, -1, 1, -3, 3, -1, 0, 2, -1, 3, -2, -2, -4, -3, 3, -1, 4, -2, -3,
     -1, 1, 5, 2, 4, -2, -4, 3, -1, 7, 0, 4, -4, -3, 4, -2, 4, -2, -4, -1] := by
  eta_coeff

end WeightTwoCusps
