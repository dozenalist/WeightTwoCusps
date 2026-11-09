module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^3 η(5z)^3 η(6z)^(-2) η(10z)^(-2) η(11z) η(15z)^(-2) η(22z)^(-1) η(30z)^2 η(66z) η(110z) η(165z) η(330z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^3 η(5z)^3 η(6z)^(-2) η(10z)^(-2) η(11z) η(15z)^(-2) η(22z)^(-1) η(30z)^2 η(66z) η(110z) η(165z) η(330z)^(-1)` at level 330. -/
abbrev cuspForm_330_eta_1m2_2p2_3p3_5p3_6m2_10m2_11p1_15m2_22m1_30p2_66p1_110p1_165p1_330m1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -2, 1 => 2, 2 => 3, 4 => 3, 5 => -2, 9 => -2, 10 => 1, 14 => -2, 21 => -1, 29 => 2, 65 => 1, 109 => 1, 164 => 1, 329 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m2_2p2_3p3_5p3_6m2_10m2_11p1_15m2_22m1_30p2_66p1_110p1_165p1_330m1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m2_2p2_3p3_5p3_6m2_10m2_11p1_15m2_22m1_30p2_66p1_110p1_165p1_330m1 =
    [0, 1, 2, 3, 3, 3, 2, 0, 0, 1, 2, 0, 0, -2, -3, -2, 2, 4, 2, 2,
     0, -2, 0, 5, 4, 1, -1, -2, -6, -2, 0, 1, -2, 0, -3, -6, -1, -3, -2, -2,
     4, -2, -3, 0, 0, -1, 6, 6, 1, -5, -2, -4, -2, 6, 4, 0, -9, -4, -10, -1,
     1, 4, 4, 0, -1, -2, 0, 1, 0, 0, -1, -9, -8, -10, 0, -3, 4, 0, -5, -8,
     -7, 2, 0, 4, 2, 0, -11, -6, 0, 1, 2, 10, 6, 6, 2, 0, 4, 1, 8, 0] := by
  eta_coeff

end WeightTwoCusps
