module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(2z)^2 η(3z)^(-1) η(5z) η(6z)^2 η(10z)^(-1) η(11z) η(22z)^(-1) η(55z)^(-2) η(110z)^3 η(165z)^2 η(330z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z)^(-1) η(5z) η(6z)^2 η(10z)^(-1) η(11z) η(22z)^(-1) η(55z)^(-2) η(110z)^3 η(165z)^2 η(330z)^(-1)` at level 330. -/
abbrev cuspForm_330_eta_1m1_2p2_3m1_5p1_6p2_10m1_11p1_22m1_55m2_110p3_165p2_330m1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -1, 1 => 2, 2 => -1, 4 => 1, 5 => 2, 9 => -1, 10 => 1, 21 => -1, 54 => -2, 109 => 3, 164 => 2, 329 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m1_2p2_3m1_5p1_6p2_10m1_11p1_22m1_55m2_110p3_165p2_330m1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m1_2p2_3m1_5p1_6p2_10m1_11p1_22m1_55m2_110p3_165p2_330m1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, -1, 1, 0, -2, 1, 2,
     -3, 0, 1, -4, -2, 0, -2, -1, 3, -2, -1, 2, -1, -1, -1, 0, 0, 0, -1, 2,
     2, 0, 0, -4, -3, 0, 0, -1, 2, 5, -1, -2, -2, 1, 2, 2, 4, 1, 4, 2,
     -2, -2, 4, -1, -3, 1, 0, 4, 5, -1, 0, 2, -3, -2, 0, 2, 4, 3, -5, -2,
     0, -4, -3, 1, -4, 0, -1, -7, 0, 0, -3, -1, 0, -1, 4, 4, 2, 1, 2, -1] := by
  eta_coeff

end WeightTwoCusps
