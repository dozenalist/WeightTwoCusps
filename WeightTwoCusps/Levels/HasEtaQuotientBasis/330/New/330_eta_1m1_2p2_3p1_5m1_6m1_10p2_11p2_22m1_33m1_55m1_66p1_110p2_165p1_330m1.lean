module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(5z)^(-1) η(6z)^(-1) η(10z)^2 η(11z)^2 η(22z)^(-1) η(33z)^(-1) η(55z)^(-1) η(66z) η(110z)^2 η(165z) η(330z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(5z)^(-1) η(6z)^(-1) η(10z)^2 η(11z)^2 η(22z)^(-1) η(33z)^(-1) η(55z)^(-1) η(66z) η(110z)^2 η(165z) η(330z)^(-1)` at level 330. -/
abbrev cuspForm_330_eta_1m1_2p2_3p1_5m1_6m1_10p2_11p2_22m1_33m1_55m1_66p1_110p2_165p1_330m1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -1, 1 => 2, 2 => 1, 4 => -1, 5 => -1, 9 => 2, 10 => 2, 21 => -1, 32 => -1, 54 => -1, 65 => 1, 109 => 2, 164 => 1, 329 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m1_2p2_3p1_5m1_6m1_10p2_11p2_22m1_33m1_55m1_66p1_110p2_165p1_330m1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m1_2p2_3p1_5m1_6m1_10p2_11p2_22m1_33m1_55m1_66p1_110p2_165p1_330m1 =
    [0, 0, 1, 1, 0, 0, -1, 1, 1, 0, 0, -3, 0, -2, -2, 0, -2, 3, -2, -2,
     0, -1, 6, -1, 0, 0, -2, 5, -2, 0, 0, 0, 4, 0, 2, 1, 0, 4, 0, -1,
     1, -1, 1, -2, -3, 0, 0, 2, -1, -6, 1, 1, 5, 1, -5, 0, -1, 2, 1, 0,
     1, -3, -1, -1, -6, 2, -3, 0, -2, -2, 0, -1, 6, -1, -3, 1, 1, 5, 0, -2,
     0, -4, 5, -3, 1, 1, 1, 3, -4, -1, 2, 0, 4, 0, 1, 1, -2, 5, -2, -3] := by
  eta_coeff

end WeightTwoCusps
