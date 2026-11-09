module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z)^2 η(6z)^(-2) η(10z)^(-2) η(11z) η(15z)^(-2) η(30z)^3 η(33z)^(-1) η(55z)^(-1) η(66z) η(110z) η(165z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z)^2 η(6z)^(-2) η(10z)^(-2) η(11z) η(15z)^(-2) η(30z)^3 η(33z)^(-1) η(55z)^(-1) η(66z) η(110z) η(165z)` at level 330. -/
abbrev cuspForm_330_eta_1m2_2p3_3p2_5p2_6m2_10m2_11p1_15m2_30p3_33m1_55m1_66p1_110p1_165p1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -2, 1 => 3, 2 => 2, 4 => 2, 5 => -2, 9 => -2, 10 => 1, 14 => -2, 29 => 3, 32 => -1, 54 => -1, 65 => 1, 109 => 1, 164 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m2_2p3_3p2_5p2_6m2_10m2_11p1_15m2_30p3_33m1_55m1_66p1_110p1_165p1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m2_2p3_3p2_5p2_6m2_10m2_11p1_15m2_30p3_33m1_55m1_66p1_110p1_165p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 1, 0, -1,
     0, 1, 0, 0, -1, -2, -2, 2, 3, 1, 1, 0, -1, 0, 4, 2, -2, -2, -4, -5,
     -1, 2, 0, -4, 0, -2, -2, 4, 2, -2, -3, 2, -2, 0, 4, 0, -4, -2, 0, -4,
     -2, 4, -2, 0, 4, 3, 0, 0, 6, -4, 4, 0, -4, -2, 0, 2, -3, 0, -4, -9,
     -2, 2, 2, 2, 2, -1, -8, 6, 0, 4, 0, -2, -4, -4, 5, -5, 2, -4, -7, 0] := by
  eta_coeff

end WeightTwoCusps
