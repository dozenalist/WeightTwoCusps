module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(2z) η(5z)^3 η(10z)^(-2) η(11z)^2 η(15z)^(-1) η(22z)^(-1) η(30z)^2 η(33z)^2 η(55z)^(-1) η(66z)^(-1) η(110z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^3 η(10z)^(-2) η(11z)^2 η(15z)^(-1) η(22z)^(-1) η(30z)^2 η(33z)^2 η(55z)^(-1) η(66z)^(-1) η(110z)` at level 330. -/
abbrev cuspForm_330_eta_1m1_2p1_5p3_10m2_11p2_15m1_22m1_30p2_33p2_55m1_66m1_110p1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -1, 1 => 1, 4 => 3, 9 => -2, 10 => 2, 14 => -1, 21 => -1, 29 => 2, 32 => 2, 54 => -1, 65 => -1, 109 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m1_2p1_5p3_10m2_11p2_15m1_22m1_30p2_33p2_55m1_66m1_110p1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m1_2p1_5p3_10m2_11p2_15m1_22m1_30p2_33p2_55m1_66m1_110p1 =
    [0, 0, 0, 0, 1, 1, 1, 2, 2, 0, 1, 2, 0, 2, 3, 0, 0, 2, -2, -1,
     4, 1, 0, 4, 1, 0, 3, 2, 0, 3, 0, 0, 2, 0, 3, 1, -3, -4, -2, -7,
     -4, -1, -2, -2, -2, -5, -5, -2, 0, 0, 0, 4, 2, -6, -4, 0, -9, -6, -2, -6,
     -4, 4, -2, 0, -3, -1, -2, -8, 2, 10, 5, 2, 10, -6, -4, 4, -3, -4, 12, 1,
     -11, -2, -2, -8, -1, -5, -3, 2, 0, 8, 7, 2, 4, -4, -17, -7, -3, 6, -6, 2] := by
  eta_coeff

end WeightTwoCusps
