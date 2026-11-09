module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(2z) η(5z)^2 η(10z)^(-1) η(11z)^3 η(15z)^2 η(22z)^(-2) η(30z)^(-1) η(33z)^(-1) η(55z)^(-1) η(66z)^2 η(110z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^2 η(10z)^(-1) η(11z)^3 η(15z)^2 η(22z)^(-2) η(30z)^(-1) η(33z)^(-1) η(55z)^(-1) η(66z)^2 η(110z)` at level 330. -/
abbrev cuspForm_330_eta_1m1_2p1_5p2_10m1_11p3_15p2_22m2_30m1_33m1_55m1_66p2_110p1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -1, 1 => 1, 4 => 2, 9 => -1, 10 => 3, 14 => 2, 21 => -2, 29 => -1, 32 => -1, 54 => -1, 65 => 2, 109 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m1_2p1_5p2_10m1_11p3_15p2_22m2_30m1_33m1_55m1_66p2_110p1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m1_2p1_5p2_10m1_11p3_15p2_22m2_30m1_33m1_55m1_66p2_110p1 =
    [0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 4, 1, 2, 3,
     0, -1, 3, 0, -3, 0, -2, -2, -1, -1, -6, -2, 2, -2, 0, 4, 4, -4, -2, 1,
     -2, 5, 0, -3, -2, 0, -5, -8, 2, -2, 0, -6, -3, 4, 2, -2, -4, 2, -2, 0,
     0, -4, 10, -1, -8, -8, 0, 0, -5, 0, 0, 4, -3, -3, -2, 4, 5, -3, -4, -1,
     0, -6, -8, -1, -7, -4, -12, -6, -2, 0, -2, -2, -2, -4, 3, -5, 9, 10, 0, 1] := by
  eta_coeff

end WeightTwoCusps
