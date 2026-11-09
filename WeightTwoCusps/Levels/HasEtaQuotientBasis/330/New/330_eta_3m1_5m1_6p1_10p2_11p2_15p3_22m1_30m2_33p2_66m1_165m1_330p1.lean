module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(3z)^(-1) η(5z)^(-1) η(6z) η(10z)^2 η(11z)^2 η(15z)^3 η(22z)^(-1) η(30z)^(-2) η(33z)^2 η(66z)^(-1) η(165z)^(-1) η(330z)`; see
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

/-- The cuspidal eta quotient `η(3z)^(-1) η(5z)^(-1) η(6z) η(10z)^2 η(11z)^2 η(15z)^3 η(22z)^(-1) η(30z)^(-2) η(33z)^2 η(66z)^(-1) η(165z)^(-1) η(330z)` at level 330. -/
abbrev cuspForm_330_eta_3m1_5m1_6p1_10p2_11p2_15p3_22m1_30m2_33p2_66m1_165m1_330p1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 2 => -1, 4 => -1, 5 => 1, 9 => 2, 10 => 2, 14 => 3, 21 => -1, 29 => -2, 32 => 2, 65 => -1, 164 => -1, 329 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_3m1_5m1_6p1_10p2_11p2_15p3_22m1_30m2_33p2_66m1_165m1_330p1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_3m1_5m1_6p1_10p2_11p2_15p3_22m1_30m2_33p2_66m1_165m1_330p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 2, 0, -1, 2,
     0, 0, 1, -2, 0, 2, -2, -4, 3, -2, -3, 2, -4, 0, 4, -4, -4, 4, 0, -4,
     2, -2, -1, 3, -4, -8, 4, 0, -8, 2, -4, 0, 1, -6, -6, 4, 2, -7, 2, 2,
     4, 0, -2, 3, 2, 8, -6, 2, 6, 4, 2, -8, 7, 1, 0, 0, 2, 4, 7, -2,
     -8, 6, 0, 2, 2, 3, 6, 5, 2, -6, 12, 2, -4, 4, 4, 4, -2, 6, -10, 4] := by
  eta_coeff

end WeightTwoCusps
