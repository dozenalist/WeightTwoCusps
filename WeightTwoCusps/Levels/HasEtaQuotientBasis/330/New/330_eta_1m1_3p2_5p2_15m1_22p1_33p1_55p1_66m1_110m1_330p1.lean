module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(3z)^2 η(5z)^2 η(15z)^(-1) η(22z) η(33z) η(55z) η(66z)^(-1) η(110z)^(-1) η(330z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(5z)^2 η(15z)^(-1) η(22z) η(33z) η(55z) η(66z)^(-1) η(110z)^(-1) η(330z)` at level 330. -/
abbrev cuspForm_330_eta_1m1_3p2_5p2_15m1_22p1_33p1_55p1_66m1_110m1_330p1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -1, 2 => 2, 4 => 2, 14 => -1, 21 => 1, 32 => 1, 54 => 1, 65 => -1, 109 => -1, 329 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m1_3p2_5p2_15m1_22p1_33p1_55p1_66m1_110m1_330p1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m1_3p2_5p2_15m1_22p1_33p1_55p1_66m1_110m1_330p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 3, 1, 2, 0, 4,
     1, 2, 0, 3, 0, 0, 1, 5, 2, 2, 2, 3, 0, -1, 1, 2, 0, -3, 0, -2,
     0, -2, 1, 4, -1, 0, -2, 2, -4, -2, -4, 2, -6, -4, -2, -1, -5, -2, 0, 1,
     -6, -2, 0, -8, -4, -6, 0, -9, -2, -4, -1, -7, 0, -2, -4, 2, -6, 0, -7, -2,
     -4, -5, -6, 2, -6, -2, -3, -2, 2, -3, 0, 2, 2, -6, 2, -10, 10, -7, 2, 1] := by
  eta_coeff

end WeightTwoCusps
