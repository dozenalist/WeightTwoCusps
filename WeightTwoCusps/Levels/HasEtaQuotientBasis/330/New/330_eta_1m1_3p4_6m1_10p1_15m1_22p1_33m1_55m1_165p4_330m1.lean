module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(3z)^4 η(6z)^(-1) η(10z) η(15z)^(-1) η(22z) η(33z)^(-1) η(55z)^(-1) η(165z)^4 η(330z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^4 η(6z)^(-1) η(10z) η(15z)^(-1) η(22z) η(33z)^(-1) η(55z)^(-1) η(165z)^4 η(330z)^(-1)` at level 330. -/
abbrev cuspForm_330_eta_1m1_3p4_6m1_10p1_15m1_22p1_33m1_55m1_165p4_330m1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -1, 2 => 4, 5 => -1, 9 => 1, 14 => -1, 21 => 1, 32 => -1, 54 => -1, 164 => 4, 329 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m1_3p4_6m1_10p1_15m1_22p1_33m1_55m1_165p4_330m1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m1_3p4_6m1_10p1_15m1_22p1_33m1_55m1_165p4_330m1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, -1, 1, -1, 2, -2, 0,
     -1, 0, -4, -1, -2, 2, -3, 3, 2, 0, -4, -1, 2, -1, -3, -2, 2, -5, -2, 0,
     4, 4, 1, 6, 5, 2, 2, 0, 2, 0, -2, 0, -2, -2, -4, -1, 1, 2, 4, 1,
     8, -4, 2, -10, 2, -4, 4, -7, 0, -4, 1, -5, 4, 8, 12, 0, 4, 2, -3, -2,
     -4, 5, -8, 0, -4, -4, -11, -4, 2, 3, 0, 2, 0, -4, -4, -6, 0, -3, 2, -1] := by
  eta_coeff

end WeightTwoCusps
