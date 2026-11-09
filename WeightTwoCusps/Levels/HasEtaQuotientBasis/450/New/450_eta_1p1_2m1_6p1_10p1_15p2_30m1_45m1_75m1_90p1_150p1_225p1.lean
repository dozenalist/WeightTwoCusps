module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(z) η(2z)^(-1) η(6z) η(10z) η(15z)^2 η(30z)^(-1) η(45z)^(-1) η(75z)^(-1) η(90z) η(150z) η(225z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(6z) η(10z) η(15z)^2 η(30z)^(-1) η(45z)^(-1) η(75z)^(-1) η(90z) η(150z) η(225z)` at level 450. -/
abbrev cuspForm_450_eta_1p1_2m1_6p1_10p1_15p2_30m1_45m1_75m1_90p1_150p1_225p1 : gamma0CuspForms 450 :=
  etaQuotientCuspForm 450 sparse![450; 0 => 1, 1 => -1, 5 => 1, 9 => 1, 14 => 2, 29 => -1, 44 => -1, 74 => -1, 89 => 1, 149 => 1, 224 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_450_eta_1p1_2m1_6p1_10p1_15p2_30m1_45m1_75m1_90p1_150p1_225p1_first_coeffs :
    first_coeffs 100 cuspForm_450_eta_1p1_2m1_6p1_10p1_15p2_30m1_45m1_75m1_90p1_150p1_225p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 1,
     -1, 0, 0, 2, -1, 0, 0, 1, 0, 0, -2, 4, -2, 1, -3, 2, 0, 0, -4, 3,
     -1, 0, -2, 0, 0, 0, -4, 6, 1, 1, 0, 1, 0, 0, -1, 3, 0, 0, 0, 0,
     1, -2, -4, 2, 2, -2, -3, 0, 2, -3, -1, 0, 0, 0, 0, 0, 4, -4, -2, 3,
     2, 1, 0, 0, 1, -3, 0, 2, 0, 0, 1, -2, 8, -4, -3, 1, 2, 0, 2, -1] := by
  eta_coeff

end WeightTwoCusps
