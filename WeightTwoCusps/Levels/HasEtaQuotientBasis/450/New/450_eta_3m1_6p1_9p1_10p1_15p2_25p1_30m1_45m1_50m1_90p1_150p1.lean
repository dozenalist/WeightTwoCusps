module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(3z)^(-1) η(6z) η(9z) η(10z) η(15z)^2 η(25z) η(30z)^(-1) η(45z)^(-1) η(50z)^(-1) η(90z) η(150z)`; see
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

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z) η(9z) η(10z) η(15z)^2 η(25z) η(30z)^(-1) η(45z)^(-1) η(50z)^(-1) η(90z) η(150z)` at level 450. -/
abbrev cuspForm_450_eta_3m1_6p1_9p1_10p1_15p2_25p1_30m1_45m1_50m1_90p1_150p1 : gamma0CuspForms 450 :=
  etaQuotientCuspForm 450 sparse![450; 2 => -1, 5 => 1, 8 => 1, 9 => 1, 14 => 2, 24 => 1, 29 => -1, 44 => -1, 49 => -1, 89 => 1, 149 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_450_eta_3m1_6p1_9p1_10p1_15p2_25p1_30m1_45m1_50m1_90p1_150p1_first_coeffs :
    first_coeffs 100 cuspForm_450_eta_3m1_6p1_9p1_10p1_15p2_25p1_30m1_45m1_50m1_90p1_150p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, -1, 0,
     1, -1, 0, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, -1,
     -1, 1, -1, 1, -1, -1, 2, -1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 2, 1,
     0, -1, 2, 1, 2, 0, -1, 2, -1, 1, 1, -2, 0, -1, 1, 1, 0, -1, 2, -1,
     0, 2, -2, -3, 0, 1, -2, 1, 0, -5, 2, 2, -4, 2, -2, -3, 2, 1, 1, 2] := by
  eta_coeff

end WeightTwoCusps
