module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(z) η(2z)^(-1) η(3z) η(10z)^2 η(25z) η(50z)^(-1) η(75z)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(3z) η(10z)^2 η(25z) η(50z)^(-1) η(75z)` at level 450. -/
abbrev cuspForm_450_eta_1p1_2m1_3p1_10p2_25p1_50m1_75p1 : gamma0CuspForms 450 :=
  etaQuotientCuspForm 450 sparse![450; 0 => 1, 1 => -1, 2 => 1, 9 => 2, 24 => 1, 49 => -1, 74 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_450_eta_1p1_2m1_3p1_10p2_25p1_50m1_75p1_first_coeffs :
    first_coeffs 100 cuspForm_450_eta_1p1_2m1_3p1_10p2_25p1_50m1_75p1 =
    [0, 0, 0, 1, -1, 0, -2, 2, -1, 1, -1, 3, -2, 0, -1, 4, 0, -1, -2, 3,
     -4, -1, -3, 3, 0, -1, 1, 3, -3, 1, 0, 5, -1, 0, -3, 4, -6, 2, -1, 3,
     -1, -2, 2, 5, -6, 0, -1, 5, 0, -4, 0, 0, -4, 0, 0, 2, -4, -3, 4, 5,
     -4, 1, 1, 3, 2, -4, 6, 0, -4, -2, 2, 4, 0, -8, 8, 0, -1, -3, -2, 3,
     4, 5, -1, -1, -6, 2, -5, 2, -2, -6, -4, -5, -2, 1, 1, 8, 8, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
