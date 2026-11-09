module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(z) η(2z)^(-1) η(3z) η(5z)^(-1) η(10z)^2 η(25z) η(30z)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(3z) η(5z)^(-1) η(10z)^2 η(25z) η(30z)` at level 450. -/
abbrev cuspForm_450_eta_1p1_2m1_3p1_5m1_10p2_25p1_30p1 : gamma0CuspForms 450 :=
  etaQuotientCuspForm 450 sparse![450; 0 => 1, 1 => -1, 2 => 1, 4 => -1, 9 => 2, 24 => 1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_450_eta_1p1_2m1_3p1_5m1_10p2_25p1_30p1_first_coeffs :
    first_coeffs 100 cuspForm_450_eta_1p1_2m1_3p1_5m1_10p2_25p1_30p1 =
    [0, 0, 0, 1, -1, 0, -2, 2, 0, 0, -1, 1, 0, 1, -2, 3, -1, 1, -1, 1,
     -2, -1, -2, 3, -1, 0, -1, 2, -2, 2, -2, 5, -3, 0, -1, 3, -1, -1, -4, 6,
     -2, 2, -3, 2, -1, 0, 0, 4, -4, 1, -1, 5, -3, -3, -2, 6, -2, -2, -2, 4,
     -1, -2, -2, 4, 0, -3, 1, 1, 0, -3, 0, 5, -1, -3, 3, 0, -3, -3, 2, 5,
     0, 0, 3, 4, -1, -3, -1, 7, 1, -9, -1, -2, 2, -3, -1, 6, 0, -2, 3, -2] := by
  eta_coeff

end WeightTwoCusps
