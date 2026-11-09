module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(z)^2 η(2z)^(-1) η(15z) η(30z) η(225z)^(-1) η(450z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(15z) η(30z) η(225z)^(-1) η(450z)^2` at level 450. -/
abbrev cuspForm_450_eta_1p2_2m1_15p1_30p1_225m1_450p2 : gamma0CuspForms 450 :=
  etaQuotientCuspForm 450 sparse![450; 0 => 2, 1 => -1, 14 => 1, 29 => 1, 224 => -1, 449 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_450_eta_1p2_2m1_15p1_30p1_225m1_450p2_first_coeffs :
    first_coeffs 100 cuspForm_450_eta_1p2_2m1_15p1_30p1_225m1_450p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0, 2, 0, 0, 0, 0, -2,
     0, 0, 0, 0, 0, -1, 4, 0, 0, -2, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0,
     -2, 2, 0, 0, -4, 0, 2, 0, 0, 4, 2, 0, 0, 0, 0, 1, -6, 0, 0, 0,
     0, -2, 0, 0, -2, 4, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, -4, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
