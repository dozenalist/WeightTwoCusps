module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(z) η(5z)^2 η(50z)^(-1) η(75z)^(-1) η(150z)^3`; see
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

/-- The cuspidal eta quotient `η(z) η(5z)^2 η(50z)^(-1) η(75z)^(-1) η(150z)^3` at level 450. -/
abbrev cuspForm_450_eta_1p1_5p2_50m1_75m1_150p3 : gamma0CuspForms 450 :=
  etaQuotientCuspForm 450 sparse![450; 0 => 1, 4 => 2, 49 => -1, 74 => -1, 149 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_450_eta_1p1_5p2_50m1_75m1_150p3_first_coeffs :
    first_coeffs 100 cuspForm_450_eta_1p1_5p2_50m1_75m1_150p3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 0, -1,
     2, 3, 0, 0, -3, 1, -2, 0, 0, 0, -2, -1, 0, 0, 5, -1, 3, 0, 0, 4,
     -1, -5, 0, 0, -2, 0, 2, 0, 0, -4, -1, -2, 0, 0, -3, 4, 5, 0, 0, 1,
     3, 2, 0, 0, -1, 1, -4, 0, 0, -1, -2, 7, 0, 0, -4, 0, -7, 0, 0, 1,
     -4, -6, 0, 0, 11, -5, 5, 0, 0, 10, 3, -3, 0, 0, 0, -2, 2, 0, 0, -9] := by
  eta_coeff

end WeightTwoCusps
