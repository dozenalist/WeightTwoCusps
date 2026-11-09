module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(z) η(2z)^(-1) η(3z)^(-1) η(5z)^2 η(6z)^2 η(150z)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(3z)^(-1) η(5z)^2 η(6z)^2 η(150z)` at level 450. -/
abbrev cuspForm_450_eta_1p1_2m1_3m1_5p2_6p2_150p1 : gamma0CuspForms 450 :=
  etaQuotientCuspForm 450 sparse![450; 0 => 1, 1 => -1, 2 => -1, 4 => 2, 5 => 2, 149 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_450_eta_1p1_2m1_3m1_5p2_6p2_150p1_first_coeffs :
    first_coeffs 100 cuspForm_450_eta_1p1_2m1_3m1_5p2_6p2_150p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, -3, 2, 0, 1, 0, 1, 1, 0,
     -2, 0, 3, -1, 0, -1, 0, -1, -4, 0, 2, 0, 1, -1, 0, 1, 0, -4, 5, 0,
     1, 0, 2, -1, 0, 0, 0, -1, 3, 0, 1, 0, -2, -2, 0, -4, 0, 2, 1, 0,
     -3, 0, 1, -1, 0, -1, 0, 1, -2, 0, 2, 0, 3, 0, 0, 0, 0, 1, -2, 0,
     4, 0, -4, 3, 0, 5, 0, 0, 2, 0, -3, 0, -6, -1, 0, 2, 0, 1, -5, 0] := by
  eta_coeff

end WeightTwoCusps
