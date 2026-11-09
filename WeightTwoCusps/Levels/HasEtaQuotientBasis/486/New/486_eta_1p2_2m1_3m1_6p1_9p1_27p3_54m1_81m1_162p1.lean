module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(z)^2 η(2z)^(-1) η(3z)^(-1) η(6z) η(9z) η(27z)^3 η(54z)^(-1) η(81z)^(-1) η(162z)`; see
[the local level table](../../TABLE.md#level-486).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(3z)^(-1) η(6z) η(9z) η(27z)^3 η(54z)^(-1) η(81z)^(-1) η(162z)` at level 486. -/
abbrev cuspForm_486_eta_1p2_2m1_3m1_6p1_9p1_27p3_54m1_81m1_162p1 : gamma0CuspForms 486 :=
  etaQuotientCuspForm 486 sparse![486; 0 => 2, 1 => -1, 2 => -1, 5 => 1, 8 => 1, 26 => 3, 53 => -1, 80 => -1, 161 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_486_eta_1p2_2m1_3m1_6p1_9p1_27p3_54m1_81m1_162p1_first_coeffs :
    first_coeffs 100 cuspForm_486_eta_1p2_2m1_3m1_6p1_9p1_27p3_54m1_81m1_162p1 =
    [0, 0, 0, 0, 0, 1, -2, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0,
     0, 0, 0, -1, 4, 0, 0, 0, 0, -2, 0, 0, -3, 6, 0, -4, 0, 0, -4, 0,
     0, 4, 2, 0, 2, 0, 0, 0, 0, 0, 4, -12, 0, 1, 0, 0, 7, 0, 0, -1,
     -6, 0, 4, 0, 0, 5, 0, 0, -4, -6, 0, 5, 0, 0, 1, 0, 0, -4, 2, 0,
     -4, 0, 0, -3, 0, 0, 10, 6, 0, 2, 0, 0, -2, 0, 0, -1, -2, 0, -13, 0] := by
  eta_coeff

end WeightTwoCusps
