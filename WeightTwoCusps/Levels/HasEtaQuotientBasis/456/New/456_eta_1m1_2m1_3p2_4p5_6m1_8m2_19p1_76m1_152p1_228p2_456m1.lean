module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^5 η(6z)^(-1) η(8z)^(-2) η(19z) η(76z)^(-1) η(152z) η(228z)^2 η(456z)^(-1)`; see
[the local level table](../../TABLE.md#level-456).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^5 η(6z)^(-1) η(8z)^(-2) η(19z) η(76z)^(-1) η(152z) η(228z)^2 η(456z)^(-1)` at level 456. -/
abbrev cuspForm_456_eta_1m1_2m1_3p2_4p5_6m1_8m2_19p1_76m1_152p1_228p2_456m1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -1, 1 => -1, 2 => 2, 3 => 5, 5 => -1, 7 => -2, 18 => 1, 75 => -1, 151 => 1, 227 => 2, 455 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m1_2m1_3p2_4p5_6m1_8m2_19p1_76m1_152p1_228p2_456m1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m1_2m1_3p2_4p5_6m1_8m2_19p1_76m1_152p1_228p2_456m1 =
    [0, 0, 0, 0, 1, 1, 3, 2, 2, 1, 0, 3, 2, 4, 2, 0, 1, 2, 2, 3,
     0, 2, 2, 1, 3, -3, -1, 2, 1, 2, -2, -2, -2, -2, 4, -1, 0, 2, 1, 1,
     -2, 2, -3, -3, 0, -3, -4, -1, 2, -4, -2, -4, 0, -4, 1, -1, -4, -3, 1, 0,
     -6, 1, -2, 1, -1, -6, -2, -6, -1, 4, -4, 0, -4, 0, -4, -6, 0, -1, 0, -2,
     0, -2, -2, 6, 0, -3, -4, 5, 0, 6, -2, 2, -1, 0, 2, -9, -3, -2, 4, -1] := by
  eta_coeff

end WeightTwoCusps
