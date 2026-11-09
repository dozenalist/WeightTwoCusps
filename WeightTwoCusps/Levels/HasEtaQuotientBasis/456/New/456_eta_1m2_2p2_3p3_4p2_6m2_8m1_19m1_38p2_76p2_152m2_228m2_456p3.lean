module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^3 η(4z)^2 η(6z)^(-2) η(8z)^(-1) η(19z)^(-1) η(38z)^2 η(76z)^2 η(152z)^(-2) η(228z)^(-2) η(456z)^3`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^3 η(4z)^2 η(6z)^(-2) η(8z)^(-1) η(19z)^(-1) η(38z)^2 η(76z)^2 η(152z)^(-2) η(228z)^(-2) η(456z)^3` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p2_3p3_4p2_6m2_8m1_19m1_38p2_76p2_152m2_228m2_456p3 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 2, 2 => 3, 3 => 2, 5 => -2, 7 => -1, 18 => -1, 37 => 2, 75 => 2, 151 => -2, 227 => -2, 455 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p2_3p3_4p2_6m2_8m1_19m1_38p2_76p2_152m2_228m2_456p3_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p2_3p3_4p2_6m2_8m1_19m1_38p2_76p2_152m2_228m2_456p3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 3, 1, 1,
     0, 3, 4, 1, 1, -3, 1, 2, 2, 3, -3, 0, 1, 1, 3, 2, 3, 1, 0, 2,
     2, 3, 2, 0, -6, 0, 3, 2, 1, -4, 0, -1, 3, 0, -2, -5, 1, 2, -2, -1,
     -5, 0, -3, -4, -1, -1, -1, -1, -2, -4, -1, 8, 1, 1, -4, 0, 1, -7, 4, -4] := by
  eta_coeff

end WeightTwoCusps
