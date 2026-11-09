module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-1) η(3z)^3 η(4z) η(6z)^(-1) η(38z)^(-2) η(76z)^7 η(114z) η(152z)^(-3) η(228z)^(-2) η(456z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(4z) η(6z)^(-1) η(38z)^(-2) η(76z)^7 η(114z) η(152z)^(-3) η(228z)^(-2) η(456z)` at level 456. -/
abbrev cuspForm_456_eta_1m1_3p3_4p1_6m1_38m2_76p7_114p1_152m3_228m2_456p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -1, 2 => 3, 3 => 1, 5 => -1, 37 => -2, 75 => 7, 113 => 1, 151 => -3, 227 => -2, 455 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m1_3p3_4p1_6m1_38m2_76p7_114p1_152m3_228m2_456p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m1_3p3_4p1_6m1_38m2_76p7_114p1_152m3_228m2_456p1 =
    [0, 0, 0, 0, 0, 1, 1, 2, 0, 1, 0, 1, 1, 0, 0, -1, 0, 1, -1, 0,
     0, 0, 0, -2, 0, -2, 0, 1, 0, -2, -1, 0, 0, -1, 0, -1, -2, 0, 0, -1,
     0, 0, 1, -2, 2, 4, 0, 3, -1, 2, 2, 0, 0, -4, -1, 2, -2, 0, 0, 0,
     0, -2, 0, -3, 0, 0, 1, -4, -2, -1, 0, -2, 1, -2, -4, 1, 0, 1, -1, 0,
     2, -10, -2, -2, 1, 0, -2, -2, -2, 2, 0, -2, -2, -3, 2, -1, 2, 4, 0, 8] := by
  eta_coeff

end WeightTwoCusps
