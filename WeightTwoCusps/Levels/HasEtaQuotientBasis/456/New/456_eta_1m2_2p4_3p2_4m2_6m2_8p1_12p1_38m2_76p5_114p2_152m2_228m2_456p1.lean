module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-2) η(6z)^(-2) η(8z) η(12z) η(38z)^(-2) η(76z)^5 η(114z)^2 η(152z)^(-2) η(228z)^(-2) η(456z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-2) η(6z)^(-2) η(8z) η(12z) η(38z)^(-2) η(76z)^5 η(114z)^2 η(152z)^(-2) η(228z)^(-2) η(456z)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p4_3p2_4m2_6m2_8p1_12p1_38m2_76p5_114p2_152m2_228m2_456p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 4, 2 => 2, 3 => -2, 5 => -2, 7 => 1, 11 => 1, 37 => -2, 75 => 5, 113 => 2, 151 => -2, 227 => -2, 455 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p4_3p2_4m2_6m2_8p1_12p1_38m2_76p5_114p2_152m2_228m2_456p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p4_3p2_4m2_6m2_8p1_12p1_38m2_76p5_114p2_152m2_228m2_456p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 2, 2, 0, 1, 0,
     0, 0, 1, 2, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 1, 0, 0, -2,
     0, 0, -2, 0, 0, 0, 0, -2, 2, 4, 2, 2, -2, 4, 3, 0, 2, 0, 0, -4,
     1, 4, -2, -2, -2, 0, 1, 0, 2, 0, -1, 0, -2, 0, 2, -2, 0, -4, -1, 0,
     -4, 0, -2, -2, -1, -4, 0, 0, 0, 4, -4, 0, -2, 0, -3, 0, -1, -8, -2, -2] := by
  eta_coeff

end WeightTwoCusps
