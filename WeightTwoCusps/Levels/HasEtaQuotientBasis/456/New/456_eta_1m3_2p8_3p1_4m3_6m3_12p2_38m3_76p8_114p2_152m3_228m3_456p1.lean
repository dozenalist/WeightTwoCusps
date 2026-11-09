module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(38z)^(-3) η(76z)^8 η(114z)^2 η(152z)^(-3) η(228z)^(-3) η(456z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(38z)^(-3) η(76z)^8 η(114z)^2 η(152z)^(-3) η(228z)^(-3) η(456z)` at level 456. -/
abbrev cuspForm_456_eta_1m3_2p8_3p1_4m3_6m3_12p2_38m3_76p8_114p2_152m3_228m3_456p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -3, 11 => 2, 37 => -3, 75 => 8, 113 => 2, 151 => -3, 227 => -3, 455 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m3_2p8_3p1_4m3_6m3_12p2_38m3_76p8_114p2_152m3_228m3_456p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m3_2p8_3p1_4m3_6m3_12p2_38m3_76p8_114p2_152m3_228m3_456p1 =
    [0, 0, 1, 3, 1, -3, -1, 0, 0, 3, -1, -3, -2, -3, 1, 0, -1, 0, -1, 0,
     0, 3, 1, -3, 1, 3, -1, 0, 1, 0, 0, -3, 2, 0, 1, 3, 0, 3, 0, 3,
     2, 9, 5, -9, -2, -3, 0, 9, -4, -12, -6, -12, 2, 3, -3, 3, -4, 0, 1, 9,
     4, -9, 0, 9, -3, -3, 2, 0, -1, -12, 5, 3, 4, 6, 0, 6, 0, 9, -2, 6,
     6, -6, 0, -6, 0, 3, -3, -15, -2, -9, -1, 9, -1, 12, -3, 0, 3, 3, 4, -3] := by
  eta_coeff

end WeightTwoCusps
