module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(12z) η(24z) η(38z)^(-3) η(57z) η(76z)^7 η(114z) η(152z)^(-3) η(228z)^(-3) η(456z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(12z) η(24z) η(38z)^(-3) η(57z) η(76z)^7 η(114z) η(152z)^(-3) η(228z)^(-3) η(456z)^2` at level 456. -/
abbrev cuspForm_456_eta_1m3_2p7_3p2_4m3_6m3_12p1_24p1_38m3_57p1_76p7_114p1_152m3_228m3_456p2 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -3, 11 => 1, 23 => 1, 37 => -3, 56 => 1, 75 => 7, 113 => 1, 151 => -3, 227 => -3, 455 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m3_2p7_3p2_4m3_6m3_12p1_24p1_38m3_57p1_76p7_114p1_152m3_228m3_456p2_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m3_2p7_3p2_4m3_6m3_12p1_24p1_38m3_57p1_76p7_114p1_152m3_228m3_456p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2, -1,
     -1, 1, 3, 1, 0, 2, -2, -2, 1, 3, 3, -4, -1, 3, 1, 0, -1, 2, 0, -3,
     0, 3, 0, -3, -3, 0, 1, -3, -1, 1, 2, -3, -2, 6, 5, 6, 3, 1, 0, -2,
     7, 5, 0, 1, -9, -2, 3, 3, 7, -7, -3, 4, 3, 4, -4, -3, 0, -5, -1, 2,
     -6, -5, -8, -4, 2, -3, -4, -6, 7, -2, -5, 8, 6, 7, -4, 2, 4, -5, 0, 0] := by
  eta_coeff

end WeightTwoCusps
