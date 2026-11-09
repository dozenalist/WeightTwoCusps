module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-3) η(6z)^(-3) η(8z) η(12z)^4 η(19z) η(24z)^(-1) η(38z)^(-1) η(76z)^2 η(114z) η(152z)^(-1) η(228z)^(-1) η(456z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-3) η(6z)^(-3) η(8z) η(12z)^4 η(19z) η(24z)^(-1) η(38z)^(-1) η(76z)^2 η(114z) η(152z)^(-1) η(228z)^(-1) η(456z)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p5_3p1_4m3_6m3_8p1_12p4_19p1_24m1_38m1_76p2_114p1_152m1_228m1_456p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -3, 5 => -3, 7 => 1, 11 => 4, 18 => 1, 23 => -1, 37 => -1, 75 => 2, 113 => 1, 151 => -1, 227 => -1, 455 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p5_3p1_4m3_6m3_8p1_12p4_19p1_24m1_38m1_76p2_114p1_152m1_228m1_456p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p5_3p1_4m3_6m3_8p1_12p4_19p1_24m1_38m1_76p2_114p1_152m1_228m1_456p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, -1, 1, 2,
     2, 1, 1, 1, 0, 1, 2, 1, 0, 0, 0, 1, 1, 1, -1, 0, 2, 0, 0, -2,
     2, 1, -2, 1, 0, -1, -1, 0, 1, 2, -1, 0, -2, 1, 2, -1, 1, -2, 2, -2,
     -1, 3, -2, -2, 0, 1, 2, -2, -2, 2, -1, 0, -3, 0, 2, -1, 0, -2, 0, -1,
     -2, 2, 0, -2, 0, -3, 1, 1, -3, 1, -4, -4, -2, -1, -2, -4, -2, -7, -3, -1] := by
  eta_coeff

end WeightTwoCusps
