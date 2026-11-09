module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-2) η(8z)^(-1) η(19z)^2 η(24z) η(38z)^(-3) η(57z)^(-2) η(76z)^3 η(114z)^4 η(152z)^(-1) η(228z)^(-2) η(456z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-2) η(8z)^(-1) η(19z)^2 η(24z) η(38z)^(-3) η(57z)^(-2) η(76z)^3 η(114z)^4 η(152z)^(-1) η(228z)^(-2) η(456z)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p3_3p2_4p1_6m2_8m1_19p2_24p1_38m3_57m2_76p3_114p4_152m1_228m2_456p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -2, 7 => -1, 18 => 2, 23 => 1, 37 => -3, 56 => -2, 75 => 3, 113 => 4, 151 => -1, 227 => -2, 455 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p3_3p2_4p1_6m2_8m1_19p2_24p1_38m3_57m2_76p3_114p4_152m1_228m2_456p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p3_3p2_4p1_6m2_8m1_19p2_24p1_38m3_57m2_76p3_114p4_152m1_228m2_456p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0,
     0, 1, 2, 4, 0, 0, 0, 0, 4, 2, 2, 0, 0, 3, 0, -2, -2, -4, 0, 2,
     0, -2, -8, 0, 0, 0, 2, -6, -2, -4, 0, 3, -4, 2, 2, 0, 4, 0, 2, 0,
     0, 8, 0, 0, 2, 0, 4, 0, 4, 2, -4, 4, -2, -4, 0, -3, 0, -6, -2, 0,
     -8, 0, 2, 2, -2, -4, 0, -2, 0, 2, -4, -4, 0, 0, 2, 0, 4, 0, -4, 0] := by
  eta_coeff

end WeightTwoCusps
