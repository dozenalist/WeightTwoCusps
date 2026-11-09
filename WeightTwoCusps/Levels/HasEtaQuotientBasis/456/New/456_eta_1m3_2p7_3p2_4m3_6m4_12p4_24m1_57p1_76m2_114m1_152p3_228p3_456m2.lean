module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-4) η(12z)^4 η(24z)^(-1) η(57z) η(76z)^(-2) η(114z)^(-1) η(152z)^3 η(228z)^3 η(456z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-4) η(12z)^4 η(24z)^(-1) η(57z) η(76z)^(-2) η(114z)^(-1) η(152z)^3 η(228z)^3 η(456z)^(-2)` at level 456. -/
abbrev cuspForm_456_eta_1m3_2p7_3p2_4m3_6m4_12p4_24m1_57p1_76m2_114m1_152p3_228p3_456m2 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -4, 11 => 4, 23 => -1, 56 => 1, 75 => -2, 113 => -1, 151 => 3, 227 => 3, 455 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m3_2p7_3p2_4m3_6m4_12p4_24m1_57p1_76m2_114m1_152p3_228p3_456m2_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m3_2p7_3p2_4m3_6m4_12p4_24m1_57p1_76m2_114m1_152p3_228p3_456m2 =
    [0, 1, 3, 2, -1, -1, 1, 4, 4, 2, 1, -3, -1, 3, 1, 1, -1, -2, 0, -1,
     2, 2, -4, 1, 2, 1, 3, -2, 2, -3, -5, 3, 1, 0, -2, -3, -2, -1, 0, 2,
     -2, 2, 3, -3, 0, -2, -1, -2, 0, 0, -2, -3, -4, -1, -3, 0, 3, 1, 2, -5,
     -5, 3, -1, 4, -3, -7, -1, -1, -2, -4, -4, -1, 2, -2, 5, -3, -1, 0, 2, 10,
     -6, -4, 1, 6, 5, -1, 3, -2, -3, 5, 6, -1, 0, 2, -3, 2, 4, 8, -6, -4] := by
  eta_coeff

end WeightTwoCusps
