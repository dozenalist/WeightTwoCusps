module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-2) η(8z) η(19z)^(-1) η(38z)^4 η(76z)^(-4) η(114z)^(-3) η(152z)^2 η(228z)^7 η(456z)^(-3)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-2) η(8z) η(19z)^(-1) η(38z)^4 η(76z)^(-4) η(114z)^(-3) η(152z)^2 η(228z)^7 η(456z)^(-3)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p3_3p3_4m1_6m2_8p1_19m1_38p4_76m4_114m3_152p2_228p7_456m3 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -2, 7 => 1, 18 => -1, 37 => 4, 75 => -4, 113 => -3, 151 => 2, 227 => 7, 455 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p3_3p3_4m1_6m2_8p1_19m1_38p4_76m4_114m3_152p2_228p7_456m3_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p3_3p3_4m1_6m2_8p1_19m1_38p4_76m4_114m3_152p2_228p7_456m3 =
    [0, 1, 2, 2, 1, 0, 2, 2, 2, 1, -1, 0, -1, 3, 2, 0, 1, -1, 1, -1,
     2, 3, -1, 1, -1, 2, 3, 3, 5, -4, -1, -1, 2, 2, -4, 0, -3, 2, 0, -1,
     -4, -6, 0, -2, -5, -6, -5, 0, -2, 0, 1, -8, -3, -4, -3, -3, -1, 1, -5, -5,
     1, 2, 2, 0, -5, -9, -10, 4, 0, -2, -5, -2, 7, 0, 2, -2, -1, 0, 9, 3,
     -3, 3, 7, 16, 2, 4, 1, -6, 0, 7, 5, 1, 2, 6, -1, 1, 6, 10, 4, -7] := by
  eta_coeff

end WeightTwoCusps
