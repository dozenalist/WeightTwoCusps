module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-3) η(6z)^(-3) η(8z) η(12z)^5 η(19z)^(-2) η(24z)^(-2) η(38z)^6 η(57z) η(76z)^(-4) η(114z)^(-4) η(152z) η(228z)^6 η(456z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-3) η(6z)^(-3) η(8z) η(12z)^5 η(19z)^(-2) η(24z)^(-2) η(38z)^6 η(57z) η(76z)^(-4) η(114z)^(-4) η(152z) η(228z)^6 η(456z)^(-2)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p5_3p1_4m3_6m3_8p1_12p5_19m2_24m2_38p6_57p1_76m4_114m4_152p1_228p6_456m2 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -3, 5 => -3, 7 => 1, 11 => 5, 18 => -2, 23 => -2, 37 => 6, 56 => 1, 75 => -4, 113 => -4, 151 => 1, 227 => 6, 455 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p5_3p1_4m3_6m3_8p1_12p5_19m2_24m2_38p6_57p1_76m4_114m4_152p1_228p6_456m2_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p5_3p1_4m3_6m3_8p1_12p5_19m2_24m2_38p6_57p1_76m4_114m4_152p1_228p6_456m2 =
    [0, 0, 0, 0, 1, 2, 0, -1, 1, 2, 2, 1, 1, 1, 0, 1, 1, -1, 0, 1,
     -1, -1, -1, 3, 4, -1, -1, 2, 4, 3, 5, 4, 1, 0, 2, 1, -3, 0, 2, -1,
     -5, -3, -2, -1, 0, 0, -2, -4, -3, 5, 3, -4, -2, -2, -2, -3, 1, -1, 2, -4,
     -3, -9, -5, 5, -3, -3, -12, -3, -6, -5, -5, -5, -5, -1, 1, -3, -3, -1, 9, -1,
     -1, 0, 0, 0, 6, 1, 3, -8, -4, 3, -2, 0, 1, 7, -12, 1, -4, 7, 2, 5] := by
  eta_coeff

end WeightTwoCusps
