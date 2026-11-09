module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^5 η(8z)^(-2) η(12z)^(-2) η(19z)^(-2) η(24z) η(38z)^5 η(57z) η(76z)^(-1) η(114z)^(-2) η(152z)^(-1) η(456z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^5 η(8z)^(-2) η(12z)^(-2) η(19z)^(-2) η(24z) η(38z)^5 η(57z) η(76z)^(-1) η(114z)^(-2) η(152z)^(-1) η(456z)^2` at level 456. -/
abbrev cuspForm_456_eta_1m1_2m1_3p2_4p5_8m2_12m2_19m2_24p1_38p5_57p1_76m1_114m2_152m1_456p2 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -1, 1 => -1, 2 => 2, 3 => 5, 7 => -2, 11 => -2, 18 => -2, 23 => 1, 37 => 5, 56 => 1, 75 => -1, 113 => -2, 151 => -1, 455 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m1_2m1_3p2_4p5_8m2_12m2_19m2_24p1_38p5_57p1_76m1_114m2_152m1_456p2_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m1_2m1_3p2_4p5_8m2_12m2_19m2_24p1_38p5_57p1_76m1_114m2_152m1_456p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 2, 1, -1, 2, -1, 2, 0, -1,
     2, 0, 3, 1, 0, 3, -1, 3, 0, 3, 3, 4, 5, -4, 5, -3, 5, 0, -3, 3,
     -4, 6, 3, -2, 6, -1, 3, -4, -5, -3, -2, 5, -5, 1, -5, 2, 0, -3, -2, -7,
     0, 4, -5, -2, -1, -2, -3, 1, -6, -8, -3, -3, -5, -6, -2, 0, -4, -1, 2, -7] := by
  eta_coeff

end WeightTwoCusps
