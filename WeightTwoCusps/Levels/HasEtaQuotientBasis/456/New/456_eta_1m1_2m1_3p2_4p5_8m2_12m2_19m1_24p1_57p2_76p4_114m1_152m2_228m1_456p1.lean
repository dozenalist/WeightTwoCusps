module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^5 η(8z)^(-2) η(12z)^(-2) η(19z)^(-1) η(24z) η(57z)^2 η(76z)^4 η(114z)^(-1) η(152z)^(-2) η(228z)^(-1) η(456z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^5 η(8z)^(-2) η(12z)^(-2) η(19z)^(-1) η(24z) η(57z)^2 η(76z)^4 η(114z)^(-1) η(152z)^(-2) η(228z)^(-1) η(456z)` at level 456. -/
abbrev cuspForm_456_eta_1m1_2m1_3p2_4p5_8m2_12m2_19m1_24p1_57p2_76p4_114m1_152m2_228m1_456p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -1, 1 => -1, 2 => 2, 3 => 5, 7 => -2, 11 => -2, 18 => -1, 23 => 1, 56 => 2, 75 => 4, 113 => -1, 151 => -2, 227 => -1, 455 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m1_2m1_3p2_4p5_8m2_12m2_19m1_24p1_57p2_76p4_114m1_152m2_228m1_456p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m1_2m1_3p2_4p5_8m2_12m2_19m1_24p1_57p2_76p4_114m1_152m2_228m1_456p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 2, 1, -1, 2, -1, 2, 0,
     -1, 2, 0, 3, 1, 0, 3, -1, 2, -1, 0, 1, 2, 4, -3, 3, -2, 3, 0, -2,
     1, -4, 3, 2, -2, 3, 0, 4, 0, 4, 2, 2, 4, -5, 4, -6, 5, 0, -4, 3,
     -3, 6, 5, -3, 4, -4, 1, -5, 0, -3, -2, 6, -8, 2, -7, 4, 0, -7, 1, -7,
     -1, 8, -4, 2, -2, -2, -6, -4, -4, -8, -1, -7, -5, -6, -1, 0, -5, -2, -1, -10] := by
  eta_coeff

end WeightTwoCusps
