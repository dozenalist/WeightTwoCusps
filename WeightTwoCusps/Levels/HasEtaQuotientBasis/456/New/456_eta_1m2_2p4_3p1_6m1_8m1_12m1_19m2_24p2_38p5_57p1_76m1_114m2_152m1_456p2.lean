module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(8z)^(-1) η(12z)^(-1) η(19z)^(-2) η(24z)^2 η(38z)^5 η(57z) η(76z)^(-1) η(114z)^(-2) η(152z)^(-1) η(456z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(8z)^(-1) η(12z)^(-1) η(19z)^(-2) η(24z)^2 η(38z)^5 η(57z) η(76z)^(-1) η(114z)^(-2) η(152z)^(-1) η(456z)^2` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p4_3p1_6m1_8m1_12m1_19m2_24p2_38p5_57p1_76m1_114m2_152m1_456p2 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 7 => -1, 11 => -1, 18 => -2, 23 => 2, 37 => 5, 56 => 1, 75 => -1, 113 => -2, 151 => -1, 455 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p4_3p1_6m1_8m1_12m1_19m2_24p2_38p5_57p1_76m1_114m2_152m1_456p2_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p4_3p1_6m1_8m1_12m1_19m2_24p2_38p5_57p1_76m1_114m2_152m1_456p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, -1, 1, 0, 1, 0, -1,
     2, -1, 1, 1, 0, 2, 0, 1, 1, 3, 1, 2, 1, -3, 2, -1, 2, 0, -2, 3,
     -5, 2, 3, 0, 4, 1, 3, -2, -1, -2, -1, 1, -3, -1, -3, 0, 0, 0, -2, -6,
     0, 3, -1, -1, 1, -1, -2, 1, -2, -4, -2, -2, -3, -3, -1, 0, 0, -1, 1, -3] := by
  eta_coeff

end WeightTwoCusps
