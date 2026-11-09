module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(4z) η(6z)^(-2) η(8z)^(-1) η(12z) η(19z)^(-2) η(38z)^3 η(57z) η(76z)^2 η(114z)^(-1) η(152z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(4z) η(6z)^(-2) η(8z)^(-1) η(12z) η(19z)^(-2) η(38z)^3 η(57z) η(76z)^2 η(114z)^(-1) η(152z)^(-1)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p4_3p1_4p1_6m2_8m1_12p1_19m2_38p3_57p1_76p2_114m1_152m1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 4, 2 => 1, 3 => 1, 5 => -2, 7 => -1, 11 => 1, 18 => -2, 37 => 3, 56 => 1, 75 => 2, 113 => -1, 151 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p4_3p1_4p1_6m2_8m1_12p1_19m2_38p3_57p1_76p2_114m1_152m1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p4_3p1_4p1_6m2_8m1_12p1_19m2_38p3_57p1_76p2_114m1_152m1 =
    [0, 1, 2, 1, 1, -1, -3, 1, 1, 1, 0, -4, -2, -2, 1, 1, -3, -1, 0, 0,
     3, 5, 1, 2, -3, -5, 2, 2, 3, -2, -7, -6, -1, 4, 1, -4, -1, 2, 0, 7,
     7, -3, 2, -2, -4, 3, 3, 3, -6, -6, -7, 2, 5, 3, 0, -2, 6, 0, 13, 9,
     -7, 2, -1, -9, 5, 5, 0, -6, -11, -7, -1, 5, 9, -3, -7, 8, -1, 14, 5, -11,
     -3, -4, -6, 2, 4, -4, -5, -4, -4, 5, 4, 9, 4, -7, 12, -2, 13, 3, -13, -8] := by
  eta_coeff

end WeightTwoCusps
