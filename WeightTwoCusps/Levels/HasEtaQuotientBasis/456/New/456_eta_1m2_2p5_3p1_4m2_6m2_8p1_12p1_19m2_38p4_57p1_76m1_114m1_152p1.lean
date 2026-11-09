module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(6z)^(-2) η(8z) η(12z) η(19z)^(-2) η(38z)^4 η(57z) η(76z)^(-1) η(114z)^(-1) η(152z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(6z)^(-2) η(8z) η(12z) η(19z)^(-2) η(38z)^4 η(57z) η(76z)^(-1) η(114z)^(-1) η(152z)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p5_3p1_4m2_6m2_8p1_12p1_19m2_38p4_57p1_76m1_114m1_152p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -2, 7 => 1, 11 => 1, 18 => -2, 37 => 4, 56 => 1, 75 => -1, 113 => -1, 151 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p5_3p1_4m2_6m2_8p1_12p1_19m2_38p4_57p1_76m1_114m1_152p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p5_3p1_4m2_6m2_8p1_12p1_19m2_38p4_57p1_76m1_114m1_152p1 =
    [0, 0, 0, 0, 0, 0, 1, 2, 0, -1, 0, 0, 1, 0, -1, -2, -2, 1, 0, 0,
     -1, -1, -1, -2, 2, 3, 4, -1, -3, 1, 0, 2, 2, -2, -6, -3, 2, 1, 0, -2,
     -2, -2, -1, 5, 3, 2, -1, -1, 2, -1, 2, 3, 0, -6, 0, 1, 0, 0, -2, 0,
     -1, 5, 5, 4, 2, 0, 2, 1, -1, 1, 0, 1, -5, -1, -1, -3, 0, -6, 1, -1,
     2, 5, 7, 1, -1, 0, 1, 1, -3, 1, -2, -7, -2, -3, -1, 0, -8, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
