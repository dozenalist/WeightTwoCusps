module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(6z)^(-1) η(8z) η(19z)^(-2) η(38z)^5 η(57z) η(76z)^(-2) η(114z)^(-2) η(152z) η(228z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(6z)^(-1) η(8z) η(19z)^(-2) η(38z)^5 η(57z) η(76z)^(-2) η(114z)^(-2) η(152z) η(228z)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p4_3p1_4m1_6m1_8p1_19m2_38p5_57p1_76m2_114m2_152p1_228p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 5 => -1, 7 => 1, 18 => -2, 37 => 5, 56 => 1, 75 => -2, 113 => -2, 151 => 1, 227 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p4_3p1_4m1_6m1_8p1_19m2_38p5_57p1_76m2_114m2_152p1_228p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p4_3p1_4m1_6m1_8p1_19m2_38p5_57p1_76m2_114m2_152p1_228p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 1, 1, 2, 1, 1, -1, 0,
     2, 0, 1, 0, 2, 0, -1, 1, 0, 5, 2, 2, 2, 0, 5, 3, 2, -1, 0, 3,
     -2, 1, 0, 2, 0, -2, 2, -6, 2, 2, 1, -1, -6, 0, 0, 2, 0, 0, -3, -4,
     -1, -2, -5, -2, -1, 0, -5, -3, 2, 0, -2, -5, -5, -6, 1, -3, 0, -6, -2, 1,
     -4, -5, -5, -2, -1, 3, -4, -1, -3, 2, 1, -1, -2, -5, -1, 0, -5, -2, 0, 1] := by
  eta_coeff

end WeightTwoCusps
