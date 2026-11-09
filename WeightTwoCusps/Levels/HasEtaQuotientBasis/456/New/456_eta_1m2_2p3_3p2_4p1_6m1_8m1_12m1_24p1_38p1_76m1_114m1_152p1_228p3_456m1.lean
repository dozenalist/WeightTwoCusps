module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-1) η(8z)^(-1) η(12z)^(-1) η(24z) η(38z) η(76z)^(-1) η(114z)^(-1) η(152z) η(228z)^3 η(456z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-1) η(8z)^(-1) η(12z)^(-1) η(24z) η(38z) η(76z)^(-1) η(114z)^(-1) η(152z) η(228z)^3 η(456z)^(-1)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p3_3p2_4p1_6m1_8m1_12m1_24p1_38p1_76m1_114m1_152p1_228p3_456m1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -1, 7 => -1, 11 => -1, 23 => 1, 37 => 1, 75 => -1, 113 => -1, 151 => 1, 227 => 3, 455 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p3_3p2_4p1_6m1_8m1_12m1_24p1_38p1_76m1_114m1_152p1_228p3_456m1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p3_3p2_4p1_6m1_8m1_12m1_24p1_38p1_76m1_114m1_152p1_228p3_456m1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 0, 2, -2,
     0, 0, -1, 2, -2, 2, 0, 0, 2, -4, -2, -2, 0, 0, -1, 0, -2, 0, 0, 0,
     -2, -4, 0, -2, 0, 0, 0, 2, -1, 0, -2, -2, -2, 0, -2, -4, -2, 2, 0, 0,
     3, 0, 2, -2, 0, -4, -4, 4, 2, 2, 1, 0, 1, 2, 2, 0, 0, 0, 4, 2,
     0, 2, 2, 6, -2, 0, 0, -2, 2, 0, 2, -2, 2, 4, -1, 4, 2, 2, -2, -2] := by
  eta_coeff

end WeightTwoCusps
