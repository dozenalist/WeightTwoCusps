module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-1) η(6z)^(-2) η(24z) η(38z)^2 η(76z)^(-2) η(114z)^(-2) η(152z) η(228z)^5 η(456z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-1) η(6z)^(-2) η(24z) η(38z)^2 η(76z)^(-2) η(114z)^(-2) η(152z) η(228z)^5 η(456z)^(-2)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p4_3p2_4m1_6m2_24p1_38p2_76m2_114m2_152p1_228p5_456m2 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 5 => -2, 23 => 1, 37 => 2, 75 => -2, 113 => -2, 151 => 1, 227 => 5, 455 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p4_3p2_4m1_6m2_24p1_38p2_76m2_114m2_152p1_228p5_456m2_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p4_3p2_4m1_6m2_24p1_38p2_76m2_114m2_152p1_228p5_456m2 =
    [0, 0, 0, 0, 1, 2, 1, 0, -1, 0, 1, 0, 1, -2, -2, 0, 0, 2, -1, 0,
     -1, -2, 1, 0, 0, -2, -1, 0, -1, 0, 0, 0, -1, -2, 0, 0, -1, 0, 0, 0,
     2, 2, -1, -4, -3, 2, 1, 0, -1, -2, -3, 4, 5, 0, 0, -4, 3, 0, 2, 4,
     -2, 2, 1, 4, 2, 0, 4, 0, -1, 0, 3, 4, 0, 2, 3, 0, 0, 2, -5, -4,
     0, 4, 3, -4, 1, -2, -1, 4, 2, -2, -5, 0, 2, 0, -1, 0, 0, 0, 0, -4] := by
  eta_coeff

end WeightTwoCusps
