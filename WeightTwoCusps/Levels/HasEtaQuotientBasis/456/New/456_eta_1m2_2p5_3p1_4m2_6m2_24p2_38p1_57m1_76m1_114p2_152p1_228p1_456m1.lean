module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(6z)^(-2) η(24z)^2 η(38z) η(57z)^(-1) η(76z)^(-1) η(114z)^2 η(152z) η(228z) η(456z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(6z)^(-2) η(24z)^2 η(38z) η(57z)^(-1) η(76z)^(-1) η(114z)^2 η(152z) η(228z) η(456z)^(-1)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p5_3p1_4m2_6m2_24p2_38p1_57m1_76m1_114p2_152p1_228p1_456m1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -2, 23 => 2, 37 => 1, 56 => -1, 75 => -1, 113 => 2, 151 => 1, 227 => 1, 455 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p5_3p1_4m2_6m2_24p2_38p1_57m1_76m1_114p2_152p1_228p1_456m1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p5_3p1_4m2_6m2_24p2_38p1_57m1_76m1_114p2_152p1_228p1_456m1 =
    [0, 0, 0, 0, 1, 2, 0, -1, 0, 0, 1, 0, 0, 0, -2, 0, 1, 2, 0, -2,
     0, 0, 1, 0, 0, -1, -2, 0, 0, 0, 0, -1, -2, 0, 0, 0, 0, -1, 0, 0,
     2, 2, -1, -3, -2, 1, 1, 0, -1, -1, -2, 0, 3, 0, -1, -3, 0, 2, 0, 2,
     -1, -1, 2, 1, 1, 0, 0, 1, -2, 1, 3, 0, 0, 1, 2, 1, 0, 2, -2, -2,
     0, 1, 4, -2, -1, -1, -2, 1, 1, -2, -1, -1, 0, 1, 0, 4, 0, -1, 2, 1] := by
  eta_coeff

end WeightTwoCusps
