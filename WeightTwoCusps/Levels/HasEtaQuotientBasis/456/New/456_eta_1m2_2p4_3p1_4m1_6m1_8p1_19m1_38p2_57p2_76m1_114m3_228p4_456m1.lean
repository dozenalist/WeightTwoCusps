module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(6z)^(-1) η(8z) η(19z)^(-1) η(38z)^2 η(57z)^2 η(76z)^(-1) η(114z)^(-3) η(228z)^4 η(456z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(6z)^(-1) η(8z) η(19z)^(-1) η(38z)^2 η(57z)^2 η(76z)^(-1) η(114z)^(-3) η(228z)^4 η(456z)^(-1)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p4_3p1_4m1_6m1_8p1_19m1_38p2_57p2_76m1_114m3_228p4_456m1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 5 => -1, 7 => 1, 18 => -1, 37 => 2, 56 => 2, 75 => -1, 113 => -3, 227 => 4, 455 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p4_3p1_4m1_6m1_8p1_19m1_38p2_57p2_76m1_114m3_228p4_456m1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p4_3p1_4m1_6m1_8p1_19m1_38p2_57p2_76m1_114m3_228p4_456m1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 1, 1, 2, 1, 1, -1, 0,
     2, 0, 1, 0, 2, 0, -1, 1, -1, 3, 1, 1, 1, -1, 3, 2, 1, 0, 0, 1,
     -2, 0, 0, 0, 0, -1, 1, -4, 1, 2, 1, -1, -4, -1, -1, 2, -1, 0, -2, -2,
     0, -2, -3, -2, -1, 0, -3, -3, 0, -1, -1, -3, -3, -4, -1, -1, 0, -5, -2, 0,
     -2, -4, -3, -1, -1, 2, -5, -1, -3, 0, 0, -4, -2, -4, 0, 0, -5, 0, -1, 1] := by
  eta_coeff

end WeightTwoCusps
