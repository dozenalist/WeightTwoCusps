module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^3 η(3z) η(4z)^2 η(6z)^(-1) η(8z)^(-1) η(19z)^(-1) η(38z)^2 η(57z)^2 η(76z)^(-1) η(114z)^(-2) η(228z) η(456z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z) η(4z)^2 η(6z)^(-1) η(8z)^(-1) η(19z)^(-1) η(38z)^2 η(57z)^2 η(76z)^(-1) η(114z)^(-2) η(228z) η(456z)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p3_3p1_4p2_6m1_8m1_19m1_38p2_57p2_76m1_114m2_228p1_456p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 3, 2 => 1, 3 => 2, 5 => -1, 7 => -1, 18 => -1, 37 => 2, 56 => 2, 75 => -1, 113 => -2, 227 => 1, 455 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p3_3p1_4p2_6m1_8m1_19m1_38p2_57p2_76m1_114m2_228p1_456p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p3_3p1_4p2_6m1_8m1_19m1_38p2_57p2_76m1_114m2_228p1_456p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 1, 2, 2, 3, 1, 0, 2, 1, 3, 1, 0, 1, -1, 3, 0, -1, 1,
     1, 1, 0, 2, 1, 4, 3, 0, -1, 0, 3, 2, 0, -1, 0, 0, 0, -1, 0, 2,
     0, 0, -1, -5, 2, 1, -2, -4, -1, 0, -2, 2, -5, -2, -5, 3, 0, -4, 2, -3,
     1, -2, -6, -5, -4, -4, -3, -5, -5, -3, 1, -4, -3, -6, 4, 1, -5, -1, -6, 1] := by
  eta_coeff

end WeightTwoCusps
