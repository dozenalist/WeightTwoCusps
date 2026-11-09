module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(4z) η(6z)^(-2) η(8z)^(-1) η(12z) η(19z)^(-1) η(38z) η(57z)^2 η(114z)^(-1) η(456z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(4z) η(6z)^(-2) η(8z)^(-1) η(12z) η(19z)^(-1) η(38z) η(57z)^2 η(114z)^(-1) η(456z)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p4_3p1_4p1_6m2_8m1_12p1_19m1_38p1_57p2_114m1_456p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 4, 2 => 1, 3 => 1, 5 => -2, 7 => -1, 11 => 1, 18 => -1, 37 => 1, 56 => 2, 113 => -1, 455 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p4_3p1_4p1_6m2_8m1_12p1_19m1_38p1_57p2_114m1_456p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p4_3p1_4p1_6m2_8m1_12p1_19m1_38p1_57p2_114m1_456p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 2, 1, 1, -1, -3, 1, 1, 1, 0, -4, -2, -2, 1, 1, -3, -1, 0, 0, 2,
     3, 0, 1, -2, -2, 1, 1, 2, -2, -3, -4, 1, 3, 0, -1, 0, 2, 0, 5, 4,
     -3, 1, 0, -2, 2, 2, 1, -4, -3, -3, 1, 2, 3, 1, -2, 4, 0, 6, 1, -6,
     -1, 1, -1, 1, 1, -3, -2, 0, 0, 2, 1, 4, 2, -3, 4, -1, 5, 0, -4, -3] := by
  eta_coeff

end WeightTwoCusps
