module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-1) η(3z) η(4z)^5 η(8z)^(-2) η(12z)^(-2) η(24z) η(57z)^(-2) η(114z)^4 η(228z) η(456z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z) η(4z)^5 η(8z)^(-2) η(12z)^(-2) η(24z) η(57z)^(-2) η(114z)^4 η(228z) η(456z)^(-1)` at level 456. -/
abbrev cuspForm_456_eta_1m1_3p1_4p5_8m2_12m2_24p1_57m2_114p4_228p1_456m1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -1, 2 => 1, 3 => 5, 7 => -2, 11 => -2, 23 => 1, 56 => -2, 113 => 4, 227 => 1, 455 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m1_3p1_4p5_8m2_12m2_24p1_57m2_114p4_228p1_456m1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m1_3p1_4p5_8m2_12m2_24p1_57m2_114p4_228p1_456m1 =
    [0, 0, 0, 0, 0, 1, 1, 2, 2, -1, 0, -3, -1, 0, -2, 1, -4, 1, 1, 0,
     2, -2, 0, -2, 0, -2, -4, 1, 0, 2, 1, 0, 2, -1, 4, -1, -2, 0, 0, 1,
     0, 4, 1, 4, 2, 0, 0, -3, -1, 0, -2, 2, 0, 2, 1, 0, 4, 0, 0, 0,
     -2, -6, 0, 3, 4, 6, -1, 0, -6, -3, 4, -8, 1, -8, 0, 3, 0, 7, -3, 0,
     -4, -2, -4, -10, 1, 0, -2, 2, -4, 6, -2, 8, 0, -5, 0, -1, 0, -4, 6, 4] := by
  eta_coeff

end WeightTwoCusps
