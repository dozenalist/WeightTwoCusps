module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(2z)^(-3) η(3z)^(-1) η(4z)^7 η(6z)^4 η(8z)^(-3) η(12z)^(-4) η(19z)^3 η(24z)^2 η(38z)^(-2) η(57z)^(-2) η(114z)^3 η(228z)^(-1) η(456z)`; see
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

/-- The cuspidal eta quotient `η(2z)^(-3) η(3z)^(-1) η(4z)^7 η(6z)^4 η(8z)^(-3) η(12z)^(-4) η(19z)^3 η(24z)^2 η(38z)^(-2) η(57z)^(-2) η(114z)^3 η(228z)^(-1) η(456z)` at level 456. -/
abbrev cuspForm_456_eta_2m3_3m1_4p7_6p4_8m3_12m4_19p3_24p2_38m2_57m2_114p3_228m1_456p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 1 => -3, 2 => -1, 3 => 7, 5 => 4, 7 => -3, 11 => -4, 18 => 3, 23 => 2, 37 => -2, 56 => -2, 113 => 3, 227 => -1, 455 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_2m3_3m1_4p7_6p4_8m3_12m4_19p3_24p2_38m2_57m2_114p3_228m1_456p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_2m3_3m1_4p7_6p4_8m3_12m4_19p3_24p2_38m2_57m2_114p3_228m1_456p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
     0, 3, 1, 2, 3, -1, 2, -1, 0, 1, 2, 4, 3, 4, 3, 2, 3, 2, 0, 0,
     -4, -2, -5, -5, 4, 0, 9, 6, 1, -4, -8, -6, -10, -3, -3, -2, 1, -1, 4, -3,
     5, 8, 2, 1, -8, -13, -10, -1, 6, 6, 5, 11, -1, 3, -6, -11, 0, -2, 5, -3,
     -8, -1, -2, 10, 0, 0, -6, -4, -3, -3, -5, -3, 0, 8, 14, -2, -1, 2, -4, 4] := by
  eta_coeff

end WeightTwoCusps
