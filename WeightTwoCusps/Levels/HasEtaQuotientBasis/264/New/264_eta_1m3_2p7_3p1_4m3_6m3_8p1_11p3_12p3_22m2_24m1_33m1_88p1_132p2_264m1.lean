module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-3) η(6z)^(-3) η(8z) η(11z)^3 η(12z)^3 η(22z)^(-2) η(24z)^(-1) η(33z)^(-1) η(88z) η(132z)^2 η(264z)^(-1)`; see
[the local level table](../../TABLE.md#level-264).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-3) η(6z)^(-3) η(8z) η(11z)^3 η(12z)^3 η(22z)^(-2) η(24z)^(-1) η(33z)^(-1) η(88z) η(132z)^2 η(264z)^(-1)` at level 264. -/
abbrev cuspForm_264_eta_1m3_2p7_3p1_4m3_6m3_8p1_11p3_12p3_22m2_24m1_33m1_88p1_132p2_264m1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -3, 5 => -3, 7 => 1, 10 => 3, 11 => 3, 21 => -2, 23 => -1, 32 => -1, 87 => 1, 131 => 2, 263 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m3_2p7_3p1_4m3_6m3_8p1_11p3_12p3_22m2_24m1_33m1_88p1_132p2_264m1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m3_2p7_3p1_4m3_6m3_8p1_11p3_12p3_22m2_24m1_33m1_88p1_132p2_264m1 =
    [0, 0, 1, 3, 2, 0, 2, 3, 4, 6, 4, 3, 4, 3, -2, 0, 6, 0, -2, -6,
     -10, 0, 1, -3, -4, -3, -2, -3, 2, 3, 5, 6, -8, -6, 4, -3, 2, 0, -6, -6,
     -14, -3, -4, 0, 2, -15, 2, 3, 0, -3, -7, 12, 2, 0, -1, -6, 10, 0, -12, -3,
     -2, 3, -2, -15, -2, 3, 2, -6, -4, 9, -8, 3, 10, 0, 12, 3, 0, -3, 2, 3,
     -6, 9, 4, -6, -14, -12, -6, 3, 4, -12, 1, 3, -2, 3, -4, 12, 14, 9, -3, -3] := by
  eta_coeff

end WeightTwoCusps
