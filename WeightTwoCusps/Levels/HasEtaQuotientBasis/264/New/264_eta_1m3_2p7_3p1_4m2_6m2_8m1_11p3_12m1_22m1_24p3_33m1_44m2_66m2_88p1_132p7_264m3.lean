module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(8z)^(-1) η(11z)^3 η(12z)^(-1) η(22z)^(-1) η(24z)^3 η(33z)^(-1) η(44z)^(-2) η(66z)^(-2) η(88z) η(132z)^7 η(264z)^(-3)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(8z)^(-1) η(11z)^3 η(12z)^(-1) η(22z)^(-1) η(24z)^3 η(33z)^(-1) η(44z)^(-2) η(66z)^(-2) η(88z) η(132z)^7 η(264z)^(-3)` at level 264. -/
abbrev cuspForm_264_eta_1m3_2p7_3p1_4m2_6m2_8m1_11p3_12m1_22m1_24p3_33m1_44m2_66m2_88p1_132p7_264m3 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 7 => -1, 10 => 3, 11 => -1, 21 => -1, 23 => 3, 32 => -1, 43 => -2, 65 => -2, 87 => 1, 131 => 7, 263 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m3_2p7_3p1_4m2_6m2_8m1_11p3_12m1_22m1_24p3_33m1_44m2_66m2_88p1_132p7_264m3_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m3_2p7_3p1_4m2_6m2_8m1_11p3_12m1_22m1_24p3_33m1_44m2_66m2_88p1_132p7_264m3 =
    [0, 1, 3, 2, 0, 1, 0, 1, 3, 1, 3, 1, -3, -5, -3, 5, 0, 4, 3, -6,
     3, -6, 0, 6, -3, 0, -9, 0, -6, -9, 0, -10, 3, -1, 0, 5, 0, 0, -6, 2,
     0, 9, 3, 0, 0, -14, 9, 0, 3, 6, -6, 8, 0, 9, 3, -2, 3, -12, 0, 7,
     -3, 3, -3, -21, -6, -9, 0, 16, 6, 8, -12, 0, 3, 2, 9, -8, 6, 0, -3, -7,
     -3, 10, 6, 12, 6, 16, 6, -1, 0, -10, 3, -11, -3, 1, -18, -18, -9, 7, 3, 1] := by
  eta_coeff

end WeightTwoCusps
