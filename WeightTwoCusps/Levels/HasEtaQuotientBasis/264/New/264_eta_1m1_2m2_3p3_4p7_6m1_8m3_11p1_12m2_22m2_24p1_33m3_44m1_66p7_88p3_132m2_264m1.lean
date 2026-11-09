module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-1) η(2z)^(-2) η(3z)^3 η(4z)^7 η(6z)^(-1) η(8z)^(-3) η(11z) η(12z)^(-2) η(22z)^(-2) η(24z) η(33z)^(-3) η(44z)^(-1) η(66z)^7 η(88z)^3 η(132z)^(-2) η(264z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-2) η(3z)^3 η(4z)^7 η(6z)^(-1) η(8z)^(-3) η(11z) η(12z)^(-2) η(22z)^(-2) η(24z) η(33z)^(-3) η(44z)^(-1) η(66z)^7 η(88z)^3 η(132z)^(-2) η(264z)^(-1)` at level 264. -/
abbrev cuspForm_264_eta_1m1_2m2_3p3_4p7_6m1_8m3_11p1_12m2_22m2_24p1_33m3_44m1_66p7_88p3_132m2_264m1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -1, 1 => -2, 2 => 3, 3 => 7, 5 => -1, 7 => -3, 10 => 1, 11 => -2, 21 => -2, 23 => 1, 32 => -3, 43 => -1, 65 => 7, 87 => 3, 131 => -2, 263 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m1_2m2_3p3_4p7_6m1_8m3_11p1_12m2_22m2_24p1_33m3_44m1_66p7_88p3_132m2_264m1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m1_2m2_3p3_4p7_6m1_8m3_11p1_12m2_22m2_24p1_33m3_44m1_66p7_88p3_132m2_264m1 =
    [0, 1, 1, 4, 2, 4, -1, -1, -1, -1, 4, 0, -2, -3, -8, 3, -2, 4, 1, -6,
     2, -6, 1, -1, -2, 5, -2, 5, -1, -3, -1, -5, 3, -2, 10, 3, 2, 1, 0, 2,
     5, 3, 2, -6, -1, -5, -4, 0, 8, 2, 2, 0, -7, 1, 2, -3, -10, -8, -6, 6,
     -2, 1, -11, -19, 4, -13, 2, 11, -4, 10, -8, 3, -1, 8, 21, 0, 0, -2, 2, -5,
     4, 5, -2, 10, 7, -2, -6, -9, -1, -13, 4, -3, 10, -9, -13, -6, -12, 14, 3, 2] := by
  eta_coeff

end WeightTwoCusps
