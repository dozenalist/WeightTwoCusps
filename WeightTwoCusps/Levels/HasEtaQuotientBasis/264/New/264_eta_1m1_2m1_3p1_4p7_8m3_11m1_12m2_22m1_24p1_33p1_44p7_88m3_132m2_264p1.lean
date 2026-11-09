module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-1) η(2z)^(-1) η(3z) η(4z)^7 η(8z)^(-3) η(11z)^(-1) η(12z)^(-2) η(22z)^(-1) η(24z) η(33z) η(44z)^7 η(88z)^(-3) η(132z)^(-2) η(264z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-1) η(3z) η(4z)^7 η(8z)^(-3) η(11z)^(-1) η(12z)^(-2) η(22z)^(-1) η(24z) η(33z) η(44z)^7 η(88z)^(-3) η(132z)^(-2) η(264z)` at level 264. -/
abbrev cuspForm_264_eta_1m1_2m1_3p1_4p7_8m3_11m1_12m2_22m1_24p1_33p1_44p7_88m3_132m2_264p1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -1, 1 => -1, 2 => 1, 3 => 7, 7 => -3, 10 => -1, 11 => -2, 21 => -1, 23 => 1, 32 => 1, 43 => 7, 87 => -3, 131 => -2, 263 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m1_2m1_3p1_4p7_8m3_11m1_12m2_22m1_24p1_33p1_44p7_88m3_132m2_264p1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m1_2m1_3p1_4p7_8m3_11m1_12m2_22m1_24p1_33p1_44p7_88m3_132m2_264p1 =
    [0, 0, 1, 1, 3, 3, 1, 2, -3, 0, 0, 0, 3, -2, 2, 2, 3, 4, 1, -4,
     0, 0, -1, 1, -3, 1, 8, 10, 6, 2, -12, 1, -3, -1, 6, -10, 3, 9, 8, 10,
     0, -14, 2, -6, -3, -1, -18, -4, 3, 4, 7, -10, -12, 4, -11, -3, -6, -16, -6, 15,
     0, -2, -4, -14, 3, -20, -1, -5, -18, 4, 0, -17, -3, -6, 2, 3, -12, -2, -16, -6,
     0, 13, -6, -10, 6, -6, -4, -14, 3, 5, 0, 28, 18, -16, 6, 24, -3, -1, -3, 0] := by
  eta_coeff

end WeightTwoCusps
