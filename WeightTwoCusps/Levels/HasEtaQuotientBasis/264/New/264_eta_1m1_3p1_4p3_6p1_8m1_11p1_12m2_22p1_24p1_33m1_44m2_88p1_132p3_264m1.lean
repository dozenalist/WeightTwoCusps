module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-1) η(3z) η(4z)^3 η(6z) η(8z)^(-1) η(11z) η(12z)^(-2) η(22z) η(24z) η(33z)^(-1) η(44z)^(-2) η(88z) η(132z)^3 η(264z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z) η(4z)^3 η(6z) η(8z)^(-1) η(11z) η(12z)^(-2) η(22z) η(24z) η(33z)^(-1) η(44z)^(-2) η(88z) η(132z)^3 η(264z)^(-1)` at level 264. -/
abbrev cuspForm_264_eta_1m1_3p1_4p3_6p1_8m1_11p1_12m2_22p1_24p1_33m1_44m2_88p1_132p3_264m1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -1, 2 => 1, 3 => 3, 5 => 1, 7 => -1, 10 => 1, 11 => -2, 21 => 1, 23 => 1, 32 => -1, 43 => -2, 87 => 1, 131 => 3, 263 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m1_3p1_4p3_6p1_8m1_11p1_12m2_22p1_24p1_33m1_44m2_88p1_132p3_264m1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m1_3p1_4p3_6p1_8m1_11p1_12m2_22p1_24p1_33m1_44m2_88p1_132p3_264m1 =
    [0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 1, 2, 0, 2, 0, 0, 2, -1, 2, -1,
     0, 1, 0, 4, -2, 0, 0, -2, 0, -5, -2, -6, -2, -2, -4, -2, 0, 2, -4, 0,
     -4, -1, 2, -1, 0, -6, 3, 2, -2, 6, -3, 7, 0, 4, 0, -4, 8, -1, 2, -2,
     0, 2, 1, 1, -6, -4, -1, -2, 0, -6, 2, -6, 2, -4, -3, 0, 0, 1, -4, -1,
     -4, 0, 2, 2, 0, 4, 6, 5, 2, 2, -5, 4, 0, 8, -2, 4, 2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
