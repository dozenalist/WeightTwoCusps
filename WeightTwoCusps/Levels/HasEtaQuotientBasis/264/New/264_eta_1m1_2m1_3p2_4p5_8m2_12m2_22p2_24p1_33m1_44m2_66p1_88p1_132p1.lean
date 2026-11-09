module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^5 η(8z)^(-2) η(12z)^(-2) η(22z)^2 η(24z) η(33z)^(-1) η(44z)^(-2) η(66z) η(88z) η(132z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^5 η(8z)^(-2) η(12z)^(-2) η(22z)^2 η(24z) η(33z)^(-1) η(44z)^(-2) η(66z) η(88z) η(132z)` at level 264. -/
abbrev cuspForm_264_eta_1m1_2m1_3p2_4p5_8m2_12m2_22p2_24p1_33m1_44m2_66p1_88p1_132p1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -1, 1 => -1, 2 => 2, 3 => 5, 7 => -2, 11 => -2, 21 => 2, 23 => 1, 32 => -1, 43 => -2, 65 => 1, 87 => 1, 131 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m1_2m1_3p2_4p5_8m2_12m2_22p2_24p1_33m1_44m2_66p1_88p1_132p1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m1_2m1_3p2_4p5_8m2_12m2_22p2_24p1_33m1_44m2_66p1_88p1_132p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 2, 1, -1, 2, -1, 2, 0,
     -1, 2, 0, 3, 1, 0, 3, -1, 1, -2, -3, -3, -2, -3, -6, -3, -3, 3, -4, 1,
     -5, -4, 3, -2, 1, -4, 1, 2, -7, 5, -4, 4, 5, 1, 2, -6, 9, 1, 2, 0,
     2, 2, 4, 4, -6, -5, -2, -5, -2, -7, 4, -7, 2, -4, -6, 2, -2, 1, -9, -2,
     -3, -1, 0, -2, -5, 2, 6, 3, 1, 7, -5, 5, -3, 6, 3, 8, 11, -2, -2, 1] := by
  eta_coeff

end WeightTwoCusps
