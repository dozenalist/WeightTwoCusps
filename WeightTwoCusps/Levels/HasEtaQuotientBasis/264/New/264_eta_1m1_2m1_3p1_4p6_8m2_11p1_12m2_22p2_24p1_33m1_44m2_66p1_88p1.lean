module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-1) η(2z)^(-1) η(3z) η(4z)^6 η(8z)^(-2) η(11z) η(12z)^(-2) η(22z)^2 η(24z) η(33z)^(-1) η(44z)^(-2) η(66z) η(88z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-1) η(3z) η(4z)^6 η(8z)^(-2) η(11z) η(12z)^(-2) η(22z)^2 η(24z) η(33z)^(-1) η(44z)^(-2) η(66z) η(88z)` at level 264. -/
abbrev cuspForm_264_eta_1m1_2m1_3p1_4p6_8m2_11p1_12m2_22p2_24p1_33m1_44m2_66p1_88p1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -1, 1 => -1, 2 => 1, 3 => 6, 7 => -2, 10 => 1, 11 => -2, 21 => 2, 23 => 1, 32 => -1, 43 => -2, 65 => 1, 87 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m1_2m1_3p1_4p6_8m2_11p1_12m2_22p2_24p1_33m1_44m2_66p1_88p1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m1_2m1_3p1_4p6_8m2_11p1_12m2_22p2_24p1_33m1_44m2_66p1_88p1 =
    [0, 0, 0, 0, 1, 1, 3, 3, 2, 3, 0, 3, 2, 3, 3, -1, 3, 0, 3, 4,
     1, 4, 0, 4, 1, 0, 3, -4, -5, -9, -6, -7, 2, -3, -6, -7, -5, 5, -6, 2,
     -7, -9, 3, -6, 1, -9, 0, 5, -12, 11, -3, 10, 7, 2, -3, -7, 11, 6, 0, -6,
     -1, -3, 3, 3, -13, -7, -3, -1, -2, -14, 6, -18, 2, -12, -9, 1, 0, 3, -15, -11,
     -9, 1, 6, 0, -1, -4, 6, 3, 2, 9, -9, 13, -7, 14, 3, 14, 13, -2, -6, 0] := by
  eta_coeff

end WeightTwoCusps
