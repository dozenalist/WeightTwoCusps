module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(11z)^(-1) η(12z) η(22z) η(33z) η(44z)^2 η(66z)^(-2) η(88z)^(-1) η(132z)^3 η(264z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(11z)^(-1) η(12z) η(22z) η(33z) η(44z)^2 η(66z)^(-2) η(88z)^(-1) η(132z)^3 η(264z)^(-1)` at level 264. -/
abbrev cuspForm_264_eta_1m3_2p6_3p3_4m2_6m3_11m1_12p1_22p1_33p1_44p2_66m2_88m1_132p3_264m1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 10 => -1, 11 => 1, 21 => 1, 32 => 1, 43 => 2, 65 => -2, 87 => -1, 131 => 3, 263 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m3_2p6_3p3_4m2_6m3_11m1_12p1_22p1_33p1_44p2_66m2_88m1_132p3_264m1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m3_2p6_3p3_4m2_6m3_11m1_12p1_22p1_33p1_44p2_66m2_88m1_132p3_264m1 =
    [0, 0, 1, 3, 3, 1, -1, 0, 3, 2, 2, 0, -3, 0, 2, 6, 1, -4, 1, 0,
     2, 2, -1, -3, -3, 3, 6, -2, -4, 2, -2, -1, -1, -1, -4, -6, 3, 5, -2, -4,
     2, -2, -2, 2, -1, -7, -8, -6, -1, -6, -1, 2, -14, -4, -1, -1, -4, -4, 0, -1,
     -2, 4, 0, -8, 1, 0, 1, -7, 2, 0, 4, 5, 3, 2, -6, 9, 8, 0, -6, 8,
     6, 11, 0, 2, 4, -6, 10, -2, -1, -5, 2, 12, 16, 2, 0, 12, 1, 3, -3, -2] := by
  eta_coeff

end WeightTwoCusps
