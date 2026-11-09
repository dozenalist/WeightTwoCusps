module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-2) η(2z)^4 η(4z) η(8z)^(-1) η(11z)^(-1) η(22z)^4 η(33z) η(44z)^(-3) η(66z)^(-2) η(88z)^2 η(132z)^2 η(264z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z) η(8z)^(-1) η(11z)^(-1) η(22z)^4 η(33z) η(44z)^(-3) η(66z)^(-2) η(88z)^2 η(132z)^2 η(264z)^(-1)` at level 264. -/
abbrev cuspForm_264_eta_1m2_2p4_4p1_8m1_11m1_22p4_33p1_44m3_66m2_88p2_132p2_264m1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -2, 1 => 4, 3 => 1, 7 => -1, 10 => -1, 21 => 4, 32 => 1, 43 => -3, 65 => -2, 87 => 2, 131 => 2, 263 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m2_2p4_4p1_8m1_11m1_22p4_33p1_44m3_66m2_88p2_132p2_264m1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m2_2p4_4p1_8m1_11m1_22p4_33p1_44m3_66m2_88p2_132p2_264m1 =
    [0, 1, 2, 1, 2, 1, -2, 2, 0, -2, 2, -1, 1, 2, -1, -1, -1, 0, 2, 0,
     -4, 0, -1, -2, -6, -5, -7, -6, 8, -6, -2, 1, -4, 2, -4, -4, -1, 4, 0, 4,
     -6, -6, 7, 2, 2, 0, 10, 5, 10, 11, -8, 4, 2, 5, 4, -1, 9, 8, 6, -3,
     4, -10, 8, 14, -5, 2, -2, 7, -10, -2, -10, -12, 6, 2, 0, -7, -6, 1, -5, -18,
     -1, 2, -4, 12, -8, -16, 6, -6, 3, -12, 2, 8, 10, 13, -8, 2, -2, 6, 6, -1] := by
  eta_coeff

end WeightTwoCusps
