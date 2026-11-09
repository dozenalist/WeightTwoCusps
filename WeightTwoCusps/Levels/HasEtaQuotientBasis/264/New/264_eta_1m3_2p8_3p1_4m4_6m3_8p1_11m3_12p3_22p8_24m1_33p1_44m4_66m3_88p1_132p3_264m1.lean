module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-4) η(6z)^(-3) η(8z) η(11z)^(-3) η(12z)^3 η(22z)^8 η(24z)^(-1) η(33z) η(44z)^(-4) η(66z)^(-3) η(88z) η(132z)^3 η(264z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-4) η(6z)^(-3) η(8z) η(11z)^(-3) η(12z)^3 η(22z)^8 η(24z)^(-1) η(33z) η(44z)^(-4) η(66z)^(-3) η(88z) η(132z)^3 η(264z)^(-1)` at level 264. -/
abbrev cuspForm_264_eta_1m3_2p8_3p1_4m4_6m3_8p1_11m3_12p3_22p8_24m1_33p1_44m4_66m3_88p1_132p3_264m1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 8, 2 => 1, 3 => -4, 5 => -3, 7 => 1, 10 => -3, 11 => 3, 21 => 8, 23 => -1, 32 => 1, 43 => -4, 65 => -3, 87 => 1, 131 => 3, 263 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m3_2p8_3p1_4m4_6m3_8p1_11m3_12p3_22p8_24m1_33p1_44m4_66m3_88p1_132p3_264m1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m3_2p8_3p1_4m4_6m3_8p1_11m3_12p3_22p8_24m1_33p1_44m4_66m3_88p1_132p3_264m1 =
    [0, 1, 3, 1, -3, 0, 3, 1, 0, -1, 0, -1, 0, 9, 3, -11, -3, 8, 3, -2,
     -3, 1, -3, -8, 3, 0, -9, -8, 3, 0, -9, 1, 0, -1, -6, -8, -3, 5, 0, -3,
     -3, -8, 9, -8, 3, 10, 6, 9, 0, 11, -6, 10, 15, 3, -6, 0, 9, 20, 12, -11,
     3, -19, 15, 21, -3, 8, -3, -1, 6, -7, -6, 2, 0, -6, -15, 11, 0, -1, -15, -7,
     -3, -14, 6, 18, -9, -30, 12, -10, 0, -23, 0, 16, -15, 2, -15, 6, 3, -3, -3, 1] := by
  eta_coeff

end WeightTwoCusps
