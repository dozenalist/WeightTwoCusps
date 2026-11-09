module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-1) η(6z)^(-2) η(8z)^(-1) η(11z)^(-3) η(22z)^7 η(24z) η(33z) η(44z)^(-1) η(66z)^(-2) η(88z)^(-1) η(264z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-1) η(6z)^(-2) η(8z)^(-1) η(11z)^(-3) η(22z)^7 η(24z) η(33z) η(44z)^(-1) η(66z)^(-2) η(88z)^(-1) η(264z)` at level 264. -/
abbrev cuspForm_264_eta_1m3_2p7_3p1_4m1_6m2_8m1_11m3_22p7_24p1_33p1_44m1_66m2_88m1_264p1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -1, 5 => -2, 7 => -1, 10 => -3, 21 => 7, 23 => 1, 32 => 1, 43 => -1, 65 => -2, 87 => -1, 263 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m3_2p7_3p1_4m1_6m2_8m1_11m3_22p7_24p1_33p1_44m1_66m2_88m1_264p1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m3_2p7_3p1_4m1_6m2_8m1_11m3_22p7_24p1_33p1_44m1_66m2_88m1_264p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 0, -3, -1, 3, -1, 0, -2, 0, 10,
     3, 1, 0, -10, 0, 7, -3, -3, -9, -6, 9, -5, 3, 0, -12, 8, 0, -3, -12, -13,
     3, 2, -3, 4, 0, -10, 12, -3, -3, -14, -9, 20, -3, 9, 9, 0, -3, 12, 6, -1,
     -3, -9, 9, -19, 0, 16, 0, 9, 12, 1, 6, 4, 3, 8, -15, 8, 12, -1, 3, -3,
     3, 3, 12, 18, 3, 6, 12, 4, -3, 5, 0, 0, -3, 6, -3, -30, 0, -19, -6, -2] := by
  eta_coeff

end WeightTwoCusps
