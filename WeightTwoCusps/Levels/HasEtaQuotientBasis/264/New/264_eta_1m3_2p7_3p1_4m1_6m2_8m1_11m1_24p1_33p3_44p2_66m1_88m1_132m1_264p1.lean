module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-1) η(6z)^(-2) η(8z)^(-1) η(11z)^(-1) η(24z) η(33z)^3 η(44z)^2 η(66z)^(-1) η(88z)^(-1) η(132z)^(-1) η(264z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-1) η(6z)^(-2) η(8z)^(-1) η(11z)^(-1) η(24z) η(33z)^3 η(44z)^2 η(66z)^(-1) η(88z)^(-1) η(132z)^(-1) η(264z)` at level 264. -/
abbrev cuspForm_264_eta_1m3_2p7_3p1_4m1_6m2_8m1_11m1_24p1_33p3_44p2_66m1_88m1_132m1_264p1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -1, 5 => -2, 7 => -1, 10 => -1, 23 => 1, 32 => 3, 43 => 2, 65 => -1, 87 => -1, 131 => -1, 263 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m3_2p7_3p1_4m1_6m2_8m1_11m1_24p1_33p3_44p2_66m1_88m1_132m1_264p1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m3_2p7_3p1_4m1_6m2_8m1_11m1_24p1_33p3_44p2_66m1_88m1_132m1_264p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 0, -3, -1, 3, -1, 0, -2, -2, 4,
     -1, 1, 0, -4, 2, 1, -1, -3, -5, 0, 7, 1, 1, 0, -10, 2, 4, -3, -6, -7,
     1, 2, -3, 4, 0, -4, 10, -3, -1, -8, -9, 8, -3, 3, 5, 0, -5, 6, 4, -1,
     -5, -3, 11, -7, 4, 10, 0, 3, 8, 1, 2, 4, -1, 2, -11, 2, 8, -1, 5, 3,
     1, 3, 2, 6, 3, 0, 6, 4, -1, -1, -2, 0, -3, 6, 5, -12, -2, -7, -2, -2] := by
  eta_coeff

end WeightTwoCusps
