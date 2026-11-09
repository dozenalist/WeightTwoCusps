module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(11z)^(-3) η(12z) η(22z)^7 η(33z) η(44z)^(-2) η(66z)^(-2) η(132z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(11z)^(-3) η(12z) η(22z)^7 η(33z) η(44z)^(-2) η(66z)^(-2) η(132z)` at level 264. -/
abbrev cuspForm_264_eta_1m3_2p7_3p1_4m2_6m2_11m3_12p1_22p7_33p1_44m2_66m2_132p1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 10 => -3, 11 => 1, 21 => 7, 32 => 1, 43 => -2, 65 => -2, 131 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m3_2p7_3p1_4m2_6m2_11m3_12p1_22p7_33p1_44m2_66m2_132p1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m3_2p7_3p1_4m2_6m2_11m3_12p1_22p7_33p1_44m2_66m2_132p1 =
    [0, 0, 0, 1, 3, 2, 0, 1, 0, 1, 3, 0, 0, -1, 3, 10, 3, 0, 3, 0,
     3, 7, 0, -2, -3, 3, 9, -7, -3, 2, 0, 1, 0, -1, -12, -2, 3, 1, -12, -9,
     3, -4, -3, -4, -3, -21, -3, 3, 0, -2, -6, 8, -15, -1, 3, -2, -9, -10, 0, 1,
     -3, 1, 0, -19, 3, -2, 0, -1, -6, 2, 12, 0, 0, -2, -12, 12, 0, -1, -9, -1,
     3, 24, 6, 2, 9, -8, 18, 0, 0, -3, -6, 0, 15, -3, 3, 4, -3, 5, -6, -1] := by
  eta_coeff

end WeightTwoCusps
