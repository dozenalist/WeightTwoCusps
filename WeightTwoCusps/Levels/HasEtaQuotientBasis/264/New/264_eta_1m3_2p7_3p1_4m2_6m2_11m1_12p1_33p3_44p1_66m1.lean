module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(11z)^(-1) η(12z) η(33z)^3 η(44z) η(66z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(11z)^(-1) η(12z) η(33z)^3 η(44z) η(66z)^(-1)` at level 264. -/
abbrev cuspForm_264_eta_1m3_2p7_3p1_4m2_6m2_11m1_12p1_33p3_44p1_66m1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 10 => -1, 11 => 1, 32 => 3, 43 => 1, 65 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m3_2p7_3p1_4m2_6m2_11m1_12p1_33p3_44p1_66m1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m3_2p7_3p1_4m2_6m2_11m1_12p1_33p3_44p1_66m1 =
    [0, 0, 0, 1, 3, 2, 0, 1, 0, 1, 3, 0, 0, -1, 1, 4, -1, 0, 1, 0,
     1, 1, 0, -2, -1, 3, 7, -1, -3, 2, 0, 1, 4, -1, -8, -2, 1, 1, -8, -3,
     3, -4, -1, -4, -1, -9, -3, 3, 2, -2, -6, 2, -7, -1, 3, -2, -11, -4, 0, 1,
     -3, 1, 4, -13, 3, -2, 0, -1, -6, 2, 8, 0, -2, -2, -8, 6, 0, -1, -7, -1,
     1, 12, 2, 2, 5, -8, 10, 0, 0, -3, -4, 0, 9, -3, 3, 4, -3, 5, -6, -1] := by
  eta_coeff

end WeightTwoCusps
