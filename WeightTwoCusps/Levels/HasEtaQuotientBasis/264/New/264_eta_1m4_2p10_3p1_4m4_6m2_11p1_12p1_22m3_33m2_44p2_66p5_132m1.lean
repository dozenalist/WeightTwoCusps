module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(11z) η(12z) η(22z)^(-3) η(33z)^(-2) η(44z)^2 η(66z)^5 η(132z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(11z) η(12z) η(22z)^(-3) η(33z)^(-2) η(44z)^2 η(66z)^5 η(132z)^(-1)` at level 264. -/
abbrev cuspForm_264_eta_1m4_2p10_3p1_4m4_6m2_11p1_12p1_22m3_33m2_44p2_66p5_132m1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 10 => 1, 11 => 1, 21 => -3, 32 => -2, 43 => 2, 65 => 5, 131 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m4_2p10_3p1_4m4_6m2_11p1_12p1_22m3_33m2_44p2_66p5_132m1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m4_2p10_3p1_4m4_6m2_11p1_12p1_22m3_33m2_44p2_66p5_132m1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 4, 4, -1, 0, 4, 1, 0, 0, 2, 4, -5, -6,
     -4, -3, 1, -4, 3, 0, -8, -2, -5, 6, 10, 6, 2, -1, 8, -6, -4, 6, 4, 5,
     -9, -8, -6, -4, 2, -4, 9, 4, -14, 0, -2, 2, 11, 0, -1, -1, 8, -4, -10, 4,
     -2, -1, -2, -9, -8, 0, 2, -8, 2, 6, -14, 4, 0, 0, 14, -2, 2, -2, 16, -1,
     -12, 8, -2, -2, -9, -14, -16, 2, 3, -12, 6, 8, -16, -2, 3, 14, 21, 4, 6, -4] := by
  eta_coeff

end WeightTwoCusps
