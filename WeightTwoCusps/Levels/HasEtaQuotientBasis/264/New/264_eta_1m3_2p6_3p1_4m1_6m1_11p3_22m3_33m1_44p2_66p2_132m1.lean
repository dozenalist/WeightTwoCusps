module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-1) η(6z)^(-1) η(11z)^3 η(22z)^(-3) η(33z)^(-1) η(44z)^2 η(66z)^2 η(132z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-1) η(6z)^(-1) η(11z)^3 η(22z)^(-3) η(33z)^(-1) η(44z)^2 η(66z)^2 η(132z)^(-1)` at level 264. -/
abbrev cuspForm_264_eta_1m3_2p6_3p1_4m1_6m1_11p3_22m3_33m1_44p2_66p2_132m1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 6, 2 => 1, 3 => -1, 5 => -1, 10 => 3, 21 => -3, 32 => -1, 43 => 2, 65 => 2, 131 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m3_2p6_3p1_4m1_6m1_11p3_22m3_33m1_44p2_66p2_132m1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m3_2p6_3p1_4m1_6m1_11p3_22m3_33m1_44p2_66p2_132m1 =
    [0, 1, 3, 3, 3, 4, 3, 5, 6, 5, 6, 5, 6, -1, -3, 1, -3, 4, -3, -6,
     -3, -7, 3, -8, 3, 8, -3, 8, -9, 4, 9, 5, 12, -9, 6, -8, -9, 7, -12, 7,
     -9, -18, -9, -14, 3, -10, 6, 9, -18, -3, -12, 0, 15, 1, 0, -16, 3, -6, -24, 7,
     -3, 1, -9, -31, -15, -12, 3, -9, -6, 11, -18, -2, -6, 0, 27, 3, 0, -5, 3, -9,
     -21, 16, 6, -2, -9, -28, -12, -2, 6, -13, 0, 10, -15, -10, -3, 20, 27, 17, -3, 1] := by
  eta_coeff

end WeightTwoCusps
