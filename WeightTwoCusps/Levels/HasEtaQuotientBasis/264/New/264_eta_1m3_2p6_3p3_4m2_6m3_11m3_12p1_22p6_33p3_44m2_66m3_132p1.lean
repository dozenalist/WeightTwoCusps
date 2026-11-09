module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(11z)^(-3) η(12z) η(22z)^6 η(33z)^3 η(44z)^(-2) η(66z)^(-3) η(132z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(11z)^(-3) η(12z) η(22z)^6 η(33z)^3 η(44z)^(-2) η(66z)^(-3) η(132z)` at level 264. -/
abbrev cuspForm_264_eta_1m3_2p6_3p3_4m2_6m3_11m3_12p1_22p6_33p3_44m2_66m3_132p1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 10 => -3, 11 => 1, 21 => 6, 32 => 3, 43 => -2, 65 => -3, 131 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m3_2p6_3p3_4m2_6m3_11m3_12p1_22p6_33p3_44m2_66m3_132p1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m3_2p6_3p3_4m2_6m3_11m3_12p1_22p6_33p3_44m2_66m3_132p1 =
    [0, 0, 1, 3, 3, 1, -1, 0, 3, 2, 2, 0, -3, 2, 8, 12, 3, -6, 1, 6,
     6, 6, -1, -9, -3, 7, 18, 0, -12, 4, -2, 3, 3, -3, -10, -14, 3, 11, -8, -10,
     6, -12, -8, -4, -3, -9, -20, -4, -3, -12, -1, 4, -18, -12, -1, -1, -12, -10, -6, -3,
     -6, 6, 0, -20, 3, 8, 1, -19, 6, 2, 16, 9, 3, 2, -18, 23, 12, 0, -18, 8,
     6, 21, 6, 2, 12, -22, 16, -4, -3, -1, 2, 20, 12, -10, 12, 20, -3, -3, -15, -2] := by
  eta_coeff

end WeightTwoCusps
