module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-3) η(6z)^(-2) η(11z)^3 η(12z)^2 η(22z)^(-2) η(33z)^(-1) η(66z) η(132z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-3) η(6z)^(-2) η(11z)^3 η(12z)^2 η(22z)^(-2) η(33z)^(-1) η(66z) η(132z)` at level 264. -/
abbrev cuspForm_264_eta_1m3_2p7_3p1_4m3_6m2_11p3_12p2_22m2_33m1_66p1_132p1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -3, 5 => -2, 10 => 3, 11 => 2, 21 => -2, 32 => -1, 65 => 1, 131 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m3_2p7_3p1_4m3_6m2_11p3_12p2_22m2_33m1_66p1_132p1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m3_2p7_3p1_4m3_6m2_11p3_12p2_22m2_33m1_66p1_132p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 2, 3, 3, 3, 3, 6, 4, 0, -4,
     -3, 5, 0, -2, 0, -3, -3, -9, -3, 4, 3, 5, -3, -2, 0, -8, 0, 5, 0, -1,
     -9, -6, -3, -4, 0, -8, 6, 3, -9, 4, -3, 4, 3, -3, -3, -4, 9, -4, -6, -1,
     -3, -3, -3, 1, -6, 0, 0, -5, 0, -1, -6, 0, 3, -6, 3, 4, 0, -1, 3, -1,
     -9, 13, 0, -2, -3, -16, 0, -2, 3, -11, 0, 10, -9, 0, 3, 16, 12, 3, 6, 0] := by
  eta_coeff

end WeightTwoCusps
