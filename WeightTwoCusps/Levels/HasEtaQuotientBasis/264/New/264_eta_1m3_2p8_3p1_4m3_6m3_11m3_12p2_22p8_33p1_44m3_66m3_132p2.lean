module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-3) η(11z)^(-3) η(12z)^2 η(22z)^8 η(33z) η(44z)^(-3) η(66z)^(-3) η(132z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-3) η(11z)^(-3) η(12z)^2 η(22z)^8 η(33z) η(44z)^(-3) η(66z)^(-3) η(132z)^2` at level 264. -/
abbrev cuspForm_264_eta_1m3_2p8_3p1_4m3_6m3_11m3_12p2_22p8_33p1_44m3_66m3_132p2 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -3, 10 => -3, 11 => 2, 21 => 8, 32 => 1, 43 => -3, 65 => -3, 131 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m3_2p8_3p1_4m3_6m3_11m3_12p2_22p8_33p1_44m3_66m3_132p2_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m3_2p8_3p1_4m3_6m3_11m3_12p2_22p8_33p1_44m3_66m3_132p2 =
    [0, 0, 0, 0, 0, 1, 3, 1, -3, -1, 0, 0, 3, -1, -3, -2, 0, 10, 3, -10,
     -3, -1, 0, 9, 0, -8, -9, -7, 9, 0, -6, 0, -3, 0, 0, 10, 0, -10, 0, 1,
     -3, 8, 9, -2, 0, -16, 12, 11, 3, 18, -3, 6, 3, 11, -3, -1, 3, -6, 6, 2,
     3, -9, 3, -7, 0, -12, -3, 20, -12, 8, -6, -11, -3, -10, 3, -9, -12, -1, -3, -11,
     -3, 7, 0, 0, -3, 8, 0, -2, 3, -10, -9, -20, 3, -1, -9, -10, 0, 12, 6, 1] := by
  eta_coeff

end WeightTwoCusps
