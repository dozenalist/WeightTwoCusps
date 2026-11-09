module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-2) η(8z)^(-1) η(12z) η(44z)^2 η(66z) η(88z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-2) η(8z)^(-1) η(12z) η(44z)^2 η(66z) η(88z)^(-1)` at level 264. -/
abbrev cuspForm_264_eta_1m2_2p3_3p2_4p1_6m2_8m1_12p1_44p2_66p1_88m1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -2, 7 => -1, 11 => 1, 43 => 2, 65 => 1, 87 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m2_2p3_3p2_4p1_6m2_8m1_12p1_44p2_66p1_88m1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m2_2p3_3p2_4p1_6m2_8m1_12p1_44p2_66p1_88m1 =
    [0, 0, 0, 1, 2, 2, 2, 0, 0, 1, 2, 4, 0, 0, 0, -1, 2, 0, 0, 0,
     0, 2, 0, -2, 2, 0, 0, 2, -2, 0, -2, 0, 0, -3, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, -1, 2, -6, -6, -4, -4, -2, -2, -2, -6, -8, 0, 0, -4, 4,
     -2, 0, 0, -2, -2, -8, 0, 4, -4, -1, -4, -6, 0, 0, 4, 0, 0, -2, 0, 0,
     0, 3, -4, -4, 2, 0, 0, -4, 0, 4, -6, 8, 4, -3, 2, 4, 6, 0, 4, 3] := by
  eta_coeff

end WeightTwoCusps
