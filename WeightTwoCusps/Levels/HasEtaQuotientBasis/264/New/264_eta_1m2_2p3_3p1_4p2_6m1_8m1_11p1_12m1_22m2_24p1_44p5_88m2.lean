module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-2) η(2z)^3 η(3z) η(4z)^2 η(6z)^(-1) η(8z)^(-1) η(11z) η(12z)^(-1) η(22z)^(-2) η(24z) η(44z)^5 η(88z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z) η(4z)^2 η(6z)^(-1) η(8z)^(-1) η(11z) η(12z)^(-1) η(22z)^(-2) η(24z) η(44z)^5 η(88z)^(-2)` at level 264. -/
abbrev cuspForm_264_eta_1m2_2p3_3p1_4p2_6m1_8m1_11p1_12m1_22m2_24p1_44p5_88m2 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -2, 1 => 3, 2 => 1, 3 => 2, 5 => -1, 7 => -1, 10 => 1, 11 => -1, 21 => -2, 23 => 1, 43 => 5, 87 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m2_2p3_3p1_4p2_6m1_8m1_11p1_12m1_22m2_24p1_44p5_88m2_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m2_2p3_3p1_4p2_6m1_8m1_11p1_12m1_22m2_24p1_44p5_88m2 =
    [0, 1, 2, 2, 3, 1, 0, 2, 1, 3, 1, 0, 0, -2, 3, -1, 1, 2, -1, 2,
     -3, 2, 0, 1, 5, -3, 3, 0, 0, 4, -1, 4, -1, 0, -2, -6, 3, -4, 2, 4,
     -2, 0, -5, 2, 0, -1, -1, -15, -10, -5, -3, -6, -6, -3, -6, 0, -5, -4, -6, 0,
     -3, -6, -3, -8, 3, -6, 1, 2, -6, 1, -8, -3, -5, -10, 5, -4, 0, -1, 1, 10,
     1, 11, -8, -14, 0, 0, 2, -6, 1, 6, -2, 20, 9, 4, 8, 10, 13, -8, 6, -2] := by
  eta_coeff

end WeightTwoCusps
