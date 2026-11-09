module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-1) η(8z)^(-1) η(12z)^(-1) η(22z)^(-2) η(24z) η(44z)^5 η(88z)^(-2) η(132z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-1) η(8z)^(-1) η(12z)^(-1) η(22z)^(-2) η(24z) η(44z)^5 η(88z)^(-2) η(132z)` at level 264. -/
abbrev cuspForm_264_eta_1m2_2p3_3p2_4p1_6m1_8m1_12m1_22m2_24p1_44p5_88m2_132p1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -1, 7 => -1, 11 => -1, 21 => -2, 23 => 1, 43 => 5, 87 => -2, 131 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m2_2p3_3p2_4p1_6m1_8m1_12m1_22m2_24p1_44p5_88m2_132p1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m2_2p3_3p2_4p1_6m1_8m1_12m1_22m2_24p1_44p5_88m2_132p1 =
    [0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 0, 2, -2, 0, 0, -1, 2,
     -2, 2, 0, 0, 2, -4, -2, -2, 2, 4, 3, 4, -2, 0, 0, 0, 2, -8, 0, -2,
     -2, 4, -4, 6, 0, 2, 4, -8, -6, -4, -2, -4, -2, 0, -4, 0, 2, 2, -4, -8,
     0, -8, -2, 0, 0, 4, 1, 4, 0, 2, -4, 0, -4, -8, 2, -2, 0, 0, 6, 10,
     -2, 2, 0, -8, -2, 0, 0, -2, 2, 0, -1, 8, 2, 2, 2, 4, 8, -4, 4, 0] := by
  eta_coeff

end WeightTwoCusps
