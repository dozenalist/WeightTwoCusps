module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-2) η(8z)^(-1) η(11z)^2 η(22z)^(-3) η(24z) η(33z)^(-2) η(44z)^3 η(66z)^4 η(88z)^(-1) η(132z)^(-2) η(264z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-2) η(8z)^(-1) η(11z)^2 η(22z)^(-3) η(24z) η(33z)^(-2) η(44z)^3 η(66z)^4 η(88z)^(-1) η(132z)^(-2) η(264z)` at level 264. -/
abbrev cuspForm_264_eta_1m2_2p3_3p2_4p1_6m2_8m1_11p2_22m3_24p1_33m2_44p3_66p4_88m1_132m2_264p1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -2, 7 => -1, 10 => 2, 21 => -3, 23 => 1, 32 => -2, 43 => 3, 65 => 4, 87 => -1, 131 => -2, 263 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m2_2p3_3p2_4p1_6m2_8m1_11p2_22m3_24p1_33m2_44p3_66p4_88m1_132m2_264p1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m2_2p3_3p2_4p1_6m2_8m1_11p2_22m3_24p1_33m2_44p3_66p4_88m1_132m2_264p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0, 0, 1, 2, 4, 0, 0,
     -2, -4, 0, -2, 2, 0, -2, -1, -6, 2, 2, 2, 4, -2, 2, -2, 0, 2, -2, 4,
     -2, -2, 0, -4, 0, -1, 2, 4, 0, 2, -4, 0, 6, -2, 0, -4, -6, -4, -6, 0,
     -6, -4, 0, -10, 2, 2, 0, 2, 0, 5, -4, 2, 0, -4, 4, -3, 0, 0, -2, -4,
     -6, 7, 2, 4, 2, -8, -2, 0, 0, -6, 2, -2, -14, -5, -2, 0, -2, 0, 0, 1] := by
  eta_coeff

end WeightTwoCusps
