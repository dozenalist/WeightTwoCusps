module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^6 η(3z) η(6z)^(-2) η(8z)^(-1) η(11z)^3 η(22z)^(-3) η(24z) η(33z)^(-1) η(44z)^3 η(66z) η(88z)^(-1) η(132z)^(-1) η(264z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z) η(6z)^(-2) η(8z)^(-1) η(11z)^3 η(22z)^(-3) η(24z) η(33z)^(-1) η(44z)^3 η(66z) η(88z)^(-1) η(132z)^(-1) η(264z)` at level 264. -/
abbrev cuspForm_264_eta_1m3_2p6_3p1_6m2_8m1_11p3_22m3_24p1_33m1_44p3_66p1_88m1_132m1_264p1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 6, 2 => 1, 5 => -2, 7 => -1, 10 => 3, 21 => -3, 23 => 1, 32 => -1, 43 => 3, 65 => 1, 87 => -1, 131 => -1, 263 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m3_2p6_3p1_6m2_8m1_11p3_22m3_24p1_33m1_44p3_66p1_88m1_132m1_264p1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m3_2p6_3p1_6m2_8m1_11p3_22m3_24p1_33m1_44p3_66p1_88m1_132m1_264p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 3, 3, 3, 0, 3, 6, 4, 6, 3, 0,
     -3, -3, 0, -3, 8, 0, -9, 0, -9, 3, 6, 3, 5, -3, 6, -9, 0, 9, -6, 9,
     -5, -9, -3, -6, 0, -6, 9, 0, -13, 3, -6, 0, 9, -3, -3, -6, -5, -18, -18, 6,
     -9, -6, -12, -24, 0, -3, 0, -3, 0, 9, -12, -3, -5, -6, 12, -3, 0, 0, -3, -6,
     -11, 21, 12, 0, 3, -12, 0, -3, 1, -3, 6, 15, -21, -12, -9, 12, 10, -6, 6, 0] := by
  eta_coeff

end WeightTwoCusps
