module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-2) η(2z)^3 η(3z) η(4z)^3 η(6z)^(-2) η(8z)^(-2) η(12z) η(33z)^(-1) η(66z)^3 η(132z)^(-2) η(264z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z) η(4z)^3 η(6z)^(-2) η(8z)^(-2) η(12z) η(33z)^(-1) η(66z)^3 η(132z)^(-2) η(264z)^2` at level 264. -/
abbrev cuspForm_264_eta_1m2_2p3_3p1_4p3_6m2_8m2_12p1_33m1_66p3_132m2_264p2 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -2, 1 => 3, 2 => 1, 3 => 3, 5 => -2, 7 => -2, 11 => 1, 32 => -1, 65 => 3, 131 => -2, 263 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m2_2p3_3p1_4p3_6m2_8m2_12p1_33m1_66p3_132m2_264p2_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m2_2p3_3p1_4p3_6m2_8m2_12p1_33m1_66p3_132m2_264p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2,
     2, 3, 0, -2, 1, 0, 4, 4, -2, -2, -4, 0, 2, -1, 0, -2, -2, 4, 0, -3,
     0, -4, 2, 0, 0, 0, -6, -2, -4, 0, 2, 3, 2, 0, 0, 0, 2, -1, 0, 4,
     0, -2, 0, -5, -4, -2, -1, 0, 0, 2, 4, -6, -1, 2, -2, 6, 0, 0, -8, -6,
     -2, -2, 0, 0, 2, -2, 0, -6, 0, 4, -1, 8, -2, -10, 2, 2, 2, -4, -4, 1] := by
  eta_coeff

end WeightTwoCusps
