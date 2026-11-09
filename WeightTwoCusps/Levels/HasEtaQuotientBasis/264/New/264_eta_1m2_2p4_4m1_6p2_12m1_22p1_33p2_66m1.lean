module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(6z)^2 η(12z)^(-1) η(22z) η(33z)^2 η(66z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(6z)^2 η(12z)^(-1) η(22z) η(33z)^2 η(66z)^(-1)` at level 264. -/
abbrev cuspForm_264_eta_1m2_2p4_4m1_6p2_12m1_22p1_33p2_66m1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -2, 1 => 4, 3 => -1, 5 => 2, 11 => -1, 21 => 1, 32 => 2, 65 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m2_2p4_4m1_6p2_12m1_22p1_33p2_66m1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m2_2p4_4m1_6p2_12m1_22p1_33p2_66m1 =
    [0, 1, 2, 1, 2, 3, 2, 2, 0, 2, 2, 1, 4, 0, 2, 3, 2, 2, 0, 4,
     2, 2, 0, -1, 0, 0, 2, -1, 0, 0, 2, 1, 0, -1, -4, -2, -2, -5, -8, -4,
     0, 0, -6, -6, -2, -8, -2, -2, -12, -7, -4, -2, -8, -8, -2, -1, -2, 0, -4, -9,
     2, 0, -2, -12, -2, 0, 2, 7, -8, -1, 0, 1, -4, -12, -2, 4, -4, 0, -2, 2,
     -2, 13, 8, -6, 0, -2, 8, -4, 2, 7, 0, 0, 10, -3, -4, 4, 16, -3, -6, 0] := by
  eta_coeff

end WeightTwoCusps
