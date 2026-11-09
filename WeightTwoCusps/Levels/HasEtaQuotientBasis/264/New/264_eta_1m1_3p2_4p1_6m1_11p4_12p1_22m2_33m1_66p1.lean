module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-1) η(3z)^2 η(4z) η(6z)^(-1) η(11z)^4 η(12z) η(22z)^(-2) η(33z)^(-1) η(66z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z) η(6z)^(-1) η(11z)^4 η(12z) η(22z)^(-2) η(33z)^(-1) η(66z)` at level 264. -/
abbrev cuspForm_264_eta_1m1_3p2_4p1_6m1_11p4_12p1_22m2_33m1_66p1 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -1, 2 => 2, 3 => 1, 5 => -1, 10 => 4, 11 => 1, 21 => -2, 32 => -1, 65 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m1_3p2_4p1_6m1_11p4_12p1_22m2_33m1_66p1_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m1_3p2_4p1_6m1_11p4_12p1_22m2_33m1_66p1 =
    [0, 0, 1, 1, 2, 1, 2, 2, 3, 4, 4, 4, 5, 2, 3, -1, 4, 2, 2, 0,
     -3, -2, 0, -1, 1, -2, 3, -1, -4, 0, -1, 2, 1, -4, -6, -6, -2, 2, -8, 4,
     -8, -4, -3, -4, 0, -3, 2, 1, -13, 2, -9, 2, 2, -3, -5, -8, 3, -2, -8, -2,
     -3, -2, -2, -8, -6, -2, 0, 0, -6, 1, -2, -5, -1, -8, 0, -5, -2, -1, -7, -2,
     -11, 8, 2, -2, -4, -12, 10, 2, 4, -4, -7, 8, -5, 2, 2, 10, 19, 2, 1, 0] := by
  eta_coeff

end WeightTwoCusps
