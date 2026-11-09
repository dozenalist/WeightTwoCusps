module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-1) η(3z) η(4z) η(6z)^2 η(9z)^4 η(12z)^(-1) η(18z)^(-3) η(27z)^(-2) η(36z) η(54z)^3 η(108z)^(-1)`; see
[the local level table](../../TABLE.md#level-216).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z) η(4z) η(6z)^2 η(9z)^4 η(12z)^(-1) η(18z)^(-3) η(27z)^(-2) η(36z) η(54z)^3 η(108z)^(-1)` at level 216. -/
abbrev cuspForm_216_eta_1m1_3p1_4p1_6p2_9p4_12m1_18m3_27m2_36p1_54p3_108m1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -1, 2 => 1, 3 => 1, 5 => 2, 8 => 4, 11 => -1, 17 => -3, 26 => -2, 35 => 1, 53 => 3, 107 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m1_3p1_4p1_6p2_9p4_12m1_18m3_27m2_36p1_54p3_108m1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m1_3p1_4p1_6p2_9p4_12m1_18m3_27m2_36p1_54p3_108m1 =
    [0, 1, 1, 2, 2, 3, 4, 3, 5, 4, 2, 3, 0, 1, -3, -4, 2, -6, 0, -1,
     -3, 0, -2, 6, 0, -7, 6, -4, -2, 0, 0, 2, -7, 8, 0, -9, 0, 3, 0, -4,
     -6, 0, -16, 4, 3, -8, -4, -6, 0, -4, -8, 4, -8, -3, 0, -14, -5, -8, 4, 0,
     0, -5, -7, 0, 2, 0, 0, -13, 0, -16, -2, 0, 0, 7, 0, -2, 4, -3, 8, 7,
     -3, 4, -4, 3, 0, 8, 14, 12, 6, 12, 0, 9, 6, 16, 4, -6, 0, -1, 4, 16] := by
  eta_coeff

end WeightTwoCusps
