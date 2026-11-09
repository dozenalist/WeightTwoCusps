module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-1) η(2z)^(-1) η(3z)^3 η(4z)^2 η(6z) η(8z)^(-1) η(12z)^(-1) η(16z)^2 η(24z) η(32z)^(-1) η(48z)^(-1) η(96z)`; see
[the local level table](../../TABLE.md#level-288).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-1) η(3z)^3 η(4z)^2 η(6z) η(8z)^(-1) η(12z)^(-1) η(16z)^2 η(24z) η(32z)^(-1) η(48z)^(-1) η(96z)` at level 288. -/
abbrev cuspForm_288_eta_1m1_2m1_3p3_4p2_6p1_8m1_12m1_16p2_24p1_32m1_48m1_96p1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -1, 1 => -1, 2 => 3, 3 => 2, 5 => 1, 7 => -1, 11 => -1, 15 => 2, 23 => 1, 31 => -1, 47 => -1, 95 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m1_2m1_3p3_4p2_6p1_8m1_12m1_16p2_24p1_32m1_48m1_96p1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m1_2m1_3p3_4p2_6p1_8m1_12m1_16p2_24p1_32m1_48m1_96p1 =
    [0, 0, 0, 1, 1, 3, 1, 4, 1, 4, 1, 3, 2, 4, 3, 6, 0, 6, 1, 6,
     1, 0, 2, -2, 0, 0, -1, 1, 0, 1, -2, -8, 0, -4, -1, -4, -2, -4, -5, -2,
     0, -10, 0, -6, -2, -8, -4, 4, 0, 0, 1, -14, -2, -7, 1, -4, -4, 4, -3, -1,
     -4, -4, 1, -8, 0, -14, -4, -2, -1, 8, 0, -6, 0, -8, 4, -1, -4, 0, -2, 0,
     0, -8, 3, 5, 0, 0, -7, -2, 0, 8, -2, -8, 4, -8, 0, -2, 0, 8, -4, 12] := by
  eta_coeff

end WeightTwoCusps
