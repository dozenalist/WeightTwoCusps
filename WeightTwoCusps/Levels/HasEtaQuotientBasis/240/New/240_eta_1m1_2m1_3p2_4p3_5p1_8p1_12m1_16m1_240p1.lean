module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^3 η(5z) η(8z) η(12z)^(-1) η(16z)^(-1) η(240z)`; see
[the local level table](../../TABLE.md#level-240).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^3 η(5z) η(8z) η(12z)^(-1) η(16z)^(-1) η(240z)` at level 240. -/
abbrev cuspForm_240_eta_1m1_2m1_3p2_4p3_5p1_8p1_12m1_16m1_240p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -1, 1 => -1, 2 => 2, 3 => 3, 4 => 1, 7 => 1, 11 => -1, 15 => -1, 239 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m1_2m1_3p2_4p3_5p1_8p1_12m1_16m1_240p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m1_2m1_3p2_4p3_5p1_8p1_12m1_16m1_240p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 4, 2, 4, 3, 3, 2,
     0, 1, -2, 2, 0, 2, 0, 1, 0, -1, 0, 0, -4, -2, -4, -1, -6, 0, -2, -3,
     0, -4, -3, -8, 0, -1, -4, -2, -4, -2, -4, 3, 0, -5, -2, -8, 0, -7, 2, -3,
     -3, -4, 2, 1, -4, -1, 2, 0, 0, 0, 0, -6, 0, 6, -4, -6, 0, -2, -4, 8,
     4, 2, 6, 6, 6, -4, 4, 0, 0, 2, 2, -2, 0, 7, 0, 12, 4, -2, -6, -1] := by
  eta_coeff

end WeightTwoCusps
