module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(z)^3 η(2z)^(-1) η(3z)^(-1) η(12z) η(38z)^3 η(76z)^(-1)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^3 η(2z)^(-1) η(3z)^(-1) η(12z) η(38z)^3 η(76z)^(-1)` at level 228. -/
abbrev cuspForm_228_eta_1p3_2m1_3m1_12p1_38p3_76m1 : gamma0CuspForms 228 :=
  etaQuotientCuspForm 228 sparse![228; 0 => 3, 1 => -1, 2 => -1, 11 => 1, 37 => 3, 75 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_228_eta_1p3_2m1_3m1_12p1_38p3_76m1_first_coeffs :
    first_coeffs 100 cuspForm_228_eta_1p3_2m1_3m1_12p1_38p3_76m1 =
    [0, 0, 1, -3, 1, 3, -1, 0, 0, -3, -1, 3, -2, 3, 1, 0, -1, 0, -1, 0,
     0, -3, 1, 3, 1, -3, -1, 0, 1, 0, 0, 3, 2, 0, 1, -3, 0, -3, 0, -3,
     -4, 9, -1, -9, 4, 3, 0, 9, 2, -6, 6, -6, -4, -3, 3, -3, 2, 0, 1, 9,
     -2, -9, -6, 9, 3, 3, -4, 0, -1, -6, -7, -3, -2, 12, 0, 12, 0, 9, 4, -6,
     -6, 6, -6, -12, 0, -3, 3, -3, -2, -9, 5, 9, -1, 6, 3, 0, -3, -3, -2, 3] := by
  eta_coeff

end WeightTwoCusps
