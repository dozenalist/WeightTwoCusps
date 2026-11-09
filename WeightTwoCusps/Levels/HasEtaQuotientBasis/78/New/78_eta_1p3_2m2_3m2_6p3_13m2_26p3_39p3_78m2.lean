module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 78

The eta expression is `η(z)^3 η(2z)^(-2) η(3z)^(-2) η(6z)^3 η(13z)^(-2) η(26z)^3 η(39z)^3 η(78z)^(-2)`; see
[the local level table](../../TABLE.md#level-78).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^3 η(2z)^(-2) η(3z)^(-2) η(6z)^3 η(13z)^(-2) η(26z)^3 η(39z)^3 η(78z)^(-2)` at level 78. -/
abbrev cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2 : gamma0CuspForms 78 :=
  etaQuotientCuspForm 78 sparse![78; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 12 => -2, 25 => 3, 38 => 3, 77 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2 =
    [0, 1, -3, 2, 1, -1, -1, 3, -1, 0, -2, -2, 2, 0, 2, -5, 7, 2, -4, -4,
     7, -3, 0, -2, -3, 3, 0, -1, -5, 8, 5, -6, -3, 8, -3, 2, 0, -5, 2, 0,
     -6, -2, 1, 6, -2, 0, 6, -1, 4, 1, -4, -3, 0, -8, 5, -10, 2, 8, 0, 0,
     3, 6, 6, 2, -11, 0, -4, 2, -14, -4, 13, -3, -2, 4, 6, 5, 4, -6, 1, 2,
     3, -6, -12, 8, -11, -7, 1, 4, 8, 12, -1, 2, -2, -2, 2, -4, -1, -2, -10, 0] := by
  eta_coeff

end WeightTwoCusps
