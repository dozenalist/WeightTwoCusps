module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-1) η(3z)^2 η(4z) η(6z) η(12z)^(-1) η(39z)^3 η(78z)^(-2) η(117z)^(-2) η(156z) η(234z)^3 η(468z)^(-1)`; see
[the local level table](../../TABLE.md#level-468).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z) η(6z) η(12z)^(-1) η(39z)^3 η(78z)^(-2) η(117z)^(-2) η(156z) η(234z)^3 η(468z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m1_3p2_4p1_6p1_12m1_39p3_78m2_117m2_156p1_234p3_468m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -1, 2 => 2, 3 => 1, 5 => 1, 11 => -1, 38 => 3, 77 => -2, 116 => -2, 155 => 1, 233 => 3, 467 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m1_3p2_4p1_6p1_12m1_39p3_78m2_117m2_156p1_234p3_468m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m1_3p2_4p1_6p1_12m1_39p3_78m2_117m2_156p1_234p3_468m1 =
    [0, 0, 0, 0, 0, 1, 1, 2, 1, 2, 2, 1, 2, 0, 2, 1, 2, 2, 0, 2,
     3, 2, 2, 0, 2, 0, 1, 2, 0, 2, 2, 4, 0, 1, 2, 2, 2, 2, 0, 0,
     2, 3, 2, 0, -1, -1, -6, -1, -6, -4, 0, -4, 0, -6, -1, -4, -4, 2, -4, -7,
     -5, -4, 2, -6, 4, -3, -4, 0, -6, -4, -10, 1, -1, -6, -6, -2, -4, 2, 0, -4,
     -7, -6, 2, -3, -2, 6, 0, 6, -2, -5, 0, 0, 8, -4, -2, -2, -5, 2, 0, 3] := by
  eta_coeff

end WeightTwoCusps
