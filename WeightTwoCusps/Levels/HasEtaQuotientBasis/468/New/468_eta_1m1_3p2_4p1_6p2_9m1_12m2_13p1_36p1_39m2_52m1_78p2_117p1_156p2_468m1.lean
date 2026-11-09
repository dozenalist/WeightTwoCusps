module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-1) η(3z)^2 η(4z) η(6z)^2 η(9z)^(-1) η(12z)^(-2) η(13z) η(36z) η(39z)^(-2) η(52z)^(-1) η(78z)^2 η(117z) η(156z)^2 η(468z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z) η(6z)^2 η(9z)^(-1) η(12z)^(-2) η(13z) η(36z) η(39z)^(-2) η(52z)^(-1) η(78z)^2 η(117z) η(156z)^2 η(468z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m1_3p2_4p1_6p2_9m1_12m2_13p1_36p1_39m2_52m1_78p2_117p1_156p2_468m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -1, 2 => 2, 3 => 1, 5 => 2, 8 => -1, 11 => -2, 12 => 1, 35 => 1, 38 => -2, 51 => -1, 77 => 2, 116 => 1, 155 => 2, 467 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m1_3p2_4p1_6p2_9m1_12m2_13p1_36p1_39m2_52m1_78p2_117p1_156p2_468m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m1_3p2_4p1_6p2_9m1_12m2_13p1_36p1_39m2_52m1_78p2_117p1_156p2_468m1 =
    [0, 1, 1, 2, 1, 2, 2, 0, 1, -2, 2, 0, 2, 2, -1, 3, -1, 1, -4, -2,
     2, -1, 2, -2, 2, 1, 0, 1, -5, -1, 1, 0, -1, -2, 1, 2, -4, 0, -5, 0,
     2, 0, 1, -4, 6, -1, -2, 0, -2, 7, -1, 5, 0, -3, 7, -2, -1, -6, 3, 4,
     1, 2, -1, -1, 1, 0, -2, -10, 1, 4, -2, 0, -4, 0, 2, -3, -1, -12, 0, 2,
     -2, -4, -4, 8, -7, 2, -6, 0, 2, 2, 1, -8, -2, 8, -2, -6, -2, 8, 3, 2] := by
  eta_coeff

end WeightTwoCusps
