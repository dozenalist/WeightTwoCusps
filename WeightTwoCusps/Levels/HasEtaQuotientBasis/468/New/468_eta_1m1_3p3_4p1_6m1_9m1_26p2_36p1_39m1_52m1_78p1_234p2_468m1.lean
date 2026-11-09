module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-1) η(3z)^3 η(4z) η(6z)^(-1) η(9z)^(-1) η(26z)^2 η(36z) η(39z)^(-1) η(52z)^(-1) η(78z) η(234z)^2 η(468z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(4z) η(6z)^(-1) η(9z)^(-1) η(26z)^2 η(36z) η(39z)^(-1) η(52z)^(-1) η(78z) η(234z)^2 η(468z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m1_3p3_4p1_6m1_9m1_26p2_36p1_39m1_52m1_78p1_234p2_468m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -1, 2 => 3, 3 => 1, 5 => -1, 8 => -1, 25 => 2, 35 => 1, 38 => -1, 51 => -1, 77 => 1, 233 => 2, 467 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m1_3p3_4p1_6m1_9m1_26p2_36p1_39m1_52m1_78p1_234p2_468m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m1_3p3_4p1_6m1_9m1_26p2_36p1_39m1_52m1_78p1_234p2_468m1 =
    [0, 0, 0, 1, 1, 2, 0, 1, 0, 1, 1, 0, 1, 0, 2, 1, 0, 0, 1, 1,
     0, 0, 1, 2, 1, 2, 0, 0, 1, -2, -1, -4, 4, -1, 0, -2, -1, 1, -2, 0,
     -3, -2, 3, 2, 0, -1, 1, 0, -1, -2, 0, -3, 0, 2, 0, 0, -2, 2, -5, 2,
     1, 2, 0, 0, 3, 0, -2, 2, -4, -2, -3, 2, 0, 1, -2, -2, -3, 0, 0, -2,
     -4, 3, 3, -2, -4, -7, 0, -2, -1, -2, -5, 0, 2, 0, -3, -2, 0, -5, 0, 1] := by
  eta_coeff

end WeightTwoCusps
