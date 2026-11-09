module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-2) η(12z) η(26z)^2 η(39z)^(-1) η(52z)^(-1) η(78z) η(234z)^2 η(468z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-2) η(12z) η(26z)^2 η(39z)^(-1) η(52z)^(-1) η(78z) η(234z)^2 η(468z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p3_3p3_4m1_6m2_12p1_26p2_39m1_52m1_78p1_234p2_468m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -2, 11 => 1, 25 => 2, 38 => -1, 51 => -1, 77 => 1, 233 => 2, 467 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p3_3p3_4m1_6m2_12p1_26p2_39m1_52m1_78p1_234p2_468m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p3_3p3_4m1_6m2_12p1_26p2_39m1_52m1_78p1_234p2_468m1 =
    [0, 0, 1, 2, 2, 1, 0, 2, 2, 2, 2, 1, 2, 0, 2, 2, 0, 2, 2, 2,
     1, 0, 2, 2, 2, 4, 0, 0, 0, -2, -2, -2, 1, -2, -4, -2, -2, 0, -2, 0,
     -2, -3, 6, 0, -1, -2, 0, 5, -2, 0, -1, -6, 0, 4, 0, -4, -2, 4, 4, -1,
     2, 0, -2, 0, 2, 1, -4, 2, -8, -4, -4, -3, 0, -8, 0, -4, -4, 0, 0, -4,
     -3, 6, 2, -5, -8, -4, 2, -4, 2, -3, -10, -2, 6, 0, -6, -4, 0, 4, -3, 2] := by
  eta_coeff

end WeightTwoCusps
