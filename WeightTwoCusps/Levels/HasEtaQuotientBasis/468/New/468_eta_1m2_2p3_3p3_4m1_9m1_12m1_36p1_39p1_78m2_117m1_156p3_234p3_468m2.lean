module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(9z)^(-1) η(12z)^(-1) η(36z) η(39z) η(78z)^(-2) η(117z)^(-1) η(156z)^3 η(234z)^3 η(468z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(9z)^(-1) η(12z)^(-1) η(36z) η(39z) η(78z)^(-2) η(117z)^(-1) η(156z)^3 η(234z)^3 η(468z)^(-2)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p3_3p3_4m1_9m1_12m1_36p1_39p1_78m2_117m1_156p3_234p3_468m2 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 8 => -1, 11 => -1, 35 => 1, 38 => 1, 77 => -2, 116 => -1, 155 => 3, 233 => 3, 467 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p3_3p3_4m1_9m1_12m1_36p1_39p1_78m2_117m1_156p3_234p3_468m2_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p3_3p3_4m1_9m1_12m1_36p1_39p1_78m2_117m1_156p3_234p3_468m2 =
    [0, 1, 2, 2, 1, 0, 2, 0, -2, -2, 0, 4, -2, 0, 0, 0, 1, -4, 2, -2,
     0, 0, -2, 0, -2, 1, 0, 2, 0, 0, 0, 0, -2, -4, -2, 0, -2, 0, 4, 0,
     -1, -6, -2, -3, -4, -2, 0, 2, 0, 1, -2, 6, 0, 0, 2, -1, 4, -6, 2, 4,
     0, 2, 0, 2, 0, 0, 2, -2, -4, 0, 0, 2, 2, 4, 0, 4, 2, -4, 0, 1,
     6, 0, 1, 8, 2, 0, 2, 0, 1, -2, -6, 0, 0, -2, 1, -4, 4, 0, -2, 4] := by
  eta_coeff

end WeightTwoCusps
