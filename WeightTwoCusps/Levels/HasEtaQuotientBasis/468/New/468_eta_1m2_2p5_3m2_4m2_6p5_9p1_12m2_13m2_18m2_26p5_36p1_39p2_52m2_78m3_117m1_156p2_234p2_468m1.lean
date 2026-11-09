module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^5 η(3z)^(-2) η(4z)^(-2) η(6z)^5 η(9z) η(12z)^(-2) η(13z)^(-2) η(18z)^(-2) η(26z)^5 η(36z) η(39z)^2 η(52z)^(-2) η(78z)^(-3) η(117z)^(-1) η(156z)^2 η(234z)^2 η(468z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z)^(-2) η(4z)^(-2) η(6z)^5 η(9z) η(12z)^(-2) η(13z)^(-2) η(18z)^(-2) η(26z)^5 η(36z) η(39z)^2 η(52z)^(-2) η(78z)^(-3) η(117z)^(-1) η(156z)^2 η(234z)^2 η(468z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p5_3m2_4m2_6p5_9p1_12m2_13m2_18m2_26p5_36p1_39p2_52m2_78m3_117m1_156p2_234p2_468m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 5, 2 => -2, 3 => -2, 5 => 5, 8 => 1, 11 => -2, 12 => -2, 17 => -2, 25 => 5, 35 => 1, 38 => 2, 51 => -2, 77 => -3, 116 => -1, 155 => 2, 233 => 2, 467 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p5_3m2_4m2_6p5_9p1_12m2_13m2_18m2_26p5_36p1_39p2_52m2_78m3_117m1_156p2_234p2_468m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p5_3m2_4m2_6p5_9p1_12m2_13m2_18m2_26p5_36p1_39p2_52m2_78m3_117m1_156p2_234p2_468m1 =
    [0, 0, 1, 2, 0, 2, 6, 0, 0, 4, 0, 1, -2, 0, 4, 0, 4, 0, 6, 12,
     -1, 6, 8, 0, 4, -4, 0, 8, -4, 2, 4, 4, -2, -6, 12, 0, -4, 4, 2, 0,
     0, -2, 0, 8, -4, -14, -8, -3, -14, -8, -2, 8, 0, -8, 6, -4, 0, -12, -8, 2,
     -20, -20, 0, -8, 4, -1, -8, 12, -8, -4, -12, 4, 8, -16, -2, 6, -8, -4, -2, 0,
     2, -14, 0, 4, 14, 4, 8, 12, 4, 2, -14, 0, 6, -12, -12, -4, 6, 0, -2, 26] := by
  eta_coeff

end WeightTwoCusps
