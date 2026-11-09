module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^5 η(4z)^(-1) η(6z)^(-4) η(9z)^(-2) η(12z) η(13z) η(18z)^3 η(26z)^(-3) η(36z)^(-1) η(39z)^(-3) η(52z)^2 η(78z)^8 η(117z) η(156z)^(-3) η(234z)^(-3) η(468z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^5 η(4z)^(-1) η(6z)^(-4) η(9z)^(-2) η(12z) η(13z) η(18z)^3 η(26z)^(-3) η(36z)^(-1) η(39z)^(-3) η(52z)^2 η(78z)^8 η(117z) η(156z)^(-3) η(234z)^(-3) η(468z)^2` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p3_3p5_4m1_6m4_9m2_12p1_13p1_18p3_26m3_36m1_39m3_52p2_78p8_117p1_156m3_234m3_468p2 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 3, 2 => 5, 3 => -1, 5 => -4, 8 => -2, 11 => 1, 12 => 1, 17 => 3, 25 => -3, 35 => -1, 38 => -3, 51 => 2, 77 => 8, 116 => 1, 155 => -3, 233 => -3, 467 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p3_3p5_4m1_6m4_9m2_12p1_13p1_18p3_26m3_36m1_39m3_52p2_78p8_117p1_156m3_234m3_468p2_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p3_3p5_4m1_6m4_9m2_12p1_13p1_18p3_26m3_36m1_39m3_52p2_78p8_117p1_156m3_234m3_468p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2,
     2, -1, -4, -2, 1, 4, 0, -2, -2, -2, 2, -1, 0, -5, -3, 2, 2, 3, -4, -1,
     -2, 2, 4, 2, 6, 2, 5, 0, -4, 0, 0, 8, 1, -2, -1, -2, 0, -6, 0, -4,
     -4, -6, -2, 3, -4, -2, -6, 1, 2, 6, 7, 4, 0, -5, 2, 2, 8, 4, 0, -2,
     0, 4, 0, -2, -3, -1, -2, -4, -2, -4, -2, -1, -6, 6, 6, 2, 0, 1, 2, -3] := by
  eta_coeff

end WeightTwoCusps
