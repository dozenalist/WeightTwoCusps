module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^5 η(4z)^(-1) η(6z)^(-4) η(9z)^(-2) η(12z) η(18z)^3 η(36z)^(-1) η(39z)^(-3) η(78z)^7 η(117z)^2 η(156z)^(-2) η(234z)^(-3) η(468z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^5 η(4z)^(-1) η(6z)^(-4) η(9z)^(-2) η(12z) η(18z)^3 η(36z)^(-1) η(39z)^(-3) η(78z)^7 η(117z)^2 η(156z)^(-2) η(234z)^(-3) η(468z)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p3_3p5_4m1_6m4_9m2_12p1_18p3_36m1_39m3_78p7_117p2_156m2_234m3_468p1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 3, 2 => 5, 3 => -1, 5 => -4, 8 => -2, 11 => 1, 17 => 3, 35 => -1, 38 => -3, 77 => 7, 116 => 2, 155 => -2, 233 => -3, 467 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p3_3p5_4m1_6m4_9m2_12p1_18p3_36m1_39m3_78p7_117p2_156m2_234m3_468p1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p3_3p5_4m1_6m4_9m2_12p1_18p3_36m1_39m3_78p7_117p2_156m2_234m3_468p1 =
    [0, 0, 0, 0, 0, 1, 2, 2, -1, -4, -2, 1, 4, 0, -2, -2, -2, 2, 0, 2,
     -3, -4, -2, 0, 4, 0, -1, -4, 0, 2, 4, 4, 0, -2, -2, 2, 4, 2, 0, 0,
     -2, 3, 4, 0, 1, 2, 6, -1, -12, -4, 0, 8, 0, -6, -2, -4, 4, -4, 4, -7,
     -10, -4, -2, 12, -4, -3, -8, 0, 6, 8, 10, 1, -2, -6, 6, 4, 4, 2, 0, -4,
     7, 12, -2, -3, -4, 6, 0, -12, 2, -5, 0, 0, -8, 8, 2, -2, -10, 2, 0, -6] := by
  eta_coeff

end WeightTwoCusps
